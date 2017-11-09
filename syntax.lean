import smt2.except
import data.hash_map

-- non-meta instance
attribute [derive decidable_eq] name

open except
open state

def unreachable {α : Type} : except string α :=
error "unreachable"

-- syntax

@[reducible] def syntax_id := ℕ
@[reducible] def macro_scope_id := ℕ

-- byte offset into source string
@[reducible] def position := ℕ

structure span :=
(left : position)
(right : position)
(file : string)

inductive syntax
| ident (id : syntax_id) (sp : option span) (n : name) (msc : option macro_scope_id)
/- any non-ident atom -/
| atom (id : syntax_id) (sp : option span) (val : name)
| list (ls : list syntax)
| node (id : syntax_id) (sp : option span) (m : name) (args : list syntax)

protected meta def syntax.to_format : syntax → format :=
λ s, format.group $ format.nest 2 $ match s with
| (syntax.ident id _ n none) := format!"({id}: ident `{n})"
| (syntax.ident id _ n (some sc)) := format!"({id}: ident `{n} from {sc})"
| (syntax.atom id _ val) := format!"(atom {val})"
| (syntax.list ls) := format!"[{format.join $ ls.map syntax.to_format}]"
| (syntax.node id _ m args) :=
    let args := format.join $ args.map (λ arg, format!"\n{arg.to_format}") in
    format!"({id}: node `{m} {args})"
end

meta instance : has_to_format syntax := ⟨syntax.to_format⟩
meta instance : has_to_string syntax := ⟨to_string ∘ to_fmt⟩
meta instance : has_repr syntax := ⟨to_string ∘ to_fmt⟩

structure resolved :=
(decl : syntax_id)
/- prefix of the reference that corresponds to the decl. All trailing name components
   are field accesses. -/
(«prefix» : name)

meta instance : has_to_format resolved := ⟨λ r, to_fmt (r.decl, r.prefix)⟩

@[reducible] def resolve_map := hash_map syntax_id (λ _, resolved)
def scope := hash_map (name × option macro_scope_id) (λ _, syntax_id)

@[reducible] def resolve_m := state_t resolve_map (except string)

def exp_fuel := 1000

structure macro :=
(name : name)
-- (read : reader)
-- TODO: What else does an expander need? How to model recursive expansion?
(expand : option (list syntax → syntax) := none)
(resolve : option (scope → syntax_id → list syntax → resolve_m (list scope)) := none)
-- (elaborate : list syntax → expr → tactic expr)

-- identifiers in macro expansions are annotated with incremental tags
structure expand_state :=
(next_tag : ℕ)

@[reducible] def exp_m := state expand_state

def mk_tag : exp_m ℕ :=
do st ← read,
   write {st with next_tag := st.next_tag + 1},
   pure st.next_tag

section
parameter (macros : name → option macro)

def flip_tag (tag : ℕ) : syntax → syntax
| (syntax.node id sp m args) := syntax.node id sp m (args.map
    -- flip_tag
    (λ s, flip_tag s))
| (syntax.list ls) := syntax.list (ls.map
    -- flip_tag
    (λ s, flip_tag s))
| (syntax.ident id sp n none) := syntax.ident id sp n (some tag)
| (syntax.ident id sp n (some tag')) := syntax.ident id sp n (if tag = tag' then none else some tag')
| stx := stx
using_well_founded { dec_tac := tactic.admit } -- TODO

def expand : ℕ → syntax → exp_m syntax
| (fuel + 1) (syntax.node id sp m args) :=
do some (macro.mk _ (some expander) _) ← pure $ macros m
     | syntax.node id sp m <$> args.mmap (expand fuel),
   tag ← mk_tag,
   let args := args.map $ flip_tag tag,
   -- expand recursively
   expand fuel $ flip_tag tag $ expander args
| _ stx := pure stx

def resolve : scope → syntax → resolve_m unit
| sc (syntax.node id sp m args) :=
do some (macro.mk _ _ (some resolver)) ← pure $ macros m
     | args.mmap' $ resolve sc,
   arg_scopes ← resolver sc id args,
   (arg_scopes.zip args).mmap' -- (uncurry resolve)
                               (λ ⟨sc, stx⟩, resolve sc stx)
| _ _ := pure ()
using_well_founded { dec_tac := tactic.admit }
end

-- some examples

def sp : option span := none

def lambda_macro := {macro .
  name := "lambda",
  resolve := some $ λ sc _ args,
  do [syntax.ident id sp n msc, body] ← pure args
       -- TODO: add `monad_error` class to remove lift (also, `monad_lift` seems to be broken)
       | state_t.lift unreachable,
     pure [sc, sc.insert (n, msc) id]}

def resolve_name (msc : option macro_scope_id) (sc : scope) : name → option resolved
| (name.mk_string s n) :=
do {
  decl ← sc.find (n.mk_string s, msc),
  pure ⟨decl, n.mk_string s⟩
} <|> resolve_name n
| _ := none

def ref_macro := {macro .
  name := "ref",
  resolve := some $ λ sc _ args,
  do [syntax.ident id _ n msc] ← pure args
       | state_t.lift unreachable,
     some resolved ← pure $ resolve_name msc sc n
       | state_t.lift $ error sformat!"unknown identifier {n}",
     state_t.modify (λ h, hash_map.insert h id resolved),
     pure []}

def intro_x_macro := {macro .
  name := "intro_x",
  expand := some $ λ args,
    -- TODO: how to manage IDs?
    syntax.node 5 sp "lambda" (syntax.ident 6 sp "x" none :: args)}

def macros : name → option macro
| "lambda" := some lambda_macro
| "ref" := some ref_macro
| "intro_x" := some intro_x_macro
| _ := none

def expand' (stx : syntax) : syntax :=
(expand macros 1000 stx {next_tag := 0}).1

def resolve' (stx : syntax) : except string (syntax × resolve_map) :=
let sc : scope := mk_hash_map (λ ⟨n, _⟩, n.to_string.length), -- TODO
    resolve_map : resolve_map := mk_hash_map id in
    do ⟨(), rsm⟩ ← resolve macros sc stx resolve_map,
       pure (stx, rsm)

meta def test (stx : syntax) : command :=
match resolve' (expand' stx) with
| except.error e := tactic.fail e
| except.ok    o := tactic.trace stx >> tactic.trace o
end

run_cmd test $ syntax.node 0 sp "lambda" [
  syntax.ident 1 sp "x" none,
  syntax.node 2 sp "ref" [
    syntax.ident 3 sp "x" none
  ]
]

-- test macro shadowing
run_cmd test $ syntax.node 0 sp "lambda" [
  syntax.ident 1 sp "x" none,
  syntax.node 4 sp "intro_x" [
    syntax.node 2 sp "ref" [
      syntax.ident 3 sp "x" none
    ]
  ]
]

-- test field notation
run_cmd test $ syntax.node 0 sp "lambda" [
  syntax.ident 1 sp `x.y none,
  syntax.node 2 sp "ref" [
    syntax.ident 3 sp `x.y.z none
  ]
]

-- hygiene

namespace name
-- TODO: make original non-meta by making decidable_eq instance non-meta
def replace_prefix' : name → name → name → name
| anonymous        p p' := anonymous
| (mk_string s c)  p p' := if c = p then mk_string s p' else mk_string s (replace_prefix' c p p')
| (mk_numeral v c) p p' := if c = p then mk_numeral v p' else mk_numeral v (replace_prefix' c p p')
end name

def α_conv (rsm : resolve_map) (σ : syntax_id → name) : syntax → syntax
| (syntax.ident id sp n msc) := match rsm.find id with
  | some r := syntax.ident id none (n.replace_prefix' r.prefix (σ r.decl)) msc
  | none   := syntax.ident id none (σ id) msc
  end
| (syntax.node id sp m args) := syntax.node id sp m (args.map (λ a, α_conv a))
| (syntax.list ls) := syntax.list (ls.map (λ a, α_conv a))
| (syntax.atom id sp s) := syntax.atom id sp s
using_well_founded { dec_tac := tactic.admit }

run_cmd
let stx := syntax.node 0 sp "lambda" [
  syntax.ident 1 sp `x.y none,
  syntax.node 2 sp "ref" [
    syntax.ident 3 sp `x.y.z none
  ]
] in
match resolve' (expand' stx) with
| except.ok (_, rsm) := tactic.trace (α_conv rsm (λ id, if id = 1 then `a else `b) stx)
| except.error _ := tactic.skip
end

def α_equiv (rsm : resolve_map) (s₁ s₂ : syntax) :=
∃ σ, α_conv rsm σ s₁ = s₂

theorem hygienic (s₁ s₂ : syntax) :
match resolve' (expand' s₁) : _ → Prop with
| except.ok (_, rsm) := α_equiv rsm s₁ s₂ → α_equiv rsm (expand' s₁) (expand' s₂)
| except.error _ := false
end := sorry
