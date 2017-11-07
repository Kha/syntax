import smt2.except
import data.hash_map

-- non-meta instance
attribute [derive decidable_eq] name

open except
open state

def unreachable {α : Type} : except string α :=
error "unreachable"

--

@[reducible] def syntax_id := ℕ
@[reducible] def macro_scope_id := ℕ

inductive syntax
| macro (id : syntax_id) (m : name) (args : list syntax)
| name (id : syntax_id) (n : name) (msc : option macro_scope_id)
-- ...

protected meta def syntax.to_format : syntax → format :=
λ s, format.group $ format.nest 2 $ match s with
| (syntax.name id n none) := format!"({id}: name `{n})"
| (syntax.name id n (some sc)) := format!"({id}: name `{n} from {sc})"
| (syntax.macro id m args) :=
    let args := format.join $ args.map (λ arg, format!"\n{arg.to_format}") in
    format!"({id}: node `{m} {args})"
end

meta instance : has_to_format syntax := ⟨syntax.to_format⟩
meta instance : has_to_string syntax := ⟨to_string ∘ to_fmt⟩
meta instance : has_repr syntax := ⟨to_string ∘ to_fmt⟩

@[reducible] def resolve_map := hash_map syntax_id (λ _, syntax_id)
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
| (syntax.macro id m args) := syntax.macro id m (args.map
    -- flip_tag
    (λ s, flip_tag s))
| (syntax.name id n none) := syntax.name id n (some tag)
| (syntax.name id n (some tag')) := syntax.name id n (if tag = tag' then none else some tag')
using_well_founded { dec_tac := tactic.admit } -- TODO

def expand : ℕ → syntax → exp_m syntax
| (fuel + 1) (syntax.macro id m args) :=
do some (macro.mk _ (some expander) _) ← pure $ macros m
     | syntax.macro id m <$> args.mmap (expand fuel),
   tag ← mk_tag,
   let args := args.map $ flip_tag tag,
   -- expand recursively
   expand fuel $ flip_tag tag $ expander args
| _ stx := pure stx

def resolve : scope → syntax → resolve_m unit
| sc (syntax.macro id m args) :=
do some (macro.mk _ _ (some resolver)) ← pure $ macros m
     | args.mmap' $ resolve sc,
   arg_scopes ← resolver sc id args,
   (arg_scopes.zip args).mmap' -- (uncurry resolve)
                               (λ ⟨sc, stx⟩, resolve sc stx)
| _ _ := pure ()
using_well_founded { dec_tac := tactic.admit }
end

--

def lambda_macro := {macro .
  name := "lambda",
  resolve := some $ λ sc id args,
  do [syntax.name id n msc, body] ← pure args
       -- TODO: add `monad_error` class to remove lift (also, `monad_lift` seems to be broken)
       | state_t.lift unreachable,
     pure [sc, sc.insert (n, msc) id]}

def ident_macro := {macro .
  name := "ident",
  resolve := some $ λ sc id args,
  do [syntax.name id n msc] ← pure args
       | state_t.lift unreachable,
     some ref ← pure $ sc.find (n, msc)
       | state_t.lift $ error sformat!"unknown identifier {n}",
     state_t.modify (λ h, hash_map.insert h id ref),
     pure []}

def intro_x_macro := {macro .
  name := "intro_x",
  expand := some $ λ args,
    -- TODO: how to manage IDs?
    syntax.macro 5 "lambda" (syntax.name 6 "x" none :: args)}

def macros : name → option macro
| "lambda" := some lambda_macro
| "ident" := some ident_macro
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

run_cmd test $ syntax.macro 0 "lambda" [
  syntax.name 1 "x" none,
  syntax.macro 2 "ident" [
    syntax.name 3 "x" none
  ]
]

run_cmd test $ syntax.macro 0 "lambda" [
  syntax.name 1 "x" none,
  syntax.macro 4 "intro_x" [
    syntax.macro 2 "ident" [
      syntax.name 3 "x" none
    ]
  ]
]

--

def syntax.rename (σ : syntax_id → name) : syntax → syntax
| (syntax.name id n msc) := syntax.name id (σ id) msc
| (syntax.macro id m args) := syntax.macro id m (args.map (λ a, syntax.rename a))
using_well_founded { dec_tac := tactic.admit }

def α_conv (rsm : resolve_map) (s₁ s₂ : syntax) :=
∃ σ, s₁.rename (σ ∘ λ id, (rsm.find id).get_or_else id) = s₂

theorem hygienic (s₁ s₂ : syntax) :
match resolve' (expand' s₁) : _ → Prop with
| except.ok (_, rsm) := α_conv rsm s₁ s₂ → α_conv rsm (expand' s₁) (expand' s₂)
| except.error _ := false
end := sorry
