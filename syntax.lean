import smt2.except

-- non-meta instance
attribute [derive decidable_eq] name

universes u v w

namespace name
  @[simp] protected def quick_lt : name → name → Prop
  | anonymous        anonymous          := false
  | anonymous        _                  := true
  | (mk_numeral v n) (mk_numeral v' n') := v < v' ∨ v = v' ∧ n.quick_lt n'
  | (mk_numeral _ _) (mk_string _ _)    := true
  | (mk_string s n)  (mk_string s' n')  := s < s' ∨ s = s' ∧ n.quick_lt n'
  | _                _                  := false

  instance decidable_rel_quick_lt : decidable_rel name.quick_lt :=
  begin
    intros n n',
    induction n generalizing n',
    case anonymous {
      by_cases n' = anonymous; simp *; apply_instance
    },
    all_goals { cases n'; simp; apply_instance }
  end
end name

namespace option
  variables {α : Type u} (r : α → α → Prop)

  @[simp] protected def lt : option α → option α → Prop
  | none (some x) := true
  | (some x) (some y) := r x y
  | _ _ := false

  instance decidable_rel_lt [decidable_rel r] : decidable_rel (option.lt r) :=
  by intros a b; cases a; cases b; simp; apply_instance

  protected def has_lt [has_lt α] : has_lt (option α) := ⟨option.lt (<)⟩
end option

namespace rbmap
  variables {α : Type u} {β : Type v} {δ : Type w} {lt : α → α → Prop}
  open format prod
  variables [has_to_format α] [has_to_format β]

  private meta def format_key_data (a : α) (b : β) (first : bool) : format :=
  (if first then to_fmt "" else to_fmt "," ++ line) ++ to_fmt a ++ space ++ to_fmt "←" ++ space ++ to_fmt b

  private meta def to_format (m : rbmap α β lt) : format :=
  group $ to_fmt "⟨" ++ nest 1 (fst (fold (λ a b p, (fst p ++ format_key_data a b (snd p), ff)) m (to_fmt "", tt))) ++
          to_fmt "⟩"

  meta instance : has_to_format (rbmap α β lt) :=
  ⟨to_format⟩
end rbmap

def name.has_lt_quick : has_lt name := ⟨name.quick_lt⟩
local attribute [instance] name.has_lt_quick option.has_lt

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

structure syntax_ident :=
(id : syntax_id) (sp : option span) (name : name) (msc : option macro_scope_id)

structure syntax_atom :=
(id : syntax_id) (sp : option span) (val : name)

structure syntax_node (syntax : Type) :=
(id : syntax_id) (sp : option span) (m : name) (args : list syntax)

inductive syntax
| ident (val : syntax_ident)
/- any non-ident atom -/
| atom (val : syntax_atom)
| list (ls : list syntax)
| node (val : syntax_node syntax)

protected meta def syntax.to_format : syntax → format :=
λ s, format.group $ format.nest 2 $ match s with
| (syntax.ident ident@{msc := none, ..}) := format!"({ident.id}: ident `{ident.name})"
| (syntax.ident ident@{msc := some sc, ..}) := format!"({ident.id}: ident `{ident.name} from {sc})"
| (syntax.atom atom) := format!"({atom.id}: atom {atom.val})"
| (syntax.list ls) := format!"[{format.join $ ls.map syntax.to_format}]"
| (syntax.node node) :=
    let args := format.join $ node.args.map (λ arg, format!"\n{arg.to_format}") in
    format!"({node.id}: node `{node.m} {args})"
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

@[reducible] def resolve_map := rbmap syntax_id resolved
def scope := rbmap (name × option macro_scope_id) syntax_id

@[reducible] def resolve_m := state_t resolve_map (except string)

def exp_fuel := 1000

structure macro :=
(name : name)
-- (read : reader)
-- TODO: What else does an expander need? How to model recursive expansion?
(expand : option (syntax_node syntax → syntax) := none)
(resolve : option (scope → syntax_node syntax → resolve_m (list scope)) := none)
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
| (syntax.node node) := syntax.node {node with args := (node.args.map
    -- flip_tag
    (λ s, flip_tag s))}
| (syntax.list ls) := syntax.list (ls.map
    -- flip_tag
    (λ s, flip_tag s))
| (syntax.ident ident@{msc := none, ..}) := syntax.ident {ident with msc := some tag}
| (syntax.ident ident@{msc := some tag', ..}) :=
    syntax.ident {ident with msc := if tag = tag' then none else some tag'}
| stx := stx
using_well_founded { dec_tac := tactic.admit } -- TODO

def expand : ℕ → syntax → exp_m syntax
| (fuel + 1) (syntax.node node) :=
do some {expand := some exp, ..} ← pure $ macros node.m
     | (λ args, syntax.node {node with args := args}) <$> node.args.mmap (expand fuel),
   tag ← mk_tag,
   let node := {node with args := node.args.map $ flip_tag tag},
   -- expand recursively
   expand fuel $ flip_tag tag $ exp node
| _ stx := pure stx

def resolve : scope → syntax → resolve_m unit
| sc (syntax.node node) :=
do some {resolve := some res, ..} ← pure $ macros node.m
     | node.args.mmap' $ resolve sc,
   arg_scopes ← res sc node,
   (arg_scopes.zip node.args).mmap' -- (uncurry resolve)
                                    (λ ⟨sc, stx⟩, resolve sc stx)
| _ _ := pure ()
using_well_founded { dec_tac := tactic.admit }
end

-- some examples

def sp : option span := none

def lambda_macro := {macro .
  name := "lambda",
  resolve := some $ λ sc node,
  do [syntax.ident ident, body] ← pure node.args
       -- TODO: add `monad_error` class to remove lift (also, `monad_lift` seems to be broken)
       | state_t.lift unreachable,
     pure [sc, sc.insert (ident.name, ident.msc) ident.id]}

def resolve_name (msc : option macro_scope_id) (sc : scope) : name → option resolved
| (name.mk_string s n) :=
do {
  decl ← sc.find (n.mk_string s, msc),
  pure ⟨decl, n.mk_string s⟩
} <|> resolve_name n
| _ := none

def ref_macro := {macro .
  name := "ref",
  resolve := some $ λ sc node,
  do [syntax.ident ident] ← pure node.args
       | state_t.lift unreachable,
     some resolved ← pure $ resolve_name ident.msc sc ident.name
       | state_t.lift $ error sformat!"unknown identifier {ident.name}",
     state_t.modify (λ h, h.insert ident.id resolved),
     pure []}

def intro_x_macro := {macro .
  name := "intro_x",
  expand := some $ λ node,
    -- TODO: how to manage IDs?
    syntax.node ⟨5, sp, "lambda", syntax.ident ⟨6, sp, "x", none⟩ :: node.args⟩}

def macros : name → option macro
| "lambda" := some lambda_macro
| "ref" := some ref_macro
| "intro_x" := some intro_x_macro
| _ := none

def expand' (stx : syntax) : syntax :=
(expand macros 1000 stx {next_tag := 0}).1

def resolve' (stx : syntax) : except string (syntax × resolve_map) :=
let sc : scope := mk_rbmap _ _ _,
    resolve_map : resolve_map := mk_rbmap _ _ _ in
    do ⟨(), rsm⟩ ← resolve macros sc stx resolve_map,
       pure (stx, rsm)

meta def test (stx : syntax) : command :=
match resolve' (expand' stx) with
| except.error e := tactic.fail e
| except.ok    o := tactic.trace stx >> tactic.trace o
end

run_cmd test $ syntax.node ⟨0, sp, "lambda", [
  syntax.ident ⟨1, sp, "x", none⟩,
  syntax.node ⟨2, sp, "ref", [
    syntax.ident ⟨3, sp, "x", none⟩
  ]⟩
]⟩

-- test macro shadowing
run_cmd test $ syntax.node ⟨0, sp, "lambda", [
  syntax.ident ⟨1, sp, "x", none⟩,
  syntax.node ⟨4, sp, "intro_x", [
    syntax.node ⟨2, sp, "ref", [
      syntax.ident ⟨3, sp, "x", none⟩
    ]⟩
  ]⟩
]⟩

-- test field notation
run_cmd test $ syntax.node ⟨0, sp, "lambda", [
  syntax.ident ⟨1, sp, `x.y, none⟩,
  syntax.node ⟨2, sp, "ref", [
    syntax.ident ⟨3, sp, `x.y.z, none⟩
  ]⟩
]⟩

-- hygiene

namespace name
-- TODO: make original non-meta by making decidable_eq instance non-meta
def replace_prefix' : name → name → name → name
| anonymous        p p' := anonymous
| (mk_string s c)  p p' := if c = p then mk_string s p' else mk_string s (replace_prefix' c p p')
| (mk_numeral v c) p p' := if c = p then mk_numeral v p' else mk_numeral v (replace_prefix' c p p')
end name

def α_conv (rsm : resolve_map) (σ : syntax_id → name) : syntax → syntax
| (syntax.ident ident) := match rsm.find ident.id with
  | some r := syntax.ident {ident with sp := none, name := ident.name.replace_prefix' r.prefix (σ r.decl)}
  | none   := syntax.ident {ident with sp := none, name := σ ident.id}
  end
| (syntax.node node) := syntax.node {node with args := node.args.map (λ a, α_conv a)}
| (syntax.list ls) := syntax.list (ls.map (λ a, α_conv a))
| a@(syntax.atom _) := a
using_well_founded { dec_tac := tactic.admit }

run_cmd
let stx := syntax.node ⟨0, sp, "lambda", [
  syntax.ident ⟨1, sp, `x.y, none⟩,
  syntax.node ⟨2, sp, "ref", [
    syntax.ident ⟨3, sp, `x.y.z, none⟩
  ]⟩
]⟩ in
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
