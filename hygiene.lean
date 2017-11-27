import macro

def α_conv (rsm : resolve_map) (σ : syntax_id → name) : syntax → syntax
| (syntax.ident ident) := match rsm.find ident.id with
  | some r := syntax.ident {ident with sp := none, name := ident.name.replace_prefix' r.prefix (σ r.decl)}
  | none   := syntax.ident {ident with sp := none, name := σ ident.id}
  end
| (syntax.node node) := syntax.node {node with args := node.args.map (λ a, α_conv a)}
| (syntax.list ls) := syntax.list (ls.map (λ a, α_conv a))
| a@(syntax.atom _) := a
using_well_founded { dec_tac := tactic.admit }

def α_equiv (rsm : resolve_map) (s₁ s₂ : syntax) :=
∃ σ, α_conv rsm σ s₁ = s₂

section
parameter (macros : name → option macro)

theorem hygienic (s₁ s₂ : syntax) :
match resolve' macros (expand' macros s₁) : _ → Prop with
| except.ok (_, rsm) := α_equiv rsm s₁ s₂ → α_equiv rsm (expand' macros s₁) (expand' macros s₂)
| except.error _ := false
end := sorry
end
