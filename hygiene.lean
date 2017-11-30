import macro

def α_conv (rsm : resolve_map) (σ : syntax_id → name) : syntax → syntax
| (syntax.ident ident) := match rsm.find ident.id with
  -- TODO: renaming of globals?
  | some r@{decl := sum.inl id, ..} := syntax.ident {ident with sp := none, name := ident.name.replace_prefix' r.prefix (σ id)}
  | _   := syntax.ident {ident with sp := none, name := σ ident.id}
  end
| (syntax.node node) := syntax.node {node with args := node.args.map (λ a, α_conv a)}
| (syntax.list ls) := syntax.list (ls.map (λ a, α_conv a))
| a@(syntax.atom _) := a
using_well_founded { dec_tac := tactic.admit }

def α_equiv (rsm : resolve_map) (s₁ s₂ : syntax) :=
∃ σ, α_conv rsm σ s₁ = s₂

protected def except.assert {ε} : except ε Prop → Prop
| (except.ok p)    := p
| (except.error _) := false

theorem hygienic (s₁ s₂ : syntax) (st : parse_state) :
except.assert $ parse_m.run' st () $
(do s₁' ← expand' s₁,
    s₂' ← expand' s₂,
    (_, rst) ← resolve' s₁',
    pure $ α_equiv rst.resolve_map s₁ s₂ → α_equiv rst.resolve_map s₁' s₂')
:= sorry
