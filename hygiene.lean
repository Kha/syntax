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

protected def except.passert {ε} : except ε Prop → Prop
| (except.ok p)    := p
| (except.error _) := true

namespace parse_m
variables {r σ α : Type} (cfg : r) (st : σ)

protected def passert := except.passert ∘ parse_m.run' cfg st

protected def passert' (x : parse_m r σ α) (p : σ → α → Prop) :=
match parse_m.run cfg st x : _ → Prop with
| (except.ok a, st')  := p st' a
| (except.error _, _) := true
end

variables {cfg st}

protected lemma passert_passert' (x : parse_m r σ Prop) :
  parse_m.passert cfg st x = parse_m.passert' cfg st x (λ st a, a) := sorry

variable (x : parse_m r σ α)

@[simp] lemma passert'_pure (a : α) (p) : parse_m.passert' cfg st (pure a) p = p st a := sorry

@[simp] lemma passert'_bind {β}
  (f : α → parse_m r σ β) (p : σ → β → Prop) :
  parse_m.passert' cfg st (x >>= f) p =
  parse_m.passert' cfg st x (λ st' a, parse_m.passert' cfg st' (f a) p) := sorry

@[simp] lemma passert'_fmap {β}
  (f : α → β) (p : σ → β → Prop) :
  parse_m.passert' cfg st (f <$> x) p =
  parse_m.passert' cfg st x (λ st' a, p st' (f a)) := sorry

@[simp] lemma passert'_with_state {σ'} (f : σ → σ') (p) (x : parse_m r σ' α) :
  parse_m.passert' cfg st (with_state f x) p = parse_m.passert' cfg (f st) x (λ _, p st) := sorry

@[simp] lemma passert'_get (p) :
  parse_m.passert' cfg st (get) p = p st st := sorry

@[simp] lemma passert'_put (p st') :
  parse_m.passert' cfg st (put st') p = p st' unit.star := sorry

@[simp] lemma passert'_read (p) :
  parse_m.passert' cfg st (read) p = p st cfg := sorry

lemma passert'_mp {p : parse_m r σ α} {s₀ : σ} {post₁ post₂ : σ → α → Prop} :
     parse_m.passert' cfg s₀ p post₁ → (∀ s a, post₁ s a → post₂ s a) → parse_m.passert' cfg s₀ p post₂ :=
sorry /-begin
  simp [passert],
  generalize h₁ : p s₀ = o,
  cases o with r,
  { simp [passert] },
  { cases r with a s,
    simp [passert], intros h₁ h₂, exact h₂ _ _ h₁ }
end-/

lemma passert'_mp_no_state {p : parse_m r σ α} {s₀ s₀' : σ} {post₁ post₂ : α → Prop} :
     parse_m.passert' cfg s₀ p (λ s, post₁) → (∀ a, post₁ a → post₂ a) → parse_m.passert' cfg s₀' p (λ s, post₂) :=
sorry
end parse_m

theorem hygienic (s₁ s₂ : syntax) (st : parse_state) :
parse_m.passert st () $
do s₁' ← expand' s₁,
   s₂' ← expand' s₂,
   (_, rst) ← resolve' s₁',
   pure $ α_equiv rst.resolve_map s₁ s₂ → α_equiv rst.resolve_map s₁' s₂' := sorry

lemma expand_idem (s : syntax) (cfg : parse_state) :
parse_m.passert cfg () $
do s' ← expand' s,
   s'' ← expand' s'
     | pure true,
   pure $ s'' = s' :=
begin
  -- generalize states (irrelevant) and step counts
  suffices : ∀ st st₂ steps steps₂, steps ≤ steps₂ → parse_m.passert' cfg st (expand steps s)
    (λ (_x : expand_state) (a : syntax),
       parse_m.passert' cfg st₂ (expand steps₂ a) (λ (_x : expand_state) (a_1 : syntax), a_1 = a)),
  { simp [parse_m.passert_passert', expand'], apply this, apply le_refl },
  intros st st₂ steps steps₂,
  induction steps with steps generalizing s st st₂ steps₂,
  -- `expand s` out of steps: trivial
  { intros; simp [expand] },
  { intro hsteps₂,
    -- `expand s'` can do at least one step as well
    cases steps₂ with steps₂, { exfalso, apply nat.not_succ_le_zero _ hsteps₂ },
    -- recursive case 1: holds when expanding all children (when s is not a macro)
    have expand_mmap : ∀ (val : syntax_node syntax),
      parse_m.passert' cfg st (mmap (expand steps) (val.args))
        (λ (st' : expand_state) (a_1 : list syntax),
          parse_m.passert' cfg st₂ (mmap (expand steps₂) a_1)
            (λ (st' : expand_state) (a : list syntax),
                syntax.node {id := val.id, sp := val.sp, m := val.m, args := a} =
                  syntax.node {id := val.id, sp := val.sp, m := val.m, args := a_1})),
    begin
        intro,
        induction val.args generalizing st st₂; simp [mmap],
        case list.cons {
          apply parse_m.passert'_mp (steps_ih _ st st₂ _ (nat.le_of_succ_le_succ hsteps₂)), intros st' s' expand_s',
          apply parse_m.passert'_mp (ih st' st₂), intros st'' args' mmap_args',
          apply parse_m.passert'_mp expand_s', intros st''' s''' _,
          apply parse_m.passert'_mp_no_state mmap_args', intros args this,
          injection this with this, injection this with this,
          simp *
        }
    end,
    cases hs : s; simp [expand],
    --TODO `case` for ginductives
    --case syntax.node n {
    { cases h : rbmap.find cfg.macros val.m with m,
      case none { simp [expand, h], apply expand_mmap },
      case some {
        cases m, cases m_expand,
        case none { simp [expand, h], apply expand_mmap },
        case some {
          -- recursive case 1: re-expand the expansion of s. `expand s` will do one more step than `expand s'`.
          -- `mk_tag` is so simple that `simp` can automatically transform it to its spec
          simp [expand, mk_tag],
          apply parse_m.passert'_mp (steps_ih _ _ st₂ _ (nat.le_of_succ_le hsteps₂)), intros st' s' expand_s',
          apply expand_s',
        },
      }
    }
  }
end
