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

@[simp] lemma except.passert_pure {ε p} : except.passert (pure p : except ε Prop) = p := rfl

namespace parse_m
variables {r σ α : Type} (cfg : r) (st : σ)

variable (x : parse_m r σ α)

protected def run_cont {β} (x : parse_m r σ α) (cont : σ → α → except string β) : except string β :=
match parse_m.run cfg st x with
| (except.ok a, st)   := cont st a
| (except.error e, _) := except.error e
end

protected def passert (x : parse_m r σ Prop) : Prop :=
except.passert $ parse_m.run_cont cfg st x $ λ st a, except.ok a

variables {cfg} {st}
variables {β γ : Type} (p : σ → β → except string γ)
variables (q : σ → α → except string β)

@[simp] lemma run_cont_pure (a : α) : parse_m.run_cont cfg st (pure a) q = q st a := sorry

@[simp] lemma run_cont_bind (f : α → parse_m r σ β) :
  parse_m.run_cont cfg st (x >>= f) p =
  parse_m.run_cont cfg st x (λ st' a, parse_m.run_cont cfg st' (f a) p) := sorry

@[simp] lemma run_cont_fmap (f : α → β) :
  parse_m.run_cont cfg st (f <$> x) p =
  parse_m.run_cont cfg st x (λ st' a, p st' (f a)) := sorry

@[simp] lemma run_cont_with_state {σ'} (f : σ → σ') (x : parse_m r σ' α) :
  parse_m.run_cont cfg st (with_state f x) q = parse_m.run_cont cfg (f st) x (λ _, q st) := sorry

@[simp] lemma run_cont_get (p : σ → σ → except string γ) :
  parse_m.run_cont cfg st get p = p st st := sorry

@[simp] lemma run_cont_put (p : σ → punit → except string γ) (st') :
  parse_m.run_cont cfg st (put st') p = p st' punit.star := sorry

@[simp] lemma run_cont_read (p : σ → r → except string γ) :
  parse_m.run_cont cfg st read p = p st cfg := sorry

lemma passert_mp {p : parse_m r σ α} {s₀ : σ} {post₁ post₂ : σ → α → except string Prop} :
  except.passert (parse_m.run_cont cfg s₀ p post₁) → (∀ s a, except.passert (post₁ s a) → except.passert (post₂ s a)) → except.passert (parse_m.run_cont cfg s₀ p post₂) :=
sorry /-begin
  simp [passert],
  generalize h₁ : p s₀ = o,
  cases o with r,
  { simp [passert] },
  { cases r with a s,
    simp [passert], intros h₁ h₂, exact h₂ _ _ h₁ }
end-/

lemma passert_mp_no_state {p : parse_m r σ α} {s₀ s₀' : σ} {post₁ post₂ : α → except string Prop} :
     (p.run_cont cfg s₀ (λ s, post₁)).passert → (∀ a, (post₁ a).passert → (post₂ a).passert) → (p.run_cont cfg s₀' (λ s, post₂)).passert :=
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
   s'' ← expand' s',
   pure $ s'' = s' :=
begin
  -- generalize states (irrelevant) and step counts
  suffices : ∀ st st₂ steps steps₂, steps ≤ steps₂ →
(except.passert $
 parse_m.run_cont cfg st (expand steps s) $ λ _ s',
 parse_m.run_cont cfg st₂ (expand steps₂ s') $ λ _ s'',
 pure $ s'' = s'),
  { simp [parse_m.passert, expand'], apply this, apply le_refl },
  intros st st₂ steps steps₂,
  induction steps with steps generalizing s st st₂ steps₂,
  -- `expand s` out of steps: trivial
  { intros; simp [expand] },
  { intro hsteps₂,
    -- `expand s'` can do at least one step as well
    cases steps₂ with steps₂, { exfalso, apply nat.not_succ_le_zero _ hsteps₂ },
    -- recursive case 1: holds when expanding all children (when s is not a macro)
    have expand_mmap : ∀ (val : syntax_node syntax),
      except.passert $
      parse_m.run_cont cfg st (mmap (expand steps) (val.args)) $ λ _ args',
      parse_m.run_cont cfg st₂ (mmap (expand steps₂) args') $ λ _ args'',
      pure $ syntax.node {id := val.id, sp := val.sp, m := val.m, args := args''} =
             syntax.node {id := val.id, sp := val.sp, m := val.m, args := args'},
    begin
        intro,
        induction val.args generalizing st st₂; simp [mmap],
        case list.cons {
          apply parse_m.passert_mp (steps_ih _ st st₂ _ (nat.le_of_succ_le_succ hsteps₂)), intros st' s' expand_s',
          apply parse_m.passert_mp (ih st' st₂), intros st'' args' mmap_args',
          apply parse_m.passert_mp expand_s', intros st''' s''' h,
          apply parse_m.passert_mp_no_state mmap_args', intros args this,
          simp at h this,
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
          apply parse_m.passert_mp (steps_ih _ _ st₂ _ (nat.le_of_succ_le hsteps₂)), intros st' s' expand_s',
          apply expand_s',
        },
      }
    }
  }
end
