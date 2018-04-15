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

@[simp] protected def except.passert {ε} : except ε Prop → Prop
| (except.ok p)    := p
| (except.error _) := true

@[simp] lemma except.passert_pure {ε p} : except.passert (pure p : except ε Prop) = p := rfl

section
open interactive
open interactive.types
open tactic
meta def tactic.interactive.simp_val (p : parse texpr) : tactic unit :=
do e ← i_to_expr_strict p,
   (e', _) ← conv.convert (conv.interactive.simp ff [] []) e,
   exact e'
end

namespace parse_m
variables {r σ α : Type} (cfg : r) (st : σ)

protected def run_cont {β} (x : parse_m r σ α) (cont : σ → α → except string β) : except string β :=
match parse_m.run cfg st x with
| (except.ok a, st)   := cont st a
| (except.error e, _) := except.error e
end

protected def passert_cont (x : parse_m r σ α) (cont : σ → α → Prop) : Prop :=
except.passert $ parse_m.run_cont cfg st x $ λ st a, pure (cont st a)

protected def passert (x : parse_m r σ Prop) : Prop :=
parse_m.passert_cont cfg st x (λ st, id)

variables {cfg} {st}
variables {β γ : Type} (p : σ → β → except string γ)
variables (q : σ → α → except string β)

local attribute [simp] parse_m.run_cont parse_m.run
attribute [reducible] parse_m
attribute [reducible]
  parse_m.monad_run except_t.monad_run state_t.monad_run reader_t.monad_run id.monad_run

variable (x : parse_m r σ α)

@[simp] lemma run_cont_pure (a : α) : parse_m.run_cont cfg st (pure a) q = q st a := rfl

@[simp] lemma run_cont_bind (f : α → parse_m r σ β) :
  parse_m.run_cont cfg st (x >>= f) p =
  parse_m.run_cont cfg st x (λ st' a, parse_m.run_cont cfg st' (f a) p) :=
by simp; cases (by simp_val parse_m.run cfg st x); cases fst; simp [except_t.bind_cont]

@[simp] lemma run_cont_map (f : α → β) :
  parse_m.run_cont cfg st (f <$> x) p =
  parse_m.run_cont cfg st x (λ st' a, p st' (f a)) :=
by simp; cases (by simp_val parse_m.run cfg st x); cases fst; simp [except.map]

@[simp] lemma run_cont_adapt_state {σ' σ''} (f : σ → σ' × σ'') (f') (x : parse_m r σ' α) :
  parse_m.run_cont cfg st (adapt_state f f' x) q =
    let (st',st'') := f st in parse_m.run_cont cfg st' x (λ st', q (f' st' st'')) :=
by cases h : f st with st' st''; simp [adapt_state]; rw [h]; simp; cases (by simp_val parse_m.run cfg st' x); cases fst; simp

@[simp] lemma run_cont_put (p : σ → punit → except string γ) (st') :
  parse_m.run_cont cfg st (put st') p = p st' punit.star :=
by simp [put, monad_state.lift]

@[simp] lemma run_cont_read (p : σ → r → except string γ) :
  parse_m.run_cont cfg st read p = p st cfg :=
by simp [read]

@[simp] lemma run_cont_throw (e) (p : σ → α → except string γ) :
  parse_m.run_cont cfg st (throw e) p = except.error e :=
by simp [throw]

lemma passert_mp {p : parse_m r σ α} {s₀ : σ} {post₁ post₂ : σ → α → except string Prop} :
  except.passert (parse_m.run_cont cfg s₀ p post₁) → (∀ s a, except.passert (post₁ s a) → except.passert (post₂ s a)) → except.passert (parse_m.run_cont cfg s₀ p post₂) :=
begin
  simp,
  intros hpost₁ hmp,
  cases (by simp_val parse_m.run cfg s₀ p); cases fst; simp [parse_m.run_cont] at *,
  apply hmp _ _ hpost₁
end

@[simp] lemma passert_invariant {p : parse_m r σ α} {s₀ : σ} {post : except string Prop} :
  except.passert post → except.passert (parse_m.run_cont cfg s₀ p (λ _ _, post)) :=
begin
  simp,
  cases (by simp_val parse_m.run cfg s₀ p); cases fst; simp [parse_m.run_cont] at *,
  exact id
end

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
  suffices : ∀ st steps steps₂, steps ≤ steps₂ →
(parse_m.passert_cont cfg st (expand steps s) $ λ _ s',
 ∀ st₂, parse_m.passert_cont cfg st₂ (expand steps₂ s') $ λ _ s'',
 s'' = s'),
  { simp [parse_m.passert, parse_m.passert_cont, expand'] at *,
    apply parse_m.passert_mp, apply this, apply le_refl,
    intros st' s' x, apply x },
  simp [parse_m.passert_cont],
  intros st steps steps₂,
  induction steps with steps generalizing s st steps₂,
  -- `expand s` out of steps: trivial
  { intros; simp [expand] },
  { intro hsteps₂,
    -- `expand s'` can do at least one step as well
    cases steps₂ with steps₂, { exfalso, apply nat.not_succ_le_zero _ hsteps₂ },
    -- recursive case 1: holds when expanding all children (when s is not a macro)
    have expand_mmap : ∀ (val : syntax_node syntax),
      parse_m.passert_cont cfg st (mmap (expand steps) (val.args)) $ λ _ args',
      ∀ st₂, parse_m.passert_cont cfg st₂ (mmap (expand steps₂) args') $ λ _ args'',
        args'' = args',
    begin
        intro,
        simp [parse_m.passert_cont] at *,
        induction val.args generalizing st; simp [mmap],
        case list.cons {
          apply parse_m.passert_mp (steps_ih _ st _ (nat.le_of_succ_le_succ hsteps₂)), intros st' s' expand_s',
          clear steps_ih,
          apply parse_m.passert_mp (ih st'), intros st'' args' mmap_args' st₂,
          clear ih,
          apply parse_m.passert_mp (expand_s' _), intros st''' s''' h,
          apply parse_m.passert_mp (mmap_args' _), intros st'''' args this,
          simp * at *,
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
          apply parse_m.passert_mp (steps_ih _ _ _ (nat.le_of_succ_le hsteps₂)), intros st' s' expand_s',
          apply expand_s',
        },
      }
    }
  }
end
