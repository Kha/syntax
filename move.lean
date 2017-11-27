import except

-- non-meta instance
attribute [derive decidable_eq] name

universes u v w

namespace name
  -- TODO: make original non-meta by making decidable_eq instance non-meta
  def replace_prefix' : name → name → name → name
  | anonymous        p p' := anonymous
  | (mk_string s c)  p p' := if c = p then mk_string s p' else mk_string s (replace_prefix' c p p')
  | (mk_numeral v c) p p' := if c = p then mk_numeral v p' else mk_numeral v (replace_prefix' c p p')

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

  protected def has_lt_quick : has_lt name := ⟨name.quick_lt⟩
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

def unreachable {α : Type} : except string α :=
except.error "unreachable"
