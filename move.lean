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

namespace list
  section
  parameters {α : Type u} {β : Type v}

  def pmap : Π (xs : list α), (Π (x : α), x ∈ xs → β) → list β
  | []       f := []
  | (a :: l) f := f a (mem_cons_self a l) :: pmap l (λ x h, f x (mem_cons_of_mem a h))
  end
end list

namespace monad
  def kleisli {m : Type u → Type v} [monad m] {α β γ : Type u} : (α → m β) → (β → m γ) → (α → m γ) :=
  λ a b, (>>= b) ∘ a

  infixr ` >=> `:55 := kleisli
end monad

instance : monad.{u u} id :=
{pure := @id, bind := λ _ _ x f, f x,
 id_map := by intros; refl,
 pure_bind := by intros; refl,
 bind_assoc := by intros; refl}

def reader_t (r : Type u) (m : Type u → Type v) [monad m] (α : Type u) : Type (max u v) :=
r → m α

@[reducible] def reader (r : Type u) := reader_t r id

open monad
namespace reader_t
section
  variable  {r : Type u}
  variable  {m : Type u → Type v}
  variable  [monad m]
  variables {α β : Type u}

  protected def ask : reader_t r m r :=
  λ r, pure r

  protected def run : r → reader_t r m α → m α :=
  λ r x, x r

  protected def pure (a : α) : reader_t r m α :=
  λ r, pure a

  protected def bind (x : reader_t r m α) (f : α → reader_t r m β) : reader_t r m β :=
  λ r, do a ← x r,
          f a r

  local attribute [simp] reader_t.bind reader_t.pure monad.bind_pure monad.pure_bind monad.bind_assoc

  instance : monad (reader_t r m) :=
  {pure := @reader_t.pure _ _ _, bind := @reader_t.bind _ _ _,
   id_map := by intros; simp [function.comp],
   pure_bind := by intros; simp,
   bind_assoc := by intros; simp}

  protected def lift (a : m α) : reader_t r m α :=
  λ r, a

  instance : monad_transformer (reader_t r) :=
  {is_monad := @reader_t.monad r, monad_lift := @reader_t.lift r}
end
end reader_t

--instance (r r' m α) [monad m] [has_coe r' r] : has_coe (reader_t r m α) (reader_t r' m α) :=
--⟨λ x r, x r⟩

def with_reader_t {r r' m α} [monad m] (f : r' → r) : reader_t r m α → reader_t r' m α :=
λ x r, x (f r)

def map_reader_t {r m m' α β} [monad m] [monad m'] (f : m α → m' β) : reader_t r m α → reader_t r m' β :=
λ x r, f (x r)

protected def state_t.run {σ α : Type u} {m : Type u → Type v} [monad m] (st : σ) (x : state_t σ m α) : m (α × σ) :=
x st

protected def state.run {σ α : Type u} (st : σ) (x : state_t σ id α) : α × σ :=
state_t.run st x

def with_state_t {σ σ' α : Type u} {m : Type u → Type u} [monad m] (f : σ → σ') : state_t σ' m α → state_t σ m α :=
λ x st, (λ p : α × σ', (prod.fst p, st)) <$> x (f st)

class monad_state (s : inout Type u) (m : Type u → Type v) :=
[monad_m : monad m]
(read : m s)
(write : s → m punit)
--attribute [instance] monad_state.monad_m

@[inline] def read {σ m} [monad_state σ m] : m σ := monad_state.read _ _
@[inline] def write {σ m} [monad_state σ m] : σ → m punit := monad_state.write _
@[inline] def modify {σ m} [monad_state σ m] [monad m] (f : σ → σ) : m punit :=
do s ← read, write (f s)

instance (s m) [monad m] : monad_state s (state_t s m) :=
{read := state_t.read, write := state_t.write'}

instance monad_state_lift (s m m') [has_monad_lift m m'] [monad_state s m] [monad m] [monad m'] : monad_state s m' :=
{read := monad_lift (read : m _),
 write := monad_lift ∘ (write : _ → m _)}

class monad_error (ε : inout Type u) (m : Type v → Type w) :=
[monad_m : monad m]
(fail : Π {α : Type v}, ε → m α)

@[inline] def fail {ε m α} [monad_error ε m] : ε → m α := monad_error.fail _

instance (ε) : monad_error ε (except ε) :=
{fail := @except.error _}

instance monad_error_lift (ε m m') [has_monad_lift m m'] [monad_error ε m] [monad m] [monad m'] : monad_error ε m' :=
{fail := λ _, monad_lift ∘ @fail _ m _ _}

def unreachable {α m} [monad_error string m] : m α :=
fail "unreachable"

class monad_reader (r : inout Type u) (m : Type u → Type v) :=
[monad_m : monad m]
(ask : m r)

@[inline] def ask {r m} [monad_reader r m] : m r := monad_reader.ask _ _

instance (r m) [monad m] : monad_reader r (reader_t r m) :=
{ask := reader_t.ask}

instance monad_reader_lift (r m m') [has_monad_lift m m'] [monad_reader r m] [monad m] [monad m'] : monad_reader r m' :=
{ask := monad_lift (ask : m _)}
