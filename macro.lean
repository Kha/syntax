import syntax

open except
open state

attribute [instance] name.has_lt_quick option.has_lt

--@[reducible] def parse_m (r σ) := reader_t r $ state_t σ $ except string

structure resolved :=
-- local or global
(decl : syntax_id ⊕ name)
/- prefix of the reference that corresponds to the decl. All trailing name components
   are field accesses. -/
(«prefix» : name)

meta instance : has_to_format resolved := ⟨λ r, to_fmt (r.decl, r.prefix)⟩

structure resolve_cfg :=
(global_scope : rbmap name syntax)

@[reducible] def resolve_map := rbmap syntax_id resolved

structure resolve_state :=
(resolve_map : resolve_map)

def scope := rbmap (name × option macro_scope_id) syntax_id

@[reducible] def resolve_m := reader_t resolve_cfg $ state_t resolve_state $ except string

def exp_fuel := 1000

structure macro :=
(name : name)
-- (read : reader)
-- TODO: What else does an expander need? How to model recursive expansion?
(expand : option (syntax_node syntax → syntax) := none)
(resolve : option (scope → syntax_node syntax → resolve_m (list scope)) := none)
-- (elaborate : list syntax → expr → tactic expr)

structure parse_state :=
(macros : rbmap name macro)
(resolve_cfg : resolve_cfg)

@[reducible] def parse_m := state_t parse_state id

-- identifiers in macro expansions are annotated with incremental tags
structure expand_state :=
(next_tag : ℕ)

@[reducible] def exp_m := reader_t parse_state $ state_t expand_state $ except string

def mk_tag : exp_m ℕ :=
do st ← read,
   write {st with next_tag := st.next_tag + 1},
   pure st.next_tag

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
do cfg ← reader_t.read,
   some {expand := some exp, ..} ← pure $ cfg.macros.find node.m
     | (λ args, syntax.node {node with args := args}) <$> node.args.mmap (expand fuel),
   tag ← mk_tag,
   let node := {node with args := node.args.map $ flip_tag tag},
   -- expand recursively
   expand fuel $ flip_tag tag $ exp node
| _ stx := pure stx

@[reducible] def resolve_m' := reader_t parse_state $ state_t resolve_state $ except string

--instance (r r' m α) [monad m] [has_coe r' r] : has_coe (reader_t r m α) (reader_t r' m α) :=
--⟨λ x r, x r⟩

def resolve : scope → syntax → resolve_m' unit
| sc (syntax.node node) :=
do cfg ← reader_t.read,
   some {resolve := some res, ..} ← pure $ cfg.macros.find node.m
     | node.args.mmap' $ resolve sc,
   arg_scopes ← with_reader_t parse_state.resolve_cfg $ res sc node,
   (arg_scopes.zip node.args).mmap' -- (uncurry resolve)
                                    (λ ⟨sc, stx⟩, resolve sc stx)
| _ _ := pure ()
using_well_founded { dec_tac := tactic.admit }

def expand' (stx : syntax) : reader_t parse_state (except string) syntax :=
map_reader_t (λ st, prod.fst <$> state_t.run {expand_state . next_tag := 0} st) (expand 1000 stx)

def resolve' (stx : syntax) : reader_t parse_state (except string) (syntax × resolve_state) :=
let sc : scope := mk_rbmap _ _ _,
    st : resolve_state := ⟨mk_rbmap _ _ _⟩ in
    do ⟨(), rsm⟩ ← map_reader_t (state_t.run st) $ resolve sc stx,
       pure (stx, rsm)