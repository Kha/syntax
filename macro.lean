import syntax

open except
open state

attribute [instance] name.has_lt_quick option.has_lt

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

def expand' (stx : syntax) : syntax :=
(expand 1000 stx {next_tag := 0}).1

def resolve' (stx : syntax) : except string (syntax × resolve_map) :=
let sc : scope := mk_rbmap _ _ _,
    resolve_map : resolve_map := mk_rbmap _ _ _ in
    do ⟨(), rsm⟩ ← resolve sc stx resolve_map,
       pure (stx, rsm)
end
