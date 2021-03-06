import macro
import hygiene

def sp : option span := none

def lambda_macro := {macro .
  name := "lambda",
  resolve := some $ λ sc node,
  do [syntax.ident ident, body] ← pure node.args
       | unreachable,
     pure [sc, sc.insert (ident.name, ident.msc) ident.id]}

def resolve_name (msc : option macro_scope_id) (sc : scope) : name → option resolved
| (name.mk_string s n) :=
do {
  decl ← sc.find (n.mk_string s, msc),
  pure ⟨sum.inl decl, n.mk_string s⟩
} <|> resolve_name n
| _ := none

def ref_macro := {macro .
  name := "ref",
  resolve := some $ λ sc node,
  do [syntax.ident ident] ← pure node.args
       | unreachable,
     some resolved ← pure $ resolve_name ident.msc sc ident.name
       | throw sformat!"unknown identifier {ident.name}",
     modify (λ st, ⟨st.resolve_map.insert ident.id resolved⟩),
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

def cfg : parse_state :=
{macros := rbmap.from_list $ [lambda_macro, ref_macro, intro_x_macro].map (λ m, (m.name, m)),
 resolve_cfg := {global_scope := mk_rbmap _ _}}

meta def test (stx : syntax) : command :=
match (expand' stx >>= resolve').run' cfg () with
| except.error e := tactic.fail e
| except.ok    (stx, ⟨rsm⟩) := tactic.trace stx >> tactic.trace (stx, rsm)
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

-- test α_conv
run_cmd
let stx := syntax.node ⟨0, sp, "lambda", [
  syntax.ident ⟨1, sp, `x.y, none⟩,
  syntax.node ⟨2, sp, "ref", [
    syntax.ident ⟨3, sp, `x.y.z, none⟩
  ]⟩
]⟩ in
match (expand' stx >>= resolve').run' cfg () with
| except.ok (_, ⟨rsm⟩) := tactic.trace (α_conv rsm (λ id, if id = 1 then `a else `b) stx)
| except.error _ := tactic.skip
end
