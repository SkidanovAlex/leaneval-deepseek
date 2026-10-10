import Submission.Work.CY3.Link
import Submission.Work.CY3.resEquiv_genericPoint_birationalMap

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3.Bridge` — how to discharge the `ℙ¹`-bundle bridge of the CY3 link

`Work.CY3.CY3Data.bridge` is the field

```
bridge : ResEquiv 𝕜 y x → StablyBirational 𝕜 Z Z'
```

i.e. "an isomorphism of the function fields of the two exceptional divisors makes the two centres
stably birational".  It is the abstract form of the paper's geometric statement

* the exceptional divisor of `Bl_{Z_𝕜}` is birational to `ℙ¹ × Z_𝕜` (and symmetrically with `Z'_𝕜`),

which comes from `lemma:L-link` (2) and (L3): the exceptional divisor of the blow-up along the
connected centre `Z_𝕜` is irreducible, and `τ⁻¹(Z_𝕜) → Z_𝕜` is a `ℙ¹`-fibration, so that divisor is
birational to `ℙ¹ × Z_𝕜`.

This file proves that the paper's geometric statement **implies** the field `bridge`, in the form in
which a producer can supply it: a model `W` of `Z × 𝔸¹` (or `Z × ℙ¹`) whose generic point has the
function field of the exceptional divisor `y`, and likewise for `x` and `Z' × 𝔸¹`.  The two
ingredients are

* the transitivity of `ResEquiv` (`Work.Motivic.ResEquiv`), and
* `Work.CY3.resEquiv_genericPoint_birationalMap` — the (F2)/(F3) step of
  `Submission/Work/LLink/NOTES.md` §6, proved in this directory: a `𝕜`-isomorphism of the function
  fields of two `𝕜`-varieties is a birational map between them.

*Technical remark.*  The two `Variety` instances of the products `Z × 𝔸¹`, `Z' × 𝔸¹` are taken as
explicit hypotheses rather than as instance arguments: `Work.CY3.StablyBirational` (following
`Work.K3.StablyBirational`) records them existentially, and writing `genericPoint` of such a
product inside a statement triggers a Mathlib instance-search blow-up (the `Over`/`IrreducibleSpace`
search on `AffineSpace`-products does not terminate within the heartbeat budget).  With the
instances in hand the statement below is proved directly.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.CY3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- **The `ℙ¹`-bundle description of the two exceptional divisors implies the bridge.**

Let `D` be CY3 data over `𝕜`, and let `W` be a model of `Z × 𝔸¹` (i.e. `W` is birational to
`Z × 𝔸¹`; `𝔸¹` is birational to `ℙ¹`, so this is the same as a model of `ℙ¹ × Z`), and `W'` a model
of `Z' × 𝔸¹`.  Suppose that the exceptional divisor `y` of `ψ⁻¹` has the function field of a
*generic point* of `W` (`hy` and `hw`), and that the exceptional divisor `x` of `ψ` has the function
field of a generic point of `W'` (`hx` and `hw'`) — this is the paper's "the exceptional divisor of
`Bl_{Z_𝕜}` is birational to `ℙ¹ × Z_𝕜`".

Then an isomorphism of the function fields of `x` and `y` makes the two centres stably birational,
i.e. the field `Work.CY3.CY3Data.bridge` holds.  Consequently a producer of `CY3Data` may supply
the *geometry* (the `ℙ¹`-bundle descriptions of the two exceptional divisors) instead of the
abstract implication — this is `NOTES.md` §9 (1). -/
theorem CY3Data.bridge_of_models (D : CY3Data 𝕜)
    (W W' : Scheme.{0}) [Variety 𝕜 W] [Variety 𝕜 W']
    (hZ : Variety 𝕜 (prodOver 𝕜 D.Z (Affine 𝕜 1)))
    (hZ' : Variety 𝕜 (prodOver 𝕜 D.Z' (Affine 𝕜 1)))
    (eW : Nonempty (W.BirationalMap (prodOver 𝕜 D.Z (Affine 𝕜 1))))
    (eW' : Nonempty (W'.BirationalMap (prodOver 𝕜 D.Z' (Affine 𝕜 1))))
    (w : W) (w' : W') (hw : ResEquiv 𝕜 w (genericPoint W))
    (hw' : ResEquiv 𝕜 w' (genericPoint W'))
    (hy : ResEquiv 𝕜 D.y w) (hx : ResEquiv 𝕜 D.x w') :
    ResEquiv 𝕜 D.y D.x → StablyBirational 𝕜 D.Z D.Z' := by
  intro h
  haveI := hZ
  haveI := hZ'
  -- the function fields of `y` and `x` are those of the generic points of the two models
  have hyw : ResEquiv 𝕜 D.y (genericPoint W) := Work.Motivic.ResEquiv.trans hy hw
  have hxw' : ResEquiv 𝕜 D.x (genericPoint W') := Work.Motivic.ResEquiv.trans hx hw'
  have hgen : ResEquiv 𝕜 (genericPoint W) (genericPoint W') :=
    Work.Motivic.ResEquiv.trans (Work.Motivic.ResEquiv.symm hyw)
      (Work.Motivic.ResEquiv.trans h hxw')
  -- isomorphic function fields ⟹ birational, and the two models are `Z × 𝔸¹`, `Z' × 𝔸¹`
  obtain ⟨γ⟩ := resEquiv_genericPoint_birationalMap hgen
  obtain ⟨e1⟩ := eW
  obtain ⟨e2⟩ := eW'
  exact ⟨1, 1, hZ, hZ', ⟨e1.symm.trans (γ.trans e2)⟩⟩

end

end Work.CY3
