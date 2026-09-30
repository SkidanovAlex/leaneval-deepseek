import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.Curve.BCSquare.range_germ_baseChange
import Submission.Work.CurveBasics.Curve.BCSquare.ordAt_fieldMap
import Submission.Work.CurveBasics.BaseChange.mem_range_germ_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.unusedVariables false

namespace Work.CurveBasics.Curve.BCSquare


open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
/-- **The local statement of flat base change for `L(D)`.**

Let `S : BCSquare C C'` be a base-change square of curves and let `W ⊆ C` be a nonempty
affine open subset on which `t ≠ 0` is a local equation of `-D`, i.e. `ord_Q t = -D Q` for
every place `Q` of `C` lying in `W`.  Then the `S.fieldMap t`-multiples of the functions
regular on `S.preimage W` are exactly the `F`-span of the images of the `t`-multiples of the
functions regular on `W`.

Since `range_germ_baseChange` identifies the subring of `K(C')` of functions regular on
`S.preimage W` with the `F`-span of the image of the subring of `K(C)` of functions regular
on `W`, this is a purely linear-algebraic statement: multiplication by the fixed element
`S.fieldMap t` is `F`-linear and commutes with forming spans, and it intertwines
`S.fieldMap` with multiplication by `t`. -/
theorem L_divMap_local {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') (D : Curve.Div C)
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    (t : C.functionField) (ht : t ≠ 0)
    (htord : ∀ Q : Curve.Place C, Q.point ∈ W → C.ordAt t Q = -D Q) :
    {f : C'.functionField | ∃ g ∈ (C'.germToFunctionField (S.preimage W)).hom.range,
        f = S.fieldMap.hom t * g} =
      Submodule.span F (S.fieldMap.hom '' {g : C.functionField |
        ∃ g' ∈ (C.germToFunctionField W).hom.range, g = t * g'}) := by
  classical
  -- the subring of functions regular on `W`, and its analogue on `S.preimage W`
  set A : Subring C.functionField := (C.germToFunctionField W).hom.range with hA
  set A' : Subring C'.functionField := (C'.germToFunctionField (S.preimage W)).hom.range with hA'
  -- the set of `t`-multiples of the latter
  set T : Set C.functionField := {g : C.functionField | ∃ g' ∈ A, g = t * g'} with hT
  -- multiplication by `S.fieldMap t`, as an `F`-linear endomorphism of `K(C')`
  let φ : C'.functionField →ₗ[F] C'.functionField := LinearMap.mulLeft F (S.fieldMap.hom t)
  -- flat base change of the regularity condition
  have hspan : (A' : Set C'.functionField)
      = ↑(Submodule.span F (S.fieldMap.hom '' (A : Set C.functionField))) :=
    range_germ_baseChange S W hW
  -- the left hand side is the image of `A'` under `φ`
  have hL1 : {f : C'.functionField | ∃ g ∈ A', f = S.fieldMap.hom t * g} = φ '' ↑A' := by
    ext f; constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, SetLike.mem_coe.mpr hg, LinearMap.mulLeft_apply F _ g⟩
    · rintro ⟨g, hg, hfg⟩
      exact ⟨g, SetLike.mem_coe.mp hg, hfg.symm.trans (LinearMap.mulLeft_apply F _ g)⟩
  -- `φ` intertwines `S.fieldMap` with multiplication by `t`
  have hgen : φ '' (S.fieldMap.hom '' (A : Set C.functionField)) = S.fieldMap.hom '' T := by
    ext y; constructor
    · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨t * a, ⟨a, ha, rfl⟩, by rw [map_mul, LinearMap.mulLeft_apply]⟩
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨a, ha, rfl⟩ := hg
      exact ⟨S.fieldMap.hom a, ⟨a, ha, rfl⟩, by rw [map_mul, LinearMap.mulLeft_apply]⟩
  -- `φ` commutes with `F`-spans (`Submodule.map_span`), giving the result
  rw [hL1, hspan, ← Submodule.map_coe φ, Submodule.map_span, hgen]

end Work.CurveBasics.Curve.BCSquare
