import Mathlib
import Submission.Work.CurveBasics.Point.isClosed_of_coheight_eq_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace Work.SpecLin.Alt

/-- A nonzero prime ideal of the section ring of an affine chart `U` of a curve defines a
closed point of the curve.

Indeed, the point `hU.fromSpec q` of `U` is the generic point of the curve precisely when
`q` is the generic point of `Spec Γ(U)`, i.e. (`Γ(U)` being a domain) when `q = ⊥`.  Every
point of a curve is either the generic point or a closed point
(`Work.CurveBasics.Curve.eq_genericPoint_or_isClosed`), so for `q ≠ ⊥` the point is closed. -/
theorem isClosed_fromSpec_of_ne_bot {k : Type _} [Field k] (C : Work.CurveBasics.Curve k)
    (U : C.left.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) [Nonempty U]
    (q : PrimeSpectrum (C.left.presheaf.obj (Opposite.op U))) (hq : q.asIdeal ≠ ⊥) :
    IsClosed ({hU.fromSpec q} : Set C.left) := by
  -- Work with `q` as a point of the scheme `Spec Γ(C.left, U)`.
  let q' : ↥(Spec Γ(C.left, U)) := q
  -- The generic point of the curve lies in the nonempty open chart `U`.
  have hηU : genericPoint C.left ∈ U :=
    ((genericPoint_spec C.left).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U))
  -- The prime of the generic point in the chart is the bottom prime ideal.
  have hgen' : hU.primeIdealOf (⟨genericPoint C.left, hηU⟩ : U) =
      genericPoint (Spec Γ(C.left, U)) := hU.primeIdealOf_genericPoint
  have hgen : hU.primeIdealOf (⟨genericPoint C.left, hηU⟩ : U) =
      (⊥ : PrimeSpectrum ↑Γ(C.left, U)) := by
    rw [hgen']
    exact genericPoint_eq_bot_of_affine _
  -- `primeIdealOf` inverts `fromSpec` on points.
  have hprime : hU.primeIdealOf (hU.isoSpec.inv q') = q := by
    change hU.isoSpec.hom (hU.isoSpec.inv q') = q
    rw [← Scheme.Hom.comp_apply, hU.isoSpec.inv_hom_id]
    rfl
  -- The point `hU.fromSpec q` is not the generic point.
  have hne : hU.fromSpec q' ≠ genericPoint C.left := by
    intro h
    have hsub : hU.isoSpec.inv q' = ⟨genericPoint C.left, hηU⟩ := by
      apply Subtype.ext
      exact h
    have hbot : q = ⊥ := by rw [← hprime, hsub, hgen]
    exact hq (by simpa using congrArg PrimeSpectrum.asIdeal hbot)
  -- Every point of a curve is the generic point or a closed point.
  rcases lt_or_eq_of_le (C.coheight_le_one (hU.fromSpec q')) with hlt | heq
  · exact absurd (Order.lt_one_iff.mp hlt)
      (fun h0 => hne (C.eq_genericPoint_of_coheight_eq_zero h0))
  · have hcl : IsClosed ({hU.fromSpec q'} : Set C.left) :=
      Work.CurveBasics.Point.isClosed_of_coheight_eq_one C heq
    simpa using hcl

end Work.SpecLin.Alt
