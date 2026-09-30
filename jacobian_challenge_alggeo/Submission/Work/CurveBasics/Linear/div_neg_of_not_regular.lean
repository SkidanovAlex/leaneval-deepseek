import Mathlib
import Submission.Work.CurveBasics.Basic
import Submission.Work.CurveBasics.Place
import Submission.Work.CurveBasics.Place.Coheight
import Submission.Work.CurveBasics.Place.isDiscreteValuationRing
import Submission.Work.CurveBasics.Order

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Linear

open CategoryTheory AlgebraicGeometry
open scoped Classical
open Work.CurveBasics

/-- **Converse of `Ring.ordFrac_ge_one_of_ne_zero`.**  Let `R` be a discrete valuation ring with
fraction field `K`.  If `1 ≤ Ring.ordFrac R x` for `x : K`, then `x` lies in the image of the
canonical map `R → K`.

Indeed `Ring.ordFrac R x` is the inverse of the adic valuation of the maximal ideal
(`Ring.ordFrac_eq_valuation_inv`), so `1 ≤ (v x)⁻¹` forces `v x ≤ 1` (`one_le_inv_iff₀`, which
also gives `0 < v x`, so there is no trouble at the zero case).  An element of the fraction field
with `v x ≤ 1` comes from `R` (`IsDiscreteValuationRing.exists_lift_of_le_one`). -/
lemma exists_algebraMap_eq_of_one_le_ordFrac {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {x : K} (h : 1 ≤ Ring.ordFrac R x) : ∃ a : R, algebraMap R K a = x := by
  refine IsDiscreteValuationRing.exists_lift_of_le_one ?_
  rw [Ring.ordFrac_eq_valuation_inv] at h
  exact (one_le_inv_iff₀.mp h).2

/-- If `h` is not regular at the place `Q` (i.e. `h` is not in the image of the canonical map
`O_{C,Q} → K(C)`), then `h` has a pole at `Q`: the coefficient of `Q` in `C.div h` is negative.

Proof sketch: `Q.point` is a closed point, so `coheight Q.point = 1` (`Place.eq_coheight_one`)
and the stalk `O_{C,Q}` is a discrete valuation ring (`Place.isDiscreteValuationRing`) with
fraction field `K(C)` (`IsFractionRing` instance from Mathlib's
`AlgebraicGeometry/FunctionField.lean`). Since `0` is in the image, `hh` gives `h ≠ 0`. The
missing step is the converse of `Ring.ordFrac_ge_one_of_ne_zero`: for a DVR `R` with fraction
field `K` and `x ≠ 0`, `1 ≤ Ring.ordFrac R x` implies `x` lies in the image of `R → K` (use
`Ring.ordFrac_eq_valuation_inv` and the fact that the valuation ring is `R` itself). Hence the
hypothesis implies `Ring.ordFrac (O_{C,Q}) h < 1`, which by
`Scheme.ord_eq_ordHom_of_coheight_eq_one` means `Scheme.ord h Q.point < 0`, hence
`C.div h Q < 0` by `Curve.div_apply`. -/
theorem div_neg_of_not_regular {k : Type*} [Field k] (C : Curve k) {Q : C.Place}
    {h : C.functionField}
    (hh : ¬ ∃ s : C.left.presheaf.stalk Q.point, algebraMap _ _ s = h) :
    C.div h Q < 0 := by
  rw [Curve.div_apply]
  by_contra hle
  -- `h` is regular at `Q` because it is nonnegative order there, contradicting `hh`.
  have hge : (0 : ℤ) ≤ Scheme.ord h Q.point := le_of_not_gt hle
  -- `0` is regular, so `hh` forces `h ≠ 0`.
  have hne : h ≠ 0 := fun h0 => hh ⟨0, by simp [h0]⟩
  have hz : Order.coheight Q.point = 1 := Q.eq_coheight_one
  have hIVR : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) :=
    Work.CurveBasics.Place.isDiscreteValuationRing Q
  -- Nonnegativity of the order is exactly `1 ≤ ordFrac` of the local ring at `Q`.
  have h1 : (1 : WithZero (Multiplicative ℤ)) ≤
      Ring.ordFrac (C.left.presheaf.stalk Q.point) h := by
    have := (Scheme.le_ord_iff hz hne (n := 0)).mp hge
    simpa [Scheme.ordHom] using this
  -- ... and `1 ≤ ordFrac` means that `h` comes from the local ring, i.e. is regular at `Q`.
  exact hh (exists_algebraMap_eq_of_one_le_ordFrac h1)

end Work.CurveBasics.Linear
