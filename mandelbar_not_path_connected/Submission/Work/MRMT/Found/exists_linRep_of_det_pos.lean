import Mathlib
import Submission.Work.MRMT.QC.lintegral_norm_dz_le_volume_image
import Submission.Work.MRMT.Wirtinger.dz_comp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- Every real-linear endomorphism `A` of `ℂ` whose (real) determinant is positive can be
written as `z ↦ α z + β \bar z` with `‖β‖ < ‖α‖`:  take `α = ∂A`, `β = ∂̄A`, the Wirtinger
derivatives of `A`, for which `det A = ‖α‖² - ‖β‖²`. -/
theorem exists_linRep_of_det_pos {A : ℂ →L[ℝ] ℂ} (hA : 0 < A.det) :
    ∃ α β : ℂ, ‖β‖ < ‖α‖ ∧ ∀ z : ℂ, A z = α * z + β * (starRingEnd ℂ) z := by
  refine ⟨(A 1 - Complex.I * A Complex.I) / 2, (A 1 + Complex.I * A Complex.I) / 2, ?_, ?_⟩
  · -- `det A = ‖α‖² - ‖β‖² > 0`, hence `‖β‖² < ‖α‖²` and `‖β‖ < ‖α‖`.
    have hdet := Work.MRMT.QC.clm_det_eq_normSq (L := A)
    have hsq : ‖(A 1 + Complex.I * A Complex.I) / 2‖ ^ 2
        < ‖(A 1 - Complex.I * A Complex.I) / 2‖ ^ 2 := by
      linarith [hdet]
    have habs : |‖(A 1 + Complex.I * A Complex.I) / 2‖|
        < |‖(A 1 - Complex.I * A Complex.I) / 2‖| := sq_lt_sq.mp hsq
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at habs
    exact habs
  · -- the Wirtinger decomposition of an `ℝ`-linear map `ℂ → ℂ`.
    intro z
    exact Work.MRMT.Wirtinger.realLinearMap_apply_eq A z

end Work.MRMT.Found
