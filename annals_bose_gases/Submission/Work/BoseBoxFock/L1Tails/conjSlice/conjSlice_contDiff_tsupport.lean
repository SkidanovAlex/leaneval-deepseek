import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Submission.Work.BoseBoxFock.L1Tails.DefsC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.L1Tails.conjSlice

/-- The complex-conjugate slice `w ↦ conj (H w y)` of a smooth box-supported kernel is `C¹` and
still box-supported.  Route: `w ↦ H w y = (Function.uncurry H) ∘ (w ↦ (w,y))` is smooth
(`ContDiff.comp` with `contDiff_id.prod contDiff_const`), and `starRingEnd ℂ` is the continuous
`ℝ`-linear map `Complex.conjCLE` (so `ContDiff`); the support statement is
`closure_minimal (fun w hw => (hHs w y (by simpa using hw)).1) (boxL_compact ℓ).isClosed`. -/
theorem conjSlice_contDiff_tsupport {ℓ : ℝ}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H))
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ)
    (y : EuclideanSpace ℝ (Fin 3)) :
    ContDiff ℝ 1 (fun w => (starRingEnd ℂ) (H w y)) ∧
      tsupport (fun w => (starRingEnd ℂ) (H w y)) ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
  -- `starRingEnd ℂ` is the continuous `ℝ`-linear map `Complex.conjCLE`, hence `C¹`.
  have hconj : ContDiff ℝ 1 (fun z : ℂ => (starRingEnd ℂ) z) := by
    have h : (fun z : ℂ => (starRingEnd ℂ) z) = (Complex.conjCLE : ℂ → ℂ) := by
      funext z
      exact (Complex.conjCLE_apply z).symm
    rw [h]
    exact ContinuousLinearMap.contDiff (Complex.conjCLE : ℂ →L[ℝ] ℂ)
  refine ⟨?_, ?_⟩
  · -- `w ↦ H w y = (Function.uncurry H) ∘ (w ↦ (w, y))` is smooth.
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun w : EuclideanSpace ℝ (Fin 3) => (w, y)) :=
      contDiff_id.prodMk contDiff_const
    have hcomp := hH.comp hmap
    exact hconj.comp (hcomp.of_le (by simp))
  · -- `conj` kills nothing, so the support does not grow.
    rw [tsupport]
    exact closure_minimal (fun w hw => (hHs w y (by simpa using hw)).1)
      (Work.BoseK15.corpusBox.boxL_compact ℓ).isClosed

end Work.BoseBoxFock.L1Tails.conjSlice
