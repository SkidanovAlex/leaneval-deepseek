import Mathlib
import Submission.Work.WilE9G.Sard.rankDefs

set_option autoImplicit false

noncomputable section

namespace Work.WilE9G.Sard

theorem hasFDerivAt_chart {d m : ℕ} (f : (Fin (d + 1) → ℝ) → (Fin (m + 1) → ℝ))
    (i : Fin (m + 1)) (j : Fin (d + 1)) (x₀ : Fin (d + 1) → ℝ) (hf : DifferentiableAt ℝ f x₀) :
    HasFDerivAt (chart f i j) (dchart f i j x₀) x₀ := by
  have h1 : HasFDerivAt (fun z => crj j z) (kdrj j) x₀ :=
    (ContinuousLinearMap.hasFDerivAt (kdrj j)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => kdrj_apply j z)
  have h2 : HasFDerivAt (fun z => f z i)
      ((ContinuousLinearMap.proj (R := ℝ) i).comp (fderiv ℝ f x₀)) x₀ := by
    have hh := (ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.proj (R := ℝ) i)).comp x₀ hf.hasFDerivAt
    simpa [ContinuousLinearMap.proj_apply, Function.comp_def] using hh
  have h := h1.prodMk h2
  exact h

end Work.WilE9G.Sard
