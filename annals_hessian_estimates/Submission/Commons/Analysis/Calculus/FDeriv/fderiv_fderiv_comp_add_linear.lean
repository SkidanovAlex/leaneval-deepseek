import Mathlib
import Submission.Commons.Analysis.Calculus.fderiv_fderiv_comp_continuousLinearMap

namespace Commons.Analysis.Calculus.FDeriv

theorem fderiv_fderiv_comp_add_linear {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (x₀ : F) (f : F → ℝ)
    (hf : ContDiff ℝ 2 f) (y u v : E) :
    (fderiv ℝ (fderiv ℝ (fun y : E => f (x₀ + L y))) y) u v
      = (fderiv ℝ (fderiv ℝ f) (x₀ + L y)) (L u) (L v) := by
  have hgC : ContDiff ℝ 2 (fun z : F => f (x₀ + z)) :=
    hf.comp (contDiff_const.add contDiff_id)
  have key := Commons.Analysis.Calculus.fderiv_fderiv_comp_continuousLinearMap
    (E := E) (F := F) L (fun z : F => f (x₀ + z)) hgC y u v
  have key' : fderiv ℝ (fderiv ℝ (fun y : E => f (x₀ + L y))) y u v
      = fderiv ℝ (fderiv ℝ (fun z : F => f (x₀ + z))) (L y) (L u) (L v) := by
    simpa using key
  rw [key']
  have h1 : fderiv ℝ (fun z : F => f (x₀ + z)) = fun z : F => fderiv ℝ f (x₀ + z) := by
    funext z
    exact fderiv_comp_add_left x₀
  have h2 : fderiv ℝ (fderiv ℝ (fun z : F => f (x₀ + z)))
      = fun z : F => fderiv ℝ (fderiv ℝ f) (x₀ + z) := by
    rw [h1]
    funext z
    exact fderiv_comp_add_left x₀
  have h3 : fderiv ℝ (fderiv ℝ (fun z : F => f (x₀ + z))) (L y)
      = fderiv ℝ (fderiv ℝ f) (x₀ + L y) := by
    rw [h2]
  rw [h3]

end Commons.Analysis.Calculus.FDeriv
