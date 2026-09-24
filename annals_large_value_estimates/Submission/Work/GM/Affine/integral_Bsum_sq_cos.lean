import Mathlib
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.autocorr_eq_spectral

open MeasureTheory

namespace Work.GM.Affine

theorem integral_Bsum_sq_cos {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {f : ℝ → ℝ} (hf : Continuous f)
    (hsup : SuppHyp C₀ f) {M₂ : ℝ} (hM₂ : 0 < M₂) (k : ℤ) :
    (∫ x : ℝ, ‖Bsum f M₂ x‖ ^ 2 * Real.cos (2 * Real.pi * (k : ℝ) * x))
      = ∫ v : ℝ, Hprof f M₂ v * Hprof f M₂ (v + (k : ℝ)) := by
  have hcont : Continuous (Hprof f M₂) := Hprof_continuous hf M₂
  have hcs : HasCompactSupport (Hprof f M₂) := Hprof_hasCompactSupport hsup hC₀ hM₂.le
  have key := autocorr_eq_spectral hcont hcs (k : ℝ)
  rw [key]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  show ‖Bsum f M₂ x‖ ^ 2 * Real.cos (2 * Real.pi * (k : ℝ) * x)
      = ‖Fhat (Hprof f M₂) x‖ ^ 2 * Real.cos (2 * Real.pi * x * (k : ℝ))
  rw [Bsum_eq_Fhat_Hprof hf hsup hC₀ hM₂ x,
      show 2 * Real.pi * (k : ℝ) * x = 2 * Real.pi * x * (k : ℝ) by ring]

end Work.GM.Affine
