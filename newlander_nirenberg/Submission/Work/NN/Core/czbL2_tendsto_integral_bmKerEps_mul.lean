import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmKernel_divergence_aux
import Submission.Work.CR.Flat.Cauchy.bmPotential_contDiff_one
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Cauchy.bmCZDefs

namespace Work.NN.Core

open MeasureTheory Set Filter
open scoped Topology

/-- Integrability of `bmKernel k · f` for a continuous compactly supported `f`. -/
private lemma integrable_bmKernel_mul_of {n : ℕ} (hn : 0 < n) (k : Fin n)
    {f : (Fin n → ℂ) → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel k x * f x) := by
  have h := (Work.CR.Flat.Cauchy.locallyIntegrable_bmKernel hn k)
    |>.integrable_smul_left_of_hasCompactSupport hf hfc
  simpa only [smul_eq_mul, mul_comm] using h

theorem czbL2_tendsto_integral_bmKerEps_mul {n : ℕ} (hn : 0 < n)
    {f : (Fin n → ℂ) → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (k : Fin n) :
    Filter.Tendsto (fun ε : ℝ => ∫ x, Work.CR.Flat.Cauchy.bmKerEps k ε x * f x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ x, Work.CR.Flat.Cauchy.bmKernel k x * f x)) := by
  have hbdd : Integrable (fun x : Fin n → ℂ => ‖Work.CR.Flat.Cauchy.bmKernel k x * f x‖) :=
    (integrable_bmKernel_mul_of hn k hf hfc).norm
  have hF : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      AEStronglyMeasurable
        (fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKerEps k ε x * f x) volume := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ((Work.CR.Flat.Cauchy.continuous_bmKerEps k (ne_of_gt hε)).mul hf).aestronglyMeasurable
  have hbd : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ᵐ x : Fin n → ℂ ∂volume,
        ‖Work.CR.Flat.Cauchy.bmKerEps k ε x * f x‖ ≤ ‖Work.CR.Flat.Cauchy.bmKernel k x * f x‖ := by
    filter_upwards with ε
    filter_upwards with x
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (Work.CR.Flat.Cauchy.norm_bmKerEps_le k ε x) (norm_nonneg _)
  have hlim : ∀ᵐ x : Fin n → ℂ ∂volume,
      Filter.Tendsto (fun ε : ℝ => Work.CR.Flat.Cauchy.bmKerEps k ε x * f x)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Work.CR.Flat.Cauchy.bmKernel k x * f x)) := by
    filter_upwards with x
    exact (Work.CR.Flat.Cauchy.bmKerEps_tendsto k x).mul_const (f x)
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖Work.CR.Flat.Cauchy.bmKernel k x * f x‖) hF hbd hbdd hlim

end Work.NN.Core
