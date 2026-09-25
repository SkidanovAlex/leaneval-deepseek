import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmKernel_divergence_aux

namespace Work.CR.Flat.Cauchy

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-- **The left-hand side of the Bochner–Martinelli formula for `ε → 0⁺`.**
The regularised kernel `bmKerEps k ε` converges pointwise to the singular kernel
`bmKernel k` (`bmKerEps_tendsto`) and is dominated by it (`norm_bmKerEps_le`); since
`x ↦ ‖bmKernel k x * ∂̄_k g x‖` is integrable (`integrable_bmKernel_mul_dbarCoord`), the
Lebesgue dominated convergence theorem gives the convergence of the integrals. -/
theorem bmLhs_tendsto_eps {n : ℕ} (hn : 0 < n) {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hg : ContDiff ℝ 1 g) (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0) (k : Fin n) :
    Filter.Tendsto (fun ε : ℝ => ∫ x, bmKerEps k ε x * dbarCoord k g x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ x, bmKernel k x * dbarCoord k g x)) := by
  have hbdd : Integrable (fun x => ‖bmKernel k x * dbarCoord k g x‖) :=
    (integrable_bmKernel_mul_dbarCoord hn hg hsupp k).norm
  have hF : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      AEStronglyMeasurable (fun x : Fin n → ℂ => bmKerEps k ε x * dbarCoord k g x)
        volume := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have h1 : Continuous (fun x : Fin n → ℂ => bmKerEps k ε x) :=
      continuous_bmKerEps k (ne_of_gt hε)
    have h2 : Continuous (fun x : Fin n → ℂ => dbarCoord k g x) := continuous_dbarCoord hg k
    exact (h1.mul h2).aestronglyMeasurable
  have hbd : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ᵐ x : Fin n → ℂ ∂volume,
        ‖bmKerEps k ε x * dbarCoord k g x‖ ≤ ‖bmKernel k x * dbarCoord k g x‖ := by
    filter_upwards with ε
    filter_upwards with x
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_bmKerEps_le k ε x) (norm_nonneg _)
  have hlim : ∀ᵐ x : Fin n → ℂ ∂volume,
      Tendsto (fun ε : ℝ => bmKerEps k ε x * dbarCoord k g x)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (bmKernel k x * dbarCoord k g x)) := by
    filter_upwards with x
    exact (bmKerEps_tendsto k x).mul_const (dbarCoord k g x)
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖bmKernel k x * dbarCoord k g x‖) hF hbd hbdd hlim

end Work.CR.Flat.Cauchy
