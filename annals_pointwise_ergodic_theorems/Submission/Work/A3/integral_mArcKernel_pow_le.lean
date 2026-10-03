import Mathlib
import Submission.Work.A3.majorArcKernel
import Submission.Work.A3.min_rpow_integral_bound
import Submission.Work.A3.integrable_min_rpow

/-!
# The `β`-integral of a power of the major-arc kernel

This module proves the `β`-integral bound used by the major-arc computation of Area A3:

  `∫_ℝ (mArcKernel N d β)^{2s} dβ ≤ K^{2s} N^{2s-d}`

for `d ≥ 2`, `d < 2s` and `N ≥ 1`, with a constant `K > 0` that is **uniform in `N` and in `s`**.

Since `mArcKernel N d β = (|β| + N^{-d})^{-1/d}` is at most `min (N) (|β|^{-1/d})` pointwise off the
single point `β = 0` (`mArcKernel_le_N`, `mArcKernel_le`), the bound is the `C = 1` case of
`Work.A3.min_rpow_integral_bound` transferred along the a.e. inequality
`0 ≤ f ≤ᵐ min_kernel` via `integral_mono_of_nonneg` (which only needs the integrability of the
*dominating* function, `integrable_min_rpow`).
-/

set_option autoImplicit false

namespace Work.A3

open MeasureTheory

noncomputable section

/-- **The `β`-integral of `(mArcKernel N d β)^{2s}`.**  The pointwise domination of the kernel by
`min N (|β|^{-1/d})` (valid off the null set `{0}`) reduces the estimate to
`Work.A3.min_rpow_integral_bound` with `C = 1`. -/
theorem integral_mArcKernel_pow_le {d s : ℕ} (hd : 2 ≤ d) (hds : d < 2 * s) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ), 1 ≤ N →
      ∫ β : ℝ, (Work.A3.mArcKernel N d β) ^ (2 * s) ≤ K ^ (2 * s) * (N : ℝ) ^ (2 * s - d) := by
  obtain ⟨K, hKpos, hK⟩ := min_rpow_integral_bound 1 one_pos d hd
  refine ⟨K, hKpos, fun N hN => ?_⟩
  have hd1 : 1 ≤ d := by omega
  -- the dominating function `(min N (|β|^{-1/d}))^{2s}` is integrable
  have hgi : Integrable
      (fun β : ℝ => (min (N : ℝ) (1 * |β| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s)) :=
    integrable_min_rpow 1 one_pos d hd1 N s hds
  -- the kernel's power is nonnegative
  have hnonneg : 0 ≤ᵐ[volume] fun β : ℝ => (mArcKernel N d β) ^ (2 * s) :=
    Filter.Eventually.of_forall fun β =>
      pow_nonneg (le_of_lt (mArcKernel_pos hN hd1 β)) _
  -- the pointwise domination holds off `{0}`, a null set
  have hle : (fun β : ℝ => (mArcKernel N d β) ^ (2 * s)) ≤ᵐ[volume]
      (fun β : ℝ => (min (N : ℝ) (1 * |β| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s)) := by
    rw [Filter.EventuallyLE, MeasureTheory.ae_iff]
    refine measure_mono_null (t := {0}) (fun β hβ => ?_) (by simp)
    simp only [not_le] at hβ
    by_contra hmem
    simp only [Set.mem_singleton_iff] at hmem
    have hub : mArcKernel N d β ≤ min (N : ℝ) (1 * |β| ^ (-(1 : ℝ) / (d : ℝ))) :=
      le_min (mArcKernel_le_N hN hd1 β)
        (by rw [one_mul]; exact mArcKernel_le hd1 hmem)
    have hpos : 0 ≤ mArcKernel N d β := le_of_lt (mArcKernel_pos hN hd1 β)
    exact absurd (pow_le_pow_left₀ hpos hub (2 * s)) (not_le.mpr hβ)
  calc ∫ β : ℝ, (mArcKernel N d β) ^ (2 * s)
      ≤ ∫ β : ℝ, (min (N : ℝ) (1 * |β| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s) :=
        integral_mono_of_nonneg hnonneg hgi hle
    _ ≤ K ^ (2 * s) * (N : ℝ) ^ (2 * s - d) := hK N s hN hds

end

end Work.A3
