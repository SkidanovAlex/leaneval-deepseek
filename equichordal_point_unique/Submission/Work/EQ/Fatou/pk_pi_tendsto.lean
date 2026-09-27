import Mathlib
import Submission.Work.EQ.FatouDefs

namespace Work.EQ.Fatou

/-- The angle Poisson kernel at angle `π` is `(1 - r²)/(1 + r)² = (1-r)/(1+r)`, hence tends to `0`
as `r → 1` from below. -/
theorem pk_pi_tendsto :
    Filter.Tendsto (fun r : ℝ => Work.EQ.pk r Real.pi) (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
  have hfun : (fun r : ℝ => Work.EQ.pk r Real.pi) = fun r : ℝ => (1 - r ^ 2) / (1 + r) ^ 2 := by
    funext r
    simp only [Work.EQ.pk, Real.cos_pi]
    norm_num
    ring_nf
  rw [hfun]
  have hc : ContinuousAt (fun r : ℝ => (1 - r ^ 2) / (1 + r) ^ 2) 1 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num
  have h0 : Filter.Tendsto (fun r : ℝ => (1 - r ^ 2) / (1 + r) ^ 2) (nhds 1) (nhds 0) := by
    have h := hc.tendsto
    have hval : (1 - (1 : ℝ) ^ 2) / (1 + 1) ^ 2 = 0 := by norm_num
    rwa [hval] at h
  exact h0.mono_left inf_le_left

end Work.EQ.Fatou
