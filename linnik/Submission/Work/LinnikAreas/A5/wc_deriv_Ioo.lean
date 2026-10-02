import Mathlib
import Submission.Work.LinnikAreas.A5.Weights
import Submission.Work.LinnikAreas.A5.Basic
import Submission.Work.LinnikAreas.A5.f1_deriv

open scoped Topology

namespace Work.LinnikAreas.A5

/-- On the open interval `(0,K)` the cutoff weight `wc K lam` agrees with the normalised
smooth branch `(sinh (K·lam))⁻¹ · f₁`; in particular it is differentiable there with
derivative `-lam · cosh((K-t)·lam) / sinh(K·lam)`. -/
theorem wc_deriv_Ioo (K lam : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) K) :
    deriv (Work.LinnikAreas.A5.wc K lam) t
      = -lam * Real.cosh ((K - t) * lam) / Real.sinh (K * lam) := by
  have ht0 : 0 < t := ht.1
  have htK : t < K := ht.2
  -- near `t` (which is positive) the cutoff is inactive
  have hev : wc K lam =ᶠ[𝓝 t] fun s => (Real.sinh (K * lam))⁻¹ * f1 K lam s := by
    filter_upwards [isOpen_Ioi.mem_nhds ht0] with s hs
    exact wc_of_nonneg hs.le
  rw [hev.deriv_eq]
  -- `f₁` agrees near `t` (which is `< K`) with the smooth branch, hence is differentiable
  have hf1diff : DifferentiableAt ℝ (f1 K lam) t := by
    have hev2 : f1 K lam =ᶠ[𝓝 t] fun s => Real.sinh ((K - s) * lam) := by
      filter_upwards [isOpen_Iio.mem_nhds htK] with s hs
      exact f1_of_le hs.le
    rw [hev2.differentiableAt_iff]
    fun_prop
  rw [deriv_const_mul _ hf1diff, f1_deriv K lam htK]
  ring

end Work.LinnikAreas.A5
