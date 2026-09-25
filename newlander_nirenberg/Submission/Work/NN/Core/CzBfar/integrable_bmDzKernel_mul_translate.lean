import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmCz.dCoord_bmKernel
import Submission.Work.CR.Flat.Cauchy.bmDzKernel_cz_bound

namespace Work.NN.Core.CzBfar

open MeasureTheory Set

/-- If `F` is continuous and supported in the (sup-norm) ball of radius `r`, and if the point `z`
is so far from the origin that the support of `F (z + ·)` stays at Euclidean distance `≥ 3r` from
the origin, then the translate `x ↦ ∂_{z_i}(bmKernel l) x · F (z + x)` is integrable.

Indeed, `F (z + ·)` is supported in the ball of radius `r + ‖z‖`, and on that support the kernel
is bounded by `n / (3r)^{2n}`.  Hence the integrand is bounded on a ball of finite measure and
vanishes outside it.

This is the "far field" integrability used to make sense of the Calderón–Zygmund singular
integral `∫ x, ∂_{z_i}(bmKernel l) x · F (z + x)` appearing in `czB_far_bound`. -/
theorem integrable_bmDzKernel_mul_translate {n : ℕ} (hn : 0 < n) (i l : Fin n) {r : ℝ}
    (hr : 0 < r) {F : (Fin n → ℂ) → ℂ} (hFc : Continuous F)
    (hsupp : ∀ x, r ≤ ‖x‖ → F x = 0) {z : Fin n → ℂ}
    (hgeo : ∀ x, ‖z + x‖ < r → 3 * r ≤ Work.CR.Flat.Cauchy.eucNorm x) :
    MeasureTheory.Integrable (fun x : Fin n → ℂ =>
      Work.CR.Flat.Cauchy.bmDzKernel i l x * F (z + x)) := by
  classical
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h3r : 0 < 3 * r := by linarith
  -- `F` is bounded on the (compact) closed ball of radius `r`
  obtain ⟨B, hB⟩ :=
    (isCompact_closedBall (0 : Fin n → ℂ) r).exists_bound_of_continuousOn hFc.continuousOn
  -- the resulting bound for the integrand
  set C : ℝ := (n : ℝ) / (3 * r) ^ (2 * n) * max B 0 with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    exact mul_nonneg (div_nonneg hnpos.le (by positivity)) (le_max_right _ _)
  -- the ball containing the support of the integrand
  set T : Set (Fin n → ℂ) := Metric.closedBall (0 : Fin n → ℂ) (r + ‖z‖) with hTdef
  -- the integrand vanishes outside `T`
  have hzero : ∀ x : Fin n → ℂ, x ∉ T →
      Work.CR.Flat.Cauchy.bmDzKernel i l x * F (z + x) = 0 := by
    intro x hx
    have hxmem : ¬ (‖x‖ ≤ r + ‖z‖) := by
      simpa [hTdef, Metric.mem_closedBall, dist_eq_norm] using hx
    have hxnorm : r + ‖z‖ < ‖x‖ := not_le.mp hxmem
    have hzr : r < ‖z + x‖ := by
      have h1 : ‖x‖ ≤ ‖z + x‖ + ‖z‖ := by
        calc ‖x‖ = ‖(z + x) + (-z)‖ := by ring_nf
          _ ≤ ‖z + x‖ + ‖-z‖ := norm_add_le _ _
          _ = ‖z + x‖ + ‖z‖ := by rw [norm_neg]
      linarith
    rw [hsupp (z + x) (le_of_lt hzr), mul_zero]
  -- the pointwise bound on `T`
  have hbound : ∀ x ∈ T,
      ‖Work.CR.Flat.Cauchy.bmDzKernel i l x * F (z + x)‖ ≤ C := by
    intro x _
    by_cases hS : ‖z + x‖ < r
    · have hxne : x ≠ 0 := by
        intro h0
        have h := hgeo x hS
        rw [h0, Work.CR.Flat.Cauchy.eucNorm_zero] at h
        linarith
      have hxe : 3 * r ≤ Work.CR.Flat.Cauchy.eucNorm x := hgeo x hS
      have hk : ‖Work.CR.Flat.Cauchy.bmDzKernel i l x‖ ≤ (n : ℝ) / (3 * r) ^ (2 * n) := by
        refine le_trans (Work.CR.Flat.Cauchy.BmDzCzAux.norm_bmDzKernel_le i l hxne) ?_
        refine div_le_div_of_nonneg_left (Nat.cast_nonneg n) (by positivity) ?_
        exact pow_le_pow_left₀ h3r.le hxe (2 * n)
      have hFb : ‖F (z + x)‖ ≤ max B 0 := by
        refine le_trans (hB (z + x) ?_) (le_max_left _ _)
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        exact le_of_lt hS
      rw [norm_mul]
      calc ‖Work.CR.Flat.Cauchy.bmDzKernel i l x‖ * ‖F (z + x)‖
          ≤ ((n : ℝ) / (3 * r) ^ (2 * n)) * max B 0 :=
            mul_le_mul hk hFb (norm_nonneg _) (div_nonneg hnpos.le (by positivity))
        _ = C := by rw [hCdef]
    · have hSle : r ≤ ‖z + x‖ := not_lt.mp hS
      rw [hsupp (z + x) hSle, mul_zero, norm_zero]
      exact hCnn
  -- measurability
  have hmeas : AEStronglyMeasurable
      (fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.bmDzKernel i l x * F (z + x)) volume :=
    ((Work.CR.Flat.Cauchy.BmDzCzAux.measurable_bmDzKernel i l).mul
      (hFc.measurable.comp (continuous_const.add continuous_id).measurable)).aestronglyMeasurable
  have hTmeas : MeasurableSet T := by
    rw [hTdef]; exact Metric.isClosed_closedBall.measurableSet
  have hTfin : volume T < ⊤ := by
    rw [hTdef]; exact MeasureTheory.measure_closedBall_lt_top
  have hI : IntegrableOn
      (fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.bmDzKernel i l x * F (z + x)) T volume :=
    Work.CR.Flat.Cauchy.BmDzCzAux.integrableOn_of_norm_le_const hTfin hTmeas hmeas hbound
  exact hI.integrable_of_forall_notMem_eq_zero hzero

end Work.NN.Core.CzBfar
