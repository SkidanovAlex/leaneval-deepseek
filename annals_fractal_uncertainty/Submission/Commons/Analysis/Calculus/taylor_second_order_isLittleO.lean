import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology

open Filter Asymptotics
open scoped Topology

namespace Commons.Analysis.Calculus

set_option autoImplicit false

/-- **Second order Taylor expansion in little-o form.**  If `f : E → F` is `C²` (over `ℝ`) then
the second order Taylor remainder of `f` at `x` is `o(‖h‖²)`.

The proof reduces to the one dimensional mean value theorem along the segment
`t ↦ x + t • h`: the function
`φ t = f (x + t • h) - f x - t • (fderiv ℝ f x h) - (1/2 * t²) • ((fderiv ℝ (fderiv ℝ f) x) h) h`
has `φ 1 - φ 0` equal to the Taylor remainder, and
`φ' t = (fderiv ℝ f (x + t • h) - fderiv ℝ f x - (fderiv ℝ (fderiv ℝ f) x) (t • h)) h`,
which is bounded by `ε ‖h‖` provided `‖t • h‖ ≤ ‖h‖` is small enough. -/
theorem taylor_second_order_isLittleO {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} (hf : ContDiff ℝ 2 f) :
    (fun h => f (x + h) - f x - fderiv ℝ f x h
        - (1 / 2 : ℝ) • ((fderiv ℝ (fderiv ℝ f) x) h) h)
      =o[nhds 0] fun h => ‖h‖ ^ 2 := by
  have hf_diff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hderiv_diff : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  set B : E →L[ℝ] E →L[ℝ] F := fderiv ℝ (fderiv ℝ f) x with hB
  have hBd : HasFDerivAt (fderiv ℝ f) B x := by
    rw [hB]
    exact hderiv_diff.differentiableAt.hasFDerivAt
  have hLo : (fun k : E => fderiv ℝ f (x + k) - fderiv ℝ f x - B k) =o[𝓝 0] fun k : E => k :=
    (hasFDerivAt_iff_isLittleO_nhds_zero (f := fderiv ℝ f) (f' := B) (x := x)).1 hBd
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ > 0, ∀ k : E, ‖k‖ < δ →
      ‖fderiv ℝ f (x + k) - fderiv ℝ f x - B k‖ ≤ c * ‖k‖ := by
    rcases Metric.eventually_nhds_iff.1 ((Asymptotics.isLittleO_iff.1 hLo) hc) with ⟨δ, hδpos, hδ⟩
    exact ⟨δ, hδpos, fun k hk => hδ (by simpa [dist_eq_norm] using hk)⟩
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδpos, fun h hh => ?_⟩
  have hhδ : ‖h‖ < δ := by simpa [dist_eq_norm] using hh
  -- The auxiliary one dimensional function.
  set φ : ℝ → F := fun t => f (x + t • h) - f x - t • (fderiv ℝ f x h)
    - ((1 / 2 : ℝ) * t ^ 2) • ((B h) h) with hφ
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivWithinAt φ ((fderiv ℝ f (x + t • h) - fderiv ℝ f x - B (t • h)) h)
        (Set.Icc (0:ℝ) 1) t := by
    intro t _
    have hline : HasDerivAt (fun s : ℝ => f (x + s • h)) ((fderiv ℝ f (x + t • h)) h) t := by
      have hg : HasDerivAt (fun s : ℝ => x + s • h) h t := by
        simpa using ((hasDerivAt_id t).smul_const h).const_add x
      simpa [Function.comp_def] using
        ((hf_diff.differentiableAt (x := x + t • h)).hasFDerivAt.comp_hasDerivAt t hg)
    have hlin : HasDerivAt (fun s : ℝ => s • (fderiv ℝ f x h)) (fderiv ℝ f x h) t := by
      simpa using (hasDerivAt_id t).smul_const (fderiv ℝ f x h)
    have hquad : HasDerivAt (fun s : ℝ => ((1 / 2 : ℝ) * s ^ 2) • ((B h) h))
        (t • ((B h) h)) t := by
      have h2 : HasDerivAt (fun s : ℝ => (1 / 2 : ℝ) * s ^ 2) t t := by
        have h := (hasDerivAt_pow 2 t).const_mul (1 / 2 : ℝ)
        have hval : (1 / 2 : ℝ) * (↑(2 : ℕ) * t ^ ((2 : ℕ) - 1)) = t := by
          rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
          ring
        rw [hval] at h
        exact h
      simpa using h2.smul_const ((B h) h)
    have hmain : HasDerivAt φ ((fderiv ℝ f (x + t • h)) h - fderiv ℝ f x h
        - t • ((B h) h)) t := by
      rw [hφ]
      exact ((hline.sub_const (f x)).sub hlin).sub hquad
    have heq : ((fderiv ℝ f (x + t • h)) h - fderiv ℝ f x h - t • ((B h) h))
        = ((fderiv ℝ f (x + t • h) - fderiv ℝ f x - B (t • h)) h) := by
      simp only [map_smul, sub_apply, smul_apply]
    rw [heq] at hmain
    exact hmain.hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0:ℝ) 1,
      ‖((fderiv ℝ f (x + t • h) - fderiv ℝ f x - B (t • h)) h)‖ ≤ c * ‖h‖ ^ 2 := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t < 1 := ht.2
    have hk : ‖t • h‖ < δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
      calc t * ‖h‖ ≤ 1 * ‖h‖ := by nlinarith [norm_nonneg h]
        _ = ‖h‖ := one_mul _
        _ < δ := hhδ
    have hstep := hδ (t • h) hk
    calc ‖((fderiv ℝ f (x + t • h) - fderiv ℝ f x - B (t • h)) h)‖
        ≤ ‖fderiv ℝ f (x + t • h) - fderiv ℝ f x - B (t • h)‖ * ‖h‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (c * ‖t • h‖) * ‖h‖ := by
          exact mul_le_mul_of_nonneg_right hstep (norm_nonneg h)
      _ = c * (t * ‖h‖) * ‖h‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
      _ ≤ c * ‖h‖ ^ 2 := by
          have h1 : t * ‖h‖ * ‖h‖ ≤ ‖h‖ * ‖h‖ := by nlinarith [norm_nonneg h]
          nlinarith [hc]
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
  have hφ0 : φ 0 = 0 := by simp [hφ]
  have hφ1 : φ 1 = f (x + h) - f x - fderiv ℝ f x h
      - (1 / 2 : ℝ) • ((fderiv ℝ (fderiv ℝ f) x) h) h := by
    simp only [hφ, hB, one_smul, mul_one, one_pow]
  calc ‖f (x + h) - f x - fderiv ℝ f x h
        - (1 / 2 : ℝ) • ((fderiv ℝ (fderiv ℝ f) x) h) h‖
      = ‖φ 1 - φ 0‖ := by rw [hφ1, hφ0, sub_zero]
    _ ≤ c * ‖h‖ ^ 2 := hmvt
    _ = c * ‖‖h‖ ^ 2‖ := by rw [Real.norm_of_nonneg (sq_nonneg ‖h‖)]

end Commons.Analysis.Calculus