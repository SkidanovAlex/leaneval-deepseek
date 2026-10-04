import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped ContDiff Topology
open Filter

namespace Work.OddBound.mountainPass

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Second-order Taylor estimate with an explicit small constant.**
For a `C²` function `f` and `ε > 0` there is `ρ > 0` such that for all `h` with `‖h‖ ≤ ρ`,
`|f (z+h) - f z - f'(z) h - ½ f''(z)(h,h)| ≤ ε * ‖h‖²`. -/
theorem taylor2_bound {f : E → ℝ} (hf : ContDiff ℝ 2 f) (z : E) :
    ∀ ε > 0, ∃ ρ > 0, ∀ h : E, ‖h‖ ≤ ρ →
      |f (z + h) - f z - (fderiv ℝ f z) h - (1 / 2) * ((fderiv ℝ (fderiv ℝ f) z) h h)|
        ≤ ε * ‖h‖ ^ 2 := by
  intro ε hε
  have hf' : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have hg : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((hf'.differentiable (by norm_num)).differentiableAt).hasFDerivAt
  have hlittle := hg.isLittleO
  rw [Asymptotics.isLittleO_iff] at hlittle
  have hev : ∀ᶠ x' in 𝓝 z, ‖fderiv ℝ f x' - fderiv ℝ f z -
      (fderiv ℝ (fderiv ℝ f) z) (x' - z)‖ ≤ ε * ‖x' - z‖ := hlittle hε
  obtain ⟨ρ₀, hρ₀, hbound₀⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ρ₀ / 2, by positivity, fun h hh => ?_⟩
  have hlt : ‖h‖ < ρ₀ := lt_of_le_of_lt hh (by linarith)
  set H2 := fderiv ℝ (fderiv ℝ f) z with hH2
  set φ : ℝ → ℝ := fun t => f (z + t • h) - t * ((fderiv ℝ f z) h) - (t ^ 2 / 2) * (H2 h h)
    with hφ
  have hφderiv : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt φ
      ((fderiv ℝ f (z + x • h) - fderiv ℝ f z - H2 (x • h)) h) (Set.Icc (0 : ℝ) 1) x := by
    intro x hx
    have h1 : HasDerivAt (fun t : ℝ => z + t • h) h x := by
      simpa using ((hasDerivAt_id x).smul_const h).const_add z
    have h2 : HasDerivAt (fun t : ℝ => f (z + t • h)) ((fderiv ℝ f (z + x • h)) h) x :=
      (((hf.differentiable (by norm_num)).differentiableAt).hasFDerivAt).comp_hasDerivAt x h1
    have h3 : HasDerivAt (fun t : ℝ => t * ((fderiv ℝ f z) h)) ((fderiv ℝ f z) h) x := by
      simpa using (hasDerivAt_id x).mul_const ((fderiv ℝ f z) h)
    have h4 : HasDerivAt (fun t : ℝ => (t ^ 2 / 2) * (H2 h h)) (x * (H2 h h)) x := by
      have h5 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) x x := by
        simpa using (hasDerivAt_pow 2 x).div_const 2
      exact h5.mul_const (H2 h h)
    have h6 : HasDerivAt φ
        ((fderiv ℝ f (z + x • h)) h - (fderiv ℝ f z) h - x * (H2 h h)) x :=
      (h2.sub h3).sub h4
    have h7 : HasDerivAt φ ((fderiv ℝ f (z + x • h) - fderiv ℝ f z - H2 (x • h)) h) x := by
      convert h6 using 2
      simp only [sub_apply, map_smul, smul_apply, smul_eq_mul]
    exact h7.hasDerivWithinAt
  have hbound' : ∀ x ∈ Set.Ico (0 : ℝ) 1,
      ‖(fderiv ℝ f (z + x • h) - fderiv ℝ f z - H2 (x • h)) h‖ ≤ ε * ‖h‖ ^ 2 := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x ≤ 1 := hx.2.le
    have hxh : ‖x • h‖ ≤ ‖h‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hx0]
      calc x * ‖h‖ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right hx1 (norm_nonneg h)
        _ = ‖h‖ := one_mul _
    have hxlt : ‖x • h‖ < ρ₀ := lt_of_le_of_lt hxh hlt
    have hL := hbound₀ (y := z + x • h) (by rw [dist_eq_norm]; simpa using hxlt)
    have hL2 : ‖fderiv ℝ f (z + x • h) - fderiv ℝ f z - H2 (x • h)‖ ≤ ε * ‖x • h‖ := by
      simpa [H2, add_sub_cancel_left] using hL
    calc ‖(fderiv ℝ f (z + x • h) - fderiv ℝ f z - H2 (x • h)) h‖
        ≤ ‖fderiv ℝ f (z + x • h) - fderiv ℝ f z - H2 (x • h)‖ * ‖h‖ :=
          ContinuousLinearMap.le_opNorm _ h
      _ ≤ (ε * ‖x • h‖) * ‖h‖ := by
          exact mul_le_mul_of_nonneg_right hL2 (norm_nonneg h)
      _ ≤ (ε * ‖h‖) * ‖h‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxh hε.le) (norm_nonneg h)
      _ = ε * ‖h‖ ^ 2 := by ring
  have hmain : ‖φ 1 - φ 0‖ ≤ ε * ‖h‖ ^ 2 :=
    norm_image_sub_le_of_norm_deriv_le_segment_01' hφderiv hbound'
  have hgoal : φ 1 - φ 0 = f (z + h) - f z - (fderiv ℝ f z) h - (1 / 2) * (H2 h h) := by
    rw [hφ]
    norm_num
    ring
  rw [hgoal] at hmain
  rwa [Real.norm_eq_abs] at hmain

end Work.OddBound.mountainPass
