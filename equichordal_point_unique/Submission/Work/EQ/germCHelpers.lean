import Mathlib
import Submission.Work.EQ.DefsCore

/-! Small analytic and algebraic helpers for `germC_facts` (the local stable curve of the
equichordal half map in rectangular coordinates). -/

namespace Work.EQ

open Complex Metric Filter Set
open scoped Topology

noncomputable section

/-- `(z ^ (1/2 : ℂ)) ^ 2 = z` for every complex `z`; no slit-plane hypothesis is needed because
the only problematic point `z = 0` gives `0 ^ (1/2) = 0`. -/
lemma cpow_half_sq (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
  have h := Complex.cpow_nat_inv_pow z (n := 2) (by norm_num)
  have h2 : (((2 : ℕ)) : ℂ)⁻¹ = (1 / 2 : ℂ) := by norm_num
  rw [h2] at h
  exact h

/-- The principal square root of a nonnegative real number is its real square root. -/
lemma ofReal_cpow_half {x : ℝ} (hx : 0 ≤ x) :
    ((x : ℂ) ^ (1 / 2 : ℂ)) = (Real.sqrt x : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hx (1 / 2)]
  congr 1
  exact (Real.sqrt_eq_rpow x).symm

/-- A square root of `z` whose real part is positive is the principal square root of `z`. -/
lemma cpow_half_eq_of_sq {w z : ℂ} (h : w ^ 2 = z) (hw : 0 < w.re) :
    z ^ (1 / 2 : ℂ) = w := by
  rw [← h]
  have h2 : ((2 : ℂ))⁻¹ = (1 / 2 : ℂ) := by norm_num
  have := Complex.sq_cpow_two_inv (x := w) hw
  rw [h2] at this
  exact this

/-- `dslope f a` is analytic at every point where `f` is analytic. -/
lemma analyticAt_dslope {f : ℂ → ℂ} {a b : ℂ} (hf : AnalyticAt ℂ f b) :
    AnalyticAt ℂ (dslope f a) b := by
  rcases eq_or_ne b a with rfl | hne
  · obtain ⟨p, hp⟩ := hf
    exact (hp.has_fpower_series_dslope_fslope).analyticAt
  · have hslope : AnalyticAt ℂ (slope f a) b := by
      have hfun : slope f a = fun x => (x - a)⁻¹ * (f x - f a) := by
        funext x
        rw [slope_def_field, div_eq_mul_inv, mul_comm]
      rw [hfun]
      exact ((analyticAt_id.sub analyticAt_const).inv (by
        simp only [Pi.sub_apply, id_eq]
        exact sub_ne_zero.mpr hne)).mul (hf.sub analyticAt_const)
    exact hslope.congr (dslope_eventuallyEq_slope_of_ne f hne).symm

/-- `v * dslope f 0 v = f v` when `f 0 = 0` (the `dslope` at the origin is the derivative, and
`0 · f'(0) = 0 = f 0`). -/
lemma mul_dslope_eq {f : ℂ → ℂ} {v : ℂ} (h0 : f 0 = 0) : v * dslope f 0 v = f v := by
  have h := sub_smul_dslope f (0 : ℂ) v
  simp only [sub_zero, smul_eq_mul] at h
  rw [h, h0, sub_zero]

/-- If `0 < λ < 1`, then `λ u` is closer to the origin than `u`. -/
lemma norm_mul_lt_self {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (u : ℂ) :
    ‖(l : ℂ) * u‖ < ‖u‖ ∨ ‖u‖ = 0 := by
  rcases eq_or_ne u 0 with rfl | hu
  · right
    simp
  · left
    rw [norm_mul]
    have hln : ‖(l : ℂ)‖ = l := by simp [Real.norm_eq_abs, abs_of_pos hl0]
    rw [hln]
    exact mul_lt_of_lt_one_left (norm_pos_iff.mpr hu) hl1

/-- Scaled points stay in the ball of radius `r`. -/
lemma norm_mul_lt_of_lt {l r : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (hr : 0 < r) {u : ℂ}
    (hu : ‖u‖ < r) : ‖(l : ℂ) * u‖ < r := by
  rcases eq_or_ne u 0 with rfl | hne
  · simpa using hr
  · rw [norm_mul]
    have hln : ‖(l : ℂ)‖ = l := by simp [Real.norm_eq_abs, abs_of_pos hl0]
    rw [hln]
    exact lt_trans (mul_lt_of_lt_one_left (norm_pos_iff.mpr hne) hl1) hu

/-- Analyticity of the rescaled germ `v ↦ h (λ v)` on the ball of radius `r`, for
`0 < λ < 1`. -/
lemma analyticAt_h_comp {h : ℂ → ℂ} {r l : ℝ} (hAn : AnalyticOnNhd ℂ h (Metric.ball 0 r))
    (hl0 : 0 < l) (hl1 : l < 1) (hr : 0 < r) {u : ℂ} (hu : ‖u‖ < r) :
    AnalyticAt ℂ (fun v : ℂ => h ((l : ℂ) * v)) u := by
  have h1 : AnalyticAt ℂ (fun v : ℂ => (l : ℂ) * v) u := analyticAt_const.mul analyticAt_id
  have h2 : AnalyticAt ℂ h ((l : ℂ) * u) :=
    hAn _ (by
      rw [Metric.mem_ball, dist_zero_right]
      exact norm_mul_lt_of_lt hl0 hl1 hr hu)
  simpa [Function.comp_def] using h2.comp h1

/-- A pointwise `∀ᶠ` statement at `0` holds on an honest ball around `0`. -/
lemma exists_ball_of_eventually {p : ℂ → Prop} (hp : ∀ᶠ u in 𝓝 (0 : ℂ), p u) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ, p u := by
  obtain ⟨ρ, hρ, h⟩ := Metric.eventually_nhds_iff.mp hp
  exact ⟨ρ, hρ, fun u hu => h (by simpa [dist_eq_norm] using hu)⟩

/-- The derivative of `v ↦ h (λ v)` at `0`, `λ = eqLam a`: `λ · h'(0) = -λ`. -/
lemma deriv_eqLam_mul {h : ℂ → ℂ} {a : ℝ} (hderiv : deriv h 0 = -1) :
    deriv (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 = -(eqLam a : ℂ) := by
  rw [deriv_comp_mul_left, mul_zero, hderiv, smul_eq_mul]
  ring

end

end Work.EQ
