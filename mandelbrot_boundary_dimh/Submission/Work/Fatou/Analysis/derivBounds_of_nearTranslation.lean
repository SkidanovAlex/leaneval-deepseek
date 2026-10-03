import Mathlib

/-!
# Derivative bounds for a near-translation

Let `v` be holomorphic on the ball `Metric.ball c R` and suppose that `‖v z - 1‖ < 1/4` there.
Then `v = 1 + w` with `‖w‖ < 1/4`, so `‖v‖ ≤ 5/4` on the ball and the usual Cauchy estimates give
universal bounds for `deriv v` and `deriv (deriv v)`, as well as a Lipschitz-type bound for `deriv v`
near the centre.  This is the elementary Cauchy-estimate part of Shishikura's Lemma A.2.4(i).

The numerical constant `64` below is not optimal (the proof gives `40`), but the exact value is
irrelevant for the applications.
-/

namespace Work.Fatou.Analysis

open Metric

/-- Cauchy's estimate for the first derivative of a holomorphic function on a shrunk ball:
a bound `M` on `ball c R` gives `‖deriv v z‖ ≤ 2 M / R` on the half-ball `ball c (R/2)`. -/
private lemma cauchy_deriv_le {v : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ v (ball c R)) (hM : ∀ z ∈ ball c R, ‖v z‖ ≤ M)
    {z : ℂ} (hz : z ∈ ball c (R / 2)) : ‖deriv v z‖ ≤ 2 * M / R := by
  have hzc : ‖z - c‖ < R / 2 := by
    have h := hz; rw [mem_ball, dist_eq_norm] at h; exact h
  have hsub : closedBall z (R / 2) ⊆ ball c R := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_ball, dist_eq_norm]
    have h1 : ‖w - c‖ ≤ ‖w - z‖ + ‖z - c‖ := by
      calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖z - c‖ := norm_add_le _ _
    linarith
  have hdd : DiffContOnCl ℂ v (ball z (R / 2)) := hd.diffContOnCl_ball hsub
  have hsph : ∀ w ∈ sphere z (R / 2), ‖v w‖ ≤ M := fun w hw =>
    hM w (hsub (sphere_subset_closedBall hw))
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := R / 2) (C := M)
    (f := v) (by linarith) hdd hsph
  calc ‖deriv v z‖ ≤ M / (R / 2) := h
    _ = 2 * M / R := by rw [div_div_eq_mul_div]; ring

/-- Cauchy's estimate for the second derivative of a holomorphic function on a shrunk ball:
a bound `M` on `ball c R` gives `‖v'' z‖ ≤ 8 M / R ^ 2` on the quarter-ball `ball c (R/4)`. -/
private lemma cauchy_iteratedDeriv_two_le {v : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ v (ball c R)) (hM : ∀ z ∈ ball c R, ‖v z‖ ≤ M)
    {z : ℂ} (hz : z ∈ ball c (R / 4)) : ‖deriv (deriv v) z‖ ≤ 8 * M / R ^ 2 := by
  have hzc : ‖z - c‖ < R / 4 := by
    have h := hz; rw [mem_ball, dist_eq_norm] at h; exact h
  have hsub : closedBall z (R / 2) ⊆ ball c R := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_ball, dist_eq_norm]
    have h1 : ‖w - c‖ ≤ ‖w - z‖ + ‖z - c‖ := by
      calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖z - c‖ := norm_add_le _ _
    linarith
  have hdd : DiffContOnCl ℂ v (ball z (R / 2)) := hd.diffContOnCl_ball hsub
  have hsph : ∀ w ∈ sphere z (R / 2), ‖v w‖ ≤ M := fun w hw =>
    hM w (hsub (sphere_subset_closedBall hw))
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n := 2) (c := z)
    (R := R / 2) (C := M) (f := v) (by linarith) hdd hsph
  have h2 : iteratedDeriv 2 v = deriv (deriv v) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2] at h
  calc ‖deriv (deriv v) z‖ ≤ (↑(Nat.factorial 2) * M) / ((R / 2) ^ 2) := h
    _ = 8 * M / R ^ 2 := by norm_num [Nat.factorial]; field_simp; ring

/-- Consequence of the mean value inequality plus the Cauchy estimate for the second derivative:
`deriv v` is constant up to `32 M / R ^ 2` on `ball c 4` when `16 ≤ R`. -/
private lemma deriv_diff_le {v : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 16 ≤ R)
    (hd : DifferentiableOn ℂ v (ball c R)) (hM : ∀ z ∈ ball c R, ‖v z‖ ≤ M) (hM0 : 0 ≤ M)
    {z : ℂ} (hz : z ∈ ball c 4) : ‖deriv v z - deriv v c‖ ≤ 32 * M / R ^ 2 := by
  have hRpos : 0 < R := by linarith
  have hzc : ‖z - c‖ < 4 := by
    have h := hz; rw [mem_ball, dist_eq_norm] at h; exact h
  have h4 : (4 : ℝ) ≤ R / 4 := by linarith
  have h4R : R / 4 ≤ R := by linarith
  have hz' : z ∈ ball c (R / 4) := ball_subset_ball h4 hz
  have hc' : c ∈ ball c (R / 4) := by rw [mem_ball, dist_self]; positivity
  have hC0 : 0 ≤ 8 * M / R ^ 2 := by positivity
  have hg : ∀ x ∈ ball c (R / 4), DifferentiableAt ℂ (deriv v) x := fun x hx =>
    (hd.deriv Metric.isOpen_ball).differentiableAt
      (Metric.isOpen_ball.mem_nhds (ball_subset_ball h4R hx))
  have hg' : ∀ x ∈ ball c (R / 4), ‖deriv (deriv v) x‖ ≤ 8 * M / R ^ 2 :=
    fun x hx => cauchy_iteratedDeriv_two_le hRpos hd hM hx
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv v)
    (s := ball c (R / 4)) (C := 8 * M / R ^ 2) hg hg' (convex_ball c (R / 4)) hc' hz'
  have hb : 8 * M / R ^ 2 * ‖z - c‖ ≤ 8 * M / R ^ 2 * 4 :=
    mul_le_mul_of_nonneg_left (le_of_lt hzc) hC0
  calc ‖deriv v z - deriv v c‖ ≤ 8 * M / R ^ 2 * ‖z - c‖ := hmvt
    _ ≤ 8 * M / R ^ 2 * 4 := hb
    _ = 32 * M / R ^ 2 := by ring

theorem derivBounds_of_nearTranslation :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : ℂ → ℂ) (c : ℂ) (R : ℝ), 16 ≤ R →
      (∀ z ∈ Metric.ball c R, AnalyticAt ℂ v z) →
      (∀ z ∈ Metric.ball c R, ‖v z - 1‖ < 1/4) →
      (∀ z ∈ Metric.ball c (R/2), ‖deriv v z‖ ≤ C / R) ∧
      (∀ z ∈ Metric.ball c (R/4), ‖deriv (deriv v) z‖ ≤ C / R^2) ∧
      (∀ z ∈ Metric.ball c 4, ‖deriv v z - deriv v c‖ ≤ C / R^2) ∧
      (∀ z ∈ Metric.ball c R, ‖v z‖ ≤ 5/4) := by
  refine ⟨64, by norm_num, ?_⟩
  intro v c R hR hv hnv
  have hRpos : 0 < R := by linarith
  have hd : DifferentiableOn ℂ v (ball c R) := fun z hz => (hv z hz).differentiableWithinAt
  have hnorm : ∀ z ∈ ball c R, ‖v z‖ ≤ 5 / 4 := by
    intro z hz
    have h1 : ‖v z‖ ≤ ‖v z - 1‖ + ‖(1 : ℂ)‖ := by
      calc ‖v z‖ = ‖(v z - 1) + 1‖ := by ring_nf
        _ ≤ ‖v z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    rw [norm_one] at h1
    linarith [hnv z hz]
  refine ⟨?_, ?_, ?_, hnorm⟩
  · intro z hz
    have h := cauchy_deriv_le hRpos hd hnorm hz
    have h2 : 2 * (5 / 4 : ℝ) / R ≤ 64 / R := by
      rw [div_le_div_iff_of_pos_right hRpos]; norm_num
    linarith
  · intro z hz
    have h := cauchy_iteratedDeriv_two_le hRpos hd hnorm hz
    have h2 : 8 * (5 / 4 : ℝ) / R ^ 2 ≤ 64 / R ^ 2 := by
      rw [div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < R ^ 2)]; norm_num
    linarith
  · intro z hz
    have h := deriv_diff_le hR hd hnorm (by norm_num : (0 : ℝ) ≤ 5 / 4) hz
    have h2 : 32 * (5 / 4 : ℝ) / R ^ 2 ≤ 64 / R ^ 2 := by
      rw [div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < R ^ 2)]; norm_num
    linarith

end Work.Fatou.Analysis
