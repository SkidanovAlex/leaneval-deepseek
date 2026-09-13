import Mathlib

namespace Commons.Measure.WeightedInterpolation

open MeasureTheory Metric Set Filter

/-- Arithmetic helper: `2^(n+1) * (4 * 2^n) = 8 * 4^n`. -/
private lemma two_pow_mul_four_two_pow (n : ℕ) :
    (2 : ℝ) ^ (n + 1) * (4 * 2 ^ n) = 8 * 4 ^ n := by
  have h : (4 : ℝ) ^ n = (2 : ℝ) ^ (2 * n) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  rw [h]
  have h1 : (2 : ℝ) ^ (n + 1) * (4 * 2 ^ n) = 4 * (2 ^ (n + 1) * 2 ^ n) := by ring
  rw [h1, ← pow_add, show n + 1 + n = 2 * n + 1 by ring, pow_add]
  norm_num
  ring

open MeasureTheory Metric Set Filter in
theorem weighted_lipschitz_of_osc {n : ℕ}
    {d : EuclideanSpace ℝ (Fin n) → ℝ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {C₀ A : ℝ}
    (hC₀ : 0 ≤ C₀) (hΩ : IsOpen Ω) (hne : Ω.Nonempty)
    (hdpos : ∀ x ∈ Ω, 0 < d x) (hdball : ∀ x ∈ Ω, Metric.ball x (d x) ⊆ Ω)
    (hdlip : ∀ x y, |d x - d y| ≤ dist x y)
    (hu : DifferentiableOn ℝ u Ω)
    (hgrad : ∀ (y : EuclideanSpace ℝ (Fin n)) (ρ M m : ℝ), 0 < ρ →
      Metric.closedBall y ρ ⊆ Ω → (∀ x ∈ Metric.ball y ρ, m ≤ u x ∧ u x ≤ M) →
      ‖fderiv ℝ u y‖ * ρ ≤ C₀ * (M - m))
    (hA : ∀ w ∈ Ω, (d w) ^ n * |u w| ≤ A) :
    ∀ y ∈ Ω, ∀ z ∈ Ω, y ≠ z →
      (min (d y) (d z)) ^ (n + 1) * |u y - u z| / dist y z ≤ (8 * 4 ^ n * C₀ + 4) * A := by
  intro y hy z hz hyz
  have hA0 : 0 ≤ A := by
    obtain ⟨w, hw⟩ := hne
    exact le_trans (mul_nonneg (pow_nonneg (hdpos w hw).le n) (abs_nonneg _)) (hA w hw)
  have hdy : 0 < d y := hdpos y hy
  have hdz : 0 < d z := hdpos z hz
  have hγpos : 0 < dist y z := dist_pos.mpr hyz
  set r : ℝ := min (d y) (d z) with hr
  have hrpos : 0 < r := by rw [hr]; exact lt_min hdy hdz
  have hry : r ≤ d y := by rw [hr]; exact min_le_left _ _
  have hrz : r ≤ d z := by rw [hr]; exact min_le_right _ _
  have hdiffAt : ∀ p ∈ Ω, DifferentiableAt ℝ u p := fun p hp => hu.differentiableAt (hΩ.mem_nhds hp)
  -- gradient bound at any point of `Ω`
  have hgrad_at : ∀ p ∈ Ω, ‖fderiv ℝ u p‖ * (d p) ^ (n + 1) ≤ 4 * 2 ^ n * C₀ * A := by
    intro p hp
    have hdp : 0 < d p := hdpos p hp
    have hRpos : 0 < d p / 2 := by linarith
    have hsub : Metric.closedBall p (d p / 2) ⊆ Ω := by
      refine subset_trans ?_ (hdball p hp)
      intro x hx
      rw [Metric.mem_closedBall] at hx
      rw [Metric.mem_ball]
      linarith
    have hosc : ∀ x ∈ Metric.ball p (d p / 2),
        -(A / (d p / 2) ^ n) ≤ u x ∧ u x ≤ A / (d p / 2) ^ n := by
      intro x hx
      have hxΩ : x ∈ Ω := hsub (Metric.ball_subset_closedBall hx)
      have hdist : dist x p < d p / 2 := Metric.mem_ball.mp hx
      have hdx : d p / 2 ≤ d x := by
        have h1 : |d x - d p| < d p / 2 := lt_of_le_of_lt (hdlip x p) hdist
        rw [abs_lt] at h1
        linarith [h1.1]
      have hdxpos : 0 < d x := lt_of_lt_of_le hRpos hdx
      have hux : |u x| ≤ A / (d x) ^ n := by
        rw [le_div_iff₀ (pow_pos hdxpos n)]
        rw [mul_comm]
        exact hA x hxΩ
      have hmono : A / (d x) ^ n ≤ A / (d p / 2) ^ n :=
        div_le_div_of_nonneg_left hA0 (pow_pos hRpos n) (pow_le_pow_left₀ hRpos.le hdx n)
      exact abs_le.mp (le_trans hux hmono)
    have hg := hgrad p (d p / 2) (A / (d p / 2) ^ n) (-(A / (d p / 2) ^ n)) hRpos hsub hosc
    have htwice : A / (d p / 2) ^ n - -(A / (d p / 2) ^ n) = 2 * (A / (d p / 2) ^ n) := by ring
    rw [htwice] at hg
    have hnn : 0 ≤ 2 * (d p) ^ n := by positivity
    have h1 := mul_le_mul_of_nonneg_right hg hnn
    have e1 : ‖fderiv ℝ u p‖ * (d p / 2) * (2 * (d p) ^ n) = ‖fderiv ℝ u p‖ * (d p) ^ (n + 1) := by
      rw [pow_succ']
      ring
    have e2 : C₀ * (2 * (A / (d p / 2) ^ n)) * (2 * (d p) ^ n) = 4 * 2 ^ n * C₀ * A := by
      rw [show (d p / 2) ^ n = (d p) ^ n / 2 ^ n by rw [div_pow]]
      field_simp
      ring
    rwa [e1, e2] at h1
  by_cases hcase : r / 2 ≤ dist y z
  · -- easy case: the two points are far apart relative to `r`
    have hy_le : |u y| ≤ A / r ^ n := by
      have h1 : |u y| ≤ A / (d y) ^ n := by
        rw [le_div_iff₀ (pow_pos hdy n)]
        rw [mul_comm]
        exact hA y hy
      exact le_trans h1
        (div_le_div_of_nonneg_left hA0 (pow_pos hrpos n) (pow_le_pow_left₀ hrpos.le hry n))
    have hz_le : |u z| ≤ A / r ^ n := by
      have h1 : |u z| ≤ A / (d z) ^ n := by
        rw [le_div_iff₀ (pow_pos hdz n)]
        rw [mul_comm]
        exact hA z hz
      exact le_trans h1
        (div_le_div_of_nonneg_left hA0 (pow_pos hrpos n) (pow_le_pow_left₀ hrpos.le hrz n))
    have hdiff_le : |u y - u z| ≤ 2 * (A / r ^ n) := by
      have h1 : |u y - u z| ≤ |u y| + |u z| := by
        have := abs_add_le (u y) (-(u z))
        simpa [sub_eq_add_neg] using this
      linarith
    have h2 : r ^ (n + 1) * (2 * (A / r ^ n)) = 2 * A * r := by
      rw [pow_succ']
      field_simp
    have h3 : 2 * A * r / dist y z ≤ 4 * A := by
      rw [div_le_iff₀ hγpos]
      have h4 : 2 * A * r ≤ 2 * A * (2 * dist y z) :=
        mul_le_mul_of_nonneg_left (by linarith [hcase]) (by linarith [hA0])
      linarith
    have h5 : 4 * A ≤ (8 * 4 ^ n * C₀ + 4) * A := by
      have h4n : (0 : ℝ) ≤ 4 ^ n := pow_nonneg (by norm_num) n
      nlinarith [mul_nonneg (mul_nonneg h4n hC₀) hA0]
    calc r ^ (n + 1) * |u y - u z| / dist y z
        ≤ r ^ (n + 1) * (2 * (A / r ^ n)) / dist y z :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdiff_le (pow_nonneg hrpos.le _)) hγpos.le
      _ = 2 * A * r / dist y z := by rw [h2]
      _ ≤ 4 * A := h3
      _ ≤ (8 * 4 ^ n * C₀ + 4) * A := h5
  · -- hard case: the two points are close
    have hγlt : dist y z < r / 2 := lt_of_not_ge hcase
    have hseg_closed : segment ℝ y z ⊆ closedBall y (dist y z) :=
      (convex_closedBall y _).segment_subset (by simp [mem_closedBall])
        (by simp [mem_closedBall, dist_comm])
    have hseg_sub : segment ℝ y z ⊆ Ω := by
      refine subset_trans hseg_closed ?_
      refine subset_trans ?_ (hdball y hy)
      intro x hx
      rw [mem_closedBall] at hx
      rw [mem_ball]
      linarith [hry]
    have hdist_le : ∀ p ∈ segment ℝ y z, dist p y ≤ dist y z :=
      fun p hp => mem_closedBall.mp (hseg_closed hp)
    have hd_lower : ∀ p ∈ segment ℝ y z, r / 2 ≤ d p := by
      intro p hp
      have hp1 : dist p y ≤ dist y z := hdist_le p hp
      have h2 : |d p - d y| ≤ dist p y := hdlip p y
      have h3 : d y - dist y z ≤ d p := by
        have := neg_le_abs (d p - d y)
        linarith
      linarith
    have hderiv : ∀ p ∈ segment ℝ y z, ‖fderiv ℝ u p‖ ≤ 8 * 4 ^ n * C₀ * A / r ^ (n + 1) := by
      intro p hp
      have hpΩ : p ∈ Ω := hseg_sub hp
      have hdplow : r / 2 ≤ d p := hd_lower p hp
      have hkey := hgrad_at p hpΩ
      rw [le_div_iff₀ (pow_pos hrpos (n + 1))]
      have hle : r ^ (n + 1) ≤ (2 * d p) ^ (n + 1) :=
        pow_le_pow_left₀ (by linarith [hrpos]) (by linarith) (n + 1)
      rw [mul_pow] at hle
      have hX : 0 ≤ ‖fderiv ℝ u p‖ := norm_nonneg _
      calc ‖fderiv ℝ u p‖ * r ^ (n + 1)
          ≤ ‖fderiv ℝ u p‖ * ((2 : ℝ) ^ (n + 1) * (d p) ^ (n + 1)) :=
            mul_le_mul_of_nonneg_left hle hX
        _ = (2 : ℝ) ^ (n + 1) * (‖fderiv ℝ u p‖ * (d p) ^ (n + 1)) := by ring
        _ ≤ (2 : ℝ) ^ (n + 1) * (4 * 2 ^ n * C₀ * A) :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = 8 * 4 ^ n * C₀ * A := by
            rw [show (2 : ℝ) ^ (n + 1) * (4 * 2 ^ n * C₀ * A)
                = ((2 : ℝ) ^ (n + 1) * (4 * 2 ^ n)) * (C₀ * A) by ring,
              two_pow_mul_four_two_pow]
            ring
    have hmvt : ‖u y - u z‖ ≤ (8 * 4 ^ n * C₀ * A / r ^ (n + 1)) * dist y z := by
      have h := (convex_segment y z).norm_image_sub_le_of_norm_fderiv_le
        (fun p hp => hdiffAt p (hseg_sub hp)) hderiv
        (left_mem_segment ℝ y z) (right_mem_segment ℝ y z)
      have h2 : ‖u y - u z‖ ≤ (8 * 4 ^ n * C₀ * A / r ^ (n + 1)) * ‖z - y‖ := by
        simpa only [norm_sub_rev] using h
      rwa [← dist_eq_norm z y, dist_comm z y] at h2
    have hgoal : r ^ (n + 1) * |u y - u z| / dist y z ≤ 8 * 4 ^ n * C₀ * A := by
      rw [Real.norm_eq_abs] at hmvt
      rw [div_le_iff₀ hγpos]
      have hmain : r ^ (n + 1) * (8 * 4 ^ n * C₀ * A / r ^ (n + 1))
          = 8 * 4 ^ n * C₀ * A :=
        mul_div_cancel₀ _ (ne_of_gt (pow_pos hrpos (n + 1)))
      calc r ^ (n + 1) * |u y - u z|
          ≤ r ^ (n + 1) * ((8 * 4 ^ n * C₀ * A / r ^ (n + 1)) * dist y z) :=
            mul_le_mul_of_nonneg_left hmvt (pow_nonneg hrpos.le _)
        _ = 8 * 4 ^ n * C₀ * A * dist y z := by rw [← mul_assoc, hmain]
    have h5 : 8 * 4 ^ n * C₀ * A ≤ (8 * 4 ^ n * C₀ + 4) * A := by
      have h4n : (0 : ℝ) ≤ 4 ^ n := pow_nonneg (by norm_num) n
      nlinarith [mul_nonneg (mul_nonneg h4n hC₀) hA0]
    linarith [hgoal, h5]

end Commons.Measure.WeightedInterpolation
