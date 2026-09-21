import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Pointwise RealInnerProductSpace BigOperators

set_option autoImplicit false

namespace Commons.Geometry.Ulam

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

lemma interior_nonempty_body_of_revolution [NeZero d] {R₁ R₂ : ℝ} {f : ℝ → ℝ}
    (hR : -R₁ < R₂) (hf_cont : ContinuousOn f (Set.Ioo (-R₁) R₂))
    (hf_pos : ∀ t ∈ Set.Ioo (-R₁) R₂, 0 < f t) :
    (interior {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂ ∧
      ∑ i > 0, (x i)^2 ≤ (f (x 0))^2}).Nonempty := by
  classical
  obtain ⟨t, ht_lower, ht_upper⟩ : ∃ t : ℝ, -R₁ < t ∧ t < R₂ := exists_between hR
  have ht_mem : t ∈ Set.Ioo (-R₁) R₂ := ⟨ht_lower, ht_upper⟩
  let c : ℝ := f t / 2
  have hc_pos : 0 < c := by
    dsimp [c]
    exact half_pos (hf_pos t ht_mem)
  have hf_cont_at : ContinuousAt f t := by
    exact hf_cont.continuousAt (IsOpen.mem_nhds isOpen_Ioo ht_mem)
  obtain ⟨η, hη_pos, hη⟩ := (Metric.continuousAt_iff.mp hf_cont_at) c hc_pos
  let δ₁ : ℝ := t + R₁
  have hδ₁_pos : 0 < δ₁ := by
    dsimp [δ₁]
    linarith
  let δ₂ : ℝ := R₂ - t
  have hδ₂_pos : 0 < δ₂ := by
    dsimp [δ₂]
    linarith
  let δ : ℝ := min η (min c (min δ₁ δ₂))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ_le_η : δ ≤ η := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ_le_c : δ ≤ c := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ_le_δ₁ : δ ≤ δ₁ := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ_le_δ₂ : δ ≤ δ₂ := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  let x : ℝᵈ := EuclideanSpace.single (0 : Fin d) t
  have hx_mem : x ∈ {x : ℝᵈ | x 0 ∈ Set.Icc (-R₁) R₂ ∧
      ∑ i > 0, (x i)^2 ≤ (f (x 0))^2} := by
    constructor
    · dsimp [x]
      exact ⟨le_of_lt ht_lower, le_of_lt ht_upper⟩
    · have hsum_zero : (∑ i > 0, (x i)^2) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hi_pos : 0 < i := Finset.mem_Ioi.mp hi
        simp [x, hi_pos.ne']
      rw [hsum_zero]
      dsimp [x]
      nlinarith [sq_nonneg (f t)]
  refine ⟨x, ?_⟩
  rw [mem_interior]
  refine ⟨Metric.ball x δ, ?_, Metric.isOpen_ball, Metric.mem_ball_self hδ_pos⟩
  intro y hy
  have hdist : dist y x < δ := (Metric.mem_ball.mp hy)
  have hy0_dist_le : dist (y 0) t ≤ dist y x := by
    have h := PiLp.dist_apply_le y x (0 : Fin d)
    simpa [x] using h
  have hy0_abs_lt : |y 0 - t| < δ := by
    have hlt : dist (y 0) t < δ := lt_of_le_of_lt hy0_dist_le hdist
    rwa [Real.dist_eq] at hlt
  have hy0_mem : y 0 ∈ Set.Icc (-R₁) R₂ := by
    have h1 := (abs_lt.mp hy0_abs_lt).1
    have h2 := (abs_lt.mp hy0_abs_lt).2
    constructor
    · have : -R₁ < y 0 := by linarith
      exact le_of_lt this
    · have : y 0 < R₂ := by linarith
      exact le_of_lt this
  have hy0_dist_η : dist (y 0) t < η :=
    lt_of_le_of_lt hy0_dist_le (lt_of_lt_of_le hdist hδ_le_η)
  have hf_lt : dist (f (y 0)) (f t) < c := hη hy0_dist_η
  have hfy_gt_c : c < f (y 0) := by
    have hf_lt_real : |f (y 0) - f t| < c := by
      rwa [Real.dist_eq] at hf_lt
    have h := abs_sub_lt_iff.mp hf_lt_real
    have hlt_add : f t < c + f (y 0) := sub_lt_iff_lt_add.mp h.2
    have h2c : f t = 2 * c := by
      dsimp [c]
      ring
    linarith
  have hfy_pos : 0 < f (y 0) := lt_trans hc_pos hfy_gt_c
  have hsum_le_dist_sq : (∑ i > 0, (y i)^2) ≤ dist y x ^ 2 := by
    have hs_sum : (∑ i ∈ Finset.Ioi (0 : Fin d), (y i)^2) =
        ∑ i ∈ Finset.Ioi (0 : Fin d), (y i - x i)^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi_pos : 0 < i := Finset.mem_Ioi.mp hi
      have hx : x i = 0 := by
        dsimp [x]
        simp [hi_pos.ne']
      simp [hx]
    have hsubset_le : (∑ i ∈ Finset.Ioi (0 : Fin d), (y i - x i)^2) ≤
        ∑ i, (y i - x i)^2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intro i hi hnot
        exact sq_nonneg _
    have hfull : (∑ i, (y i - x i)^2) = dist y x ^ 2 := by
      rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
      simp
    calc
      ∑ i > 0, (y i)^2 = ∑ i ∈ Finset.Ioi (0 : Fin d), (y i)^2 := by rfl
      _ = ∑ i ∈ Finset.Ioi (0 : Fin d), (y i - x i)^2 := hs_sum
      _ ≤ ∑ i, (y i - x i)^2 := hsubset_le
      _ = dist y x ^ 2 := hfull
  have hdist_sq_lt_delta_sq : dist y x ^ 2 < δ ^ 2 := by
    exact pow_lt_pow_left₀ hdist (dist_nonneg) (by norm_num : 2 ≠ 0)
  have hdelta_sq_le_c_sq : δ ^ 2 ≤ c ^ 2 := by
    exact pow_le_pow_left₀ (le_of_lt hδ_pos) hδ_le_c 2
  have hdist_sq_lt_c_sq : dist y x ^ 2 < c ^ 2 :=
    lt_of_lt_of_le hdist_sq_lt_delta_sq hdelta_sq_le_c_sq
  have hc_sq_lt_fy_sq : c ^ 2 < (f (y 0)) ^ 2 := by
    exact (sq_lt_sq₀ (le_of_lt hc_pos) (le_of_lt hfy_pos)).2 hfy_gt_c
  have hsum_lt_fy_sq : (∑ i > 0, (y i)^2) < (f (y 0)) ^ 2 :=
    lt_of_le_of_lt hsum_le_dist_sq (lt_trans hdist_sq_lt_c_sq hc_sq_lt_fy_sq)
  constructor
  · exact hy0_mem
  · exact le_of_lt hsum_lt_fy_sq

end Commons.Geometry.Ulam