import Mathlib

namespace Work.Maximal

theorem mstEta_lipschitz (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) :
    ∃ L : ℝ, 0 < L ∧ ∀ u v : ℝ, ‖η u - η v‖ ≤ L * |u - v| := by
  -- The derivative of η vanishes outside the closed interval [-1/2, 1/2].
  have hfderiv_zero : ∀ x : ℝ, 1 / 2 < |x| → fderiv ℝ η x = 0 := by
    intro x hx
    have heq : η =ᶠ[nhds x] (fun _ : ℝ => (0 : ℂ)) := by
      show ∀ᶠ y in nhds x, η y = (0 : ℂ)
      rw [Metric.eventually_nhds_iff]
      refine ⟨|x| - 1 / 2, by linarith, fun y hy => ?_⟩
      apply hηsup
      have h1 : |x| - |y| ≤ |x - y| := (le_abs_self _).trans (abs_abs_sub_abs_le x y)
      have h2 : |x - y| = dist y x := by rw [Real.dist_eq, abs_sub_comm]
      linarith
    rw [show fderiv ℝ η x = fderiv ℝ (fun _ : ℝ => (0 : ℂ)) x from heq.fderiv_eq]
    simp [fderiv_fun_const]
  -- The derivative is bounded on the compact interval, and zero outside it.
  have hcd : Continuous (fderiv ℝ η) := hηc.continuous_fderiv (by norm_num)
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc
    (f := fderiv ℝ η) hcd.continuousOn
  have hfderiv_bound : ∀ x : ℝ, ‖fderiv ℝ η x‖ ≤ max C 0 := by
    intro x
    by_cases hx : x ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)
    · exact (hC x hx).trans (le_max_left _ _)
    · have hx' : 1 / 2 < |x| := by
        have h1 : ¬ (-1 / 2 ≤ x ∧ x ≤ 1 / 2) := by simpa [Set.mem_Icc] using hx
        rcases not_and_or.mp h1 with h | h
        · have h2 : x < -1 / 2 := not_le.mp h
          rw [abs_of_neg (by linarith)]
          linarith
        · have h2 : 1 / 2 < x := not_le.mp h
          rw [abs_of_pos (by linarith)]
          linarith
      rw [hfderiv_zero x hx', norm_zero]
      exact le_max_right _ _
  refine ⟨max (max C 0) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun u v => ?_⟩
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (f := η) (C := max C 0) (s := Set.univ)
    (fun x _ => (hηc.differentiable (by norm_num)).differentiableAt)
    (fun x _ => hfderiv_bound x) convex_univ (Set.mem_univ u) (Set.mem_univ v)
  rw [Real.norm_eq_abs, abs_sub_comm, norm_sub_rev] at hmvt
  exact hmvt.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))

end Work.Maximal
