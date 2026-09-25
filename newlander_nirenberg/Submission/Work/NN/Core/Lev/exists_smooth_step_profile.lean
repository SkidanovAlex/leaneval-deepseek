import Mathlib
import Submission.Work.NN.Core.Lev.smoothTransition_deriv_data

open scoped ContDiff

namespace Work.NN.Core.Lev

/-- **Existence of a smooth step profile with globally bounded, Lipschitz derivative.**

Taking `Ψ t = 1 - Real.smoothTransition t` gives a `C^∞` function with `Ψ = 1` on `(-∞,0]`,
`Ψ = 0` on `[1,∞)` and `0 ≤ Ψ ≤ 1`.  Its derivative is `-σ'` and its second derivative is
`-σ''` where `σ = Real.smoothTransition`; by `smoothTransition_deriv_bounds` both are globally
bounded, and the mean value theorem applied to `deriv Ψ` turns the bound on `deriv (deriv Ψ)`
into a global Lipschitz bound. -/
theorem exists_smooth_step_profile :
    ∃ Ψ : ℝ → ℝ, (∀ m : ℕ, ContDiff ℝ m Ψ) ∧ (∀ t, 0 ≤ Ψ t ∧ Ψ t ≤ 1) ∧
      (∀ t, t ≤ 0 → Ψ t = 1) ∧ (∀ t, 1 ≤ t → Ψ t = 0) ∧
      ∃ C : ℝ, 0 < C ∧ (∀ t : ℝ, |deriv Ψ t| ≤ C) ∧
        ∀ s t : ℝ, |deriv Ψ s - deriv Ψ t| ≤ C * |s - t| := by
  obtain ⟨C₁, C₂, hC₁0, hC₂0, hb1, hb2, -, -, -, -⟩ := smoothTransition_deriv_bounds
  refine ⟨fun t => 1 - Real.smoothTransition t, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    exact (contDiff_const : ContDiff ℝ m (fun _ : ℝ => (1 : ℝ))).sub
      (Real.smoothTransition.contDiff (n := (m : ℕ∞)))
  · intro t
    have h1 := Real.smoothTransition.nonneg t
    have h2 := Real.smoothTransition.le_one t
    constructor <;> linarith
  · intro t ht
    show 1 - Real.smoothTransition t = 1
    rw [Real.smoothTransition.zero_of_nonpos ht]
    ring
  · intro t ht
    show 1 - Real.smoothTransition t = 0
    rw [Real.smoothTransition.one_of_one_le ht]
    ring
  · refine ⟨C₁ + C₂ + 1, by linarith, ?_, ?_⟩
    · intro t
      have hdt : deriv (fun t : ℝ => 1 - Real.smoothTransition t) t
          = - deriv Real.smoothTransition t := deriv_const_sub (1 : ℝ)
      rw [hdt, abs_neg]
      linarith [hb1 t]
    · intro s t
      have hderiv : deriv (fun t : ℝ => 1 - Real.smoothTransition t)
          = fun t => - deriv Real.smoothTransition t := deriv_const_sub' (1 : ℝ)
      have hdiff : ∀ x ∈ (Set.univ : Set ℝ),
          DifferentiableAt ℝ (fun t : ℝ => - deriv Real.smoothTransition t) x := by
        intro x _
        exact ((contDiff_deriv_smoothTransition.neg).differentiable (by simp)).differentiableAt
      have hbound : ∀ x ∈ (Set.univ : Set ℝ),
          ‖deriv (fun t : ℝ => - deriv Real.smoothTransition t) x‖ ≤ C₂ := by
        intro x _
        have hdg : deriv (fun t : ℝ => - deriv Real.smoothTransition t) x
            = - deriv (deriv Real.smoothTransition) x := deriv.neg
        rw [hdg, norm_neg, Real.norm_eq_abs]
        exact hb2 x
      have hmain : ‖(fun t : ℝ => - deriv Real.smoothTransition t) s
          - (fun t : ℝ => - deriv Real.smoothTransition t) t‖ ≤ C₂ * ‖s - t‖ :=
        Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound convex_univ
          (Set.mem_univ t) (Set.mem_univ s)
      calc |deriv (fun t : ℝ => 1 - Real.smoothTransition t) s
              - deriv (fun t : ℝ => 1 - Real.smoothTransition t) t|
          = ‖(fun t : ℝ => - deriv Real.smoothTransition t) s
              - (fun t : ℝ => - deriv Real.smoothTransition t) t‖ := by
            rw [hderiv, Real.norm_eq_abs]
        _ ≤ C₂ * ‖s - t‖ := hmain
        _ = C₂ * |s - t| := by rw [Real.norm_eq_abs]
        _ ≤ (C₁ + C₂ + 1) * |s - t| :=
            mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)

end Work.NN.Core.Lev
