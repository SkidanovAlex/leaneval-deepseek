import Submission.Rad.Expansions
set_option autoImplicit false
open Function MeasureTheory ProbabilityTheory Measure
open scoped ENNReal

noncomputable section

namespace RadType
open RademacherEnfloType

/-- The standardized biased random variable: `δ_j(θ)(ξ) = (ξ_j − cos θ)/sin θ`. -/
def delta (θ : ℝ) {n : ℕ} (ξ : Ω n) (j : Fin n) : ℝ :=
  (((ξ j : C) : ℝ) - Real.cos θ) / Real.sin θ

/-- The heat semigroup value `P_θ f(x)`, as an explicit finite sum. -/
noncomputable def heat {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (θ : ℝ) (f : Ω n → X) (x : Ω n) : X :=
  ∑ ξ : Ω n, (biasW θ ξ) • f (mulΩ x ξ)

/-- The heat semigroup value is also the biased expectation of `f(x·ξ)`. -/
lemma heat_eq_integral {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (θ : ℝ) (f : Ω n → X) (x : Ω n) :
    heat θ f x = ∫ ξ : Ω n, f (mulΩ x ξ) ∂biasedMeasure (n := n) θ := by
  unfold heat
  rw [integral_biased_eq θ (fun ξ : Ω n => f (mulΩ x ξ))]

/-- The all-ones cube point. -/
def allOne {n : ℕ} : Ω n := fun _ => cOne

@[simp] lemma mulΩ_allOne {n : ℕ} (x : Ω n) : mulΩ x (allOne (n := n)) = x := by
  ext i
  simp [allOne]

/-- The weight at `θ = 0` is the indicator of the all-ones point. -/
lemma biasW_zero_indicator {n : ℕ} (ξ : Ω n) :
    biasW 0 ξ = if ξ = allOne (n := n) then (1 : ℝ) else 0 := by
  by_cases hξ : ξ = allOne (n := n)
  · rw [if_pos hξ]
    subst hξ
    unfold biasW
    simp [allOne]
  · rw [if_neg hξ]
    unfold biasW
    have hne : ∃ j : Fin n, ξ j ≠ cOne := by
      by_contra h
      push_neg at h
      apply hξ
      funext j
      have hj : ξ j = cOne := h j
      exact hj
    rcases hne with ⟨j, hj⟩
    have hz : ((ξ j : C) : ℝ) = -1 := by
      rcases val_eq (ξ j) with h | h
      · exact False.elim (hj (by apply Subtype.ext; simpa [cOne] using h))
      · have : (ξ j : C) = cNegOne := by
          apply Subtype.ext
          simpa [cNegOne] using h
        rw [this]
        norm_num [cNegOne]
    -- product contains a zero factor at j
    have hprod : (∏ k : Fin n, ((1 + ((ξ k : C) : ℝ)) / 2)) = 0 := by
      rw [Finset.prod_eq_zero_iff]
      refine ⟨j, Finset.mem_univ j, ?_⟩
      simp [hz]
    simpa [hprod]

/-- heat at `θ=0` is the identity: `P_0 f(x) = f(x)`. -/
lemma heat_zero {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : Ω n → X) (x : Ω n) : heat 0 f x = f x := by
  unfold heat
  classical
  rw [show (∑ ξ : Ω n, (biasW 0 ξ) • f (mulΩ x ξ))
      = ∑ ξ : Ω n, (if ξ = allOne (n := n) then (1 : ℝ) else 0) • f (mulΩ x ξ) by
        refine Finset.sum_congr rfl ?_
        intro ξ hξ
        rw [biasW_zero_indicator ξ]]
  simp

/-- heat at `θ=π/2` is the uniform mean: `P_{π/2} f(x) = 𝔼 f`. -/
lemma heat_pi_half {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (f : Ω n → X) (x : Ω n) :
    heat (Real.pi / 2) f x = meanX f := by
  unfold heat
  -- weights at cos(π/2) = 0 are all 2^{-n}
  have hcos : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
  have hw : ∀ ξ : Ω n, biasW (Real.pi / 2) ξ = (1 / 2 : ℝ) ^ n := by
    intro ξ
    unfold biasW
    simp [hcos]
  calc
    (∑ ξ : Ω n, biasW (Real.pi / 2) ξ • f (mulΩ x ξ))
        = ∑ ξ : Ω n, ((1 / 2 : ℝ) ^ n) • f (mulΩ x ξ) := by
          refine Finset.sum_congr rfl ?_
          intro ξ hξ
          rw [hw ξ]
    _ = ∑ y : Ω n, ((1 / 2 : ℝ) ^ n) • f y := by
          classical
          let e : Ω n ≃ Ω n :=
            { toFun := fun ξ => mulΩ x ξ
              invFun := fun y => mulΩ x y
              left_inv := by intro ξ; simp
              right_inv := by intro y; simp }
          exact Equiv.sum_comp e (fun y : Ω n => ((1 / 2 : ℝ) ^ n) • f y)
    _ = meanX f := by
          unfold meanX
          rw [integral_uniform_eq (fun y : Ω n => f y)]

end RadType
end
