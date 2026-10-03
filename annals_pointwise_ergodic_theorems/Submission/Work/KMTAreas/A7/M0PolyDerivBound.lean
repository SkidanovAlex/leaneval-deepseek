import Mathlib
import Submission.Work.A7.m0w_bound

namespace Work.KMTAreas.A7

/-- Pointwise value and first-derivative bounds for `m0poly P j₁ j₂ t = (2πit)^{j₁}(2πiP(t))^{j₂}` on the window `[0,N]`, for `j₁,j₂ ≤ 2`, from the polynomial-growth bounds on `PevalR P` and its derivative; the constant `B` is uniform in `N`, `t`, `j₁`, `j₂`. -/
theorem M0PolyDerivBound (P : Polynomial ℤ) {A : ℝ} (hA : 0 ≤ A)
    (hval : ∀ (N : ℕ), 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
      |Work.KMTAreas.A7.PevalR P t| ≤ A * (N : ℝ) ^ P.natDegree)
    (hder : ∀ (N : ℕ), 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
      |deriv (Work.KMTAreas.A7.PevalR P) t| ≤ A * (N : ℝ) ^ P.natDegree / (N : ℝ)) :
    ∃ B : ℝ, 0 < B ∧ ∀ (N : ℕ), 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
      ∀ j₁ j₂ : ℕ, j₁ ≤ 2 → j₂ ≤ 2 →
        ‖Work.A7.m0poly P j₁ j₂ t‖ ≤ B * (N : ℝ) ^ (j₁ + P.natDegree * j₂) ∧
        ‖deriv (Work.A7.m0poly P j₁ j₂) t‖
          ≤ B * (N : ℝ) ^ (j₁ + P.natDegree * j₂) / (N : ℝ) := by
  -- The second-derivative hypothesis needed by the model-weight estimate is *not* assumed;
  -- it is supplied by the coefficient-sum bound `PevalR_deriv_bounds` for the polynomial `P`.
  obtain ⟨C, hCpos, hC⟩ := Work.A7.Pev.PevalR_deriv_bounds P
  set A' : ℝ := max A C with hA'eq
  have hAA' : A ≤ A' := le_max_left _ _
  have hCA' : C ≤ A' := le_max_right _ _
  have hA'0 : 0 ≤ A' := le_trans hA hAA'
  -- the three growth bounds with the common constant `A'`
  have hval' : ∀ (N : ℕ), 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
      |Work.KMTAreas.A7.PevalR P t| ≤ A' * (N : ℝ) ^ P.natDegree := by
    intro N hN t ht
    exact (hval N hN t ht).trans
      (mul_le_mul_of_nonneg_right hAA' (pow_nonneg (Nat.cast_nonneg N) _))
  have hder' : ∀ (N : ℕ), 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
      |deriv (Work.KMTAreas.A7.PevalR P) t| ≤ A' * (N : ℝ) ^ P.natDegree / (N : ℝ) := by
    intro N hN t ht
    exact (hder N hN t ht).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hAA' (pow_nonneg (Nat.cast_nonneg N) _))
        (Nat.cast_nonneg N))
  have hP2' : ∀ (N : ℕ), 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
      |iteratedDeriv 2 (Work.KMTAreas.A7.PevalR P) t|
        ≤ A' * (N : ℝ) ^ P.natDegree / (N : ℝ) ^ 2 := by
    intro N hN t ht
    exact ((hC N hN t ht).2.2).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCA' (pow_nonneg (Nat.cast_nonneg N) _))
        (pow_nonneg (Nat.cast_nonneg N) 2))
  refine ⟨2 * (400 * (4 * max 1 ((2 * Real.pi * A') ^ 2))), by positivity, ?_⟩
  intro N hN t ht j₁ j₂ hj₁ hj₂
  obtain ⟨h0, h1, _⟩ := Work.A7.m0poly_bounds P hA'0 hval' hder' hP2'
    (N := N) hN (t := t) ht (j₁ := j₁) (j₂ := j₂) hj₁ hj₂
  have hKnn : (0 : ℝ) ≤ 400 * (4 * max 1 ((2 * Real.pi * A') ^ 2)) := by positivity
  have hNpow : (0 : ℝ) ≤ (N : ℝ) ^ (j₁ + P.natDegree * j₂) :=
    pow_nonneg (Nat.cast_nonneg N) _
  exact ⟨h0.trans (mul_le_mul_of_nonneg_right (by linarith) hNpow), h1⟩

end Work.KMTAreas.A7
