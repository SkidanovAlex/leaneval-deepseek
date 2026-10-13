import Mathlib

namespace Work.WilG4a.locFallbackAux

/-- Expansion of the evaluation of a multivariate polynomial as a sum over its support. -/
private lemma eval_eq_sum (c : MvPolynomial (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    c.eval v = ∑ m ∈ c.support, c.coeff m * (m.prod fun n e => v n ^ e) := by
  conv_lhs => rw [MvPolynomial.as_sum c]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [MvPolynomial.eval_monomial]

/-- Evaluation of a single monomial of `MvPolynomial (Fin 3) ℝ` at `![D, r, 1]`. -/
private lemma prod_eval (m : Fin 3 →₀ ℕ) (D r : ℕ) :
    m.prod (fun n e => (![(D:ℝ),(r:ℝ),(1:ℝ)] : Fin 3 → ℝ) n ^ e)
      = (D:ℝ)^(m 0) * (r:ℝ)^(m 1) := by
  rw [Finsupp.prod_of_support_subset m (Finset.subset_univ _) _ (by intro i hi; simp)]
  rw [Fin.prod_univ_three]
  simp

/-- Any real polynomial in three variables evaluated at `![D, r, 1]` for nonnegative
integers `D`, `r` is bounded above by a polynomial with natural coefficients in `D`, `r`. -/
theorem realPoly_le_natPoly (c : MvPolynomial (Fin 3) ℝ) :
    ∃ d : MvPolynomial (Fin 2) ℕ, ∀ D r : ℕ,
      c.eval ![(D : ℝ), (r : ℝ), (1 : ℝ)] ≤ (d.eval ![D, r] : ℝ) := by
  classical
  set A : ℕ := ∑ m ∈ c.support, m 0 with hA
  set B : ℕ := ∑ m ∈ c.support, m 1 with hB
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (∑ m ∈ c.support, |c.coeff m|) ≤ (N:ℝ) :=
    ⟨Nat.ceil _, Nat.le_ceil _⟩
  set d : MvPolynomial (Fin 2) ℕ :=
    MvPolynomial.C N * ((MvPolynomial.X (0 : Fin 2) + 1)^A * (MvPolynomial.X (1 : Fin 2) + 1)^B) with hd_def
  refine ⟨d, ?_⟩
  intro D r
  have hd : (d.eval ![D,r] : ℝ) = (N:ℝ) * (((D:ℝ)+1)^A * ((r:ℝ)+1)^B) := by
    rw [hd_def]
    push_cast
    simp [MvPolynomial.eval_X]
  rw [hd]
  have heval : c.eval ![(D:ℝ),(r:ℝ),(1:ℝ)]
      = ∑ m ∈ c.support, c.coeff m * ((D:ℝ)^(m 0) * (r:ℝ)^(m 1)) := by
    rw [eval_eq_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [prod_eval]
  rw [heval]
  calc ∑ m ∈ c.support, c.coeff m * ((D:ℝ)^(m 0) * (r:ℝ)^(m 1))
      ≤ ∑ m ∈ c.support, |c.coeff m| * (((D:ℝ)+1)^A * ((r:ℝ)+1)^B) := by
        apply Finset.sum_le_sum
        intro m hm
        have hm0 : m 0 ≤ A := by
          rw [hA]
          exact Finset.single_le_sum (f := fun x : Fin 3 →₀ ℕ => x 0) (fun i hi => Nat.zero_le _) hm
        have hm1 : m 1 ≤ B := by
          rw [hB]
          exact Finset.single_le_sum (f := fun x : Fin 3 →₀ ℕ => x 1) (fun i hi => Nat.zero_le _) hm
        have hXnn : 0 ≤ (D:ℝ)^(m 0) * (r:ℝ)^(m 1) := by positivity
        have hXY : (D:ℝ)^(m 0) * (r:ℝ)^(m 1) ≤ ((D:ℝ)+1)^A * ((r:ℝ)+1)^B := by
          apply mul_le_mul
          · calc (D:ℝ)^(m 0) ≤ ((D:ℝ)+1)^(m 0) := pow_le_pow_left₀ (by positivity) (by linarith) _
              _ ≤ ((D:ℝ)+1)^A := pow_le_pow_right₀ (by linarith) hm0
          · calc (r:ℝ)^(m 1) ≤ ((r:ℝ)+1)^(m 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
              _ ≤ ((r:ℝ)+1)^B := pow_le_pow_right₀ (by linarith) hm1
          · positivity
          · positivity
        calc c.coeff m * ((D:ℝ)^(m 0) * (r:ℝ)^(m 1))
            ≤ |c.coeff m| * ((D:ℝ)^(m 0) * (r:ℝ)^(m 1)) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) hXnn
          _ ≤ |c.coeff m| * (((D:ℝ)+1)^A * ((r:ℝ)+1)^B) :=
              mul_le_mul_of_nonneg_left hXY (abs_nonneg _)
    _ = (∑ m ∈ c.support, |c.coeff m|) * (((D:ℝ)+1)^A * ((r:ℝ)+1)^B) := by
        rw [← Finset.sum_mul]
    _ ≤ (N:ℝ) * (((D:ℝ)+1)^A * ((r:ℝ)+1)^B) := by
        apply mul_le_mul_of_nonneg_right hN
        positivity

end Work.WilG4a.locFallbackAux
