import Mathlib
import Submission.Work.WilG5.Defs
import Submission.Work.WilG5.PolyEval.poly_abs_bound

namespace Work.WilG5.Count

/-- A univariate polynomial with natural coefficients grows at most like `(D+1)^d`:
`p.eval D ≤ K * (D+1)^d` with `K` the sum of the coefficients of `p` and `d = p.natDegree`.

The only ingredient is `D ^ i ≤ (D+1) ^ p.natDegree` for `i ≤ p.natDegree` (the exponent
bound `Polynomial.le_natDegree_of_mem_supp`), multiplied through the nonnegative (natural)
coefficients. -/
lemma natPoly_eval_le (p : Polynomial ℕ) :
    ∃ K d : ℕ, ∀ D : ℕ, p.eval D ≤ K * (D + 1) ^ d := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i, p.natDegree, fun D => ?_⟩
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi_le : i ≤ p.natDegree := by
    have := Finset.mem_range.mp hi; omega
  have h1 : D ^ i ≤ (D + 1) ^ p.natDegree := by
    calc D ^ i ≤ (D + 1) ^ i := Nat.pow_le_pow_left (Nat.le_succ D) i
      _ ≤ (D + 1) ^ p.natDegree := Nat.pow_le_pow_right (Nat.succ_pos D) hi_le
  exact Nat.mul_le_mul_left _ h1

/-- `Count.dominate`: a real polynomial `c` in four variables, evaluated along the
"controlled" curve
`(↑(C₀ * cD.eval D + L₀), ↑r, ↑nn, s + ↑L₁)` (`D, r : ℕ`, `s : ℝ`, `s ≥ 0`), is dominated in
absolute value by a *single* polynomial `p` in the three variables `(D, r, s)` all of whose
coefficients are nonnegative.

The three inputs are nonnegative on the curve, and each of them is at most a polynomial in the
new variables: the first by `natPoly_eval_le` (with constants `B`, `d`), the last two trivially.
Combining `PolyEval.poly_abs_bound` for `c` with these bounds, the dominating polynomial is
`M * (K' * (D+1)^d + r + s + 1)^N`, where `M` is a natural upper bound for the constant of
`poly_abs_bound`, `N` its exponent and `K' = C₀ * B + L₀ + nn + L₁ + 1`. It is realised as the
image under `Nat.castRingHom ℝ` of a `ℕ`-coefficient polynomial, so that its coefficients are
immediately nonnegative. -/
theorem dominate (c : MvPolynomial (Fin 4) ℝ) (cD : Polynomial ℕ) (C₀ L₀ L₁ nn : ℕ) :
    ∃ p : MvPolynomial (Fin 3) ℝ, (∀ m ∈ p.support, 0 ≤ p.coeff m) ∧
      ∀ (D r : ℕ) (s : ℝ), 0 ≤ s →
        |c.eval ![(↑(C₀ * cD.eval D + L₀) : ℝ), (r : ℝ), (nn : ℝ), s + (L₁ : ℝ)]| ≤
          MvPolynomial.eval ![(D : ℝ), (r : ℝ), s] p := by
  classical
  obtain ⟨C, N, hC, hbound⟩ := Work.WilG5.PolyEval.poly_abs_bound c
  obtain ⟨M, hM⟩ := exists_nat_ge C
  obtain ⟨B, d, hBd⟩ := natPoly_eval_le cD
  set K' : ℕ := C₀ * B + L₀ + nn + L₁ + 1 with hK'def
  refine ⟨MvPolynomial.map (Nat.castRingHom ℝ)
      (MvPolynomial.C M * (MvPolynomial.C K' * (MvPolynomial.X 0 + MvPolynomial.C 1) ^ d
        + MvPolynomial.X 1 + MvPolynomial.X 2 + MvPolynomial.C 1) ^ N), ?_, ?_⟩
  · -- nonnegative coefficients: the polynomial is the image of a `ℕ`-coefficient polynomial
    intro m hm
    rw [MvPolynomial.coeff_map]
    exact Nat.cast_nonneg _
  · intro D r s hs
    -- the evaluation of `p` at `(D, r, s)` is `M * (K'*(D+1)^d + r + s + 1)^N`
    let X : Fin 4 → ℝ :=
      ![(↑(C₀ * cD.eval D + L₀) : ℝ), (r : ℝ), (nn : ℝ), s + (L₁ : ℝ)]
    have hEval : MvPolynomial.eval ![(D : ℝ), (r : ℝ), s]
        (MvPolynomial.map (Nat.castRingHom ℝ)
          (MvPolynomial.C M * (MvPolynomial.C K' * (MvPolynomial.X 0 + MvPolynomial.C 1) ^ d
            + MvPolynomial.X 1 + MvPolynomial.X 2 + MvPolynomial.C 1) ^ N))
        = (M : ℝ) * ((K' : ℝ) * ((D : ℝ) + 1) ^ d + (r : ℝ) + s + 1) ^ N := by
      rw [MvPolynomial.eval_map]
      simp only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
        MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, Nat.coe_castRingHom]
      push_cast
      ring
    let T : ℝ := (K' : ℝ) * ((D : ℝ) + 1) ^ d + (r : ℝ) + s + 1
    -- all four coordinates of `X` are nonnegative, so the weight `1 + ∑ |X i|` is additive
    have habs0 : |X 0| = (↑(C₀ * cD.eval D + L₀) : ℝ) := by
      rw [show X 0 = (↑(C₀ * cD.eval D + L₀) : ℝ) from rfl]
      exact abs_of_nonneg (Nat.cast_nonneg _)
    have habs1 : |X 1| = (r : ℝ) := by
      rw [show X 1 = (r : ℝ) from rfl]; exact abs_of_nonneg (Nat.cast_nonneg _)
    have habs2 : |X 2| = (nn : ℝ) := by
      rw [show X 2 = (nn : ℝ) from rfl]; exact abs_of_nonneg (Nat.cast_nonneg _)
    have habs3 : |X 3| = s + (L₁ : ℝ) := by
      rw [show X 3 = s + (L₁ : ℝ) from rfl]
      exact abs_of_nonneg (add_nonneg hs (Nat.cast_nonneg _))
    have habssum : ∑ i, |X i| =
        (↑(C₀ * cD.eval D + L₀) : ℝ) + (r : ℝ) + (nn : ℝ) + (s + (L₁ : ℝ)) := by
      rw [Fin.sum_univ_four, habs0, habs1, habs2, habs3]
    have hS_eq : 1 + ∑ i, |X i| =
        ((↑(C₀ * cD.eval D + L₀) : ℝ) + (nn : ℝ) + (L₁ : ℝ) + 1) + (r : ℝ) + s := by
      rw [habssum]; ring
    -- the bound on the first coordinate coming from `natPoly_eval_le`
    have h1 : (↑(cD.eval D) : ℝ) ≤ (B : ℝ) * ((D : ℝ) + 1) ^ d := by exact_mod_cast hBd D
    have hcast : (↑(C₀ * cD.eval D + L₀) : ℝ) = (C₀ : ℝ) * ↑(cD.eval D) + (L₀ : ℝ) := by
      push_cast; ring
    have hKcast : (↑K' : ℝ) = (C₀ : ℝ) * (B : ℝ) + ((L₀ : ℝ) + (nn : ℝ) + (L₁ : ℝ) + 1) := by
      rw [hK'def]; push_cast; ring
    have hW1 : (1 : ℝ) ≤ ((D : ℝ) + 1) ^ d :=
      one_le_pow₀ (by have h : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D; linarith)
    have hCB : (C₀ : ℝ) * ↑(cD.eval D) ≤ (C₀ : ℝ) * ((B : ℝ) * ((D : ℝ) + 1) ^ d) :=
      mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg C₀)
    have hL : (L₀ : ℝ) + (nn : ℝ) + (L₁ : ℝ) + 1
        ≤ ((L₀ : ℝ) + (nn : ℝ) + (L₁ : ℝ) + 1) * ((D : ℝ) + 1) ^ d :=
      le_mul_of_one_le_right (by positivity) hW1
    have hA : (↑(C₀ * cD.eval D + L₀) : ℝ) + (nn : ℝ) + (L₁ : ℝ) + 1
        ≤ (K' : ℝ) * ((D : ℝ) + 1) ^ d := by
      rw [hcast, hKcast]
      have hexp : ((C₀ : ℝ) * (B : ℝ) + ((L₀ : ℝ) + (nn : ℝ) + (L₁ : ℝ) + 1)) * ((D : ℝ) + 1) ^ d
          = (C₀ : ℝ) * ((B : ℝ) * ((D : ℝ) + 1) ^ d)
            + ((L₀ : ℝ) + (nn : ℝ) + (L₁ : ℝ) + 1) * ((D : ℝ) + 1) ^ d := by ring
      rw [hexp]
      linarith [hCB, hL]
    have hSle : 1 + ∑ i, |X i| ≤ T := by
      rw [hS_eq]
      show ((↑(C₀ * cD.eval D + L₀) : ℝ) + (nn : ℝ) + (L₁ : ℝ) + 1) + (r : ℝ) + s
        ≤ (K' : ℝ) * ((D : ℝ) + 1) ^ d + (r : ℝ) + s + 1
      linarith [hA]
    have hS0 : 0 ≤ 1 + ∑ i, |X i| := by positivity
    calc |c.eval X|
        ≤ C * (1 + ∑ i, |X i|) ^ N := by simpa using hbound X
      _ ≤ (M : ℝ) * T ^ N := by
          have h1 : C * (1 + ∑ i, |X i|) ^ N ≤ (M : ℝ) * (1 + ∑ i, |X i|) ^ N :=
            mul_le_mul_of_nonneg_right hM (pow_nonneg hS0 N)
          have h2 : (M : ℝ) * (1 + ∑ i, |X i|) ^ N ≤ (M : ℝ) * T ^ N :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hS0 hSle N) (le_trans hC hM)
          linarith [h1, h2]
      _ = MvPolynomial.eval ![(D : ℝ), (r : ℝ), s]
            (MvPolynomial.map (Nat.castRingHom ℝ)
              (MvPolynomial.C M * (MvPolynomial.C K' * (MvPolynomial.X 0 + MvPolynomial.C 1) ^ d
                + MvPolynomial.X 1 + MvPolynomial.X 2 + MvPolynomial.C 1) ^ N)) := hEval.symm

end Work.WilG5.Count
