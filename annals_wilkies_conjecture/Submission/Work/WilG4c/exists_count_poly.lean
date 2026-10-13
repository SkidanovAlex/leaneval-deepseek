import Mathlib
import Submission.Work.WilG5.PolyEval.nat_poly_bound
import Submission.Work.WilG5.PolyEval.poly_abs_bound

namespace Work.WilG4c

/-! ## Two polynomial-domination pieces

The proof of `exists_count_poly` factors the two factors of the left hand side into two
independent polynomial-domination statements, and then multiplies the resulting polynomials
(taking care that the first factor only uses the variables `D, r, k` and the second only
`D, r, -log ε`).

* `nat_compose_bound_aux`: the *natural* composition `b (B₀(D,r), k*K+1)` is dominated by a
  real polynomial in `(D, r, k)`.  This is immediate from the crude growth bound
  `nat_poly_bound` for `b` and `B₀`.
* `real_shift_bound_aux`: `|c (D + B₁(D,r), r, 1, s + log 2)|` is dominated, for `s ≥ 0`, by a
  real polynomial in `(D, r, s)`.  This is the crude growth bound `poly_abs_bound` for `c`,
  combined with `nat_poly_bound` for `B₁` and the elementary bound `log 2 ≤ 1`.
-/

/-- The natural-coefficient polynomial `b`, composed with `B₀` in its first variable and with
`k ↦ k*K+1` in its second, is dominated by a real polynomial in `(D, r, k)`.

`nat_poly_bound` applied to `b` at the point `(B₀(D,r), k*K+1)` bounds the value by
`Cb * (1 + B₀(D,r) + (k*K+1))^{Nb}`; `nat_poly_bound` applied to `B₀` at `(D,r)` then bounds
`B₀(D,r) ≤ C0 * (1 + D + r)^{N0}`.  The witness is
`C Cb * (1 + C C0*(1 + X₀ + X₁)^{N0} + (C K * X₂ + 1))^{Nb}`. -/
private theorem nat_compose_bound_aux (b B₀ : MvPolynomial (Fin 2) ℕ) (K : ℕ) :
    ∃ P : MvPolynomial (Fin 3) ℝ, ∀ D r k : ℕ,
      (MvPolynomial.eval ![MvPolynomial.eval ![D, r] B₀, k * K + 1] b : ℝ)
        ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ)] P := by
  obtain ⟨Cb, Nb, hCb, hb⟩ := Work.WilG5.PolyEval.nat_poly_bound b
  obtain ⟨C0, N0, hC0, h0⟩ := Work.WilG5.PolyEval.nat_poly_bound B₀
  refine ⟨MvPolynomial.C Cb *
      (MvPolynomial.C 1 + MvPolynomial.C C0 *
          (MvPolynomial.C 1 + MvPolynomial.X 0 + MvPolynomial.X 1) ^ N0
        + (MvPolynomial.C (K : ℝ) * MvPolynomial.X 2 + MvPolynomial.C 1)) ^ Nb, ?_⟩
  intro D r k
  have hA : ((MvPolynomial.eval ![D, r] B₀ : ℕ) : ℝ) ≤ C0 * (1 + (D : ℝ) + (r : ℝ)) ^ N0 := by
    simpa [Fin.sum_univ_two, add_assoc] using h0 (![D, r] : Fin 2 → ℕ)
  have hBk : ((k * K + 1 : ℕ) : ℝ) = (K : ℝ) * (k : ℝ) + 1 := by push_cast; ring
  have hb' := hb (![MvPolynomial.eval ![D, r] B₀, k * K + 1] : Fin 2 → ℕ)
  have hsumb : (∑ i : Fin 2,
      (((![MvPolynomial.eval ![D, r] B₀, k * K + 1] : Fin 2 → ℕ) i : ℕ) : ℝ))
      = ((MvPolynomial.eval ![D, r] B₀ : ℕ) : ℝ) + ((k * K + 1 : ℕ) : ℝ) := by
    simp [Fin.sum_univ_two]
  rw [hsumb] at hb'
  have heval : MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ)]
      (MvPolynomial.C Cb *
        (MvPolynomial.C 1 + MvPolynomial.C C0 *
            (MvPolynomial.C 1 + MvPolynomial.X 0 + MvPolynomial.X 1) ^ N0
          + (MvPolynomial.C (K : ℝ) * MvPolynomial.X 2 + MvPolynomial.C 1)) ^ Nb)
      = Cb * (1 + C0 * (1 + (D : ℝ) + (r : ℝ)) ^ N0 + ((K : ℝ) * (k : ℝ) + 1)) ^ Nb := by
    simp [MvPolynomial.eval_X, MvPolynomial.eval_C, MvPolynomial.eval_add,
      MvPolynomial.eval_mul, MvPolynomial.eval_pow]
  rw [heval]
  refine le_trans hb' ?_
  apply mul_le_mul_of_nonneg_left _ hCb
  apply pow_le_pow_left₀ (by positivity)
  rw [hBk]
  linarith [hA]

/-- `|c (D + B₁(D,r), r, 1, s + log 2)|` is dominated, for `s ≥ 0`, by a real polynomial in
`(D, r, s)`.

`poly_abs_bound` applied to `c` bounds the value by `Cc * (1 + X₀ + X₁ + 1 + X₃)^{Nc}` where
`X₀ = D + B₁(D,r) ≤ D + C1*(1 + D + r)^{N1}` (using `nat_poly_bound` for `B₁`) and
`X₃ = s + log 2 ≤ s + 1` for `s ≥ 0`.  The witness is
`C Cc * (1 + (X₀ + C C1*(1 + X₀ + X₁)^{N1}) + X₁ + 1 + (X₂ + 1))^{Nc}`. -/
private theorem real_shift_bound_aux (c : MvPolynomial (Fin 4) ℝ) (B₁ : MvPolynomial (Fin 2) ℕ) :
    ∃ Q : MvPolynomial (Fin 3) ℝ, ∀ D r : ℕ, ∀ s : ℝ, 0 ≤ s →
      |MvPolynomial.eval ![((D + MvPolynomial.eval ![D, r] B₁ : ℕ) : ℝ), (r : ℝ), (1 : ℝ),
          s + Real.log 2] c|
        ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), s] Q := by
  obtain ⟨Cc, Nc, hCc, hc⟩ := Work.WilG5.PolyEval.poly_abs_bound c
  obtain ⟨C1, N1, hC1, h1⟩ := Work.WilG5.PolyEval.nat_poly_bound B₁
  refine ⟨MvPolynomial.C Cc *
      (MvPolynomial.C 1 + (MvPolynomial.X 0 + MvPolynomial.C C1 *
          (MvPolynomial.C 1 + MvPolynomial.X 0 + MvPolynomial.X 1) ^ N1)
        + MvPolynomial.X 1 + MvPolynomial.C 1 + (MvPolynomial.X 2 + MvPolynomial.C 1)) ^ Nc, ?_⟩
  intro D r s hs
  let X : Fin 4 → ℝ :=
    ![((D + MvPolynomial.eval ![D, r] B₁ : ℕ) : ℝ), (r : ℝ), (1 : ℝ), s + Real.log 2]
  have hA1 : ((MvPolynomial.eval ![D, r] B₁ : ℕ) : ℝ) ≤ C1 * (1 + (D : ℝ) + (r : ℝ)) ^ N1 := by
    simpa [Fin.sum_univ_two, add_assoc] using h1 (![D, r] : Fin 2 → ℕ)
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have habs0 : |X 0| = (D : ℝ) + ((MvPolynomial.eval ![D, r] B₁ : ℕ) : ℝ) := by
    rw [show X 0 = ((D : ℝ) + ((MvPolynomial.eval ![D, r] B₁ : ℕ) : ℝ)) by simp [X]]
    exact abs_of_nonneg (by positivity)
  have habs1 : |X 1| = (r : ℝ) := by
    rw [show X 1 = (r : ℝ) by simp [X]]; exact abs_of_nonneg (Nat.cast_nonneg _)
  have habs2 : |X 2| = (1 : ℝ) := by
    rw [show X 2 = (1 : ℝ) by simp [X]]; norm_num
  have habs3 : |X 3| = s + Real.log 2 := by
    rw [show X 3 = s + Real.log 2 by simp [X]]
    exact abs_of_nonneg (add_nonneg hs (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)))
  have habssum : (∑ i : Fin 4, |X i|) =
      ((D : ℝ) + ((MvPolynomial.eval ![D, r] B₁ : ℕ) : ℝ)) + (r : ℝ) + 1 + (s + Real.log 2) := by
    rw [Fin.sum_univ_four, habs0, habs1, habs2, habs3]
  have hSle : 1 + (∑ i : Fin 4, |X i|)
      ≤ 1 + ((D : ℝ) + C1 * (1 + (D : ℝ) + (r : ℝ)) ^ N1) + (r : ℝ) + 1 + (s + 1) := by
    rw [habssum]; linarith [hA1, hlog2]
  have heval : MvPolynomial.eval ![(D : ℝ), (r : ℝ), s]
      (MvPolynomial.C Cc *
        (MvPolynomial.C 1 + (MvPolynomial.X 0 + MvPolynomial.C C1 *
            (MvPolynomial.C 1 + MvPolynomial.X 0 + MvPolynomial.X 1) ^ N1)
          + MvPolynomial.X 1 + MvPolynomial.C 1 + (MvPolynomial.X 2 + MvPolynomial.C 1)) ^ Nc)
      = Cc * (1 + ((D : ℝ) + C1 * (1 + (D : ℝ) + (r : ℝ)) ^ N1) + (r : ℝ) + 1 + (s + 1)) ^ Nc := by
    simp [MvPolynomial.eval_X, MvPolynomial.eval_C, MvPolynomial.eval_add,
      MvPolynomial.eval_mul, MvPolynomial.eval_pow]
  calc |MvPolynomial.eval X c|
      ≤ Cc * (1 + (∑ i : Fin 4, |X i|)) ^ Nc := by simpa using hc X
    _ ≤ Cc * (1 + ((D : ℝ) + C1 * (1 + (D : ℝ) + (r : ℝ)) ^ N1) + (r : ℝ) + 1 + (s + 1)) ^ Nc :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hSle Nc) hCc
    _ = MvPolynomial.eval ![(D : ℝ), (r : ℝ), s]
        (MvPolynomial.C Cc *
          (MvPolynomial.C 1 + (MvPolynomial.X 0 + MvPolynomial.C C1 *
              (MvPolynomial.C 1 + MvPolynomial.X 0 + MvPolynomial.X 1) ^ N1)
            + MvPolynomial.X 1 + MvPolynomial.C 1 + (MvPolynomial.X 2 + MvPolynomial.C 1)) ^ Nc) :=
        heval.symm

/-- The product of (i) a natural multivariate polynomial `b` evaluated at the natural point
`(eval (D,r) B₀, k*K+1)` and (ii) the absolute value of a real polynomial `c` evaluated at
`(D + eval (D,r) B₁, r, 1, -log (ε/2))` is dominated, for `0 < ε < 1`, by a *fixed* real
polynomial `C` evaluated at `(D, r, k, -log ε)`. -/
theorem exists_count_poly (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ)
    (B₀ B₁ : MvPolynomial (Fin 2) ℕ) (K : ℕ) :
    ∃ C : MvPolynomial (Fin 4) ℝ, ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
      (MvPolynomial.eval ![(MvPolynomial.eval ![D, r] B₀), k * K + 1] b : ℝ) *
        |MvPolynomial.eval ![((D + MvPolynomial.eval ![D, r] B₁ : ℕ) : ℝ), (r : ℝ), (1 : ℝ),
          -Real.log (ε / 2)] c|
      ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] C := by
  classical
  obtain ⟨P1, hP1⟩ := nat_compose_bound_aux b B₀ K
  obtain ⟨P2, hP2⟩ := real_shift_bound_aux c B₁
  -- `C` splits the four variables: `P1` only sees `(D, r, k)`, `P2` only sees `(D, r, -log ε)`.
  refine ⟨MvPolynomial.rename (![0, 1, 2] : Fin 3 → Fin 4) P1 *
          MvPolynomial.rename (![0, 1, 3] : Fin 3 → Fin 4) P2, ?_⟩
  intro D r k ε hε0 hε1
  have hlog : -Real.log (ε / 2) = -Real.log ε + Real.log 2 := by
    rw [Real.log_div hε0.ne' (by norm_num : (2 : ℝ) ≠ 0)]; ring
  have hs : 0 ≤ -Real.log ε := by
    rw [neg_nonneg]; exact Real.log_nonpos hε0.le (le_of_lt hε1)
  have hF1 : (MvPolynomial.eval ![MvPolynomial.eval ![D, r] B₀, k * K + 1] b : ℝ)
      ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ)] P1 := hP1 D r k
  have hF2 : |MvPolynomial.eval ![((D + MvPolynomial.eval ![D, r] B₁ : ℕ) : ℝ), (r : ℝ),
        (1 : ℝ), -Real.log (ε / 2)] c|
      ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), -Real.log ε] P2 := by
    rw [hlog]
    exact hP2 D r (-Real.log ε) hs
  have hC : MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε]
        (MvPolynomial.rename (![0, 1, 2] : Fin 3 → Fin 4) P1 *
         MvPolynomial.rename (![0, 1, 3] : Fin 3 → Fin 4) P2)
      = MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ)] P1 *
        MvPolynomial.eval ![(D : ℝ), (r : ℝ), -Real.log ε] P2 := by
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_rename, MvPolynomial.eval_rename]
    have hpt1 : (![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] ∘ (![0, 1, 2] : Fin 3 → Fin 4))
        = ![(D : ℝ), (r : ℝ), (k : ℝ)] := by
      funext i; fin_cases i <;> simp
    have hpt2 : (![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] ∘ (![0, 1, 3] : Fin 3 → Fin 4))
        = ![(D : ℝ), (r : ℝ), -Real.log ε] := by
      funext i; fin_cases i <;> simp
    rw [hpt1, hpt2]
  rw [hC]
  exact mul_le_mul hF1 hF2 (abs_nonneg _) (le_trans (Nat.cast_nonneg _) hF1)

end Work.WilG4c
