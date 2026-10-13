/-
  WilG5 / Face — `face_count_poly`.

  If `p₀` is a real polynomial in three variables, `L` a natural shift of the first
  coordinate and `N` a natural multiplicity, then `(N : ℝ) * p₀(D+L, r, s)` is dominated,
  for all `D r : ℕ` and `s ≥ 0`, by the value at `(D, r, s)` of a polynomial `p` whose
  coefficients are all nonnegative.

  The construction is deliberately crude.  `PolyEval.poly_abs_bound` gives
  `|p₀(x)| ≤ C * (1 + ∑ i, |x i|)^K` with `C ≥ 0`; at `x = (D+L, r, s)` with `r, s ≥ 0`
  the sum is `1 + (D+L) + r + s`, and since `D, L, r, s ≥ 0`

  `1 + (D+L) + r + s ≤ (D+1) * (1 + L + r + s)`   (difference `= D*(L+r+s) ≥ 0`).

  Hence `(N:ℝ) * p₀(D+L,r,s) ≤ (N:ℝ) * |p₀(D+L,r,s)| ≤ N*C * (D+1)^K * (1+L+r+s)^K`,
  which is the value at `(D,r,s)` of `p = C(N*C) * (X₀+1)^K * (C(1+L) + X₁ + X₂)^K`.
  Every factor of this `p` has nonnegative coefficients (`C` of a nonnegative constant,
  `X₀ + 1`, `C(1+L) + X₁ + X₂`, powers and products of such), which is the remaining
  requirement.
-/
import Mathlib
import Submission.Work.WilG5.PolyEval.poly_abs_bound

namespace Work.WilG5.Face

open MvPolynomial

/-! ## Nonnegative coefficients are closed under the ring operations -/

private lemma coeff_nonneg_C {σ : Type*} [DecidableEq σ] {a : ℝ} (ha : 0 ≤ a) :
    ∀ m : σ →₀ ℕ, 0 ≤ (MvPolynomial.C a : MvPolynomial σ ℝ).coeff m := by
  intro m
  rw [MvPolynomial.coeff_C]
  split_ifs with h
  · exact ha
  · exact le_refl 0

private lemma coeff_nonneg_X {σ : Type*} [DecidableEq σ] (i : σ) :
    ∀ m : σ →₀ ℕ, 0 ≤ (MvPolynomial.X i : MvPolynomial σ ℝ).coeff m := by
  intro m
  rw [MvPolynomial.coeff_X]
  split_ifs with h
  · norm_num
  · exact le_refl 0

private lemma coeff_nonneg_add {σ : Type*} [DecidableEq σ] {p q : MvPolynomial σ ℝ}
    (hp : ∀ m, 0 ≤ p.coeff m) (hq : ∀ m, 0 ≤ q.coeff m) :
    ∀ m, 0 ≤ (p + q).coeff m := by
  intro m
  rw [AddMonoidAlgebra.coeff_add]
  exact add_nonneg (hp m) (hq m)

private lemma coeff_nonneg_mul {σ : Type*} [DecidableEq σ] {p q : MvPolynomial σ ℝ}
    (hp : ∀ m, 0 ≤ p.coeff m) (hq : ∀ m, 0 ≤ q.coeff m) :
    ∀ m, 0 ≤ (p * q).coeff m := by
  intro m
  rw [MvPolynomial.coeff_mul]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hp x.1) (hq x.2))

private lemma coeff_nonneg_pow {σ : Type*} [DecidableEq σ] {p : MvPolynomial σ ℝ}
    (hp : ∀ m, 0 ≤ p.coeff m) (n : ℕ) : ∀ m, 0 ≤ (p ^ n).coeff m := by
  induction n with
  | zero =>
      rw [pow_zero]
      exact coeff_nonneg_C (by norm_num : (0 : ℝ) ≤ 1)
  | succ n ih =>
      rw [pow_succ]
      exact coeff_nonneg_mul ih hp

theorem face_count_poly (p₀ : MvPolynomial (Fin 3) ℝ) (L N : ℕ) :
    ∃ p : MvPolynomial (Fin 3) ℝ, (∀ m ∈ p.support, 0 ≤ p.coeff m) ∧
      ∀ (D r : ℕ) (s : ℝ), 0 ≤ s →
        (N : ℝ) * MvPolynomial.eval ![((D + L : ℕ) : ℝ), (r : ℝ), s] p₀ ≤
          MvPolynomial.eval ![(D : ℝ), (r : ℝ), s] p := by
  obtain ⟨C, K, hC, hbound⟩ := Work.WilG5.PolyEval.poly_abs_bound p₀
  refine ⟨MvPolynomial.C ((N : ℝ) * C) *
      (MvPolynomial.X (0 : Fin 3) + MvPolynomial.C 1) ^ K *
      (MvPolynomial.C (1 + (L : ℝ)) + MvPolynomial.X (1 : Fin 3) +
        MvPolynomial.X (2 : Fin 3)) ^ K, ?_, ?_⟩
  · intro m _
    exact coeff_nonneg_mul
      (coeff_nonneg_mul (coeff_nonneg_C (mul_nonneg (Nat.cast_nonneg N) hC))
        (coeff_nonneg_pow (coeff_nonneg_add (coeff_nonneg_X 0)
          (coeff_nonneg_C (by norm_num))) K))
      (coeff_nonneg_pow (coeff_nonneg_add
        (coeff_nonneg_add (coeff_nonneg_C (by positivity)) (coeff_nonneg_X 1))
        (coeff_nonneg_X 2)) K) m
  · intro D r s hs
    have hsum : (∑ i : Fin 3, |(![((D + L : ℕ) : ℝ), (r : ℝ), s] : Fin 3 → ℝ) i|)
        = ((D + L : ℕ) : ℝ) + (r : ℝ) + s := by
      rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons]
      rw [abs_of_nonneg (Nat.cast_nonneg (D + L)), abs_of_nonneg (Nat.cast_nonneg r),
        abs_of_nonneg hs]
    have hb := hbound (![((D + L : ℕ) : ℝ), (r : ℝ), s] : Fin 3 → ℝ)
    rw [hsum] at hb
    have hD : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
    have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have hcast : ((D + L : ℕ) : ℝ) = (D : ℝ) + (L : ℝ) := by push_cast; ring
    have h1 : (1 : ℝ) + (((D + L : ℕ) : ℝ) + (r : ℝ) + s) ≤
        ((D : ℝ) + 1) * (1 + (L : ℝ) + (r : ℝ) + s) := by
      rw [hcast]
      nlinarith [mul_nonneg hD hL, mul_nonneg hD hr, mul_nonneg hD hs]
    have h2 : (1 + (((D + L : ℕ) : ℝ) + (r : ℝ) + s)) ^ K ≤
        (((D : ℝ) + 1) * (1 + (L : ℝ) + (r : ℝ) + s)) ^ K :=
      pow_le_pow_left₀ (by positivity) h1 K
    have heval : MvPolynomial.eval ![(D : ℝ), (r : ℝ), s]
        (MvPolynomial.C ((N : ℝ) * C) *
          (MvPolynomial.X (0 : Fin 3) + MvPolynomial.C 1) ^ K *
          (MvPolynomial.C (1 + (L : ℝ)) + MvPolynomial.X (1 : Fin 3) +
            MvPolynomial.X (2 : Fin 3)) ^ K)
        = (N : ℝ) * (C * (((D : ℝ) + 1) * (1 + (L : ℝ) + (r : ℝ) + s)) ^ K) := by
      simp only [MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_add,
        MvPolynomial.eval_X, MvPolynomial.eval_C, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [mul_pow]
      ring
    calc (N : ℝ) * MvPolynomial.eval ![((D + L : ℕ) : ℝ), (r : ℝ), s] p₀
        ≤ (N : ℝ) * |MvPolynomial.eval ![((D + L : ℕ) : ℝ), (r : ℝ), s] p₀| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (Nat.cast_nonneg N)
      _ ≤ (N : ℝ) * (C * (((D : ℝ) + 1) * (1 + (L : ℝ) + (r : ℝ) + s)) ^ K) :=
          mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left h2 hC))
            (Nat.cast_nonneg N)
      _ = MvPolynomial.eval ![(D : ℝ), (r : ℝ), s]
            (MvPolynomial.C ((N : ℝ) * C) *
              (MvPolynomial.X (0 : Fin 3) + MvPolynomial.C 1) ^ K *
              (MvPolynomial.C (1 + (L : ℝ)) + MvPolynomial.X (1 : Fin 3) +
                MvPolynomial.X (2 : Fin 3)) ^ K) := heval.symm

end Work.WilG5.Face
