import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension.const_add_mulT_decomp
import Submission.Work.ORHughesFree.RankAPI.rk_mul_eq_of_maxRank
import Submission.Work.ORHughesFree.RankAPI.rk_reindex
import Submission.Work.ORHughesFree.SylvesterRank

set_option autoImplicit false

universe u

/-!
# The constant coefficient of a polynomial has rank at most the rank of the polynomial

Let `R` be a von Neumann regular ring with a `MulSemiringAction (Multiplicative ℤ) R`
(the twist `τ` of the skew Laurent polynomial ring `S = R[t^{±1};τ]`), and let `rk'` be a
Sylvester rank function on `S` for which every matrix `1 + B·diag(t)` with `B` a *polynomial*
matrix (all coefficients of negative degree vanish) has full rank:

`rk' (1 + B * diag t) = n` for `B : Mat_n(S)` with no negative coefficients.

Then for every *polynomial* `q ∈ S` with constant coefficient `q₀` (i.e. `∑_{k} q_k t^k` with
`q_k = 0` for `k < 0`),

`rk' (q₀) ≤ rk' (q)`.

This is the "one third" of the squeeze used in the uniqueness of the natural extension
(`Submission/Work/ORHughesFree/NaturalExtension/naturalExtension_unique.lean`, step 2): the
constant term of a polynomial is a rank-non-increasing factor of it.

The proof is the classical one. Choose a weak (von Neumann) inverse `x` of `a = q₀`, so that
`a x a = a`. Put

`B₀ = (single 1 x) * (q - single 1 a) * t⁻¹`  and  `d = (single 1 x) * (q - single 1 a)`,

so that `B₀ * t = d`. Then, using `a x a = a`,

`a · (single 1 x) · q = a + a · d = a · (1 + B₀ t)`.

Indeed `a (single 1 x) q = single 1 (a x) q = single 1 (a x) (single 1 a) + single 1 (a x)(q - a)`
`= single 1 a + a d`. The element `B₀` is again a polynomial: `q - single 1 a` has no negative
coefficients and no constant term, `(single 1 x)·(-)` preserves this, and multiplication by `t⁻¹`
shifts the degree down by one. Hence `rk' (1 + B₀ t) = 1` by hypothesis, and multiplying by a
square matrix of maximal rank does not change the rank
(`RankAPI.rk_mul_eq_of_maxRank`), so

`rk' (a) = rk' (a (1 + B₀ t)) = rk' (a (single 1 x) q) ≤ rk' (q)`.
-/

namespace Work.ORHughesFree.NaturalExtension

section Aux

variable {U : Type u}

/-- Coefficients of a product by a constant element of `U[t^{±1};τ]`. -/
theorem coeffElt_const_mul [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (c : U) (f : SkewL U) (k : ℤ) :
    coeffElt (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) c * f) k = c * coeffElt f k := by
  simp [coeffElt]

/-- Coefficients of a product by `t⁻¹`: the degree is shifted down by one (and the twist is
trivial because `(ofAdd (w+1)) • (1 : U) = 1`). -/
theorem coeffElt_mul_skewLaurentTinv_coeff [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (f : SkewL U) (w : ℤ) :
    coeffElt (f * skewLaurentTinv (R := U)) w = coeffElt f (w + 1) := by
  rw [coeffElt, coeffElt, skewLaurentTinv, SkewMonoidAlgebra.coeff_mul_single]
  simp

/-- `t⁻¹ * t = 1` in `U[t^{±1};τ]`. -/
theorem skewLaurentTinv_mul_skewLaurentT_eq_one [Ring U]
    [MulSemiringAction (Multiplicative ℤ) U] : skewLaurentTinv (R := U) * skewLaurentT = 1 := by
  rw [skewLaurentTinv, skewLaurentT, SkewMonoidAlgebra.single_mul_single]
  simp

/-- Coefficients of a constant element of `U[t^{±1};τ]`. -/
theorem coeffElt_single_const_eq [Ring U] (c : U) (k : ℤ) :
    coeffElt (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) c : SkewL U) k =
      if k = 0 then c else 0 := by
  rw [coeffElt, SkewMonoidAlgebra.coeff_single_apply]
  by_cases h : k = 0
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro h1
    exact h (ofAdd_eq_one.mp h1.symm)

/-- Coefficient extraction is additive. -/
theorem coeffElt_sub_eq [Ring U] (a b : SkewL U) (k : ℤ) :
    coeffElt (a - b) k = coeffElt a k - coeffElt b k := by
  simp [coeffElt, sub_eq_add_neg, SkewMonoidAlgebra.coeff_add]

/-- `oneByOne` is multiplicative. -/
theorem oneByOne_mul_eq [Ring U] (a b : U) :
    oneByOne a * oneByOne b = oneByOne (a * b) := by
  ext i j
  simp [oneByOne, Matrix.mul_apply]

/-- `oneByOne` is additive. -/
theorem oneByOne_add_eq [Ring U] (a b : U) :
    oneByOne a + oneByOne b = oneByOne (a + b) := by
  ext i j
  simp [oneByOne]

/-- The `1 × 1` identity matrix is `oneByOne 1`. -/
theorem one_matrix_one_eq [Ring U] :
    (1 : Matrix (Fin 1) (Fin 1) U) = oneByOne 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [oneByOne]

/-- `oneByOne a` multiplied by the diagonal matrix `diag t` (of size `1 × 1`) is
`oneByOne (a * t)`. -/
theorem oneByOne_mul_diagonal_eq [Ring U] (a t : U) :
    oneByOne a * Matrix.diagonal (fun _ : Fin 1 => t) = oneByOne (a * t) := by
  ext i j
  simp [oneByOne]

end Aux

theorem rank_ge_const_coeff {R : Type u} [Ring R] [VonNeumannRegularRing R] [MulSemiringAction (Multiplicative ℤ) R] (rk' : SylvesterRank (SkewL R)) (hb : ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) (SkewL R)), (∀ i j, ∀ k : ℤ, k < 0 → coeffElt (B i j) k = 0) → rk'.rk n n ((1 : Matrix (Fin n) (Fin n) (SkewL R)) + B * Matrix.diagonal (fun _ => skewLaurentT)) = (n : ℝ)) (q : SkewL R) (hq : ∀ k : ℤ, k < 0 → coeffElt q k = 0) : rk'.rk 1 1 (oneByOne (SkewMonoidAlgebra.single 1 (coeffElt q 0))) ≤ rk'.rk 1 1 (oneByOne q) := by
  classical
  -- the constant term `a = q₀` and its weak inverse `x`
  set a : R := coeffElt q 0 with ha
  set A : SkewL R := SkewMonoidAlgebra.single (1 : Multiplicative ℤ) a with hA
  obtain ⟨x, hx⟩ := VonNeumannRegularRing.exists_mul_inverse a
  -- the auxiliary polynomial `B₀ = (single 1 x)(q - A) t⁻¹` and `d = (single 1 x)(q - A)`
  set d : SkewL R := SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x * (q - A) with hd
  set B₀ : SkewL R := d * skewLaurentTinv (R := R) with hB₀
  -- `B₀` has no negative coefficients
  have hB₀poly : ∀ k : ℤ, k < 0 → coeffElt B₀ k = 0 := by
    intro k hk
    rw [hB₀, coeffElt_mul_skewLaurentTinv_coeff, hd, coeffElt_const_mul]
    have hqA : coeffElt (q - A) (k + 1) = 0 := by
      rw [coeffElt_sub_eq, hA, coeffElt_single_const_eq]
      rcases lt_trichotomy (k + 1) 0 with h | h | h
      · rw [hq (k + 1) h, if_neg (by omega), sub_zero]
      · rw [h, if_pos rfl]
        simp [ha]
      · omega
    rw [hqA, mul_zero]
  -- `A * single 1 x = single 1 (a * x)` and it absorbs `A` on the right
  have hAx : A * SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x =
      SkewMonoidAlgebra.single (1 : Multiplicative ℤ) (a * x) := by
    rw [hA, SkewMonoidAlgebra.single_mul_single]
    simp
  have hAxA : SkewMonoidAlgebra.single (1 : Multiplicative ℤ) (a * x) * A = A := by
    rw [hA, SkewMonoidAlgebra.single_mul_single]
    simp [hx]
  have hAd : A * d = SkewMonoidAlgebra.single (1 : Multiplicative ℤ) (a * x) * (q - A) := by
    rw [hd, ← mul_assoc, hAx]
  have hB₀t : B₀ * skewLaurentT = d := by
    rw [hB₀, mul_assoc, skewLaurentTinv_mul_skewLaurentT_eq_one, mul_one]
  -- the key identity `A (single 1 x) q = A (1 + B₀ t)`
  have hkey : A * SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x * q =
      A * (1 + B₀ * skewLaurentT) := by
    calc A * SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x * q
        = A * SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x * (A + (q - A)) := by
            rw [show A + (q - A) = q from by abel]
      _ = A * SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x * A
            + A * SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x * (q - A) := by rw [mul_add]
      _ = A + A * d := by rw [hAx, hAxA, hAd]
      _ = A + A * B₀ * skewLaurentT := by rw [mul_assoc, hB₀t]
      _ = A * (1 + B₀ * skewLaurentT) := by rw [mul_add, mul_one, mul_assoc]
  -- the matrix `1 + (oneByOne B₀) * diag t` is the `oneByOne` of `1 + B₀ t`
  have hWdiag : (1 : Matrix (Fin 1) (Fin 1) (SkewL R)) +
      oneByOne B₀ * Matrix.diagonal (fun _ => skewLaurentT) =
      oneByOne (1 + B₀ * skewLaurentT) := by
    rw [one_matrix_one_eq, oneByOne_mul_diagonal_eq, oneByOne_add_eq]
  -- it has rank one by hypothesis
  have hbfull : rk'.rk 1 1 (oneByOne (1 + B₀ * skewLaurentT)) = ((1 : ℕ) : ℝ) := by
    have h := hb 1 (oneByOne B₀) (by
      intro i j k hk
      fin_cases i
      fin_cases j
      exact hB₀poly k hk)
    rwa [hWdiag] at h
  -- multiplying by a matrix of maximal rank does not change the rank
  have hmax : rk'.rk 1 1 (oneByOne A * oneByOne (1 + B₀ * skewLaurentT)) =
      rk'.rk 1 1 (oneByOne A) :=
    Work.ORHughesFree.RankAPI.rk_mul_eq_of_maxRank rk' (oneByOne A)
      (oneByOne (1 + B₀ * skewLaurentT)) hbfull
  calc rk'.rk 1 1 (oneByOne A)
      = rk'.rk 1 1 (oneByOne A * oneByOne (1 + B₀ * skewLaurentT)) := hmax.symm
    _ = rk'.rk 1 1 (oneByOne (A * (1 + B₀ * skewLaurentT))) := by rw [oneByOne_mul_eq]
    _ = rk'.rk 1 1 (oneByOne (A * SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x * q)) := by
          rw [← hkey]
    _ = rk'.rk 1 1 (oneByOne (A * SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x) *
            oneByOne q) := by rw [oneByOne_mul_eq]
    _ ≤ rk'.rk 1 1 (oneByOne q) := rk'.rk_mul_le_right _ _

end Work.ORHughesFree.NaturalExtension
