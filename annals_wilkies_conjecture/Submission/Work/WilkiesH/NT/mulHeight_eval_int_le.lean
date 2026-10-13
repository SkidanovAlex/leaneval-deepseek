import Mathlib
import Submission.Work.WilkiesH.Defs
import Submission.Work.WilkiesH.NT.HomogDefs
import Submission.Work.WilkiesH.NT.homog_isHomogeneous
import Submission.Work.WilkiesH.NT.homog_eval
import Submission.Work.WilkiesH.NT.mulHeightBound_homogFamily_le
import Submission.Work.WilkiesH.NT.mulHeight_le_prod_mulHeight1

set_option autoImplicit false

namespace Work.WilkiesH.NT

open MvPolynomial

/-- Height bound for the value of an integer polynomial of bounded degree and coefficients
at a point of a number field.  This is the "height of a polynomial expression" bound used in
the counting argument (BNZ, *Wilkie's conjecture for Pfaffian structures*, §6).

The proof homogenizes `P` to total degree `d` in `n + 1` variables (with the new variable set
to `1` at the point), applies Mathlib's height bound `Height.mulHeight_eval_le` for families of
homogeneous polynomials, bounds the resulting constant `Height.mulHeightBound` using the
coefficient bound `|P.coeff m| ≤ N`, and finally bounds the height of the augmented tuple
`(1, x)` by the product of the heights of the coordinates. -/
theorem mulHeight_eval_int_le {n d N : ℕ} (hN : 1 ≤ N) {K : Type*} [Field K] [NumberField K]
    (P : MvPolynomial (Fin n) ℤ) (hdeg : P.totalDegree ≤ d)
    (hcoef : ∀ m ∈ P.support, |(P.coeff m : ℤ)| ≤ (N : ℤ)) (x : Fin n → K) :
    Height.mulHeight₁ (K := K) (MvPolynomial.eval x (P.map (Int.castRingHom K)))
      ≤ ((Work.WilkiesH.monoCount n d : ℝ) * (N : ℝ)) ^ (Module.finrank ℚ K)
        * (∏ i, Height.mulHeight₁ (K := K) (x i)) ^ d := by
  classical
  set y : Fin (n + 1) → K := Fin.cons 1 x with hy
  -- the family `![homog P d, X 0 ^ d]` is homogeneous of degree `d`
  have hp : ∀ i, ((homogFamily (K := K) P d) i).IsHomogeneous d := by
    intro i
    fin_cases i
    · exact homog_isHomogeneous P hdeg
    · exact isHomogeneous_X_pow (R := K) (σ := Fin (n + 1)) 0 d
  have key := Height.mulHeight_eval_le (p := homogFamily (K := K) P d) hp y
  -- evaluating the family at `(1, x)` gives `(P(x), 1)`
  have hL : (fun j : Fin 2 => (homogFamily (K := K) P d j).eval y)
      = ![MvPolynomial.eval x (P.map (Int.castRingHom K)), 1] := by
    funext j
    fin_cases j
    · simpa [homogFamily, hy] using homog_eval P x
    · simp [homogFamily, hy]
  have hz : Height.mulHeight₁ (K := K) (MvPolynomial.eval x (P.map (Int.castRingHom K)))
      = Height.mulHeight (fun j : Fin 2 => (homogFamily (K := K) P d j).eval y) := by
    rw [hL, Height.mulHeight₁_eq_mulHeight]
  -- the constant is bounded by `(monoCount n d * N) ^ [K : ℚ]`
  have h3 := mulHeightBound_homogFamily_le (K := K) hN P hdeg hcoef
  -- the height of `(1, x)` is bounded by the product of the heights of the coordinates
  have h4 : Height.mulHeight y ≤ ∏ i, Height.mulHeight₁ (K := K) (x i) := by
    have h := mulHeight_le_prod_mulHeight1 (K := K) y
    rw [Fin.prod_univ_succ] at h
    simpa [hy] using h
  rw [hz]
  refine key.trans ?_
  refine (mul_le_mul_of_nonneg_right h3 (pow_nonneg (Height.mulHeight_pos y).le d)).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Height.mulHeight_pos y).le h4 d)
    (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _)

end Work.WilkiesH.NT
