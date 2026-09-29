import Submission.CDT.FrobeniusBeta

/-!
# The bound at a non-singular point of the eliminated operator

At a point `α` which is not a root of `Δ₁ = y(y−4)(72y+1)·cub`, all four
coefficients `A_j = 2P_jΔ₁^j`, `A_4 = −Δ₁⁴` are regular at `α`, i.e. have
order `≥ 0`; the unique minimiser of `c j + (N − j)` is then `j = 4`, so
`frobenius_unique` gives `ord_α(∑_j A_j b3^{(j)}) = ord_α(b3) − 4`.  Since the
right-hand side `Δ₁⁴R` has order `ord_α(R) ≥ 0` at such a point, `b3` can have
no pole at `α`: `ord_α b3 ≥ 0`.
-/

open Classical

noncomputable section

namespace Submission.CDT

open Polynomial

namespace FrobeniusApply

open Submission.CDT.Elim14C
open Submission.CDT.ElimOpC

lemma P0_ne_zero : P0 ≠ 0 := by
  intro h
  have h1 : P0.eval (1 : ℂ) = 0 := by rw [h]; simp
  unfold P0 y at h1
  norm_num at h1

lemma P1_ne_zero : P1 ≠ 0 := by
  intro h
  have h1 : P1.eval (1 : ℂ) = 0 := by rw [h]; simp
  unfold P1 y at h1
  norm_num at h1

lemma P2_ne_zero : P2 ≠ 0 := by
  intro h
  have h1 : P2.eval (1 : ℂ) = 0 := by rw [h]; simp
  unfold P2 y at h1
  norm_num at h1

lemma P3_ne_zero : P3 ≠ 0 := by
  intro h
  have h1 : P3.eval (1 : ℂ) = 0 := by rw [h]; simp
  unfold P3 y at h1
  norm_num at h1

lemma Afun_ne_zero (j : ℕ) (hj : j ∈ Finset.range 5) : Afun j ≠ 0 := by
  simp only [Finset.mem_range] at hj
  interval_cases j
  · rw [Afun_eq_zero]; exact mul_ne_zero two_ne_zero P0_ne_zero
  · rw [Afun_eq_one]
    exact mul_ne_zero (mul_ne_zero two_ne_zero P1_ne_zero) D1_ne_zero
  · rw [Afun_eq_two]
    exact mul_ne_zero (mul_ne_zero two_ne_zero P2_ne_zero) (pow_ne_zero 2 D1_ne_zero)
  · rw [Afun_eq_three]
    exact mul_ne_zero (mul_ne_zero two_ne_zero P3_ne_zero) (pow_ne_zero 3 D1_ne_zero)
  · rw [Afun_eq_four]
    exact neg_ne_zero.mpr (pow_ne_zero 4 D1_ne_zero)

lemma rootMultiplicity_Afun_four (α : ℂ) (hD1 : D1.eval α ≠ 0) :
    (Polynomial.rootMultiplicity α (Afun 4) : ℤ) = 0 := by
  rw [Afun_eq_four]
  have hassoc : Associated (-(D1 ^ 4)) (D1 ^ 4 : Polynomial ℂ) :=
    ⟨(-1 : (Polynomial ℂ)ˣ), by simp⟩
  rw [rootMultiplicity_eq_of_associated hassoc α, rootMultiplicity_pow' D1 4]
  have hD1r : Polynomial.rootMultiplicity α D1 = 0 := by
    rw [Polynomial.rootMultiplicity_eq_zero]
    intro hroot
    rw [Polynomial.IsRoot] at hroot
    exact hD1 hroot
  rw [hD1r, mul_zero, Nat.cast_zero]

/-- **The bound at a non-singular point** `α` (`Δ₁(α) ≠ 0`): `ord_α b3 ≥ 0`. -/
theorem generic_local (α : ℂ) (hD1 : D1.eval α ≠ 0) (b0 b1 b2 b3 R : RF) (hb : b3 ≠ 0)
    (hR : R ≠ 0) (hRlow : (0 : ℤ) ≤ ordAt α R)
    (h1 : dRat b3 + b2 - Ww * b3 = 0) (h2 : dRat b2 + b1 - Vv * b3 = 0)
    (h3 : dRat b1 + b0 - Uu * b3 = 0) (h4 : dRat b0 - Zz * b3 = R) :
    (0 : ℤ) ≤ ordAt α b3 := by
  by_contra hcon
  push_neg at hcon
  set N : ℤ := ordAt α b3 with hN
  have hNneg : N < 0 := by rw [hN]; exact hcon
  have hnum : b3.num ≠ 0 := RatFunc.num_ne_zero hb
  have hden : b3.denom ≠ 0 := RatFunc.denom_ne_zero b3
  have hrepr : b3 = am b3.num / am b3.denom := (RatFunc.num_div_denom b3).symm
  have hNord : N = (Polynomial.rootMultiplicity α b3.num : ℤ)
      - (Polynomial.rootMultiplicity α b3.denom : ℤ) := by
    rw [hN]
    conv_lhs => rw [hrepr]
    rw [ordAt_div α (RatFunc.algebraMap_ne_zero hnum) (RatFunc.algebraMap_ne_zero hden),
      ordAt_algebraMap, ordAt_algebraMap]
  have hres : ∀ j ∈ Finset.range 5, ((N + 1 : ℤ) : WithTop ℤ)
      ≤ ordAtT α (resFun α b3 N j) := by
    intro j hj
    rw [hrepr, hNord]
    exact residual_bound hnum hden j
  have hEq : (∑ j ∈ Finset.range 5, am (Afun j) * (dRat^[j] b3)) = am (D1 ^ 4) * R := by
    rw [sum5_expand]
    exact elim_equation_cleared b0 b1 b2 b3 R h1 h2 h3 h4
  have hA : ∀ j ∈ Finset.range 5,
      ordAtT α (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Afun j))
        = ((Polynomial.rootMultiplicity α (Afun j) : ℤ) : WithTop ℤ) := by
    intro j hj
    exact ordAtT_algebraMap (Afun_ne_zero j hj)
  have hmin : ∀ j ∈ Finset.range 5, j ≠ 4 →
      (Polynomial.rootMultiplicity α (Afun 4) : ℤ) + (N - (4 : ℕ))
        < (Polynomial.rootMultiplicity α (Afun j) : ℤ) + (N - (j : ℕ)) := by
    intro j hj hj4
    simp only [Finset.mem_range] at hj
    have h4 := rootMultiplicity_Afun_four α hD1
    have hj0 : (0 : ℤ) ≤ (Polynomial.rootMultiplicity α (Afun j) : ℤ) := Int.natCast_nonneg _
    have hjl : (j : ℤ) ≤ 3 := by omega
    rw [h4]
    omega
  have h := frobenius_unique hb hN.symm hNneg (Finset.range 5) Afun (fun j => j)
    (fun j => (Polynomial.rootMultiplicity α (Afun j) : ℤ)) hA hres (by simp) hmin
  rw [hEq] at h
  have hval : ordAtT α (am (D1 ^ 4) * R)
      = (((4 * (Polynomial.rootMultiplicity α D1 : ℤ)) + ordAt α R : ℤ) : WithTop ℤ) := by
    rw [ordAtT_mul α (RatFunc.algebraMap_ne_zero D1_pow_ne_zero) hR,
      ordAtT_algebraMap D1_pow_ne_zero, rootMultiplicity_pow' D1 4, ordAtT_of_ne hR,
      ← WithTop.coe_add]
    congr 1
  rw [hval, WithTop.coe_eq_coe] at h
  have hD1r : Polynomial.rootMultiplicity α D1 = 0 := by
    rw [Polynomial.rootMultiplicity_eq_zero]
    intro hroot
    rw [Polynomial.IsRoot] at hroot
    exact hD1 hroot
  rw [hD1r] at h
  have h4 := rootMultiplicity_Afun_four α hD1
  simp only [Nat.cast_zero, mul_zero, zero_add] at h
  rw [h4] at h
  simp only [zero_add] at h
  omega

end FrobeniusApply

end Submission.CDT
