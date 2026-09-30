import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

/-!
# The Frobenius difference `(∑ Xᵢᵏ)^p - ∑ Xᵢ^(kp)` is `p` times a symmetric polynomial

For a prime `p` and natural numbers `n`, `k`, the polynomial

  `(∑ i, X i ^ k) ^ p - ∑ i, X i ^ (k * p)`

has all of its integer coefficients divisible by `p`, and is symmetric.  Hence
it equals `p • Ψ` for a symmetric polynomial `Ψ` with integer coefficients.
This is the elementary "Freshman's dream" input used for the Frobenius–MvPolynomial
step in the Baker–Wüstholz argument.

The proof goes through reduction modulo `p`: the Frobenius endomorphism of
`MvPolynomial (Fin n) (ZMod p)` sends the first summand to the second, so the whole
difference maps to `0`, i.e. every coefficient is divisible by `p`.  Symmetry of the
quotient `Ψ` is deduced from symmetry of the difference by cancelling the (nonzero)
scalar `p`.
-/

namespace Work.BW

/-- If every coefficient of `H : MvPolynomial σ ℤ` is divisible by `p`, then `H` is
`p` times an explicit polynomial obtained by dividing each coefficient by `p`. -/
lemma exists_zsmul_eq_of_coeff_dvd {σ : Type*} [DecidableEq σ] (p : ℕ) (H : MvPolynomial σ ℤ)
    (h : ∀ m, (p : ℤ) ∣ H.coeff m) : ∃ Ψ : MvPolynomial σ ℤ, (p : ℤ) • Ψ = H := by
  refine ⟨∑ m ∈ H.support, MvPolynomial.monomial m (H.coeff m / (p : ℤ)), ?_⟩
  rw [MvPolynomial.smul_eq_C_mul]
  rw [Finset.mul_sum]
  trans ∑ m ∈ H.support, MvPolynomial.monomial m (H.coeff m)
  · refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [MvPolynomial.C_mul_monomial, Int.mul_ediv_cancel' (h m)]
  · exact MvPolynomial.support_sum_monomial_coeff H

/-- `map` commutes with the power sum `∑ i, X i ^ k`. -/
lemma map_X_pow_sum (n k p : ℕ) :
    MvPolynomial.map (Int.castRingHom (ZMod p))
        (∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ k)
      = ∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) (ZMod p)) ^ k := by
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_pow, MvPolynomial.map_X]

/-- Frobenius ("Freshman's dream") in characteristic `p`. -/
lemma frobenius_sum_pow_X (n k p : ℕ) (hp : p.Prime) :
    (∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) (ZMod p)) ^ k) ^ p
      = ∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) (ZMod p)) ^ (k * p) := by
  haveI : ExpChar (ZMod p) p := ExpChar.prime hp
  rw [sum_pow_char p Finset.univ
    (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) (ZMod p)) ^ k)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← pow_mul]

/-- Reduction of the Frobenius difference modulo `p` vanishes. -/
lemma map_intCast_zmod_frobenius (n k p : ℕ) (hp : p.Prime) :
    MvPolynomial.map (Int.castRingHom (ZMod p))
      ((∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ k) ^ p
        - ∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (k * p)) = 0 := by
  rw [map_sub, map_pow, map_X_pow_sum n k p, map_X_pow_sum n (k * p) p,
      frobenius_sum_pow_X n k p hp, sub_self]

/-- `rename` commutes with integer scalar multiplication. -/
lemma rename_int_smul {σ τ : Type*} (e : σ ≃ τ) (c : ℤ) (x : MvPolynomial σ ℤ) :
    MvPolynomial.rename e (c • x) = c • MvPolynomial.rename e x := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.rename_C]

/-- Multiplication by a nonzero integer is injective on `MvPolynomial σ ℤ`. -/
lemma zsmul_int_injective {σ : Type*} (p : ℕ) (hp : p ≠ 0) {x y : MvPolynomial σ ℤ}
    (h : (p : ℤ) • x = (p : ℤ) • y) : x = y := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul] at h
  exact mul_left_cancel₀ (MvPolynomial.C_ne_zero.mpr (Nat.cast_ne_zero.mpr hp)) h

theorem mvFrobenius_diff (n k p : ℕ) (hp : p.Prime) :
    ∃ Ψ : MvPolynomial (Fin n) ℤ, MvPolynomial.IsSymmetric Ψ ∧
      (p : ℤ) • Ψ = (∑ i, MvPolynomial.X i ^ k) ^ p - ∑ i, MvPolynomial.X i ^ (k * p) := by
  -- The Frobenius difference is symmetric.
  have hsymm : MvPolynomial.IsSymmetric
      ((∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ k) ^ p
        - ∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (k * p)) := by
    have hF : MvPolynomial.IsSymmetric
        (∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ k) := by
      have h := MvPolynomial.psum_isSymmetric (Fin n) ℤ k
      simpa only [MvPolynomial.psum] using h
    have hG : MvPolynomial.IsSymmetric
        (∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (k * p)) := by
      have h := MvPolynomial.psum_isSymmetric (Fin n) ℤ (k * p)
      simpa only [MvPolynomial.psum] using h
    refine MvPolynomial.IsSymmetric.sub ?_ hG
    intro e
    rw [map_pow, hF e]
  -- Every coefficient of the Frobenius difference is divisible by `p`.
  have hcoeff : ∀ m : Fin n →₀ ℕ,
      (p : ℤ) ∣ ((∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ k) ^ p
        - ∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (k * p)).coeff m := by
    intro m
    have h2 : (MvPolynomial.map (Int.castRingHom (ZMod p))
        ((∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ k) ^ p
          - ∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (k * p))).coeff m = 0 := by
      rw [map_intCast_zmod_frobenius n k p hp]
      simp
    rw [MvPolynomial.coeff_map] at h2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2
  obtain ⟨Ψ, hΨ⟩ := exists_zsmul_eq_of_coeff_dvd p _ hcoeff
  refine ⟨Ψ, ?_, hΨ⟩
  -- Symmetry of the quotient, by cancelling `p`.
  intro e
  have key : (p : ℤ) • MvPolynomial.rename e Ψ = (p : ℤ) • Ψ := by
    rw [← rename_int_smul e (p : ℤ) Ψ, hΨ]
    exact hsymm e
  exact zsmul_int_injective p hp.ne_zero key

end Work.BW
