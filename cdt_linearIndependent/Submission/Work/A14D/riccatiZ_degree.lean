import Mathlib
import Submission.Work.A14D.riccatiZ_helpers
import Submission.Work.C17.riccati_degree

/-!
# `Work.A14D.riccatiZ_degree`

Degree/leading-coefficient analysis of the Riccati equation of `L_Z`.  Writing `u = A/B`, the
equation `P₂·(u′ + u²) + P₁·u + P₀ = 0` (with `P₂ = Q2Z`, `P₁ = Q1Z`, `P₀ = Q0Z`) reads

  `Q2Z·(A′B − AB′) + Q2Z·A² + Q1Z·A·B + Q0Z·B² = 0`.

Here `Q2Z = X − 10X² + 9X³` (degree 3, leading coefficient 9), `Q1Z = 1 − 20X + 27X²`
(degree 2, leading coefficient 27) and `Q0Z = −3 + 9X` (degree 1, leading coefficient 9), with
`B` monic.  With `a = deg A`, `b = deg B`, `α = lc A`, the four terms have degrees `a+b+2`,
`2a+3`, `a+b+2`, `2b+1`; comparing the maximal degree forces `b = a+1` and `(α+1)² = 0`, i.e.
`deg A = deg B − 1` and `lc A = −1`.
-/

namespace Work.A14D

open Polynomial

theorem riccatiZ_degree (A B : Polynomial ℂ) (hB : B.Monic) (hA : A ≠ 0)
    (h : Work.A14D.Q2Z * (A.derivative * B - A * B.derivative) + Work.A14D.Q2Z * A ^ 2
          + Work.A14D.Q1Z * A * B + Work.A14D.Q0Z * B ^ 2 = 0) :
    A.natDegree = B.natDegree - 1 ∧ A.leadingCoeff = -1 := by
  have hBne : B ≠ 0 := hB.ne_zero
  have hBlc : B.leadingCoeff = 1 := hB
  have hAle : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA
  have hP2ne : Q2Z ≠ 0 := Q2Z_ne_zero
  have hP1ne : Q1Z ≠ 0 := Q1Z_ne_zero
  have hP0ne : Q0Z ≠ 0 := Q0Z_ne_zero
  have hP2d : Q2Z.natDegree = 3 := Q2Z_natDegree
  have hP1d : Q1Z.natDegree = 2 := Q1Z_natDegree
  have hP0d : Q0Z.natDegree = 1 := Q0Z_natDegree
  have hP2l : Q2Z.leadingCoeff = 9 := Q2Z_leadingCoeff
  have hP1l : Q1Z.leadingCoeff = 27 := Q1Z_leadingCoeff
  have hP0l : Q0Z.leadingCoeff = 9 := Q0Z_leadingCoeff
  have hP2c : ∀ i, 3 < i → Q2Z.coeff i = 0 := fun i hi => by
    apply coeff_eq_zero_of_natDegree_lt; rw [hP2d]; exact hi
  have hP2c3 : Q2Z.coeff 3 = 9 := by rw [← hP2d, coeff_natDegree, hP2l]
  have hAc : ∀ i, A.natDegree < i → A.coeff i = 0 := fun i => coeff_eq_zero_of_natDegree_lt
  have hBc : ∀ j, B.natDegree < j → B.coeff j = 0 := fun j => coeff_eq_zero_of_natDegree_lt
  have hA'd : ∀ i, A.natDegree ≤ i → A.derivative.coeff i = 0 := by
    intro i hi; rw [coeff_derivative]
    have : A.coeff (i+1) = 0 := hAc (i+1) (by omega)
    rw [this, zero_mul]
  have hB'd : ∀ j, B.natDegree ≤ j → B.derivative.coeff j = 0 := by
    intro j hj; rw [coeff_derivative]
    have : B.coeff (j+1) = 0 := hBc (j+1) (by omega)
    rw [this, zero_mul]
  have hE : ∀ N, A.natDegree + B.natDegree ≤ N →
      (A.derivative * B - A * B.derivative).coeff N = 0 := by
    intro N hN
    rw [coeff_sub]
    have h1 : (A.derivative * B).coeff N = 0 := by
      apply Work.C17.coeff_mul_eq_zero_of_vanishing
      intro i j hij
      by_cases hi : A.natDegree ≤ i
      · rw [hA'd i hi, zero_mul]
      · have : B.natDegree < j := by omega
        rw [hBc j this, mul_zero]
    have h2 : (A * B.derivative).coeff N = 0 := by
      apply Work.C17.coeff_mul_eq_zero_of_vanishing
      intro i j hij
      by_cases hi : A.natDegree < i
      · rw [hAc i hi, zero_mul]
      · have : B.natDegree ≤ j := by omega
        rw [hB'd j this, mul_zero]
    rw [h1, h2, sub_zero]
  have hP1AB_le : (Q1Z * A * B).natDegree ≤ 2 + A.natDegree + B.natDegree := by
    calc (Q1Z * A * B).natDegree ≤ (Q1Z * A).natDegree + B.natDegree := natDegree_mul_le
      _ ≤ (Q1Z.natDegree + A.natDegree) + B.natDegree := Nat.add_le_add_right natDegree_mul_le _
      _ = 2 + A.natDegree + B.natDegree := by rw [hP1d]
  have hP0B_le : (Q0Z * B^2).natDegree ≤ 1 + 2 * B.natDegree := by
    calc (Q0Z * B^2).natDegree ≤ Q0Z.natDegree + (B^2).natDegree := natDegree_mul_le
      _ ≤ 1 + 2 * B.natDegree := by
            rw [hP0d]; exact Nat.add_le_add_left natDegree_pow_le 1
  have hP2A2_le : (Q2Z * A^2).natDegree ≤ 3 + 2 * A.natDegree := by
    calc (Q2Z * A^2).natDegree ≤ Q2Z.natDegree + (A^2).natDegree := natDegree_mul_le
      _ ≤ 3 + 2 * A.natDegree := by
            rw [hP2d]; exact Nat.add_le_add_left natDegree_pow_le 3
  have hEA2 : (Q2Z * A^2).coeff (2 * A.natDegree + 3) = 9 * A.leadingCoeff ^ 2 := by
    have hA2ne : A^2 ≠ 0 := pow_ne_zero 2 hA
    have hnd : (Q2Z * A^2).natDegree = 3 + 2 * A.natDegree := by
      rw [natDegree_mul hP2ne hA2ne, hP2d,
        natDegree_pow' (p := A) (n := 2) (pow_ne_zero 2 hAle)]
    have hlc : (Q2Z * A^2).leadingCoeff = 9 * A.leadingCoeff ^ 2 := by
      rw [leadingCoeff_mul, hP2l, leadingCoeff_pow' (p := A) (n := 2) (pow_ne_zero 2 hAle)]
    rw [show 2 * A.natDegree + 3 = 3 + 2 * A.natDegree by ring]
    rw [← hnd, coeff_natDegree, hlc]
  -- STEP 1: `B.natDegree ≤ A.natDegree + 1`
  have hstep1 : B.natDegree ≤ A.natDegree + 1 := by
    by_contra hcon
    rw [not_le] at hcon
    have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff (2 * B.natDegree + 1)) h
    rw [coeff_zero, coeff_add, coeff_add, coeff_add] at hcoeff
    have h1 : (Q2Z * (A.derivative * B - A * B.derivative)).coeff (2 * B.natDegree + 1) = 0 := by
      apply Work.C17.coeff_mul_eq_zero_of_vanishing
      intro i j hij
      by_cases hi : 3 < i
      · rw [hP2c i hi, zero_mul]
      · have : A.natDegree + B.natDegree ≤ j := by omega
        rw [hE j this, mul_zero]
    have h2 : (Q2Z * A^2).coeff (2 * B.natDegree + 1) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt; omega
    have h3 : (Q1Z * A * B).coeff (2 * B.natDegree + 1) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt; omega
    have h4 : (Q0Z * B^2).coeff (2 * B.natDegree + 1) = 9 := by
      have hB2ne : B^2 ≠ 0 := pow_ne_zero 2 hBne
      have hnd : (Q0Z * B^2).natDegree = 1 + 2 * B.natDegree := by
        rw [natDegree_mul hP0ne hB2ne, hP0d,
          natDegree_pow' (p := B) (n := 2) (by rw [hBlc]; norm_num)]
      have hlc : (Q0Z * B^2).leadingCoeff = 9 := by
        rw [leadingCoeff_mul, hP0l,
          leadingCoeff_pow' (p := B) (n := 2) (by rw [hBlc]; norm_num)]
        rw [hBlc, one_pow, mul_one]
      rw [show 2 * B.natDegree + 1 = 1 + 2 * B.natDegree by ring]
      rw [← hnd, coeff_natDegree, hlc]
    rw [h1, h2, h3, h4] at hcoeff
    simp only [add_zero, zero_add] at hcoeff
    exact absurd hcoeff (by norm_num)
  -- STEP 2: `A.natDegree + 1 ≤ B.natDegree`
  have hstep2 : A.natDegree + 1 ≤ B.natDegree := by
    by_contra hcon
    rw [not_le] at hcon
    have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff (2 * A.natDegree + 3)) h
    rw [coeff_zero, coeff_add, coeff_add, coeff_add] at hcoeff
    have h1 : (Q2Z * (A.derivative * B - A * B.derivative)).coeff (2 * A.natDegree + 3) = 0 := by
      apply Work.C17.coeff_mul_eq_zero_of_vanishing
      intro i j hij
      by_cases hi : 3 < i
      · rw [hP2c i hi, zero_mul]
      · have : A.natDegree + B.natDegree ≤ j := by omega
        rw [hE j this, mul_zero]
    have h2 : (Q1Z * A * B).coeff (2 * A.natDegree + 3) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt; omega
    have h3 : (Q0Z * B^2).coeff (2 * A.natDegree + 3) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt; omega
    rw [h1, hEA2, h2, h3] at hcoeff
    simp only [add_zero, zero_add] at hcoeff
    have hsq : A.leadingCoeff ^ 2 = 0 := by
      rcases mul_eq_zero.mp hcoeff with h9 | h
      · norm_num at h9
      · exact h
    exact hA (leadingCoeff_eq_zero.mp (sq_eq_zero_iff.mp hsq))
  have hb_eq : B.natDegree = A.natDegree + 1 := le_antisymm hstep1 hstep2
  -- STEP 3: the top coefficients at degree `2a + 3`
  have hP2E3 : (Q2Z * (A.derivative * B - A * B.derivative)).coeff (2 * A.natDegree + 3)
      = -9 * A.leadingCoeff := by
    rw [show 2 * A.natDegree + 3 = 3 + 2 * A.natDegree by ring]
    rw [Work.C17.coeff_mul_add_of_vanishing Q2Z (A.derivative * B - A * B.derivative) 3
      (2 * A.natDegree) hP2c (fun j hj => hE j (by omega))]
    rw [hP2c3]
    rw [show 2 * A.natDegree = A.natDegree + B.natDegree - 1 by omega,
      Work.C17.wronskian_coeff_top A B hB (by omega)]
    rw [hb_eq]
    push_cast
    ring
  have hP1AB3 : (Q1Z * A * B).coeff (2 * A.natDegree + 3) = 27 * A.leadingCoeff := by
    have hp1ane : Q1Z * A ≠ 0 := mul_ne_zero hP1ne hA
    have hnd : (Q1Z * A * B).natDegree = 2 + A.natDegree + B.natDegree := by
      rw [natDegree_mul hp1ane hBne, natDegree_mul hP1ne hA, hP1d]
    have hlc : (Q1Z * A * B).leadingCoeff = 27 * A.leadingCoeff := by
      rw [leadingCoeff_mul, leadingCoeff_mul, hP1l, hBlc]
      ring
    rw [show 2 * A.natDegree + 3 = 2 + A.natDegree + B.natDegree by omega]
    rw [← hnd, coeff_natDegree, hlc]
  have hP0B3 : (Q0Z * B^2).coeff (2 * A.natDegree + 3) = 9 := by
    have hB2ne : B^2 ≠ 0 := pow_ne_zero 2 hBne
    have hnd : (Q0Z * B^2).natDegree = 1 + 2 * B.natDegree := by
      rw [natDegree_mul hP0ne hB2ne, hP0d,
        natDegree_pow' (p := B) (n := 2) (by rw [hBlc]; norm_num)]
    have hlc : (Q0Z * B^2).leadingCoeff = 9 := by
      rw [leadingCoeff_mul, hP0l,
        leadingCoeff_pow' (p := B) (n := 2) (by rw [hBlc]; norm_num)]
      rw [hBlc, one_pow, mul_one]
    rw [show 2 * A.natDegree + 3 = 1 + 2 * B.natDegree by omega]
    rw [← hnd, coeff_natDegree, hlc]
  have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff (2 * A.natDegree + 3)) h
  rw [coeff_zero, coeff_add, coeff_add, coeff_add, hP2E3, hEA2, hP1AB3, hP0B3] at hcoeff
  have hsq : (A.leadingCoeff + 1) ^ 2 = 0 := by
    have h9 : 9 * (A.leadingCoeff + 1) ^ 2 = 0 := by linear_combination hcoeff
    exact (mul_eq_zero.mp h9).resolve_left (by norm_num)
  have hα : A.leadingCoeff = -1 := by
    have hh := sq_eq_zero_iff.mp hsq
    linear_combination hh
  exact ⟨by omega, hα⟩

end Work.A14D
