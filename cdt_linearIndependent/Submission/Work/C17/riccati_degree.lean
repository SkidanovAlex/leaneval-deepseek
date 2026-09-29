import Mathlib

/-!
# `Work.C17.riccati_degree`

Degree/leading-coefficient analysis of the Riccati equation

`P₂·(u′ + u²) + P₁·u + P₀ = 0`,  `u = A/B` (so that `A′B − AB′ + A²` appears),

with `P₂, P₁, P₀` of degrees `7, 6, 5` and leading coefficients `1, 3, 1` and `B` monic.
Writing `a = deg A`, `b = deg B`, `α = lc A`, the equation reads
`P₂(A′B − AB′) + P₂A² + P₁AB + P₀B² = 0`.  Its terms have degrees `a+b+6`, `2a+7`, `a+b+6`,
`2b+5`; the maximal one must have vanishing leading coefficient, which forces `b = a+1` and
`(α+1)² = 0`, i.e. `deg A = deg B − 1` and `lc A = −1`.

This is the algebraic input of the paper's remark that the Riccati equation of the order-two
operator `M` has no *rational* solution: a solution `A/B` in lowest terms would have
`deg A = deg B − 1` and `lc A = −1`.
-/

namespace Work.C17

open Polynomial

/-- The top coefficient of a product: if `p` vanishes above degree `m` and `q` vanishes above
degree `n`, then the coefficient of `X^(m+n)` in `p*q` is `(coeff m p) * (coeff n q)`. -/
theorem coeff_mul_add_of_vanishing {K : Type*} [Semiring K] (p q : Polynomial K) (m n : ℕ)
    (hp : ∀ i, m < i → p.coeff i = 0) (hq : ∀ j, n < j → q.coeff j = 0) :
    (p * q).coeff (m + n) = p.coeff m * q.coeff n := by
  rw [coeff_mul]
  apply Finset.sum_eq_single_of_mem (m, n)
  · rw [Finset.HasAntidiagonal.mem_antidiagonal]
  · rintro x hx hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rcases Nat.lt_trichotomy x.1 m with h | h | h
    · have hxj : n < x.2 := by omega
      rw [hq x.2 hxj, mul_zero]
    · exact absurd (Prod.ext h (by omega)) hne
    · rw [hp x.1 h, zero_mul]

/-- A product of polynomials vanishes in degree `N` as soon as each coefficient pair contributing
to degree `N` has a vanishing factor. -/
theorem coeff_mul_eq_zero_of_vanishing {K : Type*} [Semiring K] (p q : Polynomial K) (N : ℕ)
    (h : ∀ i j, i + j = N → p.coeff i * q.coeff j = 0) : (p * q).coeff N = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro x hx
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  exact h x.1 x.2 hx

/-- `(p′)₍deg p − 1₎ = deg p · lc p`: the coefficient of `X^(deg p − 1)` in the derivative of `p`
(valid also in degree `0`, where both sides vanish). -/
theorem derivative_coeff_natDegree_pred {K : Type*} [CommSemiring K] (p : Polynomial K) :
    p.derivative.coeff (p.natDegree - 1) = (p.natDegree : K) * p.leadingCoeff := by
  rw [coeff_derivative]
  rcases Nat.eq_zero_or_pos p.natDegree with h | h
  · have : p.coeff 1 = 0 := coeff_eq_zero_of_natDegree_lt (by rw [h]; norm_num)
    rw [h, Nat.zero_sub, this, zero_mul, Nat.cast_zero, zero_mul]
  · have hcast : ((p.natDegree - 1 : ℕ) : K) + 1 = (p.natDegree : K) := by
      have h1 : ((p.natDegree - 1 : ℕ) : K) + ((1:ℕ):K) = (p.natDegree : K) := by
        rw [← Nat.cast_add, Nat.sub_add_cancel h]
      simpa using h1
    rw [Nat.sub_add_cancel h, coeff_natDegree, hcast]
    ring

/-- The top coefficient of the "Wronskian" `A′B − AB′` for `B` monic of positive degree:
`(A′B − AB′)₍a+b−1₎ = lc A · (a − b)` where `a = deg A`, `b = deg B`. -/
theorem wronskian_coeff_top {K : Type*} [Field K] (A B : Polynomial K) (hB : B.Monic)
    (hb : 1 ≤ B.natDegree) :
    (A.derivative * B - A * B.derivative).coeff (A.natDegree + B.natDegree - 1)
      = A.leadingCoeff * ((A.natDegree : K) - (B.natDegree : K)) := by
  have hBlc : B.leadingCoeff = 1 := hB
  have hBc : ∀ j, B.natDegree < j → B.coeff j = 0 := fun j hj => coeff_eq_zero_of_natDegree_lt hj
  have hAc : ∀ i, A.natDegree < i → A.coeff i = 0 := fun i hi => coeff_eq_zero_of_natDegree_lt hi
  have hA'd : ∀ i, A.natDegree ≤ i → A.derivative.coeff i = 0 := by
    intro i hi
    rw [coeff_derivative]
    have : A.coeff (i+1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [this, zero_mul]
  have hB'd : ∀ j, B.natDegree ≤ j → B.derivative.coeff j = 0 := by
    intro j hj
    rw [coeff_derivative]
    have : B.coeff (j+1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [this, zero_mul]
  rcases Nat.eq_zero_or_pos A.natDegree with ha | ha
  · rw [ha]
    have hA0 : A.derivative = 0 := by
      ext n
      rw [coeff_derivative, coeff_zero]
      have : A.coeff (n+1) = 0 := coeff_eq_zero_of_natDegree_lt (by rw [ha]; omega)
      rw [this, zero_mul]
    have hAc0 : ∀ i, 0 < i → A.coeff i = 0 := by
      intro i hi; exact coeff_eq_zero_of_natDegree_lt (by rw [ha]; omega)
    have hc0 : A.coeff 0 = A.leadingCoeff := by rw [← ha, coeff_natDegree]
    rw [hA0, zero_mul, zero_sub]
    rw [show (0 + B.natDegree - 1) = 0 + (B.natDegree - 1) by omega]
    rw [coeff_neg, coeff_mul_add_of_vanishing A B.derivative 0 (B.natDegree - 1) hAc0
      (fun j hj => hB'd j (by omega)), hc0, derivative_coeff_natDegree_pred B, hBlc, mul_one]
    ring
  · rw [coeff_sub]
    have h1 : (A.derivative * B).coeff (A.natDegree + B.natDegree - 1)
        = (A.natDegree : K) * A.leadingCoeff := by
      rw [show A.natDegree + B.natDegree - 1 = (A.natDegree - 1) + B.natDegree by omega]
      rw [coeff_mul_add_of_vanishing A.derivative B (A.natDegree - 1) B.natDegree
        (fun i hi => hA'd i (by omega)) hBc]
      rw [derivative_coeff_natDegree_pred A, coeff_natDegree, hBlc, mul_one]
    have h2 : (A * B.derivative).coeff (A.natDegree + B.natDegree - 1)
        = A.leadingCoeff * (B.natDegree : K) := by
      rw [show A.natDegree + B.natDegree - 1 = A.natDegree + (B.natDegree - 1) by omega]
      rw [coeff_mul_add_of_vanishing A B.derivative A.natDegree (B.natDegree - 1) hAc
        (fun j hj => hB'd j (by omega))]
      rw [derivative_coeff_natDegree_pred B, hBlc, mul_one, coeff_natDegree]
    rw [h1, h2]
    ring

theorem riccati_degree {K : Type*} [Field K] (P2 P1 P0 A B : Polynomial K)
    (hB : B.Monic) (hA : A ≠ 0)
    (hP2d : P2.natDegree = 7) (hP2l : P2.leadingCoeff = 1)
    (hP1d : P1.natDegree = 6) (hP1l : P1.leadingCoeff = 3)
    (hP0d : P0.natDegree = 5) (hP0l : P0.leadingCoeff = 1)
    (h : P2 * (A.derivative * B - A * B.derivative) + P2 * A ^ 2 + P1 * A * B + P0 * B ^ 2 = 0) :
    A.natDegree = B.natDegree - 1 ∧ A.leadingCoeff = -1 := by
  have hBne : B ≠ 0 := hB.ne_zero
  have hBlc : B.leadingCoeff = 1 := hB
  have hAle : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA
  have hP2ne : P2 ≠ 0 := by
    intro h0; rw [h0, natDegree_zero] at hP2d; exact absurd hP2d (by norm_num)
  have hP1ne : P1 ≠ 0 := by
    intro h0; rw [h0, natDegree_zero] at hP1d; exact absurd hP1d (by norm_num)
  have hP0ne : P0 ≠ 0 := by
    intro h0; rw [h0, natDegree_zero] at hP0d; exact absurd hP0d (by norm_num)
  have hP2c : ∀ i, 7 < i → P2.coeff i = 0 := fun i hi => by
    apply coeff_eq_zero_of_natDegree_lt; rw [hP2d]; exact hi
  have hP2c7 : P2.coeff 7 = 1 := by rw [← hP2d, coeff_natDegree, hP2l]
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
  -- the Wronskian term vanishes in high degree
  have hE : ∀ N, A.natDegree + B.natDegree ≤ N →
      (A.derivative * B - A * B.derivative).coeff N = 0 := by
    intro N hN
    rw [coeff_sub]
    have h1 : (A.derivative * B).coeff N = 0 := by
      apply coeff_mul_eq_zero_of_vanishing
      intro i j hij
      by_cases hi : A.natDegree ≤ i
      · rw [hA'd i hi, zero_mul]
      · have : B.natDegree < j := by omega
        rw [hBc j this, mul_zero]
    have h2 : (A * B.derivative).coeff N = 0 := by
      apply coeff_mul_eq_zero_of_vanishing
      intro i j hij
      by_cases hi : A.natDegree < i
      · rw [hAc i hi, zero_mul]
      · have : B.natDegree ≤ j := by omega
        rw [hB'd j this, mul_zero]
    rw [h1, h2, sub_zero]
  -- degree bounds for the three `P`-terms
  have hP1AB_le : (P1 * A * B).natDegree ≤ 6 + A.natDegree + B.natDegree := by
    calc (P1 * A * B).natDegree ≤ (P1 * A).natDegree + B.natDegree := natDegree_mul_le
      _ ≤ (P1.natDegree + A.natDegree) + B.natDegree := Nat.add_le_add_right natDegree_mul_le _
      _ = 6 + A.natDegree + B.natDegree := by rw [hP1d]
  have hP0B_le : (P0 * B^2).natDegree ≤ 5 + 2 * B.natDegree := by
    calc (P0 * B^2).natDegree ≤ P0.natDegree + (B^2).natDegree := natDegree_mul_le
      _ ≤ 5 + 2 * B.natDegree := by
            rw [hP0d]
            exact Nat.add_le_add_left natDegree_pow_le 5
  have hP2A2_le : (P2 * A^2).natDegree ≤ 7 + 2 * A.natDegree := by
    calc (P2 * A^2).natDegree ≤ P2.natDegree + (A^2).natDegree := natDegree_mul_le
      _ ≤ 7 + 2 * A.natDegree := by
            rw [hP2d]
            exact Nat.add_le_add_left natDegree_pow_le 7
  -- the top coefficient of `P2 * A^2`
  have hEA2 : (P2 * A^2).coeff (2 * A.natDegree + 7) = A.leadingCoeff ^ 2 := by
    have hA2ne : A^2 ≠ 0 := pow_ne_zero 2 hA
    have hnd : (P2 * A^2).natDegree = 7 + 2 * A.natDegree := by
      rw [natDegree_mul hP2ne hA2ne, hP2d, natDegree_pow' (p := A) (n := 2) (pow_ne_zero 2 hAle)]
    have hlc : (P2 * A^2).leadingCoeff = A.leadingCoeff ^ 2 := by
      rw [leadingCoeff_mul, hP2l, one_mul,
        leadingCoeff_pow' (p := A) (n := 2) (pow_ne_zero 2 hAle)]
    rw [show 2 * A.natDegree + 7 = 7 + 2 * A.natDegree by ring]
    rw [← hnd, coeff_natDegree, hlc]
  -- STEP 1: degree of `B` is at most `deg A + 1`
  have hstep1 : B.natDegree ≤ A.natDegree + 1 := by
    by_contra hcon
    rw [not_le] at hcon
    have hcoeff := congrArg (fun p : Polynomial K => p.coeff (2 * B.natDegree + 5)) h
    rw [coeff_zero, coeff_add, coeff_add, coeff_add] at hcoeff
    have h1 : (P2 * (A.derivative * B - A * B.derivative)).coeff (2 * B.natDegree + 5) = 0 := by
      apply coeff_mul_eq_zero_of_vanishing
      intro i j hij
      by_cases hi : 7 < i
      · rw [hP2c i hi, zero_mul]
      · have : A.natDegree + B.natDegree ≤ j := by omega
        rw [hE j this, mul_zero]
    have h2 : (P2 * A^2).coeff (2 * B.natDegree + 5) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt; omega
    have h3 : (P1 * A * B).coeff (2 * B.natDegree + 5) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt; omega
    have h4 : (P0 * B^2).coeff (2 * B.natDegree + 5) = 1 := by
      have hB2ne : B^2 ≠ 0 := pow_ne_zero 2 hBne
      have hnd : (P0 * B^2).natDegree = 5 + 2 * B.natDegree := by
        rw [natDegree_mul hP0ne hB2ne, hP0d,
          natDegree_pow' (p := B) (n := 2) (by rw [hBlc]; norm_num)]
      have hlc : (P0 * B^2).leadingCoeff = 1 := by
        rw [leadingCoeff_mul, hP0l, one_mul,
          leadingCoeff_pow' (p := B) (n := 2) (by rw [hBlc]; norm_num)]
        rw [hBlc, one_pow]
      rw [show 2 * B.natDegree + 5 = 5 + 2 * B.natDegree by ring]
      rw [← hnd, coeff_natDegree, hlc]
    rw [h1, h2, h3, h4] at hcoeff
    simp only [add_zero, zero_add] at hcoeff
    exact one_ne_zero hcoeff
  -- STEP 2: degree of `B` is at least `deg A + 1`
  have hstep2 : A.natDegree + 1 ≤ B.natDegree := by
    by_contra hcon
    rw [not_le] at hcon
    have hcoeff := congrArg (fun p : Polynomial K => p.coeff (2 * A.natDegree + 7)) h
    rw [coeff_zero, coeff_add, coeff_add, coeff_add] at hcoeff
    have h1 : (P2 * (A.derivative * B - A * B.derivative)).coeff (2 * A.natDegree + 7) = 0 := by
      apply coeff_mul_eq_zero_of_vanishing
      intro i j hij
      by_cases hi : 7 < i
      · rw [hP2c i hi, zero_mul]
      · have : A.natDegree + B.natDegree ≤ j := by omega
        rw [hE j this, mul_zero]
    have h2 : (P1 * A * B).coeff (2 * A.natDegree + 7) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt; omega
    have h3 : (P0 * B^2).coeff (2 * A.natDegree + 7) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt; omega
    rw [h1, hEA2, h2, h3] at hcoeff
    have hsq : A.leadingCoeff ^ 2 = 0 := by linear_combination hcoeff
    exact hA (leadingCoeff_eq_zero.mp (sq_eq_zero_iff.mp hsq))
  have hb_eq : B.natDegree = A.natDegree + 1 := le_antisymm hstep1 hstep2
  -- STEP 3: the top coefficients at degree `2a + 7`
  have hP2E3 : (P2 * (A.derivative * B - A * B.derivative)).coeff (2 * A.natDegree + 7)
      = - A.leadingCoeff := by
    rw [show 2 * A.natDegree + 7 = 7 + 2 * A.natDegree by ring]
    rw [coeff_mul_add_of_vanishing P2 (A.derivative * B - A * B.derivative) 7 (2 * A.natDegree)
      hP2c (fun j hj => hE j (by omega))]
    rw [hP2c7, one_mul]
    rw [show 2 * A.natDegree = A.natDegree + B.natDegree - 1 by omega,
      wronskian_coeff_top A B hB (by omega)]
    rw [hb_eq]
    push_cast
    ring
  have hP1AB3 : (P1 * A * B).coeff (2 * A.natDegree + 7) = 3 * A.leadingCoeff := by
    have hp1ane : P1 * A ≠ 0 := mul_ne_zero hP1ne hA
    have hnd : (P1 * A * B).natDegree = 6 + A.natDegree + B.natDegree := by
      rw [natDegree_mul hp1ane hBne, natDegree_mul hP1ne hA, hP1d]
    have hlc : (P1 * A * B).leadingCoeff = 3 * A.leadingCoeff := by
      rw [leadingCoeff_mul, leadingCoeff_mul, hP1l, hBlc]
      ring
    rw [show 2 * A.natDegree + 7 = 6 + A.natDegree + B.natDegree by omega]
    rw [← hnd, coeff_natDegree, hlc]
  have hP0B3 : (P0 * B^2).coeff (2 * A.natDegree + 7) = 1 := by
    have hB2ne : B^2 ≠ 0 := pow_ne_zero 2 hBne
    have hnd : (P0 * B^2).natDegree = 5 + 2 * B.natDegree := by
      rw [natDegree_mul hP0ne hB2ne, hP0d,
        natDegree_pow' (p := B) (n := 2) (by rw [hBlc]; norm_num)]
    have hlc : (P0 * B^2).leadingCoeff = 1 := by
      rw [leadingCoeff_mul, hP0l, one_mul,
        leadingCoeff_pow' (p := B) (n := 2) (by rw [hBlc]; norm_num)]
      rw [hBlc, one_pow]
    rw [show 2 * A.natDegree + 7 = 5 + 2 * B.natDegree by omega]
    rw [← hnd, coeff_natDegree, hlc]
  have hcoeff := congrArg (fun p : Polynomial K => p.coeff (2 * A.natDegree + 7)) h
  rw [coeff_zero, coeff_add, coeff_add, coeff_add, hP2E3, hEA2, hP1AB3, hP0B3] at hcoeff
  have hsq : (A.leadingCoeff + 1) ^ 2 = 0 := by linear_combination hcoeff
  have hα : A.leadingCoeff = -1 := by
    have hh := sq_eq_zero_iff.mp hsq
    linear_combination hh
  exact ⟨by omega, hα⟩

end Work.C17
