import Mathlib
import Submission.Work.TMC16Core.Basic.sin_prod

namespace Work.TMC14Core.Adjunct

open Finset

/-- `exp (θ·i) + exp (-θ·i) = 2 cos θ` for real `θ` (in `ℂ`). -/
lemma exp_add_exp_neg_eq_two_cos (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) + Complex.exp (-((θ : ℂ) * Complex.I))
      = 2 * (Real.cos θ : ℂ) := by
  rw [show (-((θ : ℂ) * Complex.I)) = (-(θ : ℂ)) * Complex.I by ring,
    ← Complex.two_cos (θ : ℂ), Complex.ofReal_cos]

/-- If `u * v = 1`, `u + v = 0` and `ε * ε = 1` then `(1-εu)(1-εv) = 2`. -/
lemma pair_eq_two (u v ε : ℂ) (huv : u * v = 1) (hadd : u + v = 0) (hε : ε * ε = 1) :
    (1 - ε * u) * (1 - ε * v) = 2 := by
  have h : (1 - ε * u) * (1 - ε * v) = 1 - ε * (u + v) + (ε * ε) * (u * v) := by ring
  rw [h, hadd, mul_zero, sub_zero, hε, huv, mul_one]
  norm_num

theorem cos_prod_sq (N p : ℕ) (hN : 1 ≤ N) (hpq : Nat.Coprime p (2 * N)) :
    (Finset.prod (Finset.range N)
      (fun j => 2 * Real.cos (Real.pi * (4 * (j : ℝ) + 1) * (p : ℝ) / (4 * (N : ℝ)))))^2 = 2 := by
  have hNpos : 0 < N := by omega
  have hNne : N ≠ 0 := by omega
  obtain ⟨hp2, hpN⟩ := Nat.coprime_mul_iff_right.mp hpq
  have hpodd : Odd p := hp2.odd_of_right
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hNne
  set γ : ℝ := Real.pi * (p : ℝ) / (4 * (N : ℝ)) with hγ
  set ζ : ℂ := Complex.exp ((γ : ℂ) * Complex.I) with hζ
  have hζne : ζ ≠ 0 := by rw [hζ]; exact Complex.exp_ne_zero _
  set ω : ℂ := ζ ^ 8 with hωdef
  set A : ℂ := -ζ ^ 2 with hA
  set Q : ℝ := Finset.prod (Finset.range N)
      (fun j => 2 * Real.cos (Real.pi * (4 * (j : ℝ) + 1) * (p : ℝ) / (4 * (N : ℝ)))) with hQ
  -- ω = exp (2 π i p / N) is a primitive N-th root of unity
  have hωeq : ω = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((p : ℂ) / (N : ℂ))) := by
    have h8γ : ((8 : ℕ) : ℂ) * (γ : ℂ) = 2 * (Real.pi : ℂ) * (p : ℂ) / (N : ℂ) := by
      rw [hγ]; push_cast; ring_nf
    rw [hωdef, hζ, ← Complex.exp_nat_mul]
    congr 1
    rw [← mul_assoc, h8γ]; ring
  have hωprim : IsPrimitiveRoot ω N := by
    rw [hωeq]
    exact Complex.isPrimitiveRoot_exp_of_coprime p N hNne hpN
  -- ζ ^ (2N) = i ^ p, whence (ζ ^ (2N)) ^ 2 = -1
  have hζ2N : ζ ^ (2 * N) = Complex.I ^ p := by
    have harg : (↑(2 * N) : ℂ) * ((γ : ℂ) * Complex.I)
        = (↑p : ℂ) * ((Real.pi : ℂ) / 2 * Complex.I) := by
      rw [hγ]; push_cast; field_simp; ring
    have hIp : Complex.I ^ p = (Complex.exp ((Real.pi : ℂ) / 2 * Complex.I)) ^ p := by
      rw [Complex.exp_pi_div_two_mul_I]
    rw [hζ, ← Complex.exp_nat_mul, harg, hIp, ← Complex.exp_nat_mul]
  have hI2 : Complex.I ^ 2 = -1 := by rw [pow_two, Complex.I_mul_I]
  have hu2 : (ζ ^ (2 * N)) ^ 2 = -1 := by
    rw [hζ2N, ← pow_mul, show p * 2 = 2 * p by ring, pow_mul, hI2, hpodd.neg_one_pow]
  -- exp(θ_j i) = ζ^(4j+1), with θ_j the angle of the j-th cosine factor
  have hzpow : ∀ j : ℕ,
      Complex.exp (Complex.ofReal
          (Real.pi * (4 * (j : ℝ) + 1) * (p : ℝ) / (4 * (N : ℝ))) * Complex.I)
        = ζ ^ (4 * j + 1) := by
    intro j
    have harg : Complex.ofReal
          (Real.pi * (4 * (j : ℝ) + 1) * (p : ℝ) / (4 * (N : ℝ))) * Complex.I
        = ((4 * j + 1 : ℕ) : ℂ) * ((γ : ℂ) * Complex.I) := by
      have hr : Real.pi * (4 * (j : ℝ) + 1) * (p : ℝ) / (4 * (N : ℝ))
          = (4 * (j : ℝ) + 1) * γ := by rw [hγ]; ring
      rw [hr, Complex.ofReal_mul]
      push_cast
      ring
    rw [harg, hζ, ← Complex.exp_nat_mul]
  set C : ℂ := ∏ j ∈ Finset.range N, ζ ^ (4 * j + 1) with hC
  set P : ℂ := ∏ j ∈ Finset.range N, (ζ ^ (4 * j + 1) + (ζ ^ (4 * j + 1))⁻¹) with hP
  -- (Q : ℂ) equals the complex product P
  have hQP : (Q : ℂ) = P := by
    rw [hQ, hP, Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro j _
    rw [Complex.ofReal_mul, Complex.ofReal_ofNat,
      ← exp_add_exp_neg_eq_two_cos (Real.pi * (4 * (j : ℝ) + 1) * (p : ℝ) / (4 * (N : ℝ)))]
    rw [hzpow j, Complex.exp_neg, hzpow j]
  -- factor each term
  have hfac : ∀ j : ℕ, ζ ^ (4 * j + 1) + (ζ ^ (4 * j + 1))⁻¹
      = (ζ ^ (4 * j + 1))⁻¹ * (1 - A * ω ^ j) := by
    intro j
    have hx : ζ ^ (4 * j + 1) ≠ 0 := pow_ne_zero _ hζne
    have hAω : A * ω ^ j = -(ζ ^ (4 * j + 1)) ^ 2 := by
      have e1 : A * ω ^ j = -(ζ ^ 2 * (ζ ^ 8) ^ j) := by rw [hA, hωdef, neg_mul]
      have e2 : ζ ^ 2 * (ζ ^ 8) ^ j = ζ ^ (2 + 8 * j) := by rw [← pow_mul, ← pow_add]
      have e3 : (ζ ^ (4 * j + 1)) ^ 2 = ζ ^ (2 + 8 * j) := by
        rw [← pow_mul]; congr 1; ring
      rw [e1, e2, e3]
    rw [hAω, show (1 - (-(ζ ^ (4 * j + 1)) ^ 2)) = 1 + (ζ ^ (4 * j + 1)) ^ 2 by ring,
      mul_add, mul_one]
    rw [show (ζ ^ (4 * j + 1))⁻¹ * (ζ ^ (4 * j + 1)) ^ 2 = ζ ^ (4 * j + 1) by
      rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]]
    ring
  have hstep : P = (∏ j ∈ Finset.range N, (ζ ^ (4 * j + 1))⁻¹)
      * (∏ j ∈ Finset.range N, (1 - A * ω ^ j)) := by
    rw [hP, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    exact hfac j
  have hAinv : A ^ N = (-1 : ℂ) ^ N * ζ ^ (2 * N) := by
    rw [hA, neg_pow]; congr 1; rw [← pow_mul]
  have hprodA : ∏ j ∈ Finset.range N, (1 - A * ω ^ j) = 1 - A ^ N := by
    have hshift := Work.TMC16Core.Basic.prod_range_shift N hNpos ω hωprim A 1
    rw [one_pow] at hshift
    have h1 : ∏ j ∈ Finset.range N, (1 - A * ω ^ j)
        = (-1 : ℂ) ^ N * ∏ j ∈ Finset.range N, (A * ω ^ j - 1) := by
      rw [show (∏ j ∈ Finset.range N, (1 - A * ω ^ j))
            = ∏ j ∈ Finset.range N, (-(A * ω ^ j - 1)) by
            apply Finset.prod_congr rfl; intro j _; ring]
      rw [Finset.prod_neg, Finset.card_range]
    rw [h1, hshift]
    have hsign : (-1 : ℂ) ^ N * (-1) ^ (N + 1) = -1 := by
      rw [pow_succ]
      rw [← mul_assoc, ← pow_add, show N + N = 2 * N by ring, pow_mul]
      norm_num
    rw [← mul_assoc, hsign]; ring
  have hPval : P = C⁻¹ * (1 - (-1 : ℂ) ^ N * ζ ^ (2 * N)) := by
    rw [hC, hstep, Finset.prod_inv_distrib, hprodA, hAinv]
  -- conjugation
  have hconjζ : (starRingEnd ℂ) ζ = ζ⁻¹ := by
    rw [hζ, ← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hconjC : (starRingEnd ℂ) C = C⁻¹ := by
    rw [hC, map_prod, ← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [map_pow, hconjζ, ← inv_pow]
  have hCne : C ≠ 0 := by
    rw [hC]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ hζne)
  have huadd : ζ ^ (2 * N) + (ζ ^ (2 * N))⁻¹ = 0 := by
    have hx : ζ ^ (2 * N) ≠ 0 := pow_ne_zero _ hζne
    have h2 : ζ ^ (2 * N) * (ζ ^ (2 * N) + (ζ ^ (2 * N))⁻¹) = 0 := by
      rw [mul_add, mul_inv_cancel₀ hx, ← pow_two, hu2]; ring
    exact (mul_eq_zero.mp h2).resolve_left hx
  have hε : (-1 : ℂ) ^ N * (-1 : ℂ) ^ N = 1 := by
    rw [← pow_add, show N + N = 2 * N by ring, pow_mul]; norm_num
  have hPsq : P * (starRingEnd ℂ) P = 2 := by
    have hconjd : (starRingEnd ℂ) (1 - (-1 : ℂ) ^ N * ζ ^ (2 * N))
        = 1 - (-1 : ℂ) ^ N * (ζ ^ (2 * N))⁻¹ := by
      simp only [map_sub, map_one, map_mul, map_neg, map_pow, hconjζ, inv_pow]
    have hconjCi : (starRingEnd ℂ) (C⁻¹) = C := by
      rw [Complex.conj_inv, hconjC, inv_inv]
    rw [hPval, map_mul, hconjCi, hconjd]
    rw [mul_mul_mul_comm, inv_mul_cancel₀ hCne, one_mul]
    exact pair_eq_two (ζ ^ (2 * N)) ((ζ ^ (2 * N))⁻¹) ((-1 : ℂ) ^ N)
      (mul_inv_cancel₀ (pow_ne_zero _ hζne)) huadd hε
  have hsq : ((Q : ℂ)) ^ 2 = 2 := by
    rw [hQP]
    have hPconj : (starRingEnd ℂ) P = P := by rw [← hQP, Complex.conj_ofReal]
    have h2 : P ^ 2 = P * (starRingEnd ℂ) P := by rw [hPconj, pow_two]
    rw [h2, hPsq]
  have hsz : ((Q ^ 2 : ℝ) : ℂ) = ((2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow, Complex.ofReal_ofNat]
    exact hsq
  exact Complex.ofReal_injective hsz

end Work.TMC14Core.Adjunct
