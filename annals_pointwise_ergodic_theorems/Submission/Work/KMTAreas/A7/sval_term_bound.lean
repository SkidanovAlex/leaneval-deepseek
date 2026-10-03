import Mathlib
import Submission.Work.A7.ModelApproxCore_M0_defs

namespace Work.KMTAreas.A7

open Polynomial

/-- **The size of the frequency scale term.**

With `Sval P k₁ k₂ = 2^{k₁} + 2^{d k₂}` (`d = P.natDegree`) and `k₁, k₂ ≤ L`, the quantity
`(1 + Sval²) · 2^{k₁ + d k₂}` is at most `2^{3(d+1)L + 4}`; this is the elementary bookkeeping
factor of the §6 single-scale model estimate. -/
theorem sval_term_bound (P : Polynomial ℤ) (L k₁ k₂ : ℕ) (h₁ : k₁ ≤ L) (h₂ : k₂ ≤ L) :
    (1 + (Work.A7.Sval P k₁ k₂) ^ 2) * (2 : ℝ) ^ (k₁ + P.natDegree * k₂)
      ≤ (2 : ℝ) ^ (3 * (P.natDegree + 1) * L + 4) := by
  set D := max P.natDegree 1 with hD
  have hDge1 : 1 ≤ D := by rw [hD]; exact le_max_right _ _
  have hdle : P.natDegree ≤ D := by rw [hD]; exact le_max_left _ _
  have hDle : D ≤ P.natDegree + 1 := by rw [hD]; exact max_le (by omega) (by omega)
  have hLle : L ≤ D * L := by
    calc L = 1 * L := (one_mul L).symm
      _ ≤ D * L := Nat.mul_le_mul_right L hDge1
  have hk1 : k₁ ≤ D * L := le_trans h₁ hLle
  have hk2 : P.natDegree * k₂ ≤ D * L := by
    calc P.natDegree * k₂ ≤ P.natDegree * L := Nat.mul_le_mul_left _ h₂
      _ ≤ D * L := Nat.mul_le_mul_right L hdle
  have hSnn : 0 ≤ Work.A7.Sval P k₁ k₂ := by rw [Work.A7.Sval]; positivity
  have hS1 : Work.A7.Sval P k₁ k₂ ≤ (2:ℝ)^(D*L) * 2 := by
    rw [Work.A7.Sval]
    have e1 : (2:ℝ)^k₁ ≤ (2:ℝ)^(D*L) := pow_le_pow_right₀ (by norm_num) hk1
    have e2 : (2:ℝ)^(P.natDegree*k₂) ≤ (2:ℝ)^(D*L) := pow_le_pow_right₀ (by norm_num) hk2
    linarith
  have hS1' : Work.A7.Sval P k₁ k₂ ≤ (2:ℝ)^(D*L+1) := by
    rw [pow_succ]; exact hS1
  have hSsq : (Work.A7.Sval P k₁ k₂)^2 ≤ (2:ℝ)^(2*(D*L+1)) := by
    calc (Work.A7.Sval P k₁ k₂)^2 ≤ ((2:ℝ)^(D*L+1))^2 := pow_le_pow_left₀ hSnn hS1' 2
      _ = (2:ℝ)^(2*(D*L+1)) := by rw [← pow_mul, Nat.mul_comm]
  have hone : (1:ℝ) ≤ (2:ℝ)^(2*(D*L+1)) := one_le_pow₀ (by norm_num)
  have h1S : 1 + (Work.A7.Sval P k₁ k₂)^2 ≤ (2:ℝ)^(2*(D*L+1)+1) := by
    calc 1 + (Work.A7.Sval P k₁ k₂)^2
        ≤ (2:ℝ)^(2*(D*L+1)) + (2:ℝ)^(2*(D*L+1)) := add_le_add hone hSsq
      _ = (2:ℝ)^(2*(D*L+1)+1) := by rw [pow_succ]; ring
  have hfac : (2:ℝ)^(k₁ + P.natDegree * k₂) ≤ (2:ℝ)^((P.natDegree+1)*L) := by
    apply pow_le_pow_right₀ (by norm_num)
    calc k₁ + P.natDegree * k₂ ≤ L + P.natDegree * L := add_le_add h₁ (Nat.mul_le_mul_left _ h₂)
      _ = (P.natDegree + 1) * L := by ring
  have hprod : (1 + (Work.A7.Sval P k₁ k₂)^2) * (2:ℝ)^(k₁ + P.natDegree * k₂)
      ≤ (2:ℝ)^(2*(D*L+1)+1) * (2:ℝ)^((P.natDegree+1)*L) :=
    mul_le_mul h1S hfac (by positivity) (by positivity)
  have hpow : (2:ℝ)^(2*(D*L+1)+1) * (2:ℝ)^((P.natDegree+1)*L)
      = (2:ℝ)^(2*(D*L+1)+1 + (P.natDegree+1)*L) := (pow_add _ _ _).symm
  have hexp : 2*(D*L+1)+1 + (P.natDegree+1)*L ≤ 3*(P.natDegree+1)*L + 4 := by
    have hX : D*L ≤ (P.natDegree+1)*L := Nat.mul_le_mul_right L hDle
    nlinarith [hX]
  calc (1 + (Work.A7.Sval P k₁ k₂)^2) * (2:ℝ)^(k₁ + P.natDegree*k₂)
      ≤ (2:ℝ)^(2*(D*L+1)+1) * (2:ℝ)^((P.natDegree+1)*L) := hprod
    _ = (2:ℝ)^(2*(D*L+1)+1 + (P.natDegree+1)*L) := hpow
    _ ≤ (2:ℝ)^(3*(P.natDegree+1)*L + 4) := pow_le_pow_right₀ (by norm_num) hexp

end Work.KMTAreas.A7
