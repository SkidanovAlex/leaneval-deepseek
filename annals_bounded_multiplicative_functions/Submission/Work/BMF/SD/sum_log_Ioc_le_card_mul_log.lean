import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

open Finset

/-- Every prime in `(⌊b⌋, ⌊b+h⌋]` is at most `2*b` when `h ≤ b`, hence each `log p` is
at most `log (2*b)`; summing over the (finitely many) primes in the interval gives the
bound by the cardinality times `log (2*b)`. -/
theorem sum_log_Ioc_le_card_mul_log (b h : ℝ) (hhb : h ≤ b) :
    (∑ p ∈ (Finset.Ioc ⌊b⌋₊ ⌊b + h⌋₊).filter Nat.Prime, Real.log (p : ℝ)) ≤
      (((Finset.Ioc ⌊b⌋₊ ⌊b + h⌋₊).filter Nat.Prime).card : ℝ) * Real.log (2 * b) := by
  set S : Finset ℕ := (Finset.Ioc ⌊b⌋₊ ⌊b + h⌋₊).filter Nat.Prime with hS
  have hkey : ∀ p ∈ S, Real.log (p : ℝ) ≤ Real.log (2 * b) := by
    intro p hp
    obtain ⟨hpIoc, hpprime⟩ := Finset.mem_filter.mp hp
    have hp2 : 2 ≤ p := hpprime.two_le
    have hple : p ≤ ⌊b + h⌋₊ := (Finset.mem_Ioc.mp hpIoc).2
    have hfl_ge : 1 ≤ ⌊b + h⌋₊ := le_trans (by norm_num) (le_trans hp2 hple)
    have hbh_nonneg : 0 ≤ b + h := by
      by_contra hneg
      rw [not_le] at hneg
      have hlt1 : b + h < 1 := by linarith
      have hz : ⌊b + h⌋₊ = 0 := Nat.floor_eq_zero.mpr hlt1
      rw [hz] at hfl_ge
      omega
    have hbh_le : (⌊b + h⌋₊ : ℝ) ≤ b + h := Nat.floor_le hbh_nonneg
    have hp_le_2b : (p : ℝ) ≤ 2 * b := by
      have h1 : (p : ℝ) ≤ (⌊b + h⌋₊ : ℝ) := by exact_mod_cast hple
      linarith
    exact Real.log_le_log (by exact_mod_cast (Nat.Prime.pos hpprime)) hp_le_2b
  calc ∑ p ∈ S, Real.log (p : ℝ)
      ≤ ∑ p ∈ S, Real.log (2 * b) := Finset.sum_le_sum hkey
    _ = (S.card : ℝ) * Real.log (2 * b) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end Work.BMF.SD
