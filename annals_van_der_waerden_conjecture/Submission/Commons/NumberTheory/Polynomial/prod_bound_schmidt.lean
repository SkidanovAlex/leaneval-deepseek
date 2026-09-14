import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.NumberTheory.Polynomial

open Finset

theorem prod_bound_schmidt (n : ℕ) (hn : 3 ≤ n) {Y : ℝ} (hY : 1 ≤ Y) :
    (∏ i ∈ (Finset.range (n + 1)).erase (n - 1),
        (2 * (2 ^ n * (2 ^ (2 * n + 6) * Y ^ (1 / (2 * ((n : ℝ) - 1)))) ^ (n - i)) + 1))
      ≤ (2 ^ (n * (n + 2)) * (2 ^ (2 * n + 6)) ^ (n * (n + 1) / 2 - 1) * 2) *
          Y ^ (((n : ℝ) + 2) / 4) := by
  have hmul1 : ∀ {x y : ℝ}, 1 ≤ x → 1 ≤ y → 1 ≤ x * y := by
    intro x y hx hy
    have h := mul_le_mul hx hy (zero_le_one : (0 : ℝ) ≤ 1) (by linarith : (0 : ℝ) ≤ x)
    simpa using h
  set b : ℝ := 2 ^ (2 * n + 6) * Y ^ (1 / (2 * ((n : ℝ) - 1))) with hbdef
  set S : Finset ℕ := (Finset.range (n + 1)).erase (n - 1) with hSdef
  set x : ℕ := ∑ i ∈ S, (n - i) with hxdef
  set U : ℕ := ∑ i ∈ Finset.range (n + 1), (n - i) with hUdef
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
  have hYnonneg : (0 : ℝ) ≤ Y := le_trans zero_le_one hY
  have hbden : (0 : ℝ) < 2 * ((n : ℝ) - 1) := by linarith
  have hb1 : 1 ≤ b := by
    rw [hbdef]
    exact hmul1 (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      (Real.one_le_rpow hY (le_of_lt (div_pos one_pos hbden)))
  -- Cardinality and sum identities
  have hmem : n - 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hcard : S.card = n := by
    rw [hSdef, Finset.card_erase_of_mem hmem]
    simp [Finset.card_range]
  have hsum_reflect : (∑ i ∈ Finset.range (n + 1), (n - i)) = ∑ i ∈ Finset.range (n + 1), i := by
    have h := Finset.sum_range_reflect (fun i : ℕ => i) (n + 1)
    simpa using h
  have hsum_erase : x + 1 = U := by
    rw [hxdef, hUdef, hSdef]
    have h := Finset.sum_erase_add (Finset.range (n + 1)) (fun i => n - i) hmem
    have hh : n - (n - 1) = 1 := Nat.sub_sub_self (by omega : 1 ≤ n)
    simpa [hh] using h
  have hU2 : U * 2 = n * (n + 1) := by
    rw [hUdef]
    rw [hsum_reflect]
    have h := Finset.sum_range_id_mul_two (n + 1)
    rw [h]
    simp only [Nat.add_sub_cancel]
    ring
  have hK2 : n * (n + 1) / 2 * 2 = n * (n + 1) :=
    Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_succ_self n))
  have hTK1 : x + 1 = n * (n + 1) / 2 := by
    have h1 : (x + 1) * 2 = n * (n + 1) := by rw [hsum_erase]; exact hU2
    have h2 : (x + 1) * 2 = (n * (n + 1) / 2) * 2 := by rw [h1, hK2]
    exact Nat.mul_right_cancel (by norm_num : 0 < 2) h2
  have hTK : x = n * (n + 1) / 2 - 1 := by omega
  -- Real exponent identities
  have hTreal0 : 2 * ((x : ℝ) + 1) = (n : ℝ) * ((n : ℝ) + 1) := by
    have hnat : (x + 1) * 2 = n * (n + 1) := by rw [hTK1, hK2]
    have hcast := congrArg (fun m : ℕ => (m : ℝ)) hnat
    push_cast at hcast
    linarith [hcast]
  have hTreal1 : 2 * (x : ℝ) = ((n : ℝ) - 1) * ((n : ℝ) + 2) := by
    nlinarith [hTreal0]
  have hK1real : 2 * (((n * (n + 1) / 2 - 1 : ℕ)) : ℝ) = ((n : ℝ) - 1) * ((n : ℝ) + 2) := by
    rw [← hTK]
    exact hTreal1
  have hrexp : (1 / (2 * ((n : ℝ) - 1))) * (((n * (n + 1) / 2 - 1 : ℕ)) : ℝ)
      = ((n : ℝ) + 2) / 4 := by
    have hne : ((n : ℝ) - 1) ≠ 0 := by linarith
    field_simp
    nlinarith [hK1real]
  -- Pointwise bound
  have hterm : ∀ i ∈ S, 2 * (2 ^ n * b ^ (n - i)) + 1 ≤ 2 ^ (n + 2) * b ^ (n - i) := by
    intro i hi
    have hbpow : 1 ≤ b ^ (n - i) := one_le_pow₀ hb1
    have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hA1 : 1 ≤ 2 ^ n * b ^ (n - i) := hmul1 h2n hbpow
    have h4 : (2 : ℝ) ^ (n + 2) * b ^ (n - i) = 4 * (2 ^ n * b ^ (n - i)) := by
      rw [pow_add]
      ring_nf
    rw [h4]
    nlinarith [hA1]
  have hnonneg : ∀ i ∈ S, 0 ≤ 2 * (2 ^ n * b ^ (n - i)) + 1 := by
    intro i hi
    have hp : (0 : ℝ) ≤ b ^ (n - i) := pow_nonneg (le_trans zero_le_one hb1) _
    positivity
  have hprod := Finset.prod_le_prod hnonneg hterm
  have hprodval : (∏ i ∈ S, (2 ^ (n + 2) * b ^ (n - i))) =
      2 ^ (n * (n + 2)) * b ^ (n * (n + 1) / 2 - 1) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, hcard]
    rw [← hxdef, hTK]
    have hpoweq : ((2 : ℝ) ^ (n + 2)) ^ n = 2 ^ (n * (n + 2)) := by
      rw [← pow_mul]; ring_nf
    rw [hpoweq]
  have hexpand : b ^ (n * (n + 1) / 2 - 1) =
      (2 ^ (2 * n + 6)) ^ (n * (n + 1) / 2 - 1) * Y ^ (((n : ℝ) + 2) / 4) := by
    rw [hbdef, mul_pow]
    congr 1
    rw [← Real.rpow_natCast (Y ^ (1 / (2 * ((n : ℝ) - 1)))),
        ← Real.rpow_mul hYnonneg, hrexp]
  have hfin : 2 ^ (n * (n + 2)) * b ^ (n * (n + 1) / 2 - 1) ≤
      (2 ^ (n * (n + 2)) * (2 ^ (2 * n + 6)) ^ (n * (n + 1) / 2 - 1) * 2) *
          Y ^ (((n : ℝ) + 2) / 4) := by
    rw [hexpand]
    have hYpow : 0 ≤ Y ^ (((n : ℝ) + 2) / 4) := Real.rpow_nonneg hYnonneg _
    have hP : (0 : ℝ) ≤ 2 ^ (n * (n + 2)) := by positivity
    have hQ : (0 : ℝ) ≤ (2 ^ (2 * n + 6)) ^ (n * (n + 1) / 2 - 1) := by positivity
    nlinarith [mul_nonneg (mul_nonneg hP hQ) hYpow]
  exact hprod.trans ((le_of_eq hprodval).trans hfin)

end Commons.NumberTheory.Polynomial