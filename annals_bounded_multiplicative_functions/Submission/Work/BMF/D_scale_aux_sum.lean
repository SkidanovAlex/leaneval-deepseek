import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

set_option linter.unusedVariables false

/-- Scaling the prime cut-off in an additive "wrap" sum: since `Y ≤ K * Y'` and
`t p ≤ 2 / p`, the primes in `(⌊Y'⌋₊, ⌊Y⌋₊]` contribute at most `2 * K`.
(No prime-distribution input is needed: the interval `(a, b]` has at most `b - a`
integers, each contributing at most `2 / (a + 1)`, and `b ≤ K * (a + 1)`.) -/
theorem D_scale_aux_sum {K Y Y' : ℝ} (hK : 1 ≤ K) (hY' : 11 ≤ Y') (hYK : Y / K ≤ Y') (hY'Y : Y' ≤ Y)
    (t : ℕ → ℝ) (ht0 : ∀ p, 0 ≤ t p) (ht2 : ∀ p, t p ≤ 2 / (p : ℝ)) :
    (∑ p ∈ ⌊Y⌋₊.primesLE, t p) ≤ (∑ p ∈ ⌊Y'⌋₊.primesLE, t p) + 2 * K := by
  set a : ℕ := ⌊Y'⌋₊ with ha
  set b : ℕ := ⌊Y⌋₊ with hb
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
  have hY0 : 0 ≤ Y := by linarith
  have hab : a ≤ b := by
    have h := Nat.floor_mono hY'Y
    simpa [ha, hb] using h
  have hsub : a.primesLE ⊆ b.primesLE := Nat.primesLE_mono hab
  have hb_le : (b : ℝ) ≤ Y := by
    rw [hb]; exact Nat.floor_le hY0
  have hbK : (b : ℝ) ≤ K * ((a : ℝ) + 1) := by
    have hYK' : Y ≤ Y' * K := (div_le_iff₀ hKpos).mp hYK
    have h2 : K * Y' ≤ K * ((a : ℝ) + 1) := by
      have h := Nat.lt_floor_add_one Y'
      rw [ha]
      nlinarith [hKpos]
    linarith
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have ha1 : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hstep : ∑ p ∈ Finset.Ioc a b, (2 : ℝ) / (p : ℝ) ≤ 2 * K := by
    calc ∑ p ∈ Finset.Ioc a b, (2 : ℝ) / (p : ℝ)
        ≤ ∑ p ∈ Finset.Ioc a b, (2 : ℝ) / ((a : ℝ) + 1) := by
          apply Finset.sum_le_sum
          intro p hp
          have hpgt : a < p := (Finset.mem_Ioc.mp hp).1
          have hle : a + 1 ≤ p := by omega
          have hle' : ((a : ℝ) + 1) ≤ (p : ℝ) := by exact_mod_cast hle
          exact div_le_div_of_nonneg_left (by norm_num) ha1 hle'
      _ = ((b - a : ℕ) : ℝ) * ((2 : ℝ) / ((a : ℝ) + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc]
      _ ≤ 2 * K := by
          rw [Nat.cast_sub hab, ← mul_div_assoc, div_le_iff₀ ha1]
          nlinarith [hbK, ha0]
  have hsubI : b.primesLE \ a.primesLE ⊆ Finset.Ioc a b := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    obtain ⟨hpS, hpA⟩ := hp
    rw [Nat.mem_primesLE] at hpS
    obtain ⟨hpb, hpprime⟩ := hpS
    rw [Finset.mem_Ioc]
    refine ⟨?_, hpb⟩
    by_contra hc
    have hp_le_a : p ≤ a := by omega
    exact hpA (Nat.mem_primesLE.mpr ⟨hp_le_a, hpprime⟩)
  have hE : ∑ x ∈ b.primesLE \ a.primesLE, t x ≤ 2 * K := by
    calc ∑ x ∈ b.primesLE \ a.primesLE, t x
        ≤ ∑ x ∈ b.primesLE \ a.primesLE, (2 : ℝ) / (x : ℝ) :=
          Finset.sum_le_sum (fun p _ => ht2 p)
      _ ≤ ∑ p ∈ Finset.Ioc a b, (2 : ℝ) / (p : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubI
          intro p hp hpnot
          positivity
      _ ≤ 2 * K := hstep
  have hsd := Finset.sum_sdiff (f := t) hsub
  linarith [hE, hsd]

end Work.BMF
