import Mathlib
import Submission.Work.LinnikBurgess.frame_count_prov_defs

/-!
# The arithmetic core of the Case-T estimate

This is a pure arithmetic inequality: with
`rhsC C H m d g = C * τ(m·d·g)^8 * (H^6/(d·g) + H^5/g)` and `τ(n) = n.divisors.card`
we must show
`48 * τ(m)^3 * τ(g)^2 * H^4 / g ≤ rhsC 30000 H m d g`
for `d, g > 0`.

Everything rests on two elementary inputs:

* divisor-count monotonicity `τ(m), τ(g) ≤ τ(m·d·g)` (both `m` and `g` divide `m·d·g`,
  and `Nat.divisors_subset_of_dvd` gives inclusion of divisor sets), whence
  `τ(m)^3 τ(g)^2 ≤ τ(m·d·g)^5 ≤ τ(m·d·g)^8`;
* `H^6/d + H^5 ≥ H^4` for every natural `H` (for `H ≥ 1`, `H^5 ≥ H^4`; for `H = 0` both
  sides vanish), so `30000 · (H^6/d + H^5) ≥ 30000 H^4 ≥ 48 H^4`.

Combining and clearing the positive denominator `g` finishes the estimate.
-/

namespace Work.LinnikBurgess

theorem caseT_final_arith {H m d g : ℕ} (hd : 0 < d) (hg : 0 < g) :
    48 * ((m.divisors.card : ℝ)) ^ 3 * ((g.divisors.card : ℝ)) ^ 2 * (H : ℝ) ^ 4 / (g : ℝ)
      ≤ Work.LinnikBurgess.rhsC 30000 H m d g := by
  rw [rhsC]
  have hgr : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  -- the degenerate cases `H = 0` and `m = 0` both make the left-hand side vanish
  rcases Nat.eq_zero_or_pos H with hH | hH
  · subst hH
    simp
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [Nat.divisors_zero]
    simp
  -- main case: `H ≥ 1` and `m ≥ 1`
  have hh1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hh4 : (0 : ℝ) ≤ (H : ℝ) ^ 4 := pow_nonneg (Nat.cast_nonneg H) 4
  set T : ℝ := ((m * d * g).divisors.card : ℝ) with hTdef
  set S : ℝ := (H : ℝ) ^ 6 / (d : ℝ) + (H : ℝ) ^ 5 with hSdef
  have hmdg_pos : 0 < m * d * g := by positivity
  have hT1 : (1 : ℝ) ≤ T := by
    rw [hTdef]
    have : 1 ≤ (m * d * g).divisors.card :=
      Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hmdg_pos.ne'⟩
    exact_mod_cast this
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have hA : ((m.divisors.card : ℝ)) ≤ T := by
    rw [hTdef]
    have hsub : m.divisors ⊆ (m * d * g).divisors :=
      Nat.divisors_subset_of_dvd hmdg_pos.ne'
        (by rw [mul_assoc]; exact dvd_mul_right m (d * g))
    exact_mod_cast Finset.card_le_card hsub
  have hB : ((g.divisors.card : ℝ)) ≤ T := by
    rw [hTdef]
    have hsub : g.divisors ⊆ (m * d * g).divisors :=
      Nat.divisors_subset_of_dvd hmdg_pos.ne' ⟨m * d, by ring⟩
    exact_mod_cast Finset.card_le_card hsub
  have hA0 : (0 : ℝ) ≤ (m.divisors.card : ℝ) := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ (g.divisors.card : ℝ) := Nat.cast_nonneg _
  -- `τ(m)^3 · τ(g)^2 ≤ T^8`
  have hAB : ((m.divisors.card : ℝ)) ^ 3 * ((g.divisors.card : ℝ)) ^ 2 ≤ T ^ 8 := by
    have h1 : ((m.divisors.card : ℝ)) ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ hA0 hA 3
    have h2 : ((g.divisors.card : ℝ)) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hB0 hB 2
    have hmul : ((m.divisors.card : ℝ)) ^ 3 * ((g.divisors.card : ℝ)) ^ 2
        ≤ T ^ 3 * T ^ 2 := mul_le_mul h1 h2 (pow_nonneg hB0 2) (pow_nonneg hT0 3)
    have h35 : T ^ 3 * T ^ 2 = T ^ 5 := by ring
    have h58 : T ^ 5 ≤ T ^ 8 := pow_le_pow_right₀ hT1 (by norm_num)
    calc ((m.divisors.card : ℝ)) ^ 3 * ((g.divisors.card : ℝ)) ^ 2
        ≤ T ^ 3 * T ^ 2 := hmul
      _ = T ^ 5 := h35
      _ ≤ T ^ 8 := h58
  -- `48 H^4 ≤ 30000 S`
  have hcore : 48 * (H : ℝ) ^ 4 ≤ 30000 * S := by
    have h5ge4 : (H : ℝ) ^ 4 ≤ (H : ℝ) ^ 5 := pow_le_pow_right₀ hh1 (by norm_num)
    have h4leS : (H : ℝ) ^ 4 ≤ S := by
      rw [hSdef]
      exact h5ge4.trans (le_add_of_nonneg_left (by positivity))
    nlinarith [h4leS, hh4]
  -- combine the two denominators
  have hbracket : (H : ℝ) ^ 6 / ((d : ℝ) * (g : ℝ)) + (H : ℝ) ^ 5 / (g : ℝ)
      = S / (g : ℝ) := by
    rw [div_mul_eq_div_div, ← add_div, hSdef]
  rw [hbracket, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (le_of_lt hgr)
  have hT8 : (0 : ℝ) ≤ T ^ 8 := pow_nonneg hT0 8
  have key1 : ((m.divisors.card : ℝ)) ^ 3 * ((g.divisors.card : ℝ)) ^ 2 * (H : ℝ) ^ 4
      ≤ T ^ 8 * (H : ℝ) ^ 4 := mul_le_mul_of_nonneg_right hAB hh4
  have key2 : 48 * (T ^ 8 * (H : ℝ) ^ 4) ≤ 30000 * (T ^ 8 * S) := by
    have h := mul_le_mul_of_nonneg_left hcore hT8
    nlinarith [h]
  calc 48 * ((m.divisors.card : ℝ)) ^ 3 * ((g.divisors.card : ℝ)) ^ 2 * (H : ℝ) ^ 4
      = 48 * (((m.divisors.card : ℝ)) ^ 3 * ((g.divisors.card : ℝ)) ^ 2 * (H : ℝ) ^ 4) := by
        ring
    _ ≤ 48 * (T ^ 8 * (H : ℝ) ^ 4) := mul_le_mul_of_nonneg_left key1 (by norm_num)
    _ ≤ 30000 * (T ^ 8 * S) := key2
    _ = 30000 * T ^ 8 * S := by ring

end Work.LinnikBurgess
