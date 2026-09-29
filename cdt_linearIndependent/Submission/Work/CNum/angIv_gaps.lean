import Mathlib
import Submission.Work.CNum.Fx

/-!
# `Work.CNum.angIv_gaps` — the two-sided gap of the angle enclosure

`angIv m` is the interval mantissa enclosure of the angle `m·π/1024` (`m` an integer index of
the `1024`-th roots of unity, `SC = 2^30`):

`angIv m = [⌊m·piLo/1024⌋/SC, ⌈m·piHi/1024⌉/SC]`, `piLo = ⌊π·SC⌋`, `piHi = ⌊π·SC⌋ + 1`.

The point of this file is that the enclosure is *strictly* two-sided with a quantitative gap:
the lower endpoint is at least `2⁻⁴⁰` below `m·π/1024` and the upper endpoint at least `2⁻⁴¹`
above it.  This is what makes the angle enclosure usable in the chord bounds of the `CNum`
certificate (there the gap has to beat `2⁻⁴⁰`, one `SC`-scale).

The whole content is the single numerical fact `1/8 ≤ π·SC - piLo ≤ 1/2`, which we obtain from
Mathlib's 20-digit bounds `Real.pi_gt_d20`/`Real.pi_lt_d20`; the rest is exact integer
`ediv`/`emod` bookkeeping.

* For the lower endpoint write `m·piLo = 1024·q + r`, `q = ⌊m·piLo/1024⌋`, `0 ≤ r < 1024`:
  `m·π/1024 - q/SC = (m·(π·SC - piLo) + r)/(1024·SC)`, and `m·(π·SC - piLo) + r ≥ 1`
  because `π·SC - piLo ≥ 1/8` and either `r ≥ 1`, or `r = 0` and then `m ≥ 8` (for `m ≤ 7`
  one checks `(m·piLo) % 1024 ≠ 0` directly).
* For the upper endpoint write `1024·s = m·piHi + r'`, `s = ⌈m·piHi/1024⌉`, `0 ≤ r' < 1024`:
  `s/SC - m·π/1024 = (m·(piHi - π·SC) + r')/(1024·SC)`, and `m·(piHi - π·SC) ≥ 1/2` because
  `π·SC ≤ piLo + 1/2` and `m ≥ 1`.

Both numerators are thus at least `1` resp. `1/2`, and `1024·SC = 2⁴⁰`.
-/

namespace Work.CNum

open Work.ANum

/-- `Int.ediv`/`Int.emod` decomposition `a = b·(a/b) + a%b`, cast to `ℝ`. -/
lemma angIvGaps_ediv_emod_cast (a b : ℤ) (_hb : b ≠ 0) :
    (a : ℝ) = (b : ℝ) * ((a / b : ℤ) : ℝ) + ((a % b : ℤ) : ℝ) := by
  have h := Int.mul_ediv_add_emod a b
  have h2 := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at h2
  linarith [h2]

/-- `π·SC ≥ piLo + 1/8`, from `Real.pi_gt_d20`. -/
lemma angIvGaps_pi_lo : (3373259426 : ℝ) + 1/8 ≤ Real.pi * (SC : ℝ) := by
  have hSC : (SC : ℝ) = (2 : ℝ) ^ 30 := by norm_num [SC]
  have h1 : (3373259426 : ℝ) + 1/8 ≤ (3.14159265358979323846 : ℝ) * 2 ^ 30 := by norm_num
  have h2 : (3.14159265358979323846 : ℝ) * 2 ^ 30 < Real.pi * 2 ^ 30 := by
    have hp := Real.pi_gt_d20
    nlinarith [show (0 : ℝ) < 2 ^ 30 by norm_num]
  rw [hSC]; linarith

/-- `π·SC ≤ piLo + 1/2`, from `Real.pi_lt_d20`. -/
lemma angIvGaps_pi_hi : Real.pi * (SC : ℝ) ≤ (3373259426 : ℝ) + 1/2 := by
  have hSC : (SC : ℝ) = (2 : ℝ) ^ 30 := by norm_num [SC]
  have h1 : (3.14159265358979323847 : ℝ) * 2 ^ 30 ≤ (3373259426 : ℝ) + 1/2 := by norm_num
  have h2 : Real.pi * 2 ^ 30 < (3.14159265358979323847 : ℝ) * 2 ^ 30 := by
    have hp := Real.pi_lt_d20
    nlinarith [show (0 : ℝ) < 2 ^ 30 by norm_num]
  rw [hSC]; linarith

theorem angIv_gaps :
    (∀ m : ℕ, 1 ≤ m → ((2 : ℝ) ^ 40)⁻¹ ≤ (m : ℝ) * Real.pi / 1024 - Work.ANum.m2r (angIv m).lo) ∧
    (∀ m : ℕ, 1 ≤ m → ((2 : ℝ) ^ 41)⁻¹ ≤ Work.ANum.m2r (angIv m).hi - (m : ℝ) * Real.pi / 1024) := by
  have hpiLo : (3373259426 : ℝ) + 1/8 ≤ Real.pi * (SC : ℝ) := angIvGaps_pi_lo
  have hpiHi : Real.pi * (SC : ℝ) ≤ (3373259426 : ℝ) + 1/2 := angIvGaps_pi_hi
  constructor
  · -- lower endpoint
    intro m hm
    set a : ℤ := (m : ℤ) * 3373259426 with ha
    set q : ℤ := a / 1024 with hq
    set r : ℤ := a % 1024 with hr
    have hdecomp : (a : ℝ) = 1024 * (q : ℝ) + (r : ℝ) := by
      rw [ha, hq, hr]; exact angIvGaps_ediv_emod_cast _ 1024 (by norm_num)
    have hA : (a : ℝ) = (m : ℝ) * 3373259426 := by rw [ha]; push_cast; ring
    have hqexpr : (m : ℝ) * 3373259426 = 1024 * (q : ℝ) + (r : ℝ) := by
      rw [← hA]; exact hdecomp
    have hlo : (angIv m).lo = q := by rw [hq, ha]; rfl
    have hr0 : 0 ≤ r := by rw [hr]; exact Int.emod_nonneg a (by norm_num)
    have hmr : Work.ANum.m2r (angIv m).lo = (q : ℝ) / (SC : ℝ) := by
      rw [hlo, Work.ANum.m2r]
    rw [hmr]
    have key : (m : ℝ) * Real.pi / 1024 - (q : ℝ) / (SC : ℝ)
        = ((m : ℝ) * (Real.pi * (SC : ℝ) - 3373259426) + (r : ℝ)) / (1024 * (SC : ℝ)) := by
      have hSC : (SC : ℝ) ≠ 0 := ne_of_gt SC_posR
      field_simp
      linarith [hqexpr]
    rw [key]
    have hε : (1/8 : ℝ) ≤ Real.pi * (SC : ℝ) - 3373259426 := by linarith
    have hε0 : (0 : ℝ) ≤ Real.pi * (SC : ℝ) - 3373259426 := by linarith
    have hr0' : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
    have hnum : (1 : ℝ) ≤ (m : ℝ) * (Real.pi * (SC : ℝ) - 3373259426) + (r : ℝ) := by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
      by_cases hm8 : 8 ≤ m
      · have hm8' : (8 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm8
        have h2 : (1 : ℝ) ≤ (m : ℝ) * (1/8) := by linarith
        have h3 : (m : ℝ) * (1/8) ≤ (m : ℝ) * (Real.pi * (SC : ℝ) - 3373259426) :=
          mul_le_mul_of_nonneg_left hε hm0
        linarith
      · have hm7 : m ≤ 7 := by omega
        have hr1 : 1 ≤ r := by
          rw [hr, ha]
          interval_cases m <;> decide
        have hr1' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
        have h3 : (0 : ℝ) ≤ (m : ℝ) * (Real.pi * (SC : ℝ) - 3373259426) :=
          mul_nonneg hm0 hε0
        linarith
    have hden : (1024 : ℝ) * (SC : ℝ) = (2 : ℝ) ^ 40 := by norm_num [SC]
    rw [hden]
    have h := div_le_div_of_nonneg_right hnum (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 40)
    simpa [one_div] using h
  · -- upper endpoint
    intro m hm
    set a : ℤ := (m : ℤ) * 3373259427 with ha
    set s : ℤ := -((-a) / 1024) with hs
    set r : ℤ := (-a) % 1024 with hr
    have hdecomp : 1024 * s = a + r := by
      have h := Int.mul_ediv_add_emod (-a) 1024
      simp only [hs, hr]
      linarith [h]
    have hhi : (angIv m).hi = s := by rw [hs, ha]; rfl
    have hr0 : 0 ≤ r := by rw [hr]; exact Int.emod_nonneg _ (by norm_num)
    have hmr : Work.ANum.m2r (angIv m).hi = (s : ℝ) / (SC : ℝ) := by
      rw [hhi, Work.ANum.m2r]
    rw [hmr]
    have hcast : 1024 * (s : ℝ) = (m : ℝ) * 3373259427 + (r : ℝ) := by
      have h2 := congrArg (fun z : ℤ => (z : ℝ)) hdecomp
      rw [ha] at h2
      push_cast at h2
      linarith
    have key : (s : ℝ) / (SC : ℝ) - (m : ℝ) * Real.pi / 1024
        = ((m : ℝ) * (3373259427 - Real.pi * (SC : ℝ)) + (r : ℝ)) / (1024 * (SC : ℝ)) := by
      have hSC : (SC : ℝ) ≠ 0 := ne_of_gt SC_posR
      field_simp
      linarith [hcast]
    rw [key]
    have hδ : (1/2 : ℝ) ≤ 3373259427 - Real.pi * (SC : ℝ) := by linarith
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hr0' : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
    have hnum : (1/2 : ℝ) ≤ (m : ℝ) * (3373259427 - Real.pi * (SC : ℝ)) + (r : ℝ) := by
      have h3 : (1 : ℝ) * (1/2) ≤ (m : ℝ) * (3373259427 - Real.pi * (SC : ℝ)) :=
        mul_le_mul hm1 hδ (by norm_num) hm0
      linarith
    have hden : (1024 : ℝ) * (SC : ℝ) = (2 : ℝ) ^ 40 := by norm_num [SC]
    rw [hden]
    have h := div_le_div_of_nonneg_right hnum (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 40)
    have heq : ((2 : ℝ) ^ 41)⁻¹ = (1/2) / (2 : ℝ) ^ 40 := by norm_num
    rw [heq]
    exact h

end Work.CNum
