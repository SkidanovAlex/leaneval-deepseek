import Mathlib
import Submission.Work.CNum.LgInfra

namespace Work.CNum

open Work.ANum

/-!
# `Work.CNum.ChordSpec` — the chord terms of the per-arc bounds

`Work.CNum.chord1`/`chord2` are the fixed-point mantissas computing, at scale `SC = 2^30`,
the quantities

`400 * (d + d³/12 + 4096)²`  and  `1000 * (d + d³/12 + 4096)²`.

The present file shows that the (outward rounded) mantissa values dominate the real
expressions they are meant to bound, i.e. for `x = m2r d ≥ 0`

`400 * (x + x³/12 + 4096/SC)² ≤ m2r (chord1 d)`, and likewise with `1000` and `chord2`.

The proof is pure monotone rounding.  Writing `u` for the mantissa `d + ⌈d³/SC²⌉/12 + 4096`,

* `m2r (mulU d d) ≥ (m2r d)²` and `m2r (mulU (mulU d d) d) ≥ (m2r d)³` (`le_mulU`), so
  `m2r (divU (mulU (mulU d d) d) 12) ≥ (m2r d)³/12` (`divU_ge`), whence `m2r u ≥ x + x³/12 + 4096/SC`;
* `m2r (mulU u u) ≥ (m2r u)²` and `m2r (mulU a (C·SC)) ≥ m2r a · C`, so
  `m2r (chord1 d) ≥ 400 · (m2r u)²`.

(The hypothesis `x ≥ 0` is used when multiplying `m2r (mulU d d) ≥ (m2r d)²` by `m2r d`
to obtain `(m2r d)³ ≤ m2r (mulU (mulU d d) d)`.)
-/

/-- The mantissa `d + ⌈d³/SC²⌉/12 + 4096` used by `chord1`/`chord2` dominates
`m2r d + (m2r d)³/12 + 4096/SC`, for `m2r d ≥ 0`. -/
private lemma chord_u_ge (d : ℤ) (hd : 0 ≤ m2r d) :
    m2r d + (m2r d) ^ 3 / 12 + 4096 / (SC : ℝ) ≤
      m2r (d + divU (mulU (mulU d d) d) 12 + 4096) := by
  have hx : 0 ≤ m2r d := hd
  have h1 : (m2r d) ^ 2 ≤ m2r (mulU d d) := by rw [pow_two]; exact le_mulU d d
  have h2 : (m2r d) ^ 3 ≤ m2r (mulU (mulU d d) d) := by
    calc (m2r d) ^ 3 = (m2r d) ^ 2 * m2r d := by ring
      _ ≤ m2r (mulU d d) * m2r d := mul_le_mul_of_nonneg_right h1 hx
      _ ≤ m2r (mulU (mulU d d) d) := le_mulU _ _
  have h3 : (m2r d) ^ 3 / 12 ≤ m2r (divU (mulU (mulU d d) d) 12) := by
    calc (m2r d) ^ 3 / 12 ≤ m2r (mulU (mulU d d) d) / 12 := by
            apply div_le_div_of_nonneg_right h2; norm_num
      _ ≤ m2r (divU (mulU (mulU d d) d) 12) := divU_ge (k := 12) (by norm_num) _
  have h4 : m2r (4096 : ℤ) = 4096 / (SC : ℝ) := by simp only [m2r]; push_cast; ring
  rw [m2r_add, m2r_add, h4]
  linarith

/-- The general chord bound: for `C ≥ 0`, `m2r (mulU (mulU u u) (C * SC))` dominates
`C · u²`, where `u` is the mantissa for `d + d³/12 + 4096`. -/
private lemma chord_gen (d C : ℤ) (hC : 0 ≤ C) (hd : 0 ≤ m2r d) :
    (C : ℝ) * (m2r d + (m2r d) ^ 3 / 12 + 4096 / (SC : ℝ)) ^ 2
      ≤ m2r (mulU (mulU (d + divU (mulU (mulU d d) d) 12 + 4096)
                        (d + divU (mulU (mulU d d) d) 12 + 4096)) (C * SC)) := by
  set u : ℤ := d + divU (mulU (mulU d d) d) 12 + 4096 with hu
  have hL := chord_u_ge d hd
  rw [← hu] at hL
  have hLnn : 0 ≤ m2r d + (m2r d) ^ 3 / 12 + 4096 / (SC : ℝ) := by
    have h3 : 0 ≤ (m2r d) ^ 3 := pow_nonneg hd 3
    have h4 : (0 : ℝ) < 4096 / (SC : ℝ) := by
      apply div_pos (by norm_num); exact SC_posR
    linarith
  have hCnn : (0 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
  have hsq : (m2r u) ^ 2 ≤ m2r (mulU u u) := by rw [pow_two]; exact le_mulU u u
  have hmul : (C : ℝ) * m2r (mulU u u) ≤ m2r (mulU (mulU u u) (C * SC)) := by
    have h := le_mulU (mulU u u) (C * SC)
    rw [m2r_mul_SC'] at h
    linarith [h]
  calc (C : ℝ) * (m2r d + (m2r d) ^ 3 / 12 + 4096 / (SC : ℝ)) ^ 2
      ≤ (C : ℝ) * (m2r u) ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLnn hL 2) hCnn
    _ ≤ (C : ℝ) * m2r (mulU u u) := mul_le_mul_of_nonneg_left hsq hCnn
    _ ≤ m2r (mulU (mulU u u) (C * SC)) := hmul

theorem ChordSpec : (∀ d : ℤ, 0 ≤ Work.ANum.m2r d → 400 * (Work.ANum.m2r d + (Work.ANum.m2r d) ^ 3 / 12 + 4096 / Work.ANum.SC) ^ 2 ≤ Work.ANum.m2r (Work.CNum.chord1 d)) ∧ (∀ d : ℤ, 0 ≤ Work.ANum.m2r d → 1000 * (Work.ANum.m2r d + (Work.ANum.m2r d) ^ 3 / 12 + 4096 / Work.ANum.SC) ^ 2 ≤ Work.ANum.m2r (Work.CNum.chord2 d)) := by
  constructor
  · intro d hd
    exact chord_gen d 400 (by norm_num) hd
  · intro d hd
    exact chord_gen d 1000 (by norm_num) hd

end Work.CNum
