import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.cosT_bound
import Submission.Work.CNum.CsOfIntervalSound
import Submission.Work.CNum.CosP_tail
import Submission.Work.CNum.SinP_tail
import Submission.Work.CNum.CosP_var
import Submission.Work.CNum.SinP_var
import Submission.Work.CNum.angIv_facts
import Submission.Work.CNum.angIv_gaps

/-!
# `Work.CNum.CsOfSpec`

`csOf m` is the interval evaluation, at the interval `angIv m`, of the degree-11 Taylor partial
sums `cosP · 11`, `sinP · 11` of cosine and sine, with outward rounding.  Here we upgrade the
interval-arithmetic enclosure `CsOfIntervalSound` of those *truncations* to an enclosure of
`Real.cos (mπ/1024)` and `Real.sin (mπ/1024)` themselves, for `m ≤ 255`.

The gap between a truncation and the function it approximates is at most `2/24!`, while the two
Taylor truncations are *strictly monotone* on `[0, π/4]` with variation `≳ 2⁻⁴⁰/4` across the tiny
gap between `mπ/1024` and the endpoints of `angIv m` (`angIv_gaps`).  Comparing the two sides of
each interval there (`CosP_var`, `SinP_var`) therefore absorbs the Taylor remainder with room to
spare: the lower bounds are immediate from the tail signs, and the upper bounds come from the
variation across the gap.
-/

namespace Work.CNum

open Work.CNum Work.ANum

theorem CsOfSpec {m : ℕ} (hm : m ≤ 255) :
    (csOf m).re.Mem (Real.cos ((m : ℝ) * Real.pi / 1024)) ∧
    (csOf m).im.Mem (Real.sin ((m : ℝ) * Real.pi / 1024)) := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    have h0mem : (angIv 0).Mem ((0:ℕ) * Real.pi / 1024) := by
      simpa using angIv_facts.1 0
    have h := CsOfIntervalSound h0mem
    refine ⟨?_, ?_⟩
    · have h1 : (csOf 0).re.Mem 1 := by
        have hh := h.1
        rwa [show ((0:ℕ):ℝ) * Real.pi / 1024 = 0 by norm_num, cosP_zero 11] at hh
      simpa using h1
    · have h2 : (csOf 0).im.Mem 0 := by
        have hh := h.2
        rwa [show ((0:ℕ):ℝ) * Real.pi / 1024 = 0 by norm_num, sinP_zero 11] at hh
      simpa using h2
  · have hm1 : 1 ≤ m := hpos
    set y : ℝ := (m : ℝ) * Real.pi / 1024 with hy
    set a : ℝ := m2r (angIv m).lo with ha
    set b : ℝ := m2r (angIv m).hi with hb
    have hmem : (angIv m).Mem y := angIv_facts.1 m
    have hay : a ≤ y := by rw [ha, hy]; exact hmem.1
    have hyb : y ≤ b := by rw [hb, hy]; exact hmem.2
    have hbnds := angIv_facts.2 m hm
    have ha0 : 0 ≤ a := by rw [ha]; exact hbnds.1
    have hbpi : b ≤ Real.pi / 4 := by rw [hb]; exact hbnds.2
    have hgapL : ((2:ℝ)^40)⁻¹ ≤ y - a := angIv_gaps.1 m hm1
    have hgapR : ((2:ℝ)^41)⁻¹ ≤ b - y := angIv_gaps.2 m hm1
    have hy0 : 0 ≤ y := by rw [hy]; positivity
    have hy3 : (3:ℝ)/1024 ≤ y := by
      have hm1R : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
      have hpi : (3:ℝ) ≤ Real.pi := Real.pi_gt_three.le
      rw [hy]
      nlinarith [hm1R, hpi, Real.pi_pos]
    have hypi : y ≤ Real.pi / 4 := le_trans hyb hbpi
    have hcosP := CsOfIntervalSound hmem
    have hcosPa := CsOfIntervalSound (show (angIv m).Mem a from ⟨le_rfl, le_trans hay hyb⟩)
    have hcosPb := CsOfIntervalSound (show (angIv m).Mem b from ⟨le_trans hay hyb, le_rfl⟩)
    have hcosT := CosP_tail hy0 hypi
    have hsinT := SinP_tail hy0 hypi
    have hcosVar := CosP_var ha0 hay hypi
    have hsinVar := SinP_var hy0 hyb hbpi
    have hnum1 : 4 * ((Nat.factorial 24 : ℝ))⁻¹ ≤ (3/1024) * ((2:ℝ)^40)⁻¹ / 8 := by
      norm_num [Nat.factorial]
    have hnum2 : 4 * ((Nat.factorial 25 : ℝ))⁻¹ ≤ ((2:ℝ)^41)⁻¹ / 4 := by
      norm_num [Nat.factorial]
    constructor
    · -- re
      constructor
      · exact le_trans hcosP.1.1 hcosT.1
      · have hkey : 4 * ((Nat.factorial 24 : ℝ))⁻¹ ≤ (a + y) * (y - a) / 8 := by
          have h1 : (3/1024 : ℝ) * ((2:ℝ)^40)⁻¹ / 8 ≤ (a + y) * (y - a) / 8 := by
            have h2 : (3/1024 : ℝ) * ((2:ℝ)^40)⁻¹ ≤ (a + y) * (y - a) := by
              nlinarith [ha0, hy3, hgapL]
            linarith
          linarith [hnum1, h1]
        linarith [hcosT.2, hcosVar, hcosPa.1.2, hkey]
    · -- im
      constructor
      · exact le_trans hcosP.2.1 hsinT.1
      · have hkey : 4 * ((Nat.factorial 25 : ℝ))⁻¹ ≤ (b - y) / 4 := by
          have h2 : ((2:ℝ)^41)⁻¹ / 4 ≤ (b - y) / 4 := by linarith
          linarith [hnum2, h2]
        linarith [hsinT.2, hsinVar, hcosPb.2.2, hkey]

end Work.CNum
