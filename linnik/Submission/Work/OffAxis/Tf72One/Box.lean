/-
# OffAxis/Tf72One/Box

Gluing four certified corner bounds (`Isub_le_cornerB`) into a bound valid on a whole box, using the
two interpolation lemmas `Isub_le_interp_s` (`s`-direction, constant `13/10`) and `Isub_le_interp_t`
(`σ`-direction, constant `5/8`).
-/
import Mathlib
import Submission.Work.OffAxis.Tf72One.Core
import Submission.Work.OffAxis.Tf72One.Isub_le_interp_s
import Submission.Work.OffAxis.Tf72One.Isub_le_interp_t

noncomputable section
namespace Work.OffAxis.Tf72One

open Work.ZeroFreeTables.OffAxis

/-- **Box bound from corner bounds.**  If `Isub` is bounded by `B00, B01, B10, B11` at the four
corners of the box `[s0,s1] × [t0,t1]`, then on the whole box `Isub s t` is bounded by the largest
corner bound plus the two interpolation errors. -/
theorem Isub_le_box (s t s0 s1 t0 t1 B00 B01 B10 B11 : ℝ)
    (hs0 : s0 ≤ s) (hs1 : s ≤ s1) (ht0 : t0 ≤ t) (ht1 : t ≤ t1)
    (h0 : 0 ≤ s0) (h17 : s1 ≤ 17/16)
    (h00 : Isub s0 t0 ≤ B00) (h01 : Isub s0 t1 ≤ B01)
    (h10 : Isub s1 t0 ≤ B10) (h11 : Isub s1 t1 ≤ B11) :
    Isub s t ≤ max (max B00 B01) (max B10 B11)
      + (s1 - s0) ^ 2 / 8 * (13/10) + (t1 - t0) ^ 2 / 8 * (5/8) := by
  have hs1' : 0 ≤ s1 := le_trans h0 (le_trans hs0 hs1)
  have hs017 : s0 ≤ 17/16 := le_trans hs0 (le_trans hs1 h17)
  have hIs := Isub_le_interp_s s t s0 s1 hs0 hs1 h0 h17
  have h0t := Isub_le_interp_t s0 t t0 t1 h0 hs017 ht0 ht1
  have h1t := Isub_le_interp_t s1 t t0 t1 hs1' h17 ht0 ht1
  have hmax0 : max (Isub s0 t0) (Isub s0 t1) ≤ max B00 B01 := max_le_max h00 h01
  have hmax1 : max (Isub s1 t0) (Isub s1 t1) ≤ max B10 B11 := max_le_max h10 h11
  have h0t' : Isub s0 t ≤ max (max B00 B01) (max B10 B11) + (t1 - t0) ^ 2 / 8 * (5/8) := by
    have hle : max B00 B01 ≤ max (max B00 B01) (max B10 B11) := le_max_left _ _
    linarith [h0t, hmax0, hle]
  have h1t' : Isub s1 t ≤ max (max B00 B01) (max B10 B11) + (t1 - t0) ^ 2 / 8 * (5/8) := by
    have hle : max B10 B11 ≤ max (max B00 B01) (max B10 B11) := le_max_right _ _
    linarith [h1t, hmax1, hle]
  have hmax : max (Isub s0 t) (Isub s1 t)
      ≤ max (max B00 B01) (max B10 B11) + (t1 - t0) ^ 2 / 8 * (5/8) := max_le h0t' h1t'
  linarith [hIs, hmax]

end Work.OffAxis.Tf72One
