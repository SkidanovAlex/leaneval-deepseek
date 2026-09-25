/-
# Dilation invariance of the (lattice) Hardy--Littlewood maximal function

The lattice maximal function `mstHlMax` of this development is the ordinary centred
Hardy--Littlewood maximal function on `ℝ` (`Commons.Analysis.Maximal.hlMax`), i.e.

`mstHlMax g x = ⨆ (a b : ℝ) (_ : a ≤ x ∧ x ≤ b), (b - a)⁻¹ ∫_a^b g`.

The map `y ↦ c·y + m` with `c > 0` sends intervals containing `t` bijectively onto intervals
containing `c·t + m`, changing the length by the factor `c` exactly as the Jacobian `c`
demands; hence the maximal averages of `y ↦ g (c·y + m)` at `t` are the maximal averages of `g`
at `c·t + m`.  This is the affine invariance used to move between a lattice (sampling) variable
and the dilated real variable, e.g. in `latDiscMax_lintegral_rpow_le` and its relatives.

Contents:

* `image_affine_Icc` — the affine image of a closed interval;
* `lintegral_Icc_affine` — the affine change of variables for the *normalized* interval average
  `(b - a)⁻¹ ∫_a^b g (c·y + m)`, which is the exact form consumed by the maximal function;
* `latHlMax_dilate` — the target statement.
-/

import Mathlib
import Submission.Work.Maximal.mstWide_defs

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped ENNReal

/-- The image of a closed interval under the increasing affine map `y ↦ c * y + m` (`c > 0`):
`(c · + m) '' [a, b] = [c * a + m, c * b + m]`. -/
lemma image_affine_Icc {c m a b : ℝ} (hc : 0 < c) :
    (fun y : ℝ => c * y + m) '' Set.Icc a b = Set.Icc (c * a + m) (c * b + m) := by
  ext u
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨by nlinarith [hy.1], by nlinarith [hy.2]⟩
  · intro hu
    refine ⟨(u - m) / c, ⟨?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ hc]
      nlinarith [hu.1]
    · rw [div_le_iff₀ hc]
      nlinarith [hu.2]
    · show c * ((u - m) / c) + m = u
      rw [mul_div_cancel₀ _ (ne_of_gt hc)]
      ring

/-- **Affine change of variables for the normalized interval average.**  For `c > 0` and `a ≤ b`,

`(b - a)⁻¹ ∫_a^b g (c·y + m) dy = ((c·b + m) - (c·a + m))⁻¹ ∫_{c·a+m}^{c·b+m} g u du`,

i.e. the affine substitution `u = c·y + m` leaves the *average* of `g` unchanged (the Jacobian
factor `c` is exactly compensated by the change of the length of the interval). -/
lemma lintegral_Icc_affine (g : ℝ → ℝ≥0∞) {c m : ℝ} (hc : 0 < c) {a b : ℝ} (hab : a ≤ b) :
    ENNReal.ofReal (b - a)⁻¹ * ∫⁻ y in Set.Icc a b, g (c * y + m)
      = ENNReal.ofReal ((c * b + m) - (c * a + m))⁻¹
          * ∫⁻ u in Set.Icc (c * a + m) (c * b + m), g u := by
  have hs : MeasurableSet (Set.Icc a b) := measurableSet_Icc
  have hderiv : ∀ y ∈ Set.Icc a b,
      HasDerivWithinAt (fun z : ℝ => c * z + m) c (Set.Icc a b) y := by
    intro y _
    have h : HasDerivAt (fun z : ℝ => c * z + m) c y := by
      simpa using ((hasDerivAt_id y).const_mul c).add_const m
    exact h.hasDerivWithinAt
  have hinj : Set.InjOn (fun z : ℝ => c * z + m) (Set.Icc a b) := by
    intro p _ q _ hpq
    have hcpq : c * p = c * q := by linarith
    exact mul_left_cancel₀ (ne_of_gt hc) hcpq
  have himage := image_affine_Icc (c := c) (m := m) (a := a) (b := b) hc
  have h := lintegral_image_eq_lintegral_abs_deriv_mul hs hderiv hinj g
  rw [himage, abs_of_pos hc] at h
  -- `h : ∫⁻ u in [c a + m, c b + m], g u = ∫⁻ y in [a,b], ofReal c * g (c * y + m)`
  have hcancel : (c * (b - a))⁻¹ * c = (b - a)⁻¹ := by
    rw [mul_inv]
    calc c⁻¹ * (b - a)⁻¹ * c = c⁻¹ * (c * (b - a)⁻¹) := by ring
      _ = (b - a)⁻¹ := inv_mul_cancel_left₀ (ne_of_gt hc) _
  have hBA : ENNReal.ofReal ((c * b + m) - (c * a + m))⁻¹ * ENNReal.ofReal c
      = ENNReal.ofReal (b - a)⁻¹ := by
    have h1 : c * b + m - (c * a + m) = c * (b - a) := by ring
    rw [h1, ← ENNReal.ofReal_mul
      (inv_nonneg.mpr (mul_nonneg hc.le (sub_nonneg.mpr hab))), hcancel]
  rw [h, lintegral_const_mul' (ENNReal.ofReal c) _ ENNReal.ofReal_ne_top, ← hBA, mul_assoc]

/-- **Dilation invariance of the lattice Hardy--Littlewood maximal function.**  For `c > 0`,

`mstHlMax (fun y => g (c * y + m)) t = mstHlMax g (c * t + m)`.

Both are maximal functions of the same function read on the same scale: the affine map
`y ↦ c * y + m` is a bijection of the interval systems preserving normalized averages. -/
theorem latHlMax_dilate (g : ℝ → ENNReal) {c : ℝ} (hc : 0 < c) (m t : ℝ) :
    Work.Maximal.mstHlMax (fun y : ℝ => g (c * y + m)) t = Work.Maximal.mstHlMax g (c * t + m) := by
  rw [Work.Maximal.mstHlMax_apply, Work.Maximal.mstHlMax_apply]
  refine le_antisymm ?_ ?_
  · rw [Commons.Analysis.Maximal.hlMax]
    refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    rw [lintegral_Icc_affine g hc (a := a) (b := b) (le_trans hab.1 hab.2)]
    refine Commons.Analysis.Maximal.hlMax_le_of_mem g ?_ ?_
    · have h1 : c * a ≤ c * t := mul_le_mul_of_nonneg_left hab.1 hc.le
      linarith
    · have h2 : c * t ≤ c * b := mul_le_mul_of_nonneg_left hab.2 hc.le
      linarith
  · rw [Commons.Analysis.Maximal.hlMax]
    refine iSup_le fun A => iSup_le fun B => iSup_le fun hab => ?_
    have hA : c * ((A - m) / c) + m = A := by
      rw [mul_div_cancel₀ _ (ne_of_gt hc)]; ring
    have hB : c * ((B - m) / c) + m = B := by
      rw [mul_div_cancel₀ _ (ne_of_gt hc)]; ring
    have hab' : (A - m) / c ≤ (B - m) / c := by
      rw [div_le_div_iff_of_pos_right hc]; linarith [hab.1, hab.2]
    have hta : (A - m) / c ≤ t := by
      rw [div_le_iff₀ hc]; linarith [hab.1]
    have htb : t ≤ (B - m) / c := by
      rw [le_div_iff₀ hc]; linarith [hab.2]
    have hh := lintegral_Icc_affine g hc (m := m) (a := (A - m) / c) (b := (B - m) / c) hab'
    rw [hA, hB] at hh
    rw [← hh]
    exact Commons.Analysis.Maximal.hlMax_le_of_mem (fun y : ℝ => g (c * y + m)) hta htb

end Work.BourgainPlan.Maximal
