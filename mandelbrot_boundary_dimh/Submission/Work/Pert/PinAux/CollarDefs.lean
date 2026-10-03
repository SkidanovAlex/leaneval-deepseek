import Mathlib
import Submission.Work.Pert.PinAux.Basic

/-!
# `Work.Pert.PinAux.CollarDefs`

The two geometric quantities of the "collar to medial" argument, and the elementary facts
about them.

* `minmarg Ξ α z = min (margA Ξ α z) (margB Ξ α z)` — the smaller of the two linear gate
  margins.  `z ∈ Qm Ξ α ↔ 0 < minmarg Ξ α z`.
* `clear Ξ α z = minmarg Ξ α z / √2` — the corresponding *radius*: the ball
  `ball z (minmarg Ξ α z / √2)` lies in the gate (`ball_subset_Qm_of_marg_le`).

The medial point `med Ξ α t` of the slice at height `t` is the midpoint of the gate slice; both
its margins equal `width Ξ α t / 2`.

Along a *horizontal* segment at height `t = z.im` from `z` to `med Ξ α z.im` the smaller margin
is affine: it equals `minmarg Ξ α z` at `z` and `width Ξ α t / 2` at the medial point
(`minmarg_seg_le` / `minmarg_seg_ge`).
-/

namespace Work.Pert.PinAux

open MandelDim Complex Metric

noncomputable section

/-- The smaller of the two gate margins. -/
def minmarg (Ξ : ℝ) (α z : ℂ) : ℝ := min (margA Ξ α z) (margB Ξ α z)

/-- The clearance radius of a point of the gate. -/
def clear (Ξ : ℝ) (α z : ℂ) : ℝ := minmarg Ξ α z / Real.sqrt 2

lemma minmarg_def (Ξ : ℝ) (α z : ℂ) :
    minmarg Ξ α z = min (margA Ξ α z) (margB Ξ α z) := rfl

lemma clear_def (Ξ : ℝ) (α z : ℂ) :
    clear Ξ α z = minmarg Ξ α z / Real.sqrt 2 := rfl

lemma minmarg_le_margA (Ξ : ℝ) (α z : ℂ) : minmarg Ξ α z ≤ margA Ξ α z :=
  min_le_left _ _

lemma minmarg_le_margB (Ξ : ℝ) (α z : ℂ) : minmarg Ξ α z ≤ margB Ξ α z :=
  min_le_right _ _

lemma mem_Qm_iff_minmarg_pos {Ξ : ℝ} {α z : ℂ} :
    z ∈ Qm Ξ α ↔ 0 < minmarg Ξ α z := by
  rw [mem_Qm_iff_marg]
  simp only [minmarg]
  constructor
  · rintro ⟨h1, h2⟩; exact lt_min h1 h2
  · intro h; exact ⟨lt_of_lt_of_le h (min_le_left _ _), lt_of_lt_of_le h (min_le_right _ _)⟩

lemma minmarg_pos_of_mem {Ξ : ℝ} {α z : ℂ} (hz : z ∈ Qm Ξ α) : 0 < minmarg Ξ α z :=
  mem_Qm_iff_minmarg_pos.mp hz

/-- The ball of radius `minmarg / √2` centred at `z` lies in the gate. -/
lemma ball_subset_Qm_of_minmarg {Ξ : ℝ} {α z : ℂ} (h : 0 ≤ minmarg Ξ α z) :
    Metric.ball z (minmarg Ξ α z / Real.sqrt 2) ⊆ Qm Ξ α := by
  refine ball_subset_Qm_of_marg_le (α := α) (ξ := Ξ) (z := z)
    (R := minmarg Ξ α z / Real.sqrt 2) (by positivity) ?_
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hs)]
  exact minmarg_def Ξ α z ▸ le_rfl

lemma minmarg_med (Ξ : ℝ) (α : ℂ) (t : ℝ) :
    minmarg Ξ α (med Ξ α t) = width Ξ α t / 2 := by
  simp only [minmarg, margA_med, margB_med, min_self]

/-- The difference of the two margins of a point is twice its signed distance (in `x`) from the
medial axis of its slice. -/
lemma margB_sub_margA (Ξ : ℝ) (α : ℂ) (z : ℂ) :
    margB Ξ α z - margA Ξ α z = 2 * ((med Ξ α z.im).re - z.re) := by
  have h1 : margB Ξ α z = sliceHi Ξ z.im - z.re := margB_eq_sliceHi_sub Ξ α z
  have h2 : margA Ξ α z = z.re - sliceLo Ξ α z.im := margA_eq_sub_sliceLo Ξ α z
  have h3 : (med Ξ α z.im).re = (sliceLo Ξ α z.im + sliceHi Ξ z.im) / 2 := by
    rw [med_re, xMid]
  rw [h1, h2, h3]; ring

lemma med_re_eq_xMid (Ξ : ℝ) (α : ℂ) (t : ℝ) : (med Ξ α t).re = xMid Ξ α t := med_re Ξ α t

lemma med_im_eq (Ξ : ℝ) (α : ℂ) (t : ℝ) : (med Ξ α t).im = t := med_im Ξ α t

/-- The segment point `z + t • (med Ξ α z.im - z)` has the same height as `z`. -/
lemma seg_med_im (Ξ : ℝ) (α : ℂ) (z : ℂ) (t : ℝ) :
    (z + t • (med Ξ α z.im - z)).im = z.im := by
  simp [Complex.add_im, Complex.sub_im, med_im]

lemma seg_med_re (Ξ : ℝ) (α : ℂ) (z : ℂ) (t : ℝ) :
    (z + t • (med Ξ α z.im - z)).re = z.re + t * ((med Ξ α z.im).re - z.re) := by
  simp [Complex.add_re, Complex.sub_re, med_re]

/-- The margin `A` along the horizontal segment from `z` to the medial point of its slice. -/
lemma margA_seg_med (Ξ : ℝ) (α : ℂ) (z : ℂ) (t : ℝ) :
    margA Ξ α (z + t • (med Ξ α z.im - z))
      = margA Ξ α z + t * ((med Ξ α z.im).re - z.re) := by
  rw [margA_eq_sub_sliceLo Ξ α (z + t • (med Ξ α z.im - z)), margA_eq_sub_sliceLo Ξ α z,
    seg_med_re, seg_med_im]
  ring

/-- The margin `B` along the same segment. -/
lemma margB_seg_med (Ξ : ℝ) (α : ℂ) (z : ℂ) (t : ℝ) :
    margB Ξ α (z + t • (med Ξ α z.im - z))
      = margB Ξ α z - t * ((med Ξ α z.im).re - z.re) := by
  rw [margB_eq_sliceHi_sub Ξ α (z + t • (med Ξ α z.im - z)), margB_eq_sliceHi_sub Ξ α z,
    seg_med_re, seg_med_im]
  ring

/-- Along the horizontal segment from `z` to the medial point of its slice, the smaller margin is
affine with slope `Δ = (med Ξ α z.im).re - z.re ≥ 0`. -/
lemma minmarg_seg_le {Ξ : ℝ} {α : ℂ} {z : ℂ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (h : z.re ≤ (med Ξ α z.im).re) :
    minmarg Ξ α (z + t • (med Ξ α z.im - z))
      = minmarg Ξ α z + t * ((med Ξ α z.im).re - z.re) := by
  have hA := margA_seg_med Ξ α z t
  have hB := margB_seg_med Ξ α z t
  have hz_le : margA Ξ α z ≤ margB Ξ α z := by
    have hz := margB_sub_margA Ξ α z
    linarith [hz, h]
  have hD : (0 : ℝ) ≤ t * ((med Ξ α z.im).re - z.re) :=
    mul_nonneg ht.1 (sub_nonneg.mpr h)
  have hcross : margA Ξ α (z + t • (med Ξ α z.im - z))
      ≤ margB Ξ α (z + t • (med Ξ α z.im - z)) := by
    have hm := margB_sub_margA Ξ α z
    have hΔ : (0 : ℝ) ≤ (med Ξ α z.im).re - z.re := sub_nonneg.mpr h
    have htΔ : t * ((med Ξ α z.im).re - z.re) ≤ (med Ξ α z.im).re - z.re := by
      calc t * ((med Ξ α z.im).re - z.re) ≤ 1 * ((med Ξ α z.im).re - z.re) :=
            mul_le_mul_of_nonneg_right ht.2 hΔ
        _ = (med Ξ α z.im).re - z.re := one_mul _
    rw [hA, hB]; linarith [hm, htΔ]
  rw [minmarg, min_eq_left hcross, minmarg, min_eq_left hz_le]
  exact hA

/-- The same in the case `med.re ≤ z.re`, with slope `z.re - med.re ≥ 0`. -/
lemma minmarg_seg_ge {Ξ : ℝ} {α : ℂ} {z : ℂ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (h : (med Ξ α z.im).re ≤ z.re) :
    minmarg Ξ α (z + t • (med Ξ α z.im - z))
      = minmarg Ξ α z + t * (z.re - (med Ξ α z.im).re) := by
  have hA := margA_seg_med Ξ α z t
  have hB := margB_seg_med Ξ α z t
  have hz_le : margB Ξ α z ≤ margA Ξ α z := by
    have hz := margB_sub_margA Ξ α z
    linarith [hz, h]
  have hD : (0 : ℝ) ≤ t * (z.re - (med Ξ α z.im).re) :=
    mul_nonneg ht.1 (sub_nonneg.mpr h)
  have hcross : margB Ξ α (z + t • (med Ξ α z.im - z))
      ≤ margA Ξ α (z + t • (med Ξ α z.im - z)) := by
    have hm := margB_sub_margA Ξ α z
    have hΔ : (0 : ℝ) ≤ z.re - (med Ξ α z.im).re := sub_nonneg.mpr h
    have htΔ : t * (z.re - (med Ξ α z.im).re) ≤ z.re - (med Ξ α z.im).re := by
      calc t * (z.re - (med Ξ α z.im).re) ≤ 1 * (z.re - (med Ξ α z.im).re) :=
            mul_le_mul_of_nonneg_right ht.2 hΔ
        _ = z.re - (med Ξ α z.im).re := one_mul _
    rw [hA, hB]; linarith [hm, htΔ]
  rw [minmarg, min_eq_right hcross, minmarg, min_eq_right hz_le]
  rw [hB]; ring

/-- The smaller margin along the segment is at least its value at `z`. -/
lemma minmarg_seg_ge_minmarg {Ξ : ℝ} {α : ℂ} {z : ℂ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    minmarg Ξ α z ≤ minmarg Ξ α (z + t • (med Ξ α z.im - z)) := by
  rcases le_total z.re ((med Ξ α z.im).re) with h | h
  · rw [minmarg_seg_le ht h]
    nlinarith [ht.1, sub_nonneg.mpr h]
  · rw [minmarg_seg_ge ht h]
    nlinarith [ht.1, sub_nonneg.mpr h]

/-- The gate is at distance `Ξ/2` from the origin. -/
lemma norm_ge_half_of_mem {Ξ : ℝ} {α z : ℂ} (hΞ : 0 < Ξ) (hz : z ∈ Work.Pert.Qm Ξ α) :
    Ξ / 2 ≤ ‖z‖ := by
  have hmB : 0 < margB Ξ α z := (Work.Pert.mem_Qm_iff_marg Ξ α z).mp hz |>.2
  have hmB' : 0 < |z.im| - Ξ - z.re := by simpa [Work.Pert.margB] using hmB
  have h1 : Ξ < |z.im| + |z.re| := by
    have h2 : |z.re| ≥ -z.re := neg_le_abs z.re
    have h3 : |z.im| ≥ z.im := le_abs_self z.im
    linarith [hmB']
  have h2 : |z.re| + |z.im| ≤ Real.sqrt 2 * ‖z‖ := Work.Pert.sqrt2_norm z
  have hs : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 2)]; norm_num
  have hn : 0 < ‖z‖ := by
    by_contra h
    push Not at h
    have : ‖z‖ = 0 := le_antisymm h (norm_nonneg z)
    rw [this, mul_zero] at h2
    linarith [h1, h2]
  have h3 : Real.sqrt 2 * ‖z‖ < 2 * ‖z‖ := mul_lt_mul_of_pos_right hs hn
  linarith

/-- The real part of the medial point of the slice at height `t`. -/
lemma xMid_abs_le (Ξ : ℝ) (α : ℂ) (t : ℝ) :
    |xMid Ξ α t| ≤ |t| + (|(1 / α).re| + |(1 / α).im| + 2 * |Ξ|) / 2 := by
  have h : xMid Ξ α t = (|t| - |t + (1 / α).im| - (1 / α).re) / 2 := by
    rw [xMid, Work.Pert.sliceLo, Work.Pert.sliceHi]; ring
  have hnum : |(|t| - |t + (1 / α).im| - (1 / α).re)|
      ≤ |t| + |t + (1 / α).im| + |(1 / α).re| := by
    have h1 : |t| - |t + (1 / α).im| - (1 / α).re
        = (|t| - |t + (1 / α).im|) - (1 / α).re := by ring
    rw [h1]
    calc |(|t| - |t + (1 / α).im|) - (1 / α).re|
        ≤ |(|t| - |t + (1 / α).im|)| + |(1 / α).re| := abs_sub _ _
      _ ≤ (|t| + |t + (1 / α).im|) + |(1 / α).re| := by
          have hstep : |(|t| - |t + (1 / α).im|)| ≤ |t| + |t + (1 / α).im| := by
            have hX : (0:ℝ) ≤ |t + (1 / α).im| := abs_nonneg _
            have ht : (0:ℝ) ≤ |t| := abs_nonneg _
            rcases le_total |t| |t + (1 / α).im| with hc | hc
            · rw [abs_of_nonpos (by linarith)]
              linarith
            · rw [abs_of_nonneg (by linarith)]
              linarith
          linarith
      _ = |t| + |t + (1 / α).im| + |(1 / α).re| := by ring
  have htri : |t + (1 / α).im| ≤ |t| + |(1 / α).im| := abs_add_le _ _
  have hmain : 2 * |xMid Ξ α t| ≤ 2 * |t| + |(1 / α).im| + |(1 / α).re| := by
    rw [h, abs_div, Nat.abs_ofNat]
    linarith [hnum, htri]
  have hfin : 2 * |t| + |(1 / α).im| + |(1 / α).re|
      ≤ 2 * |t| + (|(1 / α).re| + |(1 / α).im| + 2 * |Ξ|) := by
    linarith [abs_nonneg Ξ]
  linarith [hmain, hfin]

/-- `width / 2` is at most `|t|` plus a constant. -/
lemma width_le (Ξ : ℝ) (α : ℂ) (t : ℝ) (hΞ : 0 ≤ Ξ) :
    width Ξ α t / 2 ≤ |t| + (|(1 / α).re| + 2 * Ξ + |(1 / α).im|) / 2 := by
  have h := Work.Pert.PinAux.width_div_two_le Ξ α t
  have h2 : (1 / α).re - 2 * Ξ ≤ |(1 / α).re| + 2 * Ξ := by
    have h3 := le_abs_self ((1 / α).re)
    linarith
  have h3 : ((1 / α).re - 2 * Ξ + |(1 / α).im|) / 2
      ≤ (|(1 / α).re| + 2 * Ξ + |(1 / α).im|) / 2 :=
    div_le_div_of_nonneg_right (by linarith) (by norm_num)
  linarith [h, h3]

/-- The min margin is affine along the horizontal line at height `z.im`, on the `z`-side. -/
lemma minmarg_affine_le {Ξ : ℝ} {α : ℂ} {z : ℂ} {x : ℝ}
    (h : z.re ≤ (med Ξ α z.im).re) (hx : x ∈ Set.Icc z.re (med Ξ α z.im).re) :
    minmarg Ξ α (x + z.im * Complex.I) = minmarg Ξ α z + (x - z.re) := by
  have hy : (x + z.im * Complex.I).im = z.im := by simp
  have hxr : (x + z.im * Complex.I).re = x := by simp
  have hA : margA Ξ α (x + z.im * Complex.I) = margA Ξ α z + (x - z.re) := by
    rw [margA_eq_sub_sliceLo Ξ α (x + z.im * Complex.I), margA_eq_sub_sliceLo Ξ α z, hy, hxr]
    ring
  have hm : margB Ξ α (x + z.im * Complex.I) - margA Ξ α (x + z.im * Complex.I)
      = 2 * ((med Ξ α z.im).re - x) := by
    have h1 : margB Ξ α (x + z.im * Complex.I) = sliceHi Ξ z.im - x := by
      rw [margB_eq_sliceHi_sub Ξ α (x + z.im * Complex.I), hy, hxr]
    have h2 : margA Ξ α (x + z.im * Complex.I) = x - sliceLo Ξ α z.im := by
      rw [margA_eq_sub_sliceLo Ξ α (x + z.im * Complex.I), hy, hxr]
    have h3 : (med Ξ α z.im).re = (sliceLo Ξ α z.im + sliceHi Ξ z.im) / 2 := by
      rw [med_re, xMid]
    rw [h1, h2, h3]; ring
  have hz_le : margA Ξ α z ≤ margB Ξ α z := by
    have hz := margB_sub_margA Ξ α z
    linarith [hz, h]
  have hcross : margA Ξ α (x + z.im * Complex.I) ≤ margB Ξ α (x + z.im * Complex.I) := by
    linarith [hm, hx.2]
  rw [minmarg, min_eq_left hcross, minmarg, min_eq_left hz_le]
  exact hA

/-- The min margin is affine along the horizontal line at height `z.im`, on the `med`-side. -/
lemma minmarg_affine_ge {Ξ : ℝ} {α : ℂ} {z : ℂ} {x : ℝ}
    (h : (med Ξ α z.im).re ≤ z.re) (hx : x ∈ Set.Icc (med Ξ α z.im).re z.re) :
    minmarg Ξ α (x + z.im * Complex.I) = minmarg Ξ α z + (z.re - x) := by
  have hy : (x + z.im * Complex.I).im = z.im := by simp
  have hxr : (x + z.im * Complex.I).re = x := by simp
  have hA : margA Ξ α (x + z.im * Complex.I) = margA Ξ α z + (x - z.re) := by
    rw [margA_eq_sub_sliceLo Ξ α (x + z.im * Complex.I), margA_eq_sub_sliceLo Ξ α z, hy, hxr]
    ring
  have hB : margB Ξ α (x + z.im * Complex.I) = margB Ξ α z - (x - z.re) := by
    rw [margB_eq_sliceHi_sub Ξ α (x + z.im * Complex.I), margB_eq_sliceHi_sub Ξ α z, hy, hxr]
    ring
  have hm : margB Ξ α z - margA Ξ α z = 2 * ((med Ξ α z.im).re - z.re) := margB_sub_margA Ξ α z
  have hz_le : margB Ξ α z ≤ margA Ξ α z := by linarith [hm, h]
  have hcross : margB Ξ α (x + z.im * Complex.I) ≤ margA Ξ α (x + z.im * Complex.I) := by
    rw [hA, hB]; linarith [hm, hx.1]
  rw [minmarg, min_eq_right hcross, minmarg, min_eq_right hz_le]
  linarith [hB]

/-- The min margin is at least its value at `z` along the whole horizontal segment. -/
lemma minmarg_on_seg {Ξ : ℝ} {α : ℂ} {z : ℂ} {x : ℝ}
    (hx : x ∈ Set.Icc (min z.re (med Ξ α z.im).re) (max z.re (med Ξ α z.im).re)) :
    minmarg Ξ α z ≤ minmarg Ξ α (x + z.im * Complex.I) := by
  rcases le_total z.re ((med Ξ α z.im).re) with h | h
  · have hx' : x ∈ Set.Icc z.re (med Ξ α z.im).re := by
      constructor
      · rw [min_eq_left h] at hx; exact hx.1
      · rw [max_eq_right h] at hx; exact hx.2
    rw [minmarg_affine_le h hx']; linarith [hx'.1]
  · have hx' : x ∈ Set.Icc (med Ξ α z.im).re z.re := by
      constructor
      · rw [min_eq_right h] at hx; exact hx.1
      · rw [max_eq_left h] at hx; exact hx.2
    rw [minmarg_affine_ge h hx']; linarith [hx'.2]


end

end Work.Pert.PinAux
