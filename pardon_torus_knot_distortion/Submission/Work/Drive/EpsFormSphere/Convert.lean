import Mathlib
import Submission.Work.Drive.EpsFormSphere.Defs
import Submission.Work.BoxShrink.counting

/-!
# The ε-margin of the crux: from a thickened half-loop to a smaller box

The missing parameter in the residual `Work.Drive.EpsSphere.PinchEps` is an arbitrary `ε > 0`, while
the box-shrinking step needs an essential loop of the *half* of the box, so that the halving
geometry of `Work.BoxShrink.halving` applies.  This module spends the (strict) ε-margin of the crux
— `s < (1 + eps) * r` and `|u| < eps * r` — to bridge the two:

* `keeps`: an essential loop within distance `ε` of a half-region lies in `PBox (s + ε) c σ` (the
  box norm is `1`-Lipschitz in the coordinate directions) on the correct side of the shifted plane;
* `halfBox_spec` / `halfBox_spec'`: the half-box of `PBox (s + ε)` with the shifted plane
  `c (σ 2) + (u ± ε)` fits in a box of size `shrinkFactor * r`, as soon as `8 ε ≤` the margin
  `shrinkFactor * r - (b * s + |u| / 2)`, which is positive by the two strict inequalities;
* `hasEssBox_of_thickHalf`: **the conversion**, from the ε-form conclusion to `HasEssBox` at the
  shrunk radius.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal
open Metric

namespace Work.Drive.EpsSphere

noncomputable section

/-- A point close to a point of the box `PBox s c σ` lies in `PBox (s + ε) c σ`. -/
theorem mem_PBox_add_of_norm_sub_lt {s ε : ℝ} (hε : 0 ≤ ε) {c : R3}
    {σ : Equiv.Perm (Fin 3)} {x y : R3} (hx : x ∈ Submission.PBox s c σ)
    (hxy : ‖y - x‖ < ε) : y ∈ Submission.PBox (s + ε) c σ := by
  intro i
  have h1 : |y (σ i) - x (σ i)| ≤ ‖y - x‖ := by
    have h2 := PiLp.norm_apply_le (p := 2) (β := fun _ : Fin 3 => ℝ) (y - x) (σ i)
    simpa using h2
  have h1' : |y (σ i) - x (σ i)| < ε := lt_of_le_of_lt h1 hxy
  have h4 : |x (σ i) - c (σ i)| < Submission.boxSide i * s := hx i
  have h5 : (1 : ℝ) ≤ Submission.boxSide i := Submission.one_le_boxSide i
  calc |y (σ i) - c (σ i)| ≤ |y (σ i) - x (σ i)| + |x (σ i) - c (σ i)| := abs_sub_le _ _ _
    _ < ε + Submission.boxSide i * s := by linarith
    _ ≤ Submission.boxSide i * ε + Submission.boxSide i * s := by nlinarith [hε, h5]
    _ = Submission.boxSide i * (s + ε) := by ring

/-- **The ε-margin of the crux.**  The quantity
`shrinkFactor * r - (b * s + |u| / 2)` is positive: this is exactly the slack of Pardon's
`(1+ε)`-arithmetic, and it is strict because `s < (1+eps) * r` and `|u| < eps * r` are. -/
theorem margin_pos {r s u : ℝ} (hr : 0 < r) (hrs : r < s)
    (hs : s < (1 + Submission.eps) * r) (hu : |u| < Submission.eps * r) :
    0 < Submission.shrinkFactor * r - (Submission.b * s + |u| / 2) := by
  have hb : 0 < Submission.b := Submission.b_pos
  have h1 : Submission.b * s < Submission.b * ((1 + Submission.eps) * r) := by nlinarith
  have h2 : |u| / 2 < Submission.eps * r / 2 := by linarith
  have h3 : Submission.b * ((1 + Submission.eps) * r) + Submission.eps * r / 2 =
      Submission.shrinkFactor * r := by
    rw [Submission.shrinkFactor, Submission.eps, Submission.b]; ring
  linarith

/-- The numeric slack used in the conversion: `ε` with `8 ε ≤ margin` is admissible. -/
theorem halfBox_spec {r s u ε : ℝ} (hε : 0 ≤ ε)
    (hε8 : 8 * ε ≤ Submission.shrinkFactor * r - (Submission.b * s + |u| / 2)) :
    Submission.b * (s + ε) + |u + ε| / 2 ≤ Submission.shrinkFactor * r := by
  have hb : Submission.b + 1 / 2 ≤ 8 := by
    have := Submission.b_lt_four_fifths
    linarith
  have h1 : |u + ε| ≤ |u| + ε := by
    have h := abs_add_le u ε
    rwa [abs_of_nonneg hε] at h
  have h2 : Submission.b * (s + ε) + |u + ε| / 2
      ≤ (Submission.b * s + |u| / 2) + ε * (Submission.b + 1 / 2) := by
    nlinarith [h1, hε]
  have h3 : ε * (Submission.b + 1 / 2) ≤ 8 * ε := by nlinarith [hε, hb]
  linarith

/-- The same size bound on the other side of the plane. -/
theorem halfBox_spec' {r s u ε : ℝ} (hε : 0 ≤ ε)
    (hε8 : 8 * ε ≤ Submission.shrinkFactor * r - (Submission.b * s + |u| / 2)) :
    Submission.b * (s + ε) + |u - ε| / 2 ≤ Submission.shrinkFactor * r := by
  have hb : Submission.b + 1 / 2 ≤ 8 := by
    have := Submission.b_lt_four_fifths
    linarith
  have h1 : |u - ε| ≤ |u| + ε := by
    have h := abs_add_le u (-ε)
    rw [abs_neg, abs_of_nonneg hε] at h
    simpa [sub_eq_add_neg] using h
  have h2 : Submission.b * (s + ε) + |u - ε| / 2
      ≤ (Submission.b * s + |u| / 2) + ε * (Submission.b + 1 / 2) := by
    nlinarith [h1, hε]
  have h3 : ε * (Submission.b + 1 / 2) ≤ 8 * ε := by nlinarith [hε, hb]
  linarith

/-- The shifted plane is still transverse to the box of size `s + ε` in the `σ 2` direction. -/
theorem abs_add_lt_boxSide_two_mul {r s u ε : ℝ} (hr : 0 < r) (hrs : r < s)
    (hu : |u| < Submission.eps * r) (hε : 0 ≤ ε) :
    |u + ε| < Submission.boxSide 2 * (s + ε) := by
  have hb2 : Submission.eps ≤ Submission.boxSide 2 := by
    rw [Submission.boxSide_two, Submission.eps]
    linarith [Submission.one_le_rpow_two_thirds]
  have hb1 : (1 : ℝ) ≤ Submission.boxSide 2 := by
    rw [Submission.boxSide_two]; exact Submission.one_le_rpow_two_thirds
  have h1 : |u + ε| ≤ |u| + ε := by
    have h := abs_add_le u ε
    rwa [abs_of_nonneg hε] at h
  have hs0 : 0 ≤ s := le_of_lt (lt_trans hr hrs)
  have h3 : Submission.eps * r ≤ Submission.eps * s :=
    mul_le_mul_of_nonneg_left (le_of_lt hrs) (le_of_lt Submission.eps_pos)
  have h4 : ε ≤ Submission.boxSide 2 * ε := le_mul_of_one_le_left hε hb1
  have h5 : Submission.eps * s ≤ Submission.boxSide 2 * s := mul_le_mul_of_nonneg_right hb2 hs0
  linarith

/-- The same on the other side. -/
theorem abs_sub_lt_boxSide_two_mul {r s u ε : ℝ} (hr : 0 < r) (hrs : r < s)
    (hu : |u| < Submission.eps * r) (hε : 0 ≤ ε) :
    |u - ε| < Submission.boxSide 2 * (s + ε) := by
  have hb2 : Submission.eps ≤ Submission.boxSide 2 := by
    rw [Submission.boxSide_two, Submission.eps]
    linarith [Submission.one_le_rpow_two_thirds]
  have hb1 : (1 : ℝ) ≤ Submission.boxSide 2 := by
    rw [Submission.boxSide_two]; exact Submission.one_le_rpow_two_thirds
  have h1 : |u - ε| ≤ |u| + ε := by
    have h := abs_add_le u (-ε)
    rw [abs_neg, abs_of_nonneg hε] at h
    simpa [sub_eq_add_neg] using h
  have hs0 : 0 ≤ s := le_of_lt (lt_trans hr hrs)
  have h3 : Submission.eps * r ≤ Submission.eps * s :=
    mul_le_mul_of_nonneg_left (le_of_lt hrs) (le_of_lt Submission.eps_pos)
  have h4 : ε ≤ Submission.boxSide 2 * ε := le_mul_of_one_le_left hε hb1
  have h5 : Submission.eps * s ≤ Submission.boxSide 2 * s := mul_le_mul_of_nonneg_right hb2 hs0
  linarith

/-- **The conversion.**  If an essential loop of the surface lies within distance `ε` of one of the
two half-regions of `PBox s c σ` cut out by the plane `{y (σ 2) = c (σ 2) + u}`, then a box of size
`shrinkFactor * r` meets the surface in an essential loop. -/
theorem hasEssBox_of_thickHalf {P : Work.CoreTopology.ParamTorus} {r s u ε : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} (hr : 0 < r) (hrs : r < s)
    (hs : s < (1 + Submission.eps) * r) (hu : |u| < Submission.eps * r) (hε : 0 < ε)
    (hε8 : 8 * ε ≤ Submission.shrinkFactor * r - (Submission.b * s + |u| / 2))
    (h : ThickHalf P s c σ u ε) :
    ∃ c' σ', Submission.HasEssBox P (Submission.shrinkFactor * r) c' σ' := by
  have hε0 : 0 ≤ ε := le_of_lt hε
  rcases h with ⟨γ, hγ, hmem⟩ | ⟨γ, hγ, hmem⟩
  · -- `γ` lies in the thickening of the *upper* half-region: the lower half of the box
    refine ⟨c + Work.BoxShrink.shiftVσ σ (((u - ε) + Submission.boxSide 2 * (s + ε)) / 2),
      Submission.cycPerm.trans σ, γ, hγ, fun t => ?_⟩
    obtain ⟨x, hx, hd⟩ := mem_thickening_iff.mp (hmem t)
    rw [Work.BoxShrink.Core.mem_upperRegion] at hx
    have hxP : x ∈ Submission.PBox s c σ := hx.2.1
    have hxlt : c (σ 2) + u < x (σ 2) := hx.2.2
    have hdx : ‖γ t - x‖ < ε := by rw [← dist_eq_norm]; exact hd
    have h1 : γ t ∈ Submission.PBox (s + ε) c σ := mem_PBox_add_of_norm_sub_lt hε0 hxP hdx
    have h2 : |γ t (σ 2) - x (σ 2)| ≤ ‖γ t - x‖ := PiLp.norm_apply_le (p := 2)
      (β := fun _ : Fin 3 => ℝ) (γ t - x) (σ 2)
    have h4 : c (σ 2) + (u - ε) < γ t (σ 2) := by
      have h5 : -(γ t (σ 2) - x (σ 2)) ≤ |γ t (σ 2) - x (σ 2)| := neg_le_abs _
      linarith
    exact Submission.PBox_mono (halfBox_spec' hε0 hε8)
      (Work.BoxShrink.halfBox_lower_subset_perm (s + ε) (u - ε) (by linarith)
        (abs_sub_lt_boxSide_two_mul hr hrs hu hε0) c σ ⟨h1, h4⟩)
  · -- `γ` lies in the thickening of the *lower* half-region: the upper half of the box
    refine ⟨c + Work.BoxShrink.shiftVσ σ (((u + ε) - Submission.boxSide 2 * (s + ε)) / 2),
      Submission.cycPerm.trans σ, γ, hγ, fun t => ?_⟩
    obtain ⟨x, hx, hd⟩ := mem_thickening_iff.mp (hmem t)
    rw [Work.BoxShrink.Core.mem_lowerRegion] at hx
    have hxP : x ∈ Submission.PBox s c σ := hx.2.1
    have hxlt : x (σ 2) < c (σ 2) + u := hx.2.2
    have hdx : ‖γ t - x‖ < ε := by rw [← dist_eq_norm]; exact hd
    have h1 : γ t ∈ Submission.PBox (s + ε) c σ := mem_PBox_add_of_norm_sub_lt hε0 hxP hdx
    have h2 : |γ t (σ 2) - x (σ 2)| ≤ ‖γ t - x‖ := PiLp.norm_apply_le (p := 2)
      (β := fun _ : Fin 3 => ℝ) (γ t - x) (σ 2)
    have h4 : γ t (σ 2) < c (σ 2) + (u + ε) := by
      have h5 : γ t (σ 2) - x (σ 2) ≤ |γ t (σ 2) - x (σ 2)| := le_abs_self _
      linarith
    exact Submission.PBox_mono (halfBox_spec hε0 hε8)
      (Work.BoxShrink.halfBox_upper_subset_perm (s + ε) (u + ε) (by linarith)
        (abs_add_lt_boxSide_two_mul hr hrs hu hε0) c σ ⟨h1, h4⟩)


/-- **The conversion for the shifted ε-form.**  If an essential loop of the surface lies in
`PBox (s + ε) c σ` on the correct side of the plane shifted by `ε`, then a box of size
`shrinkFactor * r` meets the surface in an essential loop. -/
theorem hasEssBox_of_thickHalfShifted {P : Work.CoreTopology.ParamTorus} {r s u ε : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} (hr : 0 < r) (hrs : r < s)
    (hu : |u| < Submission.eps * r) (hε : 0 < ε)
    (hε8 : 8 * ε ≤ Submission.shrinkFactor * r - (Submission.b * s + |u| / 2))
    (h : ThickHalfShifted P s c σ u ε) :
    ∃ c' σ', Submission.HasEssBox P (Submission.shrinkFactor * r) c' σ' := by
  have hε0 : 0 ≤ ε := le_of_lt hε
  rcases h with ⟨γ, hγ, hmem⟩ | ⟨γ, hγ, hmem⟩
  · -- strictly above the plane shifted down by `ε`
    refine ⟨c + Work.BoxShrink.shiftVσ σ (((u - ε) + Submission.boxSide 2 * (s + ε)) / 2),
      Submission.cycPerm.trans σ, γ, hγ, fun t => ?_⟩
    have hlt : c (σ 2) + (u - ε) < γ t (σ 2) := by linarith [(hmem t).2]
    exact Submission.PBox_mono (halfBox_spec' hε0 hε8)
      (Work.BoxShrink.halfBox_lower_subset_perm (s + ε) (u - ε) (by linarith)
        (abs_sub_lt_boxSide_two_mul hr hrs hu hε0) c σ ⟨(hmem t).1, hlt⟩)
  · -- strictly below the plane shifted up by `ε`
    refine ⟨c + Work.BoxShrink.shiftVσ σ (((u + ε) - Submission.boxSide 2 * (s + ε)) / 2),
      Submission.cycPerm.trans σ, γ, hγ, fun t => ?_⟩
    have hlt : γ t (σ 2) < c (σ 2) + (u + ε) := by linarith [(hmem t).2]
    exact Submission.PBox_mono (halfBox_spec hε0 hε8)
      (Work.BoxShrink.halfBox_upper_subset_perm (s + ε) (u + ε) (by linarith)
        (abs_add_lt_boxSide_two_mul hr hrs hu hε0) c σ ⟨(hmem t).1, hlt⟩)

/-- **The ε-form implies the shifted ε-form**: a point within distance `ε` of a point of the
half-region `{y (σ 2) > c (σ 2) + u}` lies in `PBox (s + ε) c σ` (the box norm is `1`-Lipschitz in
the coordinate directions) and strictly above the plane shifted down by `ε`. -/
theorem thickHalfShifted_of_thickHalf {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u ε : ℝ} (hε : 0 ≤ ε) (h : ThickHalf P s c σ u ε) :
    ThickHalfShifted P s c σ u ε := by
  rcases h with ⟨γ, hγ, hmem⟩ | ⟨γ, hγ, hmem⟩
  · refine Or.inl ⟨γ, hγ, fun t => ?_⟩
    obtain ⟨x, hx, hd⟩ := mem_thickening_iff.mp (hmem t)
    rw [Work.BoxShrink.Core.mem_upperRegion] at hx
    have hdx : ‖γ t - x‖ < ε := by rw [← dist_eq_norm]; exact hd
    refine ⟨mem_PBox_add_of_norm_sub_lt hε hx.2.1 hdx, ?_⟩
    have h2 : |γ t (σ 2) - x (σ 2)| ≤ ‖γ t - x‖ := PiLp.norm_apply_le (p := 2)
      (β := fun _ : Fin 3 => ℝ) (γ t - x) (σ 2)
    have h3 : -(γ t (σ 2) - x (σ 2)) ≤ |γ t (σ 2) - x (σ 2)| := neg_le_abs _
    linarith [hx.2.2]
  · refine Or.inr ⟨γ, hγ, fun t => ?_⟩
    obtain ⟨x, hx, hd⟩ := mem_thickening_iff.mp (hmem t)
    rw [Work.BoxShrink.Core.mem_lowerRegion] at hx
    have hdx : ‖γ t - x‖ < ε := by rw [← dist_eq_norm]; exact hd
    refine ⟨mem_PBox_add_of_norm_sub_lt hε hx.2.1 hdx, ?_⟩
    have h2 : |γ t (σ 2) - x (σ 2)| ≤ ‖γ t - x‖ := PiLp.norm_apply_le (p := 2)
      (β := fun _ : Fin 3 => ℝ) (γ t - x) (σ 2)
    have h3 : γ t (σ 2) - x (σ 2) ≤ |γ t (σ 2) - x (σ 2)| := le_abs_self _
    linarith [hx.2.2]

/-- **The shifted ε-form follows from the ε-form.** -/
theorem countingHalfEpsShifted_of_countingHalfEpsSphere (h : CountingHalfEpsSphere) :
    CountingHalfEpsShifted := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    ε hε
  exact thickHalfShifted_of_thickHalf (le_of_lt hε)
    (h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
      ε hε)

end

end Work.Drive.EpsSphere
