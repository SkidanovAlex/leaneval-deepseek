import Mathlib
import Submission.Work.Drive.EpsForm.Defs
import Submission.Work.BoxShrink.Core.Defs
import Submission.Work.BoxShrink.crux
import Submission.Work.BoxShrink.Pinch.Trace

/-!
# The closed half-box endgame of Pardon's Lemma 3

A witness for Pardon's `doublebubble2` conclusion in the solid form
(`Work.Drive.CountingHalfEpsBody`) is an essential loop of the surface `F = torus ψ` all of whose
points are within `ε` of one of the two **solid** half-boxes

  `{x ∈ PBox s c σ | x (σ 2) < c (σ 2) + u}`  and  `{x ∈ PBox s c σ | c (σ 2) + u < x (σ 2)}`.

A point of the solid half-box is at distance `0` from it, so an essential loop lying in the solid
half-box is a witness for every `ε > 0`.  This module records the slightly weaker (and much more
available) criterion used by the region-level arguments of the chapter: it is enough that the loop
lie in the **closed half box**

  `LB = {x | boxNorm c σ x ≤ s ∧ x (σ 2) ≤ c (σ 2) + u}`  (resp. `UB = {x | boxNorm c σ x ≤ s ∧ c (σ 2) + u ≤ x (σ 2)}`)

— the convex region whose interior is exactly the solid half box (the hypothesis `|u| < boxSide 2 * s`
makes the two conditions compatible).  The main content is the elementary geometric lemma
`exists_mem_PBox_of_mem_closedHalfBox`: every point of the closed half box is within `ε` of the
solid half box — shrink the point radially towards the centre `c` of the box and shift it slightly
in the `σ 2`-coordinate; both movements are arbitrarily small and neither leaves the box for a small
enough parameter.

The criterion is then wired into the target:

* `conclusion_lower_of_closedHalf_loop`, `conclusion_upper_of_closedHalf_loop` — an essential loop
  of the closed half box gives the ε-conclusion;
* `countingHalfEpsBody_of_closedHalfSpans` — the target `Work.Drive.CountingHalfEpsBody` follows
  from the residual "at every configuration of the crux, the winding span of one of the two closed
  half boxes is nonzero": this is `Work.Drive.EpsForm.ClosedHalfSpans`.

Why the closed half box is the right intermediate object: it contains both the open half-region and
the parts of the trace (`sliceRegion`) and of the box sphere (`sphereTrace`) lying on its side, and
the one-sided push-off `Work.BoxShrink.PinchOff.halfPush_holds` shows
`W(lowerRegion) ≤ W(LowerSide)` — a witness in the *closed* half box need not be pushable into a
half-region.  This is exactly the situation at the `RefuteDrop` configurations
(`Submission/Work/BoxShrink/PinchOff/RefuteDrop/`), where both open half-regions are inessential
while the box region has full span: an essential loop there must run near the trace, and the trace
belongs to the closed half boxes precisely.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive.EpsForm

noncomputable section

/-! ## The two closed half boxes -/

/-- The **closed lower half box**: the closed box cut by the half-space `y (σ 2) ≤ c (σ 2) + u`.
Its interior is the solid lower half box of `Work.Drive.CountingHalfEpsBody`. -/
def closedLowerHalfBox (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  {y : R3 | Submission.boxNorm c σ y ≤ s ∧ y (σ 2) ≤ c (σ 2) + u}

/-- The **closed upper half box**. -/
def closedUpperHalfBox (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  {y : R3 | Submission.boxNorm c σ y ≤ s ∧ c (σ 2) + u ≤ y (σ 2)}

theorem lowerRegion_subset_closedLowerHalfBox {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    Work.BoxShrink.Core.lowerRegion P s c σ u ⊆ closedLowerHalfBox s c σ u := by
  intro y hy
  obtain ⟨-, hyb, hyl⟩ := Work.BoxShrink.Core.mem_lowerRegion.mp hy
  refine ⟨?_, le_of_lt hyl⟩
  have hlt := Work.BoxShrink.Core.boxNorm_lt_of_mem_boxRegion (P := P)
    (Work.BoxShrink.Core.mem_boxRegion.mpr ⟨hy.1.1, hy.1.2⟩)
  exact le_of_lt hlt

theorem upperRegion_subset_closedUpperHalfBox {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    Work.BoxShrink.Core.upperRegion P s c σ u ⊆ closedUpperHalfBox s c σ u := by
  intro y hy
  obtain ⟨-, hyb, hyu⟩ := Work.BoxShrink.Core.mem_upperRegion.mp hy
  refine ⟨?_, le_of_lt hyu⟩
  have hlt := Work.BoxShrink.Core.boxNorm_lt_of_mem_boxRegion (P := P)
    (Work.BoxShrink.Core.mem_boxRegion.mpr ⟨hy.1.1, hy.1.2⟩)
  exact le_of_lt hlt

theorem sliceRegion_subset_closedLowerHalfBox {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ closedLowerHalfBox s c σ u := by
  intro y hy
  obtain ⟨-, hyb, hyu⟩ := Work.BoxShrink.Core.mem_sliceRegion.mp hy
  refine ⟨?_, le_of_eq hyu⟩
  have hlt := Work.BoxShrink.Core.boxNorm_lt_of_mem_boxRegion (P := P)
    (Work.BoxShrink.Core.mem_boxRegion.mpr ⟨hy.1.1, hy.1.2⟩)
  exact le_of_lt hlt

theorem sliceRegion_subset_closedUpperHalfBox {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ closedUpperHalfBox s c σ u := by
  intro y hy
  obtain ⟨-, hyb, hyu⟩ := Work.BoxShrink.Core.mem_sliceRegion.mp hy
  refine ⟨?_, le_of_eq hyu.symm⟩
  have hlt := Work.BoxShrink.Core.boxNorm_lt_of_mem_boxRegion (P := P)
    (Work.BoxShrink.Core.mem_boxRegion.mpr ⟨hy.1.1, hy.1.2⟩)
  exact le_of_lt hlt

/-! ## The geometric core: a point of a closed half box is within `ε` of the solid half box -/

theorem abs_coord_le_of_boxNorm_le {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {y : R3}
    (hy : Submission.boxNorm c σ y ≤ s) (i : Fin 3) :
    |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s := by
  have h1 : |y (σ i) - c (σ i)| / Submission.boxSide i ≤ s := by
    have h2 : Submission.boxNorm c σ y =
        max (max (|y (σ 0) - c (σ 0)| / Submission.boxSide 0)
          (|y (σ 1) - c (σ 1)| / Submission.boxSide 1))
          (|y (σ 2) - c (σ 2)| / Submission.boxSide 2) := rfl
    rw [h2] at hy
    fin_cases i
    · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
    · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
    · exact le_trans (le_max_right _ _) hy
  have hpos := Submission.boxSide_pos i
  rw [div_le_iff₀ hpos] at h1
  simpa [mul_comm] using h1

theorem exists_mem_PBox_of_mem_closedHalfBox {s u ε : ℝ} (hε : 0 < ε) (hs : 0 < s)
    (hu : |u| < Submission.boxSide 2 * s) {c : R3} {σ : Equiv.Perm (Fin 3)}
    {y : R3} (hy : Submission.boxNorm c σ y ≤ s) (hlev : y (σ 2) ≤ c (σ 2) + u) :
    ∃ x ∈ Submission.PBox s c σ, x (σ 2) < c (σ 2) + u ∧ dist y x < ε := by
  have hcoord : ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s :=
    abs_coord_le_of_boxNorm_le hy
  have hbs2 : 0 < Submission.boxSide 2 := Submission.boxSide_pos 2
  set lam : ℝ := min (1/2) (ε / (2 * (dist y c + s * Submission.boxSide 2 + 1))) with hlamdef
  have hden : 0 < 2 * (dist y c + s * Submission.boxSide 2 + 1) := by positivity
  have hlampos : 0 < lam := lt_min (by norm_num) (div_pos hε hden)
  have hlamle : lam ≤ ε / (2 * (dist y c + s * Submission.boxSide 2 + 1)) := min_le_right _ _
  have hlamhalf : lam ≤ 1 / 2 := min_le_left _ _
  set mu : ℝ := lam * (s * Submission.boxSide 2 + |u|) / 2 with hmudef
  have hmupos : 0 < mu := by rw [hmudef]; positivity
  have hmult : mu < lam * (Submission.boxSide 2 * s) := by
    have h2 : lam * (s * Submission.boxSide 2 + |u|) / 2 < lam * (Submission.boxSide 2 * s) := by
      rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 2)]
      nlinarith [hu, hlampos, hbs2, abs_nonneg u]
    simpa [hmudef] using h2
  have humu : lam * |u| < mu := by
    have h2 : lam * |u| < lam * (s * Submission.boxSide 2 + |u|) / 2 := by
      rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      nlinarith [hu, hlampos, hbs2, abs_nonneg u]
    simpa [hmudef] using h2
  set z : R3 := c + (1 - lam) • (y - c) with hzdef
  set x : R3 := WithLp.toLp 2 (Function.update z.ofLp (σ 2) (z (σ 2) - mu)) with hxdef
  have hzcoord : ∀ i : Fin 3, z i = c i + (1 - lam) * (y i - c i) := by
    intro i
    rw [hzdef]
    simp only [WithLp.ofLp_add, Pi.add_apply, WithLp.ofLp_smul, Pi.smul_apply,
      WithLp.ofLp_sub, Pi.sub_apply, smul_eq_mul]
  have hxother : ∀ j : Fin 3, j ≠ σ 2 → x j = z j := by
    intro j hj
    rw [hxdef]
    simp only [WithLp.ofLp_toLp]
    exact Function.update_of_ne hj _ _
  have hxself : x (σ 2) = z (σ 2) - mu := by
    rw [hxdef]
    simp only [WithLp.ofLp_toLp]
    exact Function.update_self (σ 2) (z (σ 2) - mu) z.ofLp
  have hlevz : z (σ 2) - mu - c (σ 2) = (1 - lam) * (y (σ 2) - c (σ 2)) - mu := by
    rw [hzcoord]; ring
  refine ⟨x, ?_, ?_, ?_⟩
  · rw [Submission.mem_PBox]
    intro i
    by_cases hi : i = 2
    · subst hi
      have hA : x (σ 2) - c (σ 2) = (1 - lam) * (y (σ 2) - c (σ 2)) - mu := by
        rw [hxself]; rw [hzcoord]; ring
      rw [hA]
      have h1 : |(1 - lam) * (y (σ 2) - c (σ 2)) - mu|
          ≤ (1 - lam) * |y (σ 2) - c (σ 2)| + mu := by
        calc |(1 - lam) * (y (σ 2) - c (σ 2)) - mu|
            = |(1 - lam) * (y (σ 2) - c (σ 2)) + (-mu)| := by ring_nf
          _ ≤ |(1 - lam) * (y (σ 2) - c (σ 2))| + |(-mu)| := abs_add_le _ _
          _ = (1 - lam) * |y (σ 2) - c (σ 2)| + mu := by
                rw [abs_mul, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - lam),
                  abs_of_pos hmupos]
      have h2 : (1 - lam) * |y (σ 2) - c (σ 2)| ≤ (1 - lam) * (Submission.boxSide 2 * s) :=
        mul_le_mul_of_nonneg_left (hcoord 2) (by linarith)
      have h3 : |(1 - lam) * (y (σ 2) - c (σ 2)) - mu|
          ≤ (1 - lam) * (Submission.boxSide 2 * s) + mu := le_trans h1 (by linarith)
      have h4 : (1 - lam) * (Submission.boxSide 2 * s) + mu
          < (1 - lam) * (Submission.boxSide 2 * s) + lam * (Submission.boxSide 2 * s) := by
        linarith [hmult]
      have h5 : (1 - lam) * (Submission.boxSide 2 * s) + lam * (Submission.boxSide 2 * s)
          = Submission.boxSide 2 * s := by ring
      linarith [h3, h4, h5]
    · have hσi : σ i ≠ σ 2 := fun h => hi (σ.injective h)
      have hB : x (σ i) - c (σ i) = (1 - lam) * (y (σ i) - c (σ i)) := by
        rw [hxother (σ i) hσi, hzcoord]; ring
      rw [hB]
      have h1 : |(1 - lam) * (y (σ i) - c (σ i))|
          = (1 - lam) * |y (σ i) - c (σ i)| := by
        rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - lam)]
      rw [h1]
      have h4 : 0 < Submission.boxSide i * s := mul_pos (Submission.boxSide_pos i) hs
      have h5 : (1 - lam) * |y (σ i) - c (σ i)| ≤ (1 - lam) * (Submission.boxSide i * s) :=
        mul_le_mul_of_nonneg_left (hcoord i) (by linarith)
      nlinarith [h5, h4, hlampos, abs_nonneg (y (σ i) - c (σ i))]
  · have hA : x (σ 2) - c (σ 2) - u = (1 - lam) * (y (σ 2) - c (σ 2)) - mu - u := by
      rw [hxself]; rw [hzcoord]; ring
    have hlev' : y (σ 2) - c (σ 2) ≤ u := by linarith
    have h1 : (1 - lam) * (y (σ 2) - c (σ 2)) ≤ (1 - lam) * u :=
      mul_le_mul_of_nonneg_left hlev' (by linarith)
    have h2 : -lam * u ≤ lam * |u| := by
      have := neg_le_abs u
      nlinarith [hlampos]
    have h3 : (1 - lam) * u - mu < u := by linarith [h2, humu]
    linarith [hA, h1, h3]
  · have hsub : y - z = lam • (y - c) := by
      rw [hzdef]
      ext i
      simp only [WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_add, Pi.add_apply,
        WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      ring
    have hdist1 : dist y z = lam * dist y c := by
      rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hlampos, dist_eq_norm]
    have hsub2 : z - x = mu • (PiLp.single 2 (σ 2) (1 : ℝ) : R3) := by
      rw [hxdef]
      ext i
      by_cases hi : i = σ 2
      · subst hi
        simp only [WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_smul, Pi.smul_apply,
          WithLp.ofLp_toLp, Function.update_self, PiLp.single_eq_same, smul_eq_mul, mul_one]
        ring
      · simp only [WithLp.ofLp_sub, Pi.sub_apply,
          WithLp.ofLp_smul, Pi.smul_apply, WithLp.ofLp_toLp, Function.update_of_ne hi,
          PiLp.single_eq_of_ne (p := 2) hi, smul_eq_mul, mul_zero, sub_self]
    have hdist2 : dist z x = mu := by
      rw [dist_eq_norm, hsub2, norm_smul, Real.norm_eq_abs, abs_of_pos hmupos,
        PiLp.norm_single 2 (fun _ : Fin 3 => ℝ) (σ 2) (1 : ℝ), norm_one, mul_one]
    have hmain : dist y x ≤ lam * dist y c + mu := by
      calc dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
        _ = lam * dist y c + mu := by rw [hdist1, hdist2]
    have h1 : mu ≤ lam * (s * Submission.boxSide 2) := by
      have h2 : s * Submission.boxSide 2 + |u| ≤ 2 * (s * Submission.boxSide 2) := by
        nlinarith [abs_lt.mp hu]
      rw [hmudef]
      nlinarith [hlampos]
    have h2 : lam * (dist y c + s * Submission.boxSide 2) ≤ ε / 2 := by
      have h3 := hlamle
      rw [le_div_iff₀ hden] at h3
      nlinarith [h3]
    have h3 : lam * dist y c + mu ≤ lam * dist y c + lam * (s * Submission.boxSide 2) := by
      linarith [h1]
    have h4 : lam * dist y c + lam * (s * Submission.boxSide 2) = lam * (dist y c + s * Submission.boxSide 2) := by
      ring
    have h5 : lam * (dist y c + s * Submission.boxSide 2) < ε := by linarith [h2, hε]
    linarith [hmain, h3, h4, h5]

/-- The mirror image of `exists_mem_PBox_of_mem_closedHalfBox`: a point of the closed *upper* half
box is within `ε` of the solid upper half box. -/
theorem exists_mem_PBox_of_mem_closedUpperHalfBox {s u ε : ℝ} (hε : 0 < ε) (hs : 0 < s)
    (hu : |u| < Submission.boxSide 2 * s) {c : R3} {σ : Equiv.Perm (Fin 3)}
    {y : R3} (hy : Submission.boxNorm c σ y ≤ s) (hlev : c (σ 2) + u ≤ y (σ 2)) :
    ∃ x ∈ Submission.PBox s c σ, c (σ 2) + u < x (σ 2) ∧ dist y x < ε := by
  have hcoord : ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s :=
    abs_coord_le_of_boxNorm_le hy
  have hbs2 : 0 < Submission.boxSide 2 := Submission.boxSide_pos 2
  set lam : ℝ := min (1/2) (ε / (2 * (dist y c + s * Submission.boxSide 2 + 1))) with hlamdef
  have hden : 0 < 2 * (dist y c + s * Submission.boxSide 2 + 1) := by positivity
  have hlampos : 0 < lam := lt_min (by norm_num) (div_pos hε hden)
  have hlamhalf : lam ≤ 1 / 2 := min_le_left _ _
  have hlamle : lam ≤ ε / (2 * (dist y c + s * Submission.boxSide 2 + 1)) := min_le_right _ _
  set mu : ℝ := lam * (s * Submission.boxSide 2 + |u|) / 2 with hmudef
  have hmupos : 0 < mu := by rw [hmudef]; positivity
  have hmult : mu < lam * (Submission.boxSide 2 * s) := by
    have h2 : lam * (s * Submission.boxSide 2 + |u|) / 2 < lam * (Submission.boxSide 2 * s) := by
      rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 2)]
      nlinarith [hu, hlampos, hbs2, abs_nonneg u]
    simpa [hmudef] using h2
  have hlamu : lam * u < mu := by
    have h1 : lam * u ≤ lam * |u| := mul_le_mul_of_nonneg_left (le_abs_self u) (le_of_lt hlampos)
    have h2 : lam * |u| < lam * (s * Submission.boxSide 2 + |u|) / 2 := by
      rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      nlinarith [hu, hlampos, hbs2, abs_nonneg u]
    rw [hmudef]
    linarith [h1, h2]
  set z : R3 := c + (1 - lam) • (y - c) with hzdef
  set x : R3 := WithLp.toLp 2 (Function.update z.ofLp (σ 2) (z (σ 2) + mu)) with hxdef
  have hzcoord : ∀ i : Fin 3, z i = c i + (1 - lam) * (y i - c i) := by
    intro i
    rw [hzdef]
    simp only [WithLp.ofLp_add, Pi.add_apply, WithLp.ofLp_smul, Pi.smul_apply,
      WithLp.ofLp_sub, Pi.sub_apply, smul_eq_mul]
  have hxother : ∀ j : Fin 3, j ≠ σ 2 → x j = z j := by
    intro j hj
    rw [hxdef]
    simp only [WithLp.ofLp_toLp]
    exact Function.update_of_ne hj _ _
  have hxself : x (σ 2) = z (σ 2) + mu := by
    rw [hxdef]
    simp only [WithLp.ofLp_toLp]
    exact Function.update_self (σ 2) (z (σ 2) + mu) z.ofLp
  refine ⟨x, ?_, ?_, ?_⟩
  · rw [Submission.mem_PBox]
    intro i
    by_cases hi : i = 2
    · subst hi
      have hA : x (σ 2) - c (σ 2) = (1 - lam) * (y (σ 2) - c (σ 2)) + mu := by
        rw [hxself]; rw [hzcoord]; ring
      rw [hA]
      have h1 : |(1 - lam) * (y (σ 2) - c (σ 2)) + mu|
          ≤ (1 - lam) * |y (σ 2) - c (σ 2)| + mu := by
        calc |(1 - lam) * (y (σ 2) - c (σ 2)) + mu|
            ≤ |(1 - lam) * (y (σ 2) - c (σ 2))| + |mu| := abs_add_le _ _
          _ = (1 - lam) * |y (σ 2) - c (σ 2)| + mu := by
                rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - lam), abs_of_pos hmupos]
      have h2 : (1 - lam) * |y (σ 2) - c (σ 2)| ≤ (1 - lam) * (Submission.boxSide 2 * s) :=
        mul_le_mul_of_nonneg_left (hcoord 2) (by linarith)
      have h3 : |(1 - lam) * (y (σ 2) - c (σ 2)) + mu|
          ≤ (1 - lam) * (Submission.boxSide 2 * s) + mu := le_trans h1 (by linarith)
      have h4 : (1 - lam) * (Submission.boxSide 2 * s) + mu
          < (1 - lam) * (Submission.boxSide 2 * s) + lam * (Submission.boxSide 2 * s) := by
        linarith [hmult]
      have h5 : (1 - lam) * (Submission.boxSide 2 * s) + lam * (Submission.boxSide 2 * s)
          = Submission.boxSide 2 * s := by ring
      linarith [h3, h4, h5]
    · have hσi : σ i ≠ σ 2 := fun h => hi (σ.injective h)
      have hB : x (σ i) - c (σ i) = (1 - lam) * (y (σ i) - c (σ i)) := by
        rw [hxother (σ i) hσi, hzcoord]; ring
      rw [hB]
      have h1 : |(1 - lam) * (y (σ i) - c (σ i))|
          = (1 - lam) * |y (σ i) - c (σ i)| := by
        rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - lam)]
      rw [h1]
      have h4 : 0 < Submission.boxSide i * s := mul_pos (Submission.boxSide_pos i) hs
      have h5 : (1 - lam) * |y (σ i) - c (σ i)| ≤ (1 - lam) * (Submission.boxSide i * s) :=
        mul_le_mul_of_nonneg_left (hcoord i) (by linarith)
      nlinarith [h5, h4, hlampos, abs_nonneg (y (σ i) - c (σ i))]
  · have hA : x (σ 2) - c (σ 2) - u = (1 - lam) * (y (σ 2) - c (σ 2)) + mu - u := by
      rw [hxself]; rw [hzcoord]; ring
    have hlev' : u ≤ y (σ 2) - c (σ 2) := by linarith
    have h1 : (1 - lam) * u ≤ (1 - lam) * (y (σ 2) - c (σ 2)) :=
      mul_le_mul_of_nonneg_left hlev' (by linarith)
    have h3 : u < (1 - lam) * u + mu := by nlinarith [hlamu]
    linarith [hA, h1, h3]
  · have hsub : y - z = lam • (y - c) := by
      rw [hzdef]
      ext i
      simp only [WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_add, Pi.add_apply,
        WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      ring
    have hdist1 : dist y z = lam * dist y c := by
      rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hlampos, dist_eq_norm]
    have hsub2 : z - x = -(mu • (PiLp.single 2 (σ 2) (1 : ℝ) : R3)) := by
      rw [hxdef]
      ext i
      by_cases hi : i = σ 2
      · subst hi
        simp only [WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_neg, Pi.neg_apply,
          WithLp.ofLp_smul, Pi.smul_apply, WithLp.ofLp_toLp, Function.update_self,
          PiLp.single_eq_same, smul_eq_mul, mul_one]
        ring
      · simp only [WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_neg, Pi.neg_apply,
          WithLp.ofLp_smul, Pi.smul_apply, WithLp.ofLp_toLp, Function.update_of_ne hi,
          PiLp.single_eq_of_ne (p := 2) hi, smul_eq_mul, mul_zero, neg_zero, sub_self]
    have hdist2 : dist z x = mu := by
      rw [dist_eq_norm, hsub2, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hmupos,
        PiLp.norm_single 2 (fun _ : Fin 3 => ℝ) (σ 2) (1 : ℝ), norm_one, mul_one]
    have hmain : dist y x ≤ lam * dist y c + mu := by
      calc dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
        _ = lam * dist y c + mu := by rw [hdist1, hdist2]
    have h1 : mu ≤ lam * (s * Submission.boxSide 2) := by
      have h2 : s * Submission.boxSide 2 + |u| ≤ 2 * (s * Submission.boxSide 2) := by
        nlinarith [abs_lt.mp hu]
      rw [hmudef]
      nlinarith [hlampos]
    have h2 : lam * (dist y c + s * Submission.boxSide 2) ≤ ε / 2 := by
      have h3 := hlamle
      rw [le_div_iff₀ hden] at h3
      nlinarith [h3]
    have h3 : lam * dist y c + mu ≤ lam * dist y c + lam * (s * Submission.boxSide 2) := by
      linarith [h1]
    have h4 : lam * dist y c + lam * (s * Submission.boxSide 2)
        = lam * (dist y c + s * Submission.boxSide 2) := by ring
    have h5 : lam * (dist y c + s * Submission.boxSide 2) < ε := by linarith [h2, hε]
    linarith [hmain, h3, h4, h5]

/-! ## The criterion -/

/-- The slice lies in both closed half boxes, so an essential loop of the surface lying in the
slice already gives the residual `ClosedHalfSpans`.  (This is the "first alternative" of the trace
dichotomy `Work.Drive.EpsForm.SliceCleanOrCovered`, in the vocabulary of the closed half boxes.) -/
theorem windingSpan_closedLower_of_trace_essential {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)}
    (h : (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u)) :
    Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
      (closedLowerHalfBox s c σ u) ≠ ⊥ := by
  refine (Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mpr ?_
  obtain ⟨γ, hess, hmem⟩ := h
  exact ⟨γ, hess, fun t => sliceRegion_subset_closedLowerHalfBox (hmem t)⟩

/-- Dually, an essential loop in the slice gives the upper closed half box's span. -/
theorem windingSpan_closedUpper_of_trace_essential {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)}
    (h : (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u)) :
    Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
      (closedUpperHalfBox s c σ u) ≠ ⊥ := by
  refine (Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mpr ?_
  obtain ⟨γ, hess, hmem⟩ := h
  exact ⟨γ, hess, fun t => sliceRegion_subset_closedUpperHalfBox (hmem t)⟩

/-- The lower conclusion of `Work.Drive.CountingHalfEpsBody` from an essential loop of the closed
lower half box. -/
theorem conclusion_lower_of_closedHalf_loop {ψ : Submission.Diffeo} {s u ε : ℝ} (hε : 0 < ε)
    (hs : 0 < s) (hu : |u| < Submission.boxSide 2 * s) {c : R3} {σ : Equiv.Perm (Fin 3)}
    {γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ)}
    (hess : Work.CoreTopology.IsEssential _ γ)
    (hmem : ∀ t : ℝ, γ t ∈ closedLowerHalfBox s c σ u) :
    ∃ γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
      Work.CoreTopology.IsEssential _ γ ∧
        ∀ t : ℝ, ∃ x : R3, x ∈ Submission.PBox s c σ ∧ x (σ 2) < c (σ 2) + u ∧
          dist (γ t) x < ε :=
  ⟨γ, hess, fun t => exists_mem_PBox_of_mem_closedHalfBox hε hs hu (hmem t).1 (hmem t).2⟩

/-- The upper conclusion of `Work.Drive.CountingHalfEpsBody` from an essential loop of the closed
upper half box. -/
theorem conclusion_upper_of_closedHalf_loop {ψ : Submission.Diffeo} {s u ε : ℝ} (hε : 0 < ε)
    (hs : 0 < s) (hu : |u| < Submission.boxSide 2 * s) {c : R3} {σ : Equiv.Perm (Fin 3)}
    {γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ)}
    (hess : Work.CoreTopology.IsEssential _ γ)
    (hmem : ∀ t : ℝ, γ t ∈ closedUpperHalfBox s c σ u) :
    ∃ γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
      Work.CoreTopology.IsEssential _ γ ∧
        ∀ t : ℝ, ∃ x : R3, x ∈ Submission.PBox s c σ ∧ c (σ 2) + u < x (σ 2) ∧
          dist (γ t) x < ε :=
  ⟨γ, hess, fun t => exists_mem_PBox_of_mem_closedUpperHalfBox hε hs hu (hmem t).1 (hmem t).2⟩

/-- **The residual of the closed half-box route**: at every configuration carrying the crux's
hypotheses, one of the two closed half boxes carries a nonzero winding vector of the surface.

By `conclusion_lower_of_closedHalf_loop` / `conclusion_upper_of_closedHalf_loop` this implies the
target `Work.Drive.CountingHalfEpsBody`; it is weaker than the residuals which require the witness in
an *open* half-region (`Work.BoxShrink.Pinch.CountingHalf`, `Work.Drive.CountingHalfW`), because the
closed half boxes also contain the trace `sliceRegion` and the side `sphereTrace` of the box sphere —
which is where the essential loops of the `RefuteDrop` configurations live.

The *counting* of the crux is nevertheless load-bearing here, and cannot be replaced by topological
hypotheses: at the in-repo, sorry-free `RefuteDrop` configuration
(`Submission/Work/BoxShrink/PinchOff/RefuteDrop/`) the box-sphere trace is inessential
(`sphereTrace_inessential_drop`), the slice trace is inessential (`sigma_inessential_drop`, the
hypothesis Pardon's Lemma 2 supplies from the plane count), the box region has full span
(`omega_rank_two`), and yet *both* closed half boxes are inessential
(`not_containsEssentialLoop_halfBoxNbd_drop`, `..._upper`).  So no count-free spelling of this
residual can hold; see `NOTES_closedHalfSpans_session10.md` §3. -/
def ClosedHalfSpans : Prop :=
  ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.Drive.CleansDiscsW (Work.Smooth.Morse.torus ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (Work.Smooth.Morse.torus ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (Work.Smooth.Morse.torus ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
              (closedLowerHalfBox s c σ u) ≠ ⊥ ∨
            Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
              (closedUpperHalfBox s c σ u) ≠ ⊥

/-- **The target from the closed half-box spans.** -/
theorem countingHalfEpsBody_of_closedHalfSpans (h : ClosedHalfSpans) :
    Work.Drive.CountingHalfEpsBody := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    ε hε
  have hspos : 0 < s := lt_trans hr hrs
  have hbu : |u| < Submission.boxSide 2 * s := by
    have hle : Submission.eps ≤ Submission.boxSide 2 := by
      rw [Submission.boxSide_two, Submission.eps]
      linarith [Submission.one_le_rpow_two_thirds]
    have h1 : Submission.eps * r ≤ Submission.boxSide 2 * r :=
      mul_le_mul_of_nonneg_right hle (le_of_lt hr)
    have h2 : Submission.boxSide 2 * r < Submission.boxSide 2 * s := by
      nlinarith [Submission.boxSide_pos 2, hrs]
    linarith [hu, h1, h2]
  rcases h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    with hl | hupper
  · obtain ⟨γ, hess, hmem⟩ :=
      (Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mp hl
    exact Or.inl (conclusion_lower_of_closedHalf_loop hε hspos hbu hess hmem)
  · obtain ⟨γ, hess, hmem⟩ :=
      (Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mp hupper
    exact Or.inr (conclusion_upper_of_closedHalf_loop hε hspos hbu hess hmem)

end

end Work.Drive.EpsForm
