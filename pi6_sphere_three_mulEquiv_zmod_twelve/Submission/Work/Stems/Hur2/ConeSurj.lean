import Submission.Work.Stems.Hur2.Bd

/-!
# The cone map of the square is surjective

`Work.Stems.Cubical.coneMap (s,t) = centre + (1-s)·(bd t - centre)` maps `I × I` onto the square
(the square is star-shaped about its centre), and collapses `{1} × I` to the centre.  Surjectivity
plus compactness makes it a quotient map, which is what lets a null-homotopy of the boundary loop
descend to a filling square.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2

open Work.Stems.Cubical

noncomputable section

/-- `coneMap` at `s = 1` is the centre. -/
theorem coneMap_one (t : IC 1) :
    coneMap ((fun _ : Fin 1 => (1 : unitInterval)), t) = sqCentre := by
  funext j
  apply Subtype.ext
  show (1 : ℝ) / 2 + (1 - ((1 : unitInterval) : ℝ)) * ((bd (t 0) j : ℝ) - 1 / 2) = 1 / 2
  norm_num

/-- The boundary point of the square on the ray from the centre through `x`. -/
def rayPt (x : IC 2) (h : rad x ≠ 0) : IC 2 := fun j =>
  ⟨1 / 2 + ((x j : ℝ) - 1 / 2) / rad x, by
    have hpos : 0 < rad x := lt_of_le_of_ne (rad_nonneg x) (Ne.symm h)
    have hle : |2 * (x j : ℝ) - 1| ≤ rad x := by
      have hh : rad x = max |2 * (x 0 : ℝ) - 1| |2 * (x 1 : ℝ) - 1| := rfl
      rw [hh]
      fin_cases j <;> simp
    have hval : 1 / 2 + ((x j : ℝ) - 1 / 2) / rad x
        = (rad x / 2 + ((x j : ℝ) - 1 / 2)) / rad x := by
      field_simp
    constructor
    · rw [hval, div_nonneg_iff]
      exact Or.inl ⟨by have := neg_le_abs (2 * (x j : ℝ) - 1); linarith, rad_nonneg x⟩
    · rw [hval, div_le_one hpos]
      have := le_abs_self (2 * (x j : ℝ) - 1)
      linarith⟩

theorem rad_rayPt (x : IC 2) (h : rad x ≠ 0) : rad (rayPt x h) = 1 := by
  have hpos : 0 < rad x := lt_of_le_of_ne (rad_nonneg x) (Ne.symm h)
  have hcoord : ∀ j : Fin 2,
      |2 * ((rayPt x h) j : ℝ) - 1| = |2 * (x j : ℝ) - 1| / rad x := by
    intro j
    have hval : ((rayPt x h) j : ℝ) = 1 / 2 + ((x j : ℝ) - 1 / 2) / rad x := rfl
    have key : 2 * (1 / 2 + ((x j : ℝ) - 1 / 2) / rad x) - 1
        = 2 * ((x j : ℝ) - 1 / 2) / rad x := by
      field_simp
      ring
    rw [hval, key, abs_div, abs_of_pos hpos]
    congr 1
    ring_nf
  have hmax : max |2 * (x 0 : ℝ) - 1| |2 * (x 1 : ℝ) - 1| = rad x := rfl
  have hrew : rad (rayPt x h) =
      max (|2 * (x 0 : ℝ) - 1| / rad x) (|2 * (x 1 : ℝ) - 1| / rad x) := by
    rw [rad_eq_max, hcoord 0, hcoord 1]
  rw [hrew]
  apply le_antisymm
  · apply max_le
    · rw [div_le_one hpos]; rw [← hmax]; exact le_max_left _ _
    · rw [div_le_one hpos]; rw [← hmax]; exact le_max_right _ _
  · rcases le_total |2 * (x 0 : ℝ) - 1| |2 * (x 1 : ℝ) - 1| with hle | hle
    · have hb : |2 * (x 1 : ℝ) - 1| = rad x := by
        rw [← hmax]; exact (max_eq_right hle).symm
      rw [hb, div_self h]; exact le_max_right _ _
    · have hb : |2 * (x 0 : ℝ) - 1| = rad x := by
        rw [← hmax]; exact (max_eq_left hle).symm
      rw [hb, div_self h]; exact le_max_left _ _

theorem rayPt_mem_boundary (x : IC 2) (h : rad x ≠ 0) :
    rayPt x h ∈ Cube.boundary (Fin 2) := by
  rw [Cube.boundary]
  have hr : rad (rayPt x h) = 1 := rad_rayPt x h
  have hmax : max |2 * ((rayPt x h) 0 : ℝ) - 1| |2 * ((rayPt x h) 1 : ℝ) - 1| = 1 := by
    rw [← rad_eq_max]; exact hr
  rcases le_total |2 * ((rayPt x h) 0 : ℝ) - 1| |2 * ((rayPt x h) 1 : ℝ) - 1| with hle | hle
  · have h1 : |2 * ((rayPt x h) 1 : ℝ) - 1| = 1 := by
      rw [← max_eq_right hle]; exact hmax
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp h1 with hc | hc
    · refine ⟨1, Or.inr ?_⟩
      apply Subtype.ext
      show ((rayPt x h) 1 : ℝ) = 1
      linarith
    · refine ⟨1, Or.inl ?_⟩
      apply Subtype.ext
      show ((rayPt x h) 1 : ℝ) = 0
      linarith
  · have h1 : |2 * ((rayPt x h) 0 : ℝ) - 1| = 1 := by
      rw [← max_eq_left hle]; exact hmax
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp h1 with hc | hc
    · refine ⟨0, Or.inr ?_⟩
      apply Subtype.ext
      show ((rayPt x h) 0 : ℝ) = 1
      linarith
    · refine ⟨0, Or.inl ?_⟩
      apply Subtype.ext
      show ((rayPt x h) 0 : ℝ) = 0
      linarith

/-- **The cone map is surjective.** -/
theorem coneMap_surjective : Function.Surjective (coneMap : IC 1 × IC 1 → IC 2) := by
  intro x
  by_cases h : rad x = 0
  · have hx : x = sqCentre := by
      have hmax : max |2 * (x 0 : ℝ) - 1| |2 * (x 1 : ℝ) - 1| = 0 := by
        rw [← rad_eq_max]; exact h
      have h0 : |2 * (x 0 : ℝ) - 1| = 0 := le_antisymm (hmax ▸ le_max_left _ _) (abs_nonneg _)
      have h1 : |2 * (x 1 : ℝ) - 1| = 0 := le_antisymm (hmax ▸ le_max_right _ _) (abs_nonneg _)
      funext j
      apply Subtype.ext
      fin_cases j
      · show (x 0 : ℝ) = 1 / 2
        have := abs_eq_zero.mp h0
        linarith
      · show (x 1 : ℝ) = 1 / 2
        have := abs_eq_zero.mp h1
        linarith
    subst hx
    exact ⟨((fun _ : Fin 1 => (1 : unitInterval)), 0), coneMap_one 0⟩
  · obtain ⟨s, hs⟩ := bd_eq_of_mem_boundary (rayPt x h) (rayPt_mem_boundary x h)
    have hpos : 0 < rad x := lt_of_le_of_ne (rad_nonneg x) (Ne.symm h)
    have hmemb : (1 - rad x) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith [rad_le_one x], by linarith [rad_nonneg x]⟩
    refine ⟨(fun _ : Fin 1 => (⟨1 - rad x, hmemb⟩ : unitInterval),
      (fun _ : Fin 1 => s)), ?_⟩
    funext j
    apply Subtype.ext
    have hval : ((rayPt x h) j : ℝ) = 1 / 2 + ((x j : ℝ) - 1 / 2) / rad x := rfl
    have hcoe : ((⟨1 - rad x, hmemb⟩ : unitInterval) : ℝ) = 1 - rad x := rfl
    show 1 / 2 + (1 - ((⟨1 - rad x, hmemb⟩ : unitInterval) : ℝ)) * ((bd s j : ℝ) - 1 / 2)
      = (x j : ℝ)
    rw [hcoe, show (1 : ℝ) - (1 - rad x) = rad x by ring]
    rw [show (bd s j : ℝ) = ((rayPt x h) j : ℝ) from by
      have h1 : (bd s) j = (rayPt x h) j := congrFun hs j
      exact congrArg Subtype.val h1]
    rw [hval]
    field_simp
    ring

end

end Work.Stems.Hur2
