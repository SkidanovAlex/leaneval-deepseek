import Mathlib
import Submission.Work.Drive.Mono.JunctionGenC

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion

/-- The elementary estimate `|a| - |b| ≤ |a - b|`. -/
private theorem abs_sub_abs_le_sub (a b : ℝ) : |a| - |b| ≤ |a - b| := by
  have h2 : (a - b) + b = a := by ring
  have h : |a| ≤ |a - b| + |b| := by
    calc |a| = |(a - b) + b| := by rw [h2]
      _ ≤ |a - b| + |b| := abs_add_le _ _
  linarith

/-- The elementary estimate `|a| - |b| ≤ |a + b|`. -/
private theorem abs_sub_abs_le_add (a b : ℝ) : |a| - |b| ≤ |a + b| := by
  have h := abs_sub_abs_le_sub a (-b)
  rw [sub_neg_eq_add, abs_neg] at h
  exact h

/-- **`EdgeFree` from the margin of the edge locus.**  If the surface lies in the ball of radius
`RF` about `c`, the edge locus (two extremal box coordinates, i.e. the four vertical edge lines) keeps
the height `z ↦ z (σ 2) − (c (σ 2) + u)` at distance at least `mE > 0` from `0`, and the half-width
plus the tilt error stays strictly below both `mE` and the horizontal margin
`boxSide 2 · s − |u|`, then the closed tilted slab misses the whole edge locus
(`Work.Drive.Mono.EdgeFree`).  This is the producer-side result that discharges clause (c) of
`Work.Drive.Mono.JunctionGenC` from the finiteness `Work.Drive.Mono.VertEdgeFinite` plus a margin
(`Submission/Work/Drive/Mono/NOTES_LEAD_gammaWitness.md` §4). -/
theorem edgeFree_of_margin (ψ : Submission.Diffeo) {s u h RF mE : ℝ}
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (v : LeanEval.KnotTheory.PardonDistortion.R3)
    (hRF : ∀ z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier, ‖z - c‖ ≤ RF)
    (hedge : ∀ z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier,
        |z (σ 0) - c (σ 0)| = Submission.boxSide 0 * s →
        |z (σ 1) - c (σ 1)| = Submission.boxSide 1 * s →
        mE ≤ |z (σ 2) - (c (σ 2) + u)|)
    (hver : h + ‖v - Work.BoxShrink.shiftVσ σ 1‖ * RF < mE)
    (hhor : h + ‖v - Work.BoxShrink.shiftVσ σ 1‖ * RF < Submission.boxSide 2 * s - |u|) :
    Work.Drive.Mono.EdgeFree ψ s c σ u v h := by
  -- The slab height of `z` decomposes as the *flat* height (the `σ 2`-coordinate, measured against
  -- the cutting plane) plus the tilt error `⟪v − e, z − c⟫`, where `e = shiftVσ σ 1` is the unit
  -- vector whose functional is the `σ 2`-coordinate.
  intro z hz _hbox hext
  obtain ⟨i, j, hij, hi, hj⟩ := hext
  have hdecomp : inner ℝ v z - (inner ℝ v c + u)
      = (z (σ 2) - (c (σ 2) + u))
        + inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c) := by
    have h1 : inner ℝ v z - (inner ℝ v c + u) = inner ℝ v (z - c) - u := by
      rw [inner_sub_right]; ring
    have h2 : inner ℝ v (z - c) = inner ℝ (Work.BoxShrink.shiftVσ σ 1) (z - c)
        + inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c) := by
      rw [← inner_add_left]; congr 1; abel
    have h3 : inner ℝ (Work.BoxShrink.shiftVσ σ 1) (z - c) = (z - c) (σ 2) := by
      rw [PiLp.inner_apply]; simp [Work.BoxShrink.shiftVσ_apply]
    have h4 : (z - c) (σ 2) = z (σ 2) - c (σ 2) := by rw [PiLp.sub_apply]
    rw [h1, h2, h3, h4]; ring
  -- The tilt error is bounded by `‖v − e‖ · RF` on the surface.
  have hbound : |z (σ 2) - (c (σ 2) + u)| - ‖v - Work.BoxShrink.shiftVσ σ 1‖ * RF
      ≤ |inner ℝ v z - (inner ℝ v c + u)| := by
    rw [hdecomp]
    have h1 : |inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c)|
        ≤ ‖v - Work.BoxShrink.shiftVσ σ 1‖ * ‖z - c‖ := abs_real_inner_le_norm _ _
    have h2 : ‖z - c‖ ≤ RF := hRF z hz
    have h3 : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * ‖z - c‖
        ≤ ‖v - Work.BoxShrink.shiftVσ σ 1‖ * RF :=
      mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    have h4 := abs_sub_abs_le_add (z (σ 2) - (c (σ 2) + u))
      (inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c))
    linarith
  -- Two cases for the pair `{i, j}` of extremal coordinates.
  by_cases h2 : i = 2 ∨ j = 2
  · -- A pair containing the *height* direction: a horizontal box edge, at flat height `±b₂ s`.
    have hz2 : |z (σ 2) - c (σ 2)| = Submission.boxSide 2 * s := by
      rcases h2 with hh | hh
      · rw [hh] at hi; exact hi
      · rw [hh] at hj; exact hj
    have hbase : Submission.boxSide 2 * s - |u| ≤ |z (σ 2) - (c (σ 2) + u)| := by
      have h5 := abs_sub_abs_le_sub (z (σ 2) - c (σ 2)) u
      rw [show z (σ 2) - c (σ 2) - u = z (σ 2) - (c (σ 2) + u) by ring, hz2] at h5
      exact h5
    linarith [hbound, hbase, hhor]
  · -- A pair of the two *horizontal* directions: a vertical box edge.  Since `i ≠ j` and neither
    -- is `2`, the pair is `{0, 1}`, exactly the hypothesis `hedge`.
    simp only [not_or] at h2
    obtain ⟨hi2, hj2⟩ := h2
    have hpairs : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
      fin_cases i <;> fin_cases j <;> simp_all
    rcases hpairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hmE := hedge z hz hi hj
      linarith [hbound, hmE, hver]
    · have hmE := hedge z hz hj hi
      linarith [hbound, hmE, hver]

end Work.Drive.Mono
