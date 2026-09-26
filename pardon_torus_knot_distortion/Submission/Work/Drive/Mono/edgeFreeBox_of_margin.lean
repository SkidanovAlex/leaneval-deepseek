import Mathlib
import Submission.Work.Drive.Mono.EdgeFreeBox
import Submission.Work.Drive.Mono.edgeFree_of_margin
import Submission.Work.Drive.Mono.BoxWidth

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open scoped RealInnerProductSpace

noncomputable section

/-- **Points of the box sphere are within `5 s / 2` of the centre.**  A point with `boxNorm = s`
has each coordinate `σ i` bounded by `boxSide i * s` in absolute value; summing the squares and using
`∑ boxSide i ^ 2 < 25 / 4` bounds the distance by `5 s / 2`. -/
private theorem norm_sub_le_of_boxNorm_eq {s : ℝ} (hs : 0 < s) {c : R3}
    {σ : Equiv.Perm (Fin 3)} {z : R3} (hz : Submission.boxNorm c σ z = s) :
    ‖z - c‖ ≤ 5 / 2 * s := by
  have hle : ∀ i : Fin 3, |z (σ i) - c (σ i)| ≤ Submission.boxSide i * s := by
    intro i
    have h1 : |z (σ i) - c (σ i)| / Submission.boxSide i ≤ Submission.boxNorm c σ z := by
      rw [Submission.boxNorm]
      fin_cases i
      · exact le_trans (le_max_left _ _) (le_max_left _ _)
      · exact le_trans (le_max_right _ _) (le_max_left _ _)
      · exact le_max_right _ _
    rw [hz, div_le_iff₀ (Submission.boxSide_pos i)] at h1
    simpa [mul_comm] using h1
  have hnorm : ‖z - c‖ ^ 2 = ∑ i : Fin 3, (z i - c i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => by rw [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  have hcoord : ∀ i : Fin 3, (z i - c i) ^ 2 ≤ (Submission.boxSide (σ.symm i) * s) ^ 2 := by
    intro i
    have hh := hle (σ.symm i)
    simp only [Equiv.apply_symm_apply] at hh
    calc (z i - c i) ^ 2 = |z i - c i| ^ 2 := (sq_abs _).symm
      _ ≤ (Submission.boxSide (σ.symm i) * s) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hh 2
  have hsum : ∑ i : Fin 3, (z i - c i) ^ 2
      ≤ ∑ i : Fin 3, (Submission.boxSide (σ.symm i) * s) ^ 2 :=
    Finset.sum_le_sum fun i _ => hcoord i
  have hperm : ∑ i : Fin 3, (Submission.boxSide (σ.symm i) * s) ^ 2
      = (∑ i : Fin 3, Submission.boxSide i ^ 2) * s ^ 2 := by
    rw [Equiv.sum_comp σ.symm (fun i => (Submission.boxSide i * s) ^ 2), Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsq : ‖z - c‖ ^ 2 ≤ ((5 / 2) * s) ^ 2 := by
    rw [hnorm]
    rw [hperm] at hsum
    nlinarith [hsum, Submission.sum_boxSide_sq_lt, le_of_lt hs]
  have hpos : 0 < (5 / 2) * s := by linarith
  nlinarith [norm_nonneg (z - c), hsq, hpos]

/-- The elementary estimate `|a| - |b| ≤ |a - b|`. -/
private theorem abs_sub_abs_le_sub' (a b : ℝ) : |a| - |b| ≤ |a - b| := by
  have h2 : (a - b) + b = a := by ring
  have h : |a| ≤ |a - b| + |b| := by
    calc |a| = |(a - b) + b| := by rw [h2]
      _ ≤ |a - b| + |b| := abs_add_le _ _
  linarith

/-- The elementary estimate `|a| - |b| ≤ |a + b|`. -/
private theorem abs_sub_abs_le_add' (a b : ℝ) : |a| - |b| ≤ |a + b| := by
  have h := abs_sub_abs_le_sub' a (-b)
  rw [sub_neg_eq_add, abs_neg] at h
  exact h

/-- **`EdgeFreeBox` from the margin of the edge locus, with the carrier radius free.**  If the edge
locus (two extremal box coordinates) keeps the height `z ↦ z (σ 2) − (c (σ 2) + u)` at distance at
least `mE > 0` from `0`, and the half-width plus the tilt error stays strictly below both `mE` and the
horizontal margin `boxSide 2 · s − |u|`, referred to the *box* radius `5 s / 2` rather than to the
radius of the whole carrier, then the closed tilted slab misses the edge locus **on the closed box**
(`Work.Drive.Mono.EdgeFreeBox`).

This is `Work.Drive.Mono.edgeFree_of_margin` with the carrier radius `RF` replaced by its bound
`‖z − c‖ ≤ 5 s / 2` on the closed box, which is exactly what the lead's 20:5x ruling prescribes: the
unrestricted `Work.Drive.Mono.EdgeFree` is not producible (its extended edge lines carry points
arbitrarily far from `c`), while every consumer evaluates it only at box points. -/
theorem edgeFreeBox_of_margin (ψ : Submission.Diffeo) {s u h mE : ℝ}
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (v : LeanEval.KnotTheory.PardonDistortion.R3) (hs : 0 < s)
    (hedge : ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      |z (σ 0) - c (σ 0)| = Submission.boxSide 0 * s →
      |z (σ 1) - c (σ 1)| = Submission.boxSide 1 * s →
      mE ≤ |z (σ 2) - (c (σ 2) + u)|)
    (hver : h + ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) < mE)
    (hhor : h + ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) <
      Submission.boxSide 2 * s - |u|) :
    Work.Drive.Mono.EdgeFreeBox ψ s c σ u v h := by
  -- The slab height of `z` decomposes as the *flat* height (the `σ 2`-coordinate, measured against
  -- the cutting plane) plus the tilt error `⟪v − e, z − c⟫`, where `e = shiftVσ σ 1` is the unit
  -- vector whose functional is the `σ 2`-coordinate.
  intro z hz hzbox hext
  obtain ⟨i, j, hij, hi, hj⟩ := hext
  -- The radius bound on the closed box.
  have hR : ‖z - c‖ ≤ 5 / 2 * s := norm_sub_le_of_boxNorm_eq hs hzbox
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
  -- The tilt error is bounded by `‖v − e‖ · (5 s / 2)` on the closed box.
  have hbound : |z (σ 2) - (c (σ 2) + u)| - ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s)
      ≤ |inner ℝ v z - (inner ℝ v c + u)| := by
    rw [hdecomp]
    have h1 : |inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c)|
        ≤ ‖v - Work.BoxShrink.shiftVσ σ 1‖ * ‖z - c‖ := abs_real_inner_le_norm _ _
    have h3 : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * ‖z - c‖
        ≤ ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) :=
      mul_le_mul_of_nonneg_left hR (norm_nonneg _)
    have h4 := abs_sub_abs_le_add' (z (σ 2) - (c (σ 2) + u))
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
      have h5 := abs_sub_abs_le_sub' (z (σ 2) - c (σ 2)) u
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

end

end Work.Drive.Mono
