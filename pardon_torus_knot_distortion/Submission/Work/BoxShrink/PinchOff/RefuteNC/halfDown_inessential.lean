import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteNC.Config

/-!
# The lower half-region of the `RefuteNC` configuration is inessential

This module proves that at the `RefuteNC` configuration of the standard torus
(`ψ = id`, box radius `s = 1`, centre `c = (1, 19/10, 0)`, permutation `σ = (0 1 2)`, cutting
plane `{x = 1/2}`, i.e. `u = -1/2`) the **lower** half-region

  `Ω₋ = F ∩ PBox 1 c σ ∩ {y 0 < 1/2}`

carries no essential loop of the surface, equivalently that its winding span vanishes:

  `Work.BoxShrink.PinchOff.halfDown_inessential`.

The proof is the parameter-plane window criterion of `Work.BoxShrink.Pinch.Plane`
(`not_containsEssentialLoop_of_disjoint_windows`), in the same shape as the counterexample
`Work.BoxShrink.Pinch.BubbleHalfRefuted`: a point `(θ,φ)` of the parameter plane whose image is in
`Ω₋` satisfies

* `(2 + cos φ) sin θ ∈ (9/10, 29/10)` (the box's `y 1`-window),
* `1 - 2^{2/3} < (2 + cos φ) cos θ < 1/2` (the box's `y 0`-window together with the half-space
  `y 0 < 1/2`),

whence `sin θ ≠ 0` and, adding the squares of the two components of the vector
`(2 + cos φ)·(cos θ, sin θ)` of length `2 + cos φ`,

  `(2 + cos φ)² < (29/10)² + (3/5)² = 877/100 < (95/32)²`,

so `cos φ < 95/32 - 2 = 31/32`.  If `φ` were within `1/4` of a multiple of `2π` then Taylor's bound
would give `cos φ ≥ 1 - (1/4)²/2 = 31/32`, so `φ` lies in one of the intervals
`(2πl + 1/4, 2πl + 2π - 1/4)`, and `sin θ ≠ 0` places `θ` in one of the intervals
`(kπ, (k+1)π)`.  The products of these intervals are pairwise disjoint windows, covering the
preimage, whence the region is inessential.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff.RefuteNC

noncomputable section

/-! ## The elementary numeric bound `2^{2/3} < 8/5` -/

/-- `2^{2/3} < 8/5` (compare `(8/5)³ = 512/125 > 4 = (2^{2/3})³`). -/
theorem two_rpow_two_thirds_lt : (2 : ℝ) ^ (2 / 3 : ℝ) < 8 / 5 := by
  have h3 : ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hcube : ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 < ((8 : ℝ) / 5) ^ 3 := by
    rw [h3]; norm_num
  exact lt_of_pow_lt_pow_left₀ 3 (by positivity) hcube

/-! ## The coordinates of the preimage of the lower half-region -/

/-- **The four coordinate bounds of a parameter of the preimage** of
`Ω₋ = lowerRegion standard ncRad ncCtr ncCyc3 ncU`.  Reading `torusMap θ φ` in
`PBox ncRad ncCtr ncCyc3` (via `mem_PBox_nc`) and in `{y 0 < 1/2}` (the lower half-space of the
cutting plane) gives the two-sided bounds on the box's `y 1`-coordinate `(2 + cos φ) sin θ` and
on `(2 + cos φ) cos θ`. -/
theorem lowerRegion_preimage_bounds {q : ℝ × ℝ}
    (hq : q ∈ Work.BoxShrink.Pinch.planePreimage Work.CoreTopology.standard
      (Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard ncRad ncCtr ncCyc3 ncU)) :
    9 / 10 < (2 + Real.cos q.2) * Real.sin q.1 ∧
    (2 + Real.cos q.2) * Real.sin q.1 < 29 / 10 ∧
    1 - (2 : ℝ) ^ (2 / 3 : ℝ) < (2 + Real.cos q.2) * Real.cos q.1 ∧
    (2 + Real.cos q.2) * Real.cos q.1 < 1 / 2 := by
  rw [Work.BoxShrink.Pinch.mem_planePreimage, Work.BoxShrink.Core.mem_lowerRegion] at hq
  rw [Work.CoreTopology.standard_psi] at hq
  rw [Work.BoxShrink.PinchOff.mem_PBox_nc] at hq
  rw [Work.BoxShrink.PinchOff.ncCyc3_two, Work.BoxShrink.PinchOff.ncCtr_zero,
    Work.BoxShrink.PinchOff.ncU_eq] at hq
  rw [Work.Core.torusMap_apply_zero, Work.Core.torusMap_apply_one,
    Work.Core.torusMap_apply_two] at hq
  obtain ⟨-, ⟨h1, -, h3⟩, h4⟩ := hq
  rw [abs_lt] at h1 h3
  exact ⟨by linarith [h1.1], by linarith [h1.2], by linarith [h3.1], by linarith [h4]⟩

/-- **The first parameter of a point of the preimage of `Ω₋` is not a multiple of `π`**: the box
gives `(2 + cos φ) sin θ > 9/10 > 0`. -/
theorem sin_ne_zero_of_mem_planePreimage_lowerRegion {q : ℝ × ℝ}
    (hq : q ∈ Work.BoxShrink.Pinch.planePreimage Work.CoreTopology.standard
      (Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard ncRad ncCtr ncCyc3 ncU)) :
    Real.sin q.1 ≠ 0 := by
  intro h0
  obtain ⟨h1, -, -, -⟩ := lowerRegion_preimage_bounds hq
  rw [h0, mul_zero] at h1
  linarith

/-- **The key estimate**: `cos φ < 31/32` for a point `(θ,φ)` of the preimage of `Ω₋`. -/
theorem cos_lt_of_mem_planePreimage_lowerRegion {q : ℝ × ℝ}
    (hq : q ∈ Work.BoxShrink.Pinch.planePreimage Work.CoreTopology.standard
      (Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard ncRad ncCtr ncCyc3 ncU)) :
    Real.cos q.2 < 31 / 32 := by
  obtain ⟨h1, h2, h3, h4⟩ := lowerRegion_preimage_bounds hq
  set A := 2 + Real.cos q.2 with hA
  have hA1 : 1 ≤ A := by rw [hA]; linarith [Real.neg_one_le_cos q.2]
  have hApos : 0 < A := by linarith
  have hs : (A * Real.sin q.1) ^ 2 < (29 / 10) ^ 2 := by nlinarith [h1, h2]
  have hc : (A * Real.cos q.1) ^ 2 < (3 / 5) ^ 2 := by
    have hlt : (2 : ℝ) ^ (2 / 3 : ℝ) < 8 / 5 := two_rpow_two_thirds_lt
    have h5 : -(3 / 5) < A * Real.cos q.1 := by linarith
    have h6 : A * Real.cos q.1 < 3 / 5 := by linarith
    nlinarith [h5, h6]
  have hsq : Real.cos q.1 ^ 2 + Real.sin q.1 ^ 2 = 1 := Real.cos_sq_add_sin_sq q.1
  have hAsq : A ^ 2 < (95 / 32) ^ 2 := by
    nlinarith [hs, hc, hsq, sq_nonneg A]
  have hlt : A < 95 / 32 := by
    nlinarith [hAsq, hApos, sq_nonneg (A - 95 / 32), sq_nonneg (A + 95 / 32)]
  rw [hA] at hlt; linarith

/-! ## The windows -/

/-- **Taylor's bound at `1/4`**: if `φ` is within `1/4` of a multiple of `2π` then
`cos φ ≥ 1 - (1/4)²/2 = 31/32`. -/
theorem cos_ge_of_close_quarter {φ : ℝ} {l : ℤ} (h : |φ - l * (2 * Real.pi)| ≤ 1 / 4) :
    31 / 32 ≤ Real.cos φ := by
  have h1 : 1 - (φ - l * (2 * Real.pi)) ^ 2 / 2 ≤
      Real.cos (φ - l * (2 * Real.pi)) := Real.one_sub_sq_div_two_le_cos
  have h2 : Real.cos (φ - l * (2 * Real.pi)) = Real.cos φ := by
    have hh := Real.cos_add_int_mul_two_pi (φ - l * (2 * Real.pi)) l
    rw [show φ - l * (2 * Real.pi) + l * (2 * Real.pi) = φ by ring] at hh
    exact hh.symm
  have h3 : (φ - l * (2 * Real.pi)) ^ 2 ≤ (1 / 4) ^ 2 := by
    nlinarith [abs_le.mp h, abs_nonneg (φ - l * (2 * Real.pi))]
  rw [h2] at h1
  linarith

/-- **The `φ` window**: if `φ` avoids the `1/4`-neighbourhood of every multiple of `2π`, then it
lies in one of the intervals `(2πl + 1/4, 2πl + 2π - 1/4)`. -/
theorem exists_quarter_window (φ : ℝ) (h : ∀ l : ℤ, 1 / 4 < |φ - l * (2 * Real.pi)|) :
    ∃ l : ℤ, (l : ℝ) * (2 * Real.pi) + 1 / 4 < φ ∧
      φ < (l : ℝ) * (2 * Real.pi) + 2 * Real.pi - 1 / 4 := by
  have hπ : 0 < 2 * Real.pi := by positivity
  refine ⟨⌊φ / (2 * Real.pi)⌋, ?_, ?_⟩
  · have hle : ((⌊φ / (2 * Real.pi)⌋ : ℤ) : ℝ) ≤ φ / (2 * Real.pi) := Int.floor_le _
    have hmul : ((⌊φ / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) ≤ φ := by
      rw [le_div_iff₀ hπ] at hle; linarith
    have hlt := h ⌊φ / (2 * Real.pi)⌋
    rw [abs_of_nonneg (by linarith : 0 ≤ φ -
      ((⌊φ / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi))] at hlt
    linarith
  · have hlt : φ / (2 * Real.pi) < ((⌊φ / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have hmul : φ < (((⌊φ / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1) * (2 * Real.pi) := by
      rw [div_lt_iff₀ hπ] at hlt; linarith
    have hnext := h (⌊φ / (2 * Real.pi)⌋ + 1)
    have hval : φ - ((⌊φ / (2 * Real.pi)⌋ + 1 : ℤ) : ℝ) * (2 * Real.pi) < 0 := by
      push_cast at hmul ⊢; linarith
    rw [abs_of_neg hval] at hnext
    push_cast at hnext ⊢
    linarith

/-- The pairwise disjoint windows
`(kπ, (k+1)π) × (2πl + 1/4, 2πl + 2π - 1/4)` covering the preimage of `Ω₋`. -/
def quarterWindows : Set (Set (ℝ × ℝ)) :=
  {W | ∃ k l : ℤ, W = Set.Ioo ((k : ℝ) * Real.pi) (((k : ℝ) + 1) * Real.pi) ×ˢ
    Set.Ioo ((l : ℝ) * (2 * Real.pi) + 1 / 4)
      ((l : ℝ) * (2 * Real.pi) + 2 * Real.pi - 1 / 4)}

theorem mem_quarterWindows {W : Set (ℝ × ℝ)} :
    W ∈ quarterWindows ↔ ∃ k l : ℤ,
      W = Set.Ioo ((k : ℝ) * Real.pi) (((k : ℝ) + 1) * Real.pi) ×ˢ
        Set.Ioo ((l : ℝ) * (2 * Real.pi) + 1 / 4)
          ((l : ℝ) * (2 * Real.pi) + 2 * Real.pi - 1 / 4) := Iff.rfl

theorem isWindow_quarterWindows (W : Set (ℝ × ℝ)) (hW : W ∈ quarterWindows) : Work.BoxShrink.Pinch.IsWindow W := by
  obtain ⟨k, l, rfl⟩ := mem_quarterWindows.mp hW
  refine Work.BoxShrink.Pinch.isWindow_Ioo ?_ ?_
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos]

theorem isOpen_quarterWindows (W : Set (ℝ × ℝ)) (hW : W ∈ quarterWindows) : IsOpen W := by
  obtain ⟨k, l, rfl⟩ := mem_quarterWindows.mp hW
  exact isOpen_Ioo.prod isOpen_Ioo

theorem pairwiseDisjoint_quarterWindows : quarterWindows.Pairwise Disjoint := by
  rintro W hW W' hW' hne
  obtain ⟨k, l, rfl⟩ := mem_quarterWindows.mp hW
  obtain ⟨k', l', rfl⟩ := mem_quarterWindows.mp hW'
  rcases eq_or_ne k k' with rfl | hk
  · rcases eq_or_ne l l' with rfl | hl
    · exact absurd rfl hne
    · rw [Set.disjoint_left]
      intro q hq hq'
      obtain ⟨-, hq2⟩ := hq
      obtain ⟨-, hq2'⟩ := hq'
      rcases lt_or_gt_of_ne hl with h | h
      · have hcast : (l : ℝ) + 1 ≤ (l' : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h
        nlinarith [Real.pi_pos, hq2.2, hq2'.1]
      · have hcast : (l' : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h
        nlinarith [Real.pi_pos, hq2'.2, hq2.1]
  · rw [Set.disjoint_left]
    intro q hq hq'
    obtain ⟨hq1, -⟩ := hq
    obtain ⟨hq1', -⟩ := hq'
    rcases lt_or_gt_of_ne hk with h | h
    · have hcast : (k : ℝ) + 1 ≤ (k' : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h
      nlinarith [Real.pi_pos, hq1.2, hq1'.1]
    · have hcast : (k' : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h
      nlinarith [Real.pi_pos, hq1'.2, hq1.1]

/-! ## The preimage is covered by the windows -/

theorem planePreimage_lowerRegion_subset :
    Work.BoxShrink.Pinch.planePreimage Work.CoreTopology.standard
      (Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard ncRad ncCtr ncCyc3 ncU)
      ⊆ ⋃₀ quarterWindows := by
  intro q hq
  have hcos : Real.cos q.2 < 31 / 32 := cos_lt_of_mem_planePreimage_lowerRegion hq
  have hsin : Real.sin q.1 ≠ 0 := sin_ne_zero_of_mem_planePreimage_lowerRegion hq
  obtain ⟨k, hk1, hk2⟩ := Work.BoxShrink.Pinch.exists_int_window q.1 hsin
  have hfar : ∀ l : ℤ, 1 / 4 < |q.2 - l * (2 * Real.pi)| := fun l =>
    lt_of_not_ge (fun hle => absurd (cos_ge_of_close_quarter hle) (not_le.mpr hcos))
  obtain ⟨l, hl1, hl2⟩ := exists_quarter_window q.2 hfar
  exact mem_sUnion.mpr ⟨_, ⟨k, l, rfl⟩, ⟨hk1, hk2⟩, ⟨hl1, hl2⟩⟩

/-! ## The lower half-region is inessential -/

theorem not_containsEssentialLoop_lowerRegion :
    ¬ Work.CoreTopology.standard.ContainsEssentialLoop
      (Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard ncRad ncCtr ncCyc3 ncU) :=
  Work.BoxShrink.Pinch.not_containsEssentialLoop_of_disjoint_windows _ quarterWindows
    isWindow_quarterWindows isOpen_quarterWindows pairwiseDisjoint_quarterWindows
    planePreimage_lowerRegion_subset

theorem halfDown_inessential :
    Work.SurgeryInvariance.WindingSpan (Work.BoxShrink.PinchOff.surface Work.BoxShrink.PinchOff.idDiffeo)
      (Work.BoxShrink.PinchOff.HalfDown Work.BoxShrink.PinchOff.idDiffeo
        Work.BoxShrink.PinchOff.ncRad Work.BoxShrink.PinchOff.ncCtr
        Work.BoxShrink.PinchOff.ncCyc3 Work.BoxShrink.PinchOff.ncU) = ⊥ := by
  rw [Work.BoxShrink.PinchOff.surface_idDiffeo_eq_standard]
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  exact not_containsEssentialLoop_lowerRegion

end

end Work.BoxShrink.PinchOff.RefuteNC
