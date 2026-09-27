import Mathlib.MeasureTheory.Measure.Haar.Unique

open MeasureTheory Set
open scoped ENNReal

namespace Commons.Measure.RealEndgame

noncomputable section

/-- The real Lebesgue measure of a set shrinks by the factor `|c⁻¹|` when passing to the
preimage of the scaling map `x ↦ c * x` (for `c ≠ 0`). -/
private theorem measureReal_preimage_mul_left {c : ℝ} (hc : c ≠ 0) (s : Set ℝ) :
    (volume : Measure ℝ).real ((fun x : ℝ => c * x) ⁻¹' s) =
      |c⁻¹| * (volume : Measure ℝ).real s := by
  simp only [measureReal_def]
  rw [Real.volume_preimage_mul_left hc]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (abs_nonneg (c⁻¹ : ℝ))]

/-- The real Lebesgue measure is invariant under preimage by the reflection
`x ↦ 2 * π + (-x)` (i.e. `x ↦ 2 * π - x`). -/
private theorem measureReal_preimage_reflection_add (s : Set ℝ) (hs : MeasurableSet s) :
    (volume : Measure ℝ).real ((fun x : ℝ => 2 * Real.pi + (-x)) ⁻¹' s) =
      (volume : Measure ℝ).real s := by
  have hT : MeasurePreserving (fun x : ℝ => 2 * Real.pi + x) (volume : Measure ℝ)
      (volume : Measure ℝ) :=
    measurePreserving_add_left (volume : Measure ℝ) (2 * Real.pi)
  have hN : MeasurePreserving (fun x : ℝ => -x) (volume : Measure ℝ) (volume : Measure ℝ) :=
    Measure.measurePreserving_neg (volume : Measure ℝ)
  have hR : MeasurePreserving (fun x : ℝ => 2 * Real.pi + (-x)) (volume : Measure ℝ)
      (volume : Measure ℝ) :=
    hT.comp hN
  rw [measureReal_def, measureReal_def]
  rw [hR.measure_preimage hs.nullMeasurableSet]

theorem endgame_measure
    {A : Set ℝ}
    (hAmeas : MeasurableSet A)
    (hA01 : A ⊆ Set.Icc 0 (2 * Real.pi))
    (hAsym : ∀ ⦃x : ℝ⦄, x ∈ A → 2 * Real.pi - x ∈ A)
    (hvol : (2 * Real.pi / 3 : ℝ) ≤ (MeasureTheory.volume : MeasureTheory.Measure ℝ).real A) :
    (1 / 3 : ℝ) ≤ (MeasureTheory.volume : MeasureTheory.Measure ℝ).real
      {r : ℝ | 0 ≤ r ∧ r ≤ 1 ∧ Real.pi * r ∈ A} := by
  set B : Set ℝ := A ∩ Set.Icc 0 Real.pi with hB
  set C : Set ℝ := A ∩ Set.Icc Real.pi (2 * Real.pi) with hC
  set S : Set ℝ := {r : ℝ | 0 ≤ r ∧ r ≤ 1 ∧ Real.pi * r ∈ A} with hSdef
  change (1 / 3 : ℝ) ≤ (volume : Measure ℝ).real S
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hBmeas : MeasurableSet B := by
    rw [hB]
    exact hAmeas.inter measurableSet_Icc
  -- `C` (the right half of `A`) is the preimage of `B` (the left half) under the
  -- reflection about `π`, thanks to the symmetry hypothesis `hAsym`.
  have hCpre : C = (fun x : ℝ => 2 * Real.pi + (-x)) ⁻¹' B := by
    rw [hC, hB]
    ext x
    constructor
    · intro hx
      rw [mem_inter_iff, mem_Icc] at hx
      rcases hx with ⟨hxA, hπx, hx2π⟩
      rw [mem_preimage]
      rw [mem_inter_iff, mem_Icc]
      constructor
      · simpa [sub_eq_add_neg] using hAsym hxA
      constructor
      · linarith
      · linarith
    · intro hx
      rw [mem_preimage] at hx
      rw [mem_inter_iff, mem_Icc] at hx
      rcases hx with ⟨hmA, h0m, hmπ⟩
      rw [mem_inter_iff, mem_Icc]
      constructor
      · have hback : 2 * Real.pi - (2 * Real.pi + (-x)) ∈ A := hAsym hmA
        have hEq : 2 * Real.pi - (2 * Real.pi + (-x)) = x := by ring
        exact hEq ▸ hback
      constructor
      · linarith
      · linarith
  have hμC : (volume : Measure ℝ).real C = (volume : Measure ℝ).real B := by
    calc
      (volume : Measure ℝ).real C = (volume : Measure ℝ).real
        ((fun x : ℝ => 2 * Real.pi + (-x)) ⁻¹' B) := by rw [hCpre]
      _ = (volume : Measure ℝ).real B := measureReal_preimage_reflection_add B hBmeas
  -- `A ⊆ [0, 2 * π]` splits as the union of its left and right halves.
  have hAB : A = B ∪ C := by
    rw [hB, hC]
    ext x
    constructor
    · intro hxA
      have hxI : x ∈ Set.Icc 0 (2 * Real.pi) := hA01 hxA
      rw [mem_Icc] at hxI
      rcases hxI with ⟨h0, hx2π⟩
      rcases le_total x Real.pi with hxlo | hxhi
      · left
        rw [mem_inter_iff, mem_Icc]
        exact ⟨hxA, h0, hxlo⟩
      · right
        rw [mem_inter_iff, mem_Icc]
        exact ⟨hxA, hxhi, hx2π⟩
    · intro hx
      rcases hx with hB | hC
      · exact hB.1
      · exact hC.1
  -- By symmetry the two halves carry the same real measure, hence `A` carries at most
  -- twice the real measure of its left half `B`.
  have hineq : (volume : Measure ℝ).real A ≤ 2 * (volume : Measure ℝ).real B := by
    calc
      (volume : Measure ℝ).real A = (volume : Measure ℝ).real (B ∪ C) := by rw [hAB]
      _ ≤ (volume : Measure ℝ).real B + (volume : Measure ℝ).real C :=
        measureReal_union_le B C
      _ = 2 * (volume : Measure ℝ).real B := by rw [hμC]; ring
  have hBge : Real.pi / 3 ≤ (volume : Measure ℝ).real B := by
    nlinarith [hvol, hineq]
  -- `S` is exactly the preimage of `B` under the scaling `r ↦ π * r`.
  have hS : S = (fun r : ℝ => Real.pi * r) ⁻¹' B := by
    rw [hSdef, hB]
    ext r
    constructor
    · intro hr
      rcases hr with ⟨hr0, hr1, hrA⟩
      rw [mem_preimage]
      rw [mem_inter_iff, mem_Icc]
      constructor
      · exact hrA
      constructor
      · exact mul_nonneg (le_of_lt hpi_pos) hr0
      · have hle : Real.pi * r ≤ Real.pi * 1 :=
          mul_le_mul_of_nonneg_left hr1 (le_of_lt hpi_pos)
        simpa using hle
    · intro hr
      rw [mem_preimage] at hr
      rw [mem_inter_iff, mem_Icc] at hr
      rcases hr with ⟨hrA, h0, hπ⟩
      constructor
      · exact (mul_nonneg_iff_of_pos_left hpi_pos).mp h0
      constructor
      · have hle : Real.pi * r ≤ Real.pi * 1 := by simpa using hπ
        exact le_of_mul_le_mul_left hle hpi_pos
      · exact hrA
  -- Real measure of `S` equals `1 / π` times the real measure of `B`, which is ≥ 1/3.
  have hSpre : (volume : Measure ℝ).real S = |(Real.pi)⁻¹| * (volume : Measure ℝ).real B := by
    rw [hS]
    exact measureReal_preimage_mul_left (Real.pi_ne_zero) B
  have habs : |(Real.pi)⁻¹| = (Real.pi)⁻¹ := abs_of_pos (inv_pos.mpr hpi_pos)
  rw [hSpre, habs]
  calc
    (1 : ℝ) / 3 = (Real.pi)⁻¹ * (Real.pi / 3) := by field_simp [Real.pi_ne_zero]
    _ ≤ (Real.pi)⁻¹ * (volume : Measure ℝ).real B :=
      mul_le_mul_of_nonneg_left hBge (le_of_lt (inv_pos.mpr hpi_pos))

end

end Commons.Measure.RealEndgame