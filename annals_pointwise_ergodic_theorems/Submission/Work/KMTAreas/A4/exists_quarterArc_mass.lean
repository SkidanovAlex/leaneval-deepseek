import Mathlib
import Submission.Work.KMTAreas.A4.lip2Defs

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-!
# Two quarter arcs cover the frequency circle

For a non-negative integrable function `φ` on the frequency circle `ℝ/ℤ`, one of the two quarter
arcs centred at `0` and at `1/2` carries at least half of the total mass of `φ`.

Both halves of the argument are elementary:

* *geometry*: `arcSet 0 (1/4) ∪ arcSet (1/2) (1/4) = univ` — every point of the circle is at
  distance at most `1/4` from `0` or from `1/2` (the representatives of the circle in
  `[-1/2, 1/2]` are used);
* *measure theory*: `∫ φ ≤ ∫_{A∪B} φ ≤ ∫_A φ + ∫_B φ` for non-negative `φ`, since
  `1_{A∪B} ≤ 1_A + 1_B` pointwise.
-/

/-- `arcSet α r` is measurable: it is the image of the compact interval `[-r,r]` under the
continuous map `θ ↦ α + θ`. -/
theorem arcSet_measurable (α : FreqCircle) (r : ℝ) : MeasurableSet (arcSet α r) := by
  have hcont : Continuous (fun θ : ℝ => α + ((θ : ℝ) : FreqCircle)) :=
    continuous_const.add (AddCircle.continuous_mk' (1 : ℝ))
  have himg : arcSet α r = (fun θ : ℝ => α + ((θ : ℝ) : FreqCircle)) '' Set.Icc (-r) r := by
    ext γ
    simp only [mem_arcSet, Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      exact ⟨θ, ⟨by linarith [neg_abs_le θ, (abs_le.mp hθ).1], (abs_le.mp hθ).2⟩, rfl⟩
    · rintro ⟨θ, ⟨h1, h2⟩, rfl⟩
      exact ⟨θ, abs_le.mpr ⟨by linarith, h2⟩, rfl⟩
  rw [himg]
  exact (isCompact_Icc.image hcont).measurableSet

/-- The two quarter arcs centred at `0` and at `1/2` cover the frequency circle. -/
theorem arcSet_zero_quarter_union_half_quarter :
    arcSet (0 : FreqCircle) (1 / 4) ∪ arcSet (((1 : ℝ) / 2 : ℝ) : FreqCircle) (1 / 4)
      = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro γ
  -- every point of the circle has a representative in `[-1/2, 1/2]`
  have hcoe : ((↑) : ℝ → FreqCircle) '' Set.Icc (-(1 / 2) : ℝ) (-(1 / 2) + 1) = Set.univ :=
    AddCircle.coe_image_Icc_eq (1 : ℝ) (-(1 / 2) : ℝ)
  have hmem : γ ∈ ((↑) : ℝ → FreqCircle) '' Set.Icc (-(1 / 2) : ℝ) (-(1 / 2) + 1) := by
    rw [hcoe]; exact Set.mem_univ γ
  obtain ⟨x, hx, hxγ⟩ := hmem
  have hx1 : -(1 / 2 : ℝ) ≤ x := hx.1
  have hx2 : x ≤ 1 / 2 := by linarith [hx.2]
  rw [Set.mem_union, mem_arcSet, mem_arcSet]
  rcases lt_or_ge (1 / 4) |x| with hlt | hle
  · rw [lt_abs] at hlt
    rcases hlt with hpos | hneg
    · -- `x ∈ (1/4, 1/2]`, so `x` is within `1/4` of `1/2`
      right
      refine ⟨x - 1 / 2, ?_, ?_⟩
      · rw [abs_of_nonpos (by linarith)]
        linarith
      · rw [← hxγ, ← AddCircle.coe_add]
        congr 1
        ring
    · -- `x ∈ [-1/2, -1/4)`, so `x` is within `1/4` of `-1/2 ≡ 1/2`
      right
      refine ⟨x + 1 / 2, ?_, ?_⟩
      · rw [abs_of_nonneg (by linarith)]
        linarith
      · rw [← hxγ, ← AddCircle.coe_add]
        rw [show (1 / 2 : ℝ) + (x + 1 / 2) = x + 1 from by ring]
        rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]
  · -- `|x| ≤ 1/4`: `x` is within `1/4` of `0`
    left
    exact ⟨x, hle, by rw [zero_add]; exact hxγ.symm⟩

/-- For a non-negative integrable `φ`, the total mass is at most the sum of the masses of the two
quarter arcs. -/
theorem half_le_union_arc_mass {μ : MeasureTheory.Measure FreqCircle} {φ : FreqCircle → ℝ}
    (hφ0 : ∀ ξ, 0 ≤ φ ξ) (hφi : MeasureTheory.Integrable φ μ) :
    ∫ ξ, φ ξ ∂μ ≤
      (∫ ξ in arcSet (0 : FreqCircle) (1 / 4), φ ξ ∂μ) +
        (∫ ξ in arcSet (((1 : ℝ) / 2 : ℝ) : FreqCircle) (1 / 4), φ ξ ∂μ) := by
  set A := arcSet (0 : FreqCircle) (1 / 4) with hA
  set B := arcSet (((1 : ℝ) / 2 : ℝ) : FreqCircle) (1 / 4) with hB
  have hAmeas : MeasurableSet A := by rw [hA]; exact arcSet_measurable _ _
  have hBmeas : MeasurableSet B := by rw [hB]; exact arcSet_measurable _ _
  have hcover : A ∪ B = Set.univ := by
    rw [hA, hB]; exact arcSet_zero_quarter_union_half_quarter
  have hI1 : MeasureTheory.Integrable ((A ∪ B).indicator φ) μ :=
    hφi.indicator (hAmeas.union hBmeas)
  have hI2 : MeasureTheory.Integrable ((A.indicator φ) + (B.indicator φ)) μ :=
    (hφi.indicator hAmeas).add (hφi.indicator hBmeas)
  have hpt : (A ∪ B).indicator φ ≤ (A.indicator φ) + (B.indicator φ) := by
    intro ξ
    simp only [Pi.add_apply]
    by_cases h1 : ξ ∈ A
    · rw [Set.indicator_of_mem (Set.mem_union_left B h1) φ, Set.indicator_of_mem h1 φ]
      have hnn : 0 ≤ B.indicator φ ξ := Set.indicator_nonneg (fun _ _ => hφ0 _) ξ
      linarith
    · by_cases h2 : ξ ∈ B
      · rw [Set.indicator_of_mem (Set.mem_union_right A h2) φ, Set.indicator_of_mem h2 φ]
        have hnn : 0 ≤ A.indicator φ ξ := Set.indicator_nonneg (fun _ _ => hφ0 _) ξ
        linarith
      · have hnot : ξ ∉ A ∪ B := by simp [h1, h2]
        rw [Set.indicator_of_notMem hnot φ, Set.indicator_of_notMem h1 φ,
          Set.indicator_of_notMem h2 φ]
        norm_num
  calc ∫ ξ, φ ξ ∂μ
      = ∫ ξ in A ∪ B, φ ξ ∂μ := by rw [hcover, MeasureTheory.setIntegral_univ]
    _ = ∫ ξ, (A ∪ B).indicator φ ξ ∂μ :=
        (MeasureTheory.integral_indicator (hAmeas.union hBmeas)).symm
    _ ≤ ∫ ξ, (A.indicator φ ξ + B.indicator φ ξ) ∂μ :=
        MeasureTheory.integral_mono hI1 hI2 hpt
    _ = ∫ ξ, A.indicator φ ξ ∂μ + ∫ ξ, B.indicator φ ξ ∂μ :=
        MeasureTheory.integral_add (hφi.indicator hAmeas) (hφi.indicator hBmeas)
    _ = ∫ ξ in A, φ ξ ∂μ + ∫ ξ in B, φ ξ ∂μ := by
        rw [MeasureTheory.integral_indicator hAmeas, MeasureTheory.integral_indicator hBmeas]

theorem exists_quarterArc_mass {φ : Work.Analysis.InverseTheory.FreqCircle → ℝ}
    (hφ0 : ∀ ξ, 0 ≤ φ ξ) (hφi : MeasureTheory.Integrable φ AddCircle.haarAddCircle) :
    ∃ α : Work.Analysis.InverseTheory.FreqCircle,
      (α = 0 ∨ α = (((1 : ℝ) / 2 : ℝ) : Work.Analysis.InverseTheory.FreqCircle)) ∧
      (∫ ξ, φ ξ ∂AddCircle.haarAddCircle) / 2 ≤
        ∫ ξ in Work.KMTAreas.A4.arcSet α (1 / 4), φ ξ ∂AddCircle.haarAddCircle := by
  have hkey := half_le_union_arc_mass (μ := AddCircle.haarAddCircle) hφ0 hφi
  by_cases h : (∫ ξ, φ ξ ∂AddCircle.haarAddCircle) / 2 ≤
      ∫ ξ in arcSet (0 : FreqCircle) (1 / 4), φ ξ ∂AddCircle.haarAddCircle
  · exact ⟨0, Or.inl rfl, h⟩
  · rw [not_le] at h
    refine ⟨(((1 : ℝ) / 2 : ℝ) : FreqCircle), Or.inr rfl, ?_⟩
    linarith

end Work.KMTAreas.A4
