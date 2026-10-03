import Mathlib

namespace Work.FIArea3.JointCount

open MeasureTheory Set
open scoped ENNReal

/-- **Volume of a polar band.**  The set of complex numbers whose modulus lies in the annulus
`ρ₁ < ‖z‖ ≤ ρ₂` and whose argument lies in a measurable set `A ⊆ ℝ` has area equal to the radial
factor `(ρ₂² − ρ₁²)/2` times the (linear) measure of `A ∩ (-π, π)`.

The proof is the polar-coordinate change of variables `Complex.lintegral_comp_polarCoord_symm`
together with Fubini on the product `(0, ∞) × (-π, π)`. -/
theorem polarBand_volume (ρ₁ ρ₂ : ℝ) (A : Set ℝ) (hρ : 0 ≤ ρ₁) (hρ' : ρ₁ ≤ ρ₂)
    (hA : MeasurableSet A) :
    MeasureTheory.volume {z : ℂ | ρ₁ < ‖z‖ ∧ ‖z‖ ≤ ρ₂ ∧ Complex.arg z ∈ A}
      = ENNReal.ofReal ((ρ₂ ^ 2 - ρ₁ ^ 2) / 2
          * (MeasureTheory.volume (A ∩ Set.Ioo (-Real.pi) Real.pi)).toReal) := by
  set S : Set ℂ := {z | ρ₁ < ‖z‖ ∧ ‖z‖ ≤ ρ₂ ∧ Complex.arg z ∈ A} with hS
  set T : Set (ℝ × ℝ) := Complex.polarCoord.target with hT
  set P : Set ℝ := Set.Ioc ρ₁ ρ₂ with hP
  set Q : Set ℝ := A ∩ Set.Ioo (-Real.pi) Real.pi with hQ
  set B : Set (ℝ × ℝ) := P ×ˢ Q with hB
  have hSmeas : MeasurableSet S := by rw [hS]; measurability
  have hTmeas : MeasurableSet T := by
    rw [hT, Complex.polarCoord_target]; exact measurableSet_Ioi.prod measurableSet_Ioo
  have hBmeas : MeasurableSet B := by
    rw [hB, hP, hQ]; exact measurableSet_Ioc.prod (hA.inter measurableSet_Ioo)
  have hBT : B ⊆ T := by
    intro p hp
    rw [hB, hP, hQ, Set.mem_prod, Set.mem_Ioc, Set.mem_inter_iff] at hp
    rw [hT, Complex.polarCoord_target, Set.mem_prod, Set.mem_Ioo]
    exact ⟨lt_of_le_of_lt hρ hp.1.1, hp.2.2⟩
  have hsymm : ∀ p ∈ T, ‖Complex.polarCoord.symm p‖ = p.1 ∧
      Complex.arg (Complex.polarCoord.symm p) = p.2 := by
    intro p hp
    have h := OpenPartialHomeomorph.right_inv Complex.polarCoord hp
    rw [Complex.polarCoord_apply] at h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  have hpoint : ∀ p ∈ T, ENNReal.ofReal p.1 •
        (S.indicator (1 : ℂ → ℝ≥0∞)) (Complex.polarCoord.symm p)
      = B.indicator (fun q : ℝ × ℝ => ENNReal.ofReal q.1) p := by
    intro p hp
    obtain ⟨h1, h2⟩ := hsymm p hp
    have hp2 : p.2 ∈ Set.Ioo (-Real.pi) Real.pi := by
      rw [hT, Complex.polarCoord_target, Set.mem_prod] at hp; exact hp.2
    have hSiff : (Complex.polarCoord.symm p ∈ S) ↔ (ρ₁ < p.1 ∧ p.1 ≤ ρ₂ ∧ p.2 ∈ A) := by
      rw [hS, Set.mem_ofPred_eq, h1, h2]
    have hBiff : (p ∈ B) ↔ (ρ₁ < p.1 ∧ p.1 ≤ ρ₂ ∧ p.2 ∈ A) := by
      rw [hB, hP, hQ, Set.mem_prod, Set.mem_Ioc, Set.mem_inter_iff, Set.mem_Ioo]
      constructor
      · rintro ⟨⟨h1', h2'⟩, h3', -⟩; exact ⟨h1', h2', h3'⟩
      · rintro ⟨h1', h2', h3'⟩; exact ⟨⟨h1', h2'⟩, h3', hp2.1, hp2.2⟩
    by_cases hb : p ∈ B
    · have hs : Complex.polarCoord.symm p ∈ S := hSiff.mpr (hBiff.mp hb)
      simp only [Set.indicator_of_mem hs, Set.indicator_of_mem hb, Pi.one_apply, smul_eq_mul,
        mul_one]
    · have hs : Complex.polarCoord.symm p ∉ S := fun h => hb (hBiff.mpr (hSiff.mp h))
      simp only [Set.indicator_of_notMem hs, Set.indicator_of_notMem hb, smul_zero]
  have hCV : volume S = ∫⁻ p in T, ENNReal.ofReal p.1 •
        (S.indicator (1 : ℂ → ℝ≥0∞)) (Complex.polarCoord.symm p) := by
    rw [← MeasureTheory.lintegral_indicator_one hSmeas]
    exact (Complex.lintegral_comp_polarCoord_symm (S.indicator (1 : ℂ → ℝ≥0∞))).symm
  have h3 : ∫⁻ p in T, ENNReal.ofReal p.1 •
        (S.indicator (1 : ℂ → ℝ≥0∞)) (Complex.polarCoord.symm p)
      = ∫⁻ p in T, B.indicator (fun q : ℝ × ℝ => ENNReal.ofReal q.1) p :=
    MeasureTheory.setLIntegral_congr_fun hTmeas (fun p hp => hpoint p hp)
  have h4 : ∫⁻ p in T, B.indicator (fun q : ℝ × ℝ => ENNReal.ofReal q.1) p
      = ∫⁻ p in B, ENNReal.ofReal p.1 := by
    rw [MeasureTheory.lintegral_indicator hBmeas]
    rw [MeasureTheory.Measure.restrict_restrict_of_subset hBT]
  have h5 : ∫⁻ p in B, ENNReal.ofReal p.1
      = (∫⁻ r in P, ENNReal.ofReal r) * volume Q := by
    rw [hB]
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    rw [MeasureTheory.setLIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (s := P) (t := Q) (f := fun p : ℝ × ℝ => ENNReal.ofReal p.1) (by measurability)]
    simp only [MeasureTheory.setLIntegral_const]
    rw [MeasureTheory.lintegral_mul_const (volume Q) ENNReal.measurable_ofReal]
  have h6 : ∫⁻ r in P, ENNReal.ofReal r = ENNReal.ofReal ((ρ₂^2 - ρ₁^2)/2) := by
    rw [hP]
    have hint : IntegrableOn (fun x : ℝ => x) (Set.Ioc ρ₁ ρ₂) volume := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hρ']
      exact continuous_id.intervalIntegrable ρ₁ ρ₂
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc ρ₁ ρ₂)] (fun x : ℝ => x) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
      exact le_of_lt (lt_of_le_of_lt hρ hx.1)
    have hkey := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn
    rw [← hkey]
    congr 1
    rw [← intervalIntegral.integral_of_le hρ', integral_id]
  have hne_top : volume Q ≠ ⊤ := by
    have hle : volume Q ≤ volume (Set.Ioo (-Real.pi) Real.pi) := by
      rw [hQ]; exact measure_mono (Set.inter_subset_right)
    rw [← lt_top_iff_ne_top]
    exact lt_of_le_of_lt hle (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
  have ha : 0 ≤ (ρ₂^2 - ρ₁^2)/2 := by nlinarith [hρ, hρ']
  calc volume S
      = ENNReal.ofReal ((ρ₂^2 - ρ₁^2)/2) * volume Q := by rw [hCV, h3, h4, h5, h6]
    _ = ENNReal.ofReal ((ρ₂^2 - ρ₁^2)/2) * ENNReal.ofReal (volume Q).toReal := by
          rw [ENNReal.ofReal_toReal hne_top]
    _ = ENNReal.ofReal ((ρ₂^2 - ρ₁^2)/2 * (volume Q).toReal) := (ENNReal.ofReal_mul ha).symm

end Work.FIArea3.JointCount
