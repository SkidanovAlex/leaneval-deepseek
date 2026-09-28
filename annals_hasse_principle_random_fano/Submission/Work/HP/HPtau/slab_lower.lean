import Mathlib

namespace Work.HP.HPtau

open MeasureTheory
open scoped ENNReal

/-- A measurable set in `ℝ × (Fin n → ℝ)` whose vertical sections are controlled on the box
`|z j| ≤ A`, with a vertical interval of length `2δ` for every point of that box, has measure at
least `2δ * (2A)^n`.

Route: Tonelli on `S` (`Measure.prod_apply_symm`) gives `volume S = ∫⁻ z, volume {t | (t,z) ∈ S} ∂z`;
each section over the box `{z | ∀ j, |z j| ≤ A}` has measure at least `2δ` (`Real.volume_Icc`,
`measure_mono`); the box has measure `(2A)^n` (`volume_pi_pi`, `Real.volume_Icc`). Do not try to make
`z ↦ t₀` measurable. -/
theorem slab_lower (n : ℕ) (S : Set (ℝ × (Fin n → ℝ))) (hS : MeasurableSet S)
    (A δ : ℝ) (hA : 0 < A) (hδ : 0 < δ)
    (hsec : ∀ z : Fin n → ℝ, (∀ j, |z j| ≤ A) → ∃ t₀ : ℝ, ∀ t : ℝ, |t - t₀| ≤ δ → (t, z) ∈ S) :
    ENNReal.ofReal (2 * δ) * (ENNReal.ofReal (2 * A)) ^ n ≤
      (MeasureTheory.volume : MeasureTheory.Measure (ℝ × (Fin n → ℝ))) S := by
  set B : Set (Fin n → ℝ) := Set.univ.pi (fun _ : Fin n => Set.Icc (-A) A) with hB
  have hBmem : ∀ z, z ∈ B ↔ ∀ j, |z j| ≤ A := by
    intro z; rw [hB]; simp only [Set.mem_univ_pi, Set.mem_Icc, abs_le]
  have hBmeas : MeasurableSet B := by
    rw [hB]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  -- Pointwise lower bound on the vertical section over each point of the box.
  have hpoint : ∀ z : Fin n → ℝ,
      B.indicator (fun _ => ENNReal.ofReal (2 * δ)) z ≤
        volume ((fun t : ℝ => (t, z)) ⁻¹' S) := by
    intro z
    by_cases hz : z ∈ B
    · rw [Set.indicator_of_mem hz]
      obtain ⟨t₀, ht₀⟩ := hsec z ((hBmem z).mp hz)
      calc ENNReal.ofReal (2 * δ)
          = volume (Set.Icc (t₀ - δ) (t₀ + δ)) := by
            rw [Real.volume_Icc]; congr 1; ring
        _ ≤ volume ((fun t : ℝ => (t, z)) ⁻¹' S) := by
            apply measure_mono
            intro t ht
            exact ht₀ t (by rw [abs_le]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    · rw [Set.indicator_of_notMem hz]; simp
  -- Tonelli: the volume is the integral of the vertical section measures.
  have hvol : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × (Fin n → ℝ))) S
      = ∫⁻ z, volume ((fun t : ℝ => (t, z)) ⁻¹' S) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ (Fin n → ℝ)]
    exact Measure.prod_apply_symm hS
  rw [hvol]
  calc ENNReal.ofReal (2 * δ) * (ENNReal.ofReal (2 * A)) ^ n
      = ENNReal.ofReal (2 * δ) * volume B := by
          congr 1
          rw [hB, volume_pi_pi]
          rw [show (∏ i : Fin n, volume (Set.Icc (-A) A))
                = (ENNReal.ofReal (2 * A)) ^ n from by
              rw [show (∏ i : Fin n, volume (Set.Icc (-A) A))
                    = ∏ _i : Fin n, ENNReal.ofReal (2 * A) from by
                  apply Finset.prod_congr rfl; intro i _; rw [Real.volume_Icc]; congr 1; ring]
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
    _ = ∫⁻ z, B.indicator (fun _ => ENNReal.ofReal (2 * δ)) z := by
          rw [lintegral_indicator_const hBmeas]
    _ ≤ ∫⁻ z, volume ((fun t : ℝ => (t, z)) ⁻¹' S) := lintegral_mono hpoint

end Work.HP.HPtau
