import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SlotWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SlotWord

open MeasureTheory

theorem abs_boxQInd_le_of_bound {N : ℕ} (L : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hAL : A ⊆ Submission.BoseGases.acube L) {volA : ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hfin : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) A < ⊤)
    {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : ∀ x : Submission.BoseGases.X N,
      (∀ j : Fin N, x j ∈ Submission.BoseGases.acube L) → |Ψ x| ≤ C)
    (i : Fin N) :
    ∀ x : Submission.BoseGases.X N, (∀ j : Fin N, x j ∈ Submission.BoseGases.acube L) →
      |Work.UBBInputs8.boxQInd volA A i Ψ x|
        ≤ C + |volA|⁻¹ * (C * (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A) := by
  intro x hx
  have hmem : ∀ z ∈ A, ∀ j : Fin N,
      Function.update x i z j ∈ Submission.BoseGases.acube L := by
    intro z hz j
    rw [Function.update_apply]
    by_cases hj : j = i
    · simp [hj, hAL hz]
    · simp [hj, hx j]
  have hgz : ∀ z ∈ A, |Ψ (Function.update x i z)| ≤ C := fun z hz => hΨ _ (hmem z hz)
  have hInt : |∫ z in A, Ψ (Function.update x i z)|
      ≤ C * (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A := by
    have h := norm_setIntegral_le_of_norm_le_const
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
      (f := fun z => Ψ (Function.update x i z)) (C := C) hfin
      (fun z hz => by simpa only [Real.norm_eq_abs] using hgz z hz)
    simpa only [Real.norm_eq_abs] using h
  have hCreal : 0 ≤ (MeasureTheory.volume :
      MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A := by
    rw [Measure.real_def]; exact ENNReal.toReal_nonneg
  have hRHS : 0 ≤ C + |volA|⁻¹ * (C * (MeasureTheory.volume :
      MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A) :=
    add_nonneg hC (mul_nonneg (inv_nonneg.mpr (abs_nonneg volA)) (mul_nonneg hC hCreal))
  rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
  by_cases hxi : x i ∈ A
  · have hu : A.indicator (fun _ => (1 : ℝ)) (x i) = 1 := Set.indicator_of_mem hxi _
    rw [hu, one_mul, mul_one]
    have h1 : |Ψ x| ≤ C := hΨ x hx
    have h2 : |(1 : ℝ) / volA| = |volA|⁻¹ := by rw [one_div, abs_inv]
    have h4 : |Ψ x - 1 / volA * (∫ z in A, Ψ (Function.update x i z))|
        ≤ |Ψ x| + |1 / volA * (∫ z in A, Ψ (Function.update x i z))| := by
      simpa [sub_eq_add_neg] using
        abs_add_le (Ψ x) (-(1 / volA * (∫ z in A, Ψ (Function.update x i z))))
    calc |Ψ x - 1 / volA * (∫ z in A, Ψ (Function.update x i z))|
        ≤ |Ψ x| + |1 / volA * (∫ z in A, Ψ (Function.update x i z))| := h4
      _ = |Ψ x| + |volA|⁻¹ * |∫ z in A, Ψ (Function.update x i z)| := by rw [abs_mul, h2]
      _ ≤ C + |volA|⁻¹ * (C * (MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A) :=
          add_le_add h1 (mul_le_mul_of_nonneg_left hInt (inv_nonneg.mpr (abs_nonneg volA)))
  · have hu : A.indicator (fun _ => (1 : ℝ)) (x i) = 0 := Set.indicator_of_notMem hxi _
    rw [hu, zero_mul, mul_zero, sub_zero, abs_zero]
    exact hRHS

end Work.SlotWord
