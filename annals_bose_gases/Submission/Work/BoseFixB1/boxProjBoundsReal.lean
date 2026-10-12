import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPIndFlat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

set_option maxHeartbeats 800000

/-! ## The two one-step bounds -/

/-- **`P_i` is a contraction on the box**: if `|Ψ| ≤ C` on `abox N ℓ` then so is `|P_i Ψ|`.
(No positivity of `volume A` is needed: when `volume A = 0` we have `1/volA = 0` and `P_i = 0`.) -/
theorem abs_boxPInd_le_real {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N) {Ψ : Submission.BoseGases.X N → ℝ}
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ C) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd (MeasureTheory.volume.real A) A i Ψ x| ≤ C := by
  intro x hx
  by_cases hv : MeasureTheory.volume.real A = 0
  · rw [Work.UBBInputs8.boxPInd, hv, div_zero, zero_mul, zero_mul, abs_zero]
    exact hC0
  · have hpos : 0 < MeasureTheory.volume.real A :=
      lt_of_le_of_ne MeasureTheory.measureReal_nonneg (Ne.symm hv)
    exact Work.BoseFixB1S.abs_boxPInd_le (volA := MeasureTheory.volume.real A)
      hℓ hpos hA rfl hAc i hC x hx

/-- **`Q_i` costs a factor two**: if `|Ψ| ≤ C` on `abox N ℓ` then `|Q_i Ψ| ≤ 2C` there. -/
theorem abs_boxQInd_le_real {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N) {Ψ : Submission.BoseGases.X N → ℝ}
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ C) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd (MeasureTheory.volume.real A) A i Ψ x| ≤ 2 * C := by
  intro x hx
  have hP := abs_boxPInd_le_real hℓ hA hAc i hC0 hC x hx
  have hind : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
    by_cases hxi : x i ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxi]
  have hmul : |A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x| ≤ C := by
    rw [abs_mul]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Ψ x| ≤ 1 * C :=
          mul_le_mul hind (hC x hx) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  have hQ : Work.UBBInputs8.boxQInd (MeasureTheory.volume.real A) A i Ψ x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
        - Work.UBBInputs8.boxPInd (MeasureTheory.volume.real A) A i Ψ x := rfl
  rw [hQ]
  calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
        - Work.UBBInputs8.boxPInd (MeasureTheory.volume.real A) A i Ψ x|
      ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x|
        + |Work.UBBInputs8.boxPInd (MeasureTheory.volume.real A) A i Ψ x| := abs_sub _ _
    _ ≤ C + C := add_le_add hmul hP
    _ = 2 * C := by ring

/-! ## The six rows -/

theorem boxProjBoundsReal {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} {C : ℝ}
    (hC : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ C) (i j : Fin N) :
    (∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxPInd (MeasureTheory.volume.real A) A i Φ x| ≤ C)
    ∧ (∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxQInd (MeasureTheory.volume.real A) A i Φ x| ≤ 2 * C)
    ∧ (∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxPInd (MeasureTheory.volume.real A) A i
          (Work.UBBInputs8.boxPInd (MeasureTheory.volume.real A) A j Φ) x| ≤ C)
    ∧ (∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxPInd (MeasureTheory.volume.real A) A i
          (Work.UBBInputs8.boxQInd (MeasureTheory.volume.real A) A j Φ) x| ≤ 2 * C)
    ∧ (∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxQInd (MeasureTheory.volume.real A) A i
          (Work.UBBInputs8.boxPInd (MeasureTheory.volume.real A) A j Φ) x| ≤ 2 * C)
    ∧ (∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxQInd (MeasureTheory.volume.real A) A i
          (Work.UBBInputs8.boxQInd (MeasureTheory.volume.real A) A j Φ) x| ≤ 4 * C) := by
  by_cases hne : (Submission.BoseGases.abox N ℓ).Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC x0 hx0)
    have hP : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxPInd (MeasureTheory.volume.real A) A k Φ x| ≤ C :=
      fun k => abs_boxPInd_le_real hℓ hA hAc k hC0 hC
    have hQ : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxQInd (MeasureTheory.volume.real A) A k Φ x| ≤ 2 * C :=
      fun k => abs_boxQInd_le_real hℓ hA hAc k hC0 hC
    refine ⟨hP i, hQ i, ?_, ?_, ?_, ?_⟩
    · exact abs_boxPInd_le_real hℓ hA hAc i hC0 (hP j)
    · exact abs_boxPInd_le_real hℓ hA hAc i (C := 2 * C) (by linarith) (hQ j)
    · exact abs_boxQInd_le_real hℓ hA hAc i hC0 (hP j)
    · have h := abs_boxQInd_le_real hℓ hA hAc i (C := 2 * C) (by linarith) (hQ j)
      intro x hx
      have h2 := h x hx
      linarith
  · have hempty : Submission.BoseGases.abox N ℓ = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro x hx <;> simp [hempty] at hx

end Work.BoseFixB1
