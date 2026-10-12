import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.qInd_pInd_sq_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.boxC1_add_cnPlus`

The `c₁`-normalisation identity of FS's `R_Ψ`-remainder: the box flat count
`Σᵢ∫(P_{B,i}Φ)²` plus the FS-faithful excited count `n₊(B) = Σᵢ∫(Q_{B,i}Φ)²`
equals the box mass `Σᵢ∫1_B(xᵢ)Φ²`.

This is the slot-by-slot Parseval splitting of the box mass for the orthogonal
decomposition `1_B(·ᵢ)·Φ = Q_{B,i}Φ + P_{B,i}Φ`, summed over the slots.  The
per-slot splitting is `Work.BoseFixB1S.qInd_pInd_sq_split`
(`∫(QᵢΦ)² + ∫(PᵢΦ)² = ∫(1_B(·ᵢ)Φ)²`), stated there under `0 < volA`; the
degenerate case `volA = 0` is handled separately here (then `1/volA = 0`, so
`PᵢΦ` vanishes identically and `QᵢΦ = 1_B(·ᵢ)Φ`).
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped Real BigOperators ENNReal

set_option maxHeartbeats 800000

/-- **Per-slot Parseval splitting**, in the orientation of `boxC1_add_cnPlus`:
`‖PᵢΦ‖² + ‖QᵢΦ‖² = ∫_{abox N ℓ} 1_A(xᵢ)·Φ²`, for a measurable `A ⊆ acube ℓ` of
(mass-normalised) volume `volA`, and continuous `Φ`.

The degenerate case `volA = 0` is the pointwise triviality `1/0 = 0`; for
`volA > 0` this is `Work.BoseFixB1S.qInd_pInd_sq_split` with the order of the two
summands reversed and the indicator absorbed into the square. -/
lemma boxPInd_sq_add_boxQInd_sq {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
      + (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2 := by
  have hnn : 0 ≤ volA := by
    rw [hvolA, ← MeasureTheory.Measure.real_def]
    exact MeasureTheory.measureReal_nonneg
  rcases lt_or_eq_of_le hnn with hpos | hzero
  · -- non-degenerate case: the orthogonal-projection splitting, re-oriented
    have hsplit := qInd_pInd_sq_split (N := N) (ℓ := ℓ) (volA := volA)
      hℓ hpos hA hvolA hAc i hΦc
    refine ((add_comm _ _).trans hsplit).trans ?_
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x i ∈ A
    · rw [Set.indicator_of_mem hx]; ring
    · rw [Set.indicator_of_notMem hx]; ring
  · -- degenerate case `volA = 0`: `PᵢΦ = 0` and `QᵢΦ = 1_A(·ᵢ)Φ` pointwise
    have hz : volA = 0 := hzero.symm
    have hP0 : ∀ x : Submission.BoseGases.X N, Work.UBBInputs8.boxPInd volA A i Φ x = 0 := by
      intro x
      simp only [Work.UBBInputs8.boxPInd, hz, div_zero, zero_mul]
    have hQ : ∀ x : Submission.BoseGases.X N,
        Work.UBBInputs8.boxQInd volA A i Φ x
          = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x := by
      intro x
      rw [Work.UBBInputs8.boxQInd, hP0 x, sub_zero]
    have e1 : (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) = 0 := by
      rw [show (fun x : Submission.BoseGases.X N =>
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) = fun _ => (0 : ℝ) from
          funext (fun x => by rw [hP0 x]; ring)]
      simp
    have e2 : (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2 := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hQ x]
      by_cases hx : x i ∈ A
      · rw [Set.indicator_of_mem hx]; ring
      · rw [Set.indicator_of_notMem hx]; ring
    rw [e1, e2, zero_add]

theorem boxC1_add_cnPlus {N : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (u : EuclideanSpace ℝ (Fin 3)) {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2)
      + Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) Φ
      = ∑ i : Fin N,
          ∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2 := by
  have hA : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    fun x hx => ((Submission.BoseGases.mem_dlBox_iff ℓ d u x).mp hx).1
  have hvolA : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  simp only [Work.UBBInputs8.cnPlusBoxInd]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl
    (fun i _ => boxPInd_sq_add_boxQInd_sq hℓ hA hvolA hAc i hΦc)

end Work.BoseFixB1S
