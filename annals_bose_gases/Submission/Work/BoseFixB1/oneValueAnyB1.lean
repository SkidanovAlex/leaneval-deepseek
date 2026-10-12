import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxQIndCore
import Submission.Work.BoseFixB1S.boxOneValueB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
noncomputable section
open MeasureTheory
namespace Work.BoseFixB1
open Work.BoseFixB1S
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
theorem oneValueAnyB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {i : Fin N}
    {w1 : (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ}

    {Ψ : Submission.BoseGases.X N → ℝ} :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2
          * Submission.BoseGases.w1Fibre ℓ w1 (x i))
      = (Work.BoseFixB1S.boxM1 ℓ A w1 / volA) *
        (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2) := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ n =>
    set F : Submission.BoseGases.X (n + 1) → ℝ :=
      fun x => (∫ z in A, Ψ (Function.update x i z)) ^ 2 with hFdef
    set h1 : EuclideanSpace ℝ (Fin 3) → ℝ :=
      fun z => A.indicator (fun _ => 1) z * Submission.BoseGases.w1Fibre ℓ w1 z with h1def
    set h2 : EuclideanSpace ℝ (Fin 3) → ℝ :=
      fun z => A.indicator (fun _ => 1) z with h2def
    set R : ℝ := ∫ y in Submission.BoseGases.abox n ℓ,
        F (Fin.insertNth i (0 : EuclideanSpace ℝ (Fin 3)) y) with hRdef
    have hindF : ∀ (x : Submission.BoseGases.X (n + 1))
        (z : EuclideanSpace ℝ (Fin 3)), F (Function.update x i z) = F x := by
      intro x z
      simp only [hFdef]
      have hEq : (fun z' : EuclideanSpace ℝ (Fin 3) =>
            Ψ (Function.update (Function.update x i z) i z'))
          = (fun z' => Ψ (Function.update x i z')) := by
        funext z'
        rw [Function.update_idem]
      simp only [hEq]
    have hpeel1 := peel_slot_aux (n := n) (ℓ := ℓ) i hindF h1
    have hpeel2 := peel_slot_aux (n := n) (ℓ := ℓ) i hindF h2
    have hmass1 : (∫ z in Submission.BoseGases.acube ℓ, h1 z) = boxM1 ℓ A w1 := by
      simp only [h1def]
      exact acube_indicator_w1_aux hA hAc
    have hmass2 : (∫ z in Submission.BoseGases.acube ℓ, h2 z) = volA := by
      simp only [h2def]
      exact acube_indicator_one_aux hA hvolA hAc
    have hpt1 : ∀ x : Submission.BoseGases.X (n + 1),
        (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2
            * Submission.BoseGases.w1Fibre ℓ w1 (x i)
          = (1 / volA) ^ 2 * (F x * h1 (x i)) := by
      intro x
      simp only [hFdef, h1def, Work.UBBInputs8.boxPInd]
      by_cases hx : x i ∈ A
      · simp only [Set.indicator_of_mem hx]
        ring
      · simp only [Set.indicator_of_notMem hx]
        ring
    have hpt2 : ∀ x : Submission.BoseGases.X (n + 1),
        (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2
          = (1 / volA) ^ 2 * (F x * h2 (x i)) := by
      intro x
      simp only [hFdef, h2def, Work.UBBInputs8.boxPInd]
      by_cases hx : x i ∈ A
      · simp only [Set.indicator_of_mem hx]
        ring
      · simp only [Set.indicator_of_notMem hx]
        ring
    have key1 : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2
            * Submission.BoseGases.w1Fibre ℓ w1 (x i))
        = (1 / volA) ^ 2 * (boxM1 ℓ A w1 * R) := by
      calc (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2
              * Submission.BoseGases.w1Fibre ℓ w1 (x i))
          = ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (1 / volA) ^ 2 * (F x * h1 (x i)) :=
            integral_congr_ae (Filter.Eventually.of_forall hpt1)
        _ = (1 / volA) ^ 2
              * (∫ x in Submission.BoseGases.abox (n + 1) ℓ, F x * h1 (x i)) :=
            integral_const_mul _ _
        _ = (1 / volA) ^ 2 * ((∫ z in Submission.BoseGases.acube ℓ, h1 z) * R) := by
            rw [hpeel1, ← hRdef]
        _ = (1 / volA) ^ 2 * (boxM1 ℓ A w1 * R) := by rw [hmass1]
    have key2 : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2)
        = (1 / volA) ^ 2 * (volA * R) := by
      calc (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2)
          = ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (1 / volA) ^ 2 * (F x * h2 (x i)) :=
            integral_congr_ae (Filter.Eventually.of_forall hpt2)
        _ = (1 / volA) ^ 2
              * (∫ x in Submission.BoseGases.abox (n + 1) ℓ, F x * h2 (x i)) :=
            integral_const_mul _ _
        _ = (1 / volA) ^ 2 * ((∫ z in Submission.BoseGases.acube ℓ, h2 z) * R) := by
            rw [hpeel2, ← hRdef]
        _ = (1 / volA) ^ 2 * (volA * R) := by rw [hmass2]
    rw [key1, key2]
    have hv : volA ≠ 0 := ne_of_gt hvol
    field_simp

end Work.BoseFixB1
