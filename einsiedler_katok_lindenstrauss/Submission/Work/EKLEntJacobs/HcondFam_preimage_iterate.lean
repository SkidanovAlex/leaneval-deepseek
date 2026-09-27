import Mathlib
import Submission.Work.EKLComp.Hpart.Hfam_join_chain

namespace Work.EKLEntJacobs

open MeasureTheory

/-- An invariant set under `T` is invariant under every iterate of `T`. -/
theorem preimage_iterate_eq_of_invariant {X : Type} [MeasurableSpace X] {κ : Type}
    {T : X → X} {B : κ → Set X} (hinv : ∀ j, T ⁻¹' B j = B j) (m : ℕ) (j : κ) :
    T^[m] ⁻¹' B j = B j := by
  rw [Set.preimage_iterate_eq]
  induction m with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, hinv j]

/-- Pulling back along an invariant set: `μ (T^[m] ⁻¹' A ∩ B) = μ (A ∩ B)`. -/
theorem measure_preimage_iterate_inter {X : Type} [MeasurableSpace X] (μ : Measure X)
    (T : X → X) (hmp : MeasurePreserving T μ μ) {A B : Set X} (hBinv : T ⁻¹' B = B)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (m : ℕ) :
    μ (T^[m] ⁻¹' A ∩ B) = μ (A ∩ B) := by
  have hBm := preimage_iterate_eq_of_invariant (κ := Unit) (fun _ => hBinv) m ()
  have hset : T^[m] ⁻¹' A ∩ B = T^[m] ⁻¹' (A ∩ B) := by
    rw [Set.preimage_inter, hBm]
  rw [hset, (hmp.iterate m).measure_preimage (hA.inter hB).nullMeasurableSet]

/-- Invariance of conditional entropy under `T^[m]` along an invariant partition `B`: if `T`
preserves the probability measure `μ` and each `B j` is `T`-invariant as a set (`T ⁻¹' B j = B j`),
then pulling a finite measurable partition `A` back along `T^[m]` does not change its conditional
entropy given the σ-algebra of `B`. Proof route: `T^[m] ⁻¹' B j = B j` by iterating the hypothesis,
so `T^[m] ⁻¹' A v ∩ B j = T^[m] ⁻¹' (A v ∩ B j)`, and
`μ (T^[m] ⁻¹' (A v ∩ B j)) = μ (A v ∩ B j)` by `MeasurePreserving.measure_preimage`
(`hmp.iterate m`); then both sides are identified by `HcondFam_partSigmaFam_eq`. -/
theorem HcondFam_preimage_iterate {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (T : X → X) (hmp : MeasureTheory.MeasurePreserving T μ μ)
    {κ θ : Type} [Fintype κ] [Fintype θ] {B : κ → Set X} (hB : Work.EKLComp.Core.IsMPart B)
    (hinv : ∀ j, T ⁻¹' B j = B j) {A : θ → Set X} (hA : Work.EKLComp.Core.IsMPart A) (m : ℕ) :
    Work.EKLComp.Core.HcondFam X μ (fun v : θ => T^[m] ⁻¹' A v) (Work.EKLComp.Core.partSigmaFam B) =
      Work.EKLComp.Core.HcondFam X μ A (Work.EKLComp.Core.partSigmaFam B) := by
  have hApull : Work.EKLComp.Core.IsMPart (fun v : θ => T^[m] ⁻¹' A v) :=
    ⟨fun v => (hA.measurable v).preimage (hmp.measurable.iterate m),
      fun i j hij => (hA.disjoint hij).preimage (T^[m]),
      by rw [← Set.preimage_iUnion, hA.cover, Set.preimage_univ]⟩
  rw [Work.EKLComp.Hpart.HcondFam_partSigmaFam_eq μ hApull hB,
    Work.EKLComp.Hpart.HcondFam_partSigmaFam_eq μ hA hB]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [measure_preimage_iterate_inter μ T hmp (hinv j) (hA.measurable i) (hB.measurable j) m]

end Work.EKLEntJacobs
