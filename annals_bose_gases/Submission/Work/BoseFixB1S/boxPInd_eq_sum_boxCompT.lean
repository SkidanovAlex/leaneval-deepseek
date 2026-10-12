import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxFlatAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators

/-- **Linearity of the box projection `Pⱼ` over a finite sum**: for a family of states which are
measurable and bounded on the analysis box, the slot mean of the sum is the sum of the slot means.
This is the `Finset`-indexed form of `BoxPotOper.boxPInd_add`; the integrability side conditions
come from `slotInt_of_bound`. -/
private theorem boxPInd_finsetSum_pt {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {ι : Type*} (s : Finset ι)
    (F : ι → Submission.BoseGases.X N → ℝ) (hF : ∀ p ∈ s, GoodState ℓ (F p))
    (j : Fin N) {x : Submission.BoseGases.X N} (hx : x ∈ Submission.BoseGases.abox N ℓ) :
    UBBInputs8.boxPInd volA A j (fun y => ∑ p ∈ s, F p y) x
      = ∑ p ∈ s, UBBInputs8.boxPInd volA A j (F p) x := by
  have hInt : (∫ z in A, (∑ p ∈ s, F p (Function.update x j z)))
      = ∑ p ∈ s, ∫ z in A, F p (Function.update x j z) :=
    MeasureTheory.integral_finsetSum s (fun p hp => by
      obtain ⟨hm, C, hb⟩ := hF p hp
      exact slotInt_of_bound hℓ hA hAc j x hx hm hb)
  simp only [UBBInputs8.boxPInd]
  rw [hInt, Finset.mul_sum, Finset.sum_mul]

theorem boxPInd_eq_sum_boxCompT {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) (j : Fin N) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A j Φ x
        = ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => j ∈ p.1),
            Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x := by
  intro x hx
  classical
  have hΦgood : GoodState ℓ Φ := goodState_of_continuous hℓ hΦc
  -- the joint components resolve `Φ` on the box
  have hdecomp : ∀ y ∈ Submission.BoseGases.abox N ℓ,
      Φ y = ∑ p ∈ disjPairs N, boxCompT volA A p.1 p.2 Φ y := by
    intro y hy
    have h := boxCompT_sum_eq hℓ hvol hA hvolA hAc hΦc y hy
    simpa [disjPairs] using h.symm
  -- each joint component is measurable and bounded on the box
  have hgood : ∀ p ∈ disjPairs N, GoodState ℓ (boxCompT volA A p.1 p.2 Φ) :=
    fun p _ => goodState_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦgood
  calc Work.UBBInputs8.boxPInd volA A j Φ x
      = UBBInputs8.boxPInd volA A j
          (fun y => ∑ p ∈ disjPairs N, boxCompT volA A p.1 p.2 Φ y) x :=
          agreeBox_boxPInd hA hAc j hdecomp x hx
    _ = ∑ p ∈ disjPairs N, UBBInputs8.boxPInd volA A j (boxCompT volA A p.1 p.2 Φ) x :=
          boxPInd_finsetSum_pt hℓ hA hAc (disjPairs N) _ hgood j hx
    _ = ∑ p ∈ disjPairs N,
          (if j ∈ p.1 then boxCompT volA A p.1 p.2 Φ x else 0) :=
          Finset.sum_congr rfl (fun p _ =>
            boxPInd_boxCompT hℓ hvol hA hvolA hAc p.1 p.2 hΦc j x hx)
    _ = ∑ p ∈ (disjPairs N).filter (fun p => j ∈ p.1), boxCompT volA A p.1 p.2 Φ x := by
          rw [Finset.sum_filter]

end Work.BoseFixB1S
