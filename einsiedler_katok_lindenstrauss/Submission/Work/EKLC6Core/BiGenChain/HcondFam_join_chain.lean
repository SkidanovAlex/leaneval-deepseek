import Mathlib
import Submission.Work.EKLC6Core.BiGenChain.Basic
import Submission.Work.EKLC6Core.HcondFam_partSigmaFam

namespace Work.EKLC6Core.BiGenChain

open MeasureTheory
open scoped ENNReal BigOperators

/-- `Hfam` only depends on the pointwise values of the family. -/
theorem Hfam_congr_general {X : Type*} [mX : MeasurableSpace X] {ι : Type*} [Fintype ι]
    (μ : Measure X) {P Q : ι → Set X} (h : ∀ i, P i = Q i) :
    Work.EKLContract.Hfam μ P = Work.EKLContract.Hfam μ Q := by
  unfold Work.EKLContract.Hfam
  exact Finset.sum_congr rfl (fun i _ => by rw [h i])

/-- The equivalence `κ × (θ × ι) ≃ ι × (κ × θ)` cycling the three factors. -/
def swingEquiv (κ θ ι : Type*) : κ × (θ × ι) ≃ ι × (κ × θ) where
  toFun q := (q.2.2, (q.1, q.2.1))
  invFun r := (r.2.1, (r.2.2, r.1))
  left_inv q := by rcases q with ⟨k, t, i⟩; rfl
  right_inv r := by rcases r with ⟨i, k, t⟩; rfl

@[simp] theorem swingEquiv_apply (κ θ ι : Type*) (q : κ × (θ × ι)) :
    swingEquiv κ θ ι q = (q.2.2, (q.1, q.2.1)) := rfl

theorem HcondFam_join_chain {X : Type*} [mX : MeasurableSpace X] {ι κ θ : Type*} [Fintype ι]
    [Fintype κ] [Fintype θ] (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    {A : ι → Set X} {C : κ → Set X} {B : θ → Set X} (hA : Work.EKLComp.Core.IsMPart A)
    (hC : Work.EKLComp.Core.IsMPart C) (hB : Work.EKLComp.Core.IsMPart B) :
    Work.EKLComp.Core.HcondFam X μ (fun p : ι × κ => A p.1 ∩ C p.2)
        (Work.EKLComp.Core.partSigmaFam B)
      = Work.EKLComp.Core.HcondFam X μ A (Work.EKLComp.Core.partSigmaFam B)
        + Work.EKLComp.Core.HcondFam X μ C
            (Work.EKLComp.Core.partSigmaFam B ⊔ Work.EKLComp.Core.partSigmaFam A) := by
  have hBC : Work.EKLComp.Core.IsMPart (fun p : ι × κ => A p.1 ∩ C p.2) := isMPart_prod hA hC
  have hf3 : Work.EKLComp.Core.IsMPart (fun q : θ × ι => B q.1 ∩ A q.2) := isMPart_prod hB hA
  -- Chain rule for each of the three conditional entropies.
  have h1 := Work.EKLC6Core.HcondFam_partSigmaFam (mX := mX) μ
      (fun p : ι × κ => A p.1 ∩ C p.2) B hBC hB
  have h2 := Work.EKLC6Core.HcondFam_partSigmaFam (mX := mX) μ A B hA hB
  have h3 := Work.EKLC6Core.HcondFam_partSigmaFam (mX := mX) μ C
      (fun q : θ × ι => B q.1 ∩ A q.2) hC hf3
  -- The σ-algebra of the conditioning family of the third term.
  have hsig : Work.EKLComp.Core.partSigmaFam (fun q : θ × ι => B q.1 ∩ A q.2)
      = Work.EKLComp.Core.partSigmaFam B ⊔ Work.EKLComp.Core.partSigmaFam A :=
    partSigmaFam_prod hB hA
  -- `Hfam` is insensitive to the order of the two joined partitions.
  have hcomm : Work.EKLContract.Hfam μ (fun q : ι × θ => A q.1 ∩ B q.2)
      = Work.EKLContract.Hfam μ (fun q : θ × ι => B q.1 ∩ A q.2) := by
    rw [show (fun q : θ × ι => B q.1 ∩ A q.2) = (fun q : θ × ι => A q.2 ∩ B q.1) from
      funext fun q => Set.inter_comm _ _]
    exact (Work.EKLComp.Core.Hfam_equiv μ (Equiv.prodComm θ ι)
      (fun q : ι × θ => A q.1 ∩ B q.2)).symm
  -- The full join `A ∨ C ∨ B` has the same entropy in the two index orders.
  have hL : Work.EKLContract.Hfam μ (fun q : (ι × κ) × θ => (A q.1.1 ∩ C q.1.2) ∩ B q.2)
      = Work.EKLContract.Hfam μ (fun r : ι × (κ × θ) => A r.1 ∩ C r.2.1 ∩ B r.2.2) :=
    Work.EKLComp.Core.Hfam_equiv μ (Equiv.prodAssoc ι κ θ)
      (fun r : ι × (κ × θ) => A r.1 ∩ C r.2.1 ∩ B r.2.2)
  have hR : Work.EKLContract.Hfam μ (fun q : κ × (θ × ι) => C q.1 ∩ (B q.2.1 ∩ A q.2.2))
      = Work.EKLContract.Hfam μ (fun r : ι × (κ × θ) => A r.1 ∩ C r.2.1 ∩ B r.2.2) := by
    rw [← Work.EKLComp.Core.Hfam_equiv μ (swingEquiv κ θ ι)
      (fun r : ι × (κ × θ) => A r.1 ∩ C r.2.1 ∩ B r.2.2)]
    refine Hfam_congr_general μ (fun q => ?_)
    ext x
    simp only [swingEquiv_apply, Set.mem_inter_iff]
    tauto
  have hkey : Work.EKLContract.Hfam μ (fun q : (ι × κ) × θ => (A q.1.1 ∩ C q.1.2) ∩ B q.2)
      = Work.EKLContract.Hfam μ (fun q : κ × (θ × ι) => C q.1 ∩ (B q.2.1 ∩ A q.2.2)) :=
    hL.trans hR.symm
  rw [h1, h2, ← hsig, h3, hcomm, hkey]
  ring

end Work.EKLC6Core.BiGenChain
