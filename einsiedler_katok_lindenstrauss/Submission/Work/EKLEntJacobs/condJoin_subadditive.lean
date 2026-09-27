import Mathlib
import Submission.Work.EKLComp.EntJacobsAux
import Submission.Work.EKLComp.Entropy
import Submission.Work.EKLComp.Hpart.Hfam_join_chain
import Submission.Work.EKLEntJacobs.HcondFam_inter_le
import Submission.Work.EKLEntJacobs.HcondFam_preimage_iterate
import Submission.Work.EKLEntJacobs.HcondFam_joinSets_append

/-!
# Subadditivity of the conditional entropy of the join `⋁_{k<N} T^{-k}Q`

`condJoin_subadditive` is the Fekete input for the Kolmogorov–Sinai identity in the
generating-sequence form: for a probability measure `μ`, a measure preserving `T`, a finite
partition `Q` and a finite measurable partition `B` all of whose atoms are `T`-invariant sets,
the sequence

  `N ↦ H_μ(⋁_{k<N} T^{-k}Q | σ(B))`

is subadditive.

The three ingredients are, with `J_N := joinSets T Q N`:

* `HcondFam_joinSets_append` — the join at the cut `m+n` splits into the product family
  `(u,v) ↦ J_m u ∩ T^{-m}J_n v`;
* `HcondFam_inter_le` — subadditivity of conditional entropy over a join,
  `H(A ∨ C | σB) ≤ H(A | σB) + H(C | σB)`;
* `HcondFam_preimage_iterate` — invariance of the conditional entropy of `T^{-m}A` under the
  measure preserving `T` when `σ(B)` is `T`-invariant.
-/

namespace Work.EKLEntJacobs

open MeasureTheory
open scoped BigOperators

variable {X : Type} [mX : MeasurableSpace X]

/-- Pulling a finite measurable partition back along an iterate of a measurable map again gives a
finite measurable partition. -/
theorem isMPart_preimage_iterate {T : X → X} (hT : Measurable T)
    {κ : Type} [Fintype κ] {A : κ → Set X} (hA : Work.EKLComp.Core.IsMPart A) (m : ℕ) :
    Work.EKLComp.Core.IsMPart (fun v => T^[m] ⁻¹' A v) :=
  ⟨fun v => (hA.measurable v).preimage (hT.iterate m),
   fun _ _ huv => (hA.disjoint huv).preimage _,
   by rw [← Set.preimage_iUnion, hA.cover, Set.preimage_univ]⟩

theorem condJoin_subadditive {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (T : X → X)
    (hmp : MeasureTheory.MeasurePreserving T μ μ) (Q : Work.EKLContract.FinPart X)
    {κ : Type} [Fintype κ] {B : κ → Set X} (hB : Work.EKLComp.Core.IsMPart B)
    (hinv : ∀ j, T ⁻¹' B j = B j) :
    Subadditive (fun N : ℕ => Work.EKLComp.HcondFam μ (Work.EKLContract.joinSets T Q N)
      (Work.EKLComp.Core.partSigmaFam B)) := by
  change Subadditive (fun N : ℕ => Work.EKLComp.Core.HcondFam X μ
    (Work.EKLContract.joinSets T Q N) (Work.EKLComp.Core.partSigmaFam B))
  intro m n
  have hT : Measurable T := hmp.measurable
  have hsplit := HcondFam_joinSets_append μ T Q hB m n
  have hsub := HcondFam_inter_le μ
    (A := Work.EKLContract.joinSets T Q m)
    (C := fun v : Fin n → Fin Q.n => T^[m] ⁻¹' Work.EKLContract.joinSets T Q n v)
    (B := B)
    (Work.EKLComp.Core.joinSets_isMPart hT Q m)
    (isMPart_preimage_iterate hT (Work.EKLComp.Core.joinSets_isMPart hT Q n) m) hB
  have hinv' := HcondFam_preimage_iterate μ T hmp hB hinv
    (A := Work.EKLContract.joinSets T Q n) (Work.EKLComp.Core.joinSets_isMPart hT Q n) m
  calc Work.EKLComp.Core.HcondFam X μ (Work.EKLContract.joinSets T Q (m + n))
        (Work.EKLComp.Core.partSigmaFam B)
      = Work.EKLComp.Core.HcondFam X μ
          (fun p : (Fin m → Fin Q.n) × (Fin n → Fin Q.n) =>
            Work.EKLContract.joinSets T Q m p.1 ∩
              T^[m] ⁻¹' Work.EKLContract.joinSets T Q n p.2)
          (Work.EKLComp.Core.partSigmaFam B) := hsplit
    _ ≤ Work.EKLComp.Core.HcondFam X μ (Work.EKLContract.joinSets T Q m)
          (Work.EKLComp.Core.partSigmaFam B) +
        Work.EKLComp.Core.HcondFam X μ
          (fun v : Fin n → Fin Q.n => T^[m] ⁻¹' Work.EKLContract.joinSets T Q n v)
          (Work.EKLComp.Core.partSigmaFam B) := hsub
    _ = Work.EKLComp.Core.HcondFam X μ (Work.EKLContract.joinSets T Q m)
          (Work.EKLComp.Core.partSigmaFam B) +
        Work.EKLComp.Core.HcondFam X μ (Work.EKLContract.joinSets T Q n)
          (Work.EKLComp.Core.partSigmaFam B) := by rw [hinv']

end Work.EKLEntJacobs
