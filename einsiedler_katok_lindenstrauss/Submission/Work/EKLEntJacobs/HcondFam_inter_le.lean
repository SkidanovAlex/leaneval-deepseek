import Mathlib
import Submission.Work.EKLComp.Hpart.Hfam_join_chain
import Submission.Work.EKLEntJacobs.negMulLog_matrix_le
import Submission.Work.EKLEntJacobs.negMulLog_inter_le_atom

/-!
# Subadditivity of conditional entropy over a join of two finite partitions

`HcondFam_inter_le` : for finite measurable partitions `A : ι → Set X`, `C : κ → Set X`,
`B : θ → Set X` of a probability space, the conditional entropy of the join `A ∨ C` (atoms
`A i ∩ C j`) given the σ-algebra of `B` is at most the sum of the two conditional entropies.

The route is the one prescribed in the statement.

* `Work.EKLComp.Hpart.HcondFam_partSigmaFam_eq` rewrites each of the three conditional entropies
  as a mass-weighted double sum over the atoms `B j` of `B`.
* On a single atom `B j` the normalised joint masses
  `p i k = (μ (A i ∩ C k ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹` form a sub-stochastic matrix,
  whose row sums are the normalised masses of `A i ∩ B j` and whose column sums are those of
  `C k ∩ B j`; the matrix lemma `Work.EKLEntJacobs.negMulLog_matrix_le` (Shannon subadditivity
  for such a matrix) gives the inequality atom by atom
  (`Work.EKLEntJacobs.negMulLog_inter_le_atom`).
* Multiplying by the nonnegative mass `(μ (B j)).toReal` and summing over `j` yields the claim:
  the sums over `j` and over the index of the join are exchanged, and the factor `(μ (B j)).toReal`
  is pulled out of the inner sums (`Finset.sum_comm`, `Finset.mul_sum`).
-/

open MeasureTheory BigOperators

namespace Work.EKLEntJacobs

/-- The join of two finite measurable partitions is a finite measurable partition. -/
theorem isMPart_prod_fam {X : Type} [mX : MeasurableSpace X] {ι κ : Type} [Fintype ι] [Fintype κ]
    {A : ι → Set X} {C : κ → Set X}
    (hA : Work.EKLComp.Core.IsMPart A) (hC : Work.EKLComp.Core.IsMPart C) :
    Work.EKLComp.Core.IsMPart (fun p : ι × κ => A p.1 ∩ C p.2) := by
  refine ⟨fun p => (hA.measurable p.1).inter (hC.measurable p.2), ?_, ?_⟩
  · rintro ⟨i, k⟩ ⟨i', k'⟩ hne
    rcases eq_or_ne i i' with rfl | hi
    · rcases eq_or_ne k k' with rfl | hk
      · exact absurd rfl hne
      · exact (hC.disjoint hk).mono Set.inter_subset_right Set.inter_subset_right
    · exact (hA.disjoint hi).mono Set.inter_subset_left Set.inter_subset_left
  · rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (by rw [hA.cover]; trivial : x ∈ ⋃ i, A i)
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (by rw [hC.cover]; trivial : x ∈ ⋃ k, C k)
    exact Set.mem_iUnion.mpr ⟨(i, k), ⟨hi, hk⟩⟩

/-- Subadditivity of conditional entropy over a join of two finite partitions: for finite
measurable partitions `A : ι → Set X`, `C : κ → Set X`, `B : θ → Set X` of a probability space,
the conditional entropy of the join `A ∨ C` (atoms `A i ∩ C j`) given the σ-algebra of `B` is at
most the sum of the two conditional entropies. Proof route: rewrite all three conditional entropies
by `Work.EKLComp.Hpart.HcondFam_partSigmaFam_eq`, then for each `j` apply the matrix lemma
`Work.EKLEntJacobs.negMulLog_matrix_le` to `p i k = (μ (A i ∩ C k ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹`
(whose row sums are `(μ (A i ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹`, column sums
`(μ (C k ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹` and total `≤ 1`), multiply by `(μ (B j)).toReal ≥ 0`
and sum over `j`. -/
theorem HcondFam_inter_le {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] {ι κ θ : Type} [Fintype ι] [Fintype κ] [Fintype θ]
    {A : ι → Set X} {C : κ → Set X} {B : θ → Set X}
    (hA : Work.EKLComp.Core.IsMPart A) (hC : Work.EKLComp.Core.IsMPart C)
    (hB : Work.EKLComp.Core.IsMPart B) :
    Work.EKLComp.Core.HcondFam X μ (fun p : ι × κ => A p.1 ∩ C p.2)
        (Work.EKLComp.Core.partSigmaFam B) ≤
      Work.EKLComp.Core.HcondFam X μ A (Work.EKLComp.Core.partSigmaFam B) +
      Work.EKLComp.Core.HcondFam X μ C (Work.EKLComp.Core.partSigmaFam B) := by
  have hAC : Work.EKLComp.Core.IsMPart (fun p : ι × κ => A p.1 ∩ C p.2) :=
    isMPart_prod_fam hA hC
  -- Rewrite the three conditional entropies as mass-weighted sums over the atoms of `B`.
  rw [Work.EKLComp.Hpart.HcondFam_partSigmaFam_eq μ hAC hB,
      Work.EKLComp.Hpart.HcondFam_partSigmaFam_eq μ hA hB,
      Work.EKLComp.Hpart.HcondFam_partSigmaFam_eq μ hC hB]
  -- Atom-by-atom subadditivity (Shannon subadditivity of the normalised joint masses on `B j`).
  have key : ∀ j : θ,
      (∑ p : ι × κ, Real.negMulLog
          ((μ (A p.1 ∩ C p.2 ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹))
        ≤ (∑ i, Real.negMulLog ((μ (A i ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹))
          + (∑ k, Real.negMulLog ((μ (C k ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹)) := by
    intro j
    have h := negMulLog_inter_le_atom μ hA hC (hB.measurable j)
    rw [Fintype.sum_prod_type]
    exact h
  have hmain : (∑ p : ι × κ, ∑ j, (μ (B j)).toReal *
        Real.negMulLog ((μ (A p.1 ∩ C p.2 ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹))
      ≤ (∑ i, ∑ j, (μ (B j)).toReal *
            Real.negMulLog ((μ (A i ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹))
        + (∑ k, ∑ j, (μ (B j)).toReal *
            Real.negMulLog ((μ (C k ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹)) := by
    calc (∑ p : ι × κ, ∑ j, (μ (B j)).toReal *
            Real.negMulLog ((μ (A p.1 ∩ C p.2 ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹))
        = (∑ j, (μ (B j)).toReal * ∑ p : ι × κ, Real.negMulLog
            ((μ (A p.1 ∩ C p.2 ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹)) := by
            rw [Finset.sum_comm]
            simp_rw [← Finset.mul_sum]
      _ ≤ (∑ j, (μ (B j)).toReal *
            ((∑ i, Real.negMulLog ((μ (A i ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹))
              + (∑ k, Real.negMulLog ((μ (C k ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹)))) :=
            Finset.sum_le_sum
              (fun j _ => mul_le_mul_of_nonneg_left (key j) ENNReal.toReal_nonneg)
      _ = (∑ j, (μ (B j)).toReal *
              ∑ i, Real.negMulLog ((μ (A i ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹))
            + (∑ j, (μ (B j)).toReal *
              ∑ k, Real.negMulLog ((μ (C k ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹)) := by
            simp_rw [mul_add, Finset.sum_add_distrib]
      _ = (∑ i, ∑ j, (μ (B j)).toReal *
              Real.negMulLog ((μ (A i ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹))
            + (∑ k, ∑ j, (μ (B j)).toReal *
              Real.negMulLog ((μ (C k ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹)) := by
            congr 1
            · rw [Finset.sum_comm]
              simp_rw [← Finset.mul_sum]
            · rw [Finset.sum_comm]
              simp_rw [← Finset.mul_sum]
  exact hmain

end Work.EKLEntJacobs
