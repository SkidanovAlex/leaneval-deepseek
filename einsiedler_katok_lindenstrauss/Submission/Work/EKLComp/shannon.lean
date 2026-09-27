import Mathlib
import Submission.Work.EKLComp.Core
import Submission.Work.EKLComp.negMulLog_sum_submodular

open MeasureTheory
open scoped BigOperators

namespace Work.EKLComp

/-- A sum over the triple product index type `(ι × κ) × ρ` as an iterated sum. -/
theorem sum_prod_prod_univ {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    {M : Type*} [AddCommMonoid M] (f : (ι × κ) × ρ → M) :
    ∑ q : (ι × κ) × ρ, f q = ∑ i, ∑ j, ∑ k, f ((i, j), k) := by
  rw [Core.sum_prod_univ, Core.sum_prod_univ]

/-- **Shannon's inequality for three partitions** (submodularity of entropy, equivalently
nonnegativity of the conditional mutual information `I(B ; C | A)`):

`H(A ∧ B ∧ C) + H(A) ≤ H(A ∧ B) + H(A ∧ C)`.

The analytic content is the finite-array submodularity lemma
`Work.EKLComp.negMulLog_sum_submodular`; the work here is the measure-theoretic reduction,
i.e. identifying each `Hfam` with the entropy of the corresponding marginal of the joint
distribution `(i,j,k) ↦ μ(A i ∩ B j ∩ C k)` on the (finite) index set. -/
theorem shannon {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ]
    {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    {A : ι → Set X} {B : κ → Set X} {C : ρ → Set X}
    (hA : Work.EKLComp.Core.IsMPart A) (hB : Work.EKLComp.Core.IsMPart B)
    (hC : Work.EKLComp.Core.IsMPart C) :
    Work.EKLContract.Hfam μ (fun q : (ι × κ) × ρ => A q.1.1 ∩ B q.1.2 ∩ C q.2)
      + Work.EKLContract.Hfam μ A
    ≤ Work.EKLContract.Hfam μ (fun q : ι × κ => A q.1 ∩ B q.2)
      + Work.EKLContract.Hfam μ (fun q : ι × ρ => A q.1 ∩ C q.2) := by
  classical
  -- Nonnegativity of the joint atom masses.
  have hm0 : ∀ i j k, 0 ≤ (μ (A i ∩ B j ∩ C k)).toReal := fun i j k => ENNReal.toReal_nonneg
  -- The marginal identities, at the level of `ℝ≥0∞`-valued measures.
  have hAi : ∀ i, μ (A i) = ∑ j, ∑ k, μ (A i ∩ B j ∩ C k) := by
    intro i
    rw [← Core.IsMPart.sum_measure_inter μ hB (hA.measurable i)]
    exact Finset.sum_congr rfl (fun j _ => (Core.IsMPart.sum_measure_inter μ hC
      ((hA.measurable i).inter (hB.measurable j))).symm)
  have hAB : ∀ i j, μ (A i ∩ B j) = ∑ k, μ (A i ∩ B j ∩ C k) := fun i j =>
    (Core.IsMPart.sum_measure_inter μ hC ((hA.measurable i).inter (hB.measurable j))).symm
  have hAC : ∀ i k, μ (A i ∩ C k) = ∑ j, μ (A i ∩ B j ∩ C k) := by
    intro i k
    rw [← Core.IsMPart.sum_measure_inter μ hB ((hA.measurable i).inter (hC.measurable k))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    ext x
    simp only [Set.mem_inter_iff]
    tauto
  -- The same identities for the real-valued masses.
  have hM : ∀ i, (μ (A i)).toReal = ∑ j, ∑ k, (μ (A i ∩ B j ∩ C k)).toReal := by
    intro i
    rw [hAi i, ENNReal.toReal_sum
      (fun j _ => ENNReal.sum_ne_top.mpr (fun k _ => measure_ne_top μ _))]
    exact Finset.sum_congr rfl (fun j _ => ENNReal.toReal_sum (fun k _ => measure_ne_top μ _))
  have hu : ∀ i j, (μ (A i ∩ B j)).toReal = ∑ k, (μ (A i ∩ B j ∩ C k)).toReal := by
    intro i j
    rw [hAB i j, ENNReal.toReal_sum (fun k _ => measure_ne_top μ _)]
  have hv : ∀ i k, (μ (A i ∩ C k)).toReal = ∑ j, (μ (A i ∩ B j ∩ C k)).toReal := by
    intro i k
    rw [hAC i k, ENNReal.toReal_sum (fun j _ => measure_ne_top μ _)]
  -- The atom masses have total mass one.
  have hsum : ∑ i, ∑ j, ∑ k, (μ (A i ∩ B j ∩ C k)).toReal = 1 := by
    rw [← Finset.sum_congr rfl (fun i _ => hM i), Core.IsMPart.sum_measure_toReal μ hA]
  have harr := negMulLog_sum_submodular (fun i j k => (μ (A i ∩ B j ∩ C k)).toReal) hm0 hsum
  -- Each `Hfam` is the entropy of the corresponding marginal.
  have e1 : Work.EKLContract.Hfam μ (fun q : (ι × κ) × ρ => A q.1.1 ∩ B q.1.2 ∩ C q.2)
      = ∑ i, ∑ j, ∑ k, Real.negMulLog ((μ (A i ∩ B j ∩ C k)).toReal) := by
    simp only [Work.EKLContract.Hfam]
    rw [sum_prod_prod_univ]
  have e2 : Work.EKLContract.Hfam μ A
      = ∑ i, Real.negMulLog (∑ j, ∑ k, (μ (A i ∩ B j ∩ C k)).toReal) := by
    simp only [Work.EKLContract.Hfam]
    exact Finset.sum_congr rfl (fun i _ => by rw [hM i])
  have e3 : Work.EKLContract.Hfam μ (fun q : ι × κ => A q.1 ∩ B q.2)
      = ∑ i, ∑ j, Real.negMulLog (∑ k, (μ (A i ∩ B j ∩ C k)).toReal) := by
    simp only [Work.EKLContract.Hfam]
    rw [Core.sum_prod_univ]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [hu i j]))
  have e4 : Work.EKLContract.Hfam μ (fun q : ι × ρ => A q.1 ∩ C q.2)
      = ∑ i, ∑ k, Real.negMulLog (∑ j, (μ (A i ∩ B j ∩ C k)).toReal) := by
    simp only [Work.EKLContract.Hfam]
    rw [Core.sum_prod_univ]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by rw [hv i k]))
  rw [e1, e2, e3, e4]
  exact harr

end Work.EKLComp
