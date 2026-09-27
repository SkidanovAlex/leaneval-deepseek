import Mathlib
import Submission.Work.EKLComp.Hcond

/-!
# The integral of the height function of a finite measurable partition

If `A : ι → Set X` is a finite measurable partition of a probability space and `c : ι → ℝ`,
then the function `∑ i, (A i).indicator (fun _ => c i)` is the "height function" that is
constant equal to `c i` on the atom `A i`.  Integrating it over the finite union
`⋃ i ∈ s, A i` of atoms therefore gives `∑ i ∈ s, c i * μ (A i)`.
-/

open MeasureTheory

namespace Work.EKLComp

open Work.EKLComp.Core

/-- On an atom `A i` of a finite measurable partition, the sum of the indicators of *all* the
atoms (weighted by the constants `c`) collapses to the single constant `c i`: the other atoms are
disjoint from `A i`. -/
theorem sum_indicator_atoms_eq_of_mem {X : Type} [mX : MeasurableSpace X] {ι : Type}
    [Fintype ι] {A : ι → Set X} (hA : IsMPart A) (c : ι → ℝ) (i : ι) {x : X}
    (hx : x ∈ A i) : (∑ j, (A j).indicator (fun _ => c j) x) = c i := by
  have h1 : ∀ j ∈ (Finset.univ : Finset ι), j ≠ i → (A j).indicator (fun _ => c j) x = 0 := by
    intro j _ hji
    exact Set.indicator_of_notMem (Set.disjoint_left.mp (hA.disjoint hji.symm) hx) _
  have h2 : i ∉ (Finset.univ : Finset ι) → (A i).indicator (fun _ => c i) x = 0 :=
    fun h => absurd (Finset.mem_univ i) h
  rw [Finset.sum_eq_single i h1 h2, Set.indicator_of_mem hx]

theorem setIntegral_iUnion_atoms {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] {ι : Type} [Fintype ι] {A : ι → Set X}
    (hA : Work.EKLComp.Core.IsMPart A) (s : Finset ι) (c : ι → ℝ) :
    ∫ x in (⋃ i ∈ s, A i), (∑ i, (A i).indicator (fun _ => c i) x) ∂μ
      = ∑ i ∈ s, c i * (μ (A i)).toReal := by
  classical
  -- The height function of the partition.
  set F : X → ℝ := fun x => ∑ i, (A i).indicator (fun _ => c i) x with hF
  -- On each atom it is constant.
  have hpt : ∀ i (x : X), x ∈ A i → F x = c i := by
    intro i x hx
    change (∑ i, (A i).indicator (fun _ => c i) x) = c i
    exact sum_indicator_atoms_eq_of_mem hA c i hx
  -- The atoms of `s` are pairwise disjoint.
  have hd : (↑s : Set ι).Pairwise (Function.onFun Disjoint A) :=
    fun i _ j _ hij => hA.disjoint hij
  -- `F` is integrable on each atom (it agrees there with a constant).
  have hInt : ∀ i ∈ s, MeasureTheory.IntegrableOn F (A i) μ := by
    intro i _
    refine MeasureTheory.IntegrableOn.congr_fun
      (MeasureTheory.integrableOn_const (C := c i)) ?_ (hA.measurable i)
    intro x hx
    exact (hpt i x hx).symm
  rw [MeasureTheory.integral_biUnion_finset s (fun i _ => hA.measurable i) hd hInt]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- On `A i` the height function is the constant `c i`.
  rw [MeasureTheory.setIntegral_congr_fun (hA.measurable i) (fun x hx => hpt i x hx),
    MeasureTheory.setIntegral_const, Measure.real_def, smul_eq_mul]
  ring

end Work.EKLComp
