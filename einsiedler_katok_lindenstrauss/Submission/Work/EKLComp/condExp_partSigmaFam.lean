import Mathlib
import Submission.Work.EKLComp.Hcond
import Submission.Work.EKLComp.real_inter_iUnion_atoms
import Submission.Work.EKLComp.setIntegral_iUnion_atoms

/-!
# Conditional expectation on the σ-algebra of a finite measurable partition

For a finite measurable partition `A` of a probability space `(X, μ)` with σ-algebra
`partSigmaFam A = generateFrom (range A)`, the conditional expectation of the indicator of a
measurable set `S` is the function which is constant on each atom `A i`, with value
`μ (S ∩ A i) / μ (A i)`:

`condExp (partSigmaFam A) μ 1_S =ᵐ[μ] ∑ i, (A i).indicator (fun _ => (μ (A i)).toReal⁻¹ * (μ (S ∩ A i)).toReal)`.

(The atoms of measure zero are irrelevant for the a.e. statement; on them the right-hand side
takes the value `0`, since `(0 : ℝ≥0∞).toReal⁻¹ = 0`.)

The proof is the standard uniqueness argument for the conditional expectation
(`MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`): the right-hand side `G` is
`partSigmaFam A`-strongly-measurable and integrable, and for every `partSigmaFam A`-measurable
set `t` — which is a finite union `⋃_{i ∈ s} A i` of atoms — the integrals of `G` and of `1_S`
over `t` agree. Both computations reduce to the two auxiliary lemmas
`setIntegral_iUnion_atoms` (the integral of `G` over a finite union of atoms) and
`real_inter_iUnion_atoms` (the decomposition of `μ (S ∩ ⋃_{i ∈ s} A i)`), and to the elementary
identity `(μ (A i)).toReal⁻¹ * (μ (S ∩ A i)).toReal * (μ (A i)).toReal = (μ (S ∩ A i)).toReal`.
-/

namespace Work.EKLComp

open MeasureTheory
open scoped BigOperators

theorem condExp_partSigmaFam {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    {ι : Type} [Fintype ι] {A : ι → Set X} (hA : Work.EKLComp.Core.IsMPart A) (S : Set X)
    (hS : MeasurableSet S) :
    MeasureTheory.condExp (Work.EKLComp.Core.partSigmaFam A) μ (S.indicator (fun _ => (1:ℝ)))
      =ᵐ[μ] fun x => ∑ i, (A i).indicator (fun _ => ((μ (A i)).toReal)⁻¹ * (μ (S ∩ A i)).toReal) x := by
  classical
  -- The values of the candidate conditional expectation on the atoms.
  set c : ι → ℝ := fun i => ((μ (A i)).toReal)⁻¹ * (μ (S ∩ A i)).toReal with hc
  set G : X → ℝ := fun x => ∑ i, (A i).indicator (fun _ => c i) x with hGdef
  -- Each atom is measurable for the partition σ-algebra.
  have hpart : ∀ i, MeasurableSet[Work.EKLComp.Core.partSigmaFam A] (A i) :=
    fun i => MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self i)
  -- `G` is strongly measurable for the partition σ-algebra.
  have hG_sm : StronglyMeasurable[Work.EKLComp.Core.partSigmaFam A] G := by
    rw [hGdef]
    exact Finset.stronglyMeasurable_fun_sum Finset.univ
      (f := fun i x => (A i).indicator (fun _ => c i) x)
      (fun i _ => (stronglyMeasurable_const (α := X) (b := c i)).indicator (hpart i))
  -- `G` is integrable (it is a finite sum of bounded measurable functions).
  have hG_int : Integrable G μ := by
    rw [hGdef]
    exact integrable_finsetSum Finset.univ
      (fun i _ => (integrable_const (c i)).indicator (hA.measurable i))
  -- Uniqueness of the conditional expectation: it suffices to test the integrals against
  -- `partSigmaFam A`-measurable sets.
  have hmain : G =ᵐ[μ]
      MeasureTheory.condExp (Work.EKLComp.Core.partSigmaFam A) μ (S.indicator (fun _ => (1:ℝ))) := by
    refine MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq (Core.partSigmaFam_le hA) ?_ ?_ ?_ ?_
    · exact (integrable_const (1:ℝ)).indicator hS
    · intro t _ _
      exact hG_int.integrableOn
    · intro t ht _
      -- A `partSigmaFam A`-measurable set is a union of atoms, indexed by a `Set ι`; since `ι` is
      -- finite, it is a union over the corresponding `Finset`.
      obtain ⟨I, rfl⟩ := (Core.measurableSet_partSigmaFam_iff hA t).mp ht
      set s : Finset ι := Finset.univ.filter (fun i => i ∈ I) with hs
      have hunion : (⋃ i ∈ I, A i) = ⋃ i ∈ s, A i := by
        ext x
        simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨i, hi, hxi⟩
          exact ⟨i, by simp [hs, hi], hxi⟩
        · rintro ⟨i, hi, hxi⟩
          exact ⟨i, by simpa [hs] using hi, hxi⟩
      -- The integral of `G` over the union of atoms.
      rw [hunion, hGdef, setIntegral_iUnion_atoms μ hA s c]
      -- The integral of the indicator of `S` over the union of atoms.
      rw [MeasureTheory.setIntegral_indicator hS]
      rw [MeasureTheory.setIntegral_const (1:ℝ), smul_eq_mul, mul_one]
      rw [Set.inter_comm, MeasureTheory.measureReal_def, real_inter_iUnion_atoms μ hA s hS]
      -- The two sums agree term by term.
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rcases eq_or_ne (μ (A i)) 0 with h0 | h0
      · have hz : μ (S ∩ A i) = 0 := measure_mono_null Set.inter_subset_right h0
        rw [hz, h0]
        simp
      · have htR : (μ (A i)).toReal ≠ 0 := by
          rw [ENNReal.toReal_ne_zero]
          exact ⟨h0, measure_ne_top μ _⟩
        have h1 : (μ (A i)).toReal⁻¹ * (μ (S ∩ A i)).toReal * (μ (A i)).toReal
            = ((μ (A i)).toReal⁻¹ * (μ (A i)).toReal) * (μ (S ∩ A i)).toReal := by ring
        rw [h1, inv_mul_cancel₀ htR, one_mul]
    · exact hG_sm.aestronglyMeasurable
  simpa only [hGdef, hc] using hmain.symm

end Work.EKLComp
