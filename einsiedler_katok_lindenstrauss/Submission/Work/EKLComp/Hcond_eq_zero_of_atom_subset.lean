import Mathlib
import Submission.Work.EKLComp.USCBasic
import Submission.Work.EKLComp.condExpKernel_atom
import Submission.Work.EKLComp.X3Background

open MeasureTheory
open scoped ENNReal

set_option linter.style.haveILetI false

namespace Work.EKLComp

/-- The integral of the indicator of a measurable set against a measure, as a real number. -/
lemma integral_indicator_one_eq_toReal {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {s : Set α} (hs : MeasurableSet s) :
    ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂ν = (ν s).toReal := by
  rw [← MeasureTheory.Measure.real_def]
  exact MeasureTheory.integral_indicator_one (μ := ν) hs

theorem Hcond_eq_zero_of_atom_subset (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ] (P : Work.EKLContract.FinPart Work.EKLContract.X3) (m : MeasurableSpace Work.EKLContract.X3) (hm : m ≤ Work.EKLContract.instMeasurableSpaceX3) (hcg : ∃ b : Set (Set Work.EKLContract.X3), b.Countable ∧ m = MeasurableSpace.generateFrom b) (h : ∀ᵐ x ∂μ, ∀ i, x ∈ @Work.EKLContract.FinPart.parts Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 P i → ∀ y, y ∈ @Work.EKLComp.atomGen Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 m x → y ∈ @Work.EKLContract.FinPart.parts Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 P i) : @Work.EKLContract.Hcond Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 μ P m = 0 := by
  classical
  letI : MeasurableSpace Work.EKLContract.X3 := Work.EKLContract.instMeasurableSpaceX3
  haveI : StandardBorelSpace Work.EKLContract.X3 := Work.EKLComp.X3Background.2.2.2.2
  -- The conditional kernel is carried by the atoms of `m`.
  have hker : ∀ᵐ x ∂μ, (ProbabilityTheory.condExpKernel μ m x) (atomGen m x) = 1 := by
    have hraw := Work.EKLComp.condExpKernel_atom (𝔪 := ⟨m⟩) hm hcg μ
    filter_upwards [hraw] with x hx
    exact hx
  -- The conditional expectation of the indicator of a part is the kernel mass of that part.
  have hcond : ∀ᵐ x ∂μ, ∀ i,
      MeasureTheory.condExp m μ ((P.parts i).indicator (fun _ => (1 : ℝ))) x
        = ((ProbabilityTheory.condExpKernel μ m x) (P.parts i)).toReal := by
    refine MeasureTheory.ae_all_iff.mpr ?_
    intro i
    have hf_int : MeasureTheory.Integrable ((P.parts i).indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator (P.measurable i)
    have h1 := ProbabilityTheory.condExp_ae_eq_integral_condExpKernel (μ := μ) (m := m) hm hf_int
    filter_upwards [h1] with x hx
    rw [hx, integral_indicator_one_eq_toReal (ProbabilityTheory.condExpKernel μ m x) (P.measurable i)]
  -- The integrand of `Hcond` vanishes almost everywhere.
  have hmain : ∀ᵐ x ∂μ,
      (∑ i, Real.negMulLog
        (MeasureTheory.condExp m μ ((P.parts i).indicator (fun _ => (1 : ℝ))) x)) = 0 := by
    filter_upwards [h, hker, hcond] with x hx_hyp hx_ker hx_cond
    obtain ⟨i0, hi0⟩ : ∃ i0, x ∈ P.parts i0 := by
      have : x ∈ ⋃ i, P.parts i := by rw [P.cover]; exact Set.mem_univ x
      exact Set.mem_iUnion.mp this
    have hPi0 : (ProbabilityTheory.condExpKernel μ m x) (P.parts i0) = 1 := by
      have h1 : (ProbabilityTheory.condExpKernel μ m x) (atomGen m x)
          ≤ (ProbabilityTheory.condExpKernel μ m x) (P.parts i0) :=
        MeasureTheory.measure_mono (hx_hyp i0 hi0)
      rw [hx_ker] at h1
      have h2 : (ProbabilityTheory.condExpKernel μ m x) (P.parts i0) ≤ 1 := by
        have h3 := MeasureTheory.measure_mono (Set.subset_univ (P.parts i0))
          (μ := ProbabilityTheory.condExpKernel μ m x)
        rwa [MeasureTheory.measure_univ] at h3
      exact le_antisymm h2 h1
    have hzero : ∀ i, i ≠ i0 → (ProbabilityTheory.condExpKernel μ m x) (P.parts i) = 0 := by
      intro i hi
      have hsub : P.parts i ⊆ (P.parts i0)ᶜ := by
        intro y hy
        exact Set.disjoint_left.mp (P.disjoint hi) hy
      have h1 : (ProbabilityTheory.condExpKernel μ m x) (P.parts i)
          ≤ (ProbabilityTheory.condExpKernel μ m x) ((P.parts i0)ᶜ) :=
        MeasureTheory.measure_mono hsub
      have h2 : (ProbabilityTheory.condExpKernel μ m x) ((P.parts i0)ᶜ)
          = (ProbabilityTheory.condExpKernel μ m x) Set.univ
            - (ProbabilityTheory.condExpKernel μ m x) (P.parts i0) :=
        MeasureTheory.measure_compl (P.measurable i0) (by rw [hPi0]; exact ENNReal.one_ne_top)
      rw [h2, hPi0, MeasureTheory.measure_univ, tsub_self] at h1
      exact le_antisymm h1 zero_le
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hx_cond i]
    by_cases hi : i = i0
    · rw [hi, hPi0]; simp
    · rw [hzero i hi]; simp
  rw [Work.EKLContract.Hcond]
  rw [MeasureTheory.integral_congr_ae hmain, MeasureTheory.integral_zero]

end Work.EKLComp
