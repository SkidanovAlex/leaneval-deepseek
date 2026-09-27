import Mathlib
import Submission.Work.EKLComp.LeafDefs

namespace Work.EKLComp

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- There is a countable π-system on `X₃` containing `univ` and generating the Borel σ-algebra:
the finite intersections of the sets of a countable generating sequence of the Borel σ-algebra. -/
private lemma exists_countable_piSystem_borel_aux :
    ∃ C : Set (Set Work.EKLContract.X3), C.Countable ∧ IsPiSystem C ∧
      (Set.univ : Set Work.EKLContract.X3) ∈ C ∧
      (∀ s ∈ C, MeasurableSet s) ∧
      (borel Work.EKLContract.X3 : MeasurableSpace Work.EKLContract.X3)
        = MeasurableSpace.generateFrom C := by
  let A : ℕ → Set Work.EKLContract.X3 := MeasurableSpace.natGeneratingSequence Work.EKLContract.X3
  have hgen : MeasurableSpace.generateFrom (Set.range A)
      = (borel Work.EKLContract.X3 : MeasurableSpace Work.EKLContract.X3) :=
    MeasurableSpace.generateFrom_natGeneratingSequence Work.EKLContract.X3
  refine ⟨Set.range (fun t : Finset ℕ => ⋂ n ∈ t, A n), countable_range _, ?_, ⟨∅, ?_⟩, ?_, ?_⟩
  · rintro s ⟨t₁, rfl⟩ s' ⟨t₂, rfl⟩ -
    refine ⟨t₁ ∪ t₂, ?_⟩
    ext x
    simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_union]
    constructor
    · intro h; exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
    · rintro ⟨h₁, h₂⟩ i (hi | hi)
      · exact h₁ i hi
      · exact h₂ i hi
  · ext x; simp
  · rintro s ⟨t, rfl⟩
    exact MeasurableSet.biInter t.countable_toSet (fun n _ =>
      MeasurableSpace.measurableSet_natGeneratingSequence n)
  · rw [← hgen]
    apply le_antisymm
    · apply MeasurableSpace.generateFrom_mono
      rintro s ⟨n, rfl⟩
      exact ⟨{n}, by ext x; simp⟩
    · apply MeasurableSpace.generateFrom_le
      rintro s ⟨t, rfl⟩
      exact MeasurableSet.biInter t.countable_toSet (fun n _ =>
        MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self n))

/-- Restricting the measure `μ` to an `𝔪.m`-measurable set `Z` does not change the conditional
kernel given `𝔪.m`: for `(μ|Z)`-almost every `x` the conditional measures of `μ|Z` and `μ` with
respect to `𝔪.m` coincide.

The reason is that an `𝔪.m`-atom either lies inside `Z` or is disjoint from it, so on `Z` the
conditional expectation of an indicator function is the same for `μ|Z` and for `μ`
(`MeasureTheory.condExp_restrict_ae_eq_restrict`); testing on a countable π-system generating the
Borel σ-algebra and using that `condExpKernel` computes the conditional probabilities
(`ProbabilityTheory.condExpKernel_ae_eq_condExp`) yields the claim. -/
theorem kernel_restrict (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsFiniteMeasure μ] [StandardBorelSpace Work.EKLContract.X3] (𝔪 : Work.EKLComp.SigAlg) (hm : 𝔪.m ≤ borel Work.EKLContract.X3) (Z : Set Work.EKLContract.X3) (hZ : 𝔪.m.MeasurableSet' Z) : ∀ᵐ x ∂(μ.restrict Z), ProbabilityTheory.condExpKernel (μ.restrict Z) 𝔪.m x = ProbabilityTheory.condExpKernel μ 𝔪.m x := by
  obtain ⟨C, hCcnt, hCpi, hCuniv, hCmeas, hCgen⟩ := exists_countable_piSystem_borel_aux
  haveI hcount : Countable ↥C := hCcnt.to_subtype
  -- For every Borel set `s`, the real-valued conditional probabilities agree a.e. for `μ|Z`.
  have hreal : ∀ s ∈ C, ∀ᵐ x ∂(μ.restrict Z),
      (condExpKernel (μ.restrict Z) 𝔪.m x).real s = (condExpKernel μ 𝔪.m x).real s := by
    intro s hs
    have hsmeas : MeasurableSet s := hCmeas s hs
    have h1 : (fun x => (condExpKernel (μ.restrict Z) 𝔪.m x).real s)
        =ᵐ[μ.restrict Z] (μ.restrict Z)[s.indicator (fun _ => (1:ℝ)) | 𝔪.m] :=
      condExpKernel_ae_eq_condExp hm hsmeas
    have hint : Integrable (s.indicator (fun _ => (1:ℝ))) μ :=
      (integrable_const (1:ℝ)).indicator hsmeas
    have h2 : (μ.restrict Z)[s.indicator (fun _ => (1:ℝ)) | 𝔪.m]
        =ᵐ[μ.restrict Z] μ[s.indicator (fun _ => (1:ℝ)) | 𝔪.m] :=
      condExp_restrict_ae_eq_restrict hm hZ hint
    have h3 : (fun x => (condExpKernel μ 𝔪.m x).real s)
        =ᵐ[μ.restrict Z] μ[s.indicator (fun _ => (1:ℝ)) | 𝔪.m] :=
      (condExpKernel_ae_eq_condExp hm hsmeas).filter_mono
        (ae_mono (Measure.restrict_le_self (μ := μ) (s := Z)))
    exact h1.trans (h2.trans h3.symm)
  -- Pass to the `ℝ≥0∞`-valued statement, simultaneously in the countable π-system.
  have hall : ∀ᵐ x ∂(μ.restrict Z), ∀ s : ↥C,
      (condExpKernel (μ.restrict Z) 𝔪.m x) (s : Set Work.EKLContract.X3)
        = (condExpKernel μ 𝔪.m x) (s : Set Work.EKLContract.X3) := by
    refine ae_all_iff.mpr fun s => ?_
    filter_upwards [hreal s s.2] with x hx
    exact (measureReal_eq_measureReal_iff (μ := condExpKernel (μ.restrict Z) 𝔪.m x)
      (ν := condExpKernel μ 𝔪.m x) (s := (s : Set Work.EKLContract.X3))
      (t := (s : Set Work.EKLContract.X3))).mp hx
  filter_upwards [hall] with x hx
  exact Measure.ext_of_generateFrom_of_iUnion C (fun _ => Set.univ) hCgen hCpi
    (by ext y; simp) (fun _ => hCuniv)
    (fun _ => by rw [measure_univ]; exact ENNReal.one_ne_top)
    (fun s hs => hx ⟨s, hs⟩)

end

end Work.EKLComp
