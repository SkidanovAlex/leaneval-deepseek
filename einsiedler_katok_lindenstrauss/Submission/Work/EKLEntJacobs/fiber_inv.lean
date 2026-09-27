import Mathlib

/-!
# Invariance of the conditional measures over the invariant σ-algebra

For a probability measure `μ` on a standard Borel space `X` preserved by a measurable map
`T : X → X`, the conditional measures of `μ` over the σ-algebra `invariants T` of `T`-invariant
sets are `T`-invariant for `μ`-almost every point.

The proof has three steps.

* For a measurable set `B`, the two `m`-measurable functions `x ↦ κ x (T ⁻¹' B)` and
  `x ↦ κ x B` (where `κ = condExpKernel μ m` and `m = invariants T`) have the same integral over
  every `m`-measurable set, because `s ∩ T ⁻¹' B = T ⁻¹' (s ∩ B)` for `s ∈ m` and `T` preserves
  `μ`.  Hence they agree `μ`-almost everywhere (uniqueness of the conditional expectation).
* Taking a countable generating sequence of the σ-algebra (which exists because `X` is standard
  Borel) and intersecting over the countably many finite index sets gives the equality
  simultaneously for a countable π-system generating the σ-algebra.
* For such a point, the two probability measures `map T (κ x)` and `κ x` agree on a π-system
  generating the σ-algebra, hence are equal.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Work.EKLEntJacobs

/-- For a measure-preserving `T` and a measurable set `B`, the conditional measure of `μ` over the
invariant σ-algebra of `T` satisfies `κ x (T ⁻¹' B) = κ x B` for `μ`-a.e. `x`. -/
lemma condExpKernel_invariants_preimage_ae {X : Type} [mX : MeasurableSpace X]
    [StandardBorelSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (hmp : MeasureTheory.MeasurePreserving T μ μ)
    {B : Set X} (hB : MeasurableSet B) :
    ∀ᵐ x ∂μ, ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x (T ⁻¹' B)
      = ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x B := by
  classical
  set κ : X → MeasureTheory.Measure X :=
    fun x => ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x with hκ
  have hm : MeasurableSpace.invariants T ≤ mX := MeasurableSpace.invariants_le T
  have htoReal : (fun x => (κ x).real (T ⁻¹' B)) =ᵐ[μ] (fun x => (κ x).real B) := by
    have h1 : (fun x => (κ x).real B) =ᵐ[μ]
        μ[B.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.invariants T] := by
      simpa only [hκ] using
        ProbabilityTheory.condExpKernel_ae_eq_condExp (μ := μ)
          (m := MeasurableSpace.invariants T) hm hB
    have h2 : (fun x => (κ x).real (T ⁻¹' B)) =ᵐ[μ]
        μ[(T ⁻¹' B).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.invariants T] := by
      simpa only [hκ] using
        ProbabilityTheory.condExpKernel_ae_eq_condExp (μ := μ)
          (m := MeasurableSpace.invariants T) hm (hT hB)
    have h3 : μ[(T ⁻¹' B).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.invariants T]
        =ᵐ[μ] μ[B.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.invariants T] := by
      refine MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hm ?_ ?_ ?_ ?_
      · exact (integrable_const (1 : ℝ)).indicator hB
      · intro s _ _
        exact (MeasureTheory.integrable_condExp (μ := μ)
          (m := MeasurableSpace.invariants T)
          (f := (T ⁻¹' B).indicator (fun _ => (1 : ℝ)))).integrableOn
      · intro s hs _
        have hsT : T ⁻¹' s = s :=
          (MeasurableSpace.measurableSet_invariants (f := T)).mp hs |>.2
        have hsX : MeasurableSet s := hm s hs
        have hmeas : MeasurableSet (s ∩ B) := hsX.inter hB
        have hset : s ∩ T ⁻¹' B = T ⁻¹' (s ∩ B) := by
          rw [Set.preimage_inter, hsT]
        have hmu : μ (T ⁻¹' (s ∩ B)) = μ (s ∩ B) := by
          rw [← Measure.map_apply hT hmeas, hmp.map_eq]
        have hA : ∫ x in s, (T ⁻¹' B).indicator (fun _ => (1 : ℝ)) x ∂μ
            = μ.real (s ∩ T ⁻¹' B) := by
          rw [← integral_indicator hsX, Set.indicator_indicator]
          exact integral_indicator_one (hsX.inter (hT hB))
        have hC : ∫ x in s, B.indicator (fun _ => (1 : ℝ)) x ∂μ
            = μ.real (s ∩ B) := by
          rw [← integral_indicator hsX, Set.indicator_indicator]
          exact integral_indicator_one (hsX.inter hB)
        have hAB : μ.real (s ∩ T ⁻¹' B) = μ.real (s ∩ B) := by
          rw [measureReal_def, measureReal_def, hset, hmu]
        have hstep : ∫ x in s,
              μ[(T ⁻¹' B).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.invariants T] x ∂μ
            = ∫ x in s, (T ⁻¹' B).indicator (fun _ => (1 : ℝ)) x ∂μ :=
          MeasureTheory.setIntegral_condExp hm
            ((integrable_const (1 : ℝ)).indicator (hT hB)) hs
        exact hstep.trans (hA.trans (hAB.trans hC.symm))
      · exact (MeasureTheory.stronglyMeasurable_condExp (μ := μ)
          (m := MeasurableSpace.invariants T)
          (f := (T ⁻¹' B).indicator (fun _ => (1 : ℝ)))).aestronglyMeasurable
    exact h2.trans (h3.trans h1.symm)
  filter_upwards [htoReal] with x hx
  have hmark : IsProbabilityMeasure (κ x) := by
    have h : IsProbabilityMeasure
        (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) :=
      IsMarkovKernel.isProbabilityMeasure x
    simpa only [hκ] using h
  simp only [measureReal_def] at hx
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hx

theorem fiber_inv {X : Type} [mX : MeasurableSpace X] [StandardBorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (hmp : MeasureTheory.MeasurePreserving T μ μ) :
    ∀ᵐ x ∂μ, MeasureTheory.MeasurePreserving T
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) := by
  classical
  set κ : X → MeasureTheory.Measure X :=
    fun x => ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x with hκ
  have key : ∀ B : Set X, MeasurableSet B → ∀ᵐ x ∂μ, κ x (T ⁻¹' B) = κ x B := by
    intro B hB
    simpa only [hκ] using condExpKernel_invariants_preimage_ae μ T hT hmp hB
  -- a countable π-system generating the σ-algebra
  set pf : Finset ℕ → Set X :=
    fun F => ⋂ n ∈ (F : Set ℕ), MeasurableSpace.natGeneratingSequence X n with hpf_def
  have hpf_mem : ∀ F : Finset ℕ, MeasurableSet (pf F) := by
    intro F
    simp only [hpf_def]
    exact MeasurableSet.biInter F.countable_toSet
      (fun n _ => MeasurableSpace.measurableSet_natGeneratingSequence (α := X) n)
  have hpi : IsPiSystem (Set.range pf) := by
    rintro s ⟨F, rfl⟩ t ⟨G, rfl⟩ -
    refine ⟨F ∪ G, ?_⟩
    show pf (F ∪ G) = pf F ∩ pf G
    ext x
    simp only [hpf_def, Set.mem_iInter, Set.mem_inter_iff, Finset.coe_union, Set.mem_union]
    constructor
    · intro h
      exact ⟨fun n hn => h n (Or.inl hn), fun n hn => h n (Or.inr hn)⟩
    · rintro ⟨h1, h2⟩ n (hn | hn)
      · exact h1 n hn
      · exact h2 n hn
  have hgen : mX = MeasurableSpace.generateFrom (Set.range pf) := by
    have h1 : MeasurableSpace.generateFrom (Set.range pf) ≤ mX := by
      refine MeasurableSpace.generateFrom_le ?_
      rintro s ⟨F, rfl⟩
      exact hpf_mem F
    have h2 : MeasurableSpace.generateFrom
          (Set.range (MeasurableSpace.natGeneratingSequence X))
        ≤ MeasurableSpace.generateFrom (Set.range pf) := by
      refine MeasurableSpace.generateFrom_mono ?_
      rintro s ⟨n, rfl⟩
      refine ⟨{n}, ?_⟩
      ext y
      simp only [hpf_def, Finset.coe_singleton, Set.mem_iInter, Set.mem_singleton_iff]
      constructor
      · intro h; exact h n rfl
      · intro h m hm; rw [hm]; exact h
    rw [MeasurableSpace.generateFrom_natGeneratingSequence X] at h2
    exact le_antisymm h2 h1
  have hall : ∀ᵐ x ∂μ, ∀ F : Finset ℕ, κ x (T ⁻¹' pf F) = κ x (pf F) :=
    MeasureTheory.ae_all_iff.2 (fun F => key (pf F) (hpf_mem F))
  have main : ∀ᵐ x ∂μ, MeasureTheory.MeasurePreserving T (κ x) (κ x) := by
    filter_upwards [hall] with x hx
    have hmark : IsProbabilityMeasure (κ x) := by
      have h : IsProbabilityMeasure
          (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) :=
        IsMarkovKernel.isProbabilityMeasure x
      simpa only [hκ] using h
    refine ⟨hT, ?_⟩
    have huniv : pf ∅ = Set.univ := by
      ext y; simp only [hpf_def]; simp
    refine Measure.ext_of_generateFrom_of_cover_subset (μ := Measure.map T (κ x))
      (ν := κ x) (S := Set.range pf) (T := {Set.univ}) hgen hpi ?_ ?_ ?_ ?_ ?_
    · intro s hs
      rw [Set.mem_singleton_iff] at hs
      exact ⟨∅, by rw [hs, huniv]⟩
    · exact Set.countable_singleton _
    · exact Set.sUnion_singleton _
    · intro s hs
      rw [Set.mem_singleton_iff] at hs
      subst hs
      rw [Measure.map_apply hT MeasurableSet.univ, Set.preimage_univ, hmark.measure_univ]
      exact ENNReal.one_ne_top
    · rintro s ⟨F, rfl⟩
      rw [Measure.map_apply hT (hpf_mem F)]
      exact hx F
  simpa only [hκ] using main

end Work.EKLEntJacobs
