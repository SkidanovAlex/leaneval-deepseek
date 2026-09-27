import Mathlib
import Submission.Work.EKLComp.Hcond

/-!
# Conditional expectation on the σ-algebra of a finite measurable partition (universe-polymorphic)

This is the universe-polymorphic version of
`Work.EKLComp.condExp_partSigmaFam` / `Work.EKLComp.setIntegral_iUnion_atoms` /
`Work.EKLComp.real_inter_iUnion_atoms`: those are stated with `X : Type`, whereas the chain rule
`Work.EKLC6Core.HcondFam_partSigmaFam` is stated with `X : Type*`, so a version living in an
arbitrary universe is needed here.

For a finite measurable partition `B` of a probability space `(X, μ)` with σ-algebra
`partSigmaFam B = generateFrom (range B)`, the conditional expectation of the indicator of a
measurable set `S` is the step function constant on each atom `B j` with value
`μ (S ∩ B j) / μ (B j)`.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Work.EKLC6Core

open Work.EKLComp.Core

/-- On an atom `B i` of a finite measurable partition, the height function `∑ j, 1_{B j} * c j`
collapses to the single constant `c i`. -/
theorem sum_indicator_atoms_eq_of_mem_poly {X : Type*} [mX : MeasurableSpace X] {ι : Type*}
    [Fintype ι] {B : ι → Set X} (hB : IsMPart B) (c : ι → ℝ) (i : ι) {x : X}
    (hx : x ∈ B i) : (∑ j, (B j).indicator (fun _ => c j) x) = c i := by
  have h1 : ∀ j ∈ (Finset.univ : Finset ι), j ≠ i → (B j).indicator (fun _ => c j) x = 0 := by
    intro j _ hji
    exact Set.indicator_of_notMem (Set.disjoint_left.mp (hB.disjoint hji.symm) hx) _
  have h2 : i ∉ (Finset.univ : Finset ι) → (B i).indicator (fun _ => c i) x = 0 :=
    fun h => absurd (Finset.mem_univ i) h
  rw [Finset.sum_eq_single i h1 h2, Set.indicator_of_mem hx]

/-- The integral of the height function of a finite measurable partition over a finite union of
atoms is the weighted sum of the masses of those atoms. -/
theorem setIntegral_iUnion_atoms_poly {X : Type*} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {B : ι → Set X} (hB : IsMPart B) (s : Finset ι) (c : ι → ℝ) :
    ∫ x in (⋃ i ∈ s, B i), (∑ i, (B i).indicator (fun _ => c i) x) ∂μ
      = ∑ i ∈ s, c i * (μ (B i)).toReal := by
  classical
  set F : X → ℝ := fun x => ∑ i, (B i).indicator (fun _ => c i) x with hF
  have hpt : ∀ i (x : X), x ∈ B i → F x = c i := by
    intro i x hx
    change (∑ i, (B i).indicator (fun _ => c i) x) = c i
    exact sum_indicator_atoms_eq_of_mem_poly hB c i hx
  have hd : (↑s : Set ι).Pairwise (Function.onFun Disjoint B) :=
    fun i _ j _ hij => hB.disjoint hij
  have hInt : ∀ i ∈ s, MeasureTheory.IntegrableOn F (B i) μ := by
    intro i _
    refine MeasureTheory.IntegrableOn.congr_fun
      (MeasureTheory.integrableOn_const (C := c i)) ?_ (hB.measurable i)
    intro x hx
    exact (hpt i x hx).symm
  rw [MeasureTheory.integral_biUnion_finset s (fun i _ => hB.measurable i) hd hInt]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.setIntegral_congr_fun (hB.measurable i) (fun x hx => hpt i x hx),
    MeasureTheory.setIntegral_const, Measure.real_def, smul_eq_mul]
  ring

/-- Slicing a measurable set by a finite union of atoms, in real-valued probability form. -/
theorem real_inter_iUnion_atoms_poly {X : Type*} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {B : ι → Set X} (hB : IsMPart B) (s : Finset ι) {T : Set X} (hT : MeasurableSet T) :
    (μ (T ∩ ⋃ i ∈ s, B i)).toReal = ∑ i ∈ s, (μ (T ∩ B i)).toReal := by
  have hm : ∀ i ∈ s, MeasurableSet (T ∩ B i) := fun i _ => hT.inter (hB.measurable i)
  have hd : (↑s : Set ι).PairwiseDisjoint (fun i => T ∩ B i) := by
    intro i _ j _ hij
    exact (hB.disjoint hij).mono Set.inter_subset_right Set.inter_subset_right
  have hset : T ∩ ⋃ i ∈ s, B i = ⋃ i ∈ s, T ∩ B i :=
    Set.inter_iUnion₂ T (fun i (_ : i ∈ s) => B i)
  rw [hset, measure_biUnion_finset hd hm,
    ENNReal.toReal_sum (fun i _ => measure_ne_top μ _)]

/-- **Conditional expectation of an indicator on a partition σ-algebra** (universe-polymorphic
form): for a finite measurable partition `B` and a measurable set `S`,
`condExp (partSigmaFam B) μ 1_S =ᵐ[μ] ∑ j, 1_{B j} * μ (S ∩ B j) / μ (B j)`. -/
theorem condExp_indicator_partSigmaFam_poly {X : Type*} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ] {κ : Type*} [Fintype κ]
    (B : κ → Set X) (hB : IsMPart B) (S : Set X) (hS : MeasurableSet S) :
    MeasureTheory.condExp (partSigmaFam B) μ (S.indicator (fun _ => (1 : ℝ)))
      =ᵐ[μ] fun x => ∑ j, (B j).indicator
        (fun _ => ((μ (B j)).toReal)⁻¹ * (μ (S ∩ B j)).toReal) x := by
  classical
  set c : κ → ℝ := fun j => ((μ (B j)).toReal)⁻¹ * (μ (S ∩ B j)).toReal with hc
  set G : X → ℝ := fun x => ∑ j, (B j).indicator (fun _ => c j) x with hGdef
  have hpart : ∀ j, MeasurableSet[partSigmaFam B] (B j) :=
    fun j => MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self j)
  have hG_sm : StronglyMeasurable[partSigmaFam B] G := by
    rw [hGdef]
    exact Finset.stronglyMeasurable_fun_sum Finset.univ
      (f := fun j x => (B j).indicator (fun _ => c j) x)
      (fun j _ => (stronglyMeasurable_const (α := X) (b := c j)).indicator (hpart j))
  have hG_int : Integrable G μ := by
    rw [hGdef]
    exact integrable_finsetSum Finset.univ
      (fun j _ => (integrable_const (c j)).indicator (hB.measurable j))
  have hmain : G =ᵐ[μ] MeasureTheory.condExp (partSigmaFam B) μ
      (S.indicator (fun _ => (1 : ℝ))) := by
    refine MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq (partSigmaFam_le hB) ?_ ?_ ?_ ?_
    · exact (integrable_const (1 : ℝ)).indicator hS
    · intro t _ _
      exact hG_int.integrableOn
    · intro t ht _
      obtain ⟨I, rfl⟩ := (measurableSet_partSigmaFam_iff hB t).mp ht
      set s : Finset κ := Finset.univ.filter (fun j => j ∈ I) with hs
      have hunion : (⋃ j ∈ I, B j) = ⋃ j ∈ s, B j := by
        ext x
        simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨j, hj, hxj⟩
          exact ⟨j, by simp [hs, hj], hxj⟩
        · rintro ⟨j, hj, hxj⟩
          exact ⟨j, by simpa [hs] using hj, hxj⟩
      rw [hunion, hGdef, setIntegral_iUnion_atoms_poly μ hB s c]
      rw [MeasureTheory.setIntegral_indicator hS]
      rw [MeasureTheory.setIntegral_const (1 : ℝ), smul_eq_mul, mul_one]
      rw [Set.inter_comm, Measure.real_def, real_inter_iUnion_atoms_poly μ hB s hS]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rcases eq_or_ne (μ (B j)) 0 with h0 | h0
      · have hz : μ (S ∩ B j) = 0 := measure_mono_null Set.inter_subset_right h0
        rw [hz, h0]
        simp
      · have htR : (μ (B j)).toReal ≠ 0 := by
          rw [ENNReal.toReal_ne_zero]
          exact ⟨h0, measure_ne_top μ _⟩
        have h1 : (μ (B j)).toReal⁻¹ * (μ (S ∩ B j)).toReal * (μ (B j)).toReal
            = ((μ (B j)).toReal⁻¹ * (μ (B j)).toReal) * (μ (S ∩ B j)).toReal := by ring
        rw [h1, inv_mul_cancel₀ htR, one_mul]
    · exact hG_sm.aestronglyMeasurable
  simpa only [hGdef, hc] using hmain.symm


/-- Atomwise collapse of a sum of `negMulLog`s of the conditional probability step functions: on
each atom `B j'` the function `x ↦ ∑ i, negMulLog (∑ j, 1_{B j} * c i j) x` is the constant
`∑ i, negMulLog (c i j')`. -/
theorem sum_negMulLog_indicator_atoms_poly {X : Type*} [mX : MeasurableSpace X] {ι κ : Type*}
    [Fintype ι] [Fintype κ] {B : κ → Set X} (hB : IsMPart B) (c : ι → κ → ℝ) :
    (fun x => ∑ i, Real.negMulLog (∑ j, (B j).indicator (fun _ => c i j) x))
      = fun x => ∑ j, (B j).indicator (fun _ => ∑ i, Real.negMulLog (c i j)) x := by
  classical
  funext x
  obtain ⟨j₀, hj₀, -⟩ := hB.exists_unique x
  have hinner : ∀ i, (∑ j, (B j).indicator (fun _ => c i j) x) = c i j₀ := by
    intro i
    have h1 : ∀ j ∈ (Finset.univ : Finset κ), j ≠ j₀ →
        (B j).indicator (fun _ => c i j) x = 0 := by
      intro j _ hjj
      exact Set.indicator_of_notMem (fun hx => Set.disjoint_left.mp (hB.disjoint hjj) hx hj₀) _
    have h2 : j₀ ∉ (Finset.univ : Finset κ) →
        (B j₀).indicator (fun _ => c i j₀) x = 0 :=
      fun h => absurd (Finset.mem_univ j₀) h
    rw [Finset.sum_eq_single j₀ h1 h2, Set.indicator_of_mem hj₀]
  have hright : (∑ j, (B j).indicator (fun _ => ∑ i, Real.negMulLog (c i j)) x)
      = ∑ i, Real.negMulLog (c i j₀) := by
    have h1 : ∀ j ∈ (Finset.univ : Finset κ), j ≠ j₀ →
        (B j).indicator (fun _ => ∑ i, Real.negMulLog (c i j)) x = 0 := by
      intro j _ hjj
      exact Set.indicator_of_notMem (fun hx => Set.disjoint_left.mp (hB.disjoint hjj) hx hj₀) _
    have h2 : j₀ ∉ (Finset.univ : Finset κ) →
        (B j₀).indicator (fun _ => (∑ i, Real.negMulLog (c i j₀))) x = 0 :=
      fun h => absurd (Finset.mem_univ j₀) h
    rw [Finset.sum_eq_single j₀ h1 h2, Set.indicator_of_mem hj₀]
  rw [show (∑ i, Real.negMulLog (∑ j, (B j).indicator (fun _ => c i j) x))
        = ∑ i, Real.negMulLog (c i j₀) from
      Finset.sum_congr rfl (fun i _ => by rw [hinner i]), hright]

end Work.EKLC6Core
