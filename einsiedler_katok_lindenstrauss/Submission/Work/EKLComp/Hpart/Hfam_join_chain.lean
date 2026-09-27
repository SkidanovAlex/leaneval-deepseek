import Mathlib
import Submission.Work.EKLComp.Hcond
import Submission.Work.EKLComp.real_inter_iUnion_atoms
import Submission.Work.EKLComp.Hpart.sum_negMulLog_chain

/-!
# The entropy chain rule for two finite partitions

`Hfam_join_chain`: for a finite measurable partition `P` and a finite family `B` generating a
σ-algebra,

  `H_μ(P ∨ B) = H_μ(B) + H_μ(P | σ(B))`,

i.e. `∑ p, negMulLog (μ (P.parts p.1 ∩ B p.2)) = ∑ j, negMulLog (μ (B j)) + Hcond μ P (σ B)`.

The proof computes the conditional entropy explicitly:

* `condExp_partSigmaFam_explicit`: the conditional expectation of the indicator of a measurable
  set against the σ-algebra of a finite partition is constant on the atoms of that partition, with
  the value `μ (S ∩ A j) / μ (A j)` on the atom `A j`;
* `setIntegral_iUnion_atoms_fam`: the integral of a piecewise constant function over a finite union
  of atoms is the corresponding weighted sum;
* `negMulLog_sum_indicator`: `negMulLog` of a piecewise constant function is the piecewise
  constant function of the values `negMulLog (c j)`;
* `sum_negMulLog_chain` (sibling module): the elementary identity
  `∑ i, negMulLog (c i) = negMulLog (∑ i, c i) + ∑ i, (∑ i, c i) * negMulLog (c i / ∑ i, c i)`.

These give `Hcond μ P (σ B) = ∑ i ∑ j (μ B j) · negMulLog (μ (P_i ∩ B_j) / μ B_j)`, and the chain
rule follows from the elementary identity summed over the atoms of `B`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section
set_option maxHeartbeats 4000000

namespace Work.EKLComp.Hpart
open Work.EKLContract Work.EKLComp.Core

variable {X : Type} [mX : MeasurableSpace X]

/-- On a finite measurable partition, the piecewise constant function `∑ j, 1_{B j} · c j` is
constant with value `c j` on the atom `B j`; hence `negMulLog` of it is the piecewise constant
function with values `negMulLog (c j)`. -/
theorem negMulLog_sum_indicator {κ : Type} [Fintype κ] {B : κ → Set X} (hB : IsMPart B)
    (c : κ → ℝ) (x : X) :
    Real.negMulLog (∑ j, (B j).indicator (fun _ => c j) x)
      = ∑ j, (B j).indicator (fun _ => Real.negMulLog (c j)) x := by
  classical
  obtain ⟨j₀, hj₀, huniq⟩ := hB.exists_unique x
  have hzero : ∀ b : κ, b ≠ j₀ → (B b).indicator (fun _ => c b) x = 0 := fun b hb =>
    Set.indicator_of_notMem (fun hx => hb (huniq b hx)) _
  have hzero' : ∀ b : κ, b ≠ j₀ → (B b).indicator (fun _ => Real.negMulLog (c b)) x = 0 :=
    fun b hb => Set.indicator_of_notMem (fun hx => hb (huniq b hx)) _
  rw [Finset.sum_eq_single j₀ (fun b _ hb => hzero b hb) (fun h => absurd (Finset.mem_univ j₀) h),
    Finset.sum_eq_single j₀ (fun b _ hb => hzero' b hb) (fun h => absurd (Finset.mem_univ j₀) h),
    Set.indicator_of_mem hj₀, Set.indicator_of_mem hj₀]

/-- A finite sum of constants times indicator functions of measurable sets of finite measure is
integrable on a probability space. -/
theorem integrable_sum_indicator (μ : Measure X) [IsProbabilityMeasure μ] {κ : Type} [Fintype κ]
    {B : κ → Set X} (hB : IsMPart B) (c : κ → ℝ) :
    Integrable (fun x => ∑ j, (B j).indicator (fun _ => c j) x) μ := by
  classical
  refine integrable_finsetSum (Finset.univ : Finset κ)
    (f := fun j : κ => (B j).indicator (fun _ => c j)) (fun j _ => ?_)
  exact (integrable_const (c j)).indicator (hB.measurable j)

open MeasureTheory in
/-- Integral of a piecewise-constant function on a finite union of atoms. -/
theorem setIntegral_iUnion_atoms_fam (μ : Measure X)
    [IsProbabilityMeasure μ] {ι : Type} [Fintype ι] {A : ι → Set X} (hA : IsMPart A)
    (s : Finset ι) (c : ι → ℝ) :
    ∫ x in (⋃ i ∈ s, A i), (∑ i, (A i).indicator (fun _ => c i) x) ∂μ
      = ∑ i ∈ s, c i * (μ (A i)).toReal := by
  classical
  have hU : MeasurableSet (⋃ i ∈ s, A i) :=
    Finset.measurableSet_biUnion s (fun i _ => hA.measurable i)
  rw [← MeasureTheory.integral_indicator hU]
  have hpoint : (⋃ i ∈ s, A i).indicator (fun x => ∑ i, (A i).indicator (fun _ => c i) x)
      = fun x => ∑ i ∈ s, (A i).indicator (fun _ => c i) x := by
    funext x
    by_cases hx : x ∈ ⋃ i ∈ s, A i
    · rw [Set.indicator_of_mem hx]
      refine (Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => ?_)).symm
      exact Set.indicator_of_notMem (fun hxi => by
        obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp hx
        have hik : i = k := by
          by_contra hne
          exact Set.disjoint_left.mp (hA.disjoint hne) hxi hxk
        rw [← hik] at hk
        exact hi hk) _
    · rw [Set.indicator_of_notMem hx]
      exact (Finset.sum_eq_zero (fun i hi =>
        Set.indicator_of_notMem (fun hxi => hx (Set.mem_iUnion₂.mpr ⟨i, hi, hxi⟩)) _)).symm
  rw [hpoint, MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.integral_indicator_const _ (hA.measurable i), Measure.real_def, smul_eq_mul,
      mul_comm]
  · intro i _
    exact (integrable_const (c i)).indicator (hA.measurable i)

open MeasureTheory in
/-- Conditional expectation on the σ-algebra of a finite measurable partition, explicitly. -/
theorem condExp_partSigmaFam_explicit (μ : Measure X)
    [IsProbabilityMeasure μ] {ι : Type} [Fintype ι] {A : ι → Set X} (hA : IsMPart A)
    (S : Set X) (hS : MeasurableSet S) :
    MeasureTheory.condExp (partSigmaFam A) μ (S.indicator (fun _ => (1 : ℝ)))
      =ᵐ[μ] fun x => ∑ j, (A j).indicator
          (fun _ => (μ (S ∩ A j)).toReal * ((μ (A j)).toReal)⁻¹) x := by
  classical
  have hpart : ∀ j, MeasurableSet[partSigmaFam A] (A j) :=
    fun j => MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self j)
  have hG_sm : StronglyMeasurable[partSigmaFam A]
      (fun x => ∑ j, (A j).indicator (fun _ => (μ (S ∩ A j)).toReal * ((μ (A j)).toReal)⁻¹) x) :=
    Finset.stronglyMeasurable_fun_sum Finset.univ
      (f := fun j x => (A j).indicator
        (fun _ => (μ (S ∩ A j)).toReal * ((μ (A j)).toReal)⁻¹) x)
      (fun j _ => (stronglyMeasurable_const (α := X)
        (b := (μ (S ∩ A j)).toReal * ((μ (A j)).toReal)⁻¹)).indicator (hpart j))
  have hG_int : Integrable (fun x => ∑ j, (A j).indicator
      (fun _ => (μ (S ∩ A j)).toReal * ((μ (A j)).toReal)⁻¹) x) μ :=
    integrable_sum_indicator μ hA _
  refine (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq (partSigmaFam_le hA) ?_ ?_ ?_ ?_).symm
  · exact (integrable_const (1 : ℝ)).indicator hS
  · intro t _ _
    exact hG_int.integrableOn
  · intro t ht _
    obtain ⟨I, rfl⟩ := (measurableSet_partSigmaFam_iff hA t).mp ht
    set s : Finset ι := Finset.univ.filter (fun i => i ∈ I) with hs
    have hunion : (⋃ i ∈ I, A i) = ⋃ i ∈ s, A i := by
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi, hxi⟩
        exact ⟨i, by simp [hs, hi], hxi⟩
      · rintro ⟨i, hi, hxi⟩
        exact ⟨i, by simpa [hs] using hi, hxi⟩
    have hGA : ∫ x in (⋃ j ∈ s, A j), (∑ j, (A j).indicator
        (fun _ => (μ (S ∩ A j)).toReal * ((μ (A j)).toReal)⁻¹) x) ∂μ
        = ∑ j ∈ s, (μ (S ∩ A j)).toReal := by
      rw [setIntegral_iUnion_atoms_fam μ hA s
        (fun j => (μ (S ∩ A j)).toReal * ((μ (A j)).toReal)⁻¹)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      show (μ (S ∩ A j)).toReal * ((μ (A j)).toReal)⁻¹ * (μ (A j)).toReal
        = (μ (S ∩ A j)).toReal
      rcases eq_or_ne (μ (A j)) 0 with h0 | h0
      · have hz : μ (S ∩ A j) = 0 := measure_mono_null Set.inter_subset_right h0
        rw [hz, h0]
        simp
      · have htR : (μ (A j)).toReal ≠ 0 := by
          rw [ENNReal.toReal_ne_zero]
          exact ⟨h0, measure_ne_top μ _⟩
        rw [mul_assoc, inv_mul_cancel₀ htR, mul_one]
    have hfA : ∫ x in (⋃ j ∈ s, A j), (S.indicator (fun _ => (1 : ℝ))) x ∂μ
        = ∑ j ∈ s, (μ (S ∩ A j)).toReal := by
      rw [MeasureTheory.setIntegral_indicator hS, MeasureTheory.setIntegral_const (1 : ℝ),
        smul_eq_mul, mul_one, Set.inter_comm, Measure.real_def,
        Work.EKLComp.real_inter_iUnion_atoms μ hA s hS]
    rw [hunion, hGA, hfA]
  · exact hG_sm.aestronglyMeasurable

/-- **Conditional entropy of a finite partition, computed on the atoms of another one:**
`H_μ(A | σ(B)) = ∑ i ∑ j (μ B j) · negMulLog ((μ (A i ∩ B j)) / (μ B j))`. -/
theorem HcondFam_partSigmaFam_eq (μ : Measure X) [IsProbabilityMeasure μ] {ι κ : Type}
    [Fintype ι] [Fintype κ] {A : ι → Set X} {B : κ → Set X} (hA : IsMPart A) (hB : IsMPart B) :
    HcondFam X μ A (partSigmaFam B)
      = ∑ i, ∑ j, (μ (B j)).toReal *
          Real.negMulLog ((μ (A i ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹) := by
  rw [HcondFam]
  have hbridge : (fun x => ∑ i, Real.negMulLog
        (condExp (partSigmaFam B) μ ((A i).indicator (fun _ => (1 : ℝ))) x))
      =ᵐ[μ] (fun x => ∑ i, ∑ j, (B j).indicator
        (fun _ => Real.negMulLog ((μ (A i ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹)) x) := by
    have hper : ∀ i : ι, (fun x => Real.negMulLog
          (condExp (partSigmaFam B) μ ((A i).indicator (fun _ => (1 : ℝ))) x))
        =ᵐ[μ] (fun x => ∑ j, (B j).indicator
          (fun _ => Real.negMulLog ((μ (A i ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹)) x) := by
      intro i
      have h1 := condExp_partSigmaFam_explicit μ hB (A i) (hA.measurable i)
      have h2 : (fun x => Real.negMulLog
            (condExp (partSigmaFam B) μ ((A i).indicator (fun _ => (1 : ℝ))) x))
          =ᵐ[μ] (fun x => Real.negMulLog
            (∑ j, (B j).indicator (fun _ => (μ (A i ∩ B j)).toReal *
              ((μ (B j)).toReal)⁻¹) x)) :=
        h1.mono (fun x hx => by simp only [hx])
      have h3 : (fun x => Real.negMulLog
            (∑ j, (B j).indicator (fun _ => (μ (A i ∩ B j)).toReal *
              ((μ (B j)).toReal)⁻¹) x))
          =ᵐ[μ] (fun x => ∑ j, (B j).indicator
            (fun _ => Real.negMulLog ((μ (A i ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹)) x) :=
        Filter.Eventually.of_forall (fun x => negMulLog_sum_indicator hB _ x)
      exact h2.trans h3
    have hall : ∀ᵐ x ∂μ, ∀ i : ι, Real.negMulLog
        (condExp (partSigmaFam B) μ ((A i).indicator (fun _ => (1 : ℝ))) x)
        = ∑ j, (B j).indicator
          (fun _ => Real.negMulLog ((μ (A i ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹)) x :=
      Filter.eventually_all.2 (fun i => hper i)
    exact hall.mono (fun x hx => Finset.sum_congr rfl (fun i _ => hx i))
  calc ∫ x, ∑ i, Real.negMulLog
        (condExp (partSigmaFam B) μ ((A i).indicator (fun _ => (1 : ℝ))) x) ∂μ
      = ∫ x, ∑ i, ∑ j, (B j).indicator
          (fun _ => Real.negMulLog ((μ (A i ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹)) x ∂μ :=
        integral_congr_ae hbridge
    _ = ∑ i, ∫ x, ∑ j, (B j).indicator
          (fun _ => Real.negMulLog ((μ (A i ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹)) x ∂μ := by
        rw [integral_finsetSum]
        intro i _
        exact integrable_sum_indicator μ hB _
    _ = ∑ i, ∑ j, ∫ x, (B j).indicator
          (fun _ => Real.negMulLog ((μ (A i ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹)) x ∂μ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [integral_finsetSum]
        intro j _
        exact (integrable_const _).indicator (hB.measurable j)
    _ = ∑ i, ∑ j, (μ (B j)).toReal *
          Real.negMulLog ((μ (A i ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [integral_indicator_const _ (hB.measurable j), Measure.real_def, smul_eq_mul]

/-- **Entropy chain rule** for two finite measurable partitions: the entropy of the join of `A`
and `B` is the entropy of `B` plus the conditional entropy of `A` against the σ-algebra of
`B`. -/
theorem Hfam_join_chain_general (μ : Measure X) [IsProbabilityMeasure μ] {ι κ : Type}
    [Fintype ι] [Fintype κ] {A : ι → Set X} {B : κ → Set X} (hA : IsMPart A) (hB : IsMPart B) :
    Hfam μ (fun p : κ × ι => B p.1 ∩ A p.2) = Hfam μ B + HcondFam X μ A (partSigmaFam B) := by
  have hmain := HcondFam_partSigmaFam_eq μ hA hB
  have hdj : ∀ j : κ, (μ (B j)).toReal = ∑ i, (μ (A i ∩ B j)).toReal := fun j => by
    rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top μ _)]
    congr 1
    rw [← IsMPart.sum_measure_inter μ hA (hB.measurable j)]
    exact Finset.sum_congr rfl (fun i _ => by rw [Set.inter_comm])
  have hper : ∀ j : κ, Real.negMulLog (∑ i, (μ (A i ∩ B j)).toReal) +
        ∑ i, (∑ i, (μ (A i ∩ B j)).toReal) * Real.negMulLog
          ((μ (A i ∩ B j)).toReal * (∑ i, (μ (A i ∩ B j)).toReal)⁻¹)
      = ∑ i, Real.negMulLog ((μ (A i ∩ B j)).toReal) := fun j => by
    have h := sum_negMulLog_chain (fun i => (μ (A i ∩ B j)).toReal)
      (fun i => ENNReal.toReal_nonneg)
    simp only [div_eq_mul_inv] at h
    exact h.symm
  have key : ∀ j : κ, Real.negMulLog ((μ (B j)).toReal) +
        ∑ i, (μ (B j)).toReal * Real.negMulLog
          ((μ (A i ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹)
      = ∑ i, Real.negMulLog ((μ (A i ∩ B j)).toReal) := fun j => by
    rw [hdj j]
    exact hper j
  have hL : Hfam μ (fun p : κ × ι => B p.1 ∩ A p.2)
      = ∑ j, ∑ i, Real.negMulLog ((μ (A i ∩ B j)).toReal) := by
    simp only [Hfam]
    rw [sum_prod_univ]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
    rw [Set.inter_comm]
  rw [hL]
  calc ∑ j, ∑ i, Real.negMulLog ((μ (A i ∩ B j)).toReal)
      = ∑ j, (Real.negMulLog ((μ (B j)).toReal) + ∑ i, (μ (B j)).toReal * Real.negMulLog
          ((μ (A i ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹)) :=
        Finset.sum_congr rfl (fun j _ => (key j).symm)
    _ = (∑ j, Real.negMulLog ((μ (B j)).toReal)) + ∑ j, ∑ i, (μ (B j)).toReal * Real.negMulLog
          ((μ (A i ∩ B j)).toReal * ((μ (B j)).toReal)⁻¹) := Finset.sum_add_distrib
    _ = Hfam μ B + HcondFam X μ A (partSigmaFam B) := by
        rw [hmain]
        congr 1
        exact Finset.sum_comm

end Work.EKLComp.Hpart

namespace Work.EKLComp.Hpart
open Work.EKLContract Work.EKLComp.Core

theorem Hfam_join_chain {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (P : Work.EKLContract.FinPart X) {κ : Type} [Fintype κ]
    {B : κ → Set X} (hB : Work.EKLComp.Core.IsMPart B) :
    Work.EKLContract.Hfam μ (fun p : Fin P.n × κ => P.parts p.1 ∩ B p.2) =
      Work.EKLContract.Hfam μ B +
        Work.EKLContract.Hcond μ P (MeasurableSpace.generateFrom (Set.range B)) := by
  have hP : IsMPart P.parts := ⟨P.measurable, P.disjoint, P.cover⟩
  have hcomm : Hfam μ (fun p : Fin P.n × κ => P.parts p.1 ∩ B p.2)
      = Hfam μ (fun p : Fin P.n × κ => B p.2 ∩ P.parts p.1) := by
    simp only [Hfam]
    exact Finset.sum_congr rfl (fun p _ => by rw [Set.inter_comm])
  have hswap : Hfam μ (fun p : Fin P.n × κ => B p.2 ∩ P.parts p.1)
      = Hfam μ (fun q : κ × Fin P.n => B q.1 ∩ P.parts q.2) :=
    Hfam_equiv μ (Equiv.prodComm (Fin P.n) κ) (fun q : κ × Fin P.n => B q.1 ∩ P.parts q.2)
  rw [hcomm, hswap, ← HcondFam_eq_Hcond μ P (MeasurableSpace.generateFrom (Set.range B))]
  exact Hfam_join_chain_general μ hP hB

end Work.EKLComp.Hpart
