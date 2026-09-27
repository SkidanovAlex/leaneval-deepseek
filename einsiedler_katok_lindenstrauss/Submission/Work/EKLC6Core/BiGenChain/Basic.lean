import Mathlib
import Submission.Work.EKLComp.Entropy
import Submission.Work.EKLComp.Hcond
import Submission.Work.EKLC6Core.Hcond_mono
import Submission.Work.EKLC6Core.HcondFam_partSigmaFam

/-!
# `EKLC6Core.BiGenChain.Basic`

Universe-polymorphic (`Type*`) helpers for the entropy chain estimates attached to the
forward-orbit σ-algebra `⋁_{n:ℕ} T^{-n}(partSigma P)`:

* monotonicity and chain rules for `Hfam` and `HcondFam` (reproduced at `Type*`; the versions in
  `Work.EKLEntJacobs` are universe-0),
* σ-algebra bookkeeping: `partSigmaFam` of a product family, pullbacks of `partSigmaFam`, and the
  containment of the finite windows `partSigmaFam (joinSets T P N)` in the orbit σ-algebra.

**Formalisation note.**  A local hypothesis of class type (`𝓕 : MeasurableSpace X`) is an instance
candidate for Lean's typeclass search, so it can capture the ambient instance of `Measure X`,
`condExp`, `HcondFam`, …  The lemmas with an extra `MeasurableSpace` binder are therefore stated
with the ambient instance bound *after* it, which makes the ambient the preferred candidate.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

namespace Work.EKLC6Core.BiGenChain

open Work.EKLContract
open Work.EKLComp.Core

/-! ## 1. Families on a product index type -/

/-- The pointwise intersection of two finite measurable partitions is a finite measurable
partition of the product index type. -/
theorem isMPart_prod {X : Type*} [mX : MeasurableSpace X] {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : ι → Set X} {B : κ → Set X} (hA : IsMPart A) (hB : IsMPart B) :
    IsMPart (fun p : ι × κ => A p.1 ∩ B p.2) := by
  refine ⟨fun p => (hA.measurable p.1).inter (hB.measurable p.2), ?_, ?_⟩
  · rintro ⟨i, j⟩ ⟨i', j'⟩ hne
    rcases eq_or_ne i i' with h | h
    · subst h
      have hjj' : j ≠ j' := fun h' => hne (by rw [h'])
      exact (hB.disjoint hjj').mono Set.inter_subset_right Set.inter_subset_right
    · exact (hA.disjoint h).mono Set.inter_subset_left Set.inter_subset_left
  · rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨i, hi⟩ : ∃ i, x ∈ A i := by
      have h : x ∈ ⋃ i, A i := by rw [hA.cover]; trivial
      simpa only [Set.mem_iUnion] using h
    obtain ⟨j, hj⟩ : ∃ j, x ∈ B j := by
      have h : x ∈ ⋃ j, B j := by rw [hB.cover]; trivial
      simpa only [Set.mem_iUnion] using h
    exact Set.mem_iUnion.mpr ⟨(i, j), hi, hj⟩

/-- The σ-algebra of the pointwise intersection is the join of the two σ-algebras. -/
theorem partSigmaFam_prod {X : Type*} [mX : MeasurableSpace X] {ι κ : Type*} [Fintype ι]
    [Fintype κ] {A : ι → Set X} {B : κ → Set X} (hA : IsMPart A) (hB : IsMPart B) :
    partSigmaFam (fun p : ι × κ => A p.1 ∩ B p.2) = partSigmaFam A ⊔ partSigmaFam B := by
  refine le_antisymm ?_ ?_
  · rw [partSigmaFam]
    refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨p, rfl⟩
    have h1 : MeasurableSet[partSigmaFam A] (A p.1) :=
      MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self _)
    have h2 : MeasurableSet[partSigmaFam B] (B p.2) :=
      MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self _)
    exact MeasurableSet.inter (MeasurableSpace.le_def.mp le_sup_left _ h1)
      (MeasurableSpace.le_def.mp le_sup_right _ h2)
  · refine sup_le ?_ ?_
    · rw [partSigmaFam]
      refine MeasurableSpace.generateFrom_le ?_
      rintro s ⟨i, rfl⟩
      have h : A i = ⋃ j : κ, (fun p : ι × κ => A p.1 ∩ B p.2) (i, j) := by
        ext x
        constructor
        · intro hx
          obtain ⟨j, hj⟩ : ∃ j, x ∈ B j := by
            have h : x ∈ ⋃ j, B j := by rw [hB.cover]; trivial
            simpa only [Set.mem_iUnion] using h
          exact Set.mem_iUnion.mpr ⟨j, ⟨hx, hj⟩⟩
        · intro hx
          obtain ⟨j, hx'⟩ := Set.mem_iUnion.mp hx
          exact hx'.1
      rw [h]
      exact MeasurableSet.iUnion fun j =>
        MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self _)
    · rw [partSigmaFam]
      refine MeasurableSpace.generateFrom_le ?_
      rintro s ⟨j, rfl⟩
      have h : B j = ⋃ i : ι, (fun p : ι × κ => A p.1 ∩ B p.2) (i, j) := by
        ext x
        constructor
        · intro hx
          obtain ⟨i, hi⟩ : ∃ i, x ∈ A i := by
            have h : x ∈ ⋃ i, A i := by rw [hA.cover]; trivial
            simpa only [Set.mem_iUnion] using h
          exact Set.mem_iUnion.mpr ⟨i, ⟨hi, hx⟩⟩
        · intro hx
          obtain ⟨i, hx'⟩ := Set.mem_iUnion.mp hx
          exact hx'.2
      rw [h]
      exact MeasurableSet.iUnion fun i =>
        MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self _)

/-- Pulling a finite measurable partition back along a measurable map. -/
theorem isMPart_preimage {X : Type*} [mX : MeasurableSpace X] {ι : Type*} [Fintype ι]
    {A : ι → Set X} {f : X → X} (hA : IsMPart A) (hf : Measurable f) :
    IsMPart (fun i => f ⁻¹' A i) :=
  ⟨fun i => (hA.measurable i).preimage hf,
   fun i j hij => (hA.disjoint hij).preimage f,
   by rw [← Set.preimage_iUnion, hA.cover, Set.preimage_univ]⟩

/-- The range of a family is unchanged by reindexing along an equivalence. -/
theorem generateFrom_range_equiv {X : Type*} {ι κ : Type*} (e : ι ≃ κ) (A : κ → Set X) :
    MeasurableSpace.generateFrom (Set.range (fun i => A (e i)))
      = MeasurableSpace.generateFrom (Set.range A) := by
  congr 1
  exact Set.ext fun x => by
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨e i, rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨e.symm k, by simp⟩

/-- The canonical equivalence `(Fin 1 → Fin n) ≃ Fin n`. -/
def fin1Equiv (n : ℕ) : (Fin 1 → Fin n) ≃ Fin n where
  toFun v := v 0
  invFun i := fun _ => i
  left_inv v := by funext k; fin_cases k; rfl
  right_inv i := rfl

@[simp] theorem fin1Equiv_apply {n : ℕ} (v : Fin 1 → Fin n) : fin1Equiv n v = v 0 := rfl

/-! ## 2. `Hfam` under a measure-preserving pullback -/

theorem Hfam_preimage {X : Type*} [mX : MeasurableSpace X] {ι : Type*} [Fintype ι]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → X} (hfmp : MeasurePreserving f μ μ)
    {F : ι → Set X} (hF : ∀ i, MeasurableSet (F i)) :
    Hfam μ (fun i => f ⁻¹' F i) = Hfam μ F := by
  simp only [Work.EKLContract.Hfam]
  exact Finset.sum_congr rfl fun i _ =>
    congrArg Real.negMulLog (congrArg ENNReal.toReal
      (hfmp.measure_preimage (hF i).nullMeasurableSet))

/-! ## 3. `HcondFam`: reindexing, integral form and monotonicity -/

/-- Reindexing a family along an equivalence does not change its conditional entropy. -/
theorem HcondFam_equiv_gen {X : Type*} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (𝓕 : MeasurableSpace X) [mX : MeasurableSpace X] (μ : Measure X) (e : ι ≃ κ)
    (A : κ → Set X) :
    HcondFam X μ (fun i => A (e i)) 𝓕 = HcondFam X μ A 𝓕 := by
  unfold Work.EKLComp.Core.HcondFam
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  exact Equiv.sum_comp e
    (fun k => Real.negMulLog (condExp 𝓕 μ ((A k).indicator (fun _ => (1 : ℝ))) x))

/-- `HcondFam` only depends on the family of sets. -/
theorem HcondFam_congr_gen {X : Type*} {ι : Type*} [Fintype ι] (𝓕 : MeasurableSpace X)
    [mX : MeasurableSpace X] (μ : Measure X) {A A' : ι → Set X} (h : ∀ i, A i = A' i) :
    HcondFam X μ A 𝓕 = HcondFam X μ A' 𝓕 := by
  unfold Work.EKLComp.Core.HcondFam
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

/-- `HcondFam` as the sum of the integrals of its individual terms. -/
theorem HcondFam_eq_sum_integral {X : Type*} {ι : Type*} [Fintype ι]
    (𝓕 : MeasurableSpace X) [mX : MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    HcondFam X μ A 𝓕 =
      ∑ i, ∫ x, Real.negMulLog (condExp 𝓕 μ ((A i).indicator (fun _ => (1 : ℝ))) x) ∂μ := by
  unfold Work.EKLComp.Core.HcondFam
  exact integral_finsetSum Finset.univ (fun i _ =>
    Work.EKLC6Core.integrable_negMulLog_condExp μ
      (Filter.Eventually.of_forall fun x => (Work.EKLC6Core.indicator_mem_Icc (A i) x).1)
      (Filter.Eventually.of_forall fun x => (Work.EKLC6Core.indicator_mem_Icc (A i) x).2)
      ((integrable_const (1 : ℝ)).indicator (hA i)))

/-- Conditional entropy is antitone in the conditioning σ-algebra. -/
theorem HcondFam_mono_gen {X : Type*} {ι : Type*} [Fintype ι] {m₁ m₂ : MeasurableSpace X}
    [mX : MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (A : ι → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (h : m₁ ≤ m₂) (hm₂ : m₂ ≤ mX) :
    HcondFam X μ A m₂ ≤ HcondFam X μ A m₁ := by
  rw [HcondFam_eq_sum_integral (𝓕 := m₂) μ A hA,
    HcondFam_eq_sum_integral (𝓕 := m₁) μ A hA]
  refine Finset.sum_le_sum (fun i _ => ?_)
  exact Work.EKLC6Core.integral_negMulLog_condExp_le (μ := μ) (m₁ := m₁) (m₂ := m₂) h
    (le_trans h hm₂)
    (Filter.Eventually.of_forall fun x => (Work.EKLC6Core.indicator_mem_Icc (A i) x).1)
    (Filter.Eventually.of_forall fun x => (Work.EKLC6Core.indicator_mem_Icc (A i) x).2)
    ((integrable_const (1 : ℝ)).indicator (hA i))

/-! ## 4. The entropy chain rule on the level of `Hfam` -/

/-- **Entropy-first bound.**  The entropy of the `N`-fold join of `Q` is at most the entropy of a
finite measurable partition `B` plus the conditional entropy of that join given the σ-algebra of
`B`.  (`Type*` version of `Work.EKLEntJacobs.Hfam_le_Hfam_add_HcondFam`.) -/
theorem Hfam_le_Hfam_add_HcondFam {X : Type*} [mX : MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {T : X → X} (hT : Measurable T) (Q : FinPart X) {κ : Type*}
    [Fintype κ] {B : κ → Set X} (hB : IsMPart B) (N : ℕ) :
    Hfam μ (joinSets T Q N) ≤ Hfam μ B + HcondFam X μ (joinSets T Q N) (partSigmaFam B) := by
  have hA : IsMPart (joinSets T Q N) := joinSets_isMPart hT Q N
  have hP : IsMPart (fun p : (Fin N → Fin Q.n) × κ => joinSets T Q N p.1 ∩ B p.2) :=
    isMPart_prod hA hB
  have h1 : Hfam μ (joinSets T Q N)
      ≤ Hfam μ (fun p : (Fin N → Fin Q.n) × κ => joinSets T Q N p.1 ∩ B p.2) :=
    Hfam_mono μ hA hP (fun p => p.1) (fun p => Set.inter_subset_left)
  have h2 : HcondFam X μ (joinSets T Q N) (partSigmaFam B)
      = Hfam μ (fun p : (Fin N → Fin Q.n) × κ => joinSets T Q N p.1 ∩ B p.2) - Hfam μ B :=
    Work.EKLC6Core.HcondFam_partSigmaFam (mX := mX) μ (joinSets T Q N) B hA hB
  linarith

/-! ## 5. Splitting a join at a cut -/

/-- Splitting an atom of `⋁_{k<N+1}T^{-k}P` at time `0`. -/
theorem joinSets_succ_cons {X : Type*} [mX : MeasurableSpace X] (T : X → X) (P : FinPart X)
    (N : ℕ) (i : Fin P.n) (v : Fin N → Fin P.n) :
    joinSets T P (N + 1) (Fin.cons i v) = P.parts i ∩ T ⁻¹' joinSets T P N v := by
  ext x
  simp only [joinSets, Set.mem_iInter, Set.mem_preimage, Set.mem_inter_iff]
  rw [Fin.forall_fin_succ]
  constructor
  · rintro ⟨h0, hrest⟩
    refine ⟨by simpa using h0, fun k => ?_⟩
    have hk := hrest k
    rw [show ((k.succ : Fin (N + 1)) : ℕ) = Nat.succ (k : ℕ) from rfl,
      Function.iterate_succ_apply] at hk
    exact hk
  · rintro ⟨h0, hrest⟩
    refine ⟨by simpa using h0, fun k => ?_⟩
    rw [show ((k.succ : Fin (N + 1)) : ℕ) = Nat.succ (k : ℕ) from rfl,
      Function.iterate_succ_apply]
    exact hrest k

/-- The conditional entropy of the join splits at a cut `m`. -/
theorem HcondFam_joinSets_append {X : Type*} [mX : MeasurableSpace X] (μ : Measure X)
    (T : X → X) (Q : FinPart X) {θ : Type*} [Fintype θ] {B : θ → Set X} (m n : ℕ) :
    HcondFam X μ (joinSets T Q (m + n)) (partSigmaFam B)
      = HcondFam X μ (fun q : (Fin m → Fin Q.n) × (Fin n → Fin Q.n) =>
          joinSets T Q m q.1 ∩ T^[m] ⁻¹' joinSets T Q n q.2) (partSigmaFam B) := by
  rw [← HcondFam_equiv_gen (partSigmaFam B) μ (Fin.appendEquiv (α := Fin Q.n) m n)
    (joinSets T Q (m + n))]
  exact HcondFam_congr_gen (partSigmaFam B) μ (fun q => joinSets_append T Q m n q.1 q.2)

/-! ## 6. σ-algebra bookkeeping for the orbit σ-algebra -/

/-- `partSigmaFam` of a measurable family is a sub-σ-algebra of the ambient one. -/
theorem partSigmaFam_le_mX {X : Type*} [mX : MeasurableSpace X] {ι : Type*}
    (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i)) : partSigmaFam A ≤ mX := by
  rw [partSigmaFam]
  exact MeasurableSpace.generateFrom_le fun S hS => by
    obtain ⟨i, rfl⟩ := hS
    exact hA i

theorem partSigma_le_mX {X : Type*} [mX : MeasurableSpace X] (P : FinPart X) :
    partSigma P ≤ mX := by
  rw [partSigma]
  exact MeasurableSpace.generateFrom_le fun S hS => by
    obtain ⟨i, rfl⟩ := hS
    exact P.measurable i

/-- `comap T` of the σ-algebra of a family is the σ-algebra of the pulled-back family. -/
theorem comap_partSigmaFam {X : Type*} [mX : MeasurableSpace X] {ι : Type*} (T : X → X)
    (Y : ι → Set X) :
    MeasurableSpace.comap T (partSigmaFam Y) = partSigmaFam (fun i => T ⁻¹' Y i) := by
  rw [partSigmaFam, partSigmaFam, MeasurableSpace.comap_generateFrom]
  congr 1
  rw [show (fun i => T ⁻¹' Y i) = Set.preimage T ∘ Y from rfl, Set.range_comp]

/-- Each atom of the `N`-fold join of `P` is measurable for the forward orbit σ-algebra. -/
theorem partSigmaFam_joinSets_le_iSup {X : Type*} [mX : MeasurableSpace X] (T : X → X)
    (P : FinPart X) (N : ℕ) :
    partSigmaFam (joinSets T P N)
      ≤ ⨆ n : ℕ, MeasurableSpace.comap (T^[n]) (partSigma P) := by
  rw [partSigmaFam]
  refine MeasurableSpace.generateFrom_le ?_
  rintro S ⟨w, rfl⟩
  rw [joinSets]
  refine MeasurableSet.iInter fun k => ?_
  exact le_iSup (fun n : ℕ => MeasurableSpace.comap (T^[n]) (partSigma P)) (k : ℕ) _
    (MeasurableSpace.measurableSet_comap.mpr ⟨P.parts (w k),
      MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self (w k)), rfl⟩)

/-- The pullback of the σ-algebra of the `m`-fold join is contained in the σ-algebra of the
`(m+1)`-fold join. -/
theorem comap_partSigmaFam_joinSets_le {X : Type*} [mX : MeasurableSpace X] (T : X → X)
    (P : FinPart X) (m : ℕ) :
    MeasurableSpace.comap T (partSigmaFam (joinSets T P m))
      ≤ partSigmaFam (joinSets T P (m + 1)) := by
  have hpt : ∀ w : Fin m → Fin P.n, T ⁻¹' joinSets T P m w
      = ⋃ i : Fin P.n, joinSets T P (m + 1) (Fin.cons i w) := by
    intro w
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ : ∃ i, x ∈ P.parts i := by
        have h : x ∈ ⋃ i, P.parts i := by rw [P.cover]; trivial
        simpa only [Set.mem_iUnion] using h
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      rw [joinSets_succ_cons]
      exact ⟨hi, hx⟩
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      rw [joinSets_succ_cons] at hi
      exact hi.2
  rw [partSigmaFam, MeasurableSpace.comap_generateFrom]
  refine MeasurableSpace.generateFrom_le ?_
  rintro S ⟨S', ⟨w, rfl⟩, rfl⟩
  rw [hpt w]
  exact MeasurableSet.iUnion fun i =>
    MeasurableSpace.measurableSet_generateFrom ⟨_, rfl⟩

/-! ## 7. Invariance of `HcondFam` under a measure-preserving pullback -/

/-- Conditional entropy is invariant under a measure-preserving pullback, both in the family and
in the conditioning σ-algebra.  (The proof only uses `HcondFam_partSigmaFam` together with the
invariance of `Hfam` under such a pullback.)

This is the `Type*` version of the invariance of the relative entropy under a measure-preserving
map; it is the key step that moves a shifted family `T^{-k}A` back to `A` while simultaneously
moving the conditioning σ-algebra `T^{-k}σ(C)` back to `σ(C)`. -/
theorem HcondFam_comap_preimage_gen {X : Type*} [mX : MeasurableSpace X] {ι κ : Type*}
    [Fintype ι] [Fintype κ] {T : X → X} (μ : Measure X) [IsProbabilityMeasure μ]
    (hmp : MeasurePreserving T μ μ) {A : ι → Set X} {C : κ → Set X} (hA : IsMPart A)
    (hC : IsMPart C) :
    HcondFam X μ (fun i => T ⁻¹' A i) (partSigmaFam (fun w => T ⁻¹' C w))
      = HcondFam X μ A (partSigmaFam C) := by
  have hApull : IsMPart (fun i => T ⁻¹' A i) := isMPart_preimage hA hmp.measurable
  have hCpull : IsMPart (fun w => T ⁻¹' C w) := isMPart_preimage hC hmp.measurable
  rw [Work.EKLC6Core.HcondFam_partSigmaFam (mX := mX) μ (fun i => T ⁻¹' A i)
        (fun w => T ⁻¹' C w) hApull hCpull,
      Work.EKLC6Core.HcondFam_partSigmaFam (mX := mX) μ A C hA hC]
  have hj : Hfam μ (fun p : ι × κ => T ⁻¹' A p.1 ∩ T ⁻¹' C p.2)
      = Hfam μ (fun p : ι × κ => A p.1 ∩ C p.2) := by
    have h : (fun p : ι × κ => T ⁻¹' A p.1 ∩ T ⁻¹' C p.2)
        = fun p : ι × κ => T ⁻¹' (A p.1 ∩ C p.2) := by
      funext p
      rw [Set.preimage_inter]
    rw [h]
    exact Hfam_preimage (μ := μ) hmp (F := fun p : ι × κ => A p.1 ∩ C p.2)
      (fun p => (hA.measurable p.1).inter (hC.measurable p.2))
  have hc : Hfam μ (fun w => T ⁻¹' C w) = Hfam μ C :=
    Hfam_preimage (μ := μ) hmp (fun w => hC.measurable w)
  rw [hj, hc]

end Work.EKLC6Core.BiGenChain
