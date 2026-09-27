import Mathlib
import Submission.Work.EKLComp.Core
import Submission.Work.EKLComp.Entropy
import Submission.Work.EKLComp.EntPowDefs
import Submission.Work.EKLComp.Hcond
import Submission.Work.EKLC6Core.Hcond_mono
import Submission.Work.EKLC6Core.HcondFam_partSigmaFam

/-!
# `EKLC6Core.BiGenAux` — auxiliary material for the bilateral generating theorem

Everything here is typed at `Type*`, i.e. universe-polymorphic, and self-contained modulo
`Work.EKLComp.Core` / `Work.EKLComp.Entropy` / `Work.EKLComp.Hcond` and the two `Type*` modules
`Work.EKLC6Core.Hcond_mono`, `Work.EKLC6Core.HcondFam_partSigmaFam`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

namespace Work.EKLC6Core.BiGenAux

open Work.EKLContract

variable {X : Type*} [mX : MeasurableSpace X]

/-- `partSigmaFam (joinSets T P N) = ⨆ k : Fin N, comap (T^[k]) (partSigma P)`. -/
theorem partSigmaFam_joinSets (T : X → X) (P : FinPart X) (N : ℕ) :
    Work.EKLComp.Core.partSigmaFam (joinSets T P N) =
      ⨆ k : Fin N, MeasurableSpace.comap (T^[(k : ℕ)]) (partSigma P) := by
  apply le_antisymm
  · rw [Work.EKLComp.Core.partSigmaFam]
    refine MeasurableSpace.generateFrom_le ?_
    rintro S ⟨w, rfl⟩
    rw [joinSets]
    refine MeasurableSet.iInter fun k => ?_
    exact le_iSup (fun k : Fin N =>
        MeasurableSpace.comap (T^[(k : ℕ)]) (partSigma P)) k _
      ⟨P.parts (w k), MeasurableSpace.measurableSet_generateFrom ⟨w k, rfl⟩, rfl⟩
  · refine iSup_le fun k => ?_
    rw [partSigma, MeasurableSpace.comap_generateFrom]
    refine MeasurableSpace.generateFrom_le ?_
    rintro S ⟨A, ⟨i, rfl⟩, rfl⟩
    have hkey : (T^[(k : ℕ)]) ⁻¹' P.parts i =
        ⋃ w : {w : Fin N → Fin P.n // w k = i}, joinSets T P N w.1 := by
      ext x
      simp only [Set.mem_preimage, Set.mem_iUnion, Subtype.exists, exists_prop]
      constructor
      · intro hx
        have hcov : x ∈ ⋃ w : Fin N → Fin P.n, joinSets T P N w := by
          rw [Work.EKLComp.Core.joinSets_iUnion]; trivial
        obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hcov
        have hwk : w k = i := by
          by_contra hne
          have h1 : T^[(k : ℕ)] x ∈ P.parts (w k) := Set.mem_iInter.mp hw k
          exact Set.disjoint_left.mp (P.disjoint hne) h1 hx
        exact ⟨w, hwk, hw⟩
      · rintro ⟨w, hwk, hw⟩
        rw [← hwk]
        exact Set.mem_iInter.mp hw k
    rw [hkey]
    exact MeasurableSet.iUnion fun w =>
      MeasurableSpace.measurableSet_generateFrom ⟨w.1, rfl⟩

/-! ## The `FinPart` attached to an `IsMPart` family -/

/-- A `FinPart` built from an `IsMPart` family over an arbitrary finite index type. -/
def finPartOfFamily {ι : Type*} [Fintype ι] (A : ι → Set X)
    (hA : Work.EKLComp.Core.IsMPart A) : FinPart X where
  n := Fintype.card ι
  parts := fun k => A ((Fintype.equivFin ι).symm k)
  measurable := fun k => hA.measurable _
  disjoint := fun k l hkl =>
    hA.disjoint (fun h => hkl ((Fintype.equivFin ι).symm.injective h))
  cover := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have h : x ∈ ⋃ i, A i := by rw [hA.cover]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    refine Set.mem_iUnion.mpr ⟨Fintype.equivFin ι i, ?_⟩
    show x ∈ A ((Fintype.equivFin ι).symm (Fintype.equivFin ι i))
    rwa [Equiv.symm_apply_apply]

theorem partSigma_finPartOfFamily {ι : Type*} [Fintype ι] (A : ι → Set X)
    (hA : Work.EKLComp.Core.IsMPart A) :
    partSigma (finPartOfFamily A hA) = Work.EKLComp.Core.partSigmaFam A := by
  have h : (finPartOfFamily A hA).parts
      = (fun k => A ((Fintype.equivFin ι).symm k)) := rfl
  rw [partSigma, Work.EKLComp.Core.partSigmaFam, h]
  congr 1
  ext s
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨(Fintype.equivFin ι).symm k, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Fintype.equivFin ι i, by simp⟩

theorem Hfam_finPartOfFamily (μ : Measure X) {ι : Type*} [Fintype ι] (A : ι → Set X)
    (hA : Work.EKLComp.Core.IsMPart A) :
    Hfam μ (finPartOfFamily A hA).parts = Hfam μ A := by
  have h : (finPartOfFamily A hA).parts
      = (fun k => A ((Fintype.equivFin ι).symm k)) := rfl
  rw [h]
  exact Work.EKLComp.Core.Hfam_equiv μ (Fintype.equivFin ι).symm A

/-! ## The binary join of two finite partitions -/

/-- The common refinement (binary join) of two finite partitions. -/
def joinPair (P Q : FinPart X) : FinPart X where
  n := P.n * Q.n
  parts := fun k => P.parts (finProdFinEquiv.symm k).1 ∩ Q.parts (finProdFinEquiv.symm k).2
  measurable := fun k => (P.measurable _).inter (Q.measurable _)
  disjoint := by
    rw [Pairwise]
    intro k l hkl
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rw [Set.mem_inter_iff] at hx1 hx2
    by_cases h1 : (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm l).1
    · have h2 : (finProdFinEquiv.symm k).2 ≠ (finProdFinEquiv.symm l).2 := by
        intro h2
        refine hkl ?_
        have hp : finProdFinEquiv.symm k = finProdFinEquiv.symm l := Prod.ext h1 h2
        rw [← Equiv.apply_symm_apply finProdFinEquiv k,
          ← Equiv.apply_symm_apply finProdFinEquiv l, hp]
      exact (Q.disjoint h2).le_bot ⟨hx1.2, hx2.2⟩
    · exact (P.disjoint h1).le_bot ⟨hx1.1, hx2.1⟩
  cover := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hxP : x ∈ ⋃ i, P.parts i := by rw [P.cover]; exact Set.mem_univ x
    have hxQ : x ∈ ⋃ j, Q.parts j := by rw [Q.cover]; exact Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxP
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxQ
    refine Set.mem_iUnion.mpr ⟨finProdFinEquiv (i, j), ?_⟩
    have hk : finProdFinEquiv.symm (finProdFinEquiv (i, j)) = (i, j) :=
      Equiv.symm_apply_apply _ _
    rw [hk]
    exact ⟨hi, hj⟩

@[simp] theorem joinPair_n (P Q : FinPart X) : (joinPair P Q).n = P.n * Q.n := rfl

theorem joinPair_parts_symm (P Q : FinPart X) (k : Fin (P.n * Q.n)) :
    (joinPair P Q).parts k
      = P.parts (finProdFinEquiv.symm k).1 ∩ Q.parts (finProdFinEquiv.symm k).2 := rfl

theorem joinPair_parts (P Q : FinPart X) (i : Fin P.n) (j : Fin Q.n) :
    (joinPair P Q).parts (finProdFinEquiv (i, j)) = P.parts i ∩ Q.parts j := by
  rw [joinPair_parts_symm, Equiv.symm_apply_apply]

theorem partSigma_joinPair (P Q : FinPart X) :
    partSigma (joinPair P Q) = partSigma P ⊔ partSigma Q := by
  refine le_antisymm ?_ ?_
  · rw [partSigma]
    refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨k, rfl⟩
    have hP : MeasurableSet[partSigma P] (P.parts (finProdFinEquiv.symm k).1) :=
      MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self _)
    have hQ : MeasurableSet[partSigma Q] (Q.parts (finProdFinEquiv.symm k).2) :=
      MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self _)
    exact MeasurableSet.inter (MeasurableSpace.le_def.mp le_sup_left _ hP)
      (MeasurableSpace.le_def.mp le_sup_right _ hQ)
  · refine sup_le ?_ ?_
    · rw [partSigma]
      refine MeasurableSpace.generateFrom_le ?_
      rintro s ⟨i, rfl⟩
      have h : P.parts i = ⋃ j : Fin Q.n, (joinPair P Q).parts (finProdFinEquiv (i, j)) := by
        ext x
        constructor
        · intro hx
          have hxQ : x ∈ ⋃ j, Q.parts j := by rw [Q.cover]; exact Set.mem_univ x
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxQ
          exact Set.mem_iUnion.mpr ⟨j, by rw [joinPair_parts]; exact ⟨hx, hj⟩⟩
        · intro hx
          obtain ⟨j, hx'⟩ := Set.mem_iUnion.mp hx
          rw [joinPair_parts] at hx'
          exact hx'.1
      rw [h]
      exact MeasurableSet.iUnion fun j =>
        MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self _)
    · rw [partSigma]
      refine MeasurableSpace.generateFrom_le ?_
      rintro s ⟨j, rfl⟩
      have h : Q.parts j = ⋃ i : Fin P.n, (joinPair P Q).parts (finProdFinEquiv (i, j)) := by
        ext x
        constructor
        · intro hx
          have hxP : x ∈ ⋃ i, P.parts i := by rw [P.cover]; exact Set.mem_univ x
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxP
          exact Set.mem_iUnion.mpr ⟨i, by rw [joinPair_parts]; exact ⟨hi, hx⟩⟩
        · intro hx
          obtain ⟨i, hx'⟩ := Set.mem_iUnion.mp hx
          rw [joinPair_parts] at hx'
          exact hx'.2
      rw [h]
      exact MeasurableSet.iUnion fun i =>
        MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self _)

theorem Hfam_joinPair_le (μ : Measure X) [IsProbabilityMeasure μ] (P Q : FinPart X) :
    Hfam μ (joinPair P Q).parts ≤ Hfam μ P.parts + Hfam μ Q.parts := by
  have h1 : Hfam μ (joinPair P Q).parts
      = Hfam μ (fun i : Fin P.n × Fin Q.n => (joinPair P Q).parts (finProdFinEquiv i)) :=
    (Work.EKLComp.Core.Hfam_equiv μ (finProdFinEquiv (m := P.n) (n := Q.n))
      (joinPair P Q).parts).symm
  have h2 : (fun i : Fin P.n × Fin Q.n => (joinPair P Q).parts (finProdFinEquiv i))
      = (fun q : Fin P.n × Fin Q.n => P.parts q.1 ∩ Q.parts q.2) := by
    funext q; rw [joinPair_parts]
  rw [h1, h2]
  exact Work.EKLComp.Core.Hfam_inter_le μ ⟨P.measurable, P.disjoint, P.cover⟩
    ⟨Q.measurable, Q.disjoint, Q.cover⟩

/-! ## Pullback of a finite partition -/

/-- The pullback of a finite partition along a measurable map. -/
def comapPart (f : X → X) (hf : Measurable f) (P : FinPart X) : FinPart X where
  n := P.n
  parts := fun i => f ⁻¹' P.parts i
  measurable := fun i => (P.measurable i).preimage hf
  disjoint := fun i j hij => (P.disjoint hij).preimage _
  cover := by
    rw [← Set.preimage_iUnion, P.cover, Set.preimage_univ]

@[simp] theorem comapPart_n (f : X → X) (hf : Measurable f) (P : FinPart X) :
    (comapPart f hf P).n = P.n := rfl

@[simp] theorem comapPart_parts (f : X → X) (hf : Measurable f) (P : FinPart X)
    (i : Fin P.n) : (comapPart f hf P).parts i = f ⁻¹' P.parts i := rfl

theorem partSigma_comapPart (f : X → X) (hf : Measurable f) (P : FinPart X) :
    partSigma (comapPart f hf P) = MeasurableSpace.comap f (partSigma P) := by
  rw [partSigma, partSigma, MeasurableSpace.comap_generateFrom]
  congr 1
  ext s
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨P.parts i, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨t, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

/-! ## Iterates of a map and its left inverse -/

/-- If `S` is a left inverse of `T`, then `S^[b] ∘ T^[j] = T^[j-b]` for `b ≤ j`. -/
theorem iterate_comp_of_leftInverse_le {T S : X → X} (h : Function.LeftInverse S T)
    {b j : ℕ} (hbj : b ≤ j) : (S^[b]) ∘ (T^[j]) = T^[j - b] := by
  funext x
  show S^[b] (T^[j] x) = T^[j - b] x
  have h1 : T^[j] x = T^[b] (T^[j - b] x) := by
    conv_lhs => rw [show j = b + (j - b) by omega]
    rw [Function.iterate_add_apply]
  rw [h1]
  exact h.iterate b (T^[j - b] x)

/-- If `S` is a left inverse of `T`, then `S^[b] ∘ T^[j] = S^[b-j]` for `j ≤ b`. -/
theorem iterate_comp_of_leftInverse_ge {T S : X → X} (h : Function.LeftInverse S T)
    {b j : ℕ} (hjb : j ≤ b) : (S^[b]) ∘ (T^[j]) = S^[b - j] := by
  funext x
  show S^[b] (T^[j] x) = S^[b - j] x
  have hb : b = (b - j) + j := (Nat.sub_add_cancel hjb).symm
  conv_lhs => rw [hb]
  rw [Function.iterate_add_apply, h.iterate j x]

/-! ## Unions of atoms -/

theorem partUnion_compl (R : FinPart X) (J : Set (Fin R.n)) :
    (⋃ j ∈ J, R.parts j)ᶜ = ⋃ j ∈ Jᶜ, R.parts j := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_iUnion]
  constructor
  · intro hx
    have hxuniv : x ∈ ⋃ i, R.parts i := by rw [R.cover]; exact Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxuniv
    exact ⟨i, fun hiJ => hx ⟨i, hiJ, hi⟩, hi⟩
  · rintro ⟨i, hiJ, hi⟩ ⟨j, hjJ, hj⟩
    have hne : j ≠ i := fun h => hiJ (h ▸ hjJ)
    exact (Set.disjoint_left.mp (R.disjoint hne) hj) hi

theorem partUnion_iUnion (R : FinPart X) (J : ℕ → Set (Fin R.n)) :
    (⋃ k : ℕ, ⋃ j ∈ J k, R.parts j) = ⋃ j ∈ (⋃ k : ℕ, J k), R.parts j := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨k, j, hj, hx⟩
    exact ⟨j, ⟨k, hj⟩, hx⟩
  · rintro ⟨j, ⟨k, hj⟩, hx⟩
    exact ⟨k, j, hj, hx⟩

/-- The σ-algebra of unions of parts of a finite partition. -/
def partUnionSigma (R : FinPart X) : MeasurableSpace X where
  MeasurableSet' S := ∃ J : Set (Fin R.n), S = ⋃ j ∈ J, R.parts j
  measurableSet_empty := ⟨∅, by simp⟩
  measurableSet_compl := by
    rintro S ⟨J, rfl⟩
    exact ⟨Jᶜ, partUnion_compl R J⟩
  measurableSet_iUnion := by
    intro f hf
    choose J hJ using hf
    refine ⟨⋃ k, J k, ?_⟩
    simp only [hJ]
    exact partUnion_iUnion R J

/-- A set is measurable for `partSigma R` iff it is a union of atoms of `R`. -/
theorem partSigma_eq_unions_atoms (R : FinPart X) (S : Set X) :
    (partSigma R).MeasurableSet' S ↔ ∃ J : Set (Fin R.n), S = ⋃ j ∈ J, R.parts j := by
  have hle : partSigma R ≤ partUnionSigma R := by
    rw [partSigma]
    refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨i, rfl⟩
    exact ⟨{i}, by ext x; simp⟩
  constructor
  · intro hS
    exact hle S hS
  · rintro ⟨J, rfl⟩
    exact Set.Finite.measurableSet_biUnion (Set.toFinite J)
      fun j _ => MeasurableSpace.measurableSet_generateFrom ⟨j, rfl⟩

/-! ## Monotonicity of `Hfam` under a generating σ-algebra inclusion -/

/-- If every atom of an `IsMPart` family `A` is measurable for `partSigma R`, then
`Hfam μ A ≤ Hfam μ R.parts`. -/
theorem Hfam_le_of_partSigma_le {ι : Type*} [Fintype ι] (μ : Measure X)
    [IsProbabilityMeasure μ] (A : ι → Set X) (hA : Work.EKLComp.Core.IsMPart A)
    (R : FinPart X) (hle : Work.EKLComp.Core.partSigmaFam A ≤ partSigma R) :
    Hfam μ A ≤ Hfam μ R.parts := by
  classical
  have hX : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    haveI := h
    have hempty : (Set.univ : Set X) = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun x => isEmptyElim x)
    have h0 : μ (Set.univ : Set X) = 0 := by rw [hempty, measure_empty]
    rw [measure_univ] at h0
    norm_num at h0
  have hι : Nonempty ι := by
    obtain ⟨x⟩ := hX
    have : x ∈ ⋃ i, A i := by rw [hA.cover]; trivial
    obtain ⟨i, -⟩ := Set.mem_iUnion.mp this
    exact ⟨i⟩
  have hkey : ∀ j : Fin R.n, ∃ i, R.parts j ⊆ A i := by
    intro j
    by_cases hne : (R.parts j).Nonempty
    · obtain ⟨x, hx⟩ := hne
      have hxuniv : x ∈ ⋃ i, A i := by rw [hA.cover]; trivial
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxuniv
      refine ⟨i, ?_⟩
      have hmeas : (partSigma R).MeasurableSet' (A i) :=
        hle (A i) (MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self i))
      obtain ⟨J, hJ⟩ := (partSigma_eq_unions_atoms R (A i)).mp hmeas
      have hxJ : x ∈ ⋃ j' ∈ J, R.parts j' := by rw [← hJ]; exact hxi
      obtain ⟨j', hj'J, hxj'⟩ := Set.mem_iUnion₂.mp hxJ
      have hjj : j' = j := by
        by_contra hne'
        exact Set.disjoint_left.mp (R.disjoint hne') hxj' hx
      intro y hy
      have : y ∈ ⋃ j' ∈ J, R.parts j' := Set.mem_iUnion₂.mpr ⟨j, hjj ▸ hj'J, hy⟩
      rw [← hJ] at this
      exact this
    · have hempty : R.parts j = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr (fun x hx => hne ⟨x, hx⟩)
      exact ⟨Classical.choice hι, by rw [hempty]; exact Set.empty_subset _⟩
  choose f hf using hkey
  exact Work.EKLComp.Core.Hfam_mono μ hA ⟨R.measurable, R.disjoint, R.cover⟩ f hf
/-! ## Products of partitions -/

theorem isMPart_inter_prod {ι κ : Type*} [Fintype ι] [Fintype κ] {A : ι → Set X}
    {B : κ → Set X} (hA : Work.EKLComp.Core.IsMPart A) (hB : Work.EKLComp.Core.IsMPart B) :
    Work.EKLComp.Core.IsMPart (fun p : ι × κ => A p.1 ∩ B p.2) := by
  refine ⟨fun p => (hA.measurable p.1).inter (hB.measurable p.2), ?_, ?_⟩
  · rintro ⟨i, j⟩ ⟨i', j'⟩ hne
    rcases eq_or_ne i i' with h | h
    · subst h
      have hjj' : j ≠ j' := fun h' => hne (by rw [h'])
      exact (hB.disjoint hjj').mono Set.inter_subset_right Set.inter_subset_right
    · exact (hA.disjoint h).mono Set.inter_subset_left Set.inter_subset_left
  · ext x
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨i, hi⟩ : ∃ i, x ∈ A i := by
        have h : x ∈ ⋃ i, A i := by rw [hA.cover]; trivial
        simpa only [Set.mem_iUnion] using h
      obtain ⟨j, hj⟩ : ∃ j, x ∈ B j := by
        have h : x ∈ ⋃ j, B j := by rw [hB.cover]; trivial
        simpa only [Set.mem_iUnion] using h
      exact Set.mem_iUnion.mpr ⟨(i, j), hi, hj⟩

theorem partSigmaFam_prod {ι κ : Type*} [Fintype ι] [Fintype κ] {A : ι → Set X}
    {B : κ → Set X} (hA : Work.EKLComp.Core.IsMPart A) (hB : Work.EKLComp.Core.IsMPart B) :
    Work.EKLComp.Core.partSigmaFam (fun p : ι × κ => A p.1 ∩ B p.2)
      = Work.EKLComp.Core.partSigmaFam A ⊔ Work.EKLComp.Core.partSigmaFam B := by
  refine le_antisymm ?_ ?_
  · rw [Work.EKLComp.Core.partSigmaFam]
    refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨p, rfl⟩
    have h1 : MeasurableSet[Work.EKLComp.Core.partSigmaFam A] (A p.1) :=
      MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self _)
    have h2 : MeasurableSet[Work.EKLComp.Core.partSigmaFam B] (B p.2) :=
      MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self _)
    exact MeasurableSet.inter (MeasurableSpace.le_def.mp le_sup_left _ h1)
      (MeasurableSpace.le_def.mp le_sup_right _ h2)
  · refine sup_le ?_ ?_
    · rw [Work.EKLComp.Core.partSigmaFam]
      refine MeasurableSpace.generateFrom_le ?_
      rintro s ⟨i, rfl⟩
      have h : A i = ⋃ j : κ, (fun p : ι × κ => A p.1 ∩ B p.2) (i, j) := by
        ext x
        constructor
        · intro hx
          have hxuniv : x ∈ ⋃ j, B j := by rw [hB.cover]; exact Set.mem_univ x
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxuniv
          exact Set.mem_iUnion.mpr ⟨j, ⟨hx, hj⟩⟩
        · intro hx
          obtain ⟨j, hx'⟩ := Set.mem_iUnion.mp hx
          exact hx'.1
      rw [h]
      exact MeasurableSet.iUnion fun j =>
        MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self _)
    · rw [Work.EKLComp.Core.partSigmaFam]
      refine MeasurableSpace.generateFrom_le ?_
      rintro s ⟨j, rfl⟩
      have h : B j = ⋃ i : ι, (fun p : ι × κ => A p.1 ∩ B p.2) (i, j) := by
        ext x
        constructor
        · intro hx
          have hxuniv : x ∈ ⋃ i, A i := by rw [hA.cover]; exact Set.mem_univ x
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxuniv
          exact Set.mem_iUnion.mpr ⟨i, ⟨hi, hx⟩⟩
        · intro hx
          obtain ⟨i, hx'⟩ := Set.mem_iUnion.mp hx
          exact hx'.2
      rw [h]
      exact MeasurableSet.iUnion fun i =>
        MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self _)

/-! ## `Hfam` of a diagonal product -/

theorem Hfam_prod_diag (μ : Measure X) [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {A : ι → Set X} (hA : Work.EKLComp.Core.IsMPart A) :
    Hfam μ (fun p : ι × ι => A p.1 ∩ A p.2) = Hfam μ A := by
  rw [Hfam, Hfam, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Set.inter_self]
  · intro j _ hji
    have hdisj : A i ∩ A j = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp (hA.disjoint (Ne.symm hji))
    rw [hdisj, measure_empty, ENNReal.toReal_zero, Real.negMulLog_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-! ## Vanishing of the conditional entropy against one's own σ-algebra -/

theorem Hcond_partSigma_eq_zero (μ : Measure X) [IsProbabilityMeasure μ] (Q : FinPart X) :
    @Hcond X mX μ Q (partSigma Q) = 0 := by
  have hQ : Work.EKLComp.Core.IsMPart Q.parts := ⟨Q.measurable, Q.disjoint, Q.cover⟩
  have h1 : @Hcond X mX μ Q (partSigma Q)
      = Work.EKLComp.Core.HcondFam X μ Q.parts
          (Work.EKLComp.Core.partSigmaFam Q.parts) :=
    (Work.EKLComp.Core.HcondFam_eq_Hcond μ Q (partSigma Q)).symm
  rw [h1, Work.EKLC6Core.HcondFam_partSigmaFam (mX := mX) μ Q.parts Q.parts hQ hQ,
    Hfam_prod_diag μ hQ]
  ring

theorem Hcond_top_le_zero (μ : Measure X) [IsProbabilityMeasure μ] (Q : FinPart X) :
    @Hcond X mX μ Q mX ≤ 0 := by
  have hle : partSigma Q ≤ mX := by
    rw [partSigma]
    refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨i, rfl⟩
    exact Q.measurable i
  have h := Work.EKLC6Core.Hcond_mono μ Q (partSigma Q) mX hle
  rw [Hcond_partSigma_eq_zero μ Q] at h
  exact h

/-! ## Fekete's lemma for `hPart` -/

theorem tendsto_hPart (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hmp : MeasurePreserving T μ μ) (P : FinPart X) :
    Filter.Tendsto (fun M : ℕ => Hfam μ (joinSets T P M) / (M : ℝ))
      Filter.atTop (nhds (@hPart X mX μ T P)) := by
  have hsub : Subadditive (fun N => Hfam μ (joinSets T P N)) :=
    fun m n => Work.EKLComp.Core.Hfam_joinSets_add_le μ hmp P m n
  have hbdd : BddBelow (Set.range fun n : ℕ =>
      Hfam μ (joinSets T P n) / (n : ℝ)) :=
    ⟨0, by rintro _ ⟨n, rfl⟩
           exact div_nonneg (Work.EKLComp.Core.Hfam_nonneg μ _) (Nat.cast_nonneg n)⟩
  have hlim := hsub.tendsto_lim hbdd
  have heq := Work.EKLComp.Core.hPart_eq_lim μ hmp P hsub
  rw [heq]
  exact hlim

/-! ## Martingale convergence of the conditional entropy -/

theorem condExp_indicator_mem_Icc (μ : Measure X) [IsProbabilityMeasure μ]
    (m : MeasurableSpace X) (hm : m ≤ mX) (s : Set X) :
    ∀ᵐ x ∂μ, condExp m μ (s.indicator (fun _ => (1 : ℝ))) x ∈ Set.Icc (0 : ℝ) 1 := by
  rcases Classical.em (Integrable (s.indicator (fun _ => (1 : ℝ))) μ) with hf | hf
  · have hlow : (0 : X → ℝ) ≤ᵐ[μ] condExp m μ (s.indicator (fun _ => (1 : ℝ))) :=
      condExp_nonneg
        (Filter.Eventually.of_forall (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x))
    have hup : condExp m μ (s.indicator (fun _ => (1 : ℝ))) ≤ᵐ[μ] (1 : X → ℝ) := by
      have h : condExp m μ (s.indicator (fun _ => (1 : ℝ))) ≤ᵐ[μ] condExp m μ (fun _ => (1 : ℝ)) :=
        condExp_mono hf (integrable_const (1 : ℝ))
          (Filter.Eventually.of_forall (fun x => by
            by_cases hx : x ∈ s
            · simp [Set.indicator_of_mem hx]
            · simp [Set.indicator_of_notMem hx]))
      rwa [condExp_const hm (1 : ℝ)] at h
    filter_upwards [hlow, hup] with x hx1 hx2
    exact ⟨hx1, hx2⟩
  · rw [condExp_of_not_integrable hf]
    exact Filter.Eventually.of_forall (fun x => by simp)

theorem HcondFam_tendsto (μ : Measure X) [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] (A : ι → Set X) (mseq : ℕ → MeasurableSpace X)
    (hmono : Monotone mseq) (hle : ∀ n, mseq n ≤ mX) :
    Filter.Tendsto (fun n => Work.EKLComp.Core.HcondFam X μ A (mseq n)) Filter.atTop
      (nhds (Work.EKLComp.Core.HcondFam X μ A (⨆ n, mseq n))) := by
  classical
  let f : ι → X → ℝ := fun i => (A i).indicator (fun _ => (1 : ℝ))
  have hconv_i : ∀ i, ∀ᵐ x ∂μ,
      Filter.Tendsto (fun n => condExp (mseq n) μ (f i) x) Filter.atTop
        (nhds (condExp (⨆ n, mseq n) μ (f i) x)) := by
    intro i
    have h := tendsto_ae_condExp (μ := μ)
      (ℱ := (⟨mseq, hmono, hle⟩ : Filtration ℕ mX)) (f i)
    exact h
  have hmem_i : ∀ n i, ∀ᵐ x ∂μ, condExp (mseq n) μ (f i) x ∈ Set.Icc (0 : ℝ) 1 :=
    fun n i => condExp_indicator_mem_Icc μ (mseq n) (hle n) (A i)
  have haesm : ∀ n, AEStronglyMeasurable
      (fun x => ∑ i, Real.negMulLog (condExp (mseq n) μ (f i) x)) μ := by
    intro n
    have h : AEStronglyMeasurable
        (∑ i : ι, fun x => Real.negMulLog (condExp (mseq n) μ (f i) x)) μ :=
      Finset.aestronglyMeasurable_sum Finset.univ (fun i _ =>
        Real.continuous_negMulLog.comp_aestronglyMeasurable
          ((stronglyMeasurable_condExp.mono (hle n)).aestronglyMeasurable))
    simpa [Finset.sum_fn] using h
  have hbdd : ∀ n, ∀ᵐ x ∂μ,
      ‖∑ i, Real.negMulLog (condExp (mseq n) μ (f i) x)‖ ≤ (Fintype.card ι : ℝ) := by
    intro n
    have hmem : ∀ᵐ x ∂μ, ∀ i,
        condExp (mseq n) μ (f i) x ∈ Set.Icc (0 : ℝ) 1 :=
      (ae_all_iff (μ := μ)).mpr (fun i => hmem_i n i)
    filter_upwards [hmem] with x hx
    have hnn : 0 ≤ ∑ i, Real.negMulLog (condExp (mseq n) μ (f i) x) :=
      Finset.sum_nonneg (fun i _ => Real.negMulLog_nonneg (hx i).1 (hx i).2)
    rw [Real.norm_of_nonneg hnn]
    calc ∑ i, Real.negMulLog (condExp (mseq n) μ (f i) x)
        ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by
            have h1 := Real.negMulLog_le_one_sub_self (hx i).1
            linarith [(hx i).1])
      _ = (Fintype.card ι : ℝ) := by simp
  have hlim : ∀ᵐ x ∂μ, Filter.Tendsto
      (fun n => ∑ i, Real.negMulLog (condExp (mseq n) μ (f i) x)) Filter.atTop
      (nhds (∑ i, Real.negMulLog (condExp (⨆ n, mseq n) μ (f i) x))) := by
    have hterm : ∀ i, ∀ᵐ x ∂μ, Filter.Tendsto
        (fun n => Real.negMulLog (condExp (mseq n) μ (f i) x)) Filter.atTop
        (nhds (Real.negMulLog (condExp (⨆ n, mseq n) μ (f i) x))) := by
      intro i
      filter_upwards [hconv_i i] with x hx
      exact (Real.continuous_negMulLog.tendsto _).comp hx
    have hterm' := (ae_all_iff (μ := μ)).mpr hterm
    filter_upwards [hterm'] with x hx
    exact tendsto_finsetSum Finset.univ (fun i _ => hx i)
  have hmain := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n x => ∑ i, Real.negMulLog (condExp (mseq n) μ (f i) x))
      (f := fun x => ∑ i, Real.negMulLog (condExp (⨆ n, mseq n) μ (f i) x))
      (fun _ : X => (Fintype.card ι : ℝ))
      haesm (integrable_const _) hbdd hlim
  simpa only [Work.EKLComp.Core.HcondFam] using hmain
/-! ## The one-sided window partition `⋁_{1 ≤ b ≤ l} Tinv^{-b} P` -/

/-- The window partition `⋁_{1 ≤ b ≤ l} Tinv^{-b} P`. -/
def winPart (Tinv : X → X) (hTinv : Measurable Tinv) (P : FinPart X) (l : ℕ) : FinPart X :=
  Work.EKLComp.joinPart hTinv (comapPart Tinv hTinv P) l

theorem partSigma_joinPart_eq {T : X → X} (hT : Measurable T) (Q : FinPart X) (N : ℕ) :
    partSigma (Work.EKLComp.joinPart hT Q N)
      = Work.EKLComp.Core.partSigmaFam (joinSets T Q N) := by
  have hparts : (Work.EKLComp.joinPart hT Q N).parts
      = (fun i => joinSets T Q N ((finFunctionFinEquiv (m := Q.n) (n := N)).symm i)) := rfl
  rw [partSigma, hparts]
  show MeasurableSpace.generateFrom
      (Set.range (fun i => joinSets T Q N
        ((finFunctionFinEquiv (m := Q.n) (n := N)).symm i)))
    = MeasurableSpace.generateFrom (Set.range (joinSets T Q N))
  congr 1
  show Set.range ((joinSets T Q N) ∘ (finFunctionFinEquiv (m := Q.n) (n := N)).symm)
      = Set.range (joinSets T Q N)
  rw [Set.range_comp, (Equiv.surjective (finFunctionFinEquiv (m := Q.n) (n := N)).symm).range_eq,
    Set.image_univ]

theorem partSigmaFam_winPart_eq (Tinv : X → X) (hTinv : Measurable Tinv) (P : FinPart X)
    (l : ℕ) :
    Work.EKLComp.Core.partSigmaFam (joinSets Tinv (comapPart Tinv hTinv P) l)
      = ⨆ i : Fin l, MeasurableSpace.comap (Tinv^[(i : ℕ) + 1]) (partSigma P) := by
  rw [partSigmaFam_joinSets]
  refine iSup_congr fun i => ?_
  rw [partSigma_comapPart, MeasurableSpace.comap_comp]
  congr 1
  funext x
  rw [Function.comp_apply, Function.iterate_succ_apply']

theorem partSigma_winPart (Tinv : X → X) (hTinv : Measurable Tinv) (P : FinPart X) (l : ℕ) :
    partSigma (winPart Tinv hTinv P l)
      = ⨆ i : Fin l, MeasurableSpace.comap (Tinv^[(i : ℕ) + 1]) (partSigma P) := by
  rw [winPart, partSigma_joinPart_eq, partSigmaFam_winPart_eq]

/-- The σ-algebra of the `N`-fold join along `T` of the window is contained in the join of the
σ-algebras of `⋁_{j<N} T^{-j}P` and of the window itself. -/
theorem partSigmaFam_winPart_le {T Tinv : X → X} (hinv : Function.LeftInverse Tinv T)
    (hT : Measurable T) (hTinv : Measurable Tinv) (P : FinPart X) {N : ℕ} (hN : 1 ≤ N)
    (l : ℕ) :
    Work.EKLComp.Core.partSigmaFam (joinSets T (winPart Tinv hTinv P l) N)
      ≤ Work.EKLComp.Core.partSigmaFam
          (fun p : (Fin N → Fin P.n) × (Fin l → Fin P.n) =>
            joinSets T P N p.1 ∩ joinSets Tinv (comapPart Tinv hTinv P) l p.2) := by
  have hwin := partSigma_winPart Tinv hTinv P l
  have hprod := partSigmaFam_prod (Work.EKLComp.Core.joinSets_isMPart hT P N)
      (Work.EKLComp.Core.joinSets_isMPart hTinv (comapPart Tinv hTinv P) l)
  have hG : (⨆ a : Fin N, MeasurableSpace.comap (T^[(a : ℕ)]) (partSigma P))
      ≤ Work.EKLComp.Core.partSigmaFam
          (fun p : (Fin N → Fin P.n) × (Fin l → Fin P.n) =>
            joinSets T P N p.1 ∩ joinSets Tinv (comapPart Tinv hTinv P) l p.2) := by
    calc (⨆ a : Fin N, MeasurableSpace.comap (T^[(a : ℕ)]) (partSigma P))
        = Work.EKLComp.Core.partSigmaFam (joinSets T P N) :=
          (partSigmaFam_joinSets T P N).symm
      _ ≤ Work.EKLComp.Core.partSigmaFam (joinSets T P N)
            ⊔ Work.EKLComp.Core.partSigmaFam
                (joinSets Tinv (comapPart Tinv hTinv P) l) := le_sup_left
      _ = _ := hprod.symm
  have hW : (⨆ i : Fin l, MeasurableSpace.comap (Tinv^[(i : ℕ) + 1]) (partSigma P))
      ≤ Work.EKLComp.Core.partSigmaFam
          (fun p : (Fin N → Fin P.n) × (Fin l → Fin P.n) =>
            joinSets T P N p.1 ∩ joinSets Tinv (comapPart Tinv hTinv P) l p.2) := by
    calc (⨆ i : Fin l, MeasurableSpace.comap (Tinv^[(i : ℕ) + 1]) (partSigma P))
        = Work.EKLComp.Core.partSigmaFam
            (joinSets Tinv (comapPart Tinv hTinv P) l) :=
          (partSigmaFam_winPart_eq Tinv hTinv P l).symm
      _ ≤ Work.EKLComp.Core.partSigmaFam (joinSets T P N)
            ⊔ Work.EKLComp.Core.partSigmaFam
                (joinSets Tinv (comapPart Tinv hTinv P) l) := le_sup_right
      _ = _ := hprod.symm
  rw [partSigmaFam_joinSets]
  refine iSup_le fun j => ?_
  rw [hwin, MeasurableSpace.comap_iSup]
  refine iSup_le fun i => ?_
  rw [MeasurableSpace.comap_comp]
  by_cases hji : (i : ℕ) + 1 ≤ (j : ℕ)
  · rw [iterate_comp_of_leftInverse_le hinv hji]
    exact le_trans (le_iSup (fun a : Fin N => MeasurableSpace.comap (T^[(a : ℕ)])
      (partSigma P)) ⟨(j : ℕ) - ((i : ℕ) + 1), by have := j.isLt; omega⟩) hG
  · push_neg at hji
    rw [iterate_comp_of_leftInverse_ge hinv (le_of_lt hji)]
    by_cases he : (i : ℕ) + 1 - (j : ℕ) = 0
    · rw [he, Function.iterate_zero, MeasurableSpace.comap_id]
      refine le_trans ?_ hG
      have hlt := le_iSup (fun a : Fin N => MeasurableSpace.comap (T^[(a : ℕ)])
        (partSigma P)) (⟨0, hN⟩ : Fin N)
      rwa [Function.iterate_zero, MeasurableSpace.comap_id] at hlt
    · refine le_trans ?_ hW
      have hlt := le_iSup (fun a : Fin l => MeasurableSpace.comap
          (Tinv^[(a : ℕ) + 1]) (partSigma P))
        (⟨(i : ℕ) + 1 - (j : ℕ) - 1, by have := i.isLt; omega⟩ : Fin l)
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ (i : ℕ) + 1 - (j : ℕ))] at hlt

/-- Entropy of the `N`-fold join of the window is bounded by the entropy of the `N`-fold join of
`P` plus the (bounded) entropy of the window itself. -/
theorem Hfam_joinSets_winPart_le (μ : Measure X) [IsProbabilityMeasure μ] {T Tinv : X → X}
    (hinv : Function.LeftInverse Tinv T) (hmp : MeasurePreserving T μ μ)
    (hTinv : Measurable Tinv) (P : FinPart X) {N : ℕ} (hN : 1 ≤ N) (l : ℕ) :
    Hfam μ (joinSets T (winPart Tinv hTinv P l) N)
      ≤ Hfam μ (joinSets T P N) + Hfam μ (joinSets Tinv (comapPart Tinv hTinv P) l) := by
  have hT : Measurable T := hmp.measurable
  have hfam : Work.EKLComp.Core.IsMPart
      (fun p : (Fin N → Fin P.n) × (Fin l → Fin P.n) =>
        joinSets T P N p.1 ∩ joinSets Tinv (comapPart Tinv hTinv P) l p.2) :=
    isMPart_inter_prod (Work.EKLComp.Core.joinSets_isMPart hT P N)
      (Work.EKLComp.Core.joinSets_isMPart hTinv (comapPart Tinv hTinv P) l)
  have hle := Hfam_le_of_partSigma_le μ (joinSets T (winPart Tinv hTinv P l) N)
    (Work.EKLComp.Core.joinSets_isMPart hT (winPart Tinv hTinv P l) N)
    (finPartOfFamily _ hfam)
    (by rw [partSigma_finPartOfFamily]; exact partSigmaFam_winPart_le hinv hT hTinv P hN l)
  rw [Hfam_finPartOfFamily] at hle
  refine le_trans hle ?_
  exact Work.EKLComp.Core.Hfam_inter_le μ (Work.EKLComp.Core.joinSets_isMPart hT P N)
    (Work.EKLComp.Core.joinSets_isMPart hTinv (comapPart Tinv hTinv P) l)

/-- **The window has the same entropy rate as `P`.** -/
theorem hPart_winPart_le (μ : Measure X) [IsProbabilityMeasure μ] {T Tinv : X → X}
    (hinv : Function.LeftInverse Tinv T) (hmp : MeasurePreserving T μ μ)
    (hTinv : Measurable Tinv) (P : FinPart X) (l : ℕ) :
    @hPart X mX μ T (winPart Tinv hTinv P l) ≤ @hPart X mX μ T P := by
  set C : ℝ := Hfam μ (joinSets Tinv (comapPart Tinv hTinv P) l) with hCdef
  have hC0 : 0 ≤ C := Work.EKLComp.Core.Hfam_nonneg μ _
  have havg : ∀ N : ℕ, Hfam μ (joinSets T (winPart Tinv hTinv P l) (N+1)) / ((N : ℝ) + 1)
      ≤ (Hfam μ (joinSets T P (N+1)) + C) / ((N : ℝ) + 1) := by
    intro N
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact Hfam_joinSets_winPart_le μ hinv hmp hTinv P (by omega) l
  have hbdd : BddBelow (Set.range fun N : ℕ =>
      (Hfam μ (joinSets T P (N+1)) + C) / ((N : ℝ) + 1)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨N, rfl⟩
    refine div_nonneg ?_ (by positivity)
    have := Work.EKLComp.Core.Hfam_nonneg μ (joinSets T P (N+1))
    linarith
  have h1 : @hPart X mX μ T (winPart Tinv hTinv P l)
      ≤ ⨅ N : ℕ, (Hfam μ (joinSets T P (N+1)) + C) / ((N : ℝ) + 1) := by
    refine le_ciInf fun N => ?_
    calc @hPart X mX μ T (winPart Tinv hTinv P l)
        ≤ Hfam μ (joinSets T (winPart Tinv hTinv P l) (N+1)) / ((N : ℝ) + 1) :=
          Work.EKLComp.Core.hPart_le_avg μ T _ N
      _ ≤ _ := havg N
  have h2 : (⨅ N : ℕ, (Hfam μ (joinSets T P (N+1)) + C) / ((N : ℝ) + 1))
      ≤ @hPart X mX μ T P := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hlim1 : Filter.Tendsto
        (fun N : ℕ => Hfam μ (joinSets T P (N+1)) / ((N : ℝ) + 1))
        Filter.atTop (nhds (@hPart X mX μ T P)) := by
      have h := (tendsto_hPart μ hmp P).comp (Filter.tendsto_add_atTop_nat 1)
      refine h.congr' ?_
      filter_upwards with N
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    have hden : Filter.Tendsto (fun N : ℕ => (N : ℝ) + 1) Filter.atTop Filter.atTop :=
      tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop
    have hlim2 : Filter.Tendsto (fun N : ℕ => C / ((N : ℝ) + 1)) Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds hden
    have hlim3 : Filter.Tendsto
        (fun N : ℕ => Hfam μ (joinSets T P (N+1)) / ((N : ℝ) + 1) + C / ((N : ℝ) + 1))
        Filter.atTop (nhds (@hPart X mX μ T P + 0)) := hlim1.add hlim2
    have hev : ∀ᶠ N : ℕ in Filter.atTop,
        Hfam μ (joinSets T P (N+1)) / ((N : ℝ) + 1) + C / ((N : ℝ) + 1)
          < @hPart X mX μ T P + ε := by
      have hlt : @hPart X mX μ T P + 0 < @hPart X mX μ T P + ε := by linarith
      exact hlim3.eventually (isOpen_Iio.mem_nhds hlt)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    refine le_trans (ciInf_le hbdd N) ?_
    rw [add_div]
    exact le_of_lt (hN N le_rfl)
  linarith [h1, h2]

end Work.EKLC6Core.BiGenAux
