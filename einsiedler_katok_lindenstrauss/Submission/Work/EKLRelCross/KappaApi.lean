import Mathlib
import Submission.Work.EKLRelCross.LeafExistDefs
import Submission.Work.EKLComp.joinAtoms

/-!
# Atoms of a wrapped sigma-algebra, and a countable pi-system for the ambient space

Auxiliary API for the proportionality theorem Work.EKLRelCross.kappa_propor.

* atomOf A x is the atom of A.m at x; we record the elementary facts that it is contained in every
  A.m-measurable set containing x, that points of an atom determine the atom, that atoms of
  countably generated sigma-algebras are measurable, that atoms of a finer sigma-algebra are
  smaller, and that the atom of a join is the intersection of the atoms (atomOf_join, the
  wrapped-sigma-algebra form of Work.EKLComp.joinAtoms).
* Measurable functions are constant on atoms (eq_of_mem_atom_ennreal etc.).
* The atom relation {(x, y) | y in atomOf A x} is measurable in the product space
  (measurableSet_atomRel); this is what makes the map x :-> kappa mu A x (atomOf A2 x) measurable.
* exists_countable_piSystem: for a standard Borel space there is a countable pi-system generating
  the ambient sigma-algebra (finite intersections of a generating sequence).
-/

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.EKLRelCross

variable {α : Type*} [mα : MeasurableSpace α]

/-! ## Elementary atom facts -/

/-- The atom of x is contained in every A.m-measurable set containing x. -/
theorem atomOf_subset_of_measurable (A : MSAlgG α) {s : Set α} (hs : MeasurableSet[A.m] s)
    {x : α} (hx : x ∈ s) : atomOf A x ⊆ s :=
  Set.sInter_subset_of_mem ⟨hs, hx⟩

/-- If y lies in the atom of x, then every A.m-measurable set containing y contains x. -/
theorem mem_of_mem_atomOf (A : MSAlgG α) {s : Set α} (hs : MeasurableSet[A.m] s) {x y : α}
    (hy : y ∈ atomOf A x) (hys : y ∈ s) : x ∈ s := by
  by_contra hxs
  exact (atomOf_subset_of_measurable A hs.compl hxs hy) hys

/-- x belongs to its own atom. -/
theorem mem_atomOf (A : MSAlgG α) (x : α) : x ∈ atomOf A x :=
  Set.mem_sInter.mpr fun _ hs => hs.2

/-- Membership in the atom is belonging to the same A.m-measurable sets. -/
theorem mem_atomOf_iff (A : MSAlgG α) (x y : α) :
    y ∈ atomOf A x ↔ ∀ s, MeasurableSet[A.m] s → (y ∈ s ↔ x ∈ s) :=
  Work.EKLComp.atomG_eq_iff A.m x y

/-- If y is in atomOf A x then y and x have the same atom. -/
theorem atomOf_eq_of_mem (A : MSAlgG α) {x y : α} (hy : y ∈ atomOf A x) :
    atomOf A y = atomOf A x := by
  have hy2 : x ∈ atomOf A y :=
    (mem_atomOf_iff A y x).mpr fun s hs => ((mem_atomOf_iff A x y).mp hy s hs).symm
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    exact (mem_atomOf_iff A x z).mpr fun s hs =>
      ((mem_atomOf_iff A y z).mp hz s hs).trans ((mem_atomOf_iff A x y).mp hy s hs)
  · intro z hz
    exact (mem_atomOf_iff A y z).mpr fun s hs =>
      ((mem_atomOf_iff A x z).mp hz s hs).trans ((mem_atomOf_iff A y x).mp hy2 s hs)

/-- Atoms of a countably generated sigma-algebra are measurable. -/
theorem measurableSet_atomOf (A : MSAlgG α)
    (hgen : ∃ b : Set (Set α), b.Countable ∧ A.m = MeasurableSpace.generateFrom b) (x : α) :
    MeasurableSet[A.m] (atomOf A x) := by
  letI := A.m
  haveI : MeasurableSpace.CountablyGenerated α :=
    ⟨hgen.choose, hgen.choose_spec.1, hgen.choose_spec.2⟩
  have hbridge : atomOf (MSAlgG.mk (inferInstance : MeasurableSpace α)) x
      = @measurableAtom α (inferInstance : MeasurableSpace α) x := by
    ext z
    simp only [atomOf, measurableAtom, Set.mem_iInter, Set.mem_sInter, Set.mem_ofPred_eq]
    tauto
  exact hbridge ▸ MeasurableSpace.measurableSet_measurableAtom x

/-- Atoms of a finer sigma-algebra are smaller (the coarser sigma-algebra is countably
generated, so that its atoms are measurable). -/
theorem atomOf_mono {A A2 : MSAlgG α} (h : A.m ≤ A2.m)
    (hgen : ∃ b : Set (Set α), b.Countable ∧ A.m = MeasurableSpace.generateFrom b) (x : α) :
    atomOf A2 x ⊆ atomOf A x :=
  atomOf_subset_of_measurable A2 ((h _) (measurableSet_atomOf A hgen x)) (mem_atomOf A x)

/-- An ENNReal-valued A.m-measurable function is constant on atoms. -/
theorem eq_of_mem_atom_ennreal (A : MSAlgG α) {f : α → ℝ≥0∞} (hf : Measurable[A.m] f) {x y : α}
    (hy : y ∈ atomOf A x) : f y = f x := by
  refine le_antisymm ?_ ?_
  · by_contra hcon
    rw [not_le] at hcon
    exact absurd (mem_of_mem_atomOf A (hf measurableSet_Ioi) hy hcon) (lt_irrefl (f x))
  · by_contra hcon
    rw [not_le] at hcon
    exact absurd (mem_of_mem_atomOf A (hf measurableSet_Iio) hy hcon) (lt_irrefl (f x))

/-- A real-valued A.m-measurable function is constant on atoms. -/
theorem eq_of_mem_atom_real (A : MSAlgG α) {f : α → ℝ} (hf : Measurable[A.m] f) {x y : α}
    (hy : y ∈ atomOf A x) : f y = f x := by
  refine le_antisymm ?_ ?_
  · by_contra hcon
    rw [not_le] at hcon
    exact absurd (mem_of_mem_atomOf A (hf measurableSet_Ioi) hy hcon) (lt_irrefl (f x))
  · by_contra hcon
    rw [not_le] at hcon
    exact absurd (mem_of_mem_atomOf A (hf measurableSet_Iio) hy hcon) (lt_irrefl (f x))

/-! ## The atom of a join -/

/-- The atom of the join A v A2 is the intersection of the atoms (countably generated A, A2). -/
theorem atomOf_join (A A2 : MSAlgG α)
    (hA : ∃ b : Set (Set α), b.Countable ∧ A.m = MeasurableSpace.generateFrom b)
    (hA2 : ∃ b : Set (Set α), b.Countable ∧ A2.m = MeasurableSpace.generateFrom b) (x : α) :
    atomOf (MSAlgG.mk (A.m ⊔ A2.m)) x = atomOf A x ∩ atomOf A2 x := by
  obtain ⟨b, _, hb⟩ := hA
  obtain ⟨b2, _, hb2⟩ := hA2
  have key : A.m ⊔ A2.m = MeasurableSpace.generateFrom (b ∪ b2) := by
    rw [hb, hb2, MeasurableSpace.generateFrom_sup_generateFrom]
  have h1 : atomOf A x = Work.EKLComp.atomG (MeasurableSpace.generateFrom b) x := by
    rw [← hb]; rfl
  have h2 : atomOf A2 x = Work.EKLComp.atomG (MeasurableSpace.generateFrom b2) x := by
    rw [← hb2]; rfl
  have h0 : atomOf (MSAlgG.mk (A.m ⊔ A2.m)) x
      = Work.EKLComp.atomG (MeasurableSpace.generateFrom (b ∪ b2)) x := by
    rw [show atomOf (MSAlgG.mk (A.m ⊔ A2.m)) x = Work.EKLComp.atomG (A.m ⊔ A2.m) x from rfl, key]
  rw [h0, h1, h2, Work.EKLComp.atomG_generateFrom, Work.EKLComp.atomG_generateFrom,
    Work.EKLComp.atomG_generateFrom]
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union]
  constructor
  · intro H; exact ⟨fun s hs => H s (Or.inl hs), fun s hs => H s (Or.inr hs)⟩
  · rintro ⟨H1, H2⟩ s (hs | hs)
    · exact H1 s hs
    · exact H2 s hs

/-! ## Measurability of the atom relation -/

/-- The atom relation {(x, y) | y in atomOf A x} is measurable in the product of the ambient
space with itself, for a countably generated A.m which is below the ambient sigma-algebra. -/
theorem measurableSet_atomRel (A : MSAlgG α) (hA : A.m ≤ mα)
    (hgen : ∃ b : Set (Set α), b.Countable ∧ A.m = MeasurableSpace.generateFrom b) :
    MeasurableSet {p : α × α | p.2 ∈ atomOf A p.1} := by
  let hcg : @MeasurableSpace.CountablyGenerated α A.m :=
    MeasurableSpace.CountablyGenerated.mk (m := A.m) hgen
  let G : ℕ → Set α := fun n => @MeasurableSpace.natGeneratingSequence α A.m hcg n
  have hGgen : A.m = MeasurableSpace.generateFrom (Set.range G) :=
    (@MeasurableSpace.generateFrom_natGeneratingSequence α A.m hcg).symm
  have hGmeas : ∀ n, MeasurableSet[A.m] (G n) := fun n =>
    @MeasurableSpace.measurableSet_natGeneratingSequence α A.m hcg n
  have hmem : ∀ (p : α × α) (n : ℕ), (p.2 ∈ G n ↔ p.1 ∈ G n)
      ↔ (p ∈ ((G n ×ˢ G n) ∪ ((G n)ᶜ ×ˢ (G n)ᶜ) : Set (α × α))) := by
    intro p n
    simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff]
    constructor
    · intro h
      by_cases hc : p.1 ∈ G n
      · exact Or.inl ⟨hc, h.mpr hc⟩
      · exact Or.inr ⟨hc, fun h2 => hc (h.mp h2)⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨fun _ => h1, fun _ => h2⟩
      · exact ⟨fun h2'' => absurd h2'' h2, fun hc => absurd hc h1⟩
  have hrel : {p : α × α | p.2 ∈ atomOf A p.1}
      = ⋂ n, ((G n ×ˢ G n) ∪ ((G n)ᶜ ×ˢ (G n)ᶜ) : Set (α × α)) := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    have hiff : p.2 ∈ Work.EKLComp.atomG (MeasurableSpace.generateFrom (Set.range G)) p.1
        ↔ (∀ s ∈ Set.range G, p.2 ∈ s ↔ p.1 ∈ s) := by
      rw [Work.EKLComp.atomG_generateFrom]
      rfl
    constructor
    · intro h n
      have h2 : p.2 ∈ Work.EKLComp.atomG (MeasurableSpace.generateFrom (Set.range G)) p.1 := by
        rw [← hGgen]; exact h
      exact (hmem p n).mp (hiff.mp h2 (G n) (Set.mem_range_self n))
    · intro h
      have h2 : ∀ s ∈ Set.range G, p.2 ∈ s ↔ p.1 ∈ s := by
        rintro s ⟨n, rfl⟩
        exact (hmem p n).mpr (h n)
      have h3 := hiff.mpr h2
      rwa [← hGgen] at h3
  rw [hrel]
  exact MeasurableSet.iInter fun n => MeasurableSet.union
    ((hA _ (hGmeas n)).prod (hA _ (hGmeas n)))
    (((hA _ (hGmeas n)).compl).prod ((hA _ (hGmeas n)).compl))

/-! ## A countable pi-system generating the ambient sigma-algebra -/

/-- For a standard Borel space the ambient sigma-algebra is generated by a countable pi-system
containing univ: the finite intersections of the sets of a generating sequence. -/
theorem exists_countable_piSystem [StandardBorelSpace α] :
    ∃ C : Set (Set α), C.Countable ∧ IsPiSystem C ∧ (Set.univ : Set α) ∈ C ∧
      (∀ s ∈ C, MeasurableSet s) ∧ (inferInstance : MeasurableSpace α)
        = MeasurableSpace.generateFrom C := by
  haveI : MeasurableSpace.CountablyGenerated α := inferInstance
  let G : ℕ → Set α := MeasurableSpace.natGeneratingSequence α
  have hgen : MeasurableSpace.generateFrom (Set.range G) = (inferInstance : MeasurableSpace α) :=
    MeasurableSpace.generateFrom_natGeneratingSequence α
  refine ⟨Set.range (fun t : Finset ℕ => ⋂ n ∈ t, G n), countable_range _, ?_, ⟨∅, ?_⟩, ?_, ?_⟩
  · rintro s ⟨t1, rfl⟩ s2 ⟨t2, rfl⟩ -
    refine ⟨t1 ∪ t2, ?_⟩
    ext x
    simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_union]
    constructor
    · intro h; exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
    · rintro ⟨h1, h2⟩ i (hi | hi)
      · exact h1 i hi
      · exact h2 i hi
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

/-- Two finite measures agreeing on a pi-system generating the ambient sigma-algebra (and having
the same total mass) are equal. -/
theorem measure_ext_of_piSystem {mu nu : Measure α} [IsFiniteMeasure mu] (C : Set (Set α))
    (hC : (inferInstance : MeasurableSpace α) = MeasurableSpace.generateFrom C)
    (hpi : IsPiSystem C) (h : ∀ s ∈ C, mu s = nu s) (huniv : mu Set.univ = nu Set.univ) :
    mu = nu :=
  MeasureTheory.ext_of_generate_finite C hC hpi h huniv

/-! ## The conditional measure is a probability measure -/

/-- kappa mu A x is a probability measure. -/
theorem kappa_univ [StandardBorelSpace α] (μ : Measure α) [IsFiniteMeasure μ] (A : MSAlgG α)
    (x : α) : kappa μ A x Set.univ = 1 := by
  rw [kappa_def]
  exact (ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure x).measure_univ

/-! ## The fundamental property of the conditional measure -/

/-- The measure of a measurable set is the integral of its conditional probabilities
(Pisa 5.9(i)): mu B = the integral of x :-> kappa mu A x B with respect to mu. -/
theorem measure_apply_eq_lintegral_kappa [StandardBorelSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (A : MSAlgG α) (hA : A.m ≤ mα) {B : Set α} (hB : MeasurableSet B) :
    μ B = ∫⁻ x, kappa μ A x B ∂μ := by
  have hcomp := ProbabilityTheory.condExpKernel_comp_trim (μ := μ) (mΩ := mα) (m := A.m) hA
  calc μ B = (Measure.bind (μ.trim hA)
        (fun x => ProbabilityTheory.condExpKernel (mΩ := mα) μ A.m x)) B := by
        rw [hcomp]
    _ = ∫⁻ x, ProbabilityTheory.condExpKernel (mΩ := mα) μ A.m x B ∂(μ.trim hA) :=
        Measure.bind_apply hB
          (ProbabilityTheory.condExpKernel (mΩ := mα) μ A.m).measurable.aemeasurable
    _ = ∫⁻ x, ProbabilityTheory.condExpKernel (mΩ := mα) μ A.m x B ∂μ :=
        lintegral_trim hA (ProbabilityTheory.Kernel.measurable_coe
          (ProbabilityTheory.condExpKernel (mΩ := mα) μ A.m) hB)
    _ = ∫⁻ x, kappa μ A x B ∂μ := by simp only [kappa_def]

/-- A measurable `mu`-null set has conditional measure zero almost everywhere. -/
theorem kappa_apply_eq_zero_of_measure_eq_zero [StandardBorelSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (A : MSAlgG α) (hA : A.m ≤ mα)
    {B : Set α} (hB : MeasurableSet B) (hBμ : μ B = 0) :
    ∀ᵐ x ∂μ, kappa μ A x B = 0 := by
  have hbound : ∀ᵐ y ∂μ, ‖B.indicator (1 : α → ℝ) y‖ ≤ 1 :=
    Filter.Eventually.of_forall fun y => by
      by_cases hy : y ∈ B
      · rw [Set.indicator_of_mem hy]; simp
      · rw [Set.indicator_of_notMem hy]; simp
  have hgint : Integrable (B.indicator (1 : α → ℝ)) μ :=
    Integrable.of_bound (measurable_const.indicator hB).aestronglyMeasurable 1 hbound
  have h1 := ProbabilityTheory.condExp_ae_eq_integral_condExpKernel (μ := μ) (mΩ := mα)
    (m := A.m) hA hgint
  have h2 : μ[B.indicator (1 : α → ℝ) | A.m] =ᵐ[μ] fun _ => (0 : ℝ) := by
    have hgg : B.indicator (1 : α → ℝ) =ᵐ[μ] fun _ => (0 : ℝ) := by
      filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hBμ] with y hy
      rw [Set.indicator_of_notMem hy]
    have hc := MeasureTheory.condExp_congr_ae (μ := μ) (m := A.m) hgg
    have hconst : μ[(fun _ : α => (0 : ℝ)) | A.m] = fun _ : α => (0 : ℝ) :=
      MeasureTheory.condExp_const (μ := μ) (m := A.m) hA (0 : ℝ)
    filter_upwards [hc] with x hx
    simpa [hconst] using hx
  filter_upwards [h1, h2] with x hx1 hx2
  have hzero : ∫ y, B.indicator (1 : α → ℝ) y
      ∂(ProbabilityTheory.condExpKernel (mΩ := mα) μ A.m x) = 0 := by
    rw [← hx1, hx2]
  have hreal : ((ProbabilityTheory.condExpKernel (mΩ := mα) μ A.m x) B).toReal = 0 := by
    rw [← MeasureTheory.Measure.real_def, ← MeasureTheory.integral_indicator_one hB]
    simpa using hzero
  rcases (ENNReal.toReal_eq_zero_iff _).mp hreal with h | h
  · exact h
  · exact absurd h (MeasureTheory.measure_ne_top _ _)

end Work.EKLRelCross
