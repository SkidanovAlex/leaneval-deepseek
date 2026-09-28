import Mathlib
import Submission.Work.Thom.FiniteCover
import Submission.Work.Thom.localThom_union
import Submission.Work.Thom.Coh_zero_cover_injective
import Submission.Work.Thom.localThomMap_pdCohMap
import Submission.Work.Thom.Coh_zero_cover_injective_gen
import Submission.Work.Cohomology.good_empty
import Submission.Work.Cohomology.pd_middleDegree_of_good
import Submission.Work.Thom.localThom_eq_of_cover
import Submission.Work.Thom.localThom_eq_of_cover_rel
import Submission.Work.Thom.pdCohMap_comp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.Thom

open Work.TangentClasses CategoryTheory CategoryTheory.Limits

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## Set algebra for finite families of pieces -/

section SetAlgebra

variable {τ : Type}

/-- The intersection over the singleton subfamily `{a}`. -/
theorem biInter_finset_singleton (a : τ) (U : τ → Set B) :
    (⋂ i ∈ (↑({a} : Finset τ) : Set τ), U i) = U a := by
  rw [Finset.coe_singleton, Set.biInter_singleton]

/-- The intersection over a union of two subfamilies. -/
theorem biInter_finset_union [DecidableEq τ] (S T : Finset τ) (U : τ → Set B) :
    (⋂ i ∈ (↑(S ∪ T) : Set τ), U i)
      = (⋂ i ∈ (S : Set τ), U i) ∩ (⋂ i ∈ (T : Set τ), U i) := by
  rw [Finset.coe_union, Set.biInter_union]

/-- The intersection over a nonempty subfamily of the pieces `U i ∩ t`. -/
theorem biInter_finset_inter (S : Finset τ) (hS : S.Nonempty) (U : τ → Set B) (t : Set B) :
    (⋂ i ∈ (S : Set τ), (U i ∩ t)) = (⋂ i ∈ (S : Set τ), U i) ∩ t := by
  ext x
  simp only [Set.mem_iInter, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun i hi => (h i hi).1, (h hS.choose hS.choose_spec).2⟩
  · rintro ⟨h1, h2⟩ i hi
    exact ⟨h1 i hi, h2⟩

/-- The union over a subfamily of the pieces `U i ∩ t`. -/
theorem biUnion_finset_inter (S : Finset τ) (U : τ → Set B) (t : Set B) :
    (⋃ i ∈ (S : Set τ), (U i ∩ t)) = (⋃ i ∈ (S : Set τ), U i) ∩ t := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨⟨i, hi, h1⟩, h2⟩
  · rintro ⟨⟨i, hi, h1⟩, h2⟩
    exact ⟨i, hi, h1, h2⟩

/-- The union over an inserted subfamily. -/
theorem biUnion_finset_insert [DecidableEq τ] (a : τ) (T : Finset τ) (U : τ → Set B) :
    (⋃ i ∈ (↑(insert a T) : Set τ), U i) = U a ∪ (⋃ i ∈ (T : Set τ), U i) := by
  rw [Finset.coe_insert, Set.biUnion_insert]

/-- The union over an image of a family of subfamilies. -/
theorem biUnion_finset_image {α : Type} [DecidableEq α] [DecidableEq τ] (A : Finset α)
    (f : Finset τ → Set B) (g : α → Finset τ) :
    (⋃ S ∈ (A.image g : Finset (Finset τ)), f S) = ⋃ i ∈ (A : Set α), f (g i) := by
  ext x
  simp only [Set.mem_iUnion, Finset.mem_image]
  constructor
  · rintro ⟨S, ⟨T, hT, rfl⟩, hx⟩
    exact ⟨T, hT, hx⟩
  · rintro ⟨T, hT, hx⟩
    exact ⟨g T, ⟨T, hT, rfl⟩, hx⟩

/-- The union over the full finite family. -/
theorem biUnion_finset_univ [Fintype τ] (U : τ → Set B) :
    (⋃ i ∈ (↑(Finset.univ : Finset τ) : Set τ), U i) = ⋃ i, U i := by
  rw [Finset.coe_univ, Set.biUnion_univ]

/-- The restriction direction for finite intersections. -/
theorem biInter_finset_mono {S T : Finset τ} (U : τ → Set B) (h : S ⊆ T) :
    (⋂ i ∈ (T : Set τ), U i) ⊆ (⋂ i ∈ (S : Set τ), U i) :=
  Set.biInter_subset_biInter_left (s := (T : Set τ)) (s' := (S : Set τ)) (t := U)
    (Finset.coe_subset.mpr h)

/-- A nonempty intersection of pieces is contained in the union of a larger family. -/
theorem biInter_finset_subset_biUnion {S T : Finset τ} (U : τ → Set B) (hS : S.Nonempty)
    (h : S ⊆ T) : (⋂ i ∈ (S : Set τ), U i) ⊆ (⋃ i ∈ (T : Set τ), U i) :=
  (Set.biInter_subset_of_mem (s := (S : Set τ)) (t := U)
      (Finset.mem_coe.mpr hS.choose_spec)).trans
    (Set.subset_biUnion_of_mem (Finset.mem_coe.mpr (h hS.choose_spec)))

end SetAlgebra

/-! ## Transport of the piece-theoretic data along equalities of pieces -/

section Transport

/-- `Subsingleton` transfers along an equality of pieces. -/
theorem subsingleton_PieceCoh_of_eq (Z : RealBundle B F ι) {W W' : Set B} {m : ℕ} (h : W = W')
    (hs : Subsingleton (PieceCoh Z W m)) : Subsingleton (PieceCoh Z W' m) := by
  cases h; exact hs

/-- The local Thom isomorphism transfers along an equality of pieces. -/
theorem bijective_localThomMap_cast (Z : RealBundle B F ι) {W W' : Set B} {n : ℕ} (h : W = W')
    (τ : PieceCoh Z W n) (j : ℕ) (hb : Function.Bijective (localThomMap Z n W τ j)) :
    Function.Bijective (localThomMap Z n W' (h ▸ τ) j) := by
  cases h; exact hb

/-- The restriction to a piece can be transported along an equality of the *source* piece. -/
theorem pdCohMap_cast_source (Z : RealBundle B F ι) {U U' W : Set B} (hU : U = U')
    (hUW : W ⊆ U) (hUW' : W ⊆ U') {m : ℕ} (x : PieceCoh Z U m) :
    (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U') (Z.proj ⁻¹' W) (Set.preimage_mono hUW') m).hom (hU ▸ x)
      = (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (Set.preimage_mono hUW) m).hom x := by
  cases hU; rfl

/-- The restriction to a piece can be transported along an equality of the *target* piece. -/
theorem pdCohMap_cast_target (Z : RealBundle B F ι) {U W W' : Set B} (hW : W' = W)
    (hUW : W ⊆ U) (hUW' : W' ⊆ U) {m : ℕ} (x : PieceCoh Z U m) :
    hW ▸ ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' W') (Set.preimage_mono hUW') m).hom x)
      = (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' W) (Set.preimage_mono hUW) m).hom x := by
  cases hW; rfl

end Transport

/-! ## Vanishing on an empty piece -/

section Empty

/-- The absolute cohomology of an empty space vanishes. -/
theorem subsingleton_Coh_of_isEmpty {X : Type} [TopologicalSpace X] (h : IsEmpty X) (j : ℕ) :
    Subsingleton (Coh ℤ j X) := by
  haveI : IsEmpty (↥(TopCat.of X)) := h
  exact ModuleCat.subsingleton_of_isZero
    (Work.Cohomology.isZero_homology_of_isZero_X_cochain j
      (Work.Cohomology.isZero_singularCochainComplex_of_isEmpty (TopCat.of X) j))

/-- The piece cohomology of an empty piece vanishes. -/
theorem subsingleton_PieceCoh_of_isEmpty (Z : RealBundle B F ι) (m : ℕ) {W : Set B}
    (h : IsEmpty ↥W) : Subsingleton (PieceCoh Z W m) := by
  haveI hW : IsEmpty ↥(Z.proj ⁻¹' W) := ⟨fun p => h.false ⟨Z.proj p.1, p.2⟩⟩
  haveI : IsEmpty ↥({y : ↥(Z.proj ⁻¹' W) | (y : Z.TotalSpace) ∈ zeroComplement Z}) :=
    ⟨fun y => hW.false y.1⟩
  haveI : IsIso (Work.Cohomology.relIncl ℤ (TopCat.of (Z.proj ⁻¹' W))
      {y : ↥(Z.proj ⁻¹' W) | (y : Z.TotalSpace) ∈ zeroComplement Z}) :=
    Work.Cohomology.isIso_relIncl_of_isEmpty _ _
  have h0 : IsZero ((Work.Cohomology.singularCochainComplex ℤ
      (TopCat.of (Z.proj ⁻¹' W))).homology m) :=
    Work.Cohomology.isZero_homology_of_isZero_X_cochain m
      (Work.Cohomology.isZero_singularCochainComplex_of_isEmpty (TopCat.of (Z.proj ⁻¹' W)) m)
  exact ModuleCat.subsingleton_of_isZero
    (IsZero.of_iso h0 (asIso (HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℤ
      (TopCat.of (Z.proj ⁻¹' W))
      {y : ↥(Z.proj ⁻¹' W) | (y : Z.TotalSpace) ∈ zeroComplement Z}) m)))

end Empty


/-- Composition of `Eq`-casts. -/
theorem eq_trans_cast {α : Sort _} (P : α → Sort _) {a b c : α} (h₁ : a = b) (h₂ : b = c)
    (x : P a) : (h₁.trans h₂) ▸ x = h₂ ▸ (h₁ ▸ x) := by
  cases h₁; cases h₂; rfl

/-- A union of sets indexed by a finite family of subfamilies only depends on the sets. -/
theorem biUnion_congr_finset {α : Type} {A : Finset α} {f g : α → Set B}
    (h : ∀ S ∈ A, f S = g S) : (⋃ S ∈ A, f S) = ⋃ S ∈ A, g S := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨S, hS, hx⟩
    exact ⟨S, hS, (h S hS) ▸ hx⟩
  · rintro ⟨S, hS, hx⟩
    exact ⟨S, hS, (h S hS).symm ▸ hx⟩


/-- Element form of the functoriality of `pdCohMap`. -/
theorem pdCohMap_comp_apply (Z : RealBundle B F ι) {V U W : Set B} (hVU : V ⊆ U) (hUW : U ⊆ W)
    {m : ℕ} (x : PieceCoh Z W m) :
    (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (Set.preimage_mono hVU) m).hom
      ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' W) (Z.proj ⁻¹' U) (Set.preimage_mono hUW) m).hom x)
      = (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' W) (Z.proj ⁻¹' V) (Set.preimage_mono (hVU.trans hUW)) m).hom x := by
  rw [← ModuleCat.comp_apply, ← Work.Thom.pdCohMap_comp]

/-! ## The finite-cover Thom class theorem -/


section Main

variable {τ : Type} [DecidableEq τ]

/-- **The finite-cover Thom class theorem, indexed by a finite set of pieces.**  This is the
induction step of `Work.Thom.thomClass_of_finite_cover`: rather than inducing on the number of
pieces with the `Fin`-indexed intersections of the statement (which forces transports of the data
along `Fin.castSucc`), we fix an arbitrary index type `τ`, a finite set `T` of indices, and the
family `U : τ → Set B`, and induce on `T`.  The hypotheses (`c`, `hc`, `hcompat`, `hlow`) never
mention `T`, so they are literally shared by the sub-cover in the induction step and only the
conclusion mentions `T` (over `⋃ i ∈ T, U i`). -/
theorem thomClass_of_finset :
    ∀ (T : Finset τ) (Z : RealBundle B F ι) (n : ℕ) (hn : 1 ≤ n)
      (U : τ → Set B) (hU : ∀ i, IsOpen (U i))
      (c : ∀ S : Finset τ, S.Nonempty → PieceCoh Z (⋂ i ∈ (S : Set τ), U i) n)
      (hc : ∀ (S : Finset τ) (hS : S.Nonempty) (j : ℕ),
        Function.Bijective (localThomMap Z n (⋂ i ∈ (S : Set τ), U i) (c S hS) j))
      (hcompat : ∀ (S S' : Finset τ) (hS : S.Nonempty) (hS' : S'.Nonempty) (h : S ⊆ S'),
        (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
          (Z.proj ⁻¹' (⋂ i ∈ (S : Set τ), U i)) (Z.proj ⁻¹' (⋂ i ∈ (S' : Set τ), U i))
          (Set.preimage_mono (biInter_finset_mono U h)) n).hom (c S hS) = c S' hS')
      (hlow : ∀ A : Finset (Finset τ), (∀ S ∈ A, S.Nonempty) → A.Nonempty →
        Subsingleton (PieceCoh Z (⋃ S ∈ A, ⋂ i ∈ (S : Set τ), U i) (n - 1))),
      ∃ cT : PieceCoh Z (⋃ i ∈ (T : Set τ), U i) n,
        (∀ j, Function.Bijective (localThomMap Z n (⋃ i ∈ (T : Set τ), U i) cT j)) ∧
        (∀ (S : Finset τ) (hS : S.Nonempty) (hST : S ⊆ T),
          (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
            (Z.proj ⁻¹' (⋃ i ∈ (T : Set τ), U i)) (Z.proj ⁻¹' (⋂ i ∈ (S : Set τ), U i))
            (Set.preimage_mono (biInter_finset_subset_biUnion U hS hST)) n).hom cT
            = c S hS) := by
  intro T
  induction T using Finset.induction with
  | empty =>
      intro Z n hn U hU c hc hcompat hlow
      have hEmpty : (⋃ i ∈ (↑(∅ : Finset τ) : Set τ), U i) = (∅ : Set B) := by
        rw [Finset.coe_empty, Set.biUnion_empty]
      refine ⟨0, ?_, ?_⟩
      · intro j
        haveI hE : IsEmpty ↥(⋃ i ∈ (↑(∅ : Finset τ) : Set τ), U i) := by
          rw [hEmpty]; exact ⟨fun x => x.2⟩
        haveI : Subsingleton (Coh ℤ j ↥(⋃ i ∈ (↑(∅ : Finset τ) : Set τ), U i)) :=
          subsingleton_Coh_of_isEmpty hE j
        haveI : Subsingleton (PieceCoh Z (⋃ i ∈ (↑(∅ : Finset τ) : Set τ), U i) (j + n)) :=
          subsingleton_PieceCoh_of_eq Z hEmpty.symm
            (subsingleton_PieceCoh_of_isEmpty Z (j + n) (W := (∅ : Set B)) ⟨fun x => x.2⟩)
        exact ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
      · intro S hS hST
        exact absurd (hST hS.choose_spec) (Finset.notMem_empty _)
  | insert a T haT ih =>
      intro Z n hn U hU c hc hcompat hlow
      classical
      let W : Set B := ⋃ i ∈ (T : Set τ), U i
      let V : τ → Set B := fun i => U i ∩ U a
      obtain ⟨cW, hcW, hresW⟩ := ih Z n hn U hU c hc hcompat hlow
      have hunion : ∀ {S S' : Finset τ}, S ⊆ S' → S ∪ ({a} : Finset τ) ⊆ S' ∪ ({a} : Finset τ) :=
        fun h x hx => by
          rcases Finset.mem_union.mp hx with h1 | h2
          · exact Finset.mem_union_left _ (h h1)
          · exact Finset.mem_union_right _ h2
      have hWopen : IsOpen W := isOpen_biUnion (fun i _ => hU i)
      have hUaopen : IsOpen (U a) := hU a
      have hVopen : ∀ i, IsOpen (V i) := fun i => (hU i).inter (hU a)
      -- the data over the new piece `U a`
      have eqNew : (⋂ i ∈ (↑({a} : Finset τ) : Set τ), U i) = U a :=
        biInter_finset_singleton a U
      let cNew : PieceCoh Z (U a) n := eqNew ▸ c {a} (Finset.singleton_nonempty a)
      have hcNew : ∀ j, Function.Bijective (localThomMap Z n (U a) cNew j) := fun j =>
        bijective_localThomMap_cast Z eqNew (c {a} (Finset.singleton_nonempty a)) j
          (hc {a} (Finset.singleton_nonempty a) j)
      -- the data over the overlap family `V = U ∩ U a`
      have eqOv : ∀ (S : Finset τ) (hS : S.Nonempty),
          (⋂ i ∈ (↑(S ∪ {a}) : Set τ), U i) = (⋂ i ∈ (S : Set τ), V i) := by
        intro S hS
        rw [biInter_finset_union S {a} U, biInter_finset_singleton a U]
        exact (biInter_finset_inter S hS U (U a)).symm
      let c₂ : ∀ S : Finset τ, S.Nonempty → PieceCoh Z (⋂ i ∈ (S : Set τ), V i) n := fun S hS =>
        (eqOv S hS) ▸ c (S ∪ {a}) (Finset.Nonempty.mono Finset.subset_union_left hS)
      have hc₂ : ∀ (S : Finset τ) (hS : S.Nonempty) (j : ℕ),
          Function.Bijective (localThomMap Z n (⋂ i ∈ (S : Set τ), V i) (c₂ S hS) j) := fun S hS j =>
        bijective_localThomMap_cast Z (eqOv S hS)
          (c (S ∪ {a}) (Finset.Nonempty.mono Finset.subset_union_left hS)) j
          (hc (S ∪ {a}) (Finset.Nonempty.mono Finset.subset_union_left hS) j)
      have hcompat₂ : ∀ (S S' : Finset τ) (hS : S.Nonempty) (hS' : S'.Nonempty) (h : S ⊆ S'),
          (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
            (Z.proj ⁻¹' (⋂ i ∈ (S : Set τ), V i)) (Z.proj ⁻¹' (⋂ i ∈ (S' : Set τ), V i))
            (Set.preimage_mono (biInter_finset_mono V h)) n).hom (c₂ S hS) = c₂ S' hS' := by
        intro S S' hS hS' h
        rw [show c₂ S hS = (eqOv S hS) ▸ c (S ∪ {a})
              (Finset.Nonempty.mono Finset.subset_union_left hS) from rfl]
        rw [show c₂ S' hS' = (eqOv S' hS') ▸ c (S' ∪ {a})
              (Finset.Nonempty.mono Finset.subset_union_left hS') from rfl]
        rw [pdCohMap_cast_source Z (eqOv S hS)
          ((biInter_finset_mono V h).trans (le_of_eq (eqOv S hS).symm))
          (biInter_finset_mono V h)]
        rw [← pdCohMap_cast_target Z (eqOv S' hS')
          ((biInter_finset_mono V h).trans (le_of_eq (eqOv S hS).symm))
          (biInter_finset_mono U (hunion h))]
        exact congrArg (fun t => (eqOv S' hS') ▸ t) (hcompat (S ∪ {a}) (S' ∪ {a})
          (Finset.Nonempty.mono Finset.subset_union_left hS)
          (Finset.Nonempty.mono Finset.subset_union_left hS')
          (hunion h))
      have hlow₂ : ∀ (A : Finset (Finset τ)), (∀ S ∈ A, S.Nonempty) → A.Nonempty →
          Subsingleton (PieceCoh Z (⋃ S ∈ A, ⋂ i ∈ (S : Set τ), V i) (n - 1)) := by
        intro A hA hAne
        have hne : ∀ S ∈ A.image (fun S => S ∪ ({a} : Finset τ)), S.Nonempty := by
          intro S hS
          obtain ⟨S₀, hS₀, rfl⟩ := Finset.mem_image.mp hS
          exact Finset.Nonempty.mono Finset.subset_union_left (hA S₀ hS₀)
        have hAne' : (A.image (fun S => S ∪ ({a} : Finset τ))).Nonempty :=
          hAne.image (fun S => S ∪ ({a} : Finset τ))
        refine subsingleton_PieceCoh_of_eq Z ?_
          (hlow (A.image (fun S => S ∪ ({a} : Finset τ))) hne hAne')
        rw [biUnion_finset_image]
        exact biUnion_congr_finset (fun S hS => eqOv S (hA S hS))
      obtain ⟨cI, hcI, hresI⟩ := ih Z n hn V hVopen c₂ hc₂ hcompat₂ hlow₂
      have E_I : (⋃ i ∈ (T : Set τ), V i) = W ∩ U a := biUnion_finset_inter T U (U a)
      let cI' : PieceCoh Z (W ∩ U a) n := E_I ▸ cI
      have hcI' : ∀ j, Function.Bijective (localThomMap Z n (W ∩ U a) cI' j) := fun j =>
        bijective_localThomMap_cast Z E_I cI j (hcI j)
      have hVsub : ∀ k ∈ T, V k ⊆ W ∩ U a := fun k hk x hx =>
        ⟨Set.subset_biUnion_of_mem (Finset.mem_coe.mpr hk) hx.1, hx.2⟩
      have hcov1 : W ∩ U a ⊆ ⋃ k ∈ (T : Set τ), V k := by
        intro x hx
        obtain ⟨hxW, hxU⟩ := hx
        obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxW
        obtain ⟨hk, hxk⟩ := Set.mem_iUnion.mp hxk
        exact Set.mem_biUnion (Finset.mem_coe.mpr hk) ⟨hxk, hxU⟩
      have hlow' : Subsingleton (PieceCoh Z (W ∩ U a) (n - 1)) := by
        by_cases hT : T = ∅
        · subst hT
          have hW0 : W = (∅ : Set B) := by
            rw [show W = (⋃ i ∈ (↑(∅ : Finset τ) : Set τ), U i) from rfl, Finset.coe_empty,
              Set.biUnion_empty]
          exact subsingleton_PieceCoh_of_eq Z (by rw [hW0, Set.empty_inter])
            (subsingleton_PieceCoh_of_isEmpty Z (n - 1) (W := (∅ : Set B)) ⟨fun x => x.2⟩)
        · have hne : ∀ S ∈ T.image (fun i => ({i} ∪ {a} : Finset τ)), S.Nonempty := by
            intro S hS
            obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hS
            exact Finset.Nonempty.mono Finset.subset_union_right (Finset.singleton_nonempty a)
          have hAne : (T.image (fun i => ({i} ∪ {a} : Finset τ))).Nonempty :=
            Finset.image_nonempty.mpr (Finset.nonempty_iff_ne_empty.mpr hT)
          have hcalc : (⋃ S ∈ T.image (fun i => ({i} ∪ {a} : Finset τ)), ⋂ i ∈ (S : Set τ), U i)
              = (⋃ i ∈ (T : Set τ), (U i ∩ U a)) :=
            (biUnion_finset_image T (fun S => ⋂ j ∈ (S : Set τ), U j)
              (fun i => {i} ∪ {a})).trans
              (biUnion_congr_finset (fun i _ =>
                biInter_finset_union {i} {a} U ▸ biInter_finset_singleton i U ▸
                  biInter_finset_singleton a U ▸ rfl))
          exact subsingleton_PieceCoh_of_eq Z (hcalc.trans (biUnion_finset_inter T U (U a)))
            (hlow _ hne hAne)
      have hpiece : ∀ (k : τ) (hk : k ∈ T),
          (⋂ i ∈ (↑({k} ∪ {a} : Finset τ) : Set τ), U i) = V k := fun k hk =>
        (eqOv {k} (Finset.singleton_nonempty k)).trans (biInter_finset_singleton k V)
      have hsubU : ∀ (k : τ) (hk : k ∈ T), V k ⊆ (⋂ i ∈ (↑({k} : Finset τ) : Set τ), U i) :=
        fun k hk x hx => by rw [biInter_finset_singleton k U]; exact hx.1
      have hsubUa : ∀ (k : τ) (hk : k ∈ T), V k ⊆ (⋂ i ∈ (↑({a} : Finset τ) : Set τ), U i) :=
        fun k hk x hx => by rw [biInter_finset_singleton a U]; exact hx.2
      have hsubVk : ∀ (k : τ) (hk : k ∈ T), V k ⊆ W := fun k hk x hx =>
        Set.subset_biUnion_of_mem (s := (T : Set τ)) (u := U) (Finset.mem_coe.mpr hk) hx.1
      have hsubW : ∀ (k : τ) (hk : k ∈ T),
          (⋂ i ∈ (↑({k} : Finset τ) : Set τ), U i) ⊆ W := fun k hk x hx => by
        rw [biInter_finset_singleton k U] at hx
        exact Set.subset_biUnion_of_mem (s := (T : Set τ)) (u := U) (Finset.mem_coe.mpr hk) hx
      have hsubOvl : ∀ (k : τ) (hk : k ∈ T),
          (⋂ i ∈ (↑({k} ∪ {a} : Finset τ) : Set τ), U i) ⊆ V k := fun k hk => le_of_eq (hpiece k hk)
      -- the restriction of `cI'` to a cover piece
      have hrestI : ∀ (k : τ) (hk : k ∈ T),
          (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
            (Z.proj ⁻¹' (W ∩ U a)) (Z.proj ⁻¹' (V k)) (Set.preimage_mono (hVsub k hk)) n).hom cI'
          = (hpiece k hk) ▸ c ({k} ∪ {a})
              (Finset.Nonempty.mono Finset.subset_union_left (Finset.singleton_nonempty k)) := by
        intro k hk
        rw [show cI' = E_I ▸ cI from rfl]
        rw [pdCohMap_cast_source Z E_I
          (Set.subset_biUnion_of_mem (s := (T : Set τ)) (u := V) (Finset.mem_coe.mpr hk))
          (hVsub k hk) cI]
        rw [← pdCohMap_cast_target Z (biInter_finset_singleton k V)
          (Set.subset_biUnion_of_mem (s := (T : Set τ)) (u := V) (Finset.mem_coe.mpr hk))
          ((Set.biInter_subset_of_mem (s := (↑({k} : Finset τ) : Set τ)) (t := V)
            (Finset.mem_coe.mpr (Finset.mem_singleton_self k))).trans
            (Set.subset_biUnion_of_mem (s := (T : Set τ)) (u := V) (Finset.mem_coe.mpr hk)))
          cI]
        rw [hresI {k} (Finset.singleton_nonempty k) (Finset.singleton_subset_iff.mpr hk)]
        rw [show c₂ {k} (Finset.singleton_nonempty k) =
            (eqOv {k} (Finset.singleton_nonempty k)) ▸ c ({k} ∪ {a})
              (Finset.Nonempty.mono Finset.subset_union_left (Finset.singleton_nonempty k)) from rfl]
        exact (eq_trans_cast (fun W => PieceCoh Z W n) (eqOv {k} (Finset.singleton_nonempty k))
          (biInter_finset_singleton k V)
          (c ({k} ∪ {a}) (Finset.Nonempty.mono Finset.subset_union_left
            (Finset.singleton_nonempty k)))).symm
      have h1 : (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
          (Z.proj ⁻¹' W) (Z.proj ⁻¹' (W ∩ U a)) (Set.preimage_mono Set.inter_subset_left) n).hom cW
          = cI' :=
        localThom_eq_of_cover_rel Z n V hVopen T hVsub hcov1 cI'
          ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
            (Z.proj ⁻¹' W) (Z.proj ⁻¹' (W ∩ U a)) (Set.preimage_mono Set.inter_subset_left) n).hom cW)
          (hcI' 0)
          (fun k hk => by
            rw [hrestI k hk]
            exact (bijective_localThomMap_cast Z (hpiece k hk) (c ({k} ∪ {a})
              (Finset.Nonempty.mono Finset.subset_union_left (Finset.singleton_nonempty k))) 0
              (hc ({k} ∪ {a}) (Finset.Nonempty.mono Finset.subset_union_left
                (Finset.singleton_nonempty k)) 0)).1)
          (fun k hk => by
            rw [hrestI k hk]
            rw [pdCohMap_comp_apply Z (hVU := hVsub k hk) (hUW := Set.inter_subset_left) cW]
            rw [← pdCohMap_comp_apply Z (hVU := hsubU k hk) (hUW := hsubW k hk) cW]
            rw [hresW {k} (Finset.singleton_nonempty k) (Finset.singleton_subset_iff.mpr hk)]
            rw [← pdCohMap_cast_target Z (hpiece k hk) (hsubU k hk)
              (biInter_finset_mono U (Finset.subset_union_left : ({k} : Finset τ) ⊆ {k} ∪ {a}))]
            rw [hcompat {k} ({k} ∪ {a}) (Finset.singleton_nonempty k)
              (Finset.Nonempty.mono Finset.subset_union_left (Finset.singleton_nonempty k))
              Finset.subset_union_left])
      have h2 : (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
          (Z.proj ⁻¹' (U a)) (Z.proj ⁻¹' (W ∩ U a)) (Set.preimage_mono Set.inter_subset_right) n).hom
          cNew = cI' :=
        localThom_eq_of_cover_rel Z n V hVopen T hVsub hcov1 cI'
          ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (zeroComplement Z)
            (Z.proj ⁻¹' (U a)) (Z.proj ⁻¹' (W ∩ U a)) (Set.preimage_mono Set.inter_subset_right) n).hom
            cNew)
          (hcI' 0)
          (fun k hk => by
            rw [hrestI k hk]
            exact (bijective_localThomMap_cast Z (hpiece k hk) (c ({k} ∪ {a})
              (Finset.Nonempty.mono Finset.subset_union_left (Finset.singleton_nonempty k))) 0
              (hc ({k} ∪ {a}) (Finset.Nonempty.mono Finset.subset_union_left
                (Finset.singleton_nonempty k)) 0)).1)
          (fun k hk => by
            rw [hrestI k hk]
            rw [pdCohMap_comp_apply Z (hVU := hVsub k hk) (hUW := Set.inter_subset_right) cNew]
            rw [show cNew = eqNew ▸ c {a} (Finset.singleton_nonempty a) from rfl]
            rw [pdCohMap_cast_source Z eqNew (hsubUa k hk) (fun x hx => hx.2)
              (c {a} (Finset.singleton_nonempty a))]
            rw [← pdCohMap_cast_target Z (hpiece k hk) (hsubUa k hk)
              (biInter_finset_mono U (Finset.subset_union_right : ({a} : Finset τ) ⊆ {k} ∪ {a}))]
            rw [hcompat {a} ({k} ∪ {a}) (Finset.singleton_nonempty a)
              (Finset.Nonempty.mono Finset.subset_union_left (Finset.singleton_nonempty k))
              Finset.subset_union_right])
      obtain ⟨cU, hcU, hU1, hU2⟩ :=
        localThom_union Z n hn hWopen hUaopen cW hcW cNew hcNew cI' hcI' h1 h2 hlow'
      have E₂ : W ∪ U a = ⋃ i ∈ (↑(insert a T) : Set τ), U i := by
        rw [biUnion_finset_insert]
        exact Set.union_comm _ _
      refine ⟨E₂ ▸ cU, fun j => bijective_localThomMap_cast Z E₂ cU j (hcU j), ?_⟩
      intro S hS hST
      have hSU : (⋂ i ∈ (S : Set τ), U i) ⊆ W ∪ U a :=
        (biInter_finset_subset_biUnion U hS hST).trans (le_of_eq E₂.symm)
      rw [pdCohMap_cast_source Z E₂ hSU (biInter_finset_subset_biUnion U hS hST)]
      by_cases ha : a ∈ S
      · rw [← pdCohMap_comp_apply Z
            (show (⋂ i ∈ (S : Set τ), U i) ⊆ U a from
              fun x hx => Set.biInter_subset_of_mem (Finset.mem_coe.mpr ha) hx)
            (show U a ⊆ W ∪ U a from Set.subset_union_right) cU]
        rw [hU2]
        rw [pdCohMap_cast_source Z eqNew
          (show (⋂ i ∈ (S : Set τ), U i) ⊆ (⋂ i ∈ (↑({a} : Finset τ) : Set τ), U i) from
            Set.biInter_subset_biInter_left (s := (S : Set τ)) (s' := (↑({a} : Finset τ) : Set τ))
              (t := U) (Finset.coe_subset.mpr (Finset.singleton_subset_iff.mpr ha)))
          (show (⋂ i ∈ (S : Set τ), U i) ⊆ U a from
            fun x hx => Set.biInter_subset_of_mem (Finset.mem_coe.mpr ha) hx)]
        exact hcompat {a} S (Finset.singleton_nonempty a) hS (Finset.singleton_subset_iff.mpr ha)
      · have hST' : S ⊆ T := by
          intro i hi
          rcases Finset.mem_insert.mp (hST hi) with h | h
          · exact absurd (h ▸ hi) ha
          · exact h
        rw [← pdCohMap_comp_apply Z
            (show (⋂ i ∈ (S : Set τ), U i) ⊆ W from
              (biInter_finset_subset_biUnion U hS hST').trans
                (le_of_eq (show (⋃ i ∈ (T : Set τ), U i) = W from rfl)))
            (show W ⊆ W ∪ U a from Set.subset_union_left) cU]
        rw [hU1]
        exact hresW S hS hST'

end Main

/-! ## The finite-cover Thom class theorem -/

/-- **The finite-cover Thom class theorem.**  For a real bundle `Z → B` of rank `n ≥ 1`, an open
family `U : Fin N → Set B` of pieces, and local Thom data over every nonempty intersection
`finInter U S` of subfamilies, compatible under the restriction maps and with the low-degree
vanishing of `PieceCoh Z (⋃ S ∈ A, finInter U S) (n-1)` for every nonempty family `A` of nonempty
subfamilies, there is local Thom data over the union `⋃ k, U k` restricting to the given data on
every intersection.

Proof route: induction on `N`.  In the step, apply the induction hypothesis to the sub-cover
`U ∘ Fin.castSucc` (data over `W := ⋃ k : Fin N, U (Fin.castSucc k)` with prescribed restrictions)
and to the sub-cover `fun k : Fin N => U (Fin.castSucc k) ∩ U (Fin.last N)` of `W ∩ U (Fin.last N)`
(whose nonempty intersections are again `finInter U S`), then glue with
`Work.Thom.localThom_union`.  The compatibility of the two overlap data is proved with
`Work.Thom.Coh_zero_cover_injective`: two local Thom classes over `W ∩ U (Fin.last N)` agreeing on
each piece `U (Fin.castSucc k) ∩ U (Fin.last N)` are equal, using the local Thom isomorphism of one
of them in degree `0` (giving a class of `Coh ℤ 0`), the local Thom property of the restrictions to
the pieces, and the unitality of the cup product. -/
theorem thomClass_of_finite_cover
    {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ) (hn : 1 ≤ n)
    (N : ℕ) (U : Fin N → Set B) (hU : ∀ k, IsOpen (U k))
    (c : ∀ S : Finset (Fin N), S.Nonempty → Work.Thom.PieceCoh Z (Work.Thom.finInter U S) n)
    (hc : ∀ (S : Finset (Fin N)) (hS : S.Nonempty) (j : ℕ),
      Function.Bijective (Work.Thom.localThomMap Z n (Work.Thom.finInter U S) (c S hS) j))
    (hcompat : ∀ (S T : Finset (Fin N)) (hS : S.Nonempty) (hT : T.Nonempty) (hST : S ⊆ T),
      (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (Work.Thom.finInter U S)) (Z.proj ⁻¹' (Work.Thom.finInter U T))
        (Set.preimage_mono (Work.Thom.finInter_mono hST)) n).hom (c S hS) = c T hT)
    (hlowU : ∀ A : Finset (Finset (Fin N)), (∀ S ∈ A, S.Nonempty) → A.Nonempty →
      Subsingleton (Work.Thom.PieceCoh Z (⋃ S ∈ A, Work.Thom.finInter U S) (n - 1))) :
    ∃ cU : Work.Thom.PieceCoh Z (⋃ k, U k) n,
      (∀ j : ℕ, Function.Bijective (Work.Thom.localThomMap Z n (⋃ k, U k) cU j)) ∧
      (∀ (S : Finset (Fin N)) (hS : S.Nonempty),
        (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' (⋃ k, U k)) (Z.proj ⁻¹' (Work.Thom.finInter U S))
          (Set.preimage_mono (Work.Thom.finInter_nonempty_subset_iUnion hS)) n).hom cU
          = c S hS) := by
  obtain ⟨cT, hcT, hresT⟩ :=
    thomClass_of_finset (Finset.univ : Finset (Fin N)) Z n hn U hU c hc hcompat hlowU
  have hE : (⋃ i ∈ (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)), U i) = (⋃ k, U k) :=
    biUnion_finset_univ U
  refine ⟨hE ▸ cT, fun j => bijective_localThomMap_cast Z hE cT j (hcT j), ?_⟩
  intro S hS
  have hgoal : (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
      (Z.proj ⁻¹' (⋃ k, U k)) (Z.proj ⁻¹' (⋂ i ∈ (S : Set (Fin N)), U i))
      (Set.preimage_mono (show (⋂ i ∈ (S : Set (Fin N)), U i) ⊆ ⋃ k, U k from
        Work.Thom.finInter_nonempty_subset_iUnion hS)) n).hom
      (hE ▸ cT) = c S hS := by
    rw [pdCohMap_cast_source Z hE (biInter_finset_subset_biUnion U hS (Finset.subset_univ S))
      (Work.Thom.finInter_nonempty_subset_iUnion hS) cT]
    exact hresT S hS (Finset.subset_univ S)
  exact hgoal

end Work.Thom
