import Mathlib
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.ThomBordism.moduleFiniteHomologyBiprod

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Finitely generated singular homology for spaces with a finite good cover

A *good cover* of a topological space `Z` is a family `U : ι → Set Z` of open sets covering `Z`
such that every nonempty finite intersection of the `U i` is contractible.  The main theorem of this
file (`finiteGoodCoverHomology`) is that for a **finite** good cover the singular homology
`H_k(Z; ℤ)` is a finitely generated `ℤ`-module in every degree `k`.

## Strategy

The argument is an induction on the number of sets, following the classical proof.

The key geometric input is the Mayer–Vietoris long exact sequence
(`Work.Cohomology.MVSequence`): for an open cover `Z = U ∪ V` the sequence

`H_{k}(U ∩ V) ⟶ H_k(U) ⊞ H_k(V) ⟶ H_k(Z) ⟶ H_{k-1}(U ∩ V)`

is exact in the sense that `H_k(Z)` sits between the kernel and the cokernel of explicit maps.  Since
`ℤ` is a Noetherian ring, `isNoetherian_of_range_eq_ker` applied to the exact piece
`H_k(U) ⊞ H_k(V) ⟶ H_k(Z) ⟶ H_{k-1}(U ∩ V)` exhibits `H_k(Z)` as an extension of a submodule of
the finitely generated `H_{k-1}(U ∩ V)` by a quotient of the finitely generated
`H_k(U) ⊞ H_k(V)`; hence it is finitely generated.

Splitting off the last set of the cover, `Z = (U_0 ∪ ⋯ ∪ U_{m-1}) ∪ U_m`, all three of the spaces
`A = U_0 ∪ ⋯ ∪ U_{m-1}`, `U_m` and `A ∩ U_m` inherit finite good covers:
`A` and `A ∩ U_m` from the sub-family `U_0, …, U_{m-1}` (intersected with `U_m` in the second case)
and `U_m` from the single set `U_m`, which is contractible (or empty).  This is the induction.

Degree `0` is not covered by the sequence above (there is no `H_{-1}`), and is treated separately:
`H_0(Z;ℤ)` is the free `ℤ`-module on the set of path components of `Z`
(`TopCat.singularHomology₀Iso`), and a finite cover by path-connected sets bounds the number of
path components by the number of sets.

* `IsGoodFam` — the good-cover condition in the form used by the induction;
* `fgch_...` — the auxiliary finiteness lemmas (`H_0`, the empty space, contractible spaces);
* `finiteHomology_of_goodFam` — the induction;
* `finiteGoodCoverHomology` — the statement of the assignment.
-/

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open CategoryTheory Limits

namespace Work.ThomBordism

noncomputable section

/-! ## Elementary transport lemmas for finite generation -/

/-- A vanishing `ℤ`-module is finitely generated. -/
theorem fgch_moduleFinite_of_isZero {M : ModuleCat ℤ} (h : IsZero M) : Module.Finite ℤ M := by
  haveI : Subsingleton M := ModuleCat.subsingleton_of_isZero h
  exact Module.Finite.of_surjective (0 : ℤ →ₗ[ℤ] M) (fun y => ⟨0, Subsingleton.elim _ _⟩)

/-- Finite generation transfers to the target of an isomorphism of `ℤ`-modules. -/
theorem fgch_moduleFinite_of_iso {M N : ModuleCat ℤ} (e : M ≅ N) (h : Module.Finite ℤ M) :
    Module.Finite ℤ N := by
  haveI := h
  exact Module.Finite.of_surjective (e.hom : M ⟶ N).hom
    ((ModuleCat.epi_iff_surjective (e.hom)).mp inferInstance)

/-- Finite generation transfers to the source of an isomorphism of `ℤ`-modules. -/
theorem fgch_moduleFinite_of_iso_symm {M N : ModuleCat ℤ} (e : M ≅ N)
    (h : Module.Finite ℤ N) : Module.Finite ℤ M := by
  haveI := h
  exact Module.Finite.of_surjective (e.inv : N ⟶ M).hom
    ((ModuleCat.epi_iff_surjective (e.inv)).mp inferInstance)

/-! ## The singular homology of the empty space -/

/-- A coproduct over an empty index type is a zero object. -/
theorem fgch_isZero_coproduct_of_isEmpty {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasZeroObject C] {β : Type*} [IsEmpty β] (f : β → C) [HasCoproduct f] :
    IsZero (∐ f) :=
  (coproductIsCoproduct f).isZero_pt
    ((Functor.isZero_iff (Discrete.functor f)).mpr (fun X => isEmptyElim X.as))

/-- The singular `n`-simplices of an empty space form an empty type. -/
theorem fgch_isEmpty_singularSimplex (Y : TopCat) [IsEmpty (↥Y)] (n : ℕ) :
    IsEmpty ((TopCat.toSSet.obj Y).obj (Opposite.op (SimplexCategory.mk n))) := by
  refine ⟨fun x => ?_⟩
  have hx := (TopCat.toSSetObjEquivOld Y (Opposite.op (SimplexCategory.mk n))) x
  haveI : Nonempty (↑(stdSimplex ℝ (Fin ((Opposite.unop (Opposite.op (SimplexCategory.mk n))).len + 1)))) :=
    inferInstance
  exact isEmptyElim (hx (Classical.arbitrary _))

/-- Every component of the singular chain complex of an empty space is a zero object. -/
theorem fgch_isZero_singularChains_X_of_isEmpty (Y : TopCat) [IsEmpty (↥Y)] (n : ℕ) :
    IsZero ((Work.Cohomology.singularChains ℤ Y).X n) := by
  haveI : IsEmpty ((TopCat.toSSet.obj Y).obj (Opposite.op (SimplexCategory.mk n))) :=
    fgch_isEmpty_singularSimplex Y n
  exact fgch_isZero_coproduct_of_isEmpty
    (fun _ : ((TopCat.toSSet.obj Y).obj (Opposite.op (SimplexCategory.mk n))) => ModuleCat.of ℤ ℤ)

/-- **The singular homology of the empty space vanishes.** -/
theorem fgch_isZero_homology_of_isEmpty (Y : TopCat) [IsEmpty (↥Y)] (m : ℕ) :
    IsZero ((Work.Cohomology.singularChains ℤ Y).homology m) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _ (fgch_isZero_singularChains_X_of_isEmpty Y m)

/-! ## Degree zero: spaces with finitely many path components -/

/-- The intersections over `PUnit` of a constant family. -/
theorem fgch_iInter_punit {α : Type*} (s : Set α) : (⋂ _ : PUnit, s) = s := by
  ext x
  simp

/-- If a space is covered by finitely many path-connected sets, it has finitely many path
components. -/
theorem fgch_finite_zerothHomotopy_of_cover {Z : Type} [TopologicalSpace Z] {ι : Type}
    [Fintype ι] (U : ι → Set Z) (hcov : (⋃ i, U i) = Set.univ)
    (hpc : ∀ i, (U i).Nonempty → PathConnectedSpace ↥(U i)) :
    Finite (ZerothHomotopy Z) := by
  classical
  by_cases hZ : Nonempty Z
  · have hsurj : Function.Surjective (fun i : {i : ι // (U i).Nonempty} =>
        ZerothHomotopy.mk (Classical.choose i.2)) := by
      intro z
      obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective z
      have hx : x ∈ (⋃ i, U i) := by rw [hcov]; exact Set.mem_univ x
      rw [Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      refine ⟨⟨i, ⟨x, hi⟩⟩, ?_⟩
      haveI : PathConnectedSpace ↥(U i) := hpc i ⟨x, hi⟩
      obtain ⟨γ⟩ := PathConnectedSpace.joined
        (⟨Classical.choose (show (U i).Nonempty from ⟨x, hi⟩),
          Classical.choose_spec (show (U i).Nonempty from ⟨x, hi⟩)⟩ : ↥(U i))
        (⟨x, hi⟩ : ↥(U i))
      exact ZerothHomotopy.sound (γ.map continuous_subtype_val)
    exact Finite.of_surjective _ hsurj
  · haveI : IsEmpty Z := not_nonempty_iff.mp hZ
    haveI : IsEmpty (ZerothHomotopy Z) :=
      ⟨fun q => ZerothHomotopy.rec (motive := fun _ => False) (fun x => isEmptyElim x) q⟩
    exact inferInstance

/-- If the space of path components is finite, then `H₀` is finitely generated. -/
theorem fgch_moduleFinite_homology_zero_of_fintype {Z : Type} [TopologicalSpace Z]
    [Fintype (ZerothHomotopy (TopCat.of Z))] :
    Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of Z)).homology 0) := by
  classical
  have e : ((Work.Cohomology.singularChains ℤ (TopCat.of Z)).homology 0) ≅
      ∐ (fun _ : ZerothHomotopy (TopCat.of Z) ↦ ModuleCat.of ℤ ℤ) :=
    TopCat.singularHomology₀Iso (TopCat.of Z) (ModuleCat.of ℤ ℤ)
  haveI : Module.Finite ℤ ↥(∐ (fun _ : ZerothHomotopy (TopCat.of Z) ↦ ModuleCat.of ℤ ℤ)) := by
    letI : DecidableEq (ZerothHomotopy (TopCat.of Z)) := Classical.decEq _
    have h1 : Module.Finite ℤ
        (DirectSum (ZerothHomotopy (TopCat.of Z)) (fun _ => ℤ)) :=
      Module.Finite.equiv
        (DirectSum.linearEquivFunOnFintype ℤ (ZerothHomotopy (TopCat.of Z))
          (fun _ => ℤ)).symm
    exact fgch_moduleFinite_of_iso_symm
      (ModuleCat.coprodIsoDirectSum (fun _ : ZerothHomotopy (TopCat.of Z) ↦ ModuleCat.of ℤ ℤ)) h1
  exact fgch_moduleFinite_of_iso_symm e inferInstance

/-- **`H₀` of a space with a finite cover by path-connected sets is finitely generated.** -/
theorem fgch_moduleFinite_homology_zero_of_cover {Z : Type} [TopologicalSpace Z] {ι : Type}
    [Fintype ι] (U : ι → Set Z) (hcov : (⋃ i, U i) = Set.univ)
    (hpc : ∀ i, (U i).Nonempty → PathConnectedSpace ↥(U i)) :
    Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of Z)).homology 0) := by
  haveI hfin : Finite (ZerothHomotopy Z) := fgch_finite_zerothHomotopy_of_cover U hcov hpc
  letI : Fintype (ZerothHomotopy Z) := Fintype.ofFinite (ZerothHomotopy Z)
  exact fgch_moduleFinite_homology_zero_of_fintype

/-! ## A single set: contractible or empty -/

/-- **The homology of a space which is either empty or contractible is finitely generated.** -/
theorem fgch_moduleFinite_homology_of_contractibleOrEmpty (Z : Type) [TopologicalSpace Z]
    (h : Nonempty Z → ContractibleSpace Z) (k : ℕ) :
    Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of Z)).homology k) := by
  by_cases hne : Nonempty Z
  · haveI : Nonempty Z := hne
    haveI : ContractibleSpace Z := h hne
    cases k with
    | zero =>
      haveI : Fintype (ZerothHomotopy (TopCat.of Z)) :=
        Fintype.ofSubsingleton (ZerothHomotopy.mk (Classical.arbitrary Z))
      exact fgch_moduleFinite_homology_zero_of_fintype
    | succ k =>
      exact fgch_moduleFinite_of_isZero
        (Work.Cohomology.homologyContractible (k + 1) (Nat.succ_pos k))
  · haveI : IsEmpty Z := not_nonempty_iff.mp hne
    exact fgch_moduleFinite_of_isZero (fgch_isZero_homology_of_isEmpty (TopCat.of Z) k)

/-! ## The good-cover condition -/

/-- A family of subsets of `Z` is a *good family* if it consists of open sets and every nonempty
finite intersection is contractible.  (The condition is indexed by an arbitrary finite type with a
base point, which makes it stable under restriction to subspaces and under reindexing.) -/
def IsGoodFam {Z : Type} [TopologicalSpace Z] {ι : Type} (U : ι → Set Z) : Prop :=
  (∀ i, IsOpen (U i)) ∧ ∀ (β : Type) [Fintype β] (f : β → ι) (b : β),
    (⋂ i : β, U (f i)).Nonempty → ContractibleSpace ↥(⋂ i : β, U (f i))

/-- The `Finset`-indexed form of the good-cover condition implies `IsGoodFam`. -/
theorem fgch_isGoodFam_of_finset {Z : Type} [TopologicalSpace Z] {ι : Type} (U : ι → Set Z)
    (hU : ∀ i, IsOpen (U i))
    (hgood : ∀ S : Finset ι, S.Nonempty → (⋂ i ∈ S, U i).Nonempty →
      ContractibleSpace ↥(⋂ i ∈ S, U i)) : IsGoodFam U := by
  classical
  refine ⟨hU, fun β _ f b hne => ?_⟩
  haveI : Nonempty β := ⟨b⟩
  have heq : (⋂ i : β, U (f i)) = ⋂ j ∈ (Finset.univ.image f), U j := by
    ext x
    simp only [Set.mem_iInter, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun h j hij => by obtain ⟨a, rfl⟩ := hij; exact h a,
      fun h i => h (f i) ⟨i, rfl⟩⟩
  rw [heq]
  exact hgood _ (Finset.image_nonempty.mpr Finset.univ_nonempty)
    (by rw [heq] at hne; exact hne)

/-- `IsGoodFam` is stable under reindexing. -/
theorem fgch_isGoodFam_comp {Z : Type} [TopologicalSpace Z] {ι ι' : Type} {U : ι → Set Z}
    (hU : IsGoodFam U) (g : ι' → ι) : IsGoodFam (fun i => U (g i)) := by
  refine ⟨fun i => hU.1 (g i), fun β _ f b hne => ?_⟩
  exact hU.2 β (fun i => g (f i)) b hne

/-- For `B ⊆ A ⊆ Z`, the subspace `{x : A | (x : Z) ∈ B}` of `A` is homeomorphic to `B`, so
contractibility transfers. -/
theorem fgch_contractibleSpace_of_subtype_subtype {Z : Type} [TopologicalSpace Z] {A B : Set Z}
    (hBA : B ⊆ A) (h : ContractibleSpace ↥B) : ContractibleSpace ↥{x : ↥A | (x : Z) ∈ B} := by
  haveI : ContractibleSpace ↥B := h
  let e : ↥{x : ↥A | (x : Z) ∈ B} ≃ₜ ↥B :=
    { toFun := fun x => ⟨(x : Z), x.2⟩
      invFun := fun y => ⟨⟨(y : Z), hBA y.2⟩, y.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun y => by ext; rfl
      continuous_toFun := Continuous.subtype_mk
        (continuous_subtype_val.comp continuous_subtype_val) (fun x => x.2)
      continuous_invFun := Continuous.subtype_mk
        (Continuous.subtype_mk continuous_subtype_val (fun y => hBA y.2)) (fun y => y.2) }
  exact e.contractibleSpace

/-- Intersecting every member of a good family with one fixed member preserves goodness. -/
theorem fgch_isGoodFam_inter_fam {Z : Type} [TopologicalSpace Z] {ι ι' : Type} {U : ι → Set Z}
    (hU : IsGoodFam U) (g : ι' → ι) (c : ι) :
    IsGoodFam (fun i : ι' => U (g i) ∩ U c) := by
  refine ⟨fun i => (hU.1 (g i)).inter (hU.1 c), fun β _ f b hne => ?_⟩
  have heq : (⋂ i : β, (U (g (f i)) ∩ U c))
      = ⋂ j : β ⊕ PUnit, U (Sum.elim (fun i => g (f i)) (fun _ => c) j) := by
    ext x
    rw [Set.mem_iInter, Set.mem_iInter]
    constructor
    · intro hx j
      cases j with
      | inl i => exact (hx i).1
      | inr u => exact (hx b).2
    · intro hx i
      exact ⟨hx (Sum.inl i), hx (Sum.inr PUnit.unit)⟩
  rw [heq]
  exact hU.2 (β ⊕ PUnit) (Sum.elim (fun i => g (f i)) (fun _ => c))
    (Sum.inl b) (by rw [heq] at hne; exact hne)

/-- `IsGoodFam` is stable under restricting the ambient space to a set containing all the members
of the family. -/
theorem fgch_isGoodFam_restrict {Z : Type} [TopologicalSpace Z] {ι : Type} {U : ι → Set Z}
    (hU : IsGoodFam U) {A : Set Z} (hA : ∀ i, U i ⊆ A) :
    IsGoodFam (fun i => {x : ↥A | (x : Z) ∈ U i}) := by
  refine ⟨fun i => (hU.1 i).preimage continuous_subtype_val, fun β _ f b hne => ?_⟩
  have hBA : (⋂ i : β, U (f i)) ⊆ A := fun z hz => hA (f b) (Set.mem_iInter.mp hz b)
  have heq : (⋂ i : β, {x : ↥A | (x : Z) ∈ U (f i)})
      = {x : ↥A | (x : Z) ∈ ⋂ i : β, U (f i)} := by
    ext x
    simp [Set.mem_iInter]
  rw [heq]
  haveI : ContractibleSpace ↥(⋂ i : β, U (f i)) := by
    refine hU.2 β f b ?_
    obtain ⟨x, hx⟩ := hne
    exact ⟨(x : Z), by simpa [heq] using hx⟩
  exact fgch_contractibleSpace_of_subtype_subtype hBA inferInstance

/-! ## The induction on the number of sets -/

/-- **The main induction.**  A space covered by the members of a finite good family `U : Fin m → Set Z`
has finitely generated singular homology in every degree. -/
theorem finiteHomology_of_goodFam : ∀ (m : ℕ) (Z : Type) [TopologicalSpace Z] (U : Fin m → Set Z),
    IsGoodFam U → (⋃ i, U i) = Set.univ → ∀ k,
      Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of Z)).homology k) := by
  intro m
  induction m with
  | zero =>
    intro Z _ U hU hcov k
    haveI : IsEmpty Z := by
      refine ⟨fun x => ?_⟩
      have hx : x ∈ (⋃ i : Fin 0, U i) := by rw [hcov]; exact Set.mem_univ x
      simpa using hx
    exact fgch_moduleFinite_of_isZero (fgch_isZero_homology_of_isEmpty (TopCat.of Z) k)
  | succ m ih =>
    intro Z _ U hU hcov k
    set A : Set Z := ⋃ i : Fin m, U (Fin.castSucc i) with hA
    set V : Set Z := U (Fin.last m) with hV
    have hUeq : (⋃ i : Fin (m + 1), U i) = V ∪ A := by
      rw [hA, hV]
      ext x
      constructor
      · intro hx
        rw [Set.mem_iUnion] at hx
        obtain ⟨i, hi⟩ := hx
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · exact Or.inr (Set.mem_iUnion.mpr ⟨j, hi⟩)
        · exact Or.inl hi
      · intro hx
        rcases hx with hx | hx
        · exact Set.mem_iUnion.mpr ⟨Fin.last m, hx⟩
        · rw [Set.mem_iUnion] at hx
          obtain ⟨j, hj⟩ := hx
          exact Set.mem_iUnion.mpr ⟨Fin.castSucc j, hj⟩
    have hcovAV : A ∪ V = Set.univ := by
      rw [Set.union_comm, ← hUeq]
      exact hcov
    have hAopen : IsOpen A := by rw [hA]; exact isOpen_iUnion fun i => hU.1 _
    have hVopen : IsOpen V := by rw [hV]; exact hU.1 _
    rcases k with _ | k
    · -- degree zero
      refine fgch_moduleFinite_homology_zero_of_cover U hcov ?_
      intro i hne
      have h1 := hU.2 PUnit (fun _ : PUnit => i) PUnit.unit
      rw [fgch_iInter_punit] at h1
      haveI : ContractibleSpace ↥(U i) := h1 hne
      infer_instance
    · -- degree `k + 1`
      have hUg : IsGoodFam (fun i : Fin m => U (Fin.castSucc i)) :=
        fgch_isGoodFam_comp hU Fin.castSucc
      have hWA : IsGoodFam (fun i : Fin m => {x : ↥A | (x : Z) ∈ U (Fin.castSucc i)}) := by
        rw [hA]
        exact fgch_isGoodFam_restrict hUg (fun i x hx => Set.mem_iUnion.mpr ⟨i, hx⟩)
      have hWAV : IsGoodFam
          (fun i : Fin m => {x : ↥(A ∩ V) | (x : Z) ∈ U (Fin.castSucc i) ∩ V}) := by
        rw [hA, hV]
        exact fgch_isGoodFam_restrict (fgch_isGoodFam_inter_fam hU Fin.castSucc (Fin.last m))
          (fun i => Set.inter_subset_inter (fun x hx => Set.mem_iUnion.mpr ⟨i, hx⟩)
            (Set.Subset.refl _))
      have hWA_cov : (⋃ i : Fin m, {x : ↥A | (x : Z) ∈ U (Fin.castSucc i)}) = Set.univ := by
        ext x
        constructor
        · intro _; trivial
        · intro _
          have hx : (x : Z) ∈ (⋃ i : Fin m, U (Fin.castSucc i)) := by
            rw [← hA]; exact x.2
          rw [Set.mem_iUnion] at hx
          obtain ⟨i, hi⟩ := hx
          exact Set.mem_iUnion.mpr ⟨i, hi⟩
      have hWAV_cov :
          (⋃ i : Fin m, {x : ↥(A ∩ V) | (x : Z) ∈ U (Fin.castSucc i) ∩ V}) = Set.univ := by
        ext x
        constructor
        · intro _; trivial
        · intro _
          have hx : (x : Z) ∈ (⋃ i : Fin m, U (Fin.castSucc i)) := by
            rw [← hA]; exact x.2.1
          rw [Set.mem_iUnion] at hx
          obtain ⟨i, hi⟩ := hx
          exact Set.mem_iUnion.mpr ⟨i, ⟨hi, x.2.2⟩⟩
      have hVcontr : Nonempty ↥V → ContractibleSpace ↥V := by
        rw [hV]
        intro hne
        have h1 := hU.2 PUnit (fun _ : PUnit => Fin.last m) PUnit.unit
        rw [fgch_iInter_punit] at h1
        exact h1 (Set.nonempty_coe_sort.mp hne)
      have hAfin : Module.Finite ℤ
          ((Work.Cohomology.singularChains ℤ (TopCat.of ↥A)).homology (k + 1)) :=
        ih ↥A _ hWA hWA_cov (k + 1)
      have hVfin : Module.Finite ℤ
          ((Work.Cohomology.singularChains ℤ (TopCat.of ↥V)).homology (k + 1)) :=
        fgch_moduleFinite_homology_of_contractibleOrEmpty ↥V hVcontr (k + 1)
      have hAVfin : Module.Finite ℤ
          ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(A ∩ V))).homology k) :=
        ih ↥(A ∩ V) _ hWAV hWAV_cov k
      have hbip : Module.Finite ℤ
          (((Work.Cohomology.singularChains ℤ (TopCat.of A)) ⊞
            (Work.Cohomology.singularChains ℤ (TopCat.of V))).homology (k + 1)) :=
        moduleFiniteHomologyBiprod (k + 1) hAfin hVfin
      haveI : IsNoetherian ℤ
          ↥(((Work.Cohomology.singularChains ℤ (TopCat.of A)) ⊞
            (Work.Cohomology.singularChains ℤ (TopCat.of V))).homology (k + 1)) :=
        isNoetherian_of_isNoetherianRing_of_finite ℤ _
      haveI : IsNoetherian ℤ
          ↥(Work.Cohomology.HInter (X := TopCat.of Z) A V k) :=
        isNoetherian_of_isNoetherianRing_of_finite ℤ _
      have hsmall : IsNoetherian ℤ
          ↥(Work.Cohomology.HSmall (X := TopCat.of Z) A V (k + 1)) :=
        isNoetherian_of_range_eq_ker
          ((HomologicalComplex.homologyMap
            (Work.Cohomology.mvRight (X := TopCat.of Z) A V) (k + 1)).hom)
          ((Work.Cohomology.mvδ (X := TopCat.of Z) A V k).hom)
          (CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker
            (Work.Cohomology.mv_H_exact₃ (X := TopCat.of Z) A V k))
      have hsmallfin : Module.Finite ℤ
          (Work.Cohomology.HSmall (X := TopCat.of Z) A V (k + 1)) := by
        haveI := hsmall
        exact inferInstance
      exact fgch_moduleFinite_of_iso
        (Work.Cohomology.smallIso (X := TopCat.of Z) A V hAopen hVopen hcovAV (k + 1)) hsmallfin

/-! ## The statement of the assignment -/

/-- **A space with a finite good cover has finitely generated singular homology.** -/
theorem finiteGoodCoverHomology {Z : Type} [TopologicalSpace Z] (m : ℕ) (U : Fin m → Set Z)
    (hU : ∀ i, IsOpen (U i)) (hcov : (⋃ i, U i) = Set.univ)
    (hgood : ∀ S : Finset (Fin m), S.Nonempty → (⋂ i ∈ S, U i).Nonempty →
      ContractibleSpace ↥(⋂ i ∈ S, U i)) (k : ℕ) :
    Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of Z)).homology k) :=
  finiteHomology_of_goodFam m Z U (fgch_isGoodFam_of_finset U hU hgood) hcov k

end

end Work.ThomBordism
