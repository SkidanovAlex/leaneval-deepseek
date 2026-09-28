import Mathlib
import Submission.Work.ThomBordism.finiteGoodCoverHomology

/-!
# Finitely generated singular homology for a finite open cover

This file proves `Work.EMFG.finiteCoverFG`: if a space `Z` is the union of a *finite* family of
open sets `U i`, and every nonempty finite intersection `⋂ i ∈ S, U i` has finitely generated
integral singular homology in every degree, then `H_k(Z; ℤ)` is finitely generated for every `k`.

This generalises `Work.ThomBordism.finiteGoodCoverHomology` (where the intersections are required
to be contractible) to the case where only finite generation of the homology of the intersections
is assumed.  The argument is the same induction on the number of sets, using the Mayer–Vietoris
long exact sequence and the fact that `ℤ` is Noetherian; the geometric input "the intersections are
contractible" is replaced by the hypothesis itself.

## Strategy

* `Goal ι s` is the induction statement: the union of the members of `s` has finitely generated
  homology in all positive degrees.  It is proved by induction on the finite set `s`
  (`finiteHomology_finset`), splitting off one member at a time.  For `Z = A ∪ V` with `A` the
  union of the first members and `V` a single member, Mayer–Vietoris in the ambient space `↥(A ∪ V)`
  exhibits `H_{k}(Z)` as an extension of a submodule of the finitely generated `H_{k-1}(A ∩ V)` by a
  quotient of the finitely generated `H_k(A) ⊞ H_k(V)`.
* The intersection `A ∩ V = ⋃ (U i ∩ V)` is again a union of a finite family all of whose finite
  intersections are finite intersections of the `U i`, so the induction hypothesis (respectively the
  degree-zero counting argument) applies to it.
* Degree zero is treated separately, by counting path components (`fg_h0_union_finset`).
-/

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory Limits

namespace Work.EMFG

noncomputable section

/-! ## Transport of finite generation along homeomorphisms and equalities of sets -/

/-- Equal subsets give homeomorphic subspaces. -/
def homeo_of_set_eq {α : Type} [TopologicalSpace α] {S T : Set α} (h : S = T) : ↥S ≃ₜ ↥T where
  toFun x := ⟨(x : α), h ▸ x.2⟩
  invFun y := ⟨(y : α), h.symm ▸ y.2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- For `S ⊆ T`, the subspace `S` of `α` is homeomorphic to the corresponding subspace of `T`. -/
def homeo_subtype_subset {α : Type} [TopologicalSpace α] {S T : Set α} (h : S ⊆ T) :
    ↥S ≃ₜ ↥{x : ↥T | (x : α) ∈ S} where
  toFun x := ⟨⟨(x : α), h x.2⟩, x.2⟩
  invFun y := ⟨y.1.1, y.2⟩
  left_inv x := rfl
  right_inv y := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- A homeomorphism induces an isomorphism of the integral singular homology in every degree, hence
transfers finite generation. -/
theorem fg_homology_of_homeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (k : ℕ)
    (h : Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology k)) :
    Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology k) := by
  let F : TopCat ⥤ ChainComplex (ModuleCat ℤ) ℕ :=
    (AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)
  have iso := (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k).mapIso
    (F.mapIso (TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of Y) e))
  exact Work.ThomBordism.fgch_moduleFinite_of_iso iso h

/-- Finite generation of the integral singular homology transfers along an equality of subsets. -/
theorem fg_homology_of_set_eq {α : Type} [TopologicalSpace α] {S T : Set α} (h : S = T) (k : ℕ)
    (hf : Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of ↥S)).homology k)) :
    Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of ↥T)).homology k) :=
  fg_homology_of_homeomorph (homeo_of_set_eq h) k hf

/-! ## Degree zero: counting path components -/

/-- If `H₀(X; ℤ)` is finitely generated then `X` has finitely many path components. -/
theorem finite_zerothHomotopy_of_fg_h0 (X : Type) [TopologicalSpace X]
    (h : Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology 0)) :
    Finite (ZerothHomotopy X) := by
  classical
  have e : (Work.Cohomology.singularChains ℤ (TopCat.of X)).homology 0 ≅
      ∐ (fun _ : ZerothHomotopy X => ModuleCat.of ℤ ℤ) :=
    TopCat.singularHomology₀Iso (TopCat.of X) (ModuleCat.of ℤ ℤ)
  haveI h1 : Module.Finite ℤ ↥(∐ (fun _ : ZerothHomotopy X => ModuleCat.of ℤ ℤ)) :=
    Work.ThomBordism.fgch_moduleFinite_of_iso e h
  haveI h2 : Module.Finite ℤ (DirectSum (ZerothHomotopy X) (fun _ => ℤ)) :=
    Work.ThomBordism.fgch_moduleFinite_of_iso
      (ModuleCat.coprodIsoDirectSum (fun _ : ZerothHomotopy X => ModuleCat.of ℤ ℤ)) h1
  haveI h3 : Module.Finite ℤ ((ZerothHomotopy X) →₀ ℤ) :=
    Module.Finite.equiv (finsuppLEquivDirectSum ℤ ℤ (ZerothHomotopy X)).symm
  rcases (Module.finite_finsupp_self_iff (R := ℤ) (ι := ZerothHomotopy X)).mp h3 with h4 | h4
  · exact absurd h4 (not_subsingleton_iff_nontrivial.mpr inferInstance)
  · exact h4

/-- If `X` has finitely many path components then `H₀(X; ℤ)` is finitely generated. -/
theorem fg_h0_of_finite_zerothHomotopy (X : Type) [TopologicalSpace X]
    (h : Finite (ZerothHomotopy X)) :
    Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology 0) := by
  haveI : Fintype (ZerothHomotopy (TopCat.of X)) := Fintype.ofFinite _
  exact Work.ThomBordism.fgch_moduleFinite_homology_zero_of_fintype

/-- A finite cover by sets with finitely many path components has finitely many path components:
each path component of `Z` contains a path component of one of the covering sets. -/
theorem finite_zerothHomotopy_of_cover {Z : Type} [TopologicalSpace Z] {ι : Type} [Fintype ι]
    (U : ι → Set Z) (hcov : (⋃ i, U i) = Set.univ)
    (h : ∀ i, Finite (ZerothHomotopy ↥(U i))) : Finite (ZerothHomotopy Z) := by
  classical
  haveI : ∀ i, Fintype (ZerothHomotopy ↥(U i)) := fun i => Fintype.ofFinite _
  have hsurj : Function.Surjective
      (fun p : Σ i, ZerothHomotopy ↥(U i) =>
        ZerothHomotopy.lift (fun x : ↥(U p.1) => ZerothHomotopy.mk (x : Z))
          (fun x y γ => ZerothHomotopy.sound (γ.map continuous_subtype_val)) p.2) := by
    intro q
    obtain ⟨z, rfl⟩ := ZerothHomotopy.mk_surjective q
    have hz : z ∈ (⋃ i, U i) := by rw [hcov]; trivial
    rw [Set.mem_iUnion] at hz
    obtain ⟨i, hi⟩ := hz
    exact ⟨⟨i, ZerothHomotopy.mk ⟨z, hi⟩⟩, ZerothHomotopy.lift_mk _ _ _⟩
  exact Finite.of_surjective _ hsurj

/-- `H₀` of a space with a finite cover by sets with finitely generated `H₀` is finitely
generated. -/
theorem fg_h0_of_cover {Z : Type} [TopologicalSpace Z] {ι : Type} [Fintype ι] (U : ι → Set Z)
    (hcov : (⋃ i, U i) = Set.univ)
    (h : ∀ i, Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(U i))).homology 0)) :
    Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of Z)).homology 0) :=
  fg_h0_of_finite_zerothHomotopy Z
    (finite_zerothHomotopy_of_cover U hcov (fun i => finite_zerothHomotopy_of_fg_h0 ↥(U i) (h i)))

/-- `H₀` of a finite union of sets with finitely generated `H₀` is finitely generated. -/
theorem fg_h0_union_finset {ι : Type} {Z : Type} [TopologicalSpace Z] (s : Finset ι) (W : ι → Set Z)
    (h : ∀ i ∈ s,
      Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(W i))).homology 0)) :
    Module.Finite ℤ
      ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(⋃ i ∈ s, W i))).homology 0) := by
  classical
  letI : Fintype {i : ι // i ∈ s} := Fintype.ofFinset s (fun x => Iff.rfl)
  refine fg_h0_of_cover
    (U := fun i : {i : ι // i ∈ s} =>
      {x : ↥(⋃ j ∈ s, W j) | (x : Z) ∈ W i.1}) ?_ ?_
  · ext x
    constructor
    · intro _; trivial
    · intro _
      have hx : (x : Z) ∈ ⋃ j ∈ s, W j := x.2
      rw [Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      rw [Set.mem_iUnion] at hi
      obtain ⟨his, hix⟩ := hi
      exact Set.mem_iUnion.mpr ⟨⟨i, his⟩, hix⟩
  · intro i
    exact fg_homology_of_homeomorph (homeo_subtype_subset (S := W i.1) (T := ⋃ j ∈ s, W j) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨i.1, Set.mem_iUnion.mpr ⟨i.2, hx⟩⟩)) 0 (h i.1 i.2)

/-! ## The family condition -/

/-- A family of open sets such that every nonempty finite intersection of members has finitely
generated integral singular homology in every degree.  As in `Work.ThomBordism.IsGoodFam`, the
condition is indexed by an arbitrary finite type with a base point, which makes it stable under
reindexing and under intersecting with a fixed member. -/
def IsFGFam {Z : Type} [TopologicalSpace Z] {ι : Type} (U : ι → Set Z) : Prop :=
  (∀ i, IsOpen (U i)) ∧
    ∀ (β : Type) [Fintype β] (f : β → ι) (b : β) (k : ℕ),
      Module.Finite ℤ
        ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(⋂ i : β, U (f i)))).homology k)

/-- The `Finset`-indexed form of the hypothesis implies `IsFGFam`. -/
theorem isFGFam_of_finset {Z : Type} [TopologicalSpace Z] {ι : Type} (U : ι → Set Z)
    (hopen : ∀ i, IsOpen (U i))
    (hfg : ∀ S : Finset ι, S.Nonempty → ∀ k : ℕ,
      Module.Finite ℤ ((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥(⋂ i ∈ S, U i))).homology k)) :
    IsFGFam U := by
  classical
  refine ⟨hopen, fun β _ f b k => ?_⟩
  have heq : (⋂ j ∈ (Finset.univ.image f), U j) = ⋂ i : β, U (f i) := by
    ext x
    simp only [Set.mem_iInter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hx i
      exact hx (f i) ⟨i, rfl⟩
    · rintro hx i ⟨a, rfl⟩
      exact hx a
  have hne : (Finset.univ.image f).Nonempty :=
    ⟨f b, Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩⟩
  exact fg_homology_of_set_eq heq k (hfg _ hne k)

/-- An `IsFGFam` family has finitely generated homology on each of its members. -/
theorem IsFGFam.single {Z : Type} [TopologicalSpace Z] {ι : Type} {U : ι → Set Z}
    (hU : IsFGFam U) (i : ι) (k : ℕ) :
    Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(U i))).homology k) :=
  fg_homology_of_set_eq (Work.ThomBordism.fgch_iInter_punit (U i)) k
    (hU.2 PUnit (fun _ : PUnit => i) PUnit.unit k)

/-- An `IsFGFam` family has finitely generated homology on each pairwise intersection of its
members. -/
theorem IsFGFam.pair {Z : Type} [TopologicalSpace Z] {ι : Type} {U : ι → Set Z}
    (hU : IsFGFam U) (i j : ι) (k : ℕ) :
    Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(U i ∩ U j))).homology k) := by
  have heq : (⋂ b : PUnit ⊕ PUnit,
      U (Sum.elim (fun _ : PUnit => i) (fun _ : PUnit => j) b)) = U i ∩ U j := by
    ext x
    simp only [Set.mem_iInter, Set.mem_inter_iff]
    constructor
    · intro hx
      exact ⟨hx (Sum.inl PUnit.unit), hx (Sum.inr PUnit.unit)⟩
    · intro hx b
      rcases b with _ | _
      · exact hx.1
      · exact hx.2
  exact fg_homology_of_set_eq heq k (hU.2 (PUnit ⊕ PUnit)
    (Sum.elim (fun _ : PUnit => i) (fun _ : PUnit => j)) (Sum.inl PUnit.unit) k)

/-- Intersecting every member of an `IsFGFam` family with one fixed member preserves the
condition. -/
theorem isFGFam_inter {Z : Type} [TopologicalSpace Z] {ι : Type} {U : ι → Set Z}
    (hU : IsFGFam U) (c : ι) : IsFGFam (fun i => U i ∩ U c) := by
  refine ⟨fun i => (hU.1 i).inter (hU.1 c), fun β _ f b k => ?_⟩
  have heq : (⋂ j : β ⊕ PUnit, U (Sum.elim f (fun _ : PUnit => c) j))
      = ⋂ i : β, (U (f i) ∩ U c) := by
    ext x
    simp only [Set.mem_iInter, Set.mem_inter_iff]
    constructor
    · intro hx i
      exact ⟨hx (Sum.inl i), hx (Sum.inr PUnit.unit)⟩
    · intro hx j
      rcases j with i | u
      · exact (hx i).1
      · exact (hx b).2
  exact fg_homology_of_set_eq heq k
    (hU.2 (β ⊕ PUnit) (Sum.elim f (fun _ : PUnit => c)) (Sum.inl b) k)

/-! ## The two-set Mayer–Vietoris step -/

/-- **The two-set step.**  If `A` and `V` are open subsets of `W` covering `W`, and `H_{k+1}` of
`A` and of `V` as well as `H_k` of `A ∩ V` are finitely generated, then so is `H_{k+1}(W)`.

This is the Mayer–Vietoris argument of `Work.ThomBordism.finiteHomology_of_goodFam` isolated with
the ambient space, `A` and `V` as variables. -/
theorem fg_homology_union_two {W : Type} [TopologicalSpace W] {A V : Set W}
    (hAopen : IsOpen A) (hVopen : IsOpen V) (hcov : A ∪ V = Set.univ) (k : ℕ)
    (hAh : Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of ↥A)).homology (k + 1)))
    (hVh : Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of ↥V)).homology (k + 1)))
    (hAVh : Module.Finite ℤ
      ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(A ∩ V))).homology k)) :
    Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of W)).homology (k + 1)) := by
  have hbip : Module.Finite ℤ
      (((Work.Cohomology.singularChains ℤ (TopCat.of A)) ⊞
        (Work.Cohomology.singularChains ℤ (TopCat.of V))).homology (k + 1)) :=
    Work.ThomBordism.moduleFiniteHomologyBiprod (k + 1) hAh hVh
  haveI : IsNoetherian ℤ
      ↥(((Work.Cohomology.singularChains ℤ (TopCat.of A)) ⊞
        (Work.Cohomology.singularChains ℤ (TopCat.of V))).homology (k + 1)) :=
    isNoetherian_of_isNoetherianRing_of_finite ℤ _
  haveI : IsNoetherian ℤ ↥(Work.Cohomology.HInter (X := TopCat.of W) A V k) :=
    isNoetherian_of_isNoetherianRing_of_finite ℤ _
  have hsmall : IsNoetherian ℤ ↥(Work.Cohomology.HSmall (X := TopCat.of W) A V (k + 1)) :=
    isNoetherian_of_range_eq_ker
      ((HomologicalComplex.homologyMap
        (Work.Cohomology.mvRight (X := TopCat.of W) A V) (k + 1)).hom)
      ((Work.Cohomology.mvδ (X := TopCat.of W) A V k).hom)
      (CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker
        (Work.Cohomology.mv_H_exact₃ (X := TopCat.of W) A V k))
  have hsmallfin : Module.Finite ℤ (Work.Cohomology.HSmall (X := TopCat.of W) A V (k + 1)) := by
    haveI := hsmall
    exact inferInstance
  exact Work.ThomBordism.fgch_moduleFinite_of_iso
    (Work.Cohomology.smallIso (X := TopCat.of W) A V hAopen hVopen hcov (k + 1)) hsmallfin

/-! ## The induction on the finite set of members -/

/-- The induction statement: the union of the members of `s` has finitely generated integral
singular homology in every positive degree. -/
def Goal (ι : Type) (s : Finset ι) : Prop :=
  ∀ (Z : Type) [TopologicalSpace Z] (U : ι → Set Z), IsFGFam U → ∀ k : ℕ, 1 ≤ k →
    Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(⋃ i ∈ s, U i))).homology k)

/-- **The main induction.** -/
theorem finiteHomology_finset (ι : Type) (s : Finset ι) : Goal ι s := by
  classical
  induction s using Finset.induction with
  | empty =>
    intro Z _ U _ k hk
    have h0 : (⋃ i ∈ (∅ : Finset ι), U i) = (∅ : Set Z) := by
      ext x
      simp
    refine fg_homology_of_set_eq h0.symm k ?_
    haveI : IsEmpty ↥(∅ : Set Z) := Set.isEmpty_coe_sort.mpr rfl
    exact Work.ThomBordism.fgch_moduleFinite_of_isZero
      (Work.ThomBordism.fgch_isZero_homology_of_isEmpty (TopCat.of ↥(∅ : Set Z)) k)
  | insert a s has ih =>
    intro Z _ U hU k hk
    set A : Set Z := ⋃ i ∈ s, U i with hA
    set V : Set Z := U a with hV
    have hunion : (⋃ i ∈ insert a s, U i) = A ∪ V := by
      rw [hA, hV]
      ext x
      simp only [Set.mem_iUnion, Set.mem_union, Finset.mem_insert]
      aesop
    refine fg_homology_of_set_eq hunion.symm k ?_
    rcases k with _ | j
    · omega
    · have hAopen : IsOpen A := by
        rw [hA]; exact isOpen_iUnion fun i => isOpen_iUnion fun _ => hU.1 i
      have hVopen : IsOpen V := by rw [hV]; exact hU.1 a
      let A' : Set ↥(A ∪ V) := {x | (x : Z) ∈ A}
      let V' : Set ↥(A ∪ V) := {x | (x : Z) ∈ V}
      have hA'open : IsOpen A' := hAopen.preimage continuous_subtype_val
      have hV'open : IsOpen V' := hVopen.preimage continuous_subtype_val
      have hcovAV : A' ∪ V' = Set.univ := by
        ext x
        simp only [Set.mem_union, Set.mem_univ, iff_true]
        rcases x.2 with h | h
        · exact Or.inl h
        · exact Or.inr h
      have hAhom : Module.Finite ℤ
          ((Work.Cohomology.singularChains ℤ (TopCat.of A')).homology (j + 1)) :=
        fg_homology_of_homeomorph (homeo_subtype_subset (S := A) (T := A ∪ V) (by intro x hx; exact Or.inl hx)) (j + 1)
          (fg_homology_of_set_eq hA.symm (j + 1) (ih Z U hU (j + 1) (by omega)))
      have hVhom : Module.Finite ℤ
          ((Work.Cohomology.singularChains ℤ (TopCat.of V')).homology (j + 1)) :=
        fg_homology_of_homeomorph (homeo_subtype_subset (S := V) (T := A ∪ V) (by intro x hx; exact Or.inr hx)) (j + 1)
          (fg_homology_of_set_eq hV.symm (j + 1) (IsFGFam.single hU a (j + 1)))
      have heq : (⋃ i ∈ s, U i ∩ U a) = A ∩ V := by
        rw [hA, hV]
        ext x
        simp only [Set.mem_iUnion, Set.mem_inter_iff]
        aesop
      have hIV : Module.Finite ℤ
          ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(A ∩ V))).homology j) := by
        rcases Nat.eq_zero_or_pos j with hj0 | hjpos
        · subst hj0
          exact fg_homology_of_set_eq heq 0
            (fg_h0_union_finset s (fun i => U i ∩ U a) (fun i _ => IsFGFam.pair hU i a 0))
        · exact fg_homology_of_set_eq heq j
            (ih Z (fun i => U i ∩ U a) (isFGFam_inter hU a) j hjpos)
      have hIV' : Module.Finite ℤ
          ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(A' ∩ V'))).homology j) :=
        fg_homology_of_homeomorph
          (homeo_subtype_subset (S := A ∩ V) (T := A ∪ V) (by intro x hx; exact Or.inl hx.1)) j hIV
      exact fg_homology_union_two hA'open hV'open hcovAV j hAhom hVhom hIV'

/-! ## The statement of the assignment -/

theorem finiteCoverFG {Z : Type} [TopologicalSpace Z] {ι : Type} [Fintype ι]
    (U : ι → Set Z) (hopen : ∀ i, IsOpen (U i)) (hcov : (⋃ i, U i) = Set.univ)
    (hfg : ∀ (S : Finset ι), S.Nonempty → ∀ k : ℕ,
      Module.Finite ℤ ((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥(⋂ i ∈ S, U i))).homology k)) :
    ∀ k : ℕ, Module.Finite ℤ ((Work.Cohomology.singularChains ℤ (TopCat.of Z)).homology k) := by
  classical
  have hU : IsFGFam U := isFGFam_of_finset U hopen hfg
  intro k
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    exact fg_h0_of_cover U hcov (fun i => IsFGFam.single hU i 0)
  · have h1 := finiteHomology_finset ι Finset.univ Z U hU k hkpos
    have hset : (⋃ i ∈ (Finset.univ : Finset ι), U i) = (⋃ i, U i) := by
      ext x
      simp
    exact fg_homology_of_homeomorph (Homeomorph.Set.univ Z) k
      (fg_homology_of_set_eq hcov k (fg_homology_of_set_eq hset k h1))

end

end Work.EMFG
