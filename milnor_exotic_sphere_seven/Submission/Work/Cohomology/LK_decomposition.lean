import Mathlib
import Submission.Work.Cohomology.StageSplitDefs
import Submission.Work.Cohomology.relChains_compl_union_free
import Submission.Work.Cohomology.relChains_vanishing_of_compact
import Submission.Work.Cohomology.cokernel_biprod_map_iso
import Submission.Work.Cohomology.lk_twoSet_homologyMap_isIso
import Submission.Work.Cohomology.homology_biprod_fst_snd_bijective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The decomposition of the local homology of a finite disjoint union

For a finite family `K : ι → Set (EuclideanSpace ℝ (Fin N))` of pairwise disjoint compact sets,
the local homology `LK N (⋃ i, K i) = H_N(ℝ^N, ℝ^N ∖ ⋃ i, K i)` splits as the product of the
local homologies `LK N (K i)`, and the components of the splitting are the stage maps `lkMap`.

The mathematical input is the Mayer–Vietoris statement for the *relative* homology of the pair
`(ℝ^N, ℝ^N ∖ ⋃ K i)`: the complements `S i := (K i)ᶜ` are open sets covering `ℝ^N`, and the
snake lemma applied to `mvToTrivial : mvShort S T ⟶ trivialShort` (see
`Submission/Work/Cohomology/relChains_compl_union_free.lean`) exhibits the pair of restriction
maps `C_*(M)/C_*(S∩T) ⟶ C_*(M)/C_*(S) ⊞ C_*(M)/C_*(T)` whose third term is the small–chains
quotient; that quotient is acyclic in positive degrees, so the two restriction maps are a
quasi-isomorphism in degree `N ≥ 1` (`Work.Cohomology.lk_twoSet_homologyMap_isIso`).

The passage from two sets to a finite family is an induction over finite types, splitting off one
index at a time.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable {N : ℕ}

/-! ## Elementary properties of the stage maps -/

/-- The map of relative chain complexes induced by an inclusion of subsets only depends on the
subsets, not on the proof of the inclusion. -/
theorem relCokerMap_congr {M : TopCat} {A B : Set M} (h h' : A ⊆ B) :
    relCokerMap M A B h = relCokerMap M A B h' := by
  apply (cancel_epi (cokernel.π (inclChains M A))).mp
  simp only [relCokerMap_comp_π]

/-- The stage map `lkMap` only depends on the two sets, not on the proof of the inclusion. -/
theorem lkMap_congr {K K' : Set (EuclideanSpace ℝ (Fin N))} (h h' : K ⊆ K') :
    lkMap (N := N) h = lkMap (N := N) h' := by
  unfold lkMap
  congr 1

/-- A map of the form `relCokerMap M V W (le_of_eq e)` with `e : V = W` is an isomorphism (with
inverse `relCokerMap M W V (le_of_eq e.symm)`). -/
theorem isIso_relCokerMap_of_eq {M : TopCat} {V W : Set M} (e : V = W) :
    IsIso (relCokerMap M V W (le_of_eq e)) := by
  have h₁ : relCokerMap M V W (le_of_eq e) ≫ relCokerMap M W V (le_of_eq e.symm) = 𝟙 _ := by
    rw [relCokerMap_comp]
    apply (cancel_epi (cokernel.π (inclChains M V))).mp
    simp only [relCokerMap_comp_π, Category.comp_id]
  have h₂ : relCokerMap M W V (le_of_eq e.symm) ≫ relCokerMap M V W (le_of_eq e) = 𝟙 _ := by
    rw [relCokerMap_comp]
    apply (cancel_epi (cokernel.π (inclChains M W))).mp
    simp only [relCokerMap_comp_π, Category.comp_id]
  exact ⟨relCokerMap M W V (le_of_eq e.symm), h₁, h₂⟩

/-! ## Abbreviations for the two–set step

The two–set step compares the relative chain complexes of the complements of `A`, `B` and
`A ∪ B`.  The objects and maps occurring in it are abbreviated here so that the statements below
stay readable.
-/

abbrev srcC (A B : Set (EuclideanSpace ℝ (Fin N))) : ModuleCat ℤ :=
  (relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) (Aᶜ ∩ Bᶜ)).homology N

abbrev bipC (A B : Set (EuclideanSpace ℝ (Fin N))) : ModuleCat ℤ :=
  (relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) Aᶜ ⊞
    relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) Bᶜ).homology N

abbrev relAMor (A B : Set (EuclideanSpace ℝ (Fin N))) :
    relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) (Aᶜ ∩ Bᶜ) ⟶
      relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) Aᶜ :=
  relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N))) (Aᶜ ∩ Bᶜ) Aᶜ Set.inter_subset_left

abbrev relBMor (A B : Set (EuclideanSpace ℝ (Fin N))) :
    relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) (Aᶜ ∩ Bᶜ) ⟶
      relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) Bᶜ :=
  relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N))) (Aᶜ ∩ Bᶜ) Bᶜ Set.inter_subset_right

abbrev liftMor (A B : Set (EuclideanSpace ℝ (Fin N))) :
    relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) (Aᶜ ∩ Bᶜ) ⟶
      relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) Aᶜ ⊞
        relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) Bᶜ :=
  biprod.lift (relAMor A B) (relBMor A B)

abbrev fstMor (A B : Set (EuclideanSpace ℝ (Fin N))) :
    relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) Aᶜ ⊞
      relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) Bᶜ ⟶
        relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) Aᶜ :=
  biprod.fst

abbrev sndMor (A B : Set (EuclideanSpace ℝ (Fin N))) :
    relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) Aᶜ ⊞
      relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) Bᶜ ⟶
        relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) Bᶜ :=
  biprod.snd

abbrev lfA (A B : Set (EuclideanSpace ℝ (Fin N))) : ↥(srcC A B) →ₗ[ℤ] LK N A :=
  (HomologicalComplex.homologyMap (relAMor A B) N).hom

abbrev lfB (A B : Set (EuclideanSpace ℝ (Fin N))) : ↥(srcC A B) →ₗ[ℤ] LK N B :=
  (HomologicalComplex.homologyMap (relBMor A B) N).hom

abbrev lfL (A B : Set (EuclideanSpace ℝ (Fin N))) : ↥(srcC A B) →ₗ[ℤ] ↥(bipC A B) :=
  (HomologicalComplex.homologyMap (liftMor A B) N).hom

abbrev lfF (A B : Set (EuclideanSpace ℝ (Fin N))) : ↥(bipC A B) →ₗ[ℤ] LK N A :=
  (HomologicalComplex.homologyMap (fstMor A B) N).hom

abbrev lfS (A B : Set (EuclideanSpace ℝ (Fin N))) : ↥(bipC A B) →ₗ[ℤ] LK N B :=
  (HomologicalComplex.homologyMap (sndMor A B) N).hom

abbrev HMor (A B U : Set (EuclideanSpace ℝ (Fin N))) (e : Uᶜ = Aᶜ ∩ Bᶜ) :
    relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) Uᶜ ⟶
      relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) (Aᶜ ∩ Bᶜ) :=
  relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N))) Uᶜ (Aᶜ ∩ Bᶜ) (le_of_eq e)

abbrev lfH (A B U : Set (EuclideanSpace ℝ (Fin N))) (e : Uᶜ = Aᶜ ∩ Bᶜ) :
    LK N U →ₗ[ℤ] ↥(srcC A B) :=
  (HomologicalComplex.homologyMap (HMor A B U e) N).hom

/-! ## The product of the stage maps -/

/-- **The product of the stage maps** `LK N (⋃ i, K i) ⟶ ∏ i, LK N (K i)`, the map whose
components are the `lkMap`s of the inclusions `K i ⊆ ⋃ i, K i`. -/
def lkPi {ι : Type} (K : ι → Set (EuclideanSpace ℝ (Fin N))) :
    LK N (⋃ i, K i) →ₗ[ℤ] ((i : ι) → LK N (K i)) where
  toFun := fun a j => lkMap (Set.subset_iUnion K j) a
  map_add' := fun a b => by
    funext j
    simp only [Pi.add_apply, map_add]
  map_smul' := fun c a => by
    funext j
    simp only [Pi.smul_apply, RingHom.id_apply]
    exact (LinearMap.map_smul (lkMap (N := N) (Set.subset_iUnion K j)) c a).trans
      (int_smul_eq_zsmul ((LKC N (K j)).isModule) c _)

@[simp]
theorem lkPi_apply {ι : Type} (K : ι → Set (EuclideanSpace ℝ (Fin N)))
    (a : LK N (⋃ i, K i)) (j : ι) :
    lkPi (N := N) K a j = lkMap (Set.subset_iUnion K j) a := rfl

/-- `LK N ∅ = H_N(ℝ^N) = 0` for `N ≥ 1`. -/
theorem subsingleton_LK_empty :
    Subsingleton (LK N (∅ : Set (EuclideanSpace ℝ (Fin N)))) := by
  rw [show LK N (∅ : Set (EuclideanSpace ℝ (Fin N)))
      = ↥((relChains (TopCat.of (EuclideanSpace ℝ (Fin N)))
          (∅ : Set (EuclideanSpace ℝ (Fin N)))ᶜ).homology N) from rfl]
  rw [Set.compl_empty]
  exact ModuleCat.subsingleton_of_isZero
    (isZero_relChains_univ (TopCat.of (EuclideanSpace ℝ (Fin N))) N)

/-- If the index type is empty the product of the stage maps is bijective: the source is
`LK N ∅ = H_N(ℝ^N) = 0` and the target is a product over an empty type. -/
theorem lkPi_bijective_empty {ι : Type} [IsEmpty ι]
    (K : ι → Set (EuclideanSpace ℝ (Fin N))) :
    Function.Bijective (lkPi (N := N) K) := by
  haveI hsub : Subsingleton (LK N (⋃ i : ι, K i)) := by
    rw [Set.iUnion_of_empty K]
    exact subsingleton_LK_empty
  haveI : Subsingleton ((i : ι) → LK N (K i)) :=
    ⟨fun f g => funext fun i => isEmptyElim i⟩
  exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ y⟩⟩

/-! ## The two-set step -/

/-- **The two-set step.**  For compact disjoint `A, B ⊆ ℝ^N` and a set `U` with `U = A ∪ B`, the
pair of stage maps `LK N U → LK N A × LK N B` is a bijection.  This is the relative-homology
Mayer–Vietoris isomorphism of the cover of `ℝ^N` by the open complements of `A` and `B`. -/
theorem lk_pair_bijective {A B U : Set (EuclideanSpace ℝ (Fin N))}
    (hN : 1 ≤ N) (hAc : IsCompact A) (hBc : IsCompact B) (hdisj : Disjoint A B)
    (hU : U = A ∪ B) (hA : A ⊆ U) (hB : B ⊆ U) :
    Function.Bijective (LinearMap.prod (lkMap (N := N) hA) (lkMap (N := N) hB)) := by
  have hS : IsOpen (Aᶜ : Set (EuclideanSpace ℝ (Fin N))) := hAc.isClosed.isOpen_compl
  have hT : IsOpen (Bᶜ : Set (EuclideanSpace ℝ (Fin N))) := hBc.isClosed.isOpen_compl
  have hcov : (Aᶜ : Set (EuclideanSpace ℝ (Fin N))) ∪ Bᶜ = Set.univ := by
    rw [← Set.compl_inter, Set.disjoint_iff_inter_eq_empty.mp hdisj, Set.compl_empty]
  haveI hiso : IsIso (HomologicalComplex.homologyMap (liftMor A B) N) :=
    lk_twoSet_homologyMap_isIso hN (M := TopCat.of (EuclideanSpace ℝ (Fin N))) Aᶜ Bᶜ hS hT hcov
  -- the two inclusions occurring in the definition of `lkMap`
  have hA' : Uᶜ ⊆ Aᶜ := fun y hy hyA => hy (hA hyA)
  have hB' : Uᶜ ⊆ Bᶜ := fun y hy hyB => hy (hB hyB)
  have e' : Uᶜ = Aᶜ ∩ Bᶜ := by rw [hU]; exact Set.compl_union A B
  -- the identification of the two sources, componentwise
  have hrel1 : relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N))) Uᶜ Aᶜ hA'
      = HMor A B U e' ≫ relAMor A B := by
    rw [show HMor A B U e' ≫ relAMor A B
        = relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N))) Uᶜ Aᶜ
            ((le_of_eq e').trans Set.inter_subset_left) from
      relCokerMap_comp (le_of_eq e') Set.inter_subset_left]
  have hrel2 : relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N))) Uᶜ Bᶜ hB'
      = HMor A B U e' ≫ relBMor A B := by
    rw [show HMor A B U e' ≫ relBMor A B
        = relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N))) Uᶜ Bᶜ
            ((le_of_eq e').trans Set.inter_subset_right) from
      relCokerMap_comp (le_of_eq e') Set.inter_subset_right]
  have hmain1 : (HomologicalComplex.homologyMap (relCokerMap
        (TopCat.of (EuclideanSpace ℝ (Fin N))) Uᶜ Aᶜ hA') N)
      = (HomologicalComplex.homologyMap (HMor A B U e') N)
        ≫ (HomologicalComplex.homologyMap (relAMor A B) N) :=
    (congrArg (fun φ => HomologicalComplex.homologyMap φ N) hrel1).trans
      (HomologicalComplex.homologyMap_comp (HMor A B U e') (relAMor A B) N)
  have hmain2 : (HomologicalComplex.homologyMap (relCokerMap
        (TopCat.of (EuclideanSpace ℝ (Fin N))) Uᶜ Bᶜ hB') N)
      = (HomologicalComplex.homologyMap (HMor A B U e') N)
        ≫ (HomologicalComplex.homologyMap (relBMor A B) N) :=
    (congrArg (fun φ => HomologicalComplex.homologyMap φ N) hrel2).trans
      (HomologicalComplex.homologyMap_comp (HMor A B U e') (relBMor A B) N)
  have hlk1 : lkMap (N := N) hA = (lfA A B).comp (lfH A B U e') := by
    ext x
    show (HomologicalComplex.homologyMap (relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N)))
          Uᶜ Aᶜ hA') N).hom x = (lfA A B) ((lfH A B U e') x)
    exact congrFun (congrArg (fun (ψ : (relChains (TopCat.of (EuclideanSpace ℝ (Fin N)))
        Uᶜ).homology N ⟶ LKC N A) => (⇑ψ : LK N U → LK N A)) hmain1) x
  have hlk2 : lkMap (N := N) hB = (lfB A B).comp (lfH A B U e') := by
    ext x
    show (HomologicalComplex.homologyMap (relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N)))
          Uᶜ Bᶜ hB') N).hom x = (lfB A B) ((lfH A B U e') x)
    exact congrFun (congrArg (fun (ψ : (relChains (TopCat.of (EuclideanSpace ℝ (Fin N)))
        Uᶜ).homology N ⟶ LKC N B) => (⇑ψ : LK N U → LK N B)) hmain2) x
  -- the two components of the pairing
  have hm1 : (HomologicalComplex.homologyMap (liftMor A B) N)
      ≫ (HomologicalComplex.homologyMap (fstMor A B) N)
      = HomologicalComplex.homologyMap (relAMor A B) N :=
    (HomologicalComplex.homologyMap_comp (liftMor A B) (fstMor A B) N).symm.trans
      (congrArg (fun φ => HomologicalComplex.homologyMap φ N)
        (biprod.lift_fst (relAMor A B) (relBMor A B)))
  have hm2 : (HomologicalComplex.homologyMap (liftMor A B) N)
      ≫ (HomologicalComplex.homologyMap (sndMor A B) N)
      = HomologicalComplex.homologyMap (relBMor A B) N :=
    (HomologicalComplex.homologyMap_comp (liftMor A B) (sndMor A B) N).symm.trans
      (congrArg (fun φ => HomologicalComplex.homologyMap φ N)
        (biprod.lift_snd (relAMor A B) (relBMor A B)))
  have h1 : lfA A B = (lfF A B).comp (lfL A B) := by
    ext x
    show (HomologicalComplex.homologyMap (relAMor A B) N).hom x
      = (HomologicalComplex.homologyMap (fstMor A B) N).hom
          ((HomologicalComplex.homologyMap (liftMor A B) N).hom x)
    exact (congrFun (congrArg (fun (ψ : srcC A B ⟶ LKC N A) => (⇑ψ : ↥(srcC A B) → LK N A))
      hm1) x).symm
  have h2 : lfB A B = (lfS A B).comp (lfL A B) := by
    ext x
    show (HomologicalComplex.homologyMap (relBMor A B) N).hom x
      = (HomologicalComplex.homologyMap (sndMor A B) N).hom
          ((HomologicalComplex.homologyMap (liftMor A B) N).hom x)
    exact (congrFun (congrArg (fun (ψ : srcC A B ⟶ LKC N B) => (⇑ψ : ↥(srcC A B) → LK N B))
      hm2) x).symm
  -- the pairing of the two components is bijective
  have hpq : Function.Bijective (fun x : ↥(srcC A B) => (lfA A B x, lfB A B x)) := by
    have hfun : (fun x : ↥(srcC A B) => (lfA A B x, lfB A B x))
        = fun x => (LinearMap.prod (lfF A B) (lfS A B)) (lfL A B x) := by
      funext x
      exact Prod.ext (congrArg (fun φ => φ x) h1) (congrArg (fun φ => φ x) h2)
    rw [hfun]
    exact (homology_biprod_fst_snd_bijective
        (relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) Aᶜ)
        (relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) Bᶜ) N).comp
      (ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap (liftMor A B) N))
  haveI hisoT : IsIso (HomologicalComplex.homologyMap (HMor A B U e') N) := by
    haveI : IsIso (HMor A B U e') := isIso_relCokerMap_of_eq e'
    exact Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ)
      (ComplexShape.down ℕ) N) (HMor A B U e')
  -- assemble
  have hprod : (fun x : LK N U => (lkMap (N := N) hA x, lkMap (N := N) hB x))
      = fun x => (lfA A B (lfH A B U e' x), lfB A B (lfH A B U e' x)) := by
    funext x
    exact Prod.ext (congrArg (fun φ => φ x) hlk1) (congrArg (fun φ => φ x) hlk2)
  show Function.Bijective (fun x : LK N U => (lkMap (N := N) hA x, lkMap (N := N) hB x))
  rw [hprod]
  exact hpq.comp (ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap
    (HMor A B U e') N))

/-! ## Splitting off one index -/

/-- **The induction step.**  Given the product of the stage maps for the subfamily indexed by
`{i // i ≠ j₀}`, the product for the whole family is bijective as well: this is the two-set step
applied to the pair `(K j₀, ⋃_{i ≠ j₀} K i)` together with the reindexing
`Π i, LK N (K i) ≃ LK N (K j₀) × Π_{i ≠ j₀}, LK N (K i)` (`Equiv.piSplitAt`). -/
theorem lkPi_bijective_step {ι : Type} [Fintype ι] (j₀ : ι)
    (K : ι → Set (EuclideanSpace ℝ (Fin N))) (hN : 1 ≤ N)
    (hKc : ∀ i, IsCompact (K i)) (hdisj : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (hIH : Function.Bijective (lkPi (N := N) (fun i : {i : ι // i ≠ j₀} => K i.1))) :
    Function.Bijective (lkPi (N := N) K) := by
  classical
  have hU : (⋃ i : ι, K i) = K j₀ ∪ ⋃ i : {i : ι // i ≠ j₀}, K i.1 := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      by_cases h : i = j₀
      · exact Or.inl (h ▸ hi)
      · exact Or.inr ⟨⟨i, h⟩, hi⟩
    · rintro (h | ⟨i, hi⟩)
      · exact ⟨j₀, h⟩
      · exact ⟨i.1, hi⟩
  have hBc : IsCompact (⋃ i : {i : ι // i ≠ j₀}, K i.1) :=
    isCompact_iUnion (fun i => hKc i.1)
  have hdisjAB : Disjoint (K j₀) (⋃ i : {i : ι // i ≠ j₀}, K i.1) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_empty_iff_false, iff_false, not_and]
    rintro hx ⟨i, hi⟩
    have hmem : x ∈ K j₀ ∩ K i.1 := ⟨hx, hi⟩
    rw [Set.disjoint_iff_inter_eq_empty.mp (hdisj j₀ i.1 (Ne.symm i.2))] at hmem
    exact hmem
  have hBsub : (⋃ i : {i : ι // i ≠ j₀}, K i.1) ⊆ (⋃ i : ι, K i) := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i.1, hi⟩
  have hpair := lk_pair_bijective (N := N) hN (hKc j₀) hBc hdisjAB hU
    (Set.subset_iUnion K j₀) hBsub
  -- the bijectivity of the reindexed pairing
  have hstep : Function.Bijective (fun p : LK N (K j₀) × LK N (⋃ i : {i : ι // i ≠ j₀}, K i.1) =>
      (p.1, lkPi (N := N) (fun i : {i : ι // i ≠ j₀} => K i.1) p.2)) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h
      have h1 : a₁ = b₁ := by simpa using congrArg Prod.fst h
      have h2 : a₂ = b₂ := hIH.injective (by simpa using congrArg Prod.snd h)
      exact Prod.ext h1 h2
    · rintro ⟨b₁, b₂⟩
      obtain ⟨a₂, ha₂⟩ := hIH.surjective b₂
      exact ⟨(b₁, a₂), by simp [ha₂]⟩
  have hΘ : Function.Bijective (fun a : LK N (⋃ i : ι, K i) =>
      (lkMap (N := N) (Set.subset_iUnion K j₀) a,
        lkPi (N := N) (fun i : {i : ι // i ≠ j₀} => K i.1)
          (lkMap (N := N) hBsub a))) :=
    hstep.comp hpair
  -- the reindexing identifies the product of the stage maps with the reindexed pairing
  have hcomp : ∀ a : LK N (⋃ i : ι, K i),
      Equiv.piSplitAt j₀ (fun i => LK N (K i)) (lkPi (N := N) K a)
        = (lkMap (N := N) (Set.subset_iUnion K j₀) a,
            lkPi (N := N) (fun i : {i : ι // i ≠ j₀} => K i.1)
              (lkMap (N := N) hBsub a)) := by
    intro a
    apply Prod.ext
    · show (Equiv.piSplitAt j₀ (fun i => LK N (K i)) (lkPi (N := N) K a)).1
          = lkMap (N := N) (Set.subset_iUnion K j₀) a
      rw [Equiv.piSplitAt_apply]
      rfl
    · rw [Equiv.piSplitAt_apply]
      funext i
      show lkPi (N := N) K a i.1
        = lkPi (N := N) (fun i : {i : ι // i ≠ j₀} => K i.1) (lkMap (N := N) hBsub a) i
      rw [lkPi_apply, lkPi_apply]
      show lkMap (N := N) (Set.subset_iUnion K i.1) a
        = ((lkMap (N := N) (Set.subset_iUnion (fun i : {i : ι // i ≠ j₀} => K i.1) i)).comp
            (lkMap (N := N) hBsub)) a
      rw [lkMap_comp]
  have hb2 : Function.Bijective (fun a : LK N (⋃ i : ι, K i) =>
      Equiv.piSplitAt j₀ (fun i => LK N (K i)) (lkPi (N := N) K a)) := by
    rw [show (fun a : LK N (⋃ i : ι, K i) =>
          Equiv.piSplitAt j₀ (fun i => LK N (K i)) (lkPi (N := N) K a))
        = fun a => (lkMap (N := N) (Set.subset_iUnion K j₀) a,
            lkPi (N := N) (fun i : {i : ι // i ≠ j₀} => K i.1)
              (lkMap (N := N) hBsub a)) from funext hcomp]
    exact hΘ
  obtain ⟨hinj, hsurj⟩ := hb2
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · exact hinj (congrArg (Equiv.piSplitAt j₀ (fun i => LK N (K i))) hab)
  · obtain ⟨a, ha⟩ := hsurj (Equiv.piSplitAt j₀ (fun i => LK N (K i)) y)
    exact ⟨a, (Equiv.piSplitAt j₀ (fun i => LK N (K i))).injective ha⟩

/-! ## The target statement -/

theorem LK_decomposition {N : ℕ} (hN : 1 ≤ N) {ι : Type} [Fintype ι]
    (K : ι → Set (EuclideanSpace ℝ (Fin N)))
    (hKc : ∀ i, IsCompact (K i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (K i) (K j)) :
    ∃ e : Work.Cohomology.LK N (⋃ i, K i) ≃ₗ[ℤ] ((i : ι) → Work.Cohomology.LK N (K i)),
      ∀ (j : ι) (a : Work.Cohomology.LK N (⋃ i, K i)),
        e a j = Work.Cohomology.lkMap (N := N) (Set.subset_iUnion K j) a := by
  have main : ∀ (ι : Type) [Fintype ι], ∀ K : ι → Set (EuclideanSpace ℝ (Fin N)),
      (∀ i, IsCompact (K i)) → (∀ i j, i ≠ j → Disjoint (K i) (K j)) →
      Function.Bijective (lkPi (N := N) K) := by
    classical
    intro ι _
    refine Fintype.induction_subsingleton_or_nontrivial ι ?_ ?_
    · intro ι _ _ K hKc hdisj
      by_cases hne : Nonempty ι
      · obtain ⟨j₀⟩ := hne
        refine lkPi_bijective_step (N := N) j₀ K hN hKc hdisj ?_
        haveI : IsEmpty {i : ι // i ≠ j₀} :=
          ⟨fun i => i.2 (Subsingleton.elim i.1 j₀)⟩
        exact lkPi_bijective_empty _
      · haveI : IsEmpty ι := not_nonempty_iff.mp hne
        exact lkPi_bijective_empty K
    · intro ι _ _ ih K hKc hdisj
      obtain ⟨j₀⟩ : Nonempty ι := by
        obtain ⟨x, -, -⟩ := (inferInstance : Nontrivial ι).exists_pair_ne
        exact ⟨x⟩
      refine lkPi_bijective_step (N := N) j₀ K hN hKc hdisj ?_
      refine ih {i : ι // i ≠ j₀} (Fintype.card_subtype_lt (x := j₀) (fun h => h rfl))
        (fun i : {i : ι // i ≠ j₀} => K i.1) (fun i => hKc i.1) ?_
      intro i j hij
      exact hdisj i.1 j.1 (fun h => hij (Subtype.ext h))
  exact ⟨LinearEquiv.ofBijective (lkPi (N := N) K) (main ι K hKc hdisj), fun j a => by
    rw [LinearEquiv.ofBijective_apply]
    rfl⟩

end

end Work.Cohomology
