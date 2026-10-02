import Mathlib
import Submission.Work.Serre.relCohMV_les_rat
import Submission.Work.Serre.MVCohRatDefs
import Submission.Work.StemsB.AToolsR
import Submission.Work.StemsB.Rat.H0EvalRat
import Submission.Work.RatHurewicz.isZero_relCoh_of_isEmpty

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

/-!
# Gluing the degree-zero bijectivity of the cup map over an open cover

For a space `X`, a set `A ⊆ X`, an open cover `X = U ∪ V` and a class
`U₀ ∈ H^{n₀}(X,A;ℚ)`, suppose that the "cup with `U₀`" map

`x ↦ x ⌣ U₀ : H^{m}(·;ℚ) ⟶ H^{m+n₀}(·, ·∩A;ℚ)`

is bijective in degree `m = 0` over each of the three pieces `U`, `V`, `U ∩ V`, and that the pieces
have vanishing relative cohomology in degree `n₀ - 1`.  Then it is bijective in degree `0` over `X`
as well:

`Work.Serre.bijective_mixedCup_of_openCover_zero`.

The proof is the degree-zero Mayer–Vietoris argument, i.e. the two sheaf-theoretic properties of
`H⁰` together with the (relative) Mayer–Vietoris long exact sequence:

* **separatedness of `H⁰`** (`h0_restrict_eq_zero_of_cover`): a class of `H⁰(X;ℚ)` whose
  restrictions to `U` and to `V` vanish is zero, because a rational `0`-class is determined by its
  values at the points of `X` (`Work.StemsB.Rat.h0EvQ`) and `X = U ∪ V`;
* **gluing of `H⁰`** (`exists_glue_coh_zero`): classes of `H⁰(U;ℚ)` and `H⁰(V;ℚ)` agreeing on
  `U ∩ V` come from a class of `H⁰(X;ℚ)`.  This is the *middle* exactness
  (`Work.Serre.exact_mvF_mvG`) of the rational relative Mayer–Vietoris sequence of the pair
  `(X,∅)`, after identifying `H^n(X,∅;ℚ) ≅ H^n(X;ℚ)` for empty second member
  (`isIso_relToAbs_of_isEmpty`, built here from `isIso_relIncl_of_relKern_eq_top`);
* **injectivity of `mvF` in degree `n₀`** (`ker_mvF_eq_bot`): from the exactness
  `Work.Serre.exact_mvDelta_mvF` and the vanishing of the overlap term in degree `n₀ - 1`, the map
  `H^{n₀}(X,A;ℚ) → H^{n₀}(U,U∩A;ℚ) ⊞ H^{n₀}(V,V∩A;ℚ)` is injective — this is what turns the
  two local bijectivities into a global one;
* the naturality of the mixed cup product (`Work.StemsB.mixedCupC_pairNaturalR`) as the bridge
  between the local and global cup maps.

The degenerate case `n₀ = 0` is handled separately: then `H^0(U, U∩A) = 0` by hypothesis, so `U`
(and symmetrically `V`, hence `X`) is empty and both sides of the cup map are trivial.

-/

namespace Work.Serre

noncomputable section

/-! ## The (rational) cohomology of an empty space vanishes -/

/-- The singular cochain complex of an empty space is a subsingleton in every degree. -/
theorem subsingleton_singularCochainComplex_of_isEmpty {Y : Type} [TopologicalSpace Y]
    [IsEmpty Y] (n : ℕ) :
    Subsingleton ((Work.Cohomology.singularCochainComplex ℚ (TopCat.of Y)).X n) := by
  have hchain : IsZero ((Work.Cohomology.singularChains ℚ (TopCat.of Y)).X n) :=
    Work.RatHurewicz.isZero_singularChains_of_isEmpty' (TopCat.of Y) n
  haveI : Subsingleton ((Work.Cohomology.singularChains ℚ (TopCat.of Y)).X n) :=
    ModuleCat.subsingleton_of_isZero hchain
  haveI : Subsingleton ((Work.Cohomology.singularChains ℚ (TopCat.of Y)).X n →ₗ[ℚ] ℚ) :=
    ⟨fun f g => by ext x; rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  exact ‹Subsingleton ((Work.Cohomology.singularChains ℚ (TopCat.of Y)).X n →ₗ[ℚ] ℚ)›

/-- **An empty space has vanishing rational absolute cohomology.** -/
theorem isZero_coh_of_isEmpty_space {Y : Type} [TopologicalSpace Y] [IsEmpty Y] (n : ℕ) :
    IsZero (Work.Thom.Coh ℚ n Y) := by
  haveI : Subsingleton ((Work.Cohomology.singularCochainComplex ℚ (TopCat.of Y)).X n) :=
    subsingleton_singularCochainComplex_of_isEmpty n
  exact Work.RatHurewicz.isZero_homology_of_isZero_X' n (ModuleCat.isZero_of_subsingleton _)

/-- **An empty space has vanishing rational relative cohomology.** -/
theorem isZero_relCoh_of_isEmpty_space {Y : Type} [TopologicalSpace Y] [IsEmpty Y]
    (B : Set Y) (n : ℕ) : IsZero (Work.Thom.RelCoh ℚ n Y B) := by
  haveI : Subsingleton ((Work.Cohomology.singularCochainComplex ℚ (TopCat.of Y)).X n) :=
    subsingleton_singularCochainComplex_of_isEmpty n
  haveI : Subsingleton (Work.Cohomology.relKern ℚ (TopCat.of Y) B n) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim a.1 b.1)⟩
  haveI : Subsingleton ↑((Work.Cohomology.relComplex ℚ (TopCat.of Y) B).X n) :=
    ‹Subsingleton (Work.Cohomology.relKern ℚ (TopCat.of Y) B n)›
  exact Work.RatHurewicz.isZero_homology_of_isZero_X' n (ModuleCat.isZero_of_subsingleton _)

/-- The restriction of cochains to an empty piece is the zero map. -/
theorem restr_f_eq_zero_of_isEmpty {X : Type} [TopologicalSpace X] {S : Set X}
    (hS : IsEmpty ↥S) (n : ℕ) :
    (Work.Cohomology.restr ℚ (TopCat.of X) S).f n = 0 := by
  haveI := hS
  haveI : Subsingleton ((Work.Cohomology.singularCochainComplex ℚ (TopCat.of ↥S)).X n) :=
    subsingleton_singularCochainComplex_of_isEmpty n
  exact IsZero.eq_zero_of_tgt (ModuleCat.isZero_of_subsingleton _) _

/-- The relative `n`-cochains of a pair whose second set is empty are everything. -/
theorem relKern_eq_top_of_isEmpty {X : Type} [TopologicalSpace X] {S : Set X}
    (hS : IsEmpty ↥S) (n : ℕ) : Work.Cohomology.relKern ℚ (TopCat.of X) S n = ⊤ := by
  rw [Work.Cohomology.relKern, restr_f_eq_zero_of_isEmpty hS n, ModuleCat.hom_zero,
    LinearMap.ker_zero]

/-- **The forgetful map `H^n(X,∅) → H^n(X)` is an isomorphism.** -/
theorem isIso_relToAbs_of_isEmpty {X : Type} [TopologicalSpace X] (S : Set X)
    (hS : IsEmpty ↥S) (n : ℕ) : IsIso (Work.Thom.relToAbs ℚ S n) := by
  haveI : IsIso (Work.Cohomology.relIncl ℚ (TopCat.of X) S) :=
    Work.Cohomology.isIso_relIncl_of_relKern_eq_top ℚ (TopCat.of X) S
      (fun n => relKern_eq_top_of_isEmpty hS n)
  exact Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℚ)
    (ComplexShape.up ℕ) n) (Work.Cohomology.relIncl ℚ (TopCat.of X) S)

/-- The subtype of an empty set, cut out by `∈ ∅`. -/
theorem isEmpty_subtype_mem_empty {X : Type} {S : Set X} :
    IsEmpty (Subtype fun x : ↥S => (x : X) ∈ (∅ : Set X)) :=
  ⟨fun x => x.2⟩

/-- The whole empty set, as a subtype. -/
theorem isEmpty_empty_set (X : Type) : IsEmpty ↥(∅ : Set X) :=
  ⟨fun x => x.2⟩

/-! ## `H⁰` of an empty space, and the evaluation criterion -/

/-- **A space whose `H⁰` vanishes is empty.** -/
theorem isEmpty_of_subsingleton_coh_zero {Y : Type} [TopologicalSpace Y]
    (h : Subsingleton (Work.Thom.Coh ℚ 0 Y)) : IsEmpty Y := by
  haveI := h
  refine ⟨fun y => ?_⟩
  set s : (TopCat.toSSet.obj (TopCat.of Y)).obj (Opposite.op (SimplexCategory.mk 0)) :=
    TopCat.toSSetObj₀Equiv.symm y with hs
  have h1 : Work.StemsB.Rat.h0EvQ (TopCat.toSSet.obj (TopCat.of Y)) s
      (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of Y))) = 1 :=
    Work.StemsB.Rat.h0EvQ_oneH s
  have h2 : Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of Y)) = 0 :=
    @Subsingleton.elim _ h _ _
  rw [h2, map_zero] at h1
  exact zero_ne_one h1

/-- If a `0`-simplex of `X` is the image of a point of the subspace `↥U`, it is the image of a
`0`-simplex of `↥U`. -/
theorem exists_zeroSimplex_preimage {X : Type} [TopologicalSpace X] {U : Set X}
    (s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 0)))
    (hU : (TopCat.toSSetObj₀Equiv s : X) ∈ U) :
    ∃ s' : (TopCat.toSSet.obj (TopCat.of ↥U)).obj (Opposite.op (SimplexCategory.mk 0)),
      (TopCat.toSSet.map (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X)))).app
        (Opposite.op (SimplexCategory.mk 0)) s' = s := by
  refine ⟨TopCat.toSSetObj₀Equiv.symm ⟨(TopCat.toSSetObj₀Equiv s : X), hU⟩, ?_⟩
  apply TopCat.toSSetObj₀Equiv.injective
  rw [Work.StemsB.Rat.toSSetObj₀Equiv_mapQ, Equiv.apply_symm_apply]
  rfl

/-- **Separation of degree-zero rational cohomology over a cover**: a `0`-class of `X` whose
restrictions to `U` and to `V` vanish is zero, whenever `X = U ∪ V`. -/
theorem h0_restrict_eq_zero_of_cover {X : Type} [TopologicalSpace X] {U V : Set X}
    (hcov : U ∪ V = Set.univ) (x : Work.Thom.Coh ℚ 0 X)
    (hU : (Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X)) ℚ 0).hom x = 0)
    (hV : (Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X)) ℚ 0).hom x = 0) :
    x = 0 := by
  refine Work.StemsB.Rat.h0EvQ_eq_zero x (fun s => ?_)
  have hs : (TopCat.toSSetObj₀Equiv s : X) ∈ U ∪ V := by rw [hcov]; exact trivial
  rcases hs with hsU | hsV
  · obtain ⟨s', hs'⟩ := exists_zeroSimplex_preimage s hsU
    have h1 : Work.StemsB.Rat.h0EvQ (TopCat.toSSet.obj (TopCat.of X)) s x
        = Work.StemsB.Rat.h0EvQ (TopCat.toSSet.obj (TopCat.of ↥U)) s'
            ((Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X)) ℚ 0).hom x) := by
      rw [← hs', ← Work.StemsB.Rat.h0EvQ_CohMap
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X)) s' x]
    rw [h1, hU, map_zero]
  · obtain ⟨s', hs'⟩ := exists_zeroSimplex_preimage s hsV
    have h1 : Work.StemsB.Rat.h0EvQ (TopCat.toSSet.obj (TopCat.of X)) s x
        = Work.StemsB.Rat.h0EvQ (TopCat.toSSet.obj (TopCat.of ↥V)) s'
            ((Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X)) ℚ 0).hom x) := by
      rw [← hs', ← Work.StemsB.Rat.h0EvQ_CohMap
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X)) s' x]
    rw [h1, hV, map_zero]


/-! ## Gluing of degree-zero rational classes over an open cover -/

/-- The underlying linear map of a composite. -/
theorem comp_hom_apply {M N P : ModuleCat ℚ} (f : M ⟶ N) (g : N ⟶ P) (x : M) :
    (f ≫ g).hom x = g.hom (f.hom x) := by
  rw [ModuleCat.hom_comp]; rfl

/-- **`e.hom` after `e.inv`.** -/
theorem iso_hom_inv_apply {M N : ModuleCat ℚ} (e : M ≅ N) (x : N) :
    e.hom.hom (e.inv.hom x) = x := by
  have h := congrArg (fun (f : N ⟶ N) => f.hom x) (Iso.inv_hom_id e)
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
    LinearMap.id_apply] using h

/-- **Gluing of degree-zero rational classes over an open cover.**  A `0`-class of `U` and a
`0`-class of `V` which agree on `U ∩ V` come from a `0`-class of the union. -/
theorem exists_glue_coh_zero {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (a : Work.Thom.Coh ℚ 0 ↥U) (b : Work.Thom.Coh ℚ 0 ↥V)
    (h : (Work.Thom.CohMap (⟨fun x : ↥(U ∩ V) => ⟨x.1, x.2.1⟩, by continuity⟩ :
            C(↥(U ∩ V), ↥U)) ℚ 0).hom a
       = (Work.Thom.CohMap (⟨fun x : ↥(U ∩ V) => ⟨x.1, x.2.2⟩, by continuity⟩ :
            C(↥(U ∩ V), ↥V)) ℚ 0).hom b) :
    ∃ x : Work.Thom.Coh ℚ 0 X,
      (Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X)) ℚ 0).hom x = a ∧
      (Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X)) ℚ 0).hom x = b := by
  classical
  let SU : Set ↥U := fun x => (x : X) ∈ (∅ : Set X)
  let SV : Set ↥V := fun x => (x : X) ∈ (∅ : Set X)
  let SUV : Set ↥(U ∩ V) := fun x => (x : X) ∈ (∅ : Set X)
  have hEmX : IsEmpty ↥(∅ : Set X) := isEmpty_empty_set X
  have hEmU : IsEmpty ↥SU := isEmpty_subtype_mem_empty
  have hEmV : IsEmpty ↥SV := isEmpty_subtype_mem_empty
  have hEmUV : IsEmpty ↥SUV := isEmpty_subtype_mem_empty
  let A : ModuleCat ℚ := Work.Serre.mvCohU (TopCat.of X) (∅ : Set X) U 0
  let B : ModuleCat ℚ := Work.Serre.mvCohV (TopCat.of X) (∅ : Set X) V 0
  let C : ModuleCat ℚ := Work.Serre.mvCohUV (TopCat.of X) (∅ : Set X) U V 0
  let rU : Work.Thom.Coh ℚ 0 X ⟶ Work.Thom.Coh ℚ 0 ↥U :=
    Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X)) ℚ 0
  let rV : Work.Thom.Coh ℚ 0 X ⟶ Work.Thom.Coh ℚ 0 ↥V :=
    Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X)) ℚ 0
  let rUVU : Work.Thom.Coh ℚ 0 ↥U ⟶ Work.Thom.Coh ℚ 0 ↥(U ∩ V) :=
    Work.Thom.CohMap (⟨fun x : ↥(U ∩ V) => ⟨x.1, x.2.1⟩, by continuity⟩ : C(↥(U ∩ V), ↥U)) ℚ 0
  let rUVV : Work.Thom.Coh ℚ 0 ↥V ⟶ Work.Thom.Coh ℚ 0 ↥(U ∩ V) :=
    Work.Thom.CohMap (⟨fun x : ↥(U ∩ V) => ⟨x.1, x.2.2⟩, by continuity⟩ : C(↥(U ∩ V), ↥V)) ℚ 0
  let eX : Work.Thom.RelCoh ℚ 0 X (∅ : Set X) ≅ Work.Thom.Coh ℚ 0 X :=
    @asIso (ModuleCat ℚ) _ _ _ (Work.Thom.relToAbs ℚ (∅ : Set X) 0)
      (isIso_relToAbs_of_isEmpty _ hEmX 0)
  let eU : A ≅ Work.Thom.Coh ℚ 0 ↥U :=
    @asIso (ModuleCat ℚ) _ _ _ (Work.Thom.relToAbs ℚ SU 0)
      (isIso_relToAbs_of_isEmpty _ hEmU 0)
  let eV : B ≅ Work.Thom.Coh ℚ 0 ↥V :=
    @asIso (ModuleCat ℚ) _ _ _ (Work.Thom.relToAbs ℚ SV 0)
      (isIso_relToAbs_of_isEmpty _ hEmV 0)
  let eUV : C ≅ Work.Thom.Coh ℚ 0 ↥(U ∩ V) :=
    @asIso (ModuleCat ℚ) _ _ _ (Work.Thom.relToAbs ℚ SUV 0)
      (isIso_relToAbs_of_isEmpty _ hEmUV 0)
  -- compatibility of the restrictions with the comparison isomorphisms
  have cU : Work.Serre.mvRestrU (TopCat.of X) (∅ : Set X) U 0 ≫ eU.hom = eX.hom ≫ rU :=
    Work.Thom.relCohMap_relToAbs _ _ _ _ ℚ 0
  have cV : Work.Serre.mvRestrV (TopCat.of X) (∅ : Set X) V 0 ≫ eV.hom = eX.hom ≫ rV :=
    Work.Thom.relCohMap_relToAbs _ _ _ _ ℚ 0
  have cUVU : Work.Serre.mvRestrUVU (TopCat.of X) (∅ : Set X) U V 0 ≫ eUV.hom
      = eU.hom ≫ rUVU :=
    Work.Thom.relCohMap_relToAbs _ _ _ _ ℚ 0
  have cUVV : Work.Serre.mvRestrUVV (TopCat.of X) (∅ : Set X) U V 0 ≫ eUV.hom
      = eV.hom ≫ rUVV :=
    Work.Thom.relCohMap_relToAbs _ _ _ _ ℚ 0
  have cU' (y : Work.Thom.RelCoh ℚ 0 X (∅ : Set X)) :
      eU.hom.hom ((Work.Serre.mvRestrU (TopCat.of X) (∅ : Set X) U 0).hom y) = rU.hom (eX.hom.hom y) := by
    have hh := congrArg (fun (φ : Work.Thom.RelCoh ℚ 0 X (∅ : Set X) ⟶ Work.Thom.Coh ℚ 0 ↥U) =>
      φ.hom) cU
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hh
    exact LinearMap.congr_fun hh y
  have cV' (y : Work.Thom.RelCoh ℚ 0 X (∅ : Set X)) :
      eV.hom.hom ((Work.Serre.mvRestrV (TopCat.of X) (∅ : Set X) V 0).hom y) = rV.hom (eX.hom.hom y) := by
    have hh := congrArg (fun (φ : Work.Thom.RelCoh ℚ 0 X (∅ : Set X) ⟶ Work.Thom.Coh ℚ 0 ↥V) =>
      φ.hom) cV
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hh
    exact LinearMap.congr_fun hh y
  have cUVU' (y : A) :
      eUV.hom.hom ((Work.Serre.mvRestrUVU (TopCat.of X) (∅ : Set X) U V 0).hom y)
        = rUVU.hom (eU.hom.hom y) := by
    have hh := congrArg (fun (φ : A ⟶ Work.Thom.Coh ℚ 0 ↥(U ∩ V)) => φ.hom) cUVU
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hh
    exact LinearMap.congr_fun hh y
  have cUVV' (y : B) :
      eUV.hom.hom ((Work.Serre.mvRestrUVV (TopCat.of X) (∅ : Set X) U V 0).hom y)
        = rUVV.hom (eV.hom.hom y) := by
    have hh := congrArg (fun (φ : B ⟶ Work.Thom.Coh ℚ 0 ↥(U ∩ V)) => φ.hom) cUVV
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hh
    exact LinearMap.congr_fun hh y
  -- the element of the biproduct
  set a' : A := eU.inv.hom a with ha'
  set b' : B := eV.inv.hom b with hb'
  have hUa : eU.hom.hom a' = a := iso_hom_inv_apply eU a
  have hVb : eV.hom.hom b' = b := iso_hom_inv_apply eV b
  set w : (A ⊞ B : ModuleCat ℚ) := (biprod.inl : A ⟶ (A ⊞ B : ModuleCat ℚ)).hom a' + (biprod.inr : B ⟶ (A ⊞ B : ModuleCat ℚ)).hom b' with hw
  -- `w` is killed by `mvG`
  have hmvG : Work.Serre.mvG (TopCat.of X) (∅ : Set X) U V 0
      = biprod.desc (Work.Serre.mvRestrUVU (TopCat.of X) (∅ : Set X) U V 0)
          (-(Work.Serre.mvRestrUVV (TopCat.of X) (∅ : Set X) U V 0)) :=
    Work.Serre.mvG_eq_desc _ _ _ _ 0
  have hinl : (Work.Serre.mvG (TopCat.of X) (∅ : Set X) U V 0).hom
        ((biprod.inl : A ⟶ (A ⊞ B : ModuleCat ℚ)).hom a')
      = (Work.Serre.mvRestrUVU (TopCat.of X) (∅ : Set X) U V 0).hom a' := by
    have h1 : (biprod.inl : A ⟶ (A ⊞ B : ModuleCat ℚ)) ≫ Work.Serre.mvG (TopCat.of X) (∅ : Set X) U V 0
        = Work.Serre.mvRestrUVU (TopCat.of X) (∅ : Set X) U V 0 := by
      rw [hmvG, biprod.inl_desc]
    have h2 := congrArg (fun (φ : A ⟶ C) => φ.hom a') h1
    rw [ModuleCat.hom_comp] at h2
    exact h2
  have hinr : (Work.Serre.mvG (TopCat.of X) (∅ : Set X) U V 0).hom
        ((biprod.inr : B ⟶ (A ⊞ B : ModuleCat ℚ)).hom b')
      = -((Work.Serre.mvRestrUVV (TopCat.of X) (∅ : Set X) U V 0).hom b') := by
    have h1 : (biprod.inr : B ⟶ (A ⊞ B : ModuleCat ℚ)) ≫ Work.Serre.mvG (TopCat.of X) (∅ : Set X) U V 0
        = -(Work.Serre.mvRestrUVV (TopCat.of X) (∅ : Set X) U V 0) := by
      rw [hmvG, biprod.inr_desc]
    have h2 := congrArg (fun (φ : B ⟶ C) => φ.hom b') h1
    rw [ModuleCat.hom_comp, ModuleCat.hom_neg] at h2
    exact h2
  have hmG : (Work.Serre.mvG (TopCat.of X) (∅ : Set X) U V 0).hom w = 0 := by
    rw [hw, map_add, hinl, hinr]
    apply (injective_hom_of_iso eUV)
    rw [map_add, map_neg, map_zero, cUVU' a', cUVV' b', hUa, hVb, ← h, add_neg_cancel]
  -- hence `w` is in the range of `mvF`
  have hw_range : w ∈ LinearMap.range (Work.Serre.mvF (TopCat.of X) (∅ : Set X) U V 0).hom := by
    rw [Work.Serre.exact_mvF_mvG (TopCat.of X) (∅ : Set X) U V hU hV hcov 0]
    exact hmG
  obtain ⟨y, hy⟩ := hw_range
  -- components of `y`
  have hfst : (Work.Serre.mvRestrU (TopCat.of X) (∅ : Set X) U 0).hom y = a' := by
    have h1 : Work.Serre.mvF (TopCat.of X) (∅ : Set X) U V 0 ≫ biprod.fst
        = Work.Serre.mvRestrU (TopCat.of X) (∅ : Set X) U 0 := biprod.lift_fst _ _
    have h2 := congrArg (fun (φ : Work.Thom.RelCoh ℚ 0 X (∅ : Set X) ⟶ A) => φ.hom y) h1
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, hy] at h2
    have h3 : (biprod.fst : (A ⊞ B : ModuleCat ℚ) ⟶ A).hom w = a' := by
      rw [hw, map_add]
      have hA : (biprod.fst : (A ⊞ B : ModuleCat ℚ) ⟶ A).hom ((biprod.inl : A ⟶ (A ⊞ B : ModuleCat ℚ)).hom a') = a' := by
        have h := congrArg (fun (φ : A ⟶ A) => φ.hom a') (biprod.inl_fst (X := A) (Y := B))
        rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
        exact h
      have hB : (biprod.fst : (A ⊞ B : ModuleCat ℚ) ⟶ A).hom ((biprod.inr : B ⟶ (A ⊞ B : ModuleCat ℚ)).hom b') = 0 := by
        have h := congrArg (fun (φ : B ⟶ A) => φ.hom b') (biprod.inr_fst (X := A) (Y := B))
        rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
        exact h
      rw [hA, hB, add_zero]
    rw [h3] at h2
    exact h2.symm
  have hsnd : (Work.Serre.mvRestrV (TopCat.of X) (∅ : Set X) V 0).hom y = b' := by
    have h1 : Work.Serre.mvF (TopCat.of X) (∅ : Set X) U V 0 ≫ biprod.snd
        = Work.Serre.mvRestrV (TopCat.of X) (∅ : Set X) V 0 := biprod.lift_snd _ _
    have h2 := congrArg (fun (φ : Work.Thom.RelCoh ℚ 0 X (∅ : Set X) ⟶ B) => φ.hom y) h1
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, hy] at h2
    have h3 : (biprod.snd : (A ⊞ B : ModuleCat ℚ) ⟶ B).hom w = b' := by
      rw [hw, map_add]
      have hA : (biprod.snd : (A ⊞ B : ModuleCat ℚ) ⟶ B).hom ((biprod.inl : A ⟶ (A ⊞ B : ModuleCat ℚ)).hom a') = 0 := by
        have h := congrArg (fun (φ : A ⟶ B) => φ.hom a') (biprod.inl_snd (X := A) (Y := B))
        rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
        exact h
      have hB : (biprod.snd : (A ⊞ B : ModuleCat ℚ) ⟶ B).hom ((biprod.inr : B ⟶ (A ⊞ B : ModuleCat ℚ)).hom b') = b' := by
        have h := congrArg (fun (φ : B ⟶ B) => φ.hom b') (biprod.inr_snd (X := A) (Y := B))
        rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
        exact h
      rw [hA, hB, zero_add]
    rw [h3] at h2
    exact h2.symm
  refine ⟨eX.hom.hom y, ?_, ?_⟩
  · rw [← cU' y, hfst, hUa]
  · rw [← cV' y, hsnd, hVb]

/-! ## Injectivity of `mvF` in positive degrees when the overlap vanishes -/

/-- **The two ways of restricting from `X` to `U ∩ V` agree** (via `U`). -/
theorem mvRestrU_comp_mvRestrUVU {X : Type} [TopologicalSpace X] (A U V : Set X) (n : ℕ) :
    Work.Serre.mvRestrU (TopCat.of X) A U n ≫ Work.Serre.mvRestrUVU (TopCat.of X) A U V n
      = Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
          ({y : ↥(U ∩ V) | (y : X) ∈ A}) A (fun _ hy => hy) ℚ n := by
  let SUV : Set ↥(U ∩ V) := {y : ↥(U ∩ V) | (y : X) ∈ A}
  let SU : Set ↥U := {y : ↥U | (y : X) ∈ A}
  show Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X)) SU A
        (fun _ hy => hy) ℚ n
      ≫ Work.Thom.relCohMap
          (⟨fun x : ↥(U ∩ V) => ⟨x.1, x.2.1⟩, by continuity⟩ : C(↥(U ∩ V), ↥U))
          SUV SU (fun _ hy => hy) ℚ n
      = Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X)) SUV A
          (fun _ hy => hy) ℚ n
  rw [Work.Thom.relCohMap_compA SUV SU A
    (⟨fun x : ↥(U ∩ V) => ⟨x.1, x.2.1⟩, by continuity⟩ : C(↥(U ∩ V), ↥U))
    (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X)) (fun _ hy => hy) (fun _ hy => hy)
    (fun _ hy => hy) ℚ n]
  exact Work.Thom.relCohMap_congrA _ _ (ContinuousMap.ext fun x => rfl) _ _ ℚ n

/-- **The two ways of restricting from `X` to `U ∩ V` agree** (via `V`). -/
theorem mvRestrV_comp_mvRestrUVV {X : Type} [TopologicalSpace X] (A U V : Set X) (n : ℕ) :
    Work.Serre.mvRestrV (TopCat.of X) A V n ≫ Work.Serre.mvRestrUVV (TopCat.of X) A U V n
      = Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
          ({y : ↥(U ∩ V) | (y : X) ∈ A}) A (fun _ hy => hy) ℚ n := by
  let SUV : Set ↥(U ∩ V) := {y : ↥(U ∩ V) | (y : X) ∈ A}
  let SV : Set ↥V := {y : ↥V | (y : X) ∈ A}
  show Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X)) SV A
        (fun _ hy => hy) ℚ n
      ≫ Work.Thom.relCohMap
          (⟨fun x : ↥(U ∩ V) => ⟨x.1, x.2.2⟩, by continuity⟩ : C(↥(U ∩ V), ↥V))
          SUV SV (fun _ hy => hy) ℚ n
      = Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X)) SUV A
          (fun _ hy => hy) ℚ n
  rw [Work.Thom.relCohMap_compA SUV SV A
    (⟨fun x : ↥(U ∩ V) => ⟨x.1, x.2.2⟩, by continuity⟩ : C(↥(U ∩ V), ↥V))
    (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X)) (fun _ hy => hy) (fun _ hy => hy)
    (fun _ hy => hy) ℚ n]
  exact Work.Thom.relCohMap_congrA _ _ (ContinuousMap.ext fun x => rfl) _ _ ℚ n

/-- **The two restrictions from `X` to `U ∩ V` agree.** -/
theorem mvRestrUV_eq {X : Type} [TopologicalSpace X] (A U V : Set X) (n : ℕ) :
    Work.Serre.mvRestrU (TopCat.of X) A U n ≫ Work.Serre.mvRestrUVU (TopCat.of X) A U V n
      = Work.Serre.mvRestrV (TopCat.of X) A V n ≫ Work.Serre.mvRestrUVV (TopCat.of X) A U V n := by
  rw [mvRestrU_comp_mvRestrUVU, mvRestrV_comp_mvRestrUVV]

/-- **`mvF` is injective in degree `t ≥ 1` when the overlap vanishes in degree `t - 1`.** -/
theorem ker_mvF_eq_bot {X : Type} [TopologicalSpace X] (A U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (t : ℕ) (ht : 0 < t)
    (hvan : Subsingleton (Work.Serre.mvCohUV (TopCat.of X) A U V (t - 1))) :
    LinearMap.ker (Work.Serre.mvF (TopCat.of X) A U V t).hom = ⊥ := by
  haveI := hvan
  have h1 : LinearMap.ker (Work.Serre.mvF (TopCat.of X) A U V ((t - 1) + 1)).hom = ⊥ := by
    rw [← Work.Serre.exact_mvDelta_mvF (TopCat.of X) A U V hU hV hcov (t - 1)]
    have hzero : Work.Serre.mvDelta (TopCat.of X) A U V hU hV hcov (t - 1) = 0 :=
      IsZero.eq_zero_of_src (ModuleCat.isZero_of_subsingleton _) _
    rw [hzero, ModuleCat.hom_zero, LinearMap.range_zero]
  have hidx : (t - 1) + 1 = t := by omega
  rwa [hidx] at h1

/-- **An element of a biproduct with vanishing projections is zero.** -/
theorem biprod_eq_zero_of_fst_snd {R : Type} [CommRing R] {M N : ModuleCat R}
    (y : (M ⊞ N : ModuleCat R))
    (h1 : (biprod.fst : M ⊞ N ⟶ M).hom y = 0) (h2 : (biprod.snd : M ⊞ N ⟶ N).hom y = 0) :
    y = 0 := by
  have h := congrArg (fun (f : M ⊞ N ⟶ (M ⊞ N : ModuleCat R)) => f.hom y)
    (biprod.total (X := M) (Y := N))
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply] at h
  rw [h1, h2, map_zero, map_zero, add_zero] at h
  exact h.symm

theorem bijective_mixedCup_of_openCover_zero {X : Type} [TopologicalSpace X] (A : Set X)
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (n₀ : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ X A)
    (hvanU : Subsingleton ↥(Work.Thom.RelCoh ℚ (n₀ - 1) ↥U {y : ↥U | (y : X) ∈ A}))
    (hvanV : Subsingleton ↥(Work.Thom.RelCoh ℚ (n₀ - 1) ↥V {y : ↥V | (y : X) ∈ A}))
    (hvanUV : Subsingleton ↥(Work.Thom.RelCoh ℚ (n₀ - 1) ↥(U ∩ V)
      {y : ↥(U ∩ V) | (y : X) ∈ A}))
    (hlocU : Function.Bijective (fun x : Work.Thom.Coh ℚ 0 ↥U =>
      (Work.Thom.mixedCupC ℚ {y : ↥U | (y : X) ∈ A} 0 n₀) x
        ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X))
          {y : ↥U | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀)))
    (hlocV : Function.Bijective (fun x : Work.Thom.Coh ℚ 0 ↥V =>
      (Work.Thom.mixedCupC ℚ {y : ↥V | (y : X) ∈ A} 0 n₀) x
        ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X))
          {y : ↥V | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀)))
    (hlocUV : Function.Bijective (fun x : Work.Thom.Coh ℚ 0 ↥(U ∩ V) =>
      (Work.Thom.mixedCupC ℚ {y : ↥(U ∩ V) | (y : X) ∈ A} 0 n₀) x
        ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
          {y : ↥(U ∩ V) | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀))) :
    Function.Bijective (fun x : Work.Thom.Coh ℚ 0 X =>
      (Work.Thom.mixedCupC ℚ A 0 n₀) x U₀) := by
  classical
  rcases Nat.eq_zero_or_pos n₀ with hn0 | hpos
  · -- ## the degenerate case `n₀ = 0`
    subst hn0
    haveI hsubU : Subsingleton ↥(Work.Thom.RelCoh ℚ (0 + 0) ↥U {y : ↥U | (y : X) ∈ A}) := hvanU
    haveI hsubV : Subsingleton ↥(Work.Thom.RelCoh ℚ (0 + 0) ↥V {y : ↥V | (y : X) ∈ A}) := hvanV
    have hSU : Subsingleton (Work.Thom.Coh ℚ 0 ↥U) :=
      ⟨fun a b => hlocU.1 (Subsingleton.elim _ _)⟩
    have hSV : Subsingleton (Work.Thom.Coh ℚ 0 ↥V) :=
      ⟨fun a b => hlocV.1 (Subsingleton.elim _ _)⟩
    have hEU : IsEmpty ↥U := isEmpty_of_subsingleton_coh_zero hSU
    have hEV : IsEmpty ↥V := isEmpty_of_subsingleton_coh_zero hSV
    have hEX : IsEmpty X := ⟨fun x => by
      have hx : x ∈ U ∪ V := by rw [hcov]; exact trivial
      rcases hx with hxU | hxV
      · exact hEU.elim ⟨x, hxU⟩
      · exact hEV.elim ⟨x, hxV⟩⟩
    haveI : IsEmpty X := hEX
    haveI : Subsingleton (Work.Thom.Coh ℚ 0 X) :=
      ModuleCat.subsingleton_of_isZero (isZero_coh_of_isEmpty_space (Y := X) 0)
    haveI : Subsingleton (Work.Thom.RelCoh ℚ (0 + 0) X A) :=
      ModuleCat.subsingleton_of_isZero (isZero_relCoh_of_isEmpty_space (Y := X) A (0 + 0))
    exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ b⟩⟩
  · -- ## the case `n₀ ≥ 1`
    have hn0 : 0 < 0 + n₀ := by omega
    let SU : Set ↥U := {y : ↥U | (y : X) ∈ A}
    let SV : Set ↥V := {y : ↥V | (y : X) ∈ A}
    let SUV : Set ↥(U ∩ V) := {y : ↥(U ∩ V) | (y : X) ∈ A}
    let ιU : C(↥U, X) := ⟨Subtype.val, continuous_subtype_val⟩
    let ιV : C(↥V, X) := ⟨Subtype.val, continuous_subtype_val⟩
    let ιUV : C(↥(U ∩ V), X) := ⟨Subtype.val, continuous_subtype_val⟩
    let ιUVU : C(↥(U ∩ V), ↥U) := ⟨fun x => ⟨x.1, x.2.1⟩, by continuity⟩
    let ιUVV : C(↥(U ∩ V), ↥V) := ⟨fun x => ⟨x.1, x.2.2⟩, by continuity⟩
    let hfU : ∀ x ∈ SU, ιU x ∈ A := fun _ hy => hy
    let hfV : ∀ x ∈ SV, ιV x ∈ A := fun _ hy => hy
    let hfUV : ∀ x ∈ SUV, ιUV x ∈ A := fun _ hy => hy
    let hfUVU : ∀ x ∈ SUV, ιUVU x ∈ SU := fun _ hy => hy
    let hfUVV : ∀ x ∈ SUV, ιUVV x ∈ SV := fun _ hy => hy
    let rU : Work.Thom.Coh ℚ 0 X ⟶ Work.Thom.Coh ℚ 0 ↥U := Work.Thom.CohMap ιU ℚ 0
    let rV : Work.Thom.Coh ℚ 0 X ⟶ Work.Thom.Coh ℚ 0 ↥V := Work.Thom.CohMap ιV ℚ 0
    let rUVU : Work.Thom.Coh ℚ 0 ↥U ⟶ Work.Thom.Coh ℚ 0 ↥(U ∩ V) :=
      Work.Thom.CohMap ιUVU ℚ 0
    let rUVV : Work.Thom.Coh ℚ 0 ↥V ⟶ Work.Thom.Coh ℚ 0 ↥(U ∩ V) :=
      Work.Thom.CohMap ιUVV ℚ 0
    let mU : Work.Thom.RelCoh ℚ n₀ X A ⟶ Work.Thom.RelCoh ℚ n₀ ↥U SU :=
      Work.Thom.relCohMap ιU SU A hfU ℚ n₀
    let mV : Work.Thom.RelCoh ℚ n₀ X A ⟶ Work.Thom.RelCoh ℚ n₀ ↥V SV :=
      Work.Thom.relCohMap ιV SV A hfV ℚ n₀
    let mUV : Work.Thom.RelCoh ℚ n₀ X A ⟶ Work.Thom.RelCoh ℚ n₀ ↥(U ∩ V) SUV :=
      Work.Thom.relCohMap ιUV SUV A hfUV ℚ n₀
    let mUVU : Work.Thom.RelCoh ℚ n₀ ↥U SU ⟶ Work.Thom.RelCoh ℚ n₀ ↥(U ∩ V) SUV :=
      Work.Thom.relCohMap ιUVU SUV SU hfUVU ℚ n₀
    let mUVV : Work.Thom.RelCoh ℚ n₀ ↥V SV ⟶ Work.Thom.RelCoh ℚ n₀ ↥(U ∩ V) SUV :=
      Work.Thom.relCohMap ιUVV SUV SV hfUVV ℚ n₀
    let mvRU : Work.Thom.RelCoh ℚ (0 + n₀) X A ⟶ Work.Thom.RelCoh ℚ (0 + n₀) ↥U SU :=
      Work.Serre.mvRestrU (TopCat.of X) A U (0 + n₀)
    let mvRV : Work.Thom.RelCoh ℚ (0 + n₀) X A ⟶ Work.Thom.RelCoh ℚ (0 + n₀) ↥V SV :=
      Work.Serre.mvRestrV (TopCat.of X) A V (0 + n₀)
    let mvRUVU : Work.Thom.RelCoh ℚ (0 + n₀) ↥U SU ⟶
        Work.Thom.RelCoh ℚ (0 + n₀) ↥(U ∩ V) SUV :=
      Work.Serre.mvRestrUVU (TopCat.of X) A U V (0 + n₀)
    let mvRUVV : Work.Thom.RelCoh ℚ (0 + n₀) ↥V SV ⟶
        Work.Thom.RelCoh ℚ (0 + n₀) ↥(U ∩ V) SUV :=
      Work.Serre.mvRestrUVV (TopCat.of X) A U V (0 + n₀)
    let φX : Work.Thom.Coh ℚ 0 X → Work.Thom.RelCoh ℚ (0 + n₀) X A :=
      fun x => (Work.Thom.mixedCupC ℚ A 0 n₀) x U₀
    let φU : Work.Thom.Coh ℚ 0 ↥U → Work.Thom.RelCoh ℚ (0 + n₀) ↥U SU :=
      fun x => (Work.Thom.mixedCupC ℚ SU 0 n₀) x (mU.hom U₀)
    let φV : Work.Thom.Coh ℚ 0 ↥V → Work.Thom.RelCoh ℚ (0 + n₀) ↥V SV :=
      fun x => (Work.Thom.mixedCupC ℚ SV 0 n₀) x (mV.hom U₀)
    let φUV : Work.Thom.Coh ℚ 0 ↥(U ∩ V) → Work.Thom.RelCoh ℚ (0 + n₀) ↥(U ∩ V) SUV :=
      fun x => (Work.Thom.mixedCupC ℚ SUV 0 n₀) x (mUV.hom U₀)
    have hlocU' : Function.Bijective φU := hlocU
    have hlocV' : Function.Bijective φV := hlocV
    have hlocUV' : Function.Bijective φUV := hlocUV
    -- ## the two composite restrictions of `U₀` agree
    have hmUVU : mUVU.hom (mU.hom U₀) = mUV.hom U₀ := by
      have h := congrArg (fun (φ : Work.Thom.RelCoh ℚ n₀ X A ⟶
          Work.Thom.RelCoh ℚ n₀ ↥(U ∩ V) SUV) => φ.hom U₀)
        (mvRestrU_comp_mvRestrUVU A U V n₀)
      rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      exact h
    have hmUVV : mUVV.hom (mV.hom U₀) = mUV.hom U₀ := by
      have h := congrArg (fun (φ : Work.Thom.RelCoh ℚ n₀ X A ⟶
          Work.Thom.RelCoh ℚ n₀ ↥(U ∩ V) SUV) => φ.hom U₀)
        (mvRestrV_comp_mvRestrUVV A U V n₀)
      rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      exact h
    -- ## naturality of the cup map
    have natU : ∀ z : Work.Thom.Coh ℚ 0 X, mvRU.hom (φX z) = φU (rU.hom z) :=
      fun z => Work.StemsB.mixedCupC_pairNaturalR ℚ ιU SU A hfU 0 n₀ z U₀
    have natV : ∀ z : Work.Thom.Coh ℚ 0 X, mvRV.hom (φX z) = φV (rV.hom z) :=
      fun z => Work.StemsB.mixedCupC_pairNaturalR ℚ ιV SV A hfV 0 n₀ z U₀
    have natUVU : ∀ a : Work.Thom.Coh ℚ 0 ↥U, mvRUVU.hom (φU a) = φUV (rUVU.hom a) := by
      intro a
      have h := Work.StemsB.mixedCupC_pairNaturalR ℚ ιUVU SUV SU hfUVU 0 n₀ a (mU.hom U₀)
      rw [hmUVU] at h
      exact h
    have natUVV : ∀ b : Work.Thom.Coh ℚ 0 ↥V, mvRUVV.hom (φV b) = φUV (rUVV.hom b) := by
      intro b
      have h := Work.StemsB.mixedCupC_pairNaturalR ℚ ιUVV SUV SV hfUVV 0 n₀ b (mV.hom U₀)
      rw [hmUVV] at h
      exact h
    -- ## the two restrictions from `X` to `U ∩ V` agree
    have hmvcomp : mvRU ≫ mvRUVU = mvRV ≫ mvRUVV := mvRestrUV_eq A U V (0 + n₀)
    -- ## injectivity
    have hinj : Function.Injective φX := by
      intro x y hxy
      have hU1 : φU (rU.hom x) = φU (rU.hom y) := by rw [← natU x, ← natU y, hxy]
      have hV1 : φV (rV.hom x) = φV (rV.hom y) := by rw [← natV x, ← natV y, hxy]
      have hxU : rU.hom x = rU.hom y := hlocU'.1 hU1
      have hxV : rV.hom x = rV.hom y := hlocV'.1 hV1
      have hzero : x - y = 0 := by
        refine h0_restrict_eq_zero_of_cover hcov (x - y) ?_ ?_
        · rw [map_sub, hxU, sub_self]
        · rw [map_sub, hxV, sub_self]
      exact sub_eq_zero.mp hzero
    -- ## surjectivity
    have hsurj : Function.Surjective φX := by
      intro z
      obtain ⟨a, ha⟩ := hlocU'.2 (mvRU.hom z)
      obtain ⟨b, hb⟩ := hlocV'.2 (mvRV.hom z)
      have hcompat : rUVU.hom a = rUVV.hom b := by
        refine hlocUV'.1 ?_
        have h1 : mvRUVU.hom (mvRU.hom z) = mvRUVV.hom (mvRV.hom z) := by
          have h := congrArg (fun (φ : Work.Thom.RelCoh ℚ (0 + n₀) X A ⟶
              Work.Thom.RelCoh ℚ (0 + n₀) ↥(U ∩ V) SUV) => φ.hom z) hmvcomp
          rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
            LinearMap.comp_apply] at h
          exact h
        calc φUV (rUVU.hom a) = mvRUVU.hom (φU a) := (natUVU a).symm
          _ = mvRUVU.hom (mvRU.hom z) := by rw [ha]
          _ = mvRUVV.hom (mvRV.hom z) := h1
          _ = mvRUVV.hom (φV b) := by rw [hb]
          _ = φUV (rUVV.hom b) := natUVV b
      obtain ⟨x, hx1, hx2⟩ := exists_glue_coh_zero U V hU hV hcov a b hcompat
      refine ⟨x, ?_⟩
      have hz1 : mvRU.hom (φX x) = mvRU.hom z := by rw [natU x, hx1, ha]
      have hz2 : mvRV.hom (φX x) = mvRV.hom z := by rw [natV x, hx2, hb]
      have hlift : Work.Serre.mvF (TopCat.of X) A U V (0 + n₀) ≫
          (biprod.fst : Work.Thom.RelCoh ℚ (0 + n₀) ↥U SU ⊞
            Work.Thom.RelCoh ℚ (0 + n₀) ↥V SV ⟶ Work.Thom.RelCoh ℚ (0 + n₀) ↥U SU) = mvRU := by
        show biprod.lift (Work.Serre.mvRestrU (TopCat.of X) A U (0 + n₀))
            (Work.Serre.mvRestrV (TopCat.of X) A V (0 + n₀)) ≫ biprod.fst = mvRU
        rw [biprod.lift_fst]
      have hlift' : Work.Serre.mvF (TopCat.of X) A U V (0 + n₀) ≫
          (biprod.snd : Work.Thom.RelCoh ℚ (0 + n₀) ↥U SU ⊞
            Work.Thom.RelCoh ℚ (0 + n₀) ↥V SV ⟶ Work.Thom.RelCoh ℚ (0 + n₀) ↥V SV) = mvRV := by
        show biprod.lift (Work.Serre.mvRestrU (TopCat.of X) A U (0 + n₀))
            (Work.Serre.mvRestrV (TopCat.of X) A V (0 + n₀)) ≫ biprod.snd = mvRV
        rw [biprod.lift_snd]
      have hvan' : Subsingleton (Work.Serre.mvCohUV (TopCat.of X) A U V ((0 + n₀) - 1)) := by
        rw [show (0 + n₀) - 1 = n₀ - 1 from congrArg (fun t => t - 1) (Nat.zero_add n₀)]
        exact hvanUV
      have hinjF : Function.Injective (Work.Serre.mvF (TopCat.of X) A U V (0 + n₀)).hom :=
        LinearMap.ker_eq_bot.mp (ker_mvF_eq_bot A U V hU hV hcov (0 + n₀) hn0 hvan')
      have hsub : φX x - z = 0 := by
        refine hinjF ?_
        rw [map_zero]
        refine biprod_eq_zero_of_fst_snd _ ?_ ?_
        · rw [← comp_hom_apply (Work.Serre.mvF (TopCat.of X) A U V (0 + n₀))
              (biprod.fst : Work.Thom.RelCoh ℚ (0 + n₀) ↥U SU ⊞
                Work.Thom.RelCoh ℚ (0 + n₀) ↥V SV ⟶ Work.Thom.RelCoh ℚ (0 + n₀) ↥U SU)
              (φX x - z), hlift]
          rw [map_sub, hz1, sub_self]
        · rw [← comp_hom_apply (Work.Serre.mvF (TopCat.of X) A U V (0 + n₀))
              (biprod.snd : Work.Thom.RelCoh ℚ (0 + n₀) ↥U SU ⊞
                Work.Thom.RelCoh ℚ (0 + n₀) ↥V SV ⟶ Work.Thom.RelCoh ℚ (0 + n₀) ↥V SV)
              (φX x - z), hlift']
          rw [map_sub, hz2, sub_self]
      exact sub_eq_zero.mp hsub
    exact ⟨hinj, hsurj⟩

end

end Work.Serre
