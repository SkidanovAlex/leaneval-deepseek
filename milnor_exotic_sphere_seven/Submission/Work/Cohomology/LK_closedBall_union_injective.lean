import Mathlib
import Submission.Work.Cohomology.StageSplitDefs
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.pd_small_union_iso
import Submission.Work.Cohomology.euclidean_top_homology_vanishing
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.Cohomology.lkMap_isIso_of_convex
import Submission.Work.Cohomology.relChains_vanishing_of_compact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Injectivity of the local homology of a union of closed balls

The main result of this file is `Work.Cohomology.LK_closedBall_union_injective`: a class in the
local homology `LK N (⋃ j, closedBall (c j) (r j))` of a finite union of closed balls whose image in
the local homology `LK N {x j}` of a point `x j` of the `j`-th ball vanishes for every `j` is zero.

The mathematical content is the Mayer–Vietoris style statement that the map

`LK N (K₁ ∪ K₂) ⟶ LK N K₁ ⊞ LK N K₂`

is injective (`lk_twoPiece_ker`), together with the fact that for a convex set `D` the stage map
`LK N D ⟶ LK N {x}` is injective (`lkMap_isIso_of_convex`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable {N : ℕ}

/-! ## Elementary closure properties -/

/-- A proof-irrelevance statement for `lkMap`: the map only depends on the underlying inclusion, so
any two proofs of the same inclusion give the same linear map. -/
theorem lk_lkMap_congr {K K' : Set (EuclideanSpace ℝ (Fin N))} (h h' : K ⊆ K')
    (β : LK N K') : lkMap (N := N) h β = lkMap (N := N) h' β := by
  have hh : h = h' := Subsingleton.elim _ _
  rw [hh]

/-! ## The inclusions of chains of the Mayer–Vietoris pair -/

/-- `inclChainsSub` is the first component of the Mayer–Vietoris map. -/
theorem lk_inclChainsSub_eq_inclUVU {X : TopCat} {U V : Set X} (h : U ∩ V ⊆ U) :
    inclChainsSub X (U ∩ V) U h
      = SSet.chainComplexMap (TopCat.toSSet.map (inclUVU U V)) (ModuleCat.of ℤ ℤ) := by
  rw [inclChainsSub]
  have hhom : (TopCat.ofHom ⟨fun x : ↥(U ∩ V) => ⟨(x : X), h x.2⟩,
      Continuous.subtype_mk (f := fun x : ↥(U ∩ V) => (x : X)) continuous_subtype_val
        (fun x => h x.2)⟩ : TopCat.of ↥(U ∩ V) ⟶ TopCat.of U) = inclUVU U V := by
    ext x : 1
    exact Subtype.ext rfl
  rw [hhom]
  rfl

/-- `inclChainsSub` is the second component of the Mayer–Vietoris map. -/
theorem lk_inclChainsSub_eq_inclUVV {X : TopCat} {U V : Set X} (h : U ∩ V ⊆ V) :
    inclChainsSub X (U ∩ V) V h
      = SSet.chainComplexMap (TopCat.toSSet.map (inclUVV U V)) (ModuleCat.of ℤ ℤ) := by
  rw [inclChainsSub]
  have hhom : (TopCat.ofHom ⟨fun x : ↥(U ∩ V) => ⟨(x : X), h x.2⟩,
      Continuous.subtype_mk (f := fun x : ↥(U ∩ V) => (x : X)) continuous_subtype_val
        (fun x => h x.2)⟩ : TopCat.of ↥(U ∩ V) ⟶ TopCat.of V) = inclUVV U V := by
    ext x : 1
    exact Subtype.ext rfl
  rw [hhom]
  rfl

/-! ## Naturality of the connecting map of a pair -/

/-- The canonical morphism of short complexes of the pair `(X, A) ⟶ (X, A')` for `A ⊆ A'`. -/
def lk_hPairMap {X : TopCat} {A A' : Set X} (h : A ⊆ A') : hPairShort X A ⟶ hPairShort X A' where
  τ₁ := inclChainsSub X A A' h
  τ₂ := 𝟙 _
  τ₃ := relCokerMap X A A' h
  comm₁₂ := by rw [Category.comp_id]; exact inclChainsSub_comp X A A' h
  comm₂₃ := by rw [Category.id_comp]; exact (relCokerMap_comp_π X A A' h).symm

/-- **Naturality of the connecting map of a pair** in the subspace. -/
theorem lk_hPairδ_naturality {X : TopCat} {A A' : Set X} (h : A ⊆ A') (n : ℕ) :
    hPairδ X A n ≫ HomologicalComplex.homologyMap (inclChainsSub X A A' h) n
      = HomologicalComplex.homologyMap (relCokerMap X A A' h) (n + 1) ≫ hPairδ X A' n :=
  HomologicalComplex.HomologySequence.δ_naturality (lk_hPairMap h) (hPairShort_shortExact X A)
    (hPairShort_shortExact X A') (n + 1) n (by simp [ComplexShape.down])

/-- The elementwise form of the naturality of the connecting map of a pair. -/
theorem lk_hPairδ_naturality_apply {X : TopCat} {A A' : Set X} (h : A ⊆ A') (n : ℕ)
    (t : (relChains X A).homology (n + 1)) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChainsSub X A A' h) n))
        ((ModuleCat.Hom.hom (hPairδ X A n)) t)
      = (ModuleCat.Hom.hom (hPairδ X A' n))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (relCokerMap X A A' h) (n + 1))) t) := by
  have hnat := congrArg (fun (φ : (relChains X A).homology (n + 1) ⟶
      (singularChains ℤ (TopCat.of A')).homology n) => (ModuleCat.Hom.hom φ) t)
    (lk_hPairδ_naturality (X := X) (A := A) (A' := A') h n)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  exact hnat

/-! ## The Mayer–Vietoris injectivity -/

/-- **The first map of the Mayer–Vietoris sequence is injective** if `H_{n+1}` of the small
chains vanishes. -/
theorem lk_mvLeft_ker_general {X : TopCat} {U V : Set X} (n : ℕ)
    (hvan : IsZero ((smallChains U V).homology (n + 1))) :
    LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (mvLeft U V) n)) = ⊥ := by
  have hex := ShortComplex.Exact.moduleCat_range_eq_ker (mv_H_exact₁ U V n)
  have hδ : mvδ U V n = 0 := IsZero.eq_zero_of_src hvan _
  have hrange : (ModuleCat.Hom.hom (mvδ U V n)).range = ⊥ := by
    rw [hδ]; exact LinearMap.range_zero
  exact hex.symm.trans hrange

/-! ## Transport of the degree -/

/-- Application of `homologyMap` commutes with the transport of the degree. -/
theorem lk_homologyMap_eqToHom_apply {K L : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L)
    {k k' : ℕ} (h : k = k') (x : K.homology k) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap f k'))
        ((ModuleCat.Hom.hom (eqToHom (congrArg (fun j => K.homology j) h))) x)
      = (ModuleCat.Hom.hom (eqToHom (congrArg (fun j => L.homology j) h)))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap f k)) x) := by
  subst h
  simp

/-- Two morphisms that are equal act in the same way on elements. -/
theorem lk_hom_congr {M N' : ModuleCat ℤ} {f g : M ⟶ N'} (h : f = g) (x : M) :
    (ModuleCat.Hom.hom f) x = (ModuleCat.Hom.hom g) x :=
  congrArg (fun φ => (ModuleCat.Hom.hom φ) x) h

/-- A `homologyMap` only depends on the chain map. -/
theorem lk_homologyMap_congr {K L : ChainComplex (ModuleCat ℤ) ℕ} {f g : K ⟶ L} (h : f = g)
    (n : ℕ) : HomologicalComplex.homologyMap f n = HomologicalComplex.homologyMap g n :=
  congrArg (fun φ => HomologicalComplex.homologyMap φ n) h

/-! ## Elementwise facts about biproducts of `ℤ`-modules -/

/-- An element of a biproduct is the sum of its components. -/
theorem lk_biprod_eq_components {A B : ModuleCat ℤ} (y : (A ⊞ B : ModuleCat ℤ)) :
    y = (ModuleCat.Hom.hom (biprod.inl : A ⟶ (A ⊞ B : ModuleCat ℤ)))
          ((ModuleCat.Hom.hom (biprod.fst : (A ⊞ B : ModuleCat ℤ) ⟶ A)) y)
      + (ModuleCat.Hom.hom (biprod.inr : B ⟶ (A ⊞ B : ModuleCat ℤ)))
          ((ModuleCat.Hom.hom (biprod.snd : (A ⊞ B : ModuleCat ℤ) ⟶ B)) y) := by
  have hmor : (biprod.fst : (A ⊞ B : ModuleCat ℤ) ⟶ A) ≫
        (biprod.inl : A ⟶ (A ⊞ B : ModuleCat ℤ))
      + (biprod.snd : (A ⊞ B : ModuleCat ℤ) ⟶ B) ≫
        (biprod.inr : B ⟶ (A ⊞ B : ModuleCat ℤ))
      = 𝟙 (A ⊞ B : ModuleCat ℤ) := by
    refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp only [Preadditive.add_comp, Category.assoc, biprod.inl_fst, biprod.inr_fst,
        biprod.inl_snd, biprod.inr_snd, Category.comp_id, Limits.comp_zero, add_zero, zero_add,
        Category.id_comp]
  have h := congrArg (fun (φ : (A ⊞ B : ModuleCat ℤ) ⟶ (A ⊞ B : ModuleCat ℤ)) =>
    (ModuleCat.Hom.hom φ) y) hmor
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.id_apply] at h
  exact h.symm

/-- If both components of `biprod.lift f g` at `z` vanish, so does the value. -/
theorem lk_biprod_lift_eq_zero_of_components {A B C : ModuleCat ℤ} (f : A ⟶ B) (g : A ⟶ C)
    (z : A) (hf : (ModuleCat.Hom.hom f) z = 0) (hg : (ModuleCat.Hom.hom g) z = 0) :
    (ModuleCat.Hom.hom (biprod.lift f g)) z = 0 := by
  have h1 : (ModuleCat.Hom.hom (biprod.fst : (B ⊞ C : ModuleCat ℤ) ⟶ B))
      ((ModuleCat.Hom.hom (biprod.lift f g)) z) = 0 := by
    have h := congrArg (fun (φ : A ⟶ B) => (ModuleCat.Hom.hom φ) z)
      (CategoryTheory.Limits.biprod.lift_fst f g)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hf] using h
  have h2 : (ModuleCat.Hom.hom (biprod.snd : (B ⊞ C : ModuleCat ℤ) ⟶ C))
      ((ModuleCat.Hom.hom (biprod.lift f g)) z) = 0 := by
    have h := congrArg (fun (φ : A ⟶ C) => (ModuleCat.Hom.hom φ) z)
      (CategoryTheory.Limits.biprod.lift_snd f g)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hg] using h
  rw [lk_biprod_eq_components ((ModuleCat.Hom.hom (biprod.lift f g)) z), h1, h2]
  simp

/-- **The component form of the injectivity of the Mayer–Vietoris map.** -/
theorem lk_mvLeft_ker_component {X : TopCat} {U V : Set X} (n : ℕ)
    (hvan : IsZero ((smallChains U V).homology (n + 1)))
    (z : (singularChains ℤ (TopCat.of ↥(U ∩ V))).homology n)
    (h1 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map (inclUVU U V)) (ModuleCat.of ℤ ℤ)) n)) z = 0)
    (h2 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map (inclUVV U V)) (ModuleCat.of ℤ ℤ)) n)) z = 0) :
    z = 0 := by
  have hker : LinearMap.ker (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (mvLeft U V) n)) = ⊥ :=
    lk_mvLeft_ker_general n hvan
  have hinj : Function.Injective (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (mvLeft U V) n)) := LinearMap.ker_eq_bot.mp hker
  apply hinj
  rw [map_zero]
  haveI hpre : PreservesBinaryBiproduct (singularChains ℤ (TopCat.of U))
      (singularChains ℤ (TopCat.of V))
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n) :=
    preservesBinaryBiproduct_of_preservesBiproduct _ _ _
  have hfac : HomologicalComplex.homologyMap (mvLeft U V) n
      = biprod.lift
          (HomologicalComplex.homologyMap
            (SSet.chainComplexMap (TopCat.toSSet.map (inclUVU U V)) (ModuleCat.of ℤ ℤ)) n)
          (HomologicalComplex.homologyMap
            (SSet.chainComplexMap (TopCat.toSSet.map (inclUVV U V)) (ModuleCat.of ℤ ℤ)) n)
        ≫ (Functor.mapBiprod (HomologicalComplex.homologyFunctor (ModuleCat ℤ)
              (ComplexShape.down ℕ) n)
            (singularChains ℤ (TopCat.of U)) (singularChains ℤ (TopCat.of V))).inv := by
    rw [mvLeft]
    exact (CategoryTheory.Limits.biprod.lift_mapBiprod
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n)
      (singularChains ℤ (TopCat.of U)) (singularChains ℤ (TopCat.of V))
      (SSet.chainComplexMap (TopCat.toSSet.map (inclUVU U V)) (ModuleCat.of ℤ ℤ))
      (SSet.chainComplexMap (TopCat.toSSet.map (inclUVV U V)) (ModuleCat.of ℤ ℤ))).symm
  rw [hfac]
  haveI : IsIso ((Functor.mapBiprod (HomologicalComplex.homologyFunctor (ModuleCat ℤ)
        (ComplexShape.down ℕ) n)
      (singularChains ℤ (TopCat.of U)) (singularChains ℤ (TopCat.of V))).inv) :=
    inferInstance
  have hinj' : Function.Injective (ModuleCat.Hom.hom ((Functor.mapBiprod
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n)
      (singularChains ℤ (TopCat.of U)) (singularChains ℤ (TopCat.of V))).inv)) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hz : (ModuleCat.Hom.hom (biprod.lift
      (HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map (inclUVU U V)) (ModuleCat.of ℤ ℤ)) n)
      (HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map (inclUVV U V)) (ModuleCat.of ℤ ℤ)) n))) z = 0 :=
    lk_biprod_lift_eq_zero_of_components _ _ z h1 h2
  exact (congrArg (ModuleCat.Hom.hom ((Functor.mapBiprod
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n)
      (singularChains ℤ (TopCat.of U)) (singularChains ℤ (TopCat.of V))).inv)) hz).trans
    (map_zero _)

/-- **The component form of the injectivity of the Mayer–Vietoris map**, with the components
expressed through `inclChainsSub`. -/
theorem lk_mvLeft_inclChainsSub_component {X : TopCat} {U V : Set X} (h₁ : U ∩ V ⊆ U)
    (h₂ : U ∩ V ⊆ V) (n : ℕ) (hvan : IsZero ((smallChains U V).homology (n + 1)))
    (z : (singularChains ℤ (TopCat.of ↥(U ∩ V))).homology n)
    (hz₁ : (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (inclChainsSub X (U ∩ V) U h₁) n)) z = 0)
    (hz₂ : (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (inclChainsSub X (U ∩ V) V h₂) n)) z = 0) :
    z = 0 := by
  refine lk_mvLeft_ker_component n hvan z ?_ ?_
  · rw [lk_homologyMap_congr (lk_inclChainsSub_eq_inclUVU h₁) n] at hz₁
    exact hz₁
  · rw [lk_homologyMap_congr (lk_inclChainsSub_eq_inclUVV h₂) n] at hz₂
    exact hz₂

/-! ## Vanishing of the top homology of the small chains of a pair of complements -/

/-- For open `U, V ⊆ ℝ^N` the `N`-th homology of the small chains of the cover `{U, V}` vanishes:
these small chains compute `H_N(U ∪ V)` and `U ∪ V` is an open subset of `ℝ^N`. -/
theorem lk_isZero_smallChains_pair {N : ℕ} (hN : 1 ≤ N)
    {U V : Set (EuclideanSpace ℝ (Fin N))} (hU : IsOpen U) (hV : IsOpen V) :
    IsZero ((smallChains (X := TopCat.of (EuclideanSpace ℝ (Fin N))) U V).homology N) := by
  obtain ⟨Φ, -, hΦ, -, -⟩ :=
    pd_small_union_iso (M := TopCat.of (EuclideanSpace ℝ (Fin N))) U V hU hV
  haveI : IsIso (HomologicalComplex.homologyMap Φ N) := hΦ N
  exact IsZero.of_iso (euclidean_top_homology_vanishing hN (U ∪ V) (hU.union hV))
    (asIso (HomologicalComplex.homologyMap Φ N))

/-! ## Injectivity of the connecting map of a pair in `ℝ^N` -/

/-- For any `A ⊆ ℝ^N` the connecting map `H_N(ℝ^N, A) ⟶ H_{N-1}(A)` is injective (`N ≥ 1`),
because `H_N(ℝ^N) = 0`. -/
theorem lk_hPairδ_injective {N : ℕ} (hN : 1 ≤ N) {A : Set (EuclideanSpace ℝ (Fin N))} :
    Function.Injective (ModuleCat.Hom.hom
      (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) A (N - 1))) := by
  have hz : IsZero ((singularChains ℤ
      (TopCat.of (EuclideanSpace ℝ (Fin N)))).homology (N - 1 + 1)) := by
    rw [Nat.sub_add_cancel hN]
    exact homologyContractible (X := TopCat.of (EuclideanSpace ℝ (Fin N))) N hN
  have hker : (ModuleCat.Hom.hom
      (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) A (N - 1))).ker = ⊥ := by
    have hex := ShortComplex.Exact.moduleCat_range_eq_ker
      (hPair_exact₃ (TopCat.of (EuclideanSpace ℝ (Fin N))) A (N - 1))
    have hrange : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (cokernel.π (inclChains (TopCat.of (EuclideanSpace ℝ (Fin N))) A))
        (N - 1 + 1))).range = ⊥ := by
      rw [IsZero.eq_zero_of_src hz (HomologicalComplex.homologyMap
        (cokernel.π (inclChains (TopCat.of (EuclideanSpace ℝ (Fin N))) A)) (N - 1 + 1))]
      exact LinearMap.range_zero
    exact hex.symm.trans hrange
  exact LinearMap.ker_eq_bot.mp hker

/-! ## The two-piece injectivity -/

/-- **The two-piece lemma.**  A class in `H_N(ℝ^N, ℝ^N∖(K₁ ∪ K₂))` whose images in
`H_N(ℝ^N, ℝ^N∖K₁)` and `H_N(ℝ^N, ℝ^N∖K₂)` vanish is zero.

The proof uses the Mayer–Vietoris sequence of the open cover
`ℝ^N∖(K₁∪K₂) = (ℝ^N∖K₁) ∩ (ℝ^N∖K₂)` of `(ℝ^N∖K₁) ∪ (ℝ^N∖K₂) = ℝ^N∖(K₁∩K₂)`, whose
`H_N` vanishes because the latter is an open subset of `ℝ^N`. -/
theorem lk_twoPiece_ker {N : ℕ} (hN : 1 ≤ N)
    {U₁ U₂ A₀ : Set (EuclideanSpace ℝ (Fin N))} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (hA : A₀ = U₁ ∩ U₂) (h₁ : A₀ ⊆ U₁) (h₂ : A₀ ⊆ U₂)
    (β : (relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) A₀).homology N)
    (hh₁ : HomologicalComplex.homologyMap
      (relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N))) A₀ U₁ h₁) N β = 0)
    (hh₂ : HomologicalComplex.homologyMap
      (relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N))) A₀ U₂ h₂) N β = 0) : β = 0 := by
  subst hA
  have hsmall : IsZero ((smallChains (X := TopCat.of (EuclideanSpace ℝ (Fin N)))
      U₁ U₂).homology (N - 1 + 1)) := by
    rw [Nat.sub_add_cancel hN]
    exact lk_isZero_smallChains_pair hN hU₁ hU₂
  have hinj := lk_hPairδ_injective (N := N) hN (A := U₁ ∩ U₂)
  have hsub : N - 1 + 1 = N := Nat.sub_add_cancel hN
  let β' : (relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) (U₁ ∩ U₂)).homology (N - 1 + 1) :=
    (ModuleCat.Hom.hom (eqToHom (congrArg (fun j =>
      (relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) (U₁ ∩ U₂)).homology j) hsub.symm))) β
  have hh₁' : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N))) (U₁ ∩ U₂) U₁ h₁)
        (N - 1 + 1))) β' = 0 :=
    (lk_homologyMap_eqToHom_apply
      (relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N))) (U₁ ∩ U₂) U₁ h₁) hsub.symm β).trans
      (by rw [hh₁, map_zero])
  have hh₂' : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N))) (U₁ ∩ U₂) U₂ h₂)
        (N - 1 + 1))) β' = 0 :=
    (lk_homologyMap_eqToHom_apply
      (relCokerMap (TopCat.of (EuclideanSpace ℝ (Fin N))) (U₁ ∩ U₂) U₂ h₂) hsub.symm β).trans
      (by rw [hh₂, map_zero])
  let z : (singularChains ℤ (TopCat.of ↥(U₁ ∩ U₂))).homology (N - 1) :=
    (ModuleCat.Hom.hom (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) (U₁ ∩ U₂) (N - 1))) β'
  have hcomp₁ : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (inclChainsSub (TopCat.of (EuclideanSpace ℝ (Fin N))) (U₁ ∩ U₂) U₁ h₁)
        (N - 1))) z = 0 := by
    have hnat := lk_hPairδ_naturality_apply (X := TopCat.of (EuclideanSpace ℝ (Fin N)))
      (A := U₁ ∩ U₂) (A' := U₁) h₁ (N - 1) β'
    rw [hh₁', map_zero] at hnat
    exact hnat
  have hcomp₂ : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (inclChainsSub (TopCat.of (EuclideanSpace ℝ (Fin N))) (U₁ ∩ U₂) U₂ h₂)
        (N - 1))) z = 0 := by
    have hnat := lk_hPairδ_naturality_apply (X := TopCat.of (EuclideanSpace ℝ (Fin N)))
      (A := U₁ ∩ U₂) (A' := U₂) h₂ (N - 1) β'
    rw [hh₂', map_zero] at hnat
    exact hnat
  have hz0 : z = 0 :=
    lk_mvLeft_inclChainsSub_component h₁ h₂ (N - 1) hsmall z hcomp₁ hcomp₂
  have hβ'0 : β' = 0 := by
    exact hinj (by rw [map_zero]; exact hz0)
  have hg : Function.Injective (ModuleCat.Hom.hom (eqToHom (congrArg (fun j =>
      (relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) (U₁ ∩ U₂)).homology j) hsub.symm))) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  exact hg (by rw [map_zero]; exact hβ'0)

/-! ## The two-piece lemma in the language of `LK` and `lkMap` -/

/-- **The two-piece lemma.**  A class `β ∈ LK N (K₁ ∪ K₂)` whose stage maps to `LK N K₁` and
`LK N K₂` both vanish is zero. -/
theorem lk_twoPiece_lkMap {N : ℕ} (hN : 1 ≤ N)
    {K₁ K₂ : Set (EuclideanSpace ℝ (Fin N))} (hK₁ : IsClosed K₁) (hK₂ : IsClosed K₂)
    (β : LK N (K₁ ∪ K₂))
    (h₁ : lkMap (N := N) Set.subset_union_left β = 0)
    (h₂ : lkMap (N := N) Set.subset_union_right β = 0) : β = 0 := by
  refine lk_twoPiece_ker (N := N) hN (U₁ := {y | y ∉ K₁}) (U₂ := {y | y ∉ K₂})
    (A₀ := {y | y ∉ (K₁ ∪ K₂)}) hK₁.isOpen_compl hK₂.isOpen_compl ?_
    (fun y hy hyK => hy (Set.subset_union_left hyK))
    (fun y hy hyK => hy (Set.subset_union_right hyK)) β h₁ h₂
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_union]
  tauto

/-- **The two-piece lemma, with the union of the two pieces given as a set satisfying the
appropriate equation.** -/
theorem lk_twoPiece_lkMap' {N : ℕ} (hN : 1 ≤ N)
    {S K₁ K₂ : Set (EuclideanSpace ℝ (Fin N))} (hK₁ : IsClosed K₁) (hK₂ : IsClosed K₂)
    (hS : S = K₁ ∪ K₂) (hsub₁ : K₁ ⊆ S) (hsub₂ : K₂ ⊆ S) (β : LK N S)
    (h₁ : lkMap (N := N) hsub₁ β = 0) (h₂ : lkMap (N := N) hsub₂ β = 0) : β = 0 := by
  subst hS
  refine lk_twoPiece_lkMap (N := N) hN hK₁ hK₂ β ?_ ?_
  · rw [← lk_lkMap_congr hsub₁ Set.subset_union_left β]; exact h₁
  · rw [← lk_lkMap_congr hsub₂ Set.subset_union_right β]; exact h₂

/-! ## The main induction -/

/-- **Injectivity of the stage maps out of a union of closed balls.**  If `β ∈ LK N S` where
`S = ⋃ j, B j` is a finite union of compact convex sets, and the stage map of `β` at one point of
each `B j` vanishes, then `β = 0`. -/
theorem lk_union_injective_aux {N : ℕ} (hN : 1 ≤ N) :
    ∀ (k : ℕ) (B : Fin k → Set (EuclideanSpace ℝ (Fin N))) (S : Set (EuclideanSpace ℝ (Fin N))),
      S = (⋃ j, B j) →
      (∀ j, Convex ℝ (B j)) → (∀ j, IsCompact (B j)) →
      ∀ (x : Fin k → EuclideanSpace ℝ (Fin N)), (∀ j, x j ∈ B j) →
      ∀ (β : LK N S),
        (∀ j, ∀ (hsub : ({x j} : Set (EuclideanSpace ℝ (Fin N))) ⊆ S),
          lkMap (N := N) hsub β = 0) → β = 0 := by
  intro k
  induction k with
  | zero =>
    intro B S hS hBc hBk x hx β h
    subst hS
    have hEq : ({y : EuclideanSpace ℝ (Fin N) | y ∉ (⋃ j : Fin 0, B j)}) = Set.univ := by
      rw [Set.iUnion_of_empty]
      ext y
      simp
    have hz : IsZero (LKC N (⋃ j : Fin 0, B j)) :=
      IsZero.of_iso (isZero_relChains_univ (TopCat.of (EuclideanSpace ℝ (Fin N))) N)
        (eqToIso (congrArg (fun T =>
          (relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) T).homology N) hEq))
    exact (ModuleCat.subsingleton_of_isZero hz).elim β 0
  | succ n ih =>
    intro B S hS hBc hBk x hx β h
    set K₂ : Set (EuclideanSpace ℝ (Fin N)) := ⋃ j : Fin n, B (Fin.castSucc j) with hK₂def
    have hS' : S = B (Fin.last n) ∪ K₂ := by
      rw [hS, hK₂def]
      ext y
      simp only [Set.mem_union, Set.mem_iUnion]
      constructor
      · rintro ⟨j, hj⟩
        rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
        · exact Or.inr ⟨i, hj⟩
        · exact Or.inl hj
      · rintro (h' | ⟨i, hi⟩)
        · exact ⟨Fin.last n, h'⟩
        · exact ⟨Fin.castSucc i, hi⟩
    have hsub₁ : B (Fin.last n) ⊆ S := Set.subset_union_left.trans hS'.ge
    have hsub₂ : K₂ ⊆ S := Set.subset_union_right.trans hS'.ge
    have h₁ : lkMap (N := N) hsub₁ β = 0 :=
      (lkMap_isIso_of_convex (N := N) hN (hBk (Fin.last n)) (hBc (Fin.last n))
        ⟨x (Fin.last n), hx (Fin.last n)⟩ (hx (Fin.last n))).1 (by
          simp only [map_zero]
          rw [← LinearMap.comp_apply, lkMap_comp]
          exact h (Fin.last n) _)
    have h₂ : lkMap (N := N) hsub₂ β = 0 :=
      ih (fun j : Fin n => B (Fin.castSucc j)) K₂ hK₂def (fun j => hBc _) (fun j => hBk _)
        (fun j => x (Fin.castSucc j)) (fun j => hx _) (lkMap (N := N) hsub₂ β) (by
          intro j hsub'
          rw [← LinearMap.comp_apply, lkMap_comp]
          exact h (Fin.castSucc j) (hsub'.trans hsub₂))
    exact lk_twoPiece_lkMap' (N := N) hN (hBk (Fin.last n)).isClosed
      (by rw [hK₂def]
          exact isClosed_iUnion_of_finite (fun j : Fin n => (hBk (Fin.castSucc j)).isClosed))
      hS' hsub₁ hsub₂ β h₁ h₂

/-! ## The main theorem -/

theorem LK_closedBall_union_injective {N : ℕ} (hN : 1 ≤ N) {k : ℕ}
    (c : Fin k → EuclideanSpace ℝ (Fin N)) (r : Fin k → ℝ) (hr : ∀ j, 0 < r j)
    (x : Fin k → EuclideanSpace ℝ (Fin N))
    (hx : ∀ j, x j ∈ Metric.closedBall (c j) (r j))
    (β : Work.Cohomology.LK N (⋃ j, Metric.closedBall (c j) (r j)))
    (h : ∀ j, Work.Cohomology.lkMap (N := N)
      (Set.singleton_subset_iff.mpr (Set.mem_iUnion.mpr ⟨j, hx j⟩)) β = 0) :
    β = 0 := by
  refine lk_union_injective_aux (N := N) hN k (fun j => Metric.closedBall (c j) (r j))
    (⋃ j, Metric.closedBall (c j) (r j)) rfl ?_ ?_ x hx β ?_
  · intro j
    exact convex_closedBall (c j) (r j)
  · intro j
    exact isCompact_closedBall (c j) (r j)
  · intro j hsub
    exact (lk_lkMap_congr hsub
      (Set.singleton_subset_iff.mpr (Set.mem_iUnion.mpr ⟨j, hx j⟩)) β).trans (h j)

end

end Work.Cohomology
