import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.capped_localDegree_generator
import Submission.Work.Cohomology.pd_triple
import Submission.Work.Cohomology.homologyTwoCover
import Submission.Work.Cohomology.relChainsPairModel
import Submission.Work.Cohomology.localClass_point_injective
import Submission.Work.Cohomology.local_generator_convex
import Submission.Work.Cohomology.isZero_relSubPunctured
import Submission.Work.Cohomology.pd_small_union_iso
import Submission.Work.Cohomology.euclidean_top_homology_vanishing
import Submission.Work.Cohomology.relChains_vanishing_of_compact
import Submission.Work.Cohomology.homotopyInvariance

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable {N : ℕ}

/-- The subset `W \ S` of `ℝ^N` and the "relative complement" `pdRelSub W S` of the subtype `↥W`
are canonically homeomorphic. -/
def homeoPdRelSub (W S : Set (EuclideanSpace ℝ (Fin N))) :
    ↥(pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W S) ≃ₜ ↥(W \ S) where
  toFun y := ⟨(y : EuclideanSpace ℝ (Fin N)), y.1.2, y.2⟩
  invFun y := ⟨⟨y.1, y.2.1⟩, y.2.2⟩
  left_inv y := by ext <;> rfl
  right_inv y := by ext <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- `IsZero` of the singular homology of a space transports backwards along a homeomorphism. -/
theorem isZero_homology_of_homeo {X Y : TopCat} (e : X ≃ₜ Y) (n : ℕ)
    (h : IsZero ((singularChains ℤ Y).homology n)) : IsZero ((singularChains ℤ X).homology n) := by
  let f : X ⟶ Y := TopCat.ofHom e
  let g : Y ⟶ X := TopCat.ofHom e.symm
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 X) := e.toHomotopyEquiv.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 Y) := e.toHomotopyEquiv.right_inv.some
  haveI : IsIso (HomologicalComplex.homologyMap (chainMap ℤ X Y f) n) :=
    homologyEquiv ℤ X Y f g h1 h2 n
  exact IsZero.of_iso h (asIso (HomologicalComplex.homologyMap (chainMap ℤ X Y f) n))

/-- `H_N(W \ S) = 0` for `W ⊆ ℝ^N` open. -/
theorem isZero_homology_sdiff (hN : 1 ≤ N) {W : Set (EuclideanSpace ℝ (Fin N))} (hW : IsOpen W)
    {S : Set (EuclideanSpace ℝ (Fin N))} (hSc : IsCompact S) (hSW : S ⊆ W) :
    IsZero ((singularChains ℤ (TopCat.of ↥(W \ S))).homology N) :=
  euclidean_top_homology_vanishing hN (W \ S) (hW.sdiff hSc.isClosed)

-- Renamed from `pdRelSub_union` / `pdRelSub_inter` (Islands subproject, 2026): the names
-- `Work.Cohomology.pdRelSub_union` and `Work.Cohomology.pdRelSub_inter` are also declared in
-- `Cohomology/pd_relsub_aux.lean` and `Cohomology/pd_glue3.lean` (for a general space `M`,
-- not for `EuclideanSpace ℝ (Fin N)`), with *different* statements; Lean rejects a module
-- importing two such declarations, and the generated auxiliary lemma
-- `pdRelSub_union._simp_1_1` clashed as well.  This file keeps its (Euclidean) versions under
-- the suffix `Euclid`; statements unchanged.
/-- The complement of an intersection is the union of the complements. -/
lemma pdRelSub_unionEuclid (W S₁ S₂ : Set (EuclideanSpace ℝ (Fin N))) :
    pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W S₁ ∪
      pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W S₂
    = pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W (S₁ ∩ S₂) := by
  ext y
  simp only [Set.mem_union, pdRelSub, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_inter_iff]
  tauto

/-- The complement of a union is the intersection of the complements. -/
lemma pdRelSub_interEuclid (W S₁ S₂ : Set (EuclideanSpace ℝ (Fin N))) :
    pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W (S₁ ∪ S₂)
    = pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W S₁ ∩
      pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W S₂ := by
  ext y
  simp only [Set.mem_inter_iff, pdRelSub, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_union]
  tauto

/-- **`H_N` of the small chains of the pair of complements vanishes.** -/
theorem isZero_smallChains_pair {W : Set (EuclideanSpace ℝ (Fin N))} (hN : 1 ≤ N) (hW : IsOpen W)
    {S₁ S₂ : Set (EuclideanSpace ℝ (Fin N))} (hS₁c : IsCompact S₁) (hS₂c : IsCompact S₂)
    (hS₁W : S₁ ⊆ W) (hS₂W : S₂ ⊆ W) :
    IsZero ((smallChains (X := TopCat.of ↥W)
      (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W S₁)
      (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W S₂)).homology N) := by
  set X : TopCat := TopCat.of ↥W with hX
  set U : Set X := pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W S₁ with hU
  set V : Set X := pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W S₂ with hV
  have hUo : IsOpen U := hS₁c.isClosed.isOpen_compl.preimage continuous_subtype_val
  have hVo : IsOpen V := hS₂c.isClosed.isOpen_compl.preimage continuous_subtype_val
  obtain ⟨Φ, -, hΦ, -, -⟩ := pd_small_union_iso U V hUo hVo
  have hunion : U ∪ V
      = pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W (S₁ ∩ S₂) := by
    rw [hU, hV, pdRelSub_unionEuclid]
  haveI : IsIso (HomologicalComplex.homologyMap Φ N) := hΦ N
  refine IsZero.of_iso ?_ (asIso (HomologicalComplex.homologyMap Φ N))
  rw [hunion]
  exact isZero_homology_of_homeo (homeoPdRelSub W (S₁ ∩ S₂)) N
    (isZero_homology_sdiff hN hW (hS₁c.inter hS₂c) (fun x hx => hS₁W hx.1))

/-- **The connecting map of the pair `(W, B)` is injective in degree `N`.** -/
theorem hPairδ_injective (hN : 1 ≤ N) {W : Set (EuclideanSpace ℝ (Fin N))} (hW : IsOpen W)
    {S : Set (EuclideanSpace ℝ (Fin N))} (hSc : IsCompact S) (hSW : S ⊆ W)
    {B : Set ↥W} (hB : B = pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W S) :
    Function.Injective (ModuleCat.Hom.hom (hPairδ (TopCat.of ↥W) B (N - 1))) := by
  subst hB
  set X : TopCat := TopCat.of ↥W with hX
  set A : Set X := pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W S with hA
  have hz : IsZero ((singularChains ℤ X).homology (N - 1 + 1)) := by
    rw [Nat.sub_add_cancel hN]
    exact euclidean_top_homology_vanishing hN W hW
  have hker : (ModuleCat.Hom.hom (hPairδ X A (N - 1))).ker = ⊥ := by
    have hex := ShortComplex.Exact.moduleCat_range_eq_ker (hPair_exact₃ X A (N - 1))
    have hrange : (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (cokernel.π (inclChains X A)) (N - 1 + 1))).range
          = ⊥ := by
      rw [IsZero.eq_zero_of_src hz (HomologicalComplex.homologyMap
        (cokernel.π (inclChains X A)) (N - 1 + 1))]
      exact LinearMap.range_zero
    exact hex.symm.trans hrange
  exact LinearMap.ker_eq_bot.mp hker

/-- The canonical morphism of short complexes of the pair `(X, A) ⟶ (X, A')` for `A ⊆ A'`. -/
def hPairMap {X : TopCat} {A A' : Set X} (h : A ⊆ A') : hPairShort X A ⟶ hPairShort X A' where
  τ₁ := inclChainsSub X A A' h
  τ₂ := 𝟙 _
  τ₃ := relCokerMap X A A' h
  comm₁₂ := by rw [Category.comp_id]; exact inclChainsSub_comp X A A' h
  comm₂₃ := by rw [Category.id_comp]; exact (relCokerMap_comp_π X A A' h).symm

/-- **Naturality of the connecting map of a pair** in the subspace. -/
theorem hPairδ_naturality {X : TopCat} {A A' : Set X} (h : A ⊆ A') (n : ℕ) :
    hPairδ X A n ≫ HomologicalComplex.homologyMap (inclChainsSub X A A' h) n
      = HomologicalComplex.homologyMap (relCokerMap X A A' h) (n + 1) ≫ hPairδ X A' n :=
  HomologicalComplex.HomologySequence.δ_naturality (hPairMap h) (hPairShort_shortExact X A)
    (hPairShort_shortExact X A') (n + 1) n (by simp [ComplexShape.down])

/-- `inclChainsSub` is the first component of the Mayer–Vietoris map. -/
lemma inclChainsSub_eq_inclUVU {X : TopCat} {U V : Set X} (h : U ∩ V ⊆ U) :
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
lemma inclChainsSub_eq_inclUVV {X : TopCat} {U V : Set X} (h : U ∩ V ⊆ V) :
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

/-- **The first map of the Mayer–Vietoris sequence is injective** if `H_{n+1}` of the small
chains vanishes. -/
theorem mvLeft_ker_general {X : TopCat} {U V : Set X} (n : ℕ)
    (hvan : IsZero ((smallChains U V).homology (n + 1))) :
    LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (mvLeft U V) n)) = ⊥ := by
  have hex := ShortComplex.Exact.moduleCat_range_eq_ker (mv_H_exact₁ U V n)
  have hδ : mvδ U V n = 0 := IsZero.eq_zero_of_src hvan _
  have hrange : (ModuleCat.Hom.hom (mvδ U V n)).range = ⊥ := by
    rw [hδ]; exact LinearMap.range_zero
  exact hex.symm.trans hrange

/-- **The Mayer–Vietoris map `H_{N-1}(U ∩ V) → H_{N-1}(U) ⊞ H_{N-1}(V)` is injective**, for
`U`, `V` the complements of compact sets `S₁`, `S₂` inside an open `W ⊆ ℝ^N`. -/
theorem mvLeft_ker (hN : 1 ≤ N) {W : Set (EuclideanSpace ℝ (Fin N))} (hW : IsOpen W)
    {S₁ S₂ : Set (EuclideanSpace ℝ (Fin N))} (hS₁c : IsCompact S₁) (hS₂c : IsCompact S₂)
    (hS₁W : S₁ ⊆ W) (hS₂W : S₂ ⊆ W) :
    LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (mvLeft
      (X := TopCat.of ↥W)
      (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W S₁)
      (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W S₂)) (N - 1))) = ⊥ := by
  refine mvLeft_ker_general (N - 1) ?_
  rw [Nat.sub_add_cancel hN]
  exact isZero_smallChains_pair hN hW hS₁c hS₂c hS₁W hS₂W

/-- Application of `homologyMap` commutes with the transport of the degree. -/
lemma homologyMap_eqToHom_apply {K L : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L)
    {k k' : ℕ} (h : k = k') (x : K.homology k) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap f k'))
        ((ModuleCat.Hom.hom (eqToHom (congrArg (fun j => K.homology j) h))) x)
      = (ModuleCat.Hom.hom (eqToHom (congrArg (fun j => L.homology j) h)))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap f k)) x) := by
  subst h
  simp


/-! ## Elementwise facts about biproducts of `ℤ`-modules -/

/-- An element of a biproduct is the sum of its components. -/
lemma biprod_eq_components {A B : ModuleCat ℤ} (y : (A ⊞ B : ModuleCat ℤ)) :
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
lemma biprod_lift_eq_zero_of_components {A B C : ModuleCat ℤ} (f : A ⟶ B) (g : A ⟶ C) (z : A)
    (hf : (ModuleCat.Hom.hom f) z = 0) (hg : (ModuleCat.Hom.hom g) z = 0) :
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
  rw [biprod_eq_components ((ModuleCat.Hom.hom (biprod.lift f g)) z), h1, h2]
  simp

/-- **The component form of the injectivity of the Mayer–Vietoris map.** -/
theorem mvLeft_ker_component {X : TopCat} {U V : Set X} (n : ℕ)
    (hvan : IsZero ((smallChains U V).homology (n + 1)))
    (z : (singularChains ℤ (TopCat.of ↥(U ∩ V))).homology n)
    (h1 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map (inclUVU U V)) (ModuleCat.of ℤ ℤ)) n)) z = 0)
    (h2 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map (inclUVV U V)) (ModuleCat.of ℤ ℤ)) n)) z = 0) :
    z = 0 := by
  have hker : LinearMap.ker (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (mvLeft U V) n)) = ⊥ :=
    mvLeft_ker_general n hvan
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
    biprod_lift_eq_zero_of_components _ _ z h1 h2
  exact (congrArg (ModuleCat.Hom.hom ((Functor.mapBiprod
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n)
      (singularChains ℤ (TopCat.of U)) (singularChains ℤ (TopCat.of V))).inv)) hz).trans
    (map_zero _)



/-! ## Helper lemmas -/

lemma hom_map_congr {M N : ModuleCat ℤ} (f : M ⟶ N) {x y : M} (h : x = y) :
    (ModuleCat.Hom.hom f) x = (ModuleCat.Hom.hom f) y :=
  congrArg (fun w => (ModuleCat.Hom.hom f) w) h

lemma hom_congr {M N : ModuleCat ℤ} {f g : M ⟶ N} (h : f = g) (x : M) :
    (ModuleCat.Hom.hom f) x = (ModuleCat.Hom.hom g) x :=
  congrArg (fun φ => (ModuleCat.Hom.hom φ) x) h

/-- The component form of the injectivity of the Mayer–Vietoris map, stated with the
`inclChainsSub` models of the two inclusions. -/
theorem mvLeft_ker_component_sub {X : TopCat} {U V : Set X} {hU : U ∩ V ⊆ U} {hV : U ∩ V ⊆ V}
    (n : ℕ) (hvan : IsZero ((smallChains U V).homology (n + 1)))
    (z : (singularChains ℤ (TopCat.of ↥(U ∩ V))).homology n)
    (h1 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (inclChainsSub X (U ∩ V) U hU) n)) z = 0)
    (h2 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (inclChainsSub X (U ∩ V) V hV) n)) z = 0) :
    z = 0 := by
  refine mvLeft_ker_component (X := X) n hvan z ?_ ?_
  · rw [← inclChainsSub_eq_inclUVU (U := U) (V := V) hU]
    exact h1
  · rw [← inclChainsSub_eq_inclUVV (U := U) (V := V) hV]
    exact h2

/-! ## The two-piece lemma -/

set_option maxHeartbeats 8000000 in
/-- **The two-piece lemma.**  A class in `H_N(W, W∖(S₁ ∪ S₂))` whose images in
`H_N(W, W∖S₁)` and `H_N(W, W∖S₂)` vanish is zero. -/
theorem twoPiece_ker {W : Set (EuclideanSpace ℝ (Fin N))} (hN : 1 ≤ N) (hW : IsOpen W)
    {S₁ S₂ : Set (EuclideanSpace ℝ (Fin N))} (hS₁c : IsCompact S₁) (hS₂c : IsCompact S₂)
    (hS₁W : S₁ ⊆ W) (hS₂W : S₂ ⊆ W)
    {A A' A_a : Set ↥W} (hA : A = A' ∩ A_a)
    (hA' : A' = pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W S₁)
    (hA_a : A_a = pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W S₂)
    (h₁ : A ⊆ A') (h₂ : A ⊆ A_a)
    (β : (relChains (TopCat.of ↥W) A).homology N)
    (hh₁ : HomologicalComplex.homologyMap (relCokerMap (TopCat.of ↥W) A A' h₁) N β = 0)
    (hh₂ : HomologicalComplex.homologyMap (relCokerMap (TopCat.of ↥W) A A_a h₂) N β = 0) :
    β = 0 := by
  subst hA
  subst hA'
  subst hA_a
  let X : TopCat := TopCat.of ↥W
  let P₁ : Set ↥W := pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W S₁
  let P₂ : Set ↥W := pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W S₂
  have hAunion : P₁ ∩ P₂
      = pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W (S₁ ∪ S₂) :=
    (pdRelSub_interEuclid W S₁ S₂).symm
  have hinj : Function.Injective (ModuleCat.Hom.hom (hPairδ X (P₁ ∩ P₂) (N - 1))) :=
    hPairδ_injective hN hW (hS₁c.union hS₂c) (Set.union_subset hS₁W hS₂W) hAunion
  have hsmall : IsZero ((smallChains (X := X) P₁ P₂).homology (N - 1 + 1)) := by
    rw [Nat.sub_add_cancel hN]
    exact isZero_smallChains_pair hN hW hS₁c hS₂c hS₁W hS₂W
  have hsub : N - 1 + 1 = N := Nat.sub_add_cancel hN
  let β' : (relChains X (P₁ ∩ P₂)).homology (N - 1 + 1) :=
    (ModuleCat.Hom.hom (eqToHom (congrArg (fun j => (relChains X (P₁ ∩ P₂)).homology j)
      hsub.symm))) β
  have hh₁' : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relCokerMap X (P₁ ∩ P₂) P₁ h₁) (N - 1 + 1))) β' = 0 := by
    exact (homologyMap_eqToHom_apply (relCokerMap X (P₁ ∩ P₂) P₁ h₁) hsub.symm β).trans
      (by rw [hh₁, map_zero])
  have hh₂' : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relCokerMap X (P₁ ∩ P₂) P₂ h₂) (N - 1 + 1))) β' = 0 := by
    exact (homologyMap_eqToHom_apply (relCokerMap X (P₁ ∩ P₂) P₂ h₂) hsub.symm β).trans
      (by rw [hh₂, map_zero])
  let z : (singularChains ℤ (TopCat.of ↥(P₁ ∩ P₂))).homology (N - 1) :=
    (ModuleCat.Hom.hom (hPairδ X (P₁ ∩ P₂) (N - 1))) β'
  have hcomp₁ : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (inclChainsSub X (P₁ ∩ P₂) P₁ h₁) (N - 1))) z = 0 := by
    have hnat := congrArg (fun (φ : (relChains X (P₁ ∩ P₂)).homology (N - 1 + 1) ⟶
        (singularChains ℤ (TopCat.of ↥P₁)).homology (N - 1)) => (ModuleCat.Hom.hom φ) β')
      (hPairδ_naturality (X := X) (A := P₁ ∩ P₂) (A' := P₁) h₁ (N - 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
    exact hnat.trans ((hom_map_congr (hPairδ X P₁ (N - 1)) hh₁').trans (map_zero _))
  have hcomp₂ : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (inclChainsSub X (P₁ ∩ P₂) P₂ h₂) (N - 1))) z = 0 := by
    have hnat := congrArg (fun (φ : (relChains X (P₁ ∩ P₂)).homology (N - 1 + 1) ⟶
        (singularChains ℤ (TopCat.of ↥P₂)).homology (N - 1)) => (ModuleCat.Hom.hom φ) β')
      (hPairδ_naturality (X := X) (A := P₁ ∩ P₂) (A' := P₂) h₂ (N - 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
    exact hnat.trans ((hom_map_congr (hPairδ X P₂ (N - 1)) hh₂').trans (map_zero _))
  have hz0 : z = 0 :=
    mvLeft_ker_component_sub (X := X) (U := P₁) (V := P₂) (hU := h₁) (hV := h₂)
      (N - 1) hsmall z hcomp₁ hcomp₂
  have hβ'0 : β' = 0 := by
    have h1 : (ModuleCat.Hom.hom (hPairδ X (P₁ ∩ P₂) (N - 1))) β' = 0 := by
      change z = 0
      exact hz0
    exact hinj (h1.trans ((ModuleCat.Hom.hom (hPairδ X (P₁ ∩ P₂) (N - 1))).map_zero).symm)
  have hBA : eqToHom (congrArg (fun j => (relChains X (P₁ ∩ P₂)).homology j) hsub.symm)
      ≫ eqToHom (congrArg (fun j => (relChains X (P₁ ∩ P₂)).homology j) hsub) = 𝟙 _ :=
    (eqToHom_trans (congrArg (fun j => (relChains X (P₁ ∩ P₂)).homology j) hsub.symm)
      (congrArg (fun j => (relChains X (P₁ ∩ P₂)).homology j) hsub)).trans (eqToHom_refl _ _)
  have htrans : (ModuleCat.Hom.hom (eqToHom (congrArg
      (fun j => (relChains X (P₁ ∩ P₂)).homology j) hsub))) β' = β := by
    show (ModuleCat.Hom.hom (eqToHom (congrArg (fun j => (relChains X (P₁ ∩ P₂)).homology j) hsub)))
        ((ModuleCat.Hom.hom (eqToHom (congrArg (fun j => (relChains X (P₁ ∩ P₂)).homology j)
          hsub.symm))) β) = β
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, hBA, ModuleCat.hom_id]
    rfl
  rw [← htrans, hβ'0, map_zero]

/-- The composite of the relative restriction maps, on homology classes. -/
lemma homologyMap_relCokerMap_fac {X : TopCat} {A A' A'' : Set X} (h₁ : A ⊆ A') (h₂ : A' ⊆ A'')
    (n : ℕ) (β : (relChains X A).homology n) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (relCokerMap X A' A'' h₂) n))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (relCokerMap X A A' h₁) n)) β)
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (relCokerMap X A A'' (h₁.trans h₂)) n)) β := by
  exact (ModuleCat.comp_apply (HomologicalComplex.homologyMap (relCokerMap X A A' h₁) n)
      (HomologicalComplex.homologyMap (relCokerMap X A' A'' h₂) n) β).symm.trans
    (hom_congr (homologyMap_relCokerMap_comp (X := X) h₁ h₂ n) β)

/-- **The local class of a class of `H_N(W,A)` at a compact convex set.**  If `A ⊆ W∖B`, if `B` is
compact and convex in the open set `W`, and if a class of `H_N(W,A)` dies at a point `x ∈ B`, then
it dies in `H_N(W, W∖B)`. -/
theorem dies_of_dies_at_point {N : ℕ} (hN : 1 ≤ N)
    {W : Set (EuclideanSpace ℝ (Fin N))} (hW : IsOpen W)
    {B : Set (EuclideanSpace ℝ (Fin N))} (hBc : IsCompact B) (hBv : Convex ℝ B) (hBW : B ⊆ W)
    {x : EuclideanSpace ℝ (Fin N)} (hxB : x ∈ B)
    {A : Set ↥W} (h₁ : A ⊆ pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W B)
    (h₂ : pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W B
      ⊆ pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W
        ({x} : Set (EuclideanSpace ℝ (Fin N))))
    (β : (relChains (TopCat.of ↥W) A).homology N)
    (hβ : HomologicalComplex.homologyMap (relCokerMap (TopCat.of ↥W) A
        (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W
          ({x} : Set (EuclideanSpace ℝ (Fin N)))) (h₁.trans h₂)) N β = 0) :
    HomologicalComplex.homologyMap (relCokerMap (TopCat.of ↥W) A
      (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W B) h₁) N β = 0 := by
  refine localClass_point_injective (N := N) hN hW hBc hBv hBW hxB
    (HomologicalComplex.homologyMap (relCokerMap (TopCat.of ↥W) A
      (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W B) h₁) N β) ?_
  exact (homologyMap_relCokerMap_fac (X := TopCat.of ↥W) h₁ h₂ N β).trans hβ

set_option maxHeartbeats 8000000 in
/-- **A class of `H_N(W, W∖⋃ᵢ Bᵢ)` which dies at each point `xᵢ ∈ Bᵢ` is zero**, for a finite
family of compact convex sets `Bᵢ ⊆ W ⊆ ℝ^N`. -/
theorem localClass_union_injective {N : ℕ} (hN : 1 ≤ N)
    {W : Set (EuclideanSpace ℝ (Fin N))} (hW : IsOpen W)
    {ι : Type} (s : Finset ι) (B : ι → Set (EuclideanSpace ℝ (Fin N)))
    (x : ι → EuclideanSpace ℝ (Fin N))
    (hBc : ∀ i ∈ s, IsCompact (B i)) (hBv : ∀ i ∈ s, Convex ℝ (B i))
    (hBW : ∀ i ∈ s, B i ⊆ W) (hxB : ∀ i ∈ s, x i ∈ B i)
    (β : (relChains (TopCat.of ↥W)
      (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W (⋃ i ∈ s, B i))).homology N)
    (h : ∀ i (hi : i ∈ s), HomologicalComplex.homologyMap
          (relCokerMap (TopCat.of ↥W)
            (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W (⋃ i ∈ s, B i))
            (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W ({x i} : Set (EuclideanSpace ℝ (Fin N))))
            (pdRelSub_mono (M := TopCat.of (EuclideanSpace ℝ (Fin N)))
              (Set.singleton_subset_iff.mpr (Set.mem_iUnion₂.mpr ⟨i, hi, hxB i hi⟩)))) N β = 0) :
    β = 0 := by
  classical
  have key : ∀ t : Finset ι, (hBct : ∀ i ∈ t, IsCompact (B i)) → (hBvt : ∀ i ∈ t, Convex ℝ (B i)) →
      (hBWt : ∀ i ∈ t, B i ⊆ W) → (hxBt : ∀ i ∈ t, x i ∈ B i) →
      ∀ (β : (relChains (TopCat.of ↥W)
          (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W (⋃ i ∈ t, B i))).homology N),
      (∀ i (hi : i ∈ t), HomologicalComplex.homologyMap
          (relCokerMap (TopCat.of ↥W)
            (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W (⋃ i ∈ t, B i))
            (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W
              ({x i} : Set (EuclideanSpace ℝ (Fin N))))
            (pdRelSub_mono (M := TopCat.of (EuclideanSpace ℝ (Fin N)))
              (Set.singleton_subset_iff.mpr (Set.mem_iUnion₂.mpr ⟨i, hi, hxBt i hi⟩)))) N β = 0) →
      β = 0 := by
    intro t
    induction t using Finset.induction with
    | empty =>
      intro _hBct _hBvt _hBWt _hxBt β _hβ
      have huniv : (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W
          (⋃ i ∈ (∅ : Finset ι), B i) : Set ↥W) = Set.univ := by
        have hU : (⋃ i ∈ (∅ : Finset ι), B i) = (∅ : Set (EuclideanSpace ℝ (Fin N))) := by
          ext y; simp
        rw [hU]
        ext y; simp [pdRelSub]
      haveI hz : IsZero ((relChains (TopCat.of ↥W)
          (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W
            (⋃ i ∈ (∅ : Finset ι), B i))).homology N) := by
        rw [huniv]
        exact isZero_relChains_univ (TopCat.of ↥W) N
      exact (ModuleCat.subsingleton_of_isZero hz).elim β 0
    | insert a t' ha ih =>
      intro hBct hBvt hBWt hxBt β hβ
      have hU : (⋃ i ∈ insert a t', B i) = B a ∪ ⋃ i ∈ t', B i := by
        ext y
        simp only [Set.mem_iUnion, Set.mem_union, Finset.mem_insert]
        constructor
        · rintro ⟨i, hi, hy⟩
          rcases hi with rfl | hi
          · exact Or.inl hy
          · exact Or.inr ⟨i, hi, hy⟩
        · rintro (hy | ⟨i, hi, hy⟩)
          · exact ⟨a, Or.inl rfl, hy⟩
          · exact ⟨i, Or.inr hi, hy⟩
      have hS₁c : IsCompact (B a) := hBct a (Finset.mem_insert_self a t')
      have hS₂c : IsCompact (⋃ i ∈ t', B i) :=
        Finset.isCompact_biUnion t' (fun i hi => hBct i (Finset.mem_insert_of_mem hi))
      have hS₁W : B a ⊆ W := hBWt a (Finset.mem_insert_self a t')
      have hS₂W : (⋃ i ∈ t', B i) ⊆ W := by
        intro y hy
        obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hy
        obtain ⟨hi, hyi⟩ := Set.mem_iUnion.mp hyi
        exact hBWt i (Finset.mem_insert_of_mem hi) hyi
      have hA : (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W
            (⋃ i ∈ insert a t', B i))
          = (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W (B a))
            ∩ (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W (⋃ i ∈ t', B i)) := by
        rw [hU]
        exact pdRelSub_interEuclid W (B a) (⋃ i ∈ t', B i)
      have h₁ : (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W (⋃ i ∈ insert a t', B i))
          ⊆ pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W (B a) :=
        hA.le.trans Set.inter_subset_left
      have h₂ : (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W (⋃ i ∈ insert a t', B i))
          ⊆ pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W (⋃ i ∈ t', B i) :=
        hA.le.trans Set.inter_subset_right
      have hh₁ : HomologicalComplex.homologyMap (relCokerMap (TopCat.of ↥W)
          (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W (⋃ i ∈ insert a t', B i))
          (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W (B a)) h₁) N β = 0 :=
        dies_of_dies_at_point (N := N) hN hW (hBct a (Finset.mem_insert_self a t'))
          (hBvt a (Finset.mem_insert_self a t')) (hBWt a (Finset.mem_insert_self a t'))
          (hxBt a (Finset.mem_insert_self a t')) h₁
          (pdRelSub_mono (M := TopCat.of (EuclideanSpace ℝ (Fin N)))
            (Set.singleton_subset_iff.mpr (hxBt a (Finset.mem_insert_self a t'))))
          β (hβ a (Finset.mem_insert_self a t'))
      have hh₂ : HomologicalComplex.homologyMap (relCokerMap (TopCat.of ↥W)
          (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W (⋃ i ∈ insert a t', B i))
          (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W (⋃ i ∈ t', B i)) h₂) N β = 0 := by
        refine ih (fun i hi => hBct i (Finset.mem_insert_of_mem hi))
          (fun i hi => hBvt i (Finset.mem_insert_of_mem hi))
          (fun i hi => hBWt i (Finset.mem_insert_of_mem hi))
          (fun i hi => hxBt i (Finset.mem_insert_of_mem hi))
          (HomologicalComplex.homologyMap (relCokerMap (TopCat.of ↥W)
            (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W (⋃ i ∈ insert a t', B i))
            (pdRelSub (M := TopCat.of (EuclideanSpace ℝ (Fin N))) W (⋃ i ∈ t', B i)) h₂) N β) ?_
        intro i hi
        exact (homologyMap_relCokerMap_fac (X := TopCat.of ↥W) h₂
            (pdRelSub_mono (M := TopCat.of (EuclideanSpace ℝ (Fin N)))
              (Set.singleton_subset_iff.mpr
                (Set.mem_iUnion₂.mpr ⟨i, hi, hxBt i (Finset.mem_insert_of_mem hi)⟩))) N β).trans
          (hβ i (Finset.mem_insert_of_mem hi))
      exact twoPiece_ker (W := W) hN hW (S₁ := B a) (S₂ := ⋃ i ∈ t', B i)
        hS₁c hS₂c hS₁W hS₂W hA rfl rfl h₁ h₂ β hh₁ hh₂
  exact key s hBc hBv hBW hxB β h

end

end Work.Cohomology
