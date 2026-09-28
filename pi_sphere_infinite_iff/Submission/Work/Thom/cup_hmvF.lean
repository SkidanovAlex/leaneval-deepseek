import Mathlib
import Submission.Work.Thom.transgressionFleetDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Work.Thom

open CategoryTheory CategoryTheory.Limits Work.Cohomology
open scoped Simplicial

noncomputable section

/-!
# Naturality of the cup product with respect to the first map of the relative
  Mayer–Vietoris sequence

This file proves `cup_hmvF`: the cup product with a relative cochain `t` (in
`relKern ℤ X A n`) is natural with respect to the first map `hmvF` of the relative
Mayer–Vietoris sequence.  The proof splits the statement into its two components
(the `U`- and the `V`-part), reduces each component to (i) the defining property
of the descended cup map, (ii) the commutation of `hmvF` with the projections
onto the small chains, and (iii) naturality of the Alexander–Whitney cup product
under a map of simplicial sets.
-/

/-! ## 1. Basic tool: evaluating the dual of a chain map on a functional -/

/-- The transpose of a chain map, applied to a functional, is precomposition. -/
theorem dualComplexMap_apply_hom {C D : ChainComplex (ModuleCat ℤ) ℕ} (f : C ⟶ D) (n : ℕ)
    (φ : (dualComplex ℤ D).X n) :
    ModuleCat.Hom.hom ((dualComplexMap ℤ C D f).f n) φ = φ.comp ((f.f n).hom) := rfl

/-! ## 2. Naturality of the Alexander–Whitney cup product -/

/-- **Naturality of `cupHom` under a map of simplicial sets.** -/
theorem cupHom_chainComplexMap {S T : SSet} (g : S ⟶ T) {n m : ℕ}
    (α : ((T.chainComplex (ModuleCat.of ℤ ℤ)).X n →ₗ[ℤ] ℤ))
    (β : ((T.chainComplex (ModuleCat.of ℤ ℤ)).X m →ₗ[ℤ] ℤ)) :
    (SSet.chainComplexMap g (ModuleCat.of ℤ ℤ)).f (n + m) ≫ cupHom ℤ T α β
      = cupHom ℤ S
          (α.comp ((SSet.chainComplexMap g (ModuleCat.of ℤ ℤ)).f n).hom)
          (β.comp ((SSet.chainComplexMap g (ModuleCat.of ℤ ℤ)).f m).hom) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  rw [ιChainComplex_cupHom, ιChainComplex_cupHom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul]
  have hf : frontFace T n (n + m) (Nat.le_add_right n m)
      ((ConcreteCategory.hom (g.app (Opposite.op ⦋n + m⦌))) σ)
      = (ConcreteCategory.hom (g.app (Opposite.op ⦋n⦌)))
          (frontFace S n (n + m) (Nat.le_add_right n m) σ) := by
    simp only [frontFace]
    exact (CategoryTheory.NatTrans.naturality_apply g
      (Opposite.op (frontIncl n (n + m) (Nat.le_add_right n m))) σ).symm
  have hb : backFace T n m ((ConcreteCategory.hom (g.app (Opposite.op ⦋n + m⦌))) σ)
      = (ConcreteCategory.hom (g.app (Opposite.op ⦋m⦌))) (backFace S n m σ) := by
    simp only [backFace]
    exact (CategoryTheory.NatTrans.naturality_apply g (Opposite.op (backIncl n m)) σ).symm
  rw [hf, hb, ← genEval_dualMap, ← genEval_dualMap]
  rfl

/-! ## 3. Restricting a cochain to the small simplices lying in a set -/

/-- The restriction `restrIn X U V B n t` to the small simplices lying in `B` is the
restriction of `restrSmall X U V n t` along the inclusion of the simplices lying in `B`. -/
theorem restrIn_eq_dualMap (X : TopCat) (U V B : Set X) (n : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) :
    (dualComplexMap ℤ (smallInChains U V B) (smallChains U V) (smallInToSmall U V B)).f n
        (restrSmall X U V n t) = restrIn X U V B n t := by
  have hcomp : SSet.chainComplexMap (smallInSubcomplex U V B).ι (ModuleCat.of ℤ ℤ)
      = smallInToSmall U V B ≫ smallToSing U V := by
    rw [show (smallInSubcomplex U V B).ι
        = Subfunctor.homOfLe (smallInSubcomplex_le U V B) ≫ (smallSubcomplex U V).ι
        from (Subfunctor.homOfLe_ι _).symm]
    unfold SSet.chainComplexMap
    rw [Functor.map_comp]
    rfl
  change ((dualComplexMap ℤ (smallChains U V) (singularChains ℤ X) (smallToSing U V)).f n
      ≫ (dualComplexMap ℤ (smallInChains U V B) (smallChains U V) (smallInToSmall U V B)).f n)
        t = (dualComplexMap ℤ (smallInChains U V B) (singularChains ℤ X)
              (SSet.chainComplexMap (smallInSubcomplex U V B).ι (ModuleCat.of ℤ ℤ))).f n t
  rw [← HomologicalComplex.comp_f, ← dualComplexMap_comp, hcomp]

/-- The composite of `restrSmall` with the inclusion of the small simplices lying in `B`. -/
theorem restrSmall_comp (X : TopCat) (U V B : Set X) (n : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) :
    (restrSmall X U V n t).comp
        ((SSet.chainComplexMap (Subfunctor.homOfLe (smallInSubcomplex_le U V B))
          (ModuleCat.of ℤ ℤ)).f n).hom
      = restrIn X U V B n t := by
  rw [← dualComplexMap_apply_hom
    (SSet.chainComplexMap (Subfunctor.homOfLe (smallInSubcomplex_le U V B))
      (ModuleCat.of ℤ ℤ)) n (restrSmall X U V n t)]
  exact restrIn_eq_dualMap X U V B n t

/-! ## 4. The four "cup with `t`" maps, in the form used below -/

/-- The second factor of `cupTop`: the descent of the cup product to `C^{U,V}(X,A)`. -/
noncomputable def cupTopDesc (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n) :
    (dualComplex ℤ (smallChains U V)).X p ⟶ (dualComplex ℤ (relMVTopC X A U V)).X (p + n) :=
  ModuleCat.ofHom
    { toFun := fun ψ => ModuleCat.Hom.hom (cupDescendMor X A U V n p t ht ψ)
      map_add' := fun ψ ψ' => by rw [cupDescendMor_add, ModuleCat.hom_add]
      map_smul' := fun a ψ => by rw [cupDescendMor_smul, ModuleCat.hom_smul]; rfl }

/-- `cupTop` factors through `cupTopDesc`. -/
theorem cupTop_eq (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n) :
    cupTop X A U V n p t ht
      = (dualComplexMap ℤ (smallChains U V) (relMVTopC X ∅ U V)
          (cokernel.π (smallInToSmall U V ∅))).f p ≫ cupTopDesc X A U V n p t ht := rfl

/-- Cup with `restrSmall t`, as a map on the duals of the small chains. -/
noncomputable def cupSmallCochain (X : TopCat) (U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) :
    (dualComplex ℤ (smallChains U V)).X p ⟶ (dualComplex ℤ (smallChains U V)).X (p + n) :=
  ModuleCat.ofHom
    { toFun := fun ψ => cup ℤ (smallSSet U V) ψ (restrSmall X U V n t)
      map_add' := fun ψ ψ' => (cupBilinear ℤ (smallSSet U V) p n).1 ψ ψ' (restrSmall X U V n t)
      map_smul' := fun a ψ => (cupBilinear ℤ (smallSSet U V) p n).2.1 a ψ (restrSmall X U V n t) }

/-- Cup with `restrIn t`, as a map on the duals of the small chains lying in `B`. -/
noncomputable def cupInCochain (X : TopCat) (U V B : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) :
    (dualComplex ℤ (smallInChains U V B)).X p
      ⟶ (dualComplex ℤ (smallInChains U V B)).X (p + n) :=
  ModuleCat.ofHom
    { toFun := fun ψ => cup ℤ (smallInSSet U V B) ψ (restrIn X U V B n t)
      map_add' := fun ψ ψ' => (cupBilinear ℤ (smallInSSet U V B) p n).1 ψ ψ' (restrIn X U V B n t)
      map_smul' := fun a ψ => (cupBilinear ℤ (smallInSSet U V B) p n).2.1 a ψ (restrIn X U V B n t) }

/-! ## 5. The three key identities -/

/-- **The descent of the cup product commutes with the projection to `C^{U,V}(X,A)`.** -/
theorem cupTopDesc_comp (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n) :
    cupTopDesc X A U V n p t ht
      ≫ (dualComplexMap ℤ (smallChains U V) (relMVTopC X A U V)
          (cokernel.π (smallInToSmall U V A))).f (p + n)
      = cupSmallCochain X U V n p t := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro ψ
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, dualComplexMap_apply_hom]
  change ModuleCat.Hom.hom ((cokernel.π (smallInToSmall U V A)).f (p + n)
        ≫ cupDescendMor X A U V n p t ht ψ) = _
  rw [cupDescendMor_spec]
  rfl

/-- **The descent to `C^{U,V}(U,U∩A)` commutes with the projection**, `U`-component. -/
theorem cupDescendRel_compU (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n) :
    cupDescendRel X U V (Set.inter_subset_left : U ∩ A ⊆ U) n p t
        (relKern_mono (Set.inter_subset_right : U ∩ A ⊆ A) ht)
      ≫ (dualComplexMap ℤ (smallInChains U V U) (relMVUU X A U V)
          (cokernel.π (relMVτ₂U U V A))).f (p + n)
      = cupInCochain X U V U n p t := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro ψ
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, dualComplexMap_apply_hom,
    cupDescendRel_apply]
  change ModuleCat.Hom.hom ((cokernel.π (subInclChain U V
        (Set.inter_subset_left : U ∩ A ⊆ U))).f (p + n)
        ≫ cupDescendRelMor X U V (Set.inter_subset_left : U ∩ A ⊆ U) n p t
            (relKern_mono (Set.inter_subset_right : U ∩ A ⊆ A) ht) ψ) = _
  rw [cupDescendRelMor_spec]
  rfl

/-- **The descent to `C^{U,V}(V,V∩A)` commutes with the projection**, `V`-component. -/
theorem cupDescendRel_compV (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n) :
    cupDescendRel X U V (Set.inter_subset_left : V ∩ A ⊆ V) n p t
        (relKern_mono (Set.inter_subset_right : V ∩ A ⊆ A) ht)
      ≫ (dualComplexMap ℤ (smallInChains U V V) (relMVVV X A U V)
          (cokernel.π (relMVτ₂V U V A))).f (p + n)
      = cupInCochain X U V V n p t := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro ψ
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, dualComplexMap_apply_hom,
    cupDescendRel_apply]
  change ModuleCat.Hom.hom ((cokernel.π (subInclChain U V
        (Set.inter_subset_left : V ∩ A ⊆ V))).f (p + n)
        ≫ cupDescendRelMor X U V (Set.inter_subset_left : V ∩ A ⊆ V) n p t
            (relKern_mono (Set.inter_subset_right : V ∩ A ⊆ A) ht) ψ) = _
  rw [cupDescendRelMor_spec]
  rfl

/-- **Naturality of the cup-with-`restrSmall t` map** under the inclusion of the small
simplices lying in `B`. -/
theorem cupSmall_comp (X : TopCat) (U V B : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) :
    cupSmallCochain X U V n p t
      ≫ (dualComplexMap ℤ (smallInChains U V B) (smallChains U V)
          (smallInToSmall U V B)).f (p + n)
      = (dualComplexMap ℤ (smallInChains U V B) (smallChains U V)
          (smallInToSmall U V B)).f p ≫ cupInCochain X U V B n p t := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro ψ
  apply LinearMap.ext; intro w
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    dualComplexMap_apply_hom, dualComplexMap_apply_hom, LinearMap.comp_apply]
  have h1 := congrArg (fun (m : (smallInChains U V B).X (p + n) ⟶ ModuleCat.of ℤ ℤ) =>
        ModuleCat.Hom.hom m w)
      (cupHom_chainComplexMap (g := Subfunctor.homOfLe (smallInSubcomplex_le U V B))
        (α := ψ) (β := restrSmall X U V n t))
  rw [restrSmall_comp] at h1
  exact h1

/-! ## 5b. Canonical forms of `cupU` and `cupV` (unfolding `relMVτ₂U`, `relMVτ₂V`) -/

/-- The defining body of `cupU`, with the cokernel written explicitly. -/
theorem cupU_eq_can (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n) :
    cupU X A U V n p t ht
      = (dualComplexMap ℤ (smallInChains U V U) (cokernel (relMVτ₂U U V ∅))
            (cokernel.π (relMVτ₂U U V ∅))).f p
          ≫ cupDescendRel X U V (Set.inter_subset_left : U ∩ A ⊆ U) n p t
              (relKern_mono (Set.inter_subset_right : U ∩ A ⊆ A) ht) := rfl

/-- The defining body of `cupV`, with the cokernel written explicitly. -/
theorem cupV_eq_can (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n) :
    cupV X A U V n p t ht
      = (dualComplexMap ℤ (smallInChains U V V) (cokernel (relMVτ₂V U V ∅))
            (cokernel.π (relMVτ₂V U V ∅))).f p
          ≫ cupDescendRel X U V (Set.inter_subset_left : V ∩ A ⊆ V) n p t
              (relKern_mono (Set.inter_subset_right : V ∩ A ⊆ A) ht) := rfl

/-! ## 6. A general form of the degreewise biproduct computation -/

/-- The degreewise component of a `biprod.lift`, conjugated by the degreewise biproduct
isomorphism. -/
lemma biprod_lift_f_comp_biprodXIso_hom_gen {C : Type*} [Category C] [Preadditive C]
    {ι : Type*} {c : ComplexShape ι} {K L M : HomologicalComplex C c}
    [∀ i, HasBinaryBiproduct (K.X i) (L.X i)]
    (α : M ⟶ K) (β : M ⟶ L) (n : ι) :
    (biprod.lift α β).f n ≫ (HomologicalComplex.biprodXIso K L n).hom
      = biprod.lift (α.f n) (β.f n) := by
  apply biprod.hom_ext
  · rw [Category.assoc, HomologicalComplex.biprodXIso_hom_fst,
      HomologicalComplex.biprod_lift_fst_f, biprod.lift_fst]
  · rw [Category.assoc, HomologicalComplex.biprodXIso_hom_snd,
      HomologicalComplex.biprod_lift_snd_f, biprod.lift_snd]

/-- A `biprod.lift` composed with a `biprod.map` is the lift of the components. -/
lemma biprod_lift_comp_map {C : Type*} [Category C] [Preadditive C] {W X Y Z T : C}
    [HasBinaryBiproduct X Y] [HasBinaryBiproduct Z T]
    (a : W ⟶ X) (b : W ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ T) :
    biprod.lift a b ≫ biprod.map f g = biprod.lift (a ≫ f) (b ≫ g) := by
  apply biprod.hom_ext <;> simp [Category.assoc]

/-! ## 7. The two components of the naturality square -/

/-- **The `U`-component**: `hmvF ∘ cupTop = cupU` after projecting. -/
theorem cupTop_alphaU (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n) :
    cupTop X A U V n p t ht
        ≫ (dualComplexMap ℤ (relMVUU X A U V) (relMVTopC X A U V)
            (HMV.alphaU X A U V)).f (p + n)
      = (dualComplexMap ℤ (relMVUU X ∅ U V) (relMVTopC X ∅ U V)
            (HMV.alphaU X ∅ U V)).f p
          ≫ cupU X A U V n p t ht := by
  haveI hmono : Mono ((dualComplexMap ℤ (smallInChains U V U) (relMVUU X A U V)
      (cokernel.π (relMVτ₂U U V A))).f (p + n)) := by
    rw [dualComplexMap_f, ModuleCat.mono_iff_injective]
    exact LinearMap.dualMap_injective_of_surjective
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  refine (cancel_mono ((dualComplexMap ℤ (smallInChains U V U) (relMVUU X A U V)
      (cokernel.π (relMVτ₂U U V A))).f (p + n))).mp ?_
  have hα : (dualComplexMap ℤ (relMVUU X A U V) (relMVTopC X A U V)
              (HMV.alphaU X A U V)).f (p + n)
          ≫ (dualComplexMap ℤ (smallInChains U V U) (relMVUU X A U V)
              (cokernel.π (relMVτ₂U U V A))).f (p + n)
        = (dualComplexMap ℤ (smallChains U V) (relMVTopC X A U V)
            (cokernel.π (smallInToSmall U V A))).f (p + n)
          ≫ (dualComplexMap ℤ (smallInChains U V U) (smallChains U V)
              (smallInToSmall U V U)).f (p + n) := by
    rw [← HomologicalComplex.comp_f, ← dualComplexMap_comp, HMV.alphaU_comp,
      dualComplexMap_comp, HomologicalComplex.comp_f]
  have hβ : (dualComplexMap ℤ (relMVUU X ∅ U V) (relMVTopC X ∅ U V)
              (HMV.alphaU X ∅ U V)).f p
          ≫ (dualComplexMap ℤ (smallInChains U V U) (relMVUU X ∅ U V)
              (cokernel.π (relMVτ₂U U V ∅))).f p
        = (dualComplexMap ℤ (smallChains U V) (relMVTopC X ∅ U V)
            (cokernel.π (smallInToSmall U V ∅))).f p
          ≫ (dualComplexMap ℤ (smallInChains U V U) (smallChains U V)
              (smallInToSmall U V U)).f p := by
    rw [← HomologicalComplex.comp_f, ← dualComplexMap_comp, HMV.alphaU_comp,
      dualComplexMap_comp, HomologicalComplex.comp_f]
  rw [Category.assoc]
  conv_lhs => rw [hα]
  conv_lhs => rw [cupTop_eq]
  conv_lhs => rw [Category.assoc]
  conv_lhs => arg 2; rw [← Category.assoc]
  rw [cupTopDesc_comp, cupSmall_comp]
  rw [cupU]
  simp only [Category.assoc]
  rw [cupDescendRel_compU X A U V n p t ht]
  conv_rhs => rw [← Category.assoc]
  rw [hβ]
  rw [Category.assoc]

/-- **The `V`-component**: `hmvF ∘ cupTop = cupV` after projecting. -/
theorem cupTop_alphaV (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n) :
    cupTop X A U V n p t ht
        ≫ (dualComplexMap ℤ (relMVVV X A U V) (relMVTopC X A U V)
            (HMV.alphaV X A U V)).f (p + n)
      = (dualComplexMap ℤ (relMVVV X ∅ U V) (relMVTopC X ∅ U V)
            (HMV.alphaV X ∅ U V)).f p
          ≫ cupV X A U V n p t ht := by
  haveI hmono : Mono ((dualComplexMap ℤ (smallInChains U V V) (relMVVV X A U V)
      (cokernel.π (relMVτ₂V U V A))).f (p + n)) := by
    rw [dualComplexMap_f, ModuleCat.mono_iff_injective]
    exact LinearMap.dualMap_injective_of_surjective
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  refine (cancel_mono ((dualComplexMap ℤ (smallInChains U V V) (relMVVV X A U V)
      (cokernel.π (relMVτ₂V U V A))).f (p + n))).mp ?_
  have hα : (dualComplexMap ℤ (relMVVV X A U V) (relMVTopC X A U V)
              (HMV.alphaV X A U V)).f (p + n)
          ≫ (dualComplexMap ℤ (smallInChains U V V) (relMVVV X A U V)
              (cokernel.π (relMVτ₂V U V A))).f (p + n)
        = (dualComplexMap ℤ (smallChains U V) (relMVTopC X A U V)
            (cokernel.π (smallInToSmall U V A))).f (p + n)
          ≫ (dualComplexMap ℤ (smallInChains U V V) (smallChains U V)
              (smallInToSmall U V V)).f (p + n) := by
    rw [← HomologicalComplex.comp_f, ← dualComplexMap_comp, HMV.alphaV_comp,
      dualComplexMap_comp, HomologicalComplex.comp_f]
  have hβ : (dualComplexMap ℤ (relMVVV X ∅ U V) (relMVTopC X ∅ U V)
              (HMV.alphaV X ∅ U V)).f p
          ≫ (dualComplexMap ℤ (smallInChains U V V) (relMVVV X ∅ U V)
              (cokernel.π (relMVτ₂V U V ∅))).f p
        = (dualComplexMap ℤ (smallChains U V) (relMVTopC X ∅ U V)
            (cokernel.π (smallInToSmall U V ∅))).f p
          ≫ (dualComplexMap ℤ (smallInChains U V V) (smallChains U V)
              (smallInToSmall U V V)).f p := by
    rw [← HomologicalComplex.comp_f, ← dualComplexMap_comp, HMV.alphaV_comp,
      dualComplexMap_comp, HomologicalComplex.comp_f]
  rw [Category.assoc]
  conv_lhs => rw [hα]
  conv_lhs => rw [cupTop_eq]
  conv_lhs => rw [Category.assoc]
  conv_lhs => arg 2; rw [← Category.assoc]
  rw [cupTopDesc_comp, cupSmall_comp]
  rw [cupV]
  simp only [Category.assoc]
  rw [cupDescendRel_compV X A U V n p t ht]
  conv_rhs => rw [← Category.assoc]
  rw [hβ]
  rw [Category.assoc]

/-! ## 8. The main theorem -/

theorem cup_hmvF (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ Work.Cohomology.relKern ℤ X A n)
    (ψ : (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X ∅ U V)).X p) :
    ModuleCat.Hom.hom ((Work.Cohomology.hmvF X A U V).f (p + n))
        (ModuleCat.Hom.hom (Work.Thom.cupTop X A U V n p t ht) ψ)
      = ModuleCat.Hom.hom (Work.Thom.cupMid X A U V n p t ht)
          (ModuleCat.Hom.hom ((Work.Cohomology.hmvF X ∅ U V).f p) ψ) := by
  have hm : cupTop X A U V n p t ht ≫ (hmvF X A U V).f (p + n)
      = (hmvF X ∅ U V).f p ≫ cupMid X A U V n p t ht := by
    rw [hmvF, hmvF]
    rw [show cupMid X A U V n p t ht
        = (HomologicalComplex.biprodXIso (dualComplex ℤ (relMVUU X ∅ U V))
              (dualComplex ℤ (relMVVV X ∅ U V)) p).hom
          ≫ biprod.map (cupU X A U V n p t ht) (cupV X A U V n p t ht)
          ≫ (HomologicalComplex.biprodXIso (dualComplex ℤ (relMVUU X A U V))
              (dualComplex ℤ (relMVVV X A U V)) (p + n)).inv from rfl]
    refine (cancel_mono (HomologicalComplex.biprodXIso (dualComplex ℤ (relMVUU X A U V))
      (dualComplex ℤ (relMVVV X A U V)) (p + n)).hom).mp ?_
    simp only [Category.assoc]
    simp only [Iso.inv_hom_id, Category.comp_id]
    rw [biprod_lift_f_comp_biprodXIso_hom_gen]
    conv_rhs => rw [← Category.assoc]
    rw [biprod_lift_f_comp_biprodXIso_hom_gen, biprod_lift_comp_map]
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.lift_fst, biprod.lift_fst]
      exact cupTop_alphaU X A U V n p t ht
    · rw [Category.assoc, biprod.lift_snd, biprod.lift_snd]
      exact cupTop_alphaV X A U V n p t ht
  have h := congrArg (fun (m : (dualComplex ℤ (relMVTopC X ∅ U V)).X p ⟶
        (dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V)).X (p + n)) =>
      ModuleCat.Hom.hom m ψ) hm
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

end

end Work.Thom
