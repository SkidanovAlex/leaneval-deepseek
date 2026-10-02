import Mathlib
import Submission.Work.Thom.tsqHonest
import Submission.Work.Thom.transgressionBasic
import Submission.Work.Cohomology.relCohMV_honest_les

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.Thom

open CategoryTheory CategoryTheory.Limits Work.Cohomology
open scoped Simplicial

noncomputable section

/-! ## The restriction of a cochain to the small simplices lying in a set -/

/-- The restriction of a cochain `t` on `X` to the subcomplex of small simplices lying in `B`. -/
def restrIn (X : TopCat) (U V B : Set X) (n : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) : Cochain ℤ (smallInSSet U V B) n :=
  (((SSet.chainComplexMap (smallInSubcomplex U V B).ι (ModuleCat.of ℤ ℤ)).f n).hom.dualMap) t

/-- **The cup product with a cochain lying in `relKern X C` kills the chains lying in `C`.** -/
theorem subInclChain_cupHom_eq_zero (X : TopCat) (U V B C : Set X) (hCB : C ⊆ B) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X C n)
    (z : (smallInChains U V B).X p →ₗ[ℤ] ℤ) :
    (subInclChain U V hCB).f (p + n)
      ≫ cupHom ℤ (smallInSSet U V B) z (restrIn X U V B n t) = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [comp_zero, ← Category.assoc]
  rw [show (subInclChain U V hCB) = SSet.chainComplexMap
    (Subfunctor.homOfLe (by intro n x hx; exact ⟨hx.1, hx.2.trans hCB⟩))
    (ModuleCat.of ℤ ℤ) from rfl]
  rw [SSet.ι_chainComplexMap_f]
  rw [ιChainComplex_cupHom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply, one_smul]
  have key : (ConcreteCategory.hom ((smallInSubcomplex U V B).ι.app (Opposite.op ⦋p+n⦌)))
        ((ConcreteCategory.hom ((Subfunctor.homOfLe (by intro n x hx; exact ⟨hx.1, hx.2.trans hCB⟩)).app
          (Opposite.op ⦋p+n⦌))) σ)
      = (ConcreteCategory.hom ((smallInSubcomplex U V C).ι.app (Opposite.op ⦋p+n⦌))) σ := rfl
  have hb : genEval ℤ (smallInSSet U V B)
      (restrIn X U V B n t)
      (backFace (smallInSSet U V B) p n
        ((ConcreteCategory.hom ((Subfunctor.homOfLe (by intro n x hx; exact ⟨hx.1, hx.2.trans hCB⟩)).app
          (Opposite.op ⦋p+n⦌))) σ)) = 0 := by
    rw [restrIn, genEval_dualMap, app_backFace, key]
    rw [← app_backFace (smallInSubcomplex U V C).ι p n σ]
    exact genEval_eq_zero_of_isSmallIn U V C t ht _ (backFace (smallInSSet U V C) p n σ).2
  rw [hb, mul_zero]

/-! ## The descended cup map -/

/-- The cup product with `restrIn t`, descended to the relative complex `C^{U,V}(B,C)`. -/
noncomputable def cupDescendRelMor (X : TopCat) (U V : Set X) {B C : Set X} (hCB : C ⊆ B)
    (n p : ℕ) (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X C n)
    (ψ : (dualComplex ℤ (smallInChains U V B)).X p) :
    (relSmallChains U V B C hCB).X (p + n) ⟶ ModuleCat.of ℤ ℤ :=
  (cokernelComponentIso (subInclChain U V hCB) (p + n)).hom
    ≫ cokernel.desc ((subInclChain U V hCB).f (p + n))
        (cupHom ℤ (smallInSSet U V B) ψ (restrIn X U V B n t))
        (subInclChain_cupHom_eq_zero X U V B C hCB n p t ht ψ)

theorem cupDescendRelMor_add (X : TopCat) (U V : Set X) {B C : Set X} (hCB : C ⊆ B)
    (n p : ℕ) (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X C n)
    (ψ ψ' : (dualComplex ℤ (smallInChains U V B)).X p) :
    cupDescendRelMor X U V hCB n p t ht (ψ + ψ')
      = cupDescendRelMor X U V hCB n p t ht ψ + cupDescendRelMor X U V hCB n p t ht ψ' := by
  rw [cupDescendRelMor, cupDescendRelMor, cupDescendRelMor]
  rw [← Preadditive.comp_add]
  refine (cancel_epi (cokernelComponentIso (subInclChain U V hCB) (p + n)).hom).mpr ?_
  refine (cancel_epi (cokernel.π ((subInclChain U V hCB).f (p + n)))).mp ?_
  rw [Preadditive.comp_add]
  simp only [cokernel.π_desc]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_add]
  exact (cupBilinear ℤ (smallInSSet U V B) p n).1 ψ ψ' (restrIn X U V B n t)

theorem cupDescendRelMor_smul (X : TopCat) (U V : Set X) {B C : Set X} (hCB : C ⊆ B)
    (n p : ℕ) (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X C n)
    (a : ℤ) (ψ : (dualComplex ℤ (smallInChains U V B)).X p) :
    cupDescendRelMor X U V hCB n p t ht (a • ψ)
      = a • cupDescendRelMor X U V hCB n p t ht ψ := by
  rw [cupDescendRelMor, cupDescendRelMor]
  rw [← Preadditive.comp_zsmul]
  refine (cancel_epi (cokernelComponentIso (subInclChain U V hCB) (p + n)).hom).mpr ?_
  refine (cancel_epi (cokernel.π ((subInclChain U V hCB).f (p + n)))).mp ?_
  rw [Preadditive.comp_zsmul]
  simp only [cokernel.π_desc]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_smul]
  exact (cupBilinear ℤ (smallInSSet U V B) p n).2.1 a ψ (restrIn X U V B n t)

/-- The defining rule of the descended cup map. -/
theorem cupDescendRelMor_spec (X : TopCat) (U V : Set X) {B C : Set X} (hCB : C ⊆ B)
    (n p : ℕ) (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X C n)
    (ψ : (dualComplex ℤ (smallInChains U V B)).X p) :
    (cokernel.π (subInclChain U V hCB)).f (p + n)
        ≫ cupDescendRelMor X U V hCB n p t ht ψ
      = cupHom ℤ (smallInSSet U V B) ψ (restrIn X U V B n t) := by
  rw [cupDescendRelMor, ← Category.assoc, cokernelComponentIso_canon, cokernel.π_desc]

/-- **The cup product with a relative cocycle, descended through `subInclChain`.** -/
noncomputable def cupDescendRel (X : TopCat) (U V : Set X) {B C : Set X} (hCB : C ⊆ B)
    (n p : ℕ) (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X C n) :
    (dualComplex ℤ (smallInChains U V B)).X p
      ⟶ (dualComplex ℤ (relSmallChains U V B C hCB)).X (p + n) :=
  ModuleCat.ofHom
    { toFun := fun ψ => ModuleCat.Hom.hom (cupDescendRelMor X U V hCB n p t ht ψ)
      map_add' := fun ψ ψ' => by rw [cupDescendRelMor_add, ModuleCat.hom_add]
      map_smul' := fun a ψ => by rw [cupDescendRelMor_smul, ModuleCat.hom_smul]; rfl }

@[simp] theorem cupDescendRel_apply (X : TopCat) (U V : Set X) {B C : Set X} (hCB : C ⊆ B)
    (n p : ℕ) (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X C n)
    (ψ : (dualComplex ℤ (smallInChains U V B)).X p) :
    ModuleCat.Hom.hom (cupDescendRel X U V hCB n p t ht) ψ
      = ModuleCat.Hom.hom (cupDescendRelMor X U V hCB n p t ht ψ) := by
  rw [cupDescendRel]; rfl

/-! ## The descended cup map on the top term -/

/-- The cup product with `restrSmall t`, descended to the relative complex `C^{U,V}(X,A)`. -/
noncomputable def cupDescendMor (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n)
    (ψ : (dualComplex ℤ (smallChains U V)).X p) :
    (relMVTopC X A U V).X (p + n) ⟶ ModuleCat.of ℤ ℤ :=
  (cokernelComponentIso (smallInToSmall U V A) (p + n)).hom
    ≫ cokernel.desc ((smallInToSmall U V A).f (p + n))
        (cupHom ℤ (smallSSet U V) ψ (restrSmall X U V n t))
        (cupHom_smallInToSmall_eq_zero X A U V n p t ht ψ)

theorem cupDescendMor_add (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n)
    (ψ ψ' : (dualComplex ℤ (smallChains U V)).X p) :
    cupDescendMor X A U V n p t ht (ψ + ψ')
      = cupDescendMor X A U V n p t ht ψ + cupDescendMor X A U V n p t ht ψ' := by
  rw [cupDescendMor, cupDescendMor, cupDescendMor]
  rw [← Preadditive.comp_add]
  refine (cancel_epi (cokernelComponentIso (smallInToSmall U V A) (p + n)).hom).mpr ?_
  refine (cancel_epi (cokernel.π ((smallInToSmall U V A).f (p + n)))).mp ?_
  rw [Preadditive.comp_add]
  simp only [cokernel.π_desc]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_add]
  exact (cupBilinear ℤ (smallSSet U V) p n).1 ψ ψ' (restrSmall X U V n t)

theorem cupDescendMor_smul (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n)
    (a : ℤ) (ψ : (dualComplex ℤ (smallChains U V)).X p) :
    cupDescendMor X A U V n p t ht (a • ψ)
      = a • cupDescendMor X A U V n p t ht ψ := by
  rw [cupDescendMor, cupDescendMor]
  rw [← Preadditive.comp_zsmul]
  refine (cancel_epi (cokernelComponentIso (smallInToSmall U V A) (p + n)).hom).mpr ?_
  refine (cancel_epi (cokernel.π ((smallInToSmall U V A).f (p + n)))).mp ?_
  rw [Preadditive.comp_zsmul]
  simp only [cokernel.π_desc]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_smul]
  exact (cupBilinear ℤ (smallSSet U V) p n).2.1 a ψ (restrSmall X U V n t)

/-- The defining rule of `cupDescendMor`. -/
theorem cupDescendMor_spec (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n)
    (ψ : (dualComplex ℤ (smallChains U V)).X p) :
    (cokernel.π (smallInToSmall U V A)).f (p + n) ≫ cupDescendMor X A U V n p t ht ψ
      = cupHom ℤ (smallSSet U V) ψ (restrSmall X U V n t) := by
  rw [cupDescendMor, ← Category.assoc, cokernelComponentIso_canon, cokernel.π_desc]

/-! ## The four degreewise cup maps -/

/-- The degree-`n` cup map on the top term `C^*(C^{U,V}(X))`. -/
noncomputable def cupTop (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n) :
    (dualComplex ℤ (relMVTopC X ∅ U V)).X p
      ⟶ (dualComplex ℤ (relMVTopC X A U V)).X (p + n) :=
  (dualComplexMap ℤ (smallChains U V) (relMVTopC X ∅ U V)
      (cokernel.π (smallInToSmall U V ∅))).f p
    ≫ ModuleCat.ofHom
        { toFun := fun ψ => ModuleCat.Hom.hom (cupDescendMor X A U V n p t ht ψ)
          map_add' := fun ψ ψ' => by rw [cupDescendMor_add, ModuleCat.hom_add]
          map_smul' := fun a ψ => by rw [cupDescendMor_smul, ModuleCat.hom_smul]; rfl }

/-- The degree-`n` cup map on the `(U ∩ V)`-term. -/
noncomputable def cupUV (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n) :
    (dualComplex ℤ (relMVUV X ∅ U V)).X p
      ⟶ (dualComplex ℤ (relMVUV X A U V)).X (p + n) :=
  (dualComplexMap ℤ (smallInChains U V (U ∩ V)) (relMVUV X ∅ U V)
      (cokernel.π (relMVτ₁ U V ∅))).f p
    ≫ cupDescendRel X U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V) n p t
        (relKern_mono (Set.inter_subset_right : U ∩ V ∩ A ⊆ A) ht)

/-- The degree-`n` cup map on the `U`-term. -/
noncomputable def cupU (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n) :
    (dualComplex ℤ (relMVUU X ∅ U V)).X p
      ⟶ (dualComplex ℤ (relMVUU X A U V)).X (p + n) :=
  (dualComplexMap ℤ (smallInChains U V U) (relMVUU X ∅ U V)
      (cokernel.π (relMVτ₂U U V ∅))).f p
    ≫ cupDescendRel X U V (Set.inter_subset_left : U ∩ A ⊆ U) n p t
        (relKern_mono (Set.inter_subset_right : U ∩ A ⊆ A) ht)

/-- The degree-`n` cup map on the `V`-term. -/
noncomputable def cupV (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n) :
    (dualComplex ℤ (relMVVV X ∅ U V)).X p
      ⟶ (dualComplex ℤ (relMVVV X A U V)).X (p + n) :=
  (dualComplexMap ℤ (smallInChains U V V) (relMVVV X ∅ U V)
      (cokernel.π (relMVτ₂V U V ∅))).f p
    ≫ cupDescendRel X U V (Set.inter_subset_left : V ∩ A ⊆ V) n p t
        (relKern_mono (Set.inter_subset_right : V ∩ A ⊆ A) ht)

/-- The degree-`n` cup map on the middle biproduct `C^*(U,U∩A) ⊞ C^*(V,V∩A)`. -/
noncomputable def cupMid (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n) :
    (dualComplex ℤ (relMVUU X ∅ U V) ⊞ dualComplex ℤ (relMVVV X ∅ U V)).X p
      ⟶ (dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V)).X (p + n) :=
  (HomologicalComplex.biprodXIso (dualComplex ℤ (relMVUU X ∅ U V))
      (dualComplex ℤ (relMVVV X ∅ U V)) p).hom
    ≫ biprod.map (cupU X A U V n p t ht) (cupV X A U V n p t ht)
    ≫ (HomologicalComplex.biprodXIso (dualComplex ℤ (relMVUU X A U V))
        (dualComplex ℤ (relMVVV X A U V)) (p + n)).inv

end

end Work.Thom

