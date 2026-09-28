import Mathlib
import Submission.Work.Thom.transgressionFleetDefs
import Submission.Work.Thom.tsqInfra
import Submission.Work.Thom.cupDescendRelMor_d_comm
import Submission.Work.Thom.cupDescendMor_d_comm
import Submission.Work.Thom.cup_hmvG
import Submission.Work.Thom.cup_hmvF

/-!
# The cup product with a relative class as a morphism of Mayer–Vietoris short exact sequences

For a topological space `X`, a subset `A`, an open cover `X = U ∪ V`, a degree-`n` cochain `t`
lying in `relKern ℤ X A n` and a cocycle (`cochainDiff t = 0`), the cup product with `t` is a
degree-`n` morphism of cochain complexes on each of the three terms of the small-chain relative
Mayer–Vietoris sequence:

* `cupTopChain` on `C^{U,V}(X,∅) ⟶ C^{U,V}(X,A)`;
* `cupMidChain` on `C^{U,V}(U,∅) ⊞ C^{U,V}(V,∅) ⟶ C^{U,V}(U,U∩A) ⊞ C^{U,V}(V,V∩A)`;
* `cupUVChain` on `C^{U,V}(U∩V,∅) ⟶ C^{U,V}(U∩V,U∩V∩A)`;

and, by `cup_hmvF` and `cup_hmvG`, they assemble into a morphism of short exact sequences
`cupSES : mvSES X ∅ U V ⟶ shS (mvSES X A U V) n` of degree `n`
(in the sense of `Work.Thom.Tsq.shS`).  Applying the degree-`n` naturality of the connecting map
(`Work.Thom.Tsq.shS_delta_naturality`) then gives the compatibility of the Mayer–Vietoris
connecting maps with the cup product with `t`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.Thom

open CategoryTheory CategoryTheory.Limits Work.Cohomology
open scoped Simplicial

noncomputable section

variable (X : TopCat) (A U V : Set X) (n : ℕ)
variable (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n)

/-! ## The top term -/

/-- The component of `cupTopDesc` on an element. -/
lemma cupTopDesc_apply (p : ℕ) (ψ : (dualComplex ℤ (smallChains U V)).X p) :
    ModuleCat.Hom.hom (cupTopDesc X A U V n p t ht) ψ
      = ModuleCat.Hom.hom (cupDescendMor X A U V n p t ht ψ) := rfl

/-- `cupTopDesc` commutes with the differentials. -/
lemma cupTopDesc_d_comm (hdt : cochainDiff ℤ (TopCat.toSSet.obj X) t = 0) (p : ℕ) :
    cupTopDesc X A U V n p t ht ≫ (dualComplex ℤ (relMVTopC X A U V)).d (p+n) ((p+1)+n)
      = (dualComplex ℤ (smallChains U V)).d p (p+1) ≫ cupTopDesc X A U V n (p+1) t ht := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [cupTopDesc_apply, cupTopDesc_apply]
  have h : (p+1)+n = p+n+1 := by omega
  rw [show (dualComplex ℤ (relMVTopC X A U V)).d (p+n) ((p+1)+n)
      = (dualComplex ℤ (relMVTopC X A U V)).d (p+n) (p+n+1)
        ≫ ((dualComplex ℤ (relMVTopC X A U V)).XIsoOfEq h).inv from
    (HomologicalComplex.d_comp_XIsoOfEq_inv (dualComplex ℤ (relMVTopC X A U V)) h (p+n)).symm]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact (cupDescendMor_d_comm X A U V n p t ht hdt ψ).symm

/-- `cupTop` commutes with the differentials, in explicit form. -/
lemma cupTop_d_comm (hdt : cochainDiff ℤ (TopCat.toSSet.obj X) t = 0) (i : ℕ) :
    cupTop X A U V n i t ht ≫ (dualComplex ℤ (relMVTopC X A U V)).d (i+n) ((i+1)+n)
      = (dualComplex ℤ (relMVTopC X ∅ U V)).d i (i+1) ≫ cupTop X A U V n (i+1) t ht := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [cupTop_eq, cupTop_eq]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  have hcomm := congrArg (fun (g : (dualComplex ℤ (relMVTopC X ∅ U V)).X i ⟶
        (dualComplex ℤ (smallChains U V)).X (i+1)) => ModuleCat.Hom.hom g ψ)
    (HomologicalComplex.Hom.comm (dualComplexMap ℤ (smallChains U V) (relMVTopC X ∅ U V)
      (cokernel.π (smallInToSmall U V ∅))) i (i+1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
  rw [← hcomm]
  rw [cupTopDesc_apply, cupTopDesc_apply]
  have h : (i+1)+n = i+n+1 := by omega
  rw [show (dualComplex ℤ (relMVTopC X A U V)).d (i+n) ((i+1)+n)
      = (dualComplex ℤ (relMVTopC X A U V)).d (i+n) (i+n+1)
        ≫ ((dualComplex ℤ (relMVTopC X A U V)).XIsoOfEq h).inv from
    (HomologicalComplex.d_comp_XIsoOfEq_inv (dualComplex ℤ (relMVTopC X A U V)) h (i+n)).symm]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact (cupDescendMor_d_comm X A U V n i t ht hdt _).symm

/-- The cup product with `t`, as a morphism of cochain complexes of degree `n` on the top term. -/
noncomputable def cupTopChain (hdt : cochainDiff ℤ (TopCat.toSSet.obj X) t = 0) :
    dualComplex ℤ (relMVTopC X ∅ U V) ⟶ Tsq.shK (dualComplex ℤ (relMVTopC X A U V)) n :=
  HomologicalComplex.Hom.mk (fun p => cupTop X A U V n p t ht) (by
    intro i j hij
    rw [ComplexShape.up_Rel] at hij
    subst hij
    simp only [Tsq.shK_d]
    exact cupTop_d_comm X A U V n t ht hdt i)

/-! ## The relative descents `cupDescendRel`, `cupU`, `cupV`, `cupUV` -/

/-- `cupDescendRel` commutes with the differentials. -/
lemma cupDescendRel_d_comm {B C : Set X} (hCB : C ⊆ B) (ht : t ∈ relKern ℤ X C n)
    (hdt : cochainDiff ℤ (TopCat.toSSet.obj X) t = 0) (p : ℕ) :
    cupDescendRel X U V hCB n p t ht
        ≫ (dualComplex ℤ (relSmallChains U V B C hCB)).d (p+n) ((p+1)+n)
      = (dualComplex ℤ (smallInChains U V B)).d p (p+1)
        ≫ cupDescendRel X U V hCB n (p+1) t ht := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [cupDescendRel_apply, cupDescendRel_apply]
  have h : (p+1)+n = p+n+1 := by omega
  rw [show (dualComplex ℤ (relSmallChains U V B C hCB)).d (p+n) ((p+1)+n)
      = (dualComplex ℤ (relSmallChains U V B C hCB)).d (p+n) (p+n+1)
        ≫ ((dualComplex ℤ (relSmallChains U V B C hCB)).XIsoOfEq h).inv from
    (HomologicalComplex.d_comp_XIsoOfEq_inv
      (dualComplex ℤ (relSmallChains U V B C hCB)) h (p+n)).symm]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact (cupDescendRelMor_d_comm X U V hCB n p t ht hdt ψ).symm

/-- The component of `cupU` on an element, with the projection exposed. -/
lemma cupU_eq (p : ℕ) :
    cupU X A U V n p t ht
      = (dualComplexMap ℤ (smallInChains U V U) (relMVUU X ∅ U V)
            (cokernel.π (relMVτ₂U U V ∅))).f p
          ≫ cupDescendRel X U V (Set.inter_subset_left : U ∩ A ⊆ U) n p t
              (relKern_mono (Set.inter_subset_right : U ∩ A ⊆ A) ht) := rfl

/-- The component of `cupV` on an element, with the projection exposed. -/
lemma cupV_eq (p : ℕ) :
    cupV X A U V n p t ht
      = (dualComplexMap ℤ (smallInChains U V V) (relMVVV X ∅ U V)
            (cokernel.π (relMVτ₂V U V ∅))).f p
          ≫ cupDescendRel X U V (Set.inter_subset_left : V ∩ A ⊆ V) n p t
              (relKern_mono (Set.inter_subset_right : V ∩ A ⊆ A) ht) := rfl

/-- `cupU` commutes with the differentials. -/
lemma cupU_d_comm (hdt : cochainDiff ℤ (TopCat.toSSet.obj X) t = 0) (i : ℕ) :
    cupU X A U V n i t ht ≫ (dualComplex ℤ (relMVUU X A U V)).d (i+n) ((i+1)+n)
      = (dualComplex ℤ (relMVUU X ∅ U V)).d i (i+1) ≫ cupU X A U V n (i+1) t ht := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [cupU_eq, cupU_eq]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  have hcomm := congrArg (fun (g : (dualComplex ℤ (relMVUU X ∅ U V)).X i ⟶
        (dualComplex ℤ (smallInChains U V U)).X (i+1)) => ModuleCat.Hom.hom g ψ)
    (HomologicalComplex.Hom.comm (dualComplexMap ℤ (smallInChains U V U) (relMVUU X ∅ U V)
      (cokernel.π (relMVτ₂U U V ∅))) i (i+1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
  rw [← hcomm]
  rw [cupDescendRel_apply, cupDescendRel_apply]
  have h : (i+1)+n = i+n+1 := by omega
  rw [show (dualComplex ℤ (relMVUU X A U V)).d (i+n) ((i+1)+n)
      = (dualComplex ℤ (relMVUU X A U V)).d (i+n) (i+n+1)
        ≫ ((dualComplex ℤ (relMVUU X A U V)).XIsoOfEq h).inv from
    (HomologicalComplex.d_comp_XIsoOfEq_inv (dualComplex ℤ (relMVUU X A U V)) h (i+n)).symm]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact (cupDescendRelMor_d_comm X U V (Set.inter_subset_left : U ∩ A ⊆ U) n i t
    (relKern_mono (Set.inter_subset_right : U ∩ A ⊆ A) ht) hdt _).symm

/-- `cupV` commutes with the differentials. -/
lemma cupV_d_comm (hdt : cochainDiff ℤ (TopCat.toSSet.obj X) t = 0) (i : ℕ) :
    cupV X A U V n i t ht ≫ (dualComplex ℤ (relMVVV X A U V)).d (i+n) ((i+1)+n)
      = (dualComplex ℤ (relMVVV X ∅ U V)).d i (i+1) ≫ cupV X A U V n (i+1) t ht := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [cupV_eq, cupV_eq]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  have hcomm := congrArg (fun (g : (dualComplex ℤ (relMVVV X ∅ U V)).X i ⟶
        (dualComplex ℤ (smallInChains U V V)).X (i+1)) => ModuleCat.Hom.hom g ψ)
    (HomologicalComplex.Hom.comm (dualComplexMap ℤ (smallInChains U V V) (relMVVV X ∅ U V)
      (cokernel.π (relMVτ₂V U V ∅))) i (i+1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
  rw [← hcomm]
  rw [cupDescendRel_apply, cupDescendRel_apply]
  have h : (i+1)+n = i+n+1 := by omega
  rw [show (dualComplex ℤ (relMVVV X A U V)).d (i+n) ((i+1)+n)
      = (dualComplex ℤ (relMVVV X A U V)).d (i+n) (i+n+1)
        ≫ ((dualComplex ℤ (relMVVV X A U V)).XIsoOfEq h).inv from
    (HomologicalComplex.d_comp_XIsoOfEq_inv (dualComplex ℤ (relMVVV X A U V)) h (i+n)).symm]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact (cupDescendRelMor_d_comm X U V (Set.inter_subset_left : V ∩ A ⊆ V) n i t
    (relKern_mono (Set.inter_subset_right : V ∩ A ⊆ A) ht) hdt _).symm

/-- `cupUV` commutes with the differentials. -/
lemma cupUV_d_comm (hdt : cochainDiff ℤ (TopCat.toSSet.obj X) t = 0) (i : ℕ) :
    cupUV X A U V n i t ht ≫ (dualComplex ℤ (relMVUV X A U V)).d (i+n) ((i+1)+n)
      = (dualComplex ℤ (relMVUV X ∅ U V)).d i (i+1) ≫ cupUV X A U V n (i+1) t ht := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [cupUV, cupUV]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  have hcomm := congrArg (fun (g : (dualComplex ℤ (relMVUV X ∅ U V)).X i ⟶
        (dualComplex ℤ (smallInChains U V (U ∩ V))).X (i+1)) => ModuleCat.Hom.hom g ψ)
    (HomologicalComplex.Hom.comm (dualComplexMap ℤ (smallInChains U V (U ∩ V))
      (relMVUV X ∅ U V) (cokernel.π (relMVτ₁ U V ∅))) i (i+1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
  rw [← hcomm]
  rw [cupDescendRel_apply, cupDescendRel_apply]
  have h : (i+1)+n = i+n+1 := by omega
  rw [show (dualComplex ℤ (relMVUV X A U V)).d (i+n) ((i+1)+n)
      = (dualComplex ℤ (relMVUV X A U V)).d (i+n) (i+n+1)
        ≫ ((dualComplex ℤ (relMVUV X A U V)).XIsoOfEq h).inv from
    (HomologicalComplex.d_comp_XIsoOfEq_inv (dualComplex ℤ (relMVUV X A U V)) h (i+n)).symm]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact (cupDescendRelMor_d_comm X U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V) n i t
    (relKern_mono (Set.inter_subset_right : U ∩ V ∩ A ⊆ A) ht) hdt _).symm

/-! ## Biproduct calculus -/

/-- **The degreewise biproduct isomorphism is natural for the differentials.** -/
theorem shChainBiprodXIso_hom_d {K L : CochainComplex (ModuleCat ℤ) ℕ} (i j : ℕ) :
    (HomologicalComplex.biprodXIso K L i).hom ≫ biprod.map (K.d i j) (L.d i j) =
      (K ⊞ L).d i j ≫ (HomologicalComplex.biprodXIso K L j).hom := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.map_fst, ← Category.assoc, HomologicalComplex.biprodXIso_hom_fst,
      (biprod.fst : K ⊞ L ⟶ K).comm i j, Category.assoc,
      HomologicalComplex.biprodXIso_hom_fst]
  · rw [Category.assoc, biprod.map_snd, ← Category.assoc, HomologicalComplex.biprodXIso_hom_snd,
      (biprod.snd : K ⊞ L ⟶ L).comm i j, Category.assoc,
      HomologicalComplex.biprodXIso_hom_snd]

/-- **The inverse degreewise biproduct isomorphism is natural for the differentials.** -/
theorem shChainBiprodXIso_inv_d {K L : CochainComplex (ModuleCat ℤ) ℕ} (i j : ℕ) :
    (HomologicalComplex.biprodXIso K L i).inv ≫ (K ⊞ L).d i j =
      biprod.map (K.d i j) (L.d i j) ≫ (HomologicalComplex.biprodXIso K L j).inv := by
  apply biprod.hom_ext'
  · rw [← Category.assoc, HomologicalComplex.inl_biprodXIso_inv,
      (biprod.inl : K ⟶ K ⊞ L).comm i j, ← Category.assoc, biprod.inl_map, Category.assoc,
      ← HomologicalComplex.inl_biprodXIso_inv]
  · rw [← Category.assoc, HomologicalComplex.inr_biprodXIso_inv,
      (biprod.inr : L ⟶ K ⊞ L).comm i j, ← Category.assoc, biprod.inr_map, Category.assoc,
      ← HomologicalComplex.inr_biprodXIso_inv]

/-- `biprod.map` is a functor. -/
theorem shChainBiprod_map_comp {W X Y Z P Q : ModuleCat ℤ} [HasBinaryBiproduct W X]
    [HasBinaryBiproduct Y Z] [HasBinaryBiproduct P Q] (f : W ⟶ Y) (g : X ⟶ Z) (f' : Y ⟶ P)
    (g' : Z ⟶ Q) :
    biprod.map f g ≫ biprod.map f' g' = biprod.map (f ≫ f') (g ≫ g') := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.map_fst, ← Category.assoc, biprod.map_fst, Category.assoc, biprod.map_fst]
  · rw [Category.assoc, biprod.map_snd, ← Category.assoc, biprod.map_snd, Category.assoc, biprod.map_snd]

/-! ## The middle term -/

/-- **The conjugation of a biproduct of two degree-`n` maps is a chain map.**
This is the degreewise form of the statement that cupping with `t` on a biproduct of two chain
complexes is a morphism of complexes. -/
theorem shChainBiprod_conj {C D C' D' : CochainComplex (ModuleCat ℤ) ℕ} (n i : ℕ)
    (u : (C.X i) ⟶ (C'.X (i+n))) (v : (D.X i) ⟶ (D'.X (i+n)))
    (u' : (C.X (i+1)) ⟶ (C'.X ((i+1)+n))) (v' : (D.X (i+1)) ⟶ (D'.X ((i+1)+n)))
    (hu : u ≫ (C'.d (i+n) ((i+1)+n)) = (C.d i (i+1)) ≫ u')
    (hv : v ≫ (D'.d (i+n) ((i+1)+n)) = (D.d i (i+1)) ≫ v') :
    ((HomologicalComplex.biprodXIso C D i).hom ≫ biprod.map u v
        ≫ (HomologicalComplex.biprodXIso C' D' (i+n)).inv)
      ≫ (C' ⊞ D').d (i+n) ((i+1)+n)
    = (C ⊞ D).d i (i+1)
      ≫ ((HomologicalComplex.biprodXIso C D (i+1)).hom ≫ biprod.map u' v'
        ≫ (HomologicalComplex.biprodXIso C' D' ((i+1)+n)).inv) := by
  rw [Category.assoc, Category.assoc]
  rw [shChainBiprodXIso_inv_d (K := C') (L := D') (i+n) ((i+1)+n)]
  rw [← Category.assoc (biprod.map u v)
    (biprod.map (C'.d (i+n) ((i+1)+n)) (D'.d (i+n) ((i+1)+n)))
    ((HomologicalComplex.biprodXIso C' D' ((i+1)+n)).inv)]
  rw [shChainBiprod_map_comp, hu, hv]
  conv_rhs => rw [← Category.assoc]
  rw [← shChainBiprodXIso_hom_d (K := C) (L := D) i (i+1)]
  conv_rhs => rw [Category.assoc]
  conv_rhs => rw [← Category.assoc (biprod.map (C.d i (i+1)) (D.d i (i+1)))
    (biprod.map u' v') ((HomologicalComplex.biprodXIso C' D' ((i+1)+n)).inv)]
  rw [shChainBiprod_map_comp]

/-- `cupMid` commutes with the differentials. -/
lemma cupMid_d_comm (hdt : cochainDiff ℤ (TopCat.toSSet.obj X) t = 0) (i : ℕ) :
    cupMid X A U V n i t ht
        ≫ (dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V)).d (i+n) ((i+1)+n)
      = (dualComplex ℤ (relMVUU X ∅ U V) ⊞ dualComplex ℤ (relMVVV X ∅ U V)).d i (i+1)
        ≫ cupMid X A U V n (i+1) t ht :=
  shChainBiprod_conj n i (cupU X A U V n i t ht) (cupV X A U V n i t ht)
    (cupU X A U V n (i+1) t ht) (cupV X A U V n (i+1) t ht)
    (cupU_d_comm X A U V n t ht hdt i) (cupV_d_comm X A U V n t ht hdt i)

/-- The cup product with `t`, as a morphism of cochain complexes of degree `n` on the middle term. -/
noncomputable def cupMidChain (hdt : cochainDiff ℤ (TopCat.toSSet.obj X) t = 0) :
    dualComplex ℤ (relMVUU X ∅ U V) ⊞ dualComplex ℤ (relMVVV X ∅ U V)
      ⟶ Tsq.shK (dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V)) n :=
  HomologicalComplex.Hom.mk (fun p => cupMid X A U V n p t ht) (by
    intro i j hij
    rw [ComplexShape.up_Rel] at hij
    subst hij
    simp only [Tsq.shK_d]
    exact cupMid_d_comm X A U V n t ht hdt i)

/-- The cup product with `t`, as a morphism of cochain complexes of degree `n` on the `U`-piece. -/
noncomputable def cupUChain (hdt : cochainDiff ℤ (TopCat.toSSet.obj X) t = 0) :
    dualComplex ℤ (relMVUU X ∅ U V) ⟶ Tsq.shK (dualComplex ℤ (relMVUU X A U V)) n :=
  HomologicalComplex.Hom.mk (fun p => cupU X A U V n p t ht) (by
    intro i j hij
    rw [ComplexShape.up_Rel] at hij
    subst hij
    simp only [Tsq.shK_d]
    exact cupU_d_comm X A U V n t ht hdt i)

/-- The cup product with `t`, as a morphism of cochain complexes of degree `n` on the `V`-piece. -/
noncomputable def cupVChain (hdt : cochainDiff ℤ (TopCat.toSSet.obj X) t = 0) :
    dualComplex ℤ (relMVVV X ∅ U V) ⟶ Tsq.shK (dualComplex ℤ (relMVVV X A U V)) n :=
  HomologicalComplex.Hom.mk (fun p => cupV X A U V n p t ht) (by
    intro i j hij
    rw [ComplexShape.up_Rel] at hij
    subst hij
    simp only [Tsq.shK_d]
    exact cupV_d_comm X A U V n t ht hdt i)

/-- The cup product with `t`, as a morphism of cochain complexes of degree `n` on the overlap. -/
noncomputable def cupUVChain (hdt : cochainDiff ℤ (TopCat.toSSet.obj X) t = 0) :
    dualComplex ℤ (relMVUV X ∅ U V) ⟶ Tsq.shK (dualComplex ℤ (relMVUV X A U V)) n :=
  HomologicalComplex.Hom.mk (fun p => cupUV X A U V n p t ht) (by
    intro i j hij
    rw [ComplexShape.up_Rel] at hij
    subst hij
    simp only [Tsq.shK_d]
    exact cupUV_d_comm X A U V n t ht hdt i)

/-! ## The morphism of short exact sequences -/

/-- The small-model relative Mayer–Vietoris short exact sequence of the pair `(X,A)`. -/
noncomputable abbrev mvSES : ShortComplex (CochainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (hmvF X A U V) (hmvG X A U V) (hmv_comp X A U V)

/-- The cup product with `t` is a morphism of the two relative Mayer–Vietoris short exact
sequences, of degree `n`. -/
noncomputable def cupSES (hdt : cochainDiff ℤ (TopCat.toSSet.obj X) t = 0) :
    mvSES X ∅ U V ⟶ Tsq.shS (mvSES X A U V) n :=
  ShortComplex.homMk (cupTopChain X A U V n t ht hdt) (cupMidChain X A U V n t ht hdt)
    (cupUVChain X A U V n t ht hdt)
    (by
      apply HomologicalComplex.hom_ext
      intro p
      simp only [HomologicalComplex.comp_f, Tsq.shS_f, Tsq.shMap_f, mvSES]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro ψ
      exact cup_hmvF X A U V n p t ht ψ)
    (by
      apply HomologicalComplex.hom_ext
      intro p
      simp only [HomologicalComplex.comp_f, Tsq.shS_f, Tsq.shMap_f, mvSES]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro ψ
      exact cup_hmvG X A U V n p t ht ψ)

/-! ## The boundary comparison `(shK K n).homology 0 ⟶ K.homology n`

The restriction isomorphism `Tsq.shK_homologyIso` compares `(shK K n).homology k` with
`K.homology (k+n)` only for `k ≥ 1`.  At the boundary `k = 0` the object `(shK K n).homology 0`
is the module of cycles of `K` in degree `n` (there is no incoming differential), and the natural
map to `K.homology n` is the projection forgetting the boundaries. -/

/-- The comparison `(shK K n).cycles 0 ⟶ K.cycles (0+n)` (the cycles of the shifted complex in
degree `0` are the cycles of `K` in degree `n`). -/
noncomputable def shK_cyclesZeroTo (K : CochainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (Tsq.shK K n).cycles 0 ⟶ K.cycles (0+n) :=
  (K.restrictionCyclesIso (Tsq.shEmb n) 0 1
    (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel 0 1 from rfl)) rfl rfl
    (show (ComplexShape.up ℕ).next (0+n) = (1:ℕ)+n from
      ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (0+n) ((1:ℕ)+n) from by
        change 0 + n + 1 = 1 + n
        omega))).hom

/-- The boundary comparison `(shK K n).homology 0 ⟶ K.homology (0+n)`: the class of a `0`-cycle of
the shifted complex (i.e. of a cycle of `K` in degree `n`) in `H^n(K)`. -/
noncomputable def shK_homologyZero (K : CochainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (Tsq.shK K n).homology 0 ⟶ K.homology (0+n) :=
  ((Tsq.shK K n).sc 0).descHomology (shK_cyclesZeroTo K n ≫ K.homologyπ (0+n)) (by
    have hprev : (ComplexShape.up ℕ).prev 0 = 0 := by simp [ComplexShape.prev]
    have hSf : ((Tsq.shK K n).sc 0).f = 0 := by
      show (Tsq.shK K n).d ((ComplexShape.up ℕ).prev 0) 0 = 0
      rw [hprev]
      exact (Tsq.shK K n).shape 0 0 (by simp [ComplexShape.up_Rel])
    have hto : ((Tsq.shK K n).sc 0).toCycles = 0 := by
      refine (cancel_mono ((Tsq.shK K n).sc 0).iCycles).mp ?_
      rw [ShortComplex.toCycles_i, hSf, zero_comp]
    rw [hto, zero_comp])

/-- The defining property of the boundary comparison. -/
theorem shK_homologyZero_spec (K : CochainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (Tsq.shK K n).homologyπ 0 ≫ shK_homologyZero K n
      = shK_cyclesZeroTo K n ≫ K.homologyπ (0+n) := by
  show ((Tsq.shK K n).sc 0).homologyπ ≫ shK_homologyZero K n = _
  rw [shK_homologyZero]
  exact ShortComplex.π_descHomology (S := (Tsq.shK K n).sc 0) (A := K.homology (0+n))
    (shK_cyclesZeroTo K n ≫ K.homologyπ (0+n)) _

end
end Work.Thom
