import Mathlib
import Submission.Work.Thom.transgressionFleetDefs

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Thom

set_option allowUnsafeReducibility true

attribute [local reducible] Work.Cohomology.relMVτ₁ Work.Cohomology.relMVτ₂U
  Work.Cohomology.relMVτ₂V

open CategoryTheory CategoryTheory.Limits Work.Cohomology
open scoped Simplicial

noncomputable section

/-! ## The "cup with a fixed cochain" map on the duals of a small-in subcomplex

For `B ⊆ X` and a cochain `t` on `X`, the map `ψ ↦ ψ ⌣ restrIn t` on the duals of
`smallInChains U V B`.  This is the map onto which `cupDescendRel` descends, and it is what makes
the naturality with respect to `subInclChain` transparent. -/

/-- The cup product with `restrIn t`, as a map on the duals of the small chains lying in `B`. -/
noncomputable def cupHomMap (X : TopCat) (U V B : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) :
    dualObj ℤ (smallInChains U V B) p ⟶ dualObj ℤ (smallInChains U V B) (p+n) :=
  ModuleCat.ofHom
    { toFun := fun ψ => cup ℤ (smallInSSet U V B) ψ (restrIn X U V B n t)
      map_add' := fun ψ ψ' => (cupBilinear ℤ (smallInSSet U V B) p n).1 ψ ψ' _
      map_smul' := fun a ψ => (cupBilinear ℤ (smallInSSet U V B) p n).2.1 a ψ _ }

/-- The defining rule of `cupHomMap`. -/
lemma cupHomMap_apply (X : TopCat) (U V B : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n)
    (ψ : dualObj ℤ (smallInChains U V B) p) :
    ModuleCat.Hom.hom (cupHomMap X U V B n p t) ψ
      = cup ℤ (smallInSSet U V B) ψ (restrIn X U V B n t) := rfl

/-! ## Elementary observations about `dualComplexMap` -/

/-- The component of the dual of a chain map, as a `LinearMap.dualMap`. -/
lemma dualComplexMapComp_hom_apply (C D : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ D) (n : ℕ)
    (ω : (D.X n) →ₗ[ℤ] ℤ) :
    ModuleCat.Hom.hom (dualComplexMapComp ℤ C D f n) ω
      = LinearMap.dualMap (ModuleCat.Hom.hom (f.f n)) ω := rfl

/-- The component of the dual of a chain map, as a linear map. -/
lemma dualComplexMapComp_hom_eq (C D : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ D) (n : ℕ) :
    ModuleCat.Hom.hom (dualComplexMapComp ℤ C D f n)
      = LinearMap.dualMap (ModuleCat.Hom.hom (f.f n)) :=
  LinearMap.ext (fun ω => dualComplexMapComp_hom_apply C D f n ω)

/-- The `n`-th component of the cokernel projection is an epimorphism. -/
lemma epi_cokernelπ_f {K L : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L) (n : ℕ) :
    Epi ((cokernel.π f).f n) := by
  have hfac : (cokernel.π f).f n = cokernel.π (f.f n) ≫ (cokernelComponentIso f n).inv := by
    rw [← cokernelComponentIso_canon f n, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hfac]; infer_instance

/-- The dual of an epimorphic component of a chain map is a monomorphism. -/
lemma mono_dualComplexMapComp_of_epi {C D : ChainComplex (ModuleCat ℤ) ℕ} (f : C ⟶ D) (n : ℕ)
    (hf : Epi (f.f n)) : Mono (dualComplexMapComp ℤ C D f n) := by
  rw [ModuleCat.mono_iff_injective]
  change Function.Injective ⇑(ModuleCat.Hom.hom (dualComplexMapComp ℤ C D f n))
  rw [dualComplexMapComp_hom_eq]
  exact LinearMap.dualMap_injective_of_surjective ((ModuleCat.epi_iff_surjective _).mp hf)

/-! ## Functoriality of the chain complex of a simplicial set, and restriction of cochains -/

/-- Functoriality of `SSet.chainComplexMap`. -/
theorem sCM_comp {X Y Z : SSet} (f : X ⟶ Y) (g : Y ⟶ Z) (R : ModuleCat ℤ) :
    SSet.chainComplexMap (f ≫ g) R = SSet.chainComplexMap f R ≫ SSet.chainComplexMap g R := by
  simp only [SSet.chainComplexMap, Functor.map_comp]

/-- Functoriality of `SSet.chainComplexMap`, degreewise. -/
theorem sCM_comp_f {X Y Z : SSet} (f : X ⟶ Y) (g : Y ⟶ Z) (R : ModuleCat ℤ) (n : ℕ) :
    (SSet.chainComplexMap f R).f n ≫ (SSet.chainComplexMap g R).f n
      = (SSet.chainComplexMap (f ≫ g) R).f n := by
  rw [← HomologicalComplex.comp_f, sCM_comp]

/-- **Naturality of `restrIn` under the inclusion of small-in subcomplexes.** -/
theorem restrIn_natural (X : TopCat) (U V : Set X) {B C : Set X} (hCB : C ⊆ B) (n : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) :
    (dualComplexMapComp ℤ (smallInChains U V C) (smallInChains U V B)
        (subInclChain U V hCB) n).hom (restrIn X U V B n t) = restrIn X U V C n t := by
  rw [dualComplexMapComp_apply', HMV.subInclChain_eq_gen]
  apply LinearMap.ext
  intro x
  rw [restrIn, restrIn, LinearMap.comp_apply, LinearMap.dualMap_apply, LinearMap.dualMap_apply]
  congr 1
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, sCM_comp_f, HMV.subInclSSetGen_comp]

/-- **Naturality of `restrIn`**, in the form of a dual map. -/
theorem restrIn_dualMap (X : TopCat) (U V : Set X) {B C : Set X} (hCB : C ⊆ B) (n : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) :
    LinearMap.dualMap (ModuleCat.Hom.hom ((subInclChain U V hCB).f n)) (restrIn X U V B n t)
      = restrIn X U V C n t := by
  rw [← ModuleCat.hom_ofHom (LinearMap.dualMap (ModuleCat.Hom.hom ((subInclChain U V hCB).f n)))]
  exact restrIn_natural X U V hCB n t

/-! ## The descent rule and its naturality -/

/-- The descent rule of `cupDescendRel`, evaluated on a cochain and a chain: the cup product with
`restrIn t`. -/
theorem cupDescendRelMor_dualMap_apply (X : TopCat) (U V : Set X) {B C : Set X} (hCB : C ⊆ B)
    (n p : ℕ) (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X C n)
    (ψ : (dualComplex ℤ (smallInChains U V B)).X p) :
    (dualComplexMapComp ℤ (smallInChains U V B) (relSmallChains U V B C hCB)
        (cokernel.π (subInclChain U V hCB)) (p+n)).hom
      (ModuleCat.Hom.hom (cupDescendRelMor X U V hCB n p t ht ψ))
      = cup ℤ (smallInSSet U V B) ψ (restrIn X U V B n t) := by
  rw [dualComplexMapComp_apply', ← ModuleCat.hom_comp]
  show ModuleCat.Hom.hom ((cokernel.π (subInclChain U V hCB)).f (p+n)
      ≫ cupDescendRelMor X U V hCB n p t ht ψ) = _
  rw [cupDescendRelMor_spec]
  rfl

/-- The defining rule of `cupDescendRel`: composed with the cokernel projection it is
`cupHomMap`. -/
theorem cupHomMap_spec_apply (X : TopCat) (U V : Set X) {B C : Set X} (hCB : C ⊆ B)
    (n p : ℕ) (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X C n)
    (ψ : (dualComplex ℤ (smallInChains U V B)).X p) :
    ModuleCat.Hom.hom (cupDescendRel X U V hCB n p t ht
      ≫ (dualComplexMap ℤ (smallInChains U V B) (relSmallChains U V B C hCB)
          (cokernel.π (subInclChain U V hCB))).f (p+n)) ψ
      = cup ℤ (smallInSSet U V B) ψ (restrIn X U V B n t) := by
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, cupDescendRel_apply, dualComplexMap_f]
  exact cupDescendRelMor_dualMap_apply X U V hCB n p t ht ψ

/-- The defining rule of `cupDescendRel`. -/
theorem cupHomMap_spec (X : TopCat) (U V : Set X) {B C : Set X} (hCB : C ⊆ B)
    (n p : ℕ) (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X C n) :
    cupDescendRel X U V hCB n p t ht
      ≫ (dualComplexMap ℤ (smallInChains U V B) (relSmallChains U V B C hCB)
          (cokernel.π (subInclChain U V hCB))).f (p+n)
      = cupHomMap X U V B n p t := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  exact cupHomMap_spec_apply X U V hCB n p t ht ψ

/-- **Naturality of `cupHomMap` under the inclusion of `U ∩ V` into a piece.** -/
theorem cupHomMap_restrict_apply (X : TopCat) (U V : Set X) {P : Set X} (h : U ∩ V ⊆ P) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n)
    (ψ : dualObj ℤ (smallInChains U V P) p) :
    ModuleCat.Hom.hom (cupHomMap X U V P n p t
          ≫ dualComplexMapComp ℤ (smallInChains U V (U∩V)) (smallInChains U V P) (subInclChain U V h) (p+n)) ψ
      = ModuleCat.Hom.hom (dualComplexMapComp ℤ (smallInChains U V (U∩V)) (smallInChains U V P) (subInclChain U V h) p
            ≫ cupHomMap X U V (U∩V) n p t) ψ := by
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
    cupHomMap_apply, cupHomMap_apply, dualComplexMapComp_hom_apply, dualComplexMapComp_hom_apply]
  have hnat := cupNatural ℤ (HMV.subInclSSetGen U V h) ψ (restrIn X U V P n t)
  rw [← HMV.subInclChain_eq_gen] at hnat
  rw [restrIn_dualMap X U V h n t] at hnat
  exact hnat.symm

/-- **Naturality of `cupHomMap` under the inclusion of `U ∩ V` into a piece.** -/
theorem cupHomMap_restrict (X : TopCat) (U V : Set X) {P : Set X} (h : U ∩ V ⊆ P) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) :
    cupHomMap X U V P n p t
      ≫ (dualComplexMap ℤ (smallInChains U V (U∩V)) (smallInChains U V P) (subInclChain U V h)).f (p+n)
    = (dualComplexMap ℤ (smallInChains U V (U∩V)) (smallInChains U V P) (subInclChain U V h)).f p
      ≫ cupHomMap X U V (U∩V) n p t := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  exact cupHomMap_restrict_apply X U V h n p t ψ

/-! ## The Mayer--Vietoris square on the chain level, dualised -/

/-- The degreewise Mayer--Vietoris square: `γ^* (cup with t)` on the `U`-piece. -/
theorem gammaComp_sq (X : TopCat) (A U V : Set X) (k : ℕ) :
    (dualComplexMap ℤ (relMVUV X A U V) (relMVUU X A U V) (HMV.gamma X A U V)).f k
      ≫ (dualComplexMap ℤ (smallInChains U V (U∩V)) (relMVUV X A U V) (cokernel.π (relMVτ₁ U V A))).f k
    = (dualComplexMap ℤ (smallInChains U V U) (relMVUU X A U V) (cokernel.π (relMVτ₂U U V A))).f k
      ≫ (dualComplexMap ℤ (smallInChains U V (U∩V)) (smallInChains U V U) (subInclChain U V (Set.inter_subset_left : U∩V ⊆ U))).f k := by
  calc (dualComplexMap ℤ (relMVUV X A U V) (relMVUU X A U V) (HMV.gamma X A U V)).f k
        ≫ (dualComplexMap ℤ (smallInChains U V (U∩V)) (relMVUV X A U V) (cokernel.π (relMVτ₁ U V A))).f k
      = (dualComplexMap ℤ (relMVUV X A U V) (relMVUU X A U V) (HMV.gamma X A U V)
          ≫ dualComplexMap ℤ (smallInChains U V (U∩V)) (relMVUV X A U V) (cokernel.π (relMVτ₁ U V A))).f k
        := (HomologicalComplex.comp_f _ _ k).symm
    _ = (dualComplexMap ℤ (smallInChains U V (U∩V)) (relMVUU X A U V) (cokernel.π (relMVτ₁ U V A) ≫ HMV.gamma X A U V)).f k
        := congrArg (fun φ => φ.f k) (dualComplexMap_comp ℤ (C := smallInChains U V (U∩V)) (D := relMVUV X A U V) (E := relMVUU X A U V)
              (f := cokernel.π (relMVτ₁ U V A)) (g := HMV.gamma X A U V)).symm
    _ = (dualComplexMap ℤ (smallInChains U V (U∩V)) (relMVUU X A U V) (subInclChain U V (Set.inter_subset_left : U∩V ⊆ U) ≫ cokernel.π (relMVτ₂U U V A))).f k
        := congrArg (fun φ => (dualComplexMap ℤ (smallInChains U V (U∩V)) (relMVUU X A U V) φ).f k) (HMV.gamma_comp X A U V)
    _ = ((dualComplexMap ℤ (smallInChains U V U) (relMVUU X A U V) (cokernel.π (relMVτ₂U U V A)))
          ≫ (dualComplexMap ℤ (smallInChains U V (U∩V)) (smallInChains U V U) (subInclChain U V (Set.inter_subset_left : U∩V ⊆ U)))).f k
        := congrArg (fun φ => φ.f k) (dualComplexMap_comp ℤ (C := smallInChains U V (U∩V)) (D := smallInChains U V U) (E := relMVUU X A U V)
              (f := subInclChain U V (Set.inter_subset_left : U∩V ⊆ U)) (g := cokernel.π (relMVτ₂U U V A)))
    _ = _ := HomologicalComplex.comp_f _ _ k

/-- The degreewise Mayer--Vietoris square: `δ^* (cup with t)` on the `V`-piece. -/
theorem deltaComp_sq (X : TopCat) (A U V : Set X) (k : ℕ) :
    (dualComplexMap ℤ (relMVUV X A U V) (relMVVV X A U V) (HMV.delta X A U V)).f k
      ≫ (dualComplexMap ℤ (smallInChains U V (U∩V)) (relMVUV X A U V) (cokernel.π (relMVτ₁ U V A))).f k
    = (dualComplexMap ℤ (smallInChains U V V) (relMVVV X A U V) (cokernel.π (relMVτ₂V U V A))).f k
      ≫ (dualComplexMap ℤ (smallInChains U V (U∩V)) (smallInChains U V V) (subInclChain U V (Set.inter_subset_right : U∩V ⊆ V))).f k := by
  calc (dualComplexMap ℤ (relMVUV X A U V) (relMVVV X A U V) (HMV.delta X A U V)).f k
        ≫ (dualComplexMap ℤ (smallInChains U V (U∩V)) (relMVUV X A U V) (cokernel.π (relMVτ₁ U V A))).f k
      = (dualComplexMap ℤ (relMVUV X A U V) (relMVVV X A U V) (HMV.delta X A U V)
          ≫ dualComplexMap ℤ (smallInChains U V (U∩V)) (relMVUV X A U V) (cokernel.π (relMVτ₁ U V A))).f k
        := (HomologicalComplex.comp_f _ _ k).symm
    _ = (dualComplexMap ℤ (smallInChains U V (U∩V)) (relMVVV X A U V) (cokernel.π (relMVτ₁ U V A) ≫ HMV.delta X A U V)).f k
        := congrArg (fun φ => φ.f k) (dualComplexMap_comp ℤ (C := smallInChains U V (U∩V)) (D := relMVUV X A U V) (E := relMVVV X A U V)
              (f := cokernel.π (relMVτ₁ U V A)) (g := HMV.delta X A U V)).symm
    _ = (dualComplexMap ℤ (smallInChains U V (U∩V)) (relMVVV X A U V) (subInclChain U V (Set.inter_subset_right : U∩V ⊆ V) ≫ cokernel.π (relMVτ₂V U V A))).f k
        := congrArg (fun φ => (dualComplexMap ℤ (smallInChains U V (U∩V)) (relMVVV X A U V) φ).f k) (HMV.delta_comp X A U V)
    _ = ((dualComplexMap ℤ (smallInChains U V V) (relMVVV X A U V) (cokernel.π (relMVτ₂V U V A)))
          ≫ (dualComplexMap ℤ (smallInChains U V (U∩V)) (smallInChains U V V) (subInclChain U V (Set.inter_subset_right : U∩V ⊆ V)))).f k
        := congrArg (fun φ => φ.f k) (dualComplexMap_comp ℤ (C := smallInChains U V (U∩V)) (D := smallInChains U V V) (E := relMVVV X A U V)
              (f := subInclChain U V (Set.inter_subset_right : U∩V ⊆ V)) (g := cokernel.π (relMVτ₂V U V A)))
    _ = _ := HomologicalComplex.comp_f _ _ k

/-! ## The cup product commutes with the first Mayer--Vietoris map -/

/-- **The `U`-component**: the cup product commutes with `γ`. -/
theorem coreU (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n)
    (htU : t ∈ relKern ℤ X (U ∩ A) n) (htW : t ∈ relKern ℤ X (U ∩ V ∩ A) n) :
    cupDescendRel X U V (Set.inter_subset_left : U ∩ A ⊆ U) n p t htU
      ≫ (dualComplexMap ℤ (relMVUV X A U V) (relMVUU X A U V) (HMV.gamma X A U V)).f (p+n)
    = (dualComplexMap ℤ (smallInChains U V (U∩V)) (smallInChains U V U) (subInclChain U V (Set.inter_subset_left : U∩V ⊆ U))).f p
      ≫ cupDescendRel X U V (Set.inter_subset_left : U∩V∩A ⊆ U∩V) n p t htW := by
  haveI hm : Mono ((dualComplexMap ℤ (smallInChains U V (U∩V)) (relMVUV X A U V) (cokernel.π (relMVτ₁ U V A))).f (p+n)) :=
    mono_dualComplexMapComp_of_epi (cokernel.π (relMVτ₁ U V A)) (p+n) (epi_cokernelπ_f (relMVτ₁ U V A) (p+n))
  rw [← cancel_mono ((dualComplexMap ℤ (smallInChains U V (U∩V)) (relMVUV X A U V) (cokernel.π (relMVτ₁ U V A))).f (p+n))]
  rw [Category.assoc, Category.assoc]
  rw [gammaComp_sq]
  conv_lhs => rw [← Category.assoc]
  erw [cupHomMap_spec, cupHomMap_spec]
  exact cupHomMap_restrict X U V (Set.inter_subset_left : U∩V ⊆ U) n p t

/-- **The `V`-component**: the cup product commutes with `δ`. -/
theorem coreV (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n)
    (htV : t ∈ relKern ℤ X (V ∩ A) n) (htW : t ∈ relKern ℤ X (U ∩ V ∩ A) n) :
    cupDescendRel X U V (Set.inter_subset_left : V ∩ A ⊆ V) n p t htV
      ≫ (dualComplexMap ℤ (relMVUV X A U V) (relMVVV X A U V) (HMV.delta X A U V)).f (p+n)
    = (dualComplexMap ℤ (smallInChains U V (U∩V)) (smallInChains U V V) (subInclChain U V (Set.inter_subset_right : U∩V ⊆ V))).f p
      ≫ cupDescendRel X U V (Set.inter_subset_left : U∩V∩A ⊆ U∩V) n p t htW := by
  haveI hm : Mono ((dualComplexMap ℤ (smallInChains U V (U∩V)) (relMVUV X A U V) (cokernel.π (relMVτ₁ U V A))).f (p+n)) :=
    mono_dualComplexMapComp_of_epi (cokernel.π (relMVτ₁ U V A)) (p+n) (epi_cokernelπ_f (relMVτ₁ U V A) (p+n))
  rw [← cancel_mono ((dualComplexMap ℤ (smallInChains U V (U∩V)) (relMVUV X A U V) (cokernel.π (relMVτ₁ U V A))).f (p+n))]
  rw [Category.assoc, Category.assoc]
  rw [deltaComp_sq]
  conv_lhs => rw [← Category.assoc]
  erw [cupHomMap_spec, cupHomMap_spec]
  exact cupHomMap_restrict X U V (Set.inter_subset_right : U∩V ⊆ V) n p t

/-! ## The cup product commutes with the two components of the first MV map -/

/-- The cup product with a relative cocycle commutes with the `U`-component of `hmvG`. -/
theorem cupU_gamma (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n) :
    cupU X A U V n p t ht
      ≫ (dualComplexMap ℤ (relMVUV X A U V) (relMVUU X A U V) (HMV.gamma X A U V)).f (p+n)
    = (dualComplexMap ℤ (relMVUV X ∅ U V) (relMVUU X ∅ U V) (HMV.gamma X ∅ U V)).f p
      ≫ cupUV X A U V n p t ht := by
  rw [cupU, cupUV]
  conv_lhs => rw [Category.assoc]
  rw [coreU]
  conv_lhs => rw [← Category.assoc]
  conv_rhs => rw [← Category.assoc]
  rw [gammaComp_sq]

/-- The cup product with a relative cocycle commutes with the `V`-component of `hmvG`. -/
theorem cupV_delta (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n) :
    cupV X A U V n p t ht
      ≫ (dualComplexMap ℤ (relMVUV X A U V) (relMVVV X A U V) (HMV.delta X A U V)).f (p+n)
    = (dualComplexMap ℤ (relMVUV X ∅ U V) (relMVVV X ∅ U V) (HMV.delta X ∅ U V)).f p
      ≫ cupUV X A U V n p t ht := by
  rw [cupV, cupUV]
  conv_lhs => rw [Category.assoc]
  rw [coreV]
  conv_lhs => rw [← Category.assoc]
  conv_rhs => rw [← Category.assoc]
  rw [deltaComp_sq]


/-! ## Biproduct calculus -/

/-- The inverse of `biprodXIso` composed with the `desc` of the components is `biprod.desc` of the
components of the maps. -/
theorem cupHMV_biprodXIso_inv_desc (K L M : CochainComplex (ModuleCat ℤ) ℕ) (α : K ⟶ M)
    (β : L ⟶ M) (i : ℕ) :
    (HomologicalComplex.biprodXIso K L i).inv ≫ (biprod.desc α β).f i
      = biprod.desc (α.f i) (β.f i) := by
  apply biprod.hom_ext'
  · rw [← Category.assoc, HomologicalComplex.inl_biprodXIso_inv,
      HomologicalComplex.biprod_inl_desc_f, biprod.inl_desc]
  · rw [← Category.assoc, HomologicalComplex.inr_biprodXIso_inv,
      HomologicalComplex.biprod_inr_desc_f, biprod.inr_desc]

/-- The `desc` of two maps of cochain complexes, in terms of the degreewise components. -/
theorem cupHMV_biprod_desc_f (K L M : CochainComplex (ModuleCat ℤ) ℕ) (α : K ⟶ M)
    (β : L ⟶ M) (i : ℕ) :
    (biprod.desc α β).f i
      = (HomologicalComplex.biprodXIso K L i).hom ≫ biprod.desc (α.f i) (β.f i) := by
  rw [← cupHMV_biprodXIso_inv_desc K L M α β i, ← Category.assoc, Iso.hom_inv_id,
    Category.id_comp]

/-- `biprod.map` commutes with `biprod.desc`. -/
theorem cupHMV_biprod_map_desc {W X Y Z P : ModuleCat ℤ} [HasBinaryBiproduct W X]
    [HasBinaryBiproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ P) (k : Z ⟶ P) :
    biprod.map f g ≫ biprod.desc h k = biprod.desc (f ≫ h) (g ≫ k) := by
  apply biprod.hom_ext'
  · rw [← Category.assoc, biprod.inl_map, Category.assoc, biprod.inl_desc, biprod.inl_desc]
  · rw [← Category.assoc, biprod.inr_map, Category.assoc, biprod.inr_desc, biprod.inr_desc]

/-- Postcomposing a `biprod.desc` with a map. -/
theorem cupHMV_biprod_desc_comp {W X Y Z : ModuleCat ℤ} [HasBinaryBiproduct W X]
    (f : W ⟶ Y) (g : X ⟶ Y) (h : Y ⟶ Z) :
    biprod.desc f g ≫ h = biprod.desc (f ≫ h) (g ≫ h) := by
  apply biprod.hom_ext'
  · rw [← Category.assoc, biprod.inl_desc, biprod.inl_desc]
  · rw [← Category.assoc, biprod.inr_desc, biprod.inr_desc]

/-- The negation of a morphism of cochain complexes, degreewise. -/
theorem cupHMV_neg_f {K L : CochainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L) (i : ℕ) :
    (-f).f i = -(f.f i) := by
  rw [← HomologicalComplex.eval_map, ← HomologicalComplex.eval_map]
  exact Functor.map_neg _

/-! ## Assembly: the cup product commutes with the second Mayer--Vietoris map -/

/-- The right-hand side of the Mayer--Vietoris square, in biprod-normal form. -/
theorem cupHMV_cupUV_hmvG (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n) :
    (hmvG X ∅ U V).f p ≫ cupUV X A U V n p t ht
      = (HomologicalComplex.biprodXIso (dualComplex ℤ (relMVUU X ∅ U V))
            (dualComplex ℤ (relMVVV X ∅ U V)) p).hom
        ≫ biprod.desc
            ((dualComplexMap ℤ (relMVUV X ∅ U V) (relMVUU X ∅ U V) (HMV.gamma X ∅ U V)).f p
              ≫ cupUV X A U V n p t ht)
            ((-(dualComplexMap ℤ (relMVUV X ∅ U V) (relMVVV X ∅ U V) (HMV.delta X ∅ U V))).f p
              ≫ cupUV X A U V n p t ht) := by
  calc (hmvG X ∅ U V).f p ≫ cupUV X A U V n p t ht
      = ((HomologicalComplex.biprodXIso (dualComplex ℤ (relMVUU X ∅ U V))
              (dualComplex ℤ (relMVVV X ∅ U V)) p).hom
          ≫ biprod.desc
              ((dualComplexMap ℤ (relMVUV X ∅ U V) (relMVUU X ∅ U V) (HMV.gamma X ∅ U V)).f p)
              ((-(dualComplexMap ℤ (relMVUV X ∅ U V) (relMVVV X ∅ U V) (HMV.delta X ∅ U V))).f p))
          ≫ cupUV X A U V n p t ht := by
        rw [hmvG, cupHMV_biprod_desc_f]
    _ = (HomologicalComplex.biprodXIso (dualComplex ℤ (relMVUU X ∅ U V))
            (dualComplex ℤ (relMVVV X ∅ U V)) p).hom
          ≫ (biprod.desc
              ((dualComplexMap ℤ (relMVUV X ∅ U V) (relMVUU X ∅ U V) (HMV.gamma X ∅ U V)).f p)
              ((-(dualComplexMap ℤ (relMVUV X ∅ U V) (relMVVV X ∅ U V) (HMV.delta X ∅ U V))).f p)
            ≫ cupUV X A U V n p t ht) :=
        Category.assoc _ _ _
    _ = (HomologicalComplex.biprodXIso (dualComplex ℤ (relMVUU X ∅ U V))
            (dualComplex ℤ (relMVVV X ∅ U V)) p).hom
          ≫ biprod.desc
              ((dualComplexMap ℤ (relMVUV X ∅ U V) (relMVUU X ∅ U V) (HMV.gamma X ∅ U V)).f p
                ≫ cupUV X A U V n p t ht)
              ((-(dualComplexMap ℤ (relMVUV X ∅ U V) (relMVVV X ∅ U V) (HMV.delta X ∅ U V))).f p
                ≫ cupUV X A U V n p t ht) :=
        congrArg (fun φ => (HomologicalComplex.biprodXIso (dualComplex ℤ (relMVUU X ∅ U V))
            (dualComplex ℤ (relMVVV X ∅ U V)) p).hom ≫ φ)
          (cupHMV_biprod_desc_comp
            ((dualComplexMap ℤ (relMVUV X ∅ U V) (relMVUU X ∅ U V) (HMV.gamma X ∅ U V)).f p)
            ((-(dualComplexMap ℤ (relMVUV X ∅ U V) (relMVVV X ∅ U V) (HMV.delta X ∅ U V))).f p)
            (cupUV X A U V n p t ht))

/-- **The cup product with a relative cocycle commutes with `hmvG`.** -/
theorem cupMid_hmvG (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ relKern ℤ X A n) :
    cupMid X A U V n p t ht ≫ (hmvG X A U V).f (p+n)
      = (hmvG X ∅ U V).f p ≫ cupUV X A U V n p t ht := by
  rw [cupMid]
  conv_lhs =>
    rw [hmvG]
    rw [Category.assoc, Category.assoc]
    rw [cupHMV_biprodXIso_inv_desc]
    rw [cupHMV_biprod_map_desc]
  rw [cupHMV_cupUV_hmvG]
  have hdesc : biprod.desc
        (cupU X A U V n p t ht
          ≫ (dualComplexMap ℤ (relMVUV X A U V) (relMVUU X A U V) (HMV.gamma X A U V)).f (p+n))
        (cupV X A U V n p t ht
          ≫ (-(dualComplexMap ℤ (relMVUV X A U V) (relMVVV X A U V) (HMV.delta X A U V))).f (p+n))
      = biprod.desc
        ((dualComplexMap ℤ (relMVUV X ∅ U V) (relMVUU X ∅ U V) (HMV.gamma X ∅ U V)).f p
          ≫ cupUV X A U V n p t ht)
        ((-(dualComplexMap ℤ (relMVUV X ∅ U V) (relMVVV X ∅ U V) (HMV.delta X ∅ U V))).f p
          ≫ cupUV X A U V n p t ht) := by
    apply biprod.hom_ext'
    · rw [biprod.inl_desc, biprod.inl_desc]
      exact cupU_gamma X A U V n p t ht
    · rw [biprod.inr_desc, biprod.inr_desc]
      rw [cupHMV_neg_f, cupHMV_neg_f, Preadditive.comp_neg, Preadditive.neg_comp, cupV_delta]
  rw [hdesc]

end

end Work.Thom

namespace Work.Thom

theorem cup_hmvG (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ Work.Cohomology.relKern ℤ X A n)
    (u : (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVUU X ∅ U V) ⊞
        Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVVV X ∅ U V)).X p) :
    ModuleCat.Hom.hom ((Work.Cohomology.hmvG X A U V).f (p + n))
        (ModuleCat.Hom.hom (Work.Thom.cupMid X A U V n p t ht) u)
      = ModuleCat.Hom.hom (Work.Thom.cupUV X A U V n p t ht)
          (ModuleCat.Hom.hom ((Work.Cohomology.hmvG X ∅ U V).f p) u) := by
  have key := cupMid_hmvG X A U V n p t ht
  have h := congrArg (fun φ => ModuleCat.Hom.hom φ u) key
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

end Work.Thom
