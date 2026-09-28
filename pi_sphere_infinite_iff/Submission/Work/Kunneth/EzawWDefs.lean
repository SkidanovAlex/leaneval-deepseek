import Mathlib
import Submission.Work.Kunneth.EZAWHomotopy
import Submission.Work.Kunneth.EZAWDefs
import Submission.Work.Kunneth.EZAWPlan
import Submission.Work.Kunneth.ezaw_ind_nat
import Submission.Work.Kunneth.tChain_hom_ext

/-!
# The chain homotopy `ezMap ≫ awMap ≃ 𝟙` from the model chains `W`

This file assembles the second Eilenberg–Zilber homotopy from the acyclic-models data: a family
of model chains `W p q ∈ (tMod p q).X (p+q+1)` satisfying the recursion
`d (W p q) = dfc W p q` (file `EZAWDefs.lean`) produces the chain homotopy
`ezMap ≫ awMap ≃ 𝟙` on `C_*(X) ⊗_ℤ C_*(Y)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The two `ℤ`-actions on a `ℤ`-module commute. -/
instance smulCommClass_int_int (N : Type*) [AddCommGroup N] [Module ℤ N] : SMulCommClass ℤ ℤ N :=
  ⟨fun a b x => by rw [← mul_smul, ← mul_smul, mul_comm]⟩

/-! ## The two `ℤ`-actions on a `ModuleCat` object -/

/-- The canonical `ℤ`-action of an additive commutative group agrees with the one carried by any
`Module ℤ` structure on it (all such structures are propositionally equal). -/
lemma zsmulToSMul_eq' (M : Type*) [AddCommGroup M] [Module ℤ M] :
    (ZSMul.toSMul : SMul ℤ M) = (inferInstance : Module ℤ M).toDistribSMul.toSMul := by
  have h : (inferInstance : Module ℤ M) = AddCommGroup.toIntModule M := Subsingleton.elim _ _
  rw [h]
  rfl

/-! ## The classifying maps of the models -/

/-- The classifying map `Δ[p] ⟶ X` of a `p`-simplex `σ` of `X`. -/
noncomputable def cls (X : SSet) {p : ℕ} (σ : X _⦋p⦌) : SdS p ⟶ X := SSet.yonedaEquiv.symm σ

/-- The classifying map `tMod p q ⟶ tChain X Y` of a pair of simplices, written in the models:
`C_*(Δ[p]) ⊗_ℤ C_*(Δ[q]) ⟶ C_*(X) ⊗_ℤ C_*(Y)`. -/
noncomputable def cls2 (X Y : SSet) (p q : ℕ) (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    tMod p q ⟶ tChain X Y :=
  ind (cls X σ) (cls Y τ)

/-- The classifying map sends the universal simplex to the simplex it classifies. -/
lemma cls_univS (X : SSet) {p : ℕ} (σ : X _⦋p⦌) :
    (cls X σ).app (Opposite.op ⦋p⦌) (univS p) = σ := by
  simp [cls, univS]

/-- The classifying map of the `i`-th face. -/
lemma cls_delta (X : SSet) {p : ℕ} (σ : X _⦋p+1⦌) (i : Fin (p+2)) :
    cls X (X.δ i σ) = SSet.stdSimplex.map (SimplexCategory.δ i) ≫ cls X σ := by
  rw [cls, cls]
  exact (SSet.yonedaEquiv_symm_naturality_left (SimplexCategory.δ i) σ).symm

/-- The classifying map of a pair of simplices, on the universal element. -/
lemma cls2_U (X Y : SSet) (p q : ℕ) (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    ((cls2 X Y p q σ τ).f (p + q)).hom (U p q)
      = tpLof (sChain X) (sChain Y) (p + q) ⟨(p, q), rfl⟩
          (genCh X σ ⊗ₜ[ℤ] genCh Y τ) := by
  rw [U]
  show (tpMapLin (sChain (SdS p)) (sChain X) (sChain (SdS q)) (sChain Y)
      (SSet.chainComplexMap (cls X σ) zz) (SSet.chainComplexMap (cls Y τ) zz) (p + q))
      (tpLof (sMod p) (sMod q) (p + q) ⟨(p, q), rfl⟩
        (genCh (SdS p) (univS p) ⊗ₜ[ℤ] genCh (SdS q) (univS q))) = _
  rw [tpMapLin_tmul, EZHom.genCh_chainComplexMap, EZHom.genCh_chainComplexMap,
    cls_univS, cls_univS]

/-! ## The intertwining of the classifying maps with the cofaces -/

/-- The first coface of the model intertwines the classifying maps. -/
lemma phiMod_cls2 (X Y : SSet) (p q : ℕ) (i : Fin (p+2))
    (σ : X _⦋p+1⦌) (τ : Y _⦋q⦌) :
    phiMod p q i ≫ cls2 X Y (p+1) q σ τ = cls2 X Y p q (X.δ i σ) τ := by
  rw [cls2, cls2, phiMod, ind, ind, ind, tpMap_comp]
  congr 1
  · rw [← chainComplexMap_comp, ← cls_delta]
  · rw [chainComplexMap_id, Category.id_comp]

/-- The second coface of the model intertwines the classifying maps. -/
lemma psiMod_cls2 (X Y : SSet) (p q : ℕ) (j : Fin (q+2))
    (σ : X _⦋p⦌) (τ : Y _⦋q+1⦌) :
    psiMod p q j ≫ cls2 X Y p (q+1) σ τ = cls2 X Y p q σ (Y.δ j τ) := by
  rw [cls2, cls2, psiMod, ind, ind, ind, tpMap_comp]
  congr 1
  · rw [chainComplexMap_id, Category.id_comp]
  · rw [← chainComplexMap_comp, ← cls_delta]

/-! ## The summands of the homotopy -/

/-- The linear combination of a family scaled by a scalar is the scalar multiple of the linear
combination. -/
lemma LC_smul_family {α : Type*} {N : Type*} [AddCommGroup N] [Module ℤ N]
    (c : ℤ) (G : α → N) :
    Finsupp.linearCombination ℤ (fun a => c • G a) = c • Finsupp.linearCombination ℤ G := by
  refine LinearMap.ext (fun u => ?_)
  induction u using Finsupp.induction with
  | zero => simp
  | single_add a b f hb ha ih =>
      rw [map_add, map_add, ih,
        show (c • (Finsupp.linearCombination ℤ G)) (Finsupp.single a b)
            = c • ((Finsupp.linearCombination ℤ G) (Finsupp.single a b)) from rfl,
        Finsupp.linearCombination_single, Finsupp.linearCombination_single]
      rw [smul_comm]

/-- The value of the `(p,q)`-summand of the homotopy on a pair of chains, as a function of the two
variables: the double linear extension of the values of `W p q` along the classifying maps. -/
noncomputable def Hf (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1)))
    (p q : ℕ) (x : ↥((sChain X).X p)) (y : ↥((sChain Y).X q)) :
    ↥((tChain X Y).X (p + q + 1)) :=
  (Finsupp.linearCombination ℤ (fun σ : X _⦋p⦌ =>
      (Finsupp.linearCombination ℤ (fun τ : Y _⦋q⦌ =>
        ((cls2 X Y p q σ τ).f (p + q + 1)).hom (W p q)))
      ((Work.Cohomology.Crux33.coords Y q) y)))
    ((Work.Cohomology.Crux33.coords X p) x)

/-- The value of `Hf` on a pair of generators. -/
lemma Hf_gen (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1)))
    (p q : ℕ) (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    Hf X Y W p q (genCh X σ) (genCh Y τ)
      = ((cls2 X Y p q σ τ).f (p + q + 1)).hom (W p q) := by
  have hX : (Work.Cohomology.Crux33.coords X p) (genCh X σ) = Finsupp.single σ (1:ℤ) :=
    Work.Cohomology.Crux33.coords_ι X p σ
  have hY : (Work.Cohomology.Crux33.coords Y q) (genCh Y τ) = Finsupp.single τ (1:ℤ) :=
    Work.Cohomology.Crux33.coords_ι Y q τ
  rw [Hf, hX, hY, Finsupp.linearCombination_single, Finsupp.linearCombination_single]
  rw [← zsmulToSMul_eq' (↥((tChain X Y).X (p + q + 1))), one_zsmul, one_zsmul]

/-- Additivity of `Hf` in the first variable. -/
lemma Hf_add_left (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ)
    (x₁ x₂ : ↥((sChain X).X p)) (y : ↥((sChain Y).X q)) :
    Hf X Y W p q (x₁ + x₂) y = Hf X Y W p q x₁ y + Hf X Y W p q x₂ y := by
  simp only [Hf, map_add, Finsupp.linearCombination_apply, Finsupp.sum]

/-- Compatiblity of `Hf` with the scalars in the first variable. -/
lemma Hf_smul_left (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ)
    (c : ℤ) (x : ↥((sChain X).X p)) (y : ↥((sChain Y).X q)) :
    Hf X Y W p q (c • x) y = c • Hf X Y W p q x y := by
  simp only [Hf, map_zsmul, Finsupp.linearCombination_apply, Finsupp.sum]

/-- Additivity of `Hf` in the second variable. -/
lemma Hf_add_right (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ)
    (x : ↥((sChain X).X p)) (y₁ y₂ : ↥((sChain Y).X q)) :
    Hf X Y W p q x (y₁ + y₂) = Hf X Y W p q x y₁ + Hf X Y W p q x y₂ := by
  simp only [Hf, map_add, Finsupp.linearCombination_apply, Finsupp.sum, smul_add,
    Finset.sum_add_distrib]

/-- Compatibility of `Hf` with the scalars in the second variable. -/
lemma Hf_smul_right (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ)
    (c : ℤ) (x : ↥((sChain X).X p)) (y : ↥((sChain Y).X q)) :
    Hf X Y W p q x (c • y) = c • Hf X Y W p q x y := by
  simp only [Hf]
  conv_lhs => rw [show (fun σ : X _⦋p⦌ => (Finsupp.linearCombination ℤ (fun τ : Y _⦋q⦌ =>
        ((cls2 X Y p q σ τ).f (p + q + 1)).hom (W p q)))
        ((Work.Cohomology.Crux33.coords Y q) (c • y)))
      = (fun σ : X _⦋p⦌ => c • ((Finsupp.linearCombination ℤ (fun τ : Y _⦋q⦌ =>
        ((cls2 X Y p q σ τ).f (p + q + 1)).hom (W p q)))
        ((Work.Cohomology.Crux33.coords Y q) y))) from
      funext (fun σ => by rw [map_zsmul, map_zsmul])]
  rw [LC_smul_family]
  rfl

/-- `Hf` vanishes when the first variable does. -/
lemma Hf_zero_left (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ)
    (y : ↥((sChain Y).X q)) : Hf X Y W p q 0 y = 0 := by
  simp only [Hf, map_zero, Finsupp.linearCombination_apply, Finsupp.sum]

/-- `Hf` vanishes when the second variable does. -/
lemma Hf_zero_right (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ)
    (x : ↥((sChain X).X p)) : Hf X Y W p q x 0 = 0 := by
  simp only [Hf, map_zero, Finsupp.linearCombination_apply, Finsupp.sum, smul_zero,
    Finset.sum_const_zero]

/-- `Hf` as an additive homomorphism in its second variable. -/
noncomputable def Hadd2 (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1)))
    (p q : ℕ) (x : ↥((sChain X).X p)) : ↥((sChain Y).X q) →+ ↥((tChain X Y).X (p + q + 1)) :=
  AddMonoidHom.mk' (fun y => Hf X Y W p q x y) (fun y₁ y₂ => Hf_add_right X Y W p q x y₁ y₂)

/-- `Hf` as an additive homomorphism in its first variable, with values additive homomorphisms. -/
noncomputable def Hadd (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ) :
    ↥((sChain X).X p) →+ (↥((sChain Y).X q) →+ ↥((tChain X Y).X (p + q + 1))) where
  toFun m := Hadd2 X Y W p q m
  map_zero' := by
    refine AddMonoidHom.ext (fun n => ?_)
    exact Hf_zero_left X Y W p q n
  map_add' m₁ m₂ := by
    refine AddMonoidHom.ext (fun n => ?_)
    exact Hf_add_left X Y W p q m₁ m₂ n

/-- The generator of the `(p,q)`-summand of `tChain X Y`, in total degree `p+q`. -/
noncomputable def genXY (X Y : SSet) {p q : ℕ} (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    ↥((tChain X Y).X (p + q)) :=
  tpLof (sChain X) (sChain Y) (p + q) ⟨(p, q), rfl⟩ (genCh X σ ⊗ₜ[ℤ] genCh Y τ)

/-- **The `(p,q)`-summand of the homotopy**: the bilinear extension of `Hf`. -/
noncomputable def Hsum (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ) :
    tpSummand (sChain X) (sChain Y) p q →ₗ[ℤ] ↥((tChain X Y).X (p + q + 1)) :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (Hf X Y W p q) (Hf_add_left X Y W p q)
    (fun c m n => by
      rw [← zsmulToSMul_eq' (↥((sChain X).X p)),
        ← zsmulToSMul_eq' (↥((tChain X Y).X (p + q + 1)))]
      exact Hf_smul_left X Y W p q c m n)
    (Hf_add_right X Y W p q)
    (fun c m n => by
      rw [← zsmulToSMul_eq' (↥((sChain Y).X q)),
        ← zsmulToSMul_eq' (↥((tChain X Y).X (p + q + 1)))]
      exact Hf_smul_right X Y W p q c m n))

/-- The value of the summand map on a pair of generators. -/
lemma Hsum_tmul (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ)
    (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    Hsum X Y W p q (genCh X σ ⊗ₜ[ℤ] genCh Y τ)
      = ((cls2 X Y p q σ τ).f (p + q + 1)).hom (W p q) := by
  show TensorProduct.lift (LinearMap.mk₂ ℤ (Hf X Y W p q) _ _ _ _)
      (genCh X σ ⊗ₜ[ℤ] genCh Y τ) = _
  rw [TensorProduct.lift.tmul, LinearMap.mk₂_apply]
  exact Hf_gen X Y W p q σ τ

/-- The data of the summand maps of the homotopy: for every bidegree `(p,q)` a `ℤ`-linear map
out of the summand `C_p(X) ⊗_ℤ C_q(Y)` whose value on the generators is prescribed by the model
chains `W`. -/
structure HsumData (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) where
  toLin : ∀ p q, tpSummand (sChain X) (sChain Y) p q →ₗ[ℤ] ↥((tChain X Y).X (p + q + 1))
  toLin_gen : ∀ (p q : ℕ) (σ : X _⦋p⦌) (τ : Y _⦋q⦌),
    toLin p q (genCh X σ ⊗ₜ[ℤ] genCh Y τ)
      = ((cls2 X Y p q σ τ).f (p + q + 1)).hom (W p q)

/-- The summand maps exist: the bilinear extension of `Hf` provides them. -/
theorem exists_HsumData (X Y : SSet)
    (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) :
    Nonempty (HsumData X Y W) :=
  ⟨{ toLin := Hsum X Y W
     toLin_gen := fun p q σ τ => Hsum_tmul X Y W p q σ τ }⟩


/-- Transport of elements of a `ℤ`-module along an equality of modules, as a linear map. -/
noncomputable def chcast {M N : ModuleCat ℤ} (h : M = N) : ↥M →ₗ[ℤ] ↥N :=
  (eqToIso h).hom.hom

/-- Transport along a reflexive equality is the identity. -/
lemma chcast_self {M : ModuleCat ℤ} (h : M = M) (x : ↥M) : chcast h x = x := by
  rw [Subsingleton.elim h rfl]
  rfl

/-- **The `n`-th component of the chain homotopy**: the direct sum of the summand maps
`Hsum p q`, the `(p,q)`-summand being transported to total degree `n + 1`. -/
noncomputable def H (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1)))
    (hs : HsumData X Y W) (n : ℕ) :
    (tChain X Y).X n ⟶ (tChain X Y).X (n + 1) :=
  ModuleCat.ofHom (DirectSum.toModule ℤ (tpIdx n) ↥((tChain X Y).X (n + 1))
    (fun pq => (chcast (congrArg (fun k => (tChain X Y).X (k + 1)) pq.2)).comp
      (hs.toLin pq.1.1 pq.1.2)))


/-- The `(i,j)`-component of the homotopy, indexed by the source and target degrees: the `i`-th
component `H i` transported to the target degree `i+1`, and zero away from `j = i+1`. -/
noncomputable def homMap (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1)))
    (hs : HsumData X Y W) (i j : ℕ) :
    (tChain X Y).X i ⟶ (tChain X Y).X j :=
  if h : i + 1 = j then H X Y W hs i ≫ eqToHom (congrArg (fun k => (tChain X Y).X k) h) else 0

/-- The component `homMap i (i+1)` is `H i`. -/
lemma homMap_succ (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1)))
    (hs : HsumData X Y W) (i : ℕ) : homMap X Y W hs i (i + 1) = H X Y W hs i := by
  rw [homMap, dif_pos rfl]
  exact Category.comp_id _

/-- The components of `homMap` away from `j = i+1` vanish. -/
lemma homMap_neg (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1)))
    (hs : HsumData X Y W) {i j : ℕ} (h : ¬ i + 1 = j) : homMap X Y W hs i j = 0 := by
  rw [homMap, dif_neg h]

/-- The value of the homotopy on any generator of the tensor complex. -/
lemma H_tpLof (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1)))
    (hs : HsumData X Y W)
    (n p q : ℕ) (hpq : p + q = n) (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    (H X Y W hs n).hom
        (tpLof (sChain X) (sChain Y) n ⟨(p, q), hpq⟩ (genCh X σ ⊗ₜ[ℤ] genCh Y τ))
      = chcast (congrArg (fun k => (tChain X Y).X (k + 1)) hpq)
          (((cls2 X Y p q σ τ).f (p + q + 1)).hom (W p q)) := by
  subst hpq
  rw [H, ModuleCat.hom_ofHom]
  show (DirectSum.toModule ℤ (tpIdx (p + q)) ↥((tChain X Y).X (p + q + 1))
      (fun pq => (chcast (congrArg (fun k => (tChain X Y).X (k + 1)) pq.2)).comp
        (hs.toLin pq.1.1 pq.1.2)))
      ((DirectSum.lof ℤ (tpIdx (p + q))
        (fun rs => tpSummand (sChain X) (sChain Y) rs.1.1 rs.1.2) ⟨(p, q), rfl⟩)
        (genCh X σ ⊗ₜ[ℤ] genCh Y τ)) = _
  rw [DirectSum.toModule_lof, LinearMap.comp_apply, hs.toLin_gen]

/-- The value of the homotopy on a generator, in the total degree `p+q`. -/
lemma H_gen (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1)))
    (hs : HsumData X Y W) (p q : ℕ)
    (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    (H X Y W hs (p + q)).hom
        (tpLof (sChain X) (sChain Y) (p + q) ⟨(p, q), rfl⟩
          (genCh X σ ⊗ₜ[ℤ] genCh Y τ))
      = ((cls2 X Y p q σ τ).f (p + q + 1)).hom (W p q) := by
  rw [H_tpLof X Y W hs (p+q) p q rfl]
  exact chcast_self _ _

end

end Work.Kunneth
