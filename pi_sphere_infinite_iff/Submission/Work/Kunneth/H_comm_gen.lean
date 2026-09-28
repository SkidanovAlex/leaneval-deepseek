import Mathlib
import Submission.Work.Kunneth.EzawWDefs

/-!
# The commutation identity for the Eilenberg–Zilber homotopy `ezMap ≫ awMap ≃ 𝟙`

Given a family of model chains `W p q ∈ (tMod p q).X (p+q+1)` satisfying the acyclic-models
recursion `d (W p q) = dfc W p q` (`Submission/Work/Kunneth/EzawWDefs.lean`), and a choice `hs`
of summand maps for the homotopy `H`, the chain homotopy identity holds on the generators
`genXY X Y σ τ` of the tensor product `C_*(X) ⊗_ℤ C_*(Y)`:

`(Ezaw X Y) (genXY σ τ) = H (d (genXY σ τ)) + d (H (genXY σ τ)) + genXY σ τ`.

This is the pointwise input for the acyclic-models assembly of the second Eilenberg–Zilber
homotopy `ezMap ≫ awMap ≃ 𝟙`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

universe u

/-- Two `cast`s along (distinct proofs of) the same equality agree. -/
lemma cast_proof_irrel {α : Type u} {β : Type u} {h h' : α = β} (x : α) : cast h x = cast h' x := by
  rw [Subsingleton.elim h h']

/-- Transport of elements of a chain complex along an equality of degrees. -/
def Tcast (C : ChainComplex (ModuleCat ℤ) ℕ) {n m : ℕ} (h : n = m) : ↥(C.X n) → ↥(C.X m) :=
  fun x => cast (congrArg (fun k => ↥(C.X k)) h) x

@[simp] lemma Tcast_rfl (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (x : ↥(C.X n)) :
    Tcast C (rfl : n = n) x = x := rfl

lemma Tcast_congr (C : ChainComplex (ModuleCat ℤ) ℕ) {n m : ℕ} {h h' : n = m} (x : ↥(C.X n)) :
    Tcast C h x = Tcast C h' x := by
  rw [Subsingleton.elim h h']

lemma Tcast_rfl' (C : ChainComplex (ModuleCat ℤ) ℕ) {n : ℕ} (h : n = n) (x : ↥(C.X n)) :
    Tcast C h x = x := by
  rw [Tcast_congr C (h := h) (h' := rfl) x, Tcast_rfl]

lemma Tcast_trans (C : ChainComplex (ModuleCat ℤ) ℕ) {n m k : ℕ} (h : n = m) (h' : m = k)
    (x : ↥(C.X n)) : Tcast C h' (Tcast C h x) = Tcast C (h.trans h') x := by
  subst h; subst h'; rfl

lemma Tcast_add (C : ChainComplex (ModuleCat ℤ) ℕ) {n m : ℕ} (h : n = m)
    (x y : ↥(C.X n)) : Tcast C h (x + y) = Tcast C h x + Tcast C h y := by
  subst h; rfl

lemma Tcast_smul (C : ChainComplex (ModuleCat ℤ) ℕ) {n m : ℕ} (h : n = m) (c : ℤ)
    (x : ↥(C.X n)) : Tcast C h (c • x) = c • Tcast C h x := by
  subst h; rfl

lemma Tcast_zero (C : ChainComplex (ModuleCat ℤ) ℕ) {n m : ℕ} (h : n = m) :
    Tcast C h (0 : ↥(C.X n)) = 0 := by
  subst h; rfl

lemma Tcast_sum (C : ChainComplex (ModuleCat ℤ) ℕ) {n m : ℕ} (h : n = m) {ι : Type*}
    (s : Finset ι) (f : ι → ↥(C.X n)) :
    Tcast C h (∑ i ∈ s, f i) = ∑ i ∈ s, Tcast C h (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [Tcast_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Tcast_add, ih]

lemma Tcast_eq_eqToHom (C : ChainComplex (ModuleCat ℤ) ℕ) {n m : ℕ} (h : n = m)
    (x : ↥(C.X n)) :
    Tcast C h x = (ModuleCat.Hom.hom (eqToHom (congrArg C.X h))) x := by
  subst h; rfl

lemma chcast_eq_Tcast {M N : ModuleCat ℤ} (h : M = N) (x : ↥M) :
    (chcast h) x = cast (congrArg (fun K : ModuleCat ℤ => ↥K) h) x := by
  subst h; rfl

lemma chcast_congrArg_Tcast (C : ChainComplex (ModuleCat ℤ) ℕ) {n m : ℕ} (h : n = m)
    (x : ↥(C.X n)) : (chcast (congrArg C.X h)) x = Tcast C h x := by
  rw [chcast_eq_Tcast]
  exact cast_proof_irrel x

lemma chcast_succ_Tcast (C : ChainComplex (ModuleCat ℤ) ℕ) {n m : ℕ} (h : n = m)
    (x : ↥(C.X (n+1))) : (chcast (congrArg (fun k => C.X (k+1)) h)) x
      = Tcast C (congrArg (fun k => k+1) h) x := by
  rw [chcast_eq_Tcast]
  exact cast_proof_irrel x

/-- A chain map commutes with the transport `Tcast`. -/
lemma Tcast_natural {C D : ChainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) {n m : ℕ} (h : n = m)
    (x : ↥(C.X n)) :
    (ModuleCat.Hom.hom (φ.f m)) (Tcast C h x)
      = Tcast D h ((ModuleCat.Hom.hom (φ.f n)) x) := by
  subst h; rfl

/-- `dcast` is `Tcast` for the model complexes. -/
lemma dcast_eq_Tcast (p q : ℕ) {n m : ℕ} (h : n = m) (x : ↥((tMod p q).X n)) :
    dcast p q h x = Tcast (tMod p q) h x := rfl

/-- `H` on an arbitrary element of a summand of the tensor complex. -/
lemma H_tpLof_gen (X Y : SSet) (W : (p q : ℕ) → ↥((Work.Kunneth.tMod p q).X (p + q + 1)))
    (hs : HsumData X Y W) (n p q : ℕ) (hpq : p + q = n)
    (z : tpSummand (sChain X) (sChain Y) p q) :
    (H X Y W hs n).hom (tpLof (sChain X) (sChain Y) n ⟨(p, q), hpq⟩ z)
      = Tcast (tChain X Y) (congrArg (fun k => k+1) hpq) (hs.toLin p q z) := by
  subst hpq
  rw [H, ModuleCat.hom_ofHom]
  show (DirectSum.toModule ℤ (tpIdx (p + q)) ↥((tChain X Y).X (p + q + 1))
      (fun pq => (chcast (congrArg (fun k => (tChain X Y).X (k + 1)) pq.2)).comp
        (hs.toLin pq.1.1 pq.1.2)))
      ((DirectSum.lof ℤ (tpIdx (p + q))
        (fun rs => tpSummand (sChain X) (sChain Y) rs.1.1 rs.1.2) ⟨(p, q), rfl⟩) z) = _
  rw [DirectSum.toModule_lof, LinearMap.comp_apply]
  exact chcast_succ_Tcast (tChain X Y) rfl (hs.toLin p q z)

/-- Element-level form of `phiMod_cls2`. -/
lemma cls2_phiMod_apply (X Y : SSet) (p q n : ℕ) (i : Fin (p + 2)) (σ : X _⦋p + 1⦌)
    (τ : Y _⦋q⦌) (x : ↥((tMod p q).X n)) :
    (ModuleCat.Hom.hom ((cls2 X Y (p + 1) q σ τ).f n))
        ((ModuleCat.Hom.hom ((phiMod p q i).f n)) x)
      = (ModuleCat.Hom.hom
          ((cls2 X Y p q ((ConcreteCategory.hom (SimplicialObject.δ X i)) σ) τ).f n)) x := by
  have h := congrArg
    (fun (φ : tMod p q ⟶ tChain X Y) => (ModuleCat.Hom.hom (φ.f n)) x)
    (phiMod_cls2 X Y p q i σ τ)
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- Element-level form of `psiMod_cls2`. -/
lemma cls2_psiMod_apply (X Y : SSet) (p q n : ℕ) (j : Fin (q + 2)) (σ : X _⦋p⦌)
    (τ : Y _⦋q + 1⦌) (x : ↥((tMod p q).X n)) :
    (ModuleCat.Hom.hom ((cls2 X Y p (q + 1) σ τ).f n))
        ((ModuleCat.Hom.hom ((psiMod p q j).f n)) x)
      = (ModuleCat.Hom.hom
          ((cls2 X Y p q σ ((ConcreteCategory.hom (SimplicialObject.δ Y j)) τ)).f n)) x := by
  have h := congrArg
    (fun (φ : tMod p q ⟶ tChain X Y) => (ModuleCat.Hom.hom (φ.f n)) x)
    (psiMod_cls2 X Y p q j σ τ)
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- Naturality of `Ezaw` with respect to the classifying maps, at the level of elements. -/
lemma Ezaw_cls2 (X Y : SSet) (p q n : ℕ) (σ : X _⦋p⦌) (τ : Y _⦋q⦌)
    (x : ↥((tMod p q).X n)) :
    (ModuleCat.Hom.hom ((Ezaw X Y).f n)) ((ModuleCat.Hom.hom ((cls2 X Y p q σ τ).f n)) x)
      = (ModuleCat.Hom.hom ((cls2 X Y p q σ τ).f n))
          ((ModuleCat.Hom.hom ((Ezaw (SdS p) (SdS q)).f n)) x) := by
  have h := congrArg (fun (φ : tMod p q ⟶ tChain X Y) => (ModuleCat.Hom.hom (φ.f n)) x)
    (ezaw_ind_nat (cls X σ) (cls Y τ))
  simpa only [cls2, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The value of `Ezaw` on the universal element of the model. -/
lemma Ezaw_U (p q : ℕ) :
    (ModuleCat.Hom.hom ((Ezaw (SdS p) (SdS q)).f (p + q))) (U p q) = Em p q + U p q := by
  have h : Em p q = (ModuleCat.Hom.hom ((Ezaw (SdS p) (SdS q)).f (p + q))) (U p q) - U p q := rfl
  rw [h]
  abel


/-- `cls2` of `psiT`. -/
lemma cls2_psiT (X Y : SSet) (W : (p q : ℕ) → ↥((Work.Kunneth.tMod p q).X (p + q + 1)))
    (p q : ℕ) (j : Fin (q + 2)) (σ : X _⦋p⦌) (τ : Y _⦋q + 1⦌) :
    (ModuleCat.Hom.hom ((cls2 X Y p (q + 1) σ τ).f (p + (q + 1)))) (psiT W p q j)
      = (ModuleCat.Hom.hom
          ((cls2 X Y p q σ ((ConcreteCategory.hom (SimplicialObject.δ Y j)) τ)).f (p + q + 1)))
          (W p q) := by
  rw [psiT]
  exact cls2_psiMod_apply X Y p q (p + q + 1) j σ τ (W p q)

/-- `cls2` of `phiT`. -/
lemma cls2_phiT (X Y : SSet) (W : (p q : ℕ) → ↥((Work.Kunneth.tMod p q).X (p + q + 1)))
    (p q : ℕ) (i : Fin (p + 2)) (σ : X _⦋p + 1⦌) (τ : Y _⦋q⦌) :
    (ModuleCat.Hom.hom ((cls2 X Y (p + 1) q σ τ).f ((p + 1) + q))) (phiT W p q i)
      = Tcast (tChain X Y) (Nat.add_right_comm p 1 q).symm
          ((ModuleCat.Hom.hom
            ((cls2 X Y p q ((ConcreteCategory.hom (SimplicialObject.δ X i)) σ) τ).f (p + q + 1)))
            (W p q)) := by
  rw [phiT, dcast_eq_Tcast, Tcast_natural]
  exact congrArg _ (cls2_phiMod_apply X Y p q (p + q + 1) i σ τ (W p q))

/-- The boundary of the universal model element, in the `(0, q+1)` case. -/
lemma dU_psi (Q : ℕ) :
    ((tMod 0 (Q + 1)).d (0 + (Q + 1)) (0 + Q)).hom (U 0 (Q + 1))
      = tpLof (sMod 0) (sMod (Q + 1)) (0 + Q) ⟨(0, Q), rfl⟩
          (genCh (SdS 0) (univS 0) ⊗ₜ[ℤ]
            ((sMod (Q + 1)).d (Q + 1) Q).hom (genCh (SdS (Q + 1)) (univS (Q + 1)))) := by
  have h1 : (tMod 0 (Q + 1)).d (0 + (Q + 1)) (0 + Q)
      = ModuleCat.ofHom (tpD (sMod 0) (sMod (Q + 1)) (0 + Q)) := tpC_d _ _ _
  rw [h1, ModuleCat.hom_ofHom]
  rw [show U 0 (Q + 1)
      = tpLof (sMod 0) (sMod (Q + 1)) ((0 + Q) + 1) ⟨(0, Q + 1), by omega⟩
          (genCh (SdS 0) (univS 0) ⊗ₜ[ℤ] genCh (SdS (Q + 1)) (univS (Q + 1))) from rfl]
  refine (tpD_lof_tmul (sMod 0) (sMod (Q + 1)) (0 + Q) ⟨(0, Q + 1), by omega⟩
    (genCh (SdS 0) (univS 0)) (genCh (SdS (Q + 1)) (univS (Q + 1)))).trans ?_
  rw [dif_neg (show ¬ (1:ℕ) ≤ 0 by omega), dif_pos (show (1:ℕ) ≤ Q + 1 by omega)]
  conv_lhs => rw [zero_add]
  rw [pow_zero, one_smul]
  rfl

/-- `cls2` on a summand of the tensor product, in the general bidegree form. -/
lemma cls2_tpLof' (X Y : SSet) (p q n : ℕ) (pq : tpIdx n) (σ : X _⦋p⦌) (τ : Y _⦋q⦌)
    (z : tpSummand (sMod p) (sMod q) pq.1.1 pq.1.2) :
    (ModuleCat.Hom.hom ((cls2 X Y p q σ τ).f n)) (tpLof (sMod p) (sMod q) n pq z)
      = tpLof (sChain X) (sChain Y) n pq ((TensorProduct.map
          ((SSet.chainComplexMap (cls X σ) zz).f pq.1.1).hom
          ((SSet.chainComplexMap (cls Y τ) zz).f pq.1.2).hom) z) := by
  show tpMapLin (sMod p) (sChain X) (sMod q) (sChain Y)
      (SSet.chainComplexMap (cls X σ) zz) (SSet.chainComplexMap (cls Y τ) zz) n
      (tpLof (sMod p) (sMod q) n pq z) = _
  exact tpMapLin_tpLof _ _ _ _ _ _ _ _ z

/-- The `(0,q+1)`-case computation: `H` on the boundary of the universal element, pushed through
the classifying maps. -/
lemma H_boundary_psi (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1)))
    (hs : HsumData X Y W) (Q : ℕ) (σ : X _⦋0⦌) (τ : Y _⦋Q+1⦌) :
    (H X Y W hs (0+Q)).hom ((ModuleCat.Hom.hom ((cls2 X Y 0 (Q+1) σ τ).f (0+Q)))
        (((tMod 0 (Q+1)).d (0+(Q+1)) (0+Q)).hom (U 0 (Q+1))))
      = ∑ j : Fin (Q+2), (-1:ℤ)^(j:ℕ) •
          (ModuleCat.Hom.hom ((cls2 X Y 0 (Q+1) σ τ).f (0+(Q+1)))) (psiT W 0 Q j) := by
  rw [dU_psi Q, cls2_tpLof', TensorProduct.map_tmul]
  rw [EZHom.genCh_chainComplexMap, cls_univS]
  rw [← Hom_comm_apply (SSet.chainComplexMap (cls Y τ) zz) (Q+1) Q (genCh (SdS (Q+1)) (univS (Q+1)))]
  rw [EZHom.genCh_chainComplexMap, cls_univS]
  rw [d_genCh Y Q τ]
  rw [H_tpLof_gen, Tcast_rfl']
  have h1 : genCh X σ ⊗ₜ[ℤ] (∑ j : Fin (Q+2), (-1:ℤ)^(j:ℕ) • genCh Y (Y.δ j τ))
      = ∑ j : Fin (Q+2), (-1:ℤ)^(j:ℕ) • (genCh X σ ⊗ₜ[ℤ] genCh Y (Y.δ j τ)) := by
    rw [TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl (fun j _ => tmul_smul_eq ((-1:ℤ)^(j:ℕ)) (genCh X σ) (genCh Y (Y.δ j τ)))
  rw [h1, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_zsmul, hs.toLin_gen, cls2_psiT]

/-- The boundary of the universal model element, in the `(p+1, 0)` case. -/
lemma dU_phi (P : ℕ) :
    ((tMod (P+1) 0).d (P+1) P).hom (U (P+1) 0)
      = tpLof (sMod (P+1)) (sMod 0) P ⟨(P, 0), rfl⟩
          (((sMod (P+1)).d (P+1) P).hom (genCh (SdS (P+1)) (univS (P+1)))
            ⊗ₜ[ℤ] genCh (SdS 0) (univS 0)) := by
  have h1 : (tMod (P+1) 0).d (P+1) P
      = ModuleCat.ofHom (tpD (sMod (P+1)) (sMod 0) P) := tpC_d _ _ _
  rw [h1, ModuleCat.hom_ofHom]
  rw [show U (P+1) 0 = tpLof (sMod (P+1)) (sMod 0) (P+1) ⟨(P+1, 0), rfl⟩
      (genCh (SdS (P+1)) (univS (P+1)) ⊗ₜ[ℤ] genCh (SdS 0) (univS 0)) from rfl]
  refine (tpD_lof_tmul (sMod (P+1)) (sMod 0) P ⟨(P+1, 0), rfl⟩
    (genCh (SdS (P+1)) (univS (P+1))) (genCh (SdS 0) (univS 0))).trans ?_
  rw [dif_pos (show (1:ℕ) ≤ P+1 by omega), dif_neg (show ¬ (1:ℕ) ≤ 0 by omega)]
  rw [add_zero]
  rfl

/-- The `(p+1,0)`-case computation: `H` on the boundary of the universal element, pushed through
the classifying maps. -/
lemma H_boundary_phi (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1)))
    (hs : HsumData X Y W) (P : ℕ) (σ : X _⦋P+1⦌) (τ : Y _⦋0⦌) :
    (H X Y W hs P).hom ((ModuleCat.Hom.hom ((cls2 X Y (P+1) 0 σ τ).f P))
        (((tMod (P+1) 0).d (P+1) P).hom (U (P+1) 0)))
      = ∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) •
          (ModuleCat.Hom.hom ((cls2 X Y (P+1) 0 σ τ).f (P+1))) (phiT W P 0 i) := by
  rw [dU_phi P, cls2_tpLof', TensorProduct.map_tmul]
  rw [← Hom_comm_apply (SSet.chainComplexMap (cls X σ) zz) (P+1) P (genCh (SdS (P+1)) (univS (P+1)))]
  rw [EZHom.genCh_chainComplexMap, cls_univS]
  rw [d_genCh X P σ]
  rw [EZHom.genCh_chainComplexMap, cls_univS]
  rw [H_tpLof_gen, Tcast_rfl']
  have h1 : (∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) • genCh X (X.δ i σ)) ⊗ₜ[ℤ] genCh Y τ
      = ∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) • (genCh X (X.δ i σ) ⊗ₜ[ℤ] genCh Y τ) := by
    rw [TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl (fun i _ => smul_tmul_eq ((-1:ℤ)^(i:ℕ)) (genCh X (X.δ i σ)) (genCh Y τ))
  rw [h1, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_zsmul, hs.toLin_gen, cls2_phiT, Tcast_rfl']


/-- The boundary of the universal model element, in the `(p+1, q+1)` case. -/
lemma dU_both (P Q : ℕ) :
    ((tMod (P+1) (Q+1)).d ((P+1)+(Q+1)) ((P+1)+(Q+1)-1)).hom (U (P+1) (Q+1))
      = tpLof (sMod (P+1)) (sMod (Q+1)) ((P+1)+(Q+1)-1) ⟨(P, Q+1), by omega⟩
          (((sMod (P+1)).d (P+1) P).hom (genCh (SdS (P+1)) (univS (P+1)))
            ⊗ₜ[ℤ] genCh (SdS (Q+1)) (univS (Q+1)))
        + (-1:ℤ)^(P+1) • tpLof (sMod (P+1)) (sMod (Q+1)) ((P+1)+(Q+1)-1) ⟨(P+1, Q), by omega⟩
          (genCh (SdS (P+1)) (univS (P+1))
            ⊗ₜ[ℤ] ((sMod (Q+1)).d (Q+1) Q).hom (genCh (SdS (Q+1)) (univS (Q+1)))) := by
  have h1 : ((tMod (P+1) (Q+1)).d ((P+1)+(Q+1)) ((P+1)+(Q+1)-1))
      = ModuleCat.ofHom (tpD (sMod (P+1)) (sMod (Q+1)) ((P+1)+(Q+1)-1)) := tpC_d _ _ _
  rw [h1, ModuleCat.hom_ofHom]
  rw [show U (P+1) (Q+1) = tpLof (sMod (P+1)) (sMod (Q+1)) (((P+1)+(Q+1)-1)+1)
        ⟨((P+1), (Q+1)), by omega⟩
        (genCh (SdS (P+1)) (univS (P+1)) ⊗ₜ[ℤ] genCh (SdS (Q+1)) (univS (Q+1))) from rfl]
  refine (tpD_lof_tmul (sMod (P+1)) (sMod (Q+1)) ((P+1)+(Q+1)-1)
    ⟨((P+1), (Q+1)), by omega⟩
    (genCh (SdS (P+1)) (univS (P+1))) (genCh (SdS (Q+1)) (univS (Q+1)))).trans ?_
  rw [dif_pos (show (1:ℕ) ≤ P+1 by omega), dif_pos (show (1:ℕ) ≤ Q+1 by omega)]
  rfl

/-- The `(p+1,q+1)`-case computation: `H` on the boundary of the universal element, pushed
through the classifying maps. -/
lemma H_boundary_both (X Y : SSet) (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1)))
    (hs : HsumData X Y W) (P Q : ℕ) (σ : X _⦋P+1⦌) (τ : Y _⦋Q+1⦌) :
    (H X Y W hs ((P+1)+(Q+1)-1)).hom
        ((ModuleCat.Hom.hom ((cls2 X Y (P+1) (Q+1) σ τ).f ((P+1)+(Q+1)-1)))
          (((tMod (P+1) (Q+1)).d ((P+1)+(Q+1)) ((P+1)+(Q+1)-1)).hom (U (P+1) (Q+1))))
      = (∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) •
            (ModuleCat.Hom.hom ((cls2 X Y (P+1) (Q+1) σ τ).f ((P+1)+(Q+1)))) (phiT W P (Q+1) i))
        + (-1:ℤ)^(P+1) • (∑ j : Fin (Q+2), (-1:ℤ)^(j:ℕ) •
            (ModuleCat.Hom.hom ((cls2 X Y (P+1) (Q+1) σ τ).f ((P+1)+(Q+1)))) (psiT W (P+1) Q j)) := by
  rw [dU_both P Q, map_add, map_zsmul, cls2_tpLof', cls2_tpLof']
  rw [map_add, map_zsmul, H_tpLof_gen, H_tpLof_gen]
  simp only [Tcast_rfl']
  rw [TensorProduct.map_tmul, TensorProduct.map_tmul]
  rw [← Hom_comm_apply (SSet.chainComplexMap (cls X σ) zz) (P+1) P (genCh (SdS (P+1)) (univS (P+1)))]
  rw [← Hom_comm_apply (SSet.chainComplexMap (cls Y τ) zz) (Q+1) Q (genCh (SdS (Q+1)) (univS (Q+1)))]
  simp only [EZHom.genCh_chainComplexMap, cls_univS]
  rw [d_genCh X P σ, d_genCh Y Q τ]
  have hz1 : (∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) • genCh X (X.δ i σ)) ⊗ₜ[ℤ] genCh Y τ
      = ∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) • (genCh X (X.δ i σ) ⊗ₜ[ℤ] genCh Y τ) := by
    rw [TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl (fun i _ => smul_tmul_eq ((-1:ℤ)^(i:ℕ)) (genCh X (X.δ i σ)) (genCh Y τ))
  have hz2 : genCh X σ ⊗ₜ[ℤ] (∑ j : Fin (Q+2), (-1:ℤ)^(j:ℕ) • genCh Y (Y.δ j τ))
      = ∑ j : Fin (Q+2), (-1:ℤ)^(j:ℕ) • (genCh X σ ⊗ₜ[ℤ] genCh Y (Y.δ j τ)) := by
    rw [TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl (fun j _ => tmul_smul_eq ((-1:ℤ)^(j:ℕ)) (genCh X σ) (genCh Y (Y.δ j τ)))
  rw [hz1, hz2]
  have hL1 : hs.toLin P (Q+1) (∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) • (genCh X (X.δ i σ) ⊗ₜ[ℤ] genCh Y τ))
      = ∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) •
          (ModuleCat.Hom.hom ((cls2 X Y P (Q+1) (X.δ i σ) τ).f (P+(Q+1)+1))) (W P (Q+1)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_zsmul, hs.toLin_gen]
  have hL2 : hs.toLin (P+1) Q (∑ j : Fin (Q+2), (-1:ℤ)^(j:ℕ) • (genCh X σ ⊗ₜ[ℤ] genCh Y (Y.δ j τ)))
      = ∑ j : Fin (Q+2), (-1:ℤ)^(j:ℕ) •
          (ModuleCat.Hom.hom ((cls2 X Y (P+1) Q σ (Y.δ j τ)).f ((P+1)+Q+1))) (W (P+1) Q) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_zsmul, hs.toLin_gen]
  rw [hL1, hL2]
  simp only [cls2_phiT, cls2_psiT]
  congr 1
  rw [Tcast_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Tcast_smul]

theorem H_comm_gen (X Y : SSet)
    (W : (p q : ℕ) → ↥((Work.Kunneth.tMod p q).X (p + q + 1)))
    (hs : Work.Kunneth.HsumData X Y W)
    (hW : ∀ p q, (Work.Kunneth.tMod p q).d (p + q + 1) (p + q) (W p q)
      = Work.Kunneth.dfc W p q)
    (p q : ℕ) (σ : X.obj (Opposite.op (SimplexCategory.mk p)))
    (τ : Y.obj (Opposite.op (SimplexCategory.mk q))) :
    (Work.Kunneth.Ezaw X Y).f (p + q) (Work.Kunneth.genXY X Y σ τ)
      = ModuleCat.Hom.hom (CategoryTheory.CategoryStruct.comp
          ((Work.Kunneth.tChain X Y).d (p + q) (p + q - 1))
          (Work.Kunneth.homMap X Y W hs (p + q - 1) (p + q)))
          (Work.Kunneth.genXY X Y σ τ)
        + ModuleCat.Hom.hom (CategoryTheory.CategoryStruct.comp
            (Work.Kunneth.homMap X Y W hs (p + q) (p + q + 1))
            ((Work.Kunneth.tChain X Y).d (p + q + 1) (p + q)))
            (Work.Kunneth.genXY X Y σ τ)
        + Work.Kunneth.genXY X Y σ τ := by
  rcases p with _ | P <;> rcases q with _ | Q
  · -- case (0,0)
    have hU : genXY X Y σ τ
        = (ModuleCat.Hom.hom ((cls2 X Y 0 0 σ τ).f (0+0))) (U 0 0) :=
      (cls2_U X Y 0 0 σ τ).symm
    have hLHS : (Ezaw X Y).f (0+0) (genXY X Y σ τ)
        = (ModuleCat.Hom.hom ((cls2 X Y 0 0 σ τ).f (0+0))) (Em 0 0)
          + genXY X Y σ τ := by
      rw [hU, Ezaw_cls2, Ezaw_U, map_add, cls2_U]
    have hA : ModuleCat.Hom.hom (CategoryTheory.CategoryStruct.comp
          ((Work.Kunneth.tChain X Y).d (0+0) (0+0 - 1))
          (Work.Kunneth.homMap X Y W hs (0+0 - 1) (0+0)))
          (Work.Kunneth.genXY X Y σ τ) = 0 := by
      have h0 : homMap X Y W hs (0+0-1) (0+0) = 0 :=
        homMap_neg X Y W hs (i := 0+0-1) (j := 0+0) (by omega)
      rw [h0]
      simp
    have hB : ModuleCat.Hom.hom (CategoryTheory.CategoryStruct.comp
            (Work.Kunneth.homMap X Y W hs (0+0) (0+0+1))
            ((Work.Kunneth.tChain X Y).d (0+0+1) (0+0)))
            (Work.Kunneth.genXY X Y σ τ)
        = (ModuleCat.Hom.hom ((cls2 X Y 0 0 σ τ).f (0+0))) (Em 0 0) := by
      rw [homMap_succ, ModuleCat.hom_comp, LinearMap.comp_apply]
      rw [genXY, H_gen]
      rw [Hom_comm_apply, hW 0 0]
      rfl
    rw [hLHS, hA, hB]
    abel
  · -- case (0, Q+1)
    have hU : genXY X Y σ τ
        = (ModuleCat.Hom.hom ((cls2 X Y 0 (Q+1) σ τ).f (0+(Q+1)))) (U 0 (Q+1)) :=
      (cls2_U X Y 0 (Q+1) σ τ).symm
    have hLHS : (Ezaw X Y).f (0+(Q+1)) (genXY X Y σ τ)
        = (ModuleCat.Hom.hom ((cls2 X Y 0 (Q+1) σ τ).f (0+(Q+1)))) (Em 0 (Q+1))
          + genXY X Y σ τ := by
      rw [hU, Ezaw_cls2, Ezaw_U, map_add, cls2_U]
    have hB : ModuleCat.Hom.hom (CategoryTheory.CategoryStruct.comp
            (homMap X Y W hs (0+(Q+1)) (0+(Q+1)+1))
            ((tChain X Y).d (0+(Q+1)+1) (0+(Q+1))))
            (genXY X Y σ τ)
        = (ModuleCat.Hom.hom ((cls2 X Y 0 (Q+1) σ τ).f (0+(Q+1)))) (dfc W 0 (Q+1)) := by
      rw [homMap_succ, ModuleCat.hom_comp, LinearMap.comp_apply]
      rw [show genXY X Y σ τ = tpLof (sChain X) (sChain Y) (0+(Q+1)) ⟨(0,Q+1), rfl⟩
            (genCh X σ ⊗ₜ[ℤ] genCh Y τ) from rfl]
      rw [H_gen, Hom_comm_apply, hW]
    have hA : ModuleCat.Hom.hom (CategoryTheory.CategoryStruct.comp
          ((tChain X Y).d (0+(Q+1)) (0+(Q+1) - 1))
          (homMap X Y W hs (0+(Q+1) - 1) (0+(Q+1))))
          (genXY X Y σ τ)
        = ∑ j : Fin (Q+2), (-1:ℤ)^(j:ℕ) •
            (ModuleCat.Hom.hom ((cls2 X Y 0 (Q+1) σ τ).f (0+(Q+1)))) (psiT W 0 Q j) := by
      have hm : homMap X Y W hs (0+(Q+1)-1) (0+(Q+1)) = H X Y W hs (0+(Q+1)-1) :=
        homMap_succ X Y W hs (0+(Q+1)-1)
      rw [hm, ModuleCat.hom_comp, LinearMap.comp_apply, hU, Hom_comm_apply]
      exact H_boundary_psi X Y W hs Q σ τ
    have hdfc : dfc W 0 (Q+1) = Em 0 (Q+1)
        - ∑ j : Fin (Q+2), (-1:ℤ)^(j:ℕ) • psiT W 0 Q j := rfl
    have hpsi : (ModuleCat.Hom.hom ((cls2 X Y 0 (Q+1) σ τ).f (0+(Q+1))))
          (∑ j : Fin (Q+2), (-1:ℤ)^(j:ℕ) • psiT W 0 Q j)
        = ∑ j : Fin (Q+2), (-1:ℤ)^(j:ℕ) •
            (ModuleCat.Hom.hom ((cls2 X Y 0 (Q+1) σ τ).f (0+(Q+1)))) (psiT W 0 Q j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun j _ => map_zsmul _ _ _)
    rw [hLHS, hA, hB, hdfc, map_sub, hpsi]
    abel
  · -- case (P+1, 0)
    have hU : genXY X Y σ τ
        = (ModuleCat.Hom.hom ((cls2 X Y (P+1) 0 σ τ).f (P+1))) (U (P+1) 0) :=
      (cls2_U X Y (P+1) 0 σ τ).symm
    have hLHS : (Ezaw X Y).f (P+1+0) (genXY X Y σ τ)
        = (ModuleCat.Hom.hom ((cls2 X Y (P+1) 0 σ τ).f (P+1))) (Em (P+1) 0)
          + genXY X Y σ τ := by
      rw [hU, Ezaw_cls2, Ezaw_U, map_add, cls2_U]
    have hB : ModuleCat.Hom.hom (CategoryTheory.CategoryStruct.comp
            (homMap X Y W hs (P+1+0) (P+1+0+1))
            ((tChain X Y).d (P+1+0+1) (P+1+0)))
            (genXY X Y σ τ)
        = (ModuleCat.Hom.hom ((cls2 X Y (P+1) 0 σ τ).f (P+1))) (dfc W (P+1) 0) := by
      rw [homMap_succ, ModuleCat.hom_comp, LinearMap.comp_apply]
      rw [show genXY X Y σ τ = tpLof (sChain X) (sChain Y) (P+1) ⟨(P+1,0), rfl⟩
            (genCh X σ ⊗ₜ[ℤ] genCh Y τ) from rfl]
      rw [H_gen, Hom_comm_apply, hW]
    have hA : ModuleCat.Hom.hom (CategoryTheory.CategoryStruct.comp
          ((tChain X Y).d (P+1+0) (P+1+0 - 1))
          (homMap X Y W hs (P+1+0 - 1) (P+1+0)))
          (genXY X Y σ τ)
        = ∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) •
            (ModuleCat.Hom.hom ((cls2 X Y (P+1) 0 σ τ).f (P+1))) (phiT W P 0 i) := by
      have hm : homMap X Y W hs (P+1+0-1) (P+1+0) = H X Y W hs (P+1+0-1) :=
        homMap_succ X Y W hs (P+1+0-1)
      rw [hm, ModuleCat.hom_comp, LinearMap.comp_apply, hU, Hom_comm_apply]
      exact H_boundary_phi X Y W hs P σ τ
    have hdfc : dfc W (P+1) 0 = Em (P+1) 0
        - ∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) • phiT W P 0 i := rfl
    have hphi : (ModuleCat.Hom.hom ((cls2 X Y (P+1) 0 σ τ).f (P+1)))
          (∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) • phiT W P 0 i)
        = ∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) •
            (ModuleCat.Hom.hom ((cls2 X Y (P+1) 0 σ τ).f (P+1))) (phiT W P 0 i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun i _ => map_zsmul _ _ _)
    rw [hLHS, hA, hB, hdfc, map_sub, hphi]
    abel
  · -- case (P+1, Q+1)
    have hU : genXY X Y σ τ
        = (ModuleCat.Hom.hom ((cls2 X Y (P+1) (Q+1) σ τ).f ((P+1)+(Q+1)))) (U (P+1) (Q+1)) :=
      (cls2_U X Y (P+1) (Q+1) σ τ).symm
    have hLHS : (Ezaw X Y).f ((P+1)+(Q+1)) (genXY X Y σ τ)
        = (ModuleCat.Hom.hom ((cls2 X Y (P+1) (Q+1) σ τ).f ((P+1)+(Q+1)))) (Em (P+1) (Q+1))
          + genXY X Y σ τ := by
      rw [hU, Ezaw_cls2, Ezaw_U, map_add, cls2_U]
    have hB : ModuleCat.Hom.hom (CategoryTheory.CategoryStruct.comp
            (homMap X Y W hs ((P+1)+(Q+1)) ((P+1)+(Q+1)+1))
            ((tChain X Y).d ((P+1)+(Q+1)+1) ((P+1)+(Q+1))))
            (genXY X Y σ τ)
        = (ModuleCat.Hom.hom ((cls2 X Y (P+1) (Q+1) σ τ).f ((P+1)+(Q+1))))
            (dfc W (P+1) (Q+1)) := by
      rw [homMap_succ, ModuleCat.hom_comp, LinearMap.comp_apply]
      rw [show genXY X Y σ τ = tpLof (sChain X) (sChain Y) ((P+1)+(Q+1)) ⟨(P+1,Q+1), rfl⟩
            (genCh X σ ⊗ₜ[ℤ] genCh Y τ) from rfl]
      rw [H_gen, Hom_comm_apply, hW]
    have hA : ModuleCat.Hom.hom (CategoryTheory.CategoryStruct.comp
          ((tChain X Y).d ((P+1)+(Q+1)) ((P+1)+(Q+1) - 1))
          (homMap X Y W hs ((P+1)+(Q+1) - 1) ((P+1)+(Q+1))))
          (genXY X Y σ τ)
        = (∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) •
              (ModuleCat.Hom.hom ((cls2 X Y (P+1) (Q+1) σ τ).f ((P+1)+(Q+1)))) (phiT W P (Q+1) i))
          + (-1:ℤ)^(P+1) • (∑ j : Fin (Q+2), (-1:ℤ)^(j:ℕ) •
              (ModuleCat.Hom.hom ((cls2 X Y (P+1) (Q+1) σ τ).f ((P+1)+(Q+1)))) (psiT W (P+1) Q j)) := by
      have hm : homMap X Y W hs ((P+1)+(Q+1)-1) ((P+1)+(Q+1)) = H X Y W hs ((P+1)+(Q+1)-1) :=
        homMap_succ X Y W hs ((P+1)+(Q+1)-1)
      rw [hm, ModuleCat.hom_comp, LinearMap.comp_apply, hU, Hom_comm_apply]
      exact H_boundary_both X Y W hs P Q σ τ
    have hdfc : dfc W (P+1) (Q+1) = Em (P+1) (Q+1)
        - ∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) • phiT W P (Q+1) i
        - (-1:ℤ)^(P+1) • ∑ j : Fin (Q+2), (-1:ℤ)^(j:ℕ) • psiT W (P+1) Q j := rfl
    have hphi : (ModuleCat.Hom.hom ((cls2 X Y (P+1) (Q+1) σ τ).f ((P+1)+(Q+1))))
          (∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) • phiT W P (Q+1) i)
        = ∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) •
            (ModuleCat.Hom.hom ((cls2 X Y (P+1) (Q+1) σ τ).f ((P+1)+(Q+1)))) (phiT W P (Q+1) i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun i _ => map_zsmul _ _ _)
    have hpsi : (ModuleCat.Hom.hom ((cls2 X Y (P+1) (Q+1) σ τ).f ((P+1)+(Q+1))))
          (∑ j : Fin (Q+2), (-1:ℤ)^(j:ℕ) • psiT W (P+1) Q j)
        = ∑ j : Fin (Q+2), (-1:ℤ)^(j:ℕ) •
            (ModuleCat.Hom.hom ((cls2 X Y (P+1) (Q+1) σ τ).f ((P+1)+(Q+1)))) (psiT W (P+1) Q j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun j _ => map_zsmul _ _ _)
    rw [hLHS, hA, hB, hdfc, map_sub, map_sub, map_zsmul, hphi, hpsi]
    abel



end

end Work.Kunneth
