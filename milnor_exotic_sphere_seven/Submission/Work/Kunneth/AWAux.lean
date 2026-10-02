import Mathlib
import Submission.Work.Kunneth.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The generator of the `m`-chains attached to a simplex, as an element. -/
abbrev genCh (X : SSet) {m : ℕ} (σ : X _⦋m⦌) : ↥((sChain X).X m) :=
  (X.ιChainComplex (R := zz) σ).hom 1

/-- `genTensor` evaluated at `1`. -/
theorem genTensor_hom_one (X Y : SSet) {p q : ℕ} (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    (genTensor X Y σ τ).hom 1 = genCh X σ ⊗ₜ[ℤ] genCh Y τ := by
  rw [genTensor, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [ModuleCat.hom_inv_leftUnitor]
  change (ModuleCat.Hom.hom (MonoidalCategory.tensorHom (X.ιChainComplex (R := zz) σ)
      (Y.ιChainComplex (R := zz) τ)))
      ((TensorProduct.lid ℤ ℤ).symm (1 : ℤ)) = _
  rw [TensorProduct.lid_symm_apply]
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul]

/-- The value of the Alexander–Whitney chain on a generator, as an explicit sum. -/
theorem awGen_hom_one (X Y : SSet) (n : ℕ) (z : (X ⊗ Y) _⦋n⦌) :
    (awGen X Y n z).hom 1
      = ∑ p : Fin (n+1),
          tpLof (sChain X) (sChain Y) n ⟨(p.val, n - p.val), by omega⟩
            (genCh X (Work.Cohomology.frontFace X p.val n (by omega) z.1)
              ⊗ₜ[ℤ] genCh Y (backFaceLE Y (n - p.val) n (by omega) z.2)) := by
  rw [awGen]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, genTensor_hom_one]
  rfl

/-- The differential of the generator of a simplex, as an alternating sum of its faces. -/
theorem d_genCh (X : SSet) (m : ℕ) (σ : X _⦋m+1⦌) :
    ((sChain X).d (m+1) m).hom (genCh X σ)
      = ∑ i : Fin (m+2), (-1 : ℤ) ^ (i:ℕ) • genCh X (X.δ i σ) := by
  have h := congrArg
    (fun (g : ModuleCat.of ℤ ℤ ⟶ (sChain X).X m) => g.hom (1 : ℤ))
    (SSet.ιChainComplex_d X zz σ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_smul,
    LinearMap.smul_apply, genCh]

/-! ## Face identities -/

section Faces

/-- `tpLof` is insensitive to a propositionally equal second index (up to a cast). -/
lemma tpLof_congr {C D : ChainComplex (ModuleCat ℤ) ℕ} {p q q' n : ℕ} (h : q = q')
    (hpq : p + q = n) (hpq' : p + q' = n) (x : tpSummand C D p q) :
    tpLof C D n ⟨(p, q), hpq⟩ x
      = tpLof C D n ⟨(p, q'), hpq'⟩ (cast (congrArg (tpSummand C D p) h) x) := by
  subst h
  rfl

/-- The cast of an elementary tensor along a change of the second degree. -/
lemma cast_tmul {C D : ChainComplex (ModuleCat ℤ) ℕ} {p q q' : ℕ} (h : q = q')
    (x : ↥(C.X p)) (y : ↥(D.X q)) :
    cast (congrArg (tpSummand C D p) h) (x ⊗ₜ[ℤ] y)
      = x ⊗ₜ[ℤ] (cast (congrArg (fun k => ↥(D.X k)) h) y) := by
  subst h
  rfl

/-- The cast of a generator of the singular chains along a change of degree. -/
lemma genCh_cast {Y : SSet} {q q' : ℕ} (h : q = q') (σ : Y _⦋q⦌) :
    cast (congrArg (fun k => ↥((sChain Y).X k)) h) (genCh Y σ)
      = genCh Y (cast (congrArg (fun k => Y _⦋k⦌) h) σ) := by
  subst h
  rfl

/-- The structure map `tpLof` respects scalar multiplication. -/
lemma tpLof_zsmul (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (pq : tpIdx n) (c : ℤ)
    (x : tpSummand C D pq.1.1 pq.1.2) :
    tpLof C D n pq (c • x) = c • tpLof C D n pq x :=
  map_zsmul _ c x

/-- The value of `backInclLE` on a vertex. -/
@[simp] lemma hom_backInclLE_val (q n : ℕ) (h : q ≤ n) (j : Fin (q+1)) :
    ((ConcreteCategory.hom (backInclLE q n h)) j).val = n - q + j.val := rfl

/-! ### Identities in `SimplexCategory` -/

lemma frontIncl_delta_le (p q n : ℕ) (hpq : p + q = n) (k : Fin (n+2)) (hk : (k:ℕ) ≤ p) :
    Work.Cohomology.frontIncl p n (by omega) ≫ SimplexCategory.δ k
      = SimplexCategory.δ (⟨k.val, by omega⟩ : Fin (p+2))
          ≫ Work.Cohomology.frontIncl (p+1) (n+1) (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, Fin.succAbove]
  split_ifs <;>
    (simp only [Fin.val_castSucc, Fin.val_succ, Work.Cohomology.hom_frontIncl_val,
      Fin.lt_def] at *; try omega)

lemma frontIncl_delta_ge (p q n : ℕ) (hpq : p + q = n) (k : Fin (n+2)) (hk : p+1 ≤ (k:ℕ)) :
    Work.Cohomology.frontIncl p n (by omega) ≫ SimplexCategory.δ k
      = Work.Cohomology.frontIncl p (n+1) (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, Fin.succAbove]
  split_ifs <;>
    (simp only [Fin.val_castSucc, Fin.val_succ, Work.Cohomology.hom_frontIncl_val,
      Fin.lt_def] at *; try omega)

lemma delta_frontIncl_last (p q n : ℕ) (hpq : p + q = n) :
    SimplexCategory.δ (n := p) (⟨p+1, by omega⟩ : Fin (p+2))
        ≫ Work.Cohomology.frontIncl (p+1) (n+1) (by omega)
      = Work.Cohomology.frontIncl p (n+1) (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, Fin.succAbove]
  split_ifs <;>
    (simp only [Fin.val_castSucc, Fin.val_succ, Work.Cohomology.hom_frontIncl_val,
      Fin.lt_def] at *; try omega)

lemma backInclLE_delta_le (p q n : ℕ) (hpq : p + q = n) (k : Fin (n+2)) (hk : (k:ℕ) ≤ p) :
    backInclLE q n (by omega) ≫ SimplexCategory.δ k
      = backInclLE q (n+1) (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, Fin.succAbove]
  split_ifs <;>
    (simp only [Fin.val_castSucc, Fin.val_succ, hom_backInclLE_val, Fin.lt_def] at *;
      try omega)

lemma backInclLE_delta_ge (p q n : ℕ) (hpq : p + q = n) (k : Fin (n+2)) (hk : p+1 ≤ (k:ℕ)) :
    backInclLE q n (by omega) ≫ SimplexCategory.δ k
      = SimplexCategory.δ (⟨k.val - p, by omega⟩ : Fin (q+2))
          ≫ backInclLE (q+1) (n+1) (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, Fin.succAbove]
  split_ifs <;>
    (simp only [Fin.val_castSucc, Fin.val_succ, hom_backInclLE_val, Fin.lt_def] at *;
      try omega)

lemma delta_zero_backInclLE (p q n : ℕ) (hpq : p + q = n) :
    SimplexCategory.δ (n := q) (0 : Fin (q+2)) ≫ backInclLE (q+1) (n+1) (by omega)
      = backInclLE q (n+1) (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, Fin.succAbove]
  split_ifs <;>
    (simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_zero, hom_backInclLE_val,
      Fin.lt_def] at *; try omega)

/-! ### Identities for simplex faces -/

variable {X : SSet}

lemma frontFace_delta_le (p q n : ℕ) (hpq : p + q = n) (k : Fin (n+2)) (hk : (k:ℕ) ≤ p)
    (σ : X _⦋n+1⦌) :
    Work.Cohomology.frontFace X p n (by omega) (X.δ k σ)
      = X.δ (⟨k.val, by omega⟩ : Fin (p+2))
          (Work.Cohomology.frontFace X (p+1) (n+1) (by omega) σ) := by
  simp only [Work.Cohomology.frontFace, SimplicialObject.δ_def]
  rw [Work.Cohomology.map_op_comp, frontIncl_delta_le p q n hpq k hk]
  rw [← Work.Cohomology.map_op_comp]

lemma frontFace_delta_ge (p q n : ℕ) (hpq : p + q = n) (k : Fin (n+2)) (hk : p+1 ≤ (k:ℕ))
    (σ : X _⦋n+1⦌) :
    Work.Cohomology.frontFace X p n (by omega) (X.δ k σ)
      = Work.Cohomology.frontFace X p (n+1) (by omega) σ := by
  simp only [Work.Cohomology.frontFace, SimplicialObject.δ_def]
  rw [Work.Cohomology.map_op_comp, frontIncl_delta_ge p q n hpq k hk]

lemma delta_frontFace (p q n : ℕ) (hpq : p + q = n) (σ : X _⦋n+1⦌) :
    X.δ (⟨p+1, by omega⟩ : Fin (p+2))
        (Work.Cohomology.frontFace X (p+1) (n+1) (by omega) σ)
      = Work.Cohomology.frontFace X p (n+1) (by omega) σ := by
  simp only [Work.Cohomology.frontFace, SimplicialObject.δ_def]
  rw [Work.Cohomology.map_op_comp, delta_frontIncl_last p q n hpq]

lemma backFaceLE_delta_le (p q n : ℕ) (hpq : p + q = n) (k : Fin (n+2)) (hk : (k:ℕ) ≤ p)
    (τ : X _⦋n+1⦌) :
    backFaceLE X q n (by omega) (X.δ k τ)
      = backFaceLE X q (n+1) (by omega) τ := by
  simp only [backFaceLE, SimplicialObject.δ_def]
  rw [Work.Cohomology.map_op_comp, backInclLE_delta_le p q n hpq k hk]

lemma backFaceLE_delta_ge (p q n : ℕ) (hpq : p + q = n) (k : Fin (n+2)) (hk : p+1 ≤ (k:ℕ))
    (τ : X _⦋n+1⦌) :
    backFaceLE X q n (by omega) (X.δ k τ)
      = X.δ (⟨k.val - p, by omega⟩ : Fin (q+2))
          (backFaceLE X (q+1) (n+1) (by omega) τ) := by
  simp only [backFaceLE, SimplicialObject.δ_def]
  rw [Work.Cohomology.map_op_comp, backInclLE_delta_ge p q n hpq k hk]
  rw [← Work.Cohomology.map_op_comp]

lemma delta_zero_backFaceLE (p q n : ℕ) (hpq : p + q = n) (τ : X _⦋n+1⦌) :
    X.δ (0 : Fin (q+2)) (backFaceLE X (q+1) (n+1) (by omega) τ)
      = backFaceLE X q (n+1) (by omega) τ := by
  simp only [backFaceLE, SimplicialObject.δ_def]
  rw [Work.Cohomology.map_op_comp, delta_zero_backInclLE p q n hpq]

/-! ### Transport of faces along equal degrees -/

lemma backInclLE_transport {a b N : ℕ} (h : a = b) (ha : a ≤ N) (hb : b ≤ N) :
    eqToHom (congrArg SimplexCategory.mk h).symm ≫ backInclLE a N ha = backInclLE b N hb := by
  subst h
  rfl

lemma frontIncl_transport {a b N : ℕ} (h : a = b) (ha : a ≤ N) (hb : b ≤ N) :
    eqToHom (congrArg SimplexCategory.mk h).symm ≫ Work.Cohomology.frontIncl a N ha
      = Work.Cohomology.frontIncl b N hb := by
  subst h
  rfl

lemma backFaceLE_transport {a b N : ℕ} (h : a = b) (ha : a ≤ N) (hb : b ≤ N) (τ : X _⦋N⦌) :
    X.map (eqToHom (congrArg SimplexCategory.mk h).symm).op (backFaceLE X a N ha τ)
      = backFaceLE X b N hb τ := by
  simp only [backFaceLE]
  rw [Work.Cohomology.map_op_comp, backInclLE_transport h ha hb]

lemma cast_backFaceLE {a b N : ℕ} (h : a = b) (ha : a ≤ N) (hb : b ≤ N) (τ : X _⦋N⦌) :
    cast (congrArg (fun k => X _⦋k⦌) h) (backFaceLE X a N ha τ) = backFaceLE X b N hb τ :=
  (Work.Cohomology.transport_map h (backFaceLE X a N ha τ)).trans
    (backFaceLE_transport h ha hb τ)

lemma cast_backFaceLE' {X : SSet} {a b N : ℕ} (h : a = b) (ha : a ≤ N) (hb : b ≤ N)
    (τ : X _⦋N⦌) :
    (h ▸ backFaceLE X a N ha τ) = backFaceLE X b N hb τ := by
  subst h
  rfl

/-- The scalar multiplication of an elementary tensor on the left. -/
lemma smul_tmul_eq {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N]
    (c : ℤ) (m : M) (n : N) : (c • m) ⊗ₜ[ℤ] n = c • (m ⊗ₜ[ℤ] n) := rfl

/-- The scalar multiplication of an elementary tensor on the right. -/
lemma tmul_smul_eq {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N]
    (c : ℤ) (m : M) (n : N) : m ⊗ₜ[ℤ] (c • n) = c • (m ⊗ₜ[ℤ] n) :=
  map_zsmul (TensorProduct.mk ℤ M N m) c n

lemma frontFace_transport {a b N : ℕ} (h : a = b) (ha : a ≤ N) (hb : b ≤ N) (σ : X _⦋N⦌) :
    X.map (eqToHom (congrArg SimplexCategory.mk h).symm).op
        (Work.Cohomology.frontFace X a N ha σ)
      = Work.Cohomology.frontFace X b N hb σ := by
  simp only [Work.Cohomology.frontFace]
  rw [Work.Cohomology.map_op_comp, frontIncl_transport h ha hb]

/-! ## The two contributions to the comparison -/

/-- The `(a, n-a)`-component of the tensor differential of the Alexander–Whitney chain of an
`(n+1)`-simplex `(σ, τ)` of `X ⊗ Y`. -/
def awU (X Y : SSet) (n : ℕ) (a : Fin (n+1)) (σ : X _⦋n+1⦌) (τ : Y _⦋n+1⦌) :
    tpSummand (sChain X) (sChain Y) a.val (n+1-(a.val+1)) :=
  ((sChain X).d (a.val+1) a.val).hom
      (genCh X (Work.Cohomology.frontFace X (a.val+1) (n+1) (by omega) σ))
    ⊗ₜ[ℤ] genCh Y (backFaceLE Y (n+1-(a.val+1)) (n+1) (by omega) τ)
  + (-1 : ℤ) ^ (a.val) •
      (genCh X (Work.Cohomology.frontFace X a.val (n+1) (by omega) σ)
        ⊗ₜ[ℤ] ((sChain Y).d (n+1-a.val) (n+1-a.val-1)).hom
          (genCh Y (backFaceLE Y (n+1-a.val) (n+1) (by omega) τ)))

/-- The `(a, n-a)`-component of the Alexander–Whitney chain of the boundary of an `(n+1)`-simplex
`(σ, τ)` of `X ⊗ Y`. -/
def awV (X Y : SSet) (n : ℕ) (a : Fin (n+1)) (σ : X _⦋n+1⦌) (τ : Y _⦋n+1⦌) :
    tpSummand (sChain X) (sChain Y) a.val (n+1-(a.val+1)) :=
  ∑ k : Fin (n+2), (-1 : ℤ) ^ (k.val) •
    (genCh X (Work.Cohomology.frontFace X a.val n (by omega) (X.δ k σ))
      ⊗ₜ[ℤ] genCh Y (backFaceLE Y (n+1-a.val-1) n (by omega) (Y.δ k τ)))

/-- The differential of the generator of a simplex, in the form `d m (m-1)`. -/
theorem d_genCh_pred (X : SSet) (m : ℕ) (hm : 1 ≤ m) (σ : X _⦋m⦌) :
    ((sChain X).d m (m-1)).hom (genCh X σ)
      = ∑ i : Fin (m+1), (-1 : ℤ)^(i:ℕ) •
          genCh X (X.δ (i.cast (by omega : m+1 = (m-1)+2))
            ((by omega : m = m-1+1) ▸ σ)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m-1, by omega⟩
  simpa using d_genCh X k σ

/-- `d m (m-1)` on a back face, expanded as an alternating sum of the faces of the back face. -/
lemma d_genCh_pred_face (Y : SSet) (m : ℕ) (hm : 1 ≤ m) (N : ℕ) (hN : m ≤ N)
    (τ : Y _⦋N⦌) :
    ((sChain Y).d m (m-1)).hom (genCh Y (backFaceLE Y m N hN τ))
      = ∑ i : Fin (m+1), (-1 : ℤ)^(i:ℕ) •
          genCh Y (Y.δ (⟨i.val, by omega⟩ : Fin (m-1+2))
            (backFaceLE Y (m-1+1) N (by omega) τ)) := by
  rw [d_genCh_pred Y m hm (backFaceLE Y m N hN τ)]
  apply Finset.sum_congr rfl
  intro i _
  have hidx : Fin.cast (by omega : m+1 = (m-1)+2) i = (⟨i.val, by omega⟩ : Fin (m-1+2)) :=
    Fin.ext (by simp)
  have hδ : (ConcreteCategory.hom (SimplicialObject.δ Y (Fin.cast (by omega : m+1 = (m-1)+2) i)))
        ((by omega : m = m-1+1) ▸ backFaceLE Y m N hN τ)
      = (ConcreteCategory.hom (SimplicialObject.δ Y (⟨i.val, by omega⟩ : Fin (m-1+2))))
        (backFaceLE Y (m-1+1) N (by omega) τ) := by
    rw [hidx]
    congr 1
    exact cast_backFaceLE' (by omega : m = m-1+1) hN (by omega) τ
  rw [hδ]


/-- The face of a product simplex is the product of the faces. -/
lemma prod_delta (X Y : SSet) (n : ℕ) (k : Fin (n+2)) (z : (X ⊗ Y) _⦋n+1⦌) :
    (X ⊗ Y).δ k z = (X.δ k z.1, Y.δ k z.2) := rfl

/-- The `(n+1)`-simplex `(z.1, z.2)` of `X ⊗ Y` is `z`. -/
lemma prod_eta (X Y : SSet) (n : ℕ) (z : (X ⊗ Y) _⦋n+1⦌) : (z.1, z.2) = z := rfl

end Faces

end

end Work.Kunneth
