import Mathlib
import Submission.Work.Kunneth.EZ
import Submission.Work.KunnethEZ.ez23_eq_ezGen

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- A scalar on the left of a tensor product. -/
lemma smul_tmul_eq {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N]
    (c : ℤ) (m : M) (n : N) : (c • m) ⊗ₜ[ℤ] n = c • (m ⊗ₜ[ℤ] n) := rfl

/-- A scalar on the right of a tensor product. -/
lemma tmul_smul_eq {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N]
    (c : ℤ) (m : M) (n : N) : m ⊗ₜ[ℤ] (c • n) = c • (m ⊗ₜ[ℤ] n) :=
  map_zsmul (TensorProduct.mk ℤ M N m) c n

/-- `ezSummandLin` on a pure tensor of two chains is the Eilenberg–Zilber shuffle chain. -/
lemma ezSummandLin_tmul_chain (X Y : SSet) (p q : ℕ)
    (a : ↥((sChain X).X p)) (b : ↥((sChain Y).X q)) :
    ezSummandLin X Y p q (a ⊗ₜ[ℤ] b) = Work.KunnethEZ.ezChain p q X Y a b := by
  conv_lhs => rw [Work.KunnethEZ.chain_eq_sum_gen X p a]
  rw [TensorProduct.sum_tmul, map_sum]
  conv_rhs => rw [Work.KunnethEZ.chain_eq_sum_gen X p a]
  rw [Work.KunnethEZ.ezChain_sum_left]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [smul_tmul_eq ((Work.Cohomology.Crux33.coords X p a) σ) (Work.KunnethEZ.genC X σ) b]
  rw [map_zsmul]
  congr 1
  conv_lhs => rw [Work.KunnethEZ.chain_eq_sum_gen Y q b]
  rw [TensorProduct.tmul_sum, map_sum]
  conv_rhs => rw [Work.KunnethEZ.chain_eq_sum_gen Y q b]
  rw [Work.KunnethEZ.ezChain_sum_right]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [tmul_smul_eq ((Work.Cohomology.Crux33.coords Y q b) τ) (Work.KunnethEZ.genC X σ)
    (Work.KunnethEZ.genC Y τ)]
  rw [map_zsmul]
  congr 1
  exact ezSummandLin_tmul X Y p q σ τ


/-- The value of `ezHom` on a summand generator. -/
lemma ezHom_apply_tpLof (X Y : SSet) (p q n : ℕ) (h : p + q = n)
    (x : tpSummand (sChain X) (sChain Y) p q) :
    (ezHom X Y n).hom (tpLof (sChain X) (sChain Y) n ⟨(p, q), h⟩ x)
      = (eqToHom (congrArg (fun k => (sChain (sProd X Y)).X k) h)).hom
          (ezSummandLin X Y p q x) := by
  rw [show (ezHom X Y n).hom = DirectSum.toModule ℤ (tpIdx n) ↥((sChain (sProd X Y)).X n)
        (fun pq => ((eqToIso (congrArg (fun k => (sChain (sProd X Y)).X k) pq.2)).hom.hom).comp
          (ezSummandLin X Y pq.1.1 pq.1.2)) from rfl]
  change (DirectSum.toModule ℤ (tpIdx n) ↥((sChain (sProd X Y)).X n)
        (fun pq => ((eqToIso (congrArg (fun k => (sChain (sProd X Y)).X k) pq.2)).hom.hom).comp
          (ezSummandLin X Y pq.1.1 pq.1.2)))
      (DirectSum.lof ℤ (tpIdx n) (fun rs => tpSummand (sChain X) (sChain Y) rs.1.1 rs.1.2)
        ⟨(p, q), h⟩ x)
    = ((eqToIso (congrArg (fun k => (sChain (sProd X Y)).X k) h)).hom.hom)
        (ezSummandLin X Y p q x)
  rw [DirectSum.toModule_lof]
  rfl

/-- Left-composition with `DirectSum.toModule`. -/
lemma toModule_comp {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module ℤ (M i)] {N N' : Type*} [AddCommMonoid N] [AddCommMonoid N'] [Module ℤ N]
    [Module ℤ N'] (Φ : N →ₗ[ℤ] N') (g : ∀ i, M i →ₗ[ℤ] N) :
    Φ.comp (DirectSum.toModule ℤ ι N g) = DirectSum.toModule ℤ ι N' (fun i => Φ.comp (g i)) := by
  apply DirectSum.linearMap_ext ℤ
  intro i
  ext x
  simp only [LinearMap.comp_apply, DirectSum.toModule_lof]

/-- The `eqToHom` transport of the boundary of the shuffle chain changes the bidegree. -/
lemma eqToHom_d_comp (X Y : SSet) {a b m : ℕ} (h : a = b) (hb : b = m + 1) :
    (((sChain (sProd X Y)).d b m).hom).comp
        ((eqToHom (congrArg (fun k => (sChain (sProd X Y)).X k) h)).hom)
      = ((sChain (sProd X Y)).d a m).hom := by
  have ha : a = m + 1 := h.trans hb
  have := congrArg (fun (g : (sChain (sProd X Y)).X a ⟶ (sChain (sProd X Y)).X m) => g.hom)
    (HomologicalComplex.eqToHom_comp_d (C := sChain (sProd X Y))
      (c := ComplexShape.down ℕ) (show (ComplexShape.down ℕ).Rel a m from ha.symm)
      (show (ComplexShape.down ℕ).Rel b m from hb.symm))
  simpa only [ModuleCat.hom_comp] using this


/-- Transporting the target index of the boundary of a chain complex along an equality. -/
lemma d_apply_transport (X Y : SSet) {i j : ℕ} (hij : i = j + 1)
    (z : ↥((sChain (sProd X Y)).X i)) :
    (((sChain (sProd X Y)).d i j).hom) z
      = (eqToHom (congrArg (fun k => (sChain (sProd X Y)).X k) (by omega : i - 1 = j))).hom
          ((((sChain (sProd X Y)).d i (i - 1)).hom) z) := by
  have h := congrArg (fun (g : (sChain (sProd X Y)).X i ⟶ (sChain (sProd X Y)).X j) => g.hom)
    (HomologicalComplex.d_comp_eqToHom (C := sChain (sProd X Y)) (c := ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel i j from by rw [ComplexShape.down_Rel]; omega)
      (show (ComplexShape.down ℕ).Rel i (i - 1) from by rw [ComplexShape.down_Rel]; omega))
  rw [ModuleCat.hom_comp] at h
  exact congrArg (fun f => f z) h.symm

/-- `eqToHom` depends only on the (propositionally unique) proof. -/
lemma eqToHom_congr {C : Type*} [CategoryTheory.Category C] {a b : C} (h1 h2 : a = b) :
    CategoryTheory.eqToHom h1 = CategoryTheory.eqToHom h2 := by
  rw [Subsingleton.elim h1 h2]

/-- Composing `eqToHom` transports combines the proofs. -/
lemma eqToHom_comp_eq (X Y : SSet) {i j k : ℕ} (h1 : i = j) (h2 : j = k) :
    ((eqToHom (congrArg (fun t => (sChain (sProd X Y)).X t) h2)).hom).comp
        ((eqToHom (congrArg (fun t => (sChain (sProd X Y)).X t) h1)).hom)
      = ((eqToHom (congrArg (fun t => (sChain (sProd X Y)).X t) (h1.trans h2)))).hom := by
  rw [← ModuleCat.hom_comp, eqToHom_trans]

/-- The componentwise chain-map identity for `ezHom`, on a single bidegree summand. -/
lemma ezSummand_d (X Y : SSet) (n : ℕ) (pq : tpIdx (n+1)) :
    ((sChain (sProd X Y)).d (n+1) n).hom.comp
        (((eqToIso (congrArg (fun k => (sChain (sProd X Y)).X k) pq.2)).hom.hom).comp
          (ezSummandLin X Y pq.1.1 pq.1.2))
      = (DirectSum.toModule ℤ (tpIdx n) ↥((sChain (sProd X Y)).X n)
          (fun rs => ((eqToIso (congrArg (fun k => (sChain (sProd X Y)).X k) rs.2)).hom.hom).comp
            (ezSummandLin X Y rs.1.1 rs.1.2))).comp
        (tpDpq (sChain X) (sChain Y) n pq) := by
  obtain ⟨⟨p, q⟩, hpq⟩ := pq
  dsimp only
  apply TensorProduct.ext'
  intro a b
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  erw [ezSummandLin_tmul_chain]
  rw [show (eqToIso (congrArg (fun k => (sChain (sProd X Y)).X k) hpq)).hom.hom
      = (eqToHom (congrArg (fun k => (sChain (sProd X Y)).X k) hpq)).hom from rfl]
  conv_lhs => rw [← LinearMap.comp_apply, eqToHom_d_comp X Y hpq rfl]
  rw [LinearMap.comp_apply]
  erw [tpDpq_tmul (sChain X) (sChain Y) n ⟨(p,q),hpq⟩ a b]
  rw [map_add]
  dsimp only
  by_cases hp : 1 ≤ p
  · rw [dif_pos hp]
    rw [show (DirectSum.toModule ℤ (tpIdx n) ↥((sChain (sProd X Y)).X n)
          (fun rs => ((eqToIso (congrArg (fun k => (sChain (sProd X Y)).X k) rs.2)).hom.hom).comp
            (ezSummandLin X Y rs.1.1 rs.1.2)))
        ((tpLof (sChain X) (sChain Y) n ⟨(p - 1, q), by omega⟩)
          (((sChain X).d p (p - 1)).hom a ⊗ₜ[ℤ] b))
      = (ezHom X Y n).hom
        ((tpLof (sChain X) (sChain Y) n ⟨(p - 1, q), by omega⟩)
          (((sChain X).d p (p - 1)).hom a ⊗ₜ[ℤ] b)) from rfl]
    rw [ezHom_apply_tpLof, ezSummandLin_tmul_chain]
    by_cases hq : 1 ≤ q
    · rw [dif_pos hq]
      rw [map_zsmul]
      rw [show (DirectSum.toModule ℤ (tpIdx n) ↥((sChain (sProd X Y)).X n)
            (fun rs => ((eqToIso (congrArg (fun k => (sChain (sProd X Y)).X k) rs.2)).hom.hom).comp
              (ezSummandLin X Y rs.1.1 rs.1.2)))
          ((tpLof (sChain X) (sChain Y) n ⟨(p, q - 1), by omega⟩)
            (a ⊗ₜ[ℤ] (((sChain Y).d q (q - 1)).hom b)))
        = (ezHom X Y n).hom
          ((tpLof (sChain X) (sChain Y) n ⟨(p, q - 1), by omega⟩)
            (a ⊗ₜ[ℤ] (((sChain Y).d q (q - 1)).hom b))) from rfl]
      rw [ezHom_apply_tpLof, ezSummandLin_tmul_chain]
      obtain ⟨P, rfl⟩ : ∃ P, p = P + 1 := ⟨p - 1, by omega⟩
      obtain ⟨Q, rfl⟩ : ∃ Q, q = Q + 1 := ⟨q - 1, by omega⟩
      rw [d_apply_transport X Y (by omega : (P+1) + (Q+1) = n + 1)
        (Work.KunnethEZ.ezChain (P+1) (Q+1) X Y a b)]
      rw [Work.KunnethEZ.ezChain_d P Q X Y (by omega) (by omega) a b]
      simp only [map_add, map_zsmul]
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, eqToHom_trans]
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, eqToHom_trans]
      rfl
    · rw [dif_neg hq, map_zero, add_zero]
      obtain ⟨P, rfl⟩ : ∃ P, p = P + 1 := ⟨p - 1, by omega⟩
      obtain rfl : q = 0 := by omega
      rw [d_apply_transport X Y (by omega : (P+1) + 0 = n + 1)
        (Work.KunnethEZ.ezChain (P+1) 0 X Y a b)]
      rw [show ((sChain (sProd X Y)).d ((P+1)+0) ((P+1)+0-1)).hom
            (Work.KunnethEZ.ezChain (P+1) 0 X Y a b)
          = ((sChain (sProd X Y)).d (P+1) P).hom
            (Work.KunnethEZ.ezChain (P+1) 0 X Y a b) from rfl]
      rw [Work.KunnethEZ.ezChain_d_right0 P X Y a b]
      rfl
  · rw [dif_neg hp, map_zero, zero_add]
    obtain rfl : p = 0 := by omega
    obtain ⟨Q, rfl⟩ : ∃ Q, q = Q + 1 := ⟨q - 1, by omega⟩
    rw [d_apply_transport X Y (by omega : 0 + (Q+1) = n + 1)
      (Work.KunnethEZ.ezChain 0 (Q+1) X Y a b)]
    rw [show ((sChain (sProd X Y)).d (0+(Q+1)) (0+(Q+1)-1)).hom
          (Work.KunnethEZ.ezChain 0 (Q+1) X Y a b)
        = ((sChain (sProd X Y)).d (0+(Q+1)) (0+Q)).hom
          (Work.KunnethEZ.ezChain 0 (Q+1) X Y a b) from rfl]
    rw [dif_pos (by omega : 1 ≤ Q + 1)]
    rw [map_zsmul]
    erw [show (DirectSum.toModule ℤ (tpIdx n) ↥((sChain (sProd X Y)).X n)
          (fun rs => ((eqToIso (congrArg (fun k => (sChain (sProd X Y)).X k) rs.2)).hom.hom).comp
            (ezSummandLin X Y rs.1.1 rs.1.2)))
        ((tpLof (sChain X) (sChain Y) n ⟨(0, Q), by omega⟩)
          (a ⊗ₜ[ℤ] (((sChain Y).d (Q+1) Q).hom b)))
      = (ezHom X Y n).hom
        ((tpLof (sChain X) (sChain Y) n ⟨(0, Q), by omega⟩)
          (a ⊗ₜ[ℤ] (((sChain Y).d (Q+1) Q).hom b))) from rfl]
    rw [ezHom_apply_tpLof, ezSummandLin_tmul_chain]
    rw [Work.KunnethEZ.ezChain_d_left0 Q X Y a b]
    rw [pow_zero, one_zsmul]
    rfl

theorem ezHom_d (X Y : SSet) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (Work.Kunneth.ezHom X Y (n + 1))
        ((Work.Kunneth.sChain (Work.Kunneth.sProd X Y)).d (n + 1) n)
      = CategoryTheory.CategoryStruct.comp ((Work.Kunneth.tChain X Y).d (n + 1) n)
          (Work.Kunneth.ezHom X Y n) := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
  rw [show (ezHom X Y (n + 1)).hom = DirectSum.toModule ℤ (tpIdx (n + 1))
        ↥((sChain (sProd X Y)).X (n + 1))
        (fun pq => ((eqToIso (congrArg (fun k => (sChain (sProd X Y)).X k) pq.2)).hom.hom).comp
          (ezSummandLin X Y pq.1.1 pq.1.2)) from rfl]
  rw [show (ezHom X Y n).hom = DirectSum.toModule ℤ (tpIdx n)
        ↥((sChain (sProd X Y)).X n)
        (fun pq => ((eqToIso (congrArg (fun k => (sChain (sProd X Y)).X k) pq.2)).hom.hom).comp
          (ezSummandLin X Y pq.1.1 pq.1.2)) from rfl]
  rw [tpC_d]
  rw [ModuleCat.hom_ofHom]
  rw [show (tpD (sChain X) (sChain Y) n) = DirectSum.toModule ℤ (tpIdx (n + 1))
        (tpX (sChain X) (sChain Y) n) (tpDpq (sChain X) (sChain Y) n) from rfl]
  erw [toModule_comp, toModule_comp]
  apply congrArg (DirectSum.toModule ℤ (tpIdx (n + 1)) ↥((sChain (sProd X Y)).X n))
  funext pq
  exact ezSummand_d X Y n pq

end

end Work.Kunneth
