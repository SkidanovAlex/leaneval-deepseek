-- PORTED COPY (neutral island) of `Submission/Work/Serre/Surj/dzTpShiftQ.lean`.
-- The only changes are: the imports of ratShuffle-island modules are redirected to the
-- copies in `Submission/Work/Serre/Neu/`, and the abbrev `singSSet` is renamed to
-- `singSSetN` (same body) so that this module can coexist with `Work.Serre.E0Defs`,
-- which declares the same name.  Declarations and proofs are unchanged.
import Mathlib
import Submission.Work.Serre.Neu.Defs
import Submission.Work.Serre.crossProduct_defs
import Submission.Work.StemsB.RelChainsBaseChangeRat
import Submission.Work.Serre.Surj.DZGen

/-!
# The shift `H_m(C) ≅ H_{m+r+1}(C ⊗ ℤ[r+1])`

The complex `tpC C ℤ[r+1]` is `C` shifted by `r+1` degrees (the coefficient complex `ℤ[r+1]` is
concentrated in degree `r+1`, where it is free of rank one).  The present file constructs the
degreewise maps realising this shift, `x ↦ x ⊗ g` (with `g` the generator of `ℤ[r+1]`), shows that
they commute with the differentials up to the transport `twZ` of the total degree, and assembles
from them the isomorphism of homology of the target theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct MonoidalCategory

namespace Work.Serre.Surj

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-! ## The generator of `ℤ[r+1]` in degree `r+1` -/

/-- The generator of the coefficient complex `ℤ[r+1]` in degree `r+1`. -/
def dzTp_dzG (r : ℕ) : ↥((Work.Serre.dzComplex r).X (r+1)) := (Work.Serre.dzIso r).inv (1 : ℤ)

/-- The generator, as a `LinearEquiv` to `ℤ`. -/
def dzTp_dzLin (r : ℕ) : ↥((Work.Serre.dzComplex r).X (r+1)) ≃ₗ[ℤ] ℤ :=
  (Work.Serre.dzIso r).toLinearEquiv

lemma dzTp_dzLin_dzG (r : ℕ) : dzTp_dzLin r (dzTp_dzG r) = 1 := by
  change (Work.Serre.dzIso r).hom.hom ((Work.Serre.dzIso r).inv.hom (1 : ℤ)) = 1
  rw [Work.Kunneth.homIso_hom_apply]

/-- The differential of `ℤ[r+1]` kills its generator. -/
lemma dzTp_dzG_d (r : ℕ) :
    (ConcreteCategory.hom ((Work.Serre.dzComplex r).d (r+1) ((r+1)-1))) (dzTp_dzG r) = 0 := by
  rw [show ((Work.Serre.dzComplex r).d (r+1) ((r+1)-1)) = 0 from Work.Serre.dzComplex_d_succ r r]
  rfl

/-! ## The degreewise map `Cₙ ⟶ (C ⊗ ℤ[r+1])_{n+r+1}` -/

/-- The degreewise inclusion `Cₙ ⟶ (C ⊗ ℤ[r+1])_{n+r+1}`, `x ↦ x ⊗ dzG`. -/
def shiftZ (C : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) (n : ℕ) :
    ↥(C.X n) →ₗ[ℤ] Work.Kunneth.tpX C (Work.Serre.dzComplex r) (n+r+1) :=
  (Work.Kunneth.tpLof C (Work.Serre.dzComplex r) (n+r+1) ⟨(n, r+1), rfl⟩).comp
    ((LinearMap.applyₗ (dzTp_dzG r)).comp
      (TensorProduct.mk ℤ ↥(C.X n) ↥((Work.Serre.dzComplex r).X (r+1))))

lemma shiftZ_apply (C : ChainComplex (ModuleCat ℤ) ℕ) (r n : ℕ) (x : ↥(C.X n)) :
    shiftZ C r n x = Work.Kunneth.tpLof C (Work.Serre.dzComplex r) (n+r+1) ⟨(n, r+1), rfl⟩
      (x ⊗ₜ[ℤ] dzTp_dzG r) := rfl

/-- A congruence for `tpLof` in the index proof. -/
lemma tpLof_congr {C : ChainComplex (ModuleCat ℤ) ℕ} {r : ℕ} {n : ℕ} (p q : ℕ) (h h' : p + q = n)
    (v : Work.Kunneth.tpSummand C (Work.Serre.dzComplex r) p q) :
    Work.Kunneth.tpLof C (Work.Serre.dzComplex r) n ⟨(p,q), h⟩ v
      = Work.Kunneth.tpLof C (Work.Serre.dzComplex r) n ⟨(p,q), h'⟩ v := by
  congr 1

/-! ## The transport of elements along an equality of total degrees -/

/-- Transport of elements of the tensor complex along an equality of the total degree. -/
def twZ (C : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) {a b : ℕ} (h : a = b) :
    Work.Kunneth.tpX C (Work.Serre.dzComplex r) a ≃ₗ[ℤ]
      Work.Kunneth.tpX C (Work.Serre.dzComplex r) b :=
  h ▸ LinearEquiv.refl ℤ (Work.Kunneth.tpX C (Work.Serre.dzComplex r) a)

lemma twZ_tpLof {C : ChainComplex (ModuleCat ℤ) ℕ} {r : ℕ} {a b : ℕ} (h : a = b) (p q : ℕ)
    (hpq : p + q = a) (v : Work.Kunneth.tpSummand C (Work.Serre.dzComplex r) p q) :
    twZ C r h (Work.Kunneth.tpLof C (Work.Serre.dzComplex r) a ⟨(p,q), hpq⟩ v)
      = Work.Kunneth.tpLof C (Work.Serre.dzComplex r) b ⟨(p,q), by rw [← h]; exact hpq⟩ v := by
  cases h
  rfl

/-! ## The compatibility of the degreewise maps with the differentials -/

/-- **The "downwards" chain rule.** -/
lemma shiftZ_d_down (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) (hm : 1 ≤ m) (x : ↥(C.X m)) :
    twZ C r (by omega : m + r = (m-1) + r + 1)
        (Work.Kunneth.tpD C (Work.Serre.dzComplex r) (m+r) (shiftZ C r m x))
      = shiftZ C r (m-1) (C.d m (m-1) x) := by
  rw [shiftZ_apply, Work.Kunneth.tpD_lof_tmul]
  simp only [dif_pos hm, dif_pos (show (1:ℕ) ≤ r+1 by omega)]
  rw [dzTp_dzG_d, TensorProduct.tmul_zero, map_zero, zsmul_zero, add_zero]
  rw [twZ_tpLof, shiftZ_apply]

/-- **The "upwards" chain rule.** -/
lemma shiftZ_d_up (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) (x : ↥(C.X (m+1))) :
    Work.Kunneth.tpD C (Work.Serre.dzComplex r) (m+r+1)
        (twZ C r (by omega : (m+1) + r + 1 = (m+r+1) + 1) (shiftZ C r (m+1) x))
      = shiftZ C r m (C.d (m+1) m x) := by
  rw [shiftZ_apply, twZ_tpLof, Work.Kunneth.tpD_lof_tmul]
  simp only [dif_pos (show (1:ℕ) ≤ m+1 by omega), dif_pos (show (1:ℕ) ≤ r+1 by omega)]
  rw [dzTp_dzG_d, TensorProduct.tmul_zero, map_zero, zsmul_zero, add_zero]
  rw [shiftZ_apply]
  congr 1





/-! ## The linear algebra of the degreewise map -/

/-- The linear equivalence `Cₙ ⊗ ℤ[r+1] ≅ Cₙ` given by `x ⊗ g ↦ x`. -/
def dzTp_thetaLin (C : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) (n : ℕ) :
    (↥(C.X n) ⊗[ℤ] ↥((Work.Serre.dzComplex r).X (r+1))) ≃ₗ[ℤ] ↥(C.X n) :=
  (TensorProduct.congr (LinearEquiv.refl ℤ ↥(C.X n)) (dzTp_dzLin r)).trans
    (TensorProduct.rid ℤ ↥(C.X n))

lemma rid_tmul_toSpanSingleton {M : Type*} [AddCommGroup M] [Module ℤ M] (a : M) (k : ℤ) :
    (TensorProduct.rid ℤ M) (a ⊗ₜ[ℤ] k) = (LinearMap.toSpanSingleton ℤ M a) k := by
  rw [TensorProduct.rid_tmul, LinearMap.toSpanSingleton_apply]

lemma dzTp_thetaLin_tmul (C : ChainComplex (ModuleCat ℤ) ℕ) (r n : ℕ) (x : ↥(C.X n))
    (y : ↥((Work.Serre.dzComplex r).X (r+1))) :
    dzTp_thetaLin C r n (x ⊗ₜ[ℤ] y)
      = (LinearMap.toSpanSingleton ℤ ↥(C.X n) x) (dzTp_dzLin r y) := by
  rw [dzTp_thetaLin, LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  exact rid_tmul_toSpanSingleton x (dzTp_dzLin r y)

lemma dzTp_thetaLin_tmul_g (C : ChainComplex (ModuleCat ℤ) ℕ) (r n : ℕ) (x : ↥(C.X n)) :
    dzTp_thetaLin C r n (x ⊗ₜ[ℤ] dzTp_dzG r) = x := by
  rw [dzTp_thetaLin_tmul, dzTp_dzLin_dzG, LinearMap.toSpanSingleton_apply_one]

lemma dzTp_thetaLin_symm_apply (C : ChainComplex (ModuleCat ℤ) ℕ) (r n : ℕ) (x : ↥(C.X n)) :
    (dzTp_thetaLin C r n).symm x = x ⊗ₜ[ℤ] dzTp_dzG r :=
  (dzTp_thetaLin C r n).injective
    (by rw [LinearEquiv.apply_symm_apply, dzTp_thetaLin_tmul_g])

/-- The component of the tensor complex at the `(n, r+1)`-summand. -/
def dzTp_compLof (C : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) (n : ℕ) :
    Work.Kunneth.tpX C (Work.Serre.dzComplex r) (n+r+1) →ₗ[ℤ]
      (↥(C.X n) ⊗[ℤ] ↥((Work.Serre.dzComplex r).X (r+1))) :=
  DirectSum.component ℤ (Work.Kunneth.tpIdx (n+r+1))
    (fun rs => Work.Kunneth.tpSummand C (Work.Serre.dzComplex r) rs.1.1 rs.1.2)
    ⟨(n, r+1), rfl⟩

/-- The retraction `(C ⊗ ℤ[r+1])_{n+r+1} ⟶ Cₙ` of `shiftZ`. -/
def dzTp_evalDzG (C : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) (n : ℕ) :
    Work.Kunneth.tpX C (Work.Serre.dzComplex r) (n+r+1) →ₗ[ℤ] ↥(C.X n) :=
  (TensorProduct.rid ℤ ↥(C.X n)).toLinearMap.comp
    ((TensorProduct.map (LinearMap.id) ((Work.Serre.dzIso r).hom.hom)).comp
      (dzTp_compLof C r n))

lemma dzTp_compLof_lof (C : ChainComplex (ModuleCat ℤ) ℕ) (r n : ℕ)
    (v : ↥(C.X n) ⊗[ℤ] ↥((Work.Serre.dzComplex r).X (r+1))) :
    dzTp_compLof C r n
        (Work.Kunneth.tpLof C (Work.Serre.dzComplex r) (n+r+1) ⟨(n, r+1), rfl⟩ v) = v := by
  change DirectSum.component ℤ (Work.Kunneth.tpIdx (n+r+1))
    (fun rs => Work.Kunneth.tpSummand C (Work.Serre.dzComplex r) rs.1.1 rs.1.2)
    ⟨(n, r+1), rfl⟩
    (DirectSum.lof ℤ (Work.Kunneth.tpIdx (n+r+1))
      (fun rs => Work.Kunneth.tpSummand C (Work.Serre.dzComplex r) rs.1.1 rs.1.2)
      ⟨(n, r+1), rfl⟩ v) = v
  rw [DirectSum.component.of, dif_pos rfl]

lemma dzTp_evalDzG_shiftZ (C : ChainComplex (ModuleCat ℤ) ℕ) (r n : ℕ) (x : ↥(C.X n)) :
    dzTp_evalDzG C r n (shiftZ C r n x) = x := by
  have h2 : dzTp_compLof C r n
      (Work.Kunneth.tpLof C (Work.Serre.dzComplex r) (n+r+1) ⟨(n, r+1), rfl⟩
        (x ⊗ₜ[ℤ] dzTp_dzG r)) = x ⊗ₜ[ℤ] dzTp_dzG r :=
    dzTp_compLof_lof C r n _
  rw [dzTp_evalDzG, shiftZ_apply]
  show (TensorProduct.rid ℤ ↥(C.X n)) (TensorProduct.map (LinearMap.id)
      ((Work.Serre.dzIso r).hom.hom)
      (dzTp_compLof C r n
        (Work.Kunneth.tpLof C (Work.Serre.dzComplex r) (n+r+1) ⟨(n, r+1), rfl⟩
          (x ⊗ₜ[ℤ] dzTp_dzG r)))) = x
  rw [h2, TensorProduct.map_tmul, LinearMap.id_apply]
  exact dzTp_thetaLin_tmul_g C r n x

lemma shiftZ_injective (C : ChainComplex (ModuleCat ℤ) ℕ) (r n : ℕ) :
    Function.Injective (shiftZ C r n) := by
  intro x y h
  have h2 := congrArg (dzTp_evalDzG C r n) h
  simpa only [dzTp_evalDzG_shiftZ] using h2

lemma shiftZ_surjective (C : ChainComplex (ModuleCat ℤ) ℕ) (r n : ℕ) :
    Function.Surjective (shiftZ C r n) := by
  intro w
  have hsum : ∑ j : Work.Kunneth.tpIdx (n+r+1),
      Work.Kunneth.tpLof C (Work.Serre.dzComplex r) (n+r+1) j (w j) = w :=
    Work.Serre.tpX_sum_lof_gen C (Work.Serre.dzComplex r) (n+r+1) w
  have hsingle : ∑ j : Work.Kunneth.tpIdx (n+r+1),
      Work.Kunneth.tpLof C (Work.Serre.dzComplex r) (n+r+1) j (w j)
      = Work.Kunneth.tpLof C (Work.Serre.dzComplex r) (n+r+1) ⟨(n,r+1), rfl⟩
          (w ⟨(n,r+1),rfl⟩) := by
    rw [Finset.sum_eq_single ⟨(n, r+1), rfl⟩]
    · intro j _ hj
      have hq : j.1.2 ≠ r+1 := by
        intro hc
        apply hj
        apply Subtype.ext
        apply Prod.ext
        · show j.1.1 = n; omega
        · exact hc
      haveI : Subsingleton (Work.Kunneth.tpSummand C (Work.Serre.dzComplex r) j.1.1 j.1.2) :=
        Work.Serre.subsingleton_tpSummand_dz C r j.1.1 j.1.2 hq
      rw [Subsingleton.elim (w j) 0, map_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hc : dzTp_thetaLin C r n (w ⟨(n,r+1),rfl⟩) ⊗ₜ[ℤ] dzTp_dzG r = w ⟨(n,r+1),rfl⟩ := by
    rw [← dzTp_thetaLin_symm_apply C r n (dzTp_thetaLin C r n (w ⟨(n,r+1),rfl⟩)),
      LinearEquiv.symm_apply_apply]
  have hgoal : (Work.Kunneth.tpLof C (Work.Serre.dzComplex r) (n+r+1) ⟨(n,r+1),rfl⟩)
      (w ⟨(n,r+1),rfl⟩) = w := hsingle.symm.trans hsum
  exact ⟨dzTp_thetaLin C r n (w ⟨(n,r+1),rfl⟩), by
    rw [shiftZ_apply, hc]
    exact hgoal⟩

/-! ## The degreewise map as a morphism of complexes -/

/-- The degreewise map `Cₙ ⟶ (C ⊗ ℤ[r+1])_{n+r+1}` as a morphism of `ℤ`-modules. -/
def shiftZHom (C : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) (n : ℕ) :
    C.X n ⟶ (Work.Kunneth.tpC C (Work.Serre.dzComplex r)).X (n+r+1) :=
  ModuleCat.ofHom (shiftZ C r n)

/-- The transport of the degrees of `tpC C ℤ[r+1]` along an equality of the total degree, as an
isomorphism of `ℤ`-modules. -/
def twZIso (C : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) {a b : ℕ} (h : a = b) :
    (Work.Kunneth.tpC C (Work.Serre.dzComplex r)).X a ≅
      (Work.Kunneth.tpC C (Work.Serre.dzComplex r)).X b :=
  eqToIso (by rw [h])

lemma twZIso_inv_apply (C : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) {a b : ℕ} (h : a = b)
    (w : Work.Kunneth.tpX C (Work.Serre.dzComplex r) b) :
    (twZIso C r h).inv.hom (show ↥((Work.Kunneth.tpC C (Work.Serre.dzComplex r)).X b) from w)
      = (twZ C r h).symm w := by
  cases h; rfl

lemma twZIso_hom_apply (C : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) {a b : ℕ} (h : a = b)
    (w : Work.Kunneth.tpX C (Work.Serre.dzComplex r) a) :
    (twZIso C r h).hom.hom (show ↥((Work.Kunneth.tpC C (Work.Serre.dzComplex r)).X a) from w)
      = twZ C r h w := by
  cases h; rfl

/-- **The "downwards" chain rule**, elementwise. -/
lemma shiftZ_d_down_el (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) (hm : 1 ≤ m)
    (x : ↥(C.X m)) :
    (ModuleCat.Hom.hom ((Work.Kunneth.tpC C (Work.Serre.dzComplex r)).d (m+r+1) (m+r)))
        ((shiftZ C r m) x)
      = (ModuleCat.Hom.hom (twZIso C r (by omega : m + r = (m-1) + r + 1)).inv)
          ((shiftZ C r (m-1)) ((ModuleCat.Hom.hom (C.d m (m-1))) x)) := by
  have hd : (ModuleCat.Hom.hom ((Work.Kunneth.tpC C (Work.Serre.dzComplex r)).d (m+r+1) (m+r)))
        ((shiftZ C r m) x)
      = Work.Kunneth.tpD C (Work.Serre.dzComplex r) (m+r) (shiftZ C r m x) := by
    simp only [Work.Kunneth.tpC_d, ModuleCat.hom_ofHom]
    exact rfl
  rw [hd, twZIso_inv_apply, ← shiftZ_d_down C r m hm x, LinearEquiv.symm_apply_apply]

/-- **The "upwards" chain rule**, elementwise. -/
lemma shiftZ_d_up_el (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) (x : ↥(C.X (m+1))) :
    (ModuleCat.Hom.hom ((Work.Kunneth.tpC C (Work.Serre.dzComplex r)).d ((m+r+1)+1) (m+r+1)))
        ((ModuleCat.Hom.hom (twZIso C r (by omega : (m+1) + r + 1 = (m+r+1) + 1)).hom)
          ((shiftZ C r (m+1)) x))
      = (shiftZ C r m) ((ModuleCat.Hom.hom (C.d (m+1) m)) x) := by
  have hd : (ModuleCat.Hom.hom ((Work.Kunneth.tpC C (Work.Serre.dzComplex r)).d ((m+r+1)+1) (m+r+1)))
        ((ModuleCat.Hom.hom (twZIso C r (by omega : (m+1) + r + 1 = (m+r+1) + 1)).hom)
          ((shiftZ C r (m+1)) x))
      = Work.Kunneth.tpD C (Work.Serre.dzComplex r) (m+r+1)
          (twZ C r (by omega : (m+1) + r + 1 = (m+r+1) + 1) (shiftZ C r (m+1) x)) := by
    rw [twZIso_hom_apply]
    simp only [Work.Kunneth.tpC_d, ModuleCat.hom_ofHom]
    exact rfl
  rw [hd, shiftZ_d_up]

/-- **The "downwards" chain rule**, as morphisms. -/
lemma shiftZHom_d_down (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) (hm : 1 ≤ m) :
    shiftZHom C r m ≫ (Work.Kunneth.tpC C (Work.Serre.dzComplex r)).d (m+r+1) (m+r)
      = C.d m (m-1) ≫ shiftZHom C r (m-1)
        ≫ (twZIso C r (by omega : m + r = (m-1) + r + 1)).inv := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, shiftZHom, ModuleCat.hom_ofHom]
  exact shiftZ_d_down_el C r m hm x

/-- **The "upwards" chain rule**, as morphisms. -/
lemma shiftZHom_d_up (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) :
    C.d (m+1) m ≫ shiftZHom C r m
      = shiftZHom C r (m+1) ≫ (twZIso C r (by omega : (m+1) + r + 1 = (m+r+1) + 1)).hom
        ≫ (Work.Kunneth.tpC C (Work.Serre.dzComplex r)).d ((m+r+1)+1) (m+r+1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, shiftZHom, ModuleCat.hom_ofHom]
  exact (shiftZ_d_up_el C r m x).symm


/-! ## Extension of scalars to `ℚ` -/

/-- The element rule for the base change of a differential: on a pure tensor `1 ⊗ x`. -/
lemma intRatCM_d (K : ChainComplex (ModuleCat ℤ) ℕ) (i j : ℕ) (x : ↥(K.X i)) :
    (ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.obj K).d i j)) (TensorProduct.tmul ℤ (1 : ℚ) x)
      = TensorProduct.tmul ℤ (1 : ℚ) ((ModuleCat.Hom.hom (K.d i j)) x) := by
  simp only [Work.StemsB.IntRatCM, Functor.mapHomologicalComplex_obj_d]
  exact ModuleCat.ExtendScalars.map_tmul (Int.castRingHom ℚ) (K.d i j) (1 : ℚ) x

/-- The degreewise map is an isomorphism. -/
noncomputable def shiftZIso (C : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) (n : ℕ) :
    C.X n ≅ (Work.Kunneth.tpC C (Work.Serre.dzComplex r)).X (n+r+1) :=
  letI : IsIso (shiftZHom C r n) :=
    (ConcreteCategory.isIso_iff_bijective (shiftZHom C r n)).mpr
      ⟨shiftZ_injective C r n, shiftZ_surjective C r n⟩
  asIso (shiftZHom C r n)

/-- The degreewise isomorphism after base change to `ℚ`. -/
noncomputable def phiIso (C : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) (n : ℕ) :
    (Work.StemsB.IntRatCM.obj C).X n ≅
      (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).X (n+r+1) :=
  (Work.StemsB.IntRatF).mapIso (shiftZIso C r n)

/-- The degreewise isomorphism after base change, on a pure tensor. -/
lemma dzTp_Phi_tmul (C : ChainComplex (ModuleCat ℤ) ℕ) (r n : ℕ) (x : ↥(C.X n)) :
    (ConcreteCategory.hom (phiIso C r n).hom) (TensorProduct.tmul ℤ (1 : ℚ) x)
      = TensorProduct.tmul ℤ (1 : ℚ) (shiftZ C r n x) :=
  ModuleCat.ExtendScalars.map_tmul (Int.castRingHom ℚ) (shiftZIso C r n).hom (1 : ℚ) x

/-- The transport of the degrees of the tensor complex after base change along an equality of the
total degree. -/
noncomputable def twQIso (C : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) {a b : ℕ} (h : a = b) :
    (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).X a ≅
      (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).X b :=
  (Work.StemsB.IntRatF).mapIso (twZIso C r h)

/-- The forward transport of the degrees of the tensor complex after base change. -/
noncomputable abbrev twQHom (C : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) {a b : ℕ} (h : a = b) :=
  (twQIso C r h).hom

/-- The inverse transport of the degrees of the tensor complex after base change. -/
noncomputable abbrev twQInv (C : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) {a b : ℕ} (h : a = b) :=
  (twQIso C r h).inv

lemma IntRatF_map_d (C : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) (i j : ℕ) :
    (Work.StemsB.IntRatF).map ((Work.Kunneth.tpC C (Work.Serre.dzComplex r)).d i j)
      = (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).d i j :=
  (Functor.mapHomologicalComplex_obj_d (Work.StemsB.IntRatF) (ComplexShape.down ℕ)
    (Work.Kunneth.tpC C (Work.Serre.dzComplex r)) i j).symm

lemma IntRatF_map_dC (C : ChainComplex (ModuleCat ℤ) ℕ) (i j : ℕ) :
    (Work.StemsB.IntRatF).map (C.d i j) = (Work.StemsB.IntRatCM.obj C).d i j :=
  (Functor.mapHomologicalComplex_obj_d (Work.StemsB.IntRatF) (ComplexShape.down ℕ) C i j).symm

lemma IntRatF_map_shiftZHom (C : ChainComplex (ModuleCat ℤ) ℕ) (r n : ℕ) :
    (Work.StemsB.IntRatF).map (shiftZHom C r n) = (phiIso C r n).hom := rfl

/-- **The "downwards" chain rule after base change.** -/
lemma phiIso_d_down (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) (hm : 1 ≤ m) :
    (phiIso C r m).hom
        ≫ (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).d (m+r+1) (m+r)
      = (Work.StemsB.IntRatCM.obj C).d m (m-1) ≫ (phiIso C r (m-1)).hom
        ≫ (twQInv C r (by omega : m + r = (m-1) + r + 1)) := by
  have h := congrArg (fun (g : C.X m ⟶ (Work.Kunneth.tpC C (Work.Serre.dzComplex r)).X (m+r)) =>
    (Work.StemsB.IntRatF).map g) (shiftZHom_d_down C r m hm)
  simp only [Functor.map_comp, IntRatF_map_d, IntRatF_map_dC, IntRatF_map_shiftZHom] at h
  exact h

/-- **The "upwards" chain rule after base change.** -/
lemma phiIso_d_up (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) :
    (Work.StemsB.IntRatCM.obj C).d (m+1) m ≫ (phiIso C r m).hom
      = (phiIso C r (m+1)).hom ≫ (twQHom C r (by omega : (m+1) + r + 1 = (m+r+1) + 1))
        ≫ (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).d ((m+r+1)+1) (m+r+1) := by
  have h := congrArg (fun (g : C.X (m+1) ⟶ (Work.Kunneth.tpC C (Work.Serre.dzComplex r)).X (m+r+1)) =>
    (Work.StemsB.IntRatF).map g) (shiftZHom_d_up C r m)
  simp only [Functor.map_comp, IntRatF_map_d, IntRatF_map_dC, IntRatF_map_shiftZHom] at h
  exact h

/-! ## The low degrees of the tensor complex are trivial -/

/-- The tensor complex `C ⊗ ℤ[r+1]` is trivial in degrees `≤ r`. -/
lemma dzTp_subsingleton_tpX (C : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) {j : ℕ} (hj : j ≤ r) :
    Subsingleton (Work.Kunneth.tpX C (Work.Serre.dzComplex r) j) := by
  have h : ∀ x : Work.Kunneth.tpX C (Work.Serre.dzComplex r) j, x = 0 := fun x => by
    conv_lhs => rw [← Work.Serre.tpX_sum_lof_gen C (Work.Serre.dzComplex r) j x]
    refine Finset.sum_eq_zero (fun pq _ => ?_)
    have hq : pq.1.2 ≠ r+1 := by omega
    haveI : Subsingleton (Work.Kunneth.tpSummand C (Work.Serre.dzComplex r) pq.1.1 pq.1.2) :=
      Work.Serre.subsingleton_tpSummand_dz C r pq.1.1 pq.1.2 hq
    rw [Subsingleton.elim (x pq) 0, map_zero]
  exact ⟨fun x y => by rw [h x, h y]⟩

/-- Tensoring a subsingleton on the left with `ℚ` stays a subsingleton. -/
lemma dzTp_subsingleton_tensor_left {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] [Subsingleton M] : Subsingleton (M ⊗[ℤ] N) := by
  rw [subsingleton_iff]
  intro x y
  have hzero : ∀ z : M ⊗[ℤ] N, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [Subsingleton.elim m (0 : M), TensorProduct.zero_tmul]
    | add a b ha hb => rw [ha, hb, add_zero]
  rw [hzero x, hzero y]

/-- The low degrees of the base change of the tensor complex to `ℚ` are also trivial. -/
lemma dzTp_subsingleton_BX (C : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) {j : ℕ} (hj : j ≤ r) :
    Subsingleton ↥((Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).X j) := by
  haveI : Subsingleton ↥((Work.Kunneth.tpC C (Work.Serre.dzComplex r)).X j) :=
    dzTp_subsingleton_tpX C r hj
  haveI : Subsingleton (↥((Work.Kunneth.tpC C (Work.Serre.dzComplex r)).X j) ⊗[ℤ] ℚ) :=
    dzTp_subsingleton_tensor_left
  have he : ↥((Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).X j) ≃
      (↥((Work.Kunneth.tpC C (Work.Serre.dzComplex r)).X j) ⊗[ℤ] ℚ) :=
    (TensorProduct.comm ℤ ↥((Work.Kunneth.tpC C (Work.Serre.dzComplex r)).X j) ℚ).symm.toEquiv
  exact ⟨fun x y => he.injective (Subsingleton.elim (he x) (he y))⟩

/-- **The `(0+r+1, 0+r)`-differential of the tensor complex vanishes**, its target being trivial. -/
lemma dzTp_B_d_zero (C : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) :
    (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).d (0+r+1) (0+r)
      = 0 := by
  have h : (Work.Kunneth.tpC C (Work.Serre.dzComplex r)).d (0+r+1) (0+r) = 0 := by
    rw [show (Work.Kunneth.tpC C (Work.Serre.dzComplex r)).d (0+r+1) (0+r)
        = ModuleCat.ofHom (Work.Kunneth.tpD C (Work.Serre.dzComplex r) (0+r)) from
      Work.Kunneth.tpC_d C (Work.Serre.dzComplex r) (0+r)]
    have hz : Work.Kunneth.tpD C (Work.Serre.dzComplex r) (0+r) = 0 := by
      haveI : Subsingleton (Work.Kunneth.tpX C (Work.Serre.dzComplex r) (0+r)) :=
        dzTp_subsingleton_tpX C r (by omega)
      apply LinearMap.ext
      intro x
      exact Subsingleton.elim _ _
    rw [hz, ModuleCat.ofHom_zero]
  rw [← IntRatF_map_d C r (0+r+1) (0+r), h, Functor.map_zero]

/-! ## Cycles with a prescribed underlying chain -/

/-- The map `ℚ → K.X n`, `1 ↦ w`, composed with the differential, is zero when `w` is a cycle. -/
lemma dzTp_toSpan_hk (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) (w : ↥(K.X n))
    (hw : (ModuleCat.Hom.hom (K.d n (n-1))) w = 0) :
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ ↥(K.X n) w) ≫ K.d n (n-1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
    LinearMap.map_smul, hw, smul_zero]

/-- A cycle of a `ℚ`-chain complex with a prescribed underlying chain. -/
noncomputable def dzTp_cycleOfQ (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) (w : ↥(K.X n))
    (hw : (ModuleCat.Hom.hom (K.d n (n-1))) w = 0) : ↥(K.cycles n) :=
  (ModuleCat.Hom.hom (K.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ ↥(K.X n) w))
    (n-1) (Work.Kunneth.down_next n) (dzTp_toSpan_hk K n w hw))) (1 : ℚ)

/-- The underlying chain of `dzTp_cycleOfQ` is the prescribed one. -/
lemma dzTp_iCycles_cycleOfQ (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) (w : ↥(K.X n))
    (hw : (ModuleCat.Hom.hom (K.d n (n-1))) w = 0) :
    (ModuleCat.Hom.hom (K.iCycles n)) (dzTp_cycleOfQ K n w hw) = w := by
  have h := congrArg (fun (g : ModuleCat.of ℚ ℚ ⟶ K.X n) => (ModuleCat.Hom.hom g) (1 : ℚ))
    (HomologicalComplex.liftCycles_i K
      (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ ↥(K.X n) w)) (n-1)
      (Work.Kunneth.down_next n) (dzTp_toSpan_hk K n w hw))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, dzTp_cycleOfQ, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply_one] using h

/-! ## The inverse chain rules -/

/-- **The "downwards" chain rule, inverted.** -/
lemma phiIso_d_down_inv (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) (hm : 1 ≤ m) :
    (phiIso C r m).inv ≫ (Work.StemsB.IntRatCM.obj C).d m (m-1)
      = (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).d (m+r+1) (m+r)
        ≫ (twQHom C r (by omega : m + r = (m-1) + r + 1))
        ≫ (phiIso C r (m-1)).inv := by
  apply (cancel_epi (phiIso C r m).hom).mp
  conv_rhs => rw [← Category.assoc, phiIso_d_down C r m hm]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- **The "upwards" chain rule, inverted.** -/
lemma phiIso_d_up_inv (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) :
    (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).d ((m+r+1)+1) (m+r+1)
        ≫ (phiIso C r m).inv
      = (twQInv C r (by omega : (m+1) + r + 1 = (m+r+1) + 1))
        ≫ (phiIso C r (m+1)).inv ≫ (Work.StemsB.IntRatCM.obj C).d (m+1) m := by
  apply (cancel_mono (phiIso C r m).hom).mp
  simp only [Category.assoc]
  conv_rhs => rw [phiIso_d_up C r m]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-! ## The cycle-level maps and the isomorphism on homology -/

/-- The cycle condition for the cycle-level map `ψ`. -/
lemma dzTp_psi_hk (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) :
    ((Work.StemsB.IntRatCM.obj C).iCycles m ≫ (phiIso C r m).hom)
        ≫ (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).d (m+r+1) (m+r)
      = 0 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [dzTp_B_d_zero C r, comp_zero]
  · simp only [Category.assoc]
    rw [phiIso_d_down C r m hm]
    simp only [Category.assoc, HomologicalComplex.iCycles_d_assoc]
    rw [zero_comp]

/-- The cycle condition for the cycle-level map `ψ'`. -/
lemma dzTp_psiInv_hk (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) :
    ((Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).iCycles (m+r+1)
        ≫ (phiIso C r m).inv)
        ≫ (Work.StemsB.IntRatCM.obj C).d m (m-1)
      = 0 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [show (Work.StemsB.IntRatCM.obj C).d 0 (0-1) = 0 from
      HomologicalComplex.shape (Work.StemsB.IntRatCM.obj C) 0 0 (by simp [ComplexShape.down])]
    rw [comp_zero]
  · simp only [Category.assoc]
    rw [phiIso_d_down_inv C r m hm]
    simp only [Category.assoc, HomologicalComplex.iCycles_d_assoc]
    rw [zero_comp]

/-- The cycle-level map `ψ : Z_m(A) ⟶ Z_{m+r+1}(B)`. -/
noncomputable def dzTp_psiCyc (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) :
    (Work.StemsB.IntRatCM.obj C).cycles m
      ⟶ (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).cycles (m+r+1) :=
  (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).liftCycles
    ((Work.StemsB.IntRatCM.obj C).iCycles m ≫ (phiIso C r m).hom) (m+r)
    (Work.Kunneth.down_next (m+r+1)) (dzTp_psi_hk C r m)

/-- The cycle-level map `ψ' : Z_{m+r+1}(B) ⟶ Z_m(A)`. -/
noncomputable def dzTp_psiCycInv (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) :
    (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).cycles (m+r+1)
      ⟶ (Work.StemsB.IntRatCM.obj C).cycles m :=
  (Work.StemsB.IntRatCM.obj C).liftCycles
    ((Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).iCycles (m+r+1)
      ≫ (phiIso C r m).inv) (m-1)
    (Work.Kunneth.down_next m) (dzTp_psiInv_hk C r m)

lemma dzTp_psiCyc_iCycles (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) :
    dzTp_psiCyc C r m
        ≫ (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).iCycles (m+r+1)
      = (Work.StemsB.IntRatCM.obj C).iCycles m ≫ (phiIso C r m).hom :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

lemma dzTp_psiCycInv_iCycles (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) :
    dzTp_psiCycInv C r m ≫ (Work.StemsB.IntRatCM.obj C).iCycles m
      = (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).iCycles (m+r+1)
        ≫ (phiIso C r m).inv :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- **The boundary condition for `ψ`.** -/
lemma dzTp_psiCyc_toCycles (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) :
    (Work.StemsB.IntRatCM.obj C).toCycles (m+1) m ≫ dzTp_psiCyc C r m
      = (phiIso C r (m+1)).hom ≫ (twQHom C r (by omega : (m+1) + r + 1 = (m+r+1) + 1))
        ≫ (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).toCycles
            ((m+r+1)+1) (m+r+1) := by
  apply (cancel_mono ((Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).iCycles
    (m+r+1))).mp
  simp only [Category.assoc]
  rw [dzTp_psiCyc_iCycles]
  simp only [Category.assoc, HomologicalComplex.toCycles_i_assoc, HomologicalComplex.toCycles_i,
    Category.comp_id]
  exact phiIso_d_up C r m

/-- **The boundary condition for `ψ'`.** -/
lemma dzTp_psiCycInv_toCycles (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) :
    (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).toCycles
        ((m+r+1)+1) (m+r+1) ≫ dzTp_psiCycInv C r m
      = (twQInv C r (by omega : (m+1) + r + 1 = (m+r+1) + 1))
        ≫ (phiIso C r (m+1)).inv ≫ (Work.StemsB.IntRatCM.obj C).toCycles (m+1) m := by
  apply (cancel_mono ((Work.StemsB.IntRatCM.obj C).iCycles m)).mp
  simp only [Category.assoc]
  rw [dzTp_psiCycInv_iCycles]
  simp only [Category.assoc, HomologicalComplex.toCycles_i_assoc, HomologicalComplex.toCycles_i,
    Category.comp_id]
  exact phiIso_d_up_inv C r m

/-- The universal property datum defining the map induced by `ψ` on homology. -/
noncomputable def dzTp_eHomSub (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) :
    {l : (Work.StemsB.IntRatCM.obj C).homology m
        ⟶ (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).homology (m+r+1) //
      (Work.StemsB.IntRatCM.obj C).homologyπ m ≫ l
        = dzTp_psiCyc C r m
          ≫ (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).homologyπ (m+r+1)} :=
  CokernelCofork.IsColimit.desc'
    (HomologicalComplex.homologyIsCokernel (Work.StemsB.IntRatCM.obj C) (m+1) m
      (Work.Kunneth.down_prev m))
    (dzTp_psiCyc C r m
      ≫ (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).homologyπ (m+r+1))
    (by
      rw [← Category.assoc, dzTp_psiCyc_toCycles C r m]
      simp only [Category.assoc, HomologicalComplex.toCycles_comp_homologyπ, comp_zero])

/-- The universal property datum defining the map induced by `ψ'` on homology. -/
noncomputable def dzTp_eInvSub (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) :
    {l : (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).homology (m+r+1)
        ⟶ (Work.StemsB.IntRatCM.obj C).homology m //
      (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).homologyπ (m+r+1) ≫ l
        = dzTp_psiCycInv C r m ≫ (Work.StemsB.IntRatCM.obj C).homologyπ m} :=
  CokernelCofork.IsColimit.desc'
    (HomologicalComplex.homologyIsCokernel
      (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r)))
      ((m+r+1)+1) (m+r+1) (Work.Kunneth.down_prev (m+r+1)))
    (dzTp_psiCycInv C r m ≫ (Work.StemsB.IntRatCM.obj C).homologyπ m)
    (by
      rw [← Category.assoc, dzTp_psiCycInv_toCycles C r m]
      simp only [Category.assoc, HomologicalComplex.toCycles_comp_homologyπ, comp_zero])

/-- The map induced by `ψ` on homology. -/
noncomputable def dzTp_eHom (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) :
    (Work.StemsB.IntRatCM.obj C).homology m
      ⟶ (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).homology (m+r+1) :=
  (dzTp_eHomSub C r m).1

/-- The map induced by `ψ'` on homology. -/
noncomputable def dzTp_eInv (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) :
    (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).homology (m+r+1)
      ⟶ (Work.StemsB.IntRatCM.obj C).homology m :=
  (dzTp_eInvSub C r m).1

lemma dzTp_eHom_homologyπ (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) :
    (Work.StemsB.IntRatCM.obj C).homologyπ m ≫ dzTp_eHom C r m
      = dzTp_psiCyc C r m
        ≫ (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).homologyπ (m+r+1) :=
  (dzTp_eHomSub C r m).2

lemma dzTp_eInv_homologyπ (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) :
    (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).homologyπ (m+r+1)
        ≫ dzTp_eInv C r m
      = dzTp_psiCycInv C r m ≫ (Work.StemsB.IntRatCM.obj C).homologyπ m :=
  (dzTp_eInvSub C r m).2

/-- The cycle-level maps `ψ` and `ψ'` are mutually inverse. -/
lemma dzTp_psiCyc_psiCycInv (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) :
    dzTp_psiCyc C r m ≫ dzTp_psiCycInv C r m
      = 𝟙 ((Work.StemsB.IntRatCM.obj C).cycles m) := by
  apply (cancel_mono ((Work.StemsB.IntRatCM.obj C).iCycles m)).mp
  rw [Category.assoc, dzTp_psiCycInv_iCycles]
  rw [← Category.assoc, dzTp_psiCyc_iCycles]
  rw [Category.assoc, Iso.hom_inv_id]
  rw [Category.comp_id, Category.id_comp]

lemma dzTp_psiCyc_psiCycInv_assoc (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ)
    {Z : ModuleCat ℚ} (f : (Work.StemsB.IntRatCM.obj C).cycles m ⟶ Z) :
    dzTp_psiCyc C r m ≫ dzTp_psiCycInv C r m ≫ f = f := by
  rw [← Category.assoc, dzTp_psiCyc_psiCycInv, Category.id_comp]

/-- The cycle-level maps `ψ'` and `ψ` are mutually inverse. -/
lemma dzTp_psiCycInv_psiCyc (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) :
    dzTp_psiCycInv C r m ≫ dzTp_psiCyc C r m
      = 𝟙 ((Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).cycles (m+r+1)) := by
  apply (cancel_mono ((Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).iCycles
    (m+r+1))).mp
  rw [Category.assoc, dzTp_psiCyc_iCycles]
  rw [← Category.assoc, dzTp_psiCycInv_iCycles]
  rw [Category.assoc, Iso.inv_hom_id]
  rw [Category.comp_id, Category.id_comp]

lemma dzTp_psiCycInv_psiCyc_assoc (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ)
    {Z : ModuleCat ℚ}
    (f : (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).cycles (m+r+1) ⟶ Z) :
    dzTp_psiCycInv C r m ≫ dzTp_psiCyc C r m ≫ f = f := by
  rw [← Category.assoc, dzTp_psiCycInv_psiCyc, Category.id_comp]

/-- The two maps on homology are mutually inverse. -/
lemma dzTp_eHom_eInv (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) :
    dzTp_eHom C r m ≫ dzTp_eInv C r m = 𝟙 _ := by
  apply (cancel_epi ((Work.StemsB.IntRatCM.obj C).homologyπ m)).mp
  rw [← Category.assoc, dzTp_eHom_homologyπ]
  rw [Category.assoc, dzTp_eInv_homologyπ]
  rw [dzTp_psiCyc_psiCycInv_assoc]
  rw [Category.comp_id]

/-- The two maps on homology are mutually inverse. -/
lemma dzTp_eInv_eHom (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) :
    dzTp_eInv C r m ≫ dzTp_eHom C r m = 𝟙 _ := by
  apply (cancel_epi ((Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).homologyπ
    (m+r+1))).mp
  rw [← Category.assoc, dzTp_eInv_homologyπ]
  rw [Category.assoc, dzTp_eHom_homologyπ]
  rw [dzTp_psiCycInv_psiCyc_assoc]
  rw [Category.comp_id]

/-- The chain `shiftZ x` is the underlying chain of the cross product of `x` with the generator of
the coefficient complex. -/
lemma shiftZ_eq_iCycles_crossCycTens (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ)
    (h : m + (r+1) = m+r+1) (u : ↥(C.cycles m)) :
    shiftZ C r m ((C.iCycles m).hom u)
      = ((Work.Kunneth.tpC C (Work.Serre.dzComplex r)).iCycles (m+r+1)).hom
          (Work.Kunneth.crossCycTens C (Work.Serre.dzComplex r) (m+r+1) m (r+1) h
            (u ⊗ₜ[ℤ] Work.Serre.Surj.dzGenCycle r)) := by
  have hcoe : ((Work.Kunneth.tpC C (Work.Serre.dzComplex r)).iCycles (m+r+1)).hom
        (Work.Kunneth.crossCycTens C (Work.Serre.dzComplex r) (m+r+1) m (r+1) h
          (u ⊗ₜ[ℤ] Work.Serre.Surj.dzGenCycle r))
      = Work.Kunneth.tpLof C (Work.Serre.dzComplex r) (m+r+1) ⟨(m, r+1), h⟩
          (((C.iCycles m).hom u) ⊗ₜ[ℤ] dzTp_dzG r) := by
    rw [Work.Kunneth.iCycles_crossCycTens_tmul C (Work.Serre.dzComplex r) (m+r+1) m (r+1) h u
      (Work.Serre.Surj.dzGenCycle r), Work.Serre.Surj.iCycles_dzGenCycle r]
    simp only [dzTp_dzG]
  rw [shiftZ_apply, hcoe]

theorem dzTpShiftQ (C : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ) : ∃ e : (Work.StemsB.IntRatCM.obj C).homology m ≅ (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).homology (m + r + 1), ∀ (u : ↥(C.cycles m)), ∃ (x : ↥((Work.StemsB.IntRatCM.obj C).cycles m)) (y : ↥((Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).cycles (m + r + 1))), (Work.StemsB.IntRatCM.obj C).iCycles m x = TensorProduct.tmul ℤ (1 : ℚ) ((C.iCycles m).hom u) ∧ (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).iCycles (m + r + 1) y = TensorProduct.tmul ℤ (1 : ℚ) (((Work.Kunneth.tpC C (Work.Serre.dzComplex r)).iCycles (m + r + 1)).hom (Work.Kunneth.crossCycTens C (Work.Serre.dzComplex r) (m + r + 1) m (r + 1) (by omega) (u ⊗ₜ[ℤ] Work.Serre.Surj.dzGenCycle r))) ∧ e.hom ((Work.StemsB.IntRatCM.obj C).homologyπ m x) = (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).homologyπ (m + r + 1) y := by
  refine ⟨Iso.mk (dzTp_eHom C r m) (dzTp_eInv C r m) (dzTp_eHom_eInv C r m)
    (dzTp_eInv_eHom C r m), ?_⟩
  intro u
  have hcd : (ModuleCat.Hom.hom (C.d m (m-1))) ((C.iCycles m).hom u) = 0 := by
    have h := congrArg (fun (g : C.cycles m ⟶ C.X (m-1)) => (ModuleCat.Hom.hom g) u)
      (HomologicalComplex.iCycles_d C m (m-1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  have hxu : (ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.obj C).d m (m-1)))
      (TensorProduct.tmul ℤ (1 : ℚ) ((C.iCycles m).hom u)) = 0 := by
    rw [intRatCM_d C m (m-1), hcd]
    simp
  set cx : ↥((Work.StemsB.IntRatCM.obj C).cycles m) :=
    dzTp_cycleOfQ (Work.StemsB.IntRatCM.obj C) m
      (TensorProduct.tmul ℤ (1 : ℚ) ((C.iCycles m).hom u)) hxu with hcx
  have hx1 : (ConcreteCategory.hom ((Work.StemsB.IntRatCM.obj C).iCycles m)) cx
      = TensorProduct.tmul ℤ (1 : ℚ) ((C.iCycles m).hom u) := by
    rw [hcx]
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      (dzTp_iCycles_cycleOfQ (Work.StemsB.IntRatCM.obj C) m
        (TensorProduct.tmul ℤ (1 : ℚ) ((C.iCycles m).hom u)) hxu)
  have hy1 :
      (ConcreteCategory.hom
          ((Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).iCycles
            (m+r+1)))
        ((ConcreteCategory.hom (dzTp_psiCyc C r m)) cx)
      = TensorProduct.tmul ℤ (1 : ℚ)
          ((ConcreteCategory.hom
              ((Work.Kunneth.tpC C (Work.Serre.dzComplex r)).iCycles (m + r + 1)))
            (Work.Kunneth.crossCycTens C (Work.Serre.dzComplex r) (m + r + 1) m (r + 1)
              (by omega) (u ⊗ₜ[ℤ] Work.Serre.Surj.dzGenCycle r))) := by
    have h1 :
        (ConcreteCategory.hom
            ((Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).iCycles
              (m+r+1)))
          ((ConcreteCategory.hom (dzTp_psiCyc C r m)) cx)
        = (ConcreteCategory.hom (phiIso C r m).hom)
            ((ConcreteCategory.hom ((Work.StemsB.IntRatCM.obj C).iCycles m)) cx) := by
      have h := congrArg (fun (g : (Work.StemsB.IntRatCM.obj C).cycles m
          ⟶ (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).X (m+r+1)) =>
        (ConcreteCategory.hom g) cx) (dzTp_psiCyc_iCycles C r m)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
    rw [h1, hx1, dzTp_Phi_tmul C r m ((C.iCycles m).hom u)]
    rw [shiftZ_eq_iCycles_crossCycTens C r m _ u]
  have hzy :
      (ConcreteCategory.hom (dzTp_eHom C r m))
        ((ConcreteCategory.hom ((Work.StemsB.IntRatCM.obj C).homologyπ m)) cx)
      = (ConcreteCategory.hom
          ((Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).homologyπ
            (m+r+1)))
        ((ConcreteCategory.hom (dzTp_psiCyc C r m)) cx) := by
    have h := congrArg (fun (g : (Work.StemsB.IntRatCM.obj C).cycles m
        ⟶ (Work.StemsB.IntRatCM.obj (Work.Kunneth.tpC C (Work.Serre.dzComplex r))).homology
            (m+r+1)) => (ConcreteCategory.hom g) cx) (dzTp_eHom_homologyπ C r m)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  exact ⟨cx, (ConcreteCategory.hom (dzTp_psiCyc C r m)) cx, hx1, hy1, hzy⟩


end

end Work.Serre.Surj
