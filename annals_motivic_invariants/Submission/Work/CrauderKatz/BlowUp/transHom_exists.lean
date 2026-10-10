/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CrauderKatz
-/
import Mathlib
import Submission.Work.CrauderKatz.BlowUp.ThickDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

/-!
# `Work.CrauderKatz.BlowUp.transHom_exists` — the transition map of the thickened blow-up

The two charts of the (thickened) blow-up of the affine plane both have ring

`R 𝕜 = 𝕜[x,t,ε]/(ε², x·ε)`   (`thickRing 𝕜`, with `x = thickX`, `t = thickT`, `ε = thickE`),

and their overlap ring is `R 𝕜[1/t] = ovRing 𝕜`.  The classical transition map between the two
charts — in the coordinates of the second chart, `(y, s) ↦ (y s, s)`, i.e. on the overlap
`y ↦ x·t`, `s ↦ t⁻¹` — is the ring homomorphism

`φ : R 𝕜 →+* R 𝕜[1/t],   x ↦ x·t,   t ↦ t⁻¹,   ε ↦ ε`.

We prove that such a `φ` exists, that `Spec φ` is an open immersion (it identifies `Spec R[1/t]`
with the open subscheme `D(t) ⊆ Spec R`) and that it has the three prescribed values on the
generators.

The map `φ` is the composite `φ = σ ∘ L` where `L : R →+* R[1/t]` is the localization map (which
*alone* already has `Spec` an open immersion) and `σ` is the ring automorphism of `R[1/t]`
sending `L x ↦ L x · L t`, `L t ↦ (L t)⁻¹`, `L ε ↦ L ε`; `σ` is an involution, whence
`Spec σ` is an isomorphism and `Spec φ = Spec σ ≫ Spec L` is an open immersion.

## Main results

* `Work.CrauderKatz.BlowUp.transSubst` : the substitution `x ↦ x·t, t ↦ t⁻¹, ε ↦ ε` as a ring
  homomorphism `thickRing 𝕜 →+* ovRing 𝕜`.
* `Work.CrauderKatz.BlowUp.transSigma` : the induced automorphism of `ovRing 𝕜`.
* `Work.CrauderKatz.BlowUp.transHom_exists` : existence of the transition homomorphism `φ`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open MvPolynomial

namespace Work.CrauderKatz.BlowUp

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

variable (𝕜 : Type) [Field 𝕜]

/-! ### The substitution `x ↦ x·t`, `t ↦ t⁻¹`, `ε ↦ ε` on the polynomial ring -/

/-- The polynomial substitution `x ↦ x·t`, `t ↦ t⁻¹`, `ε ↦ ε`, i.e. the map on `𝕜[x,t,ε]`
corresponding to the transition between the two charts of the blow-up (in the direction from the
second chart's ring to the first chart's overlap).  Here `x = thickX 𝕜` is the first chart's
exceptional coordinate, which is the coordinate `y` of the overlap, and `t = thickT 𝕜` is the
overlap coordinate to be inverted. -/
def transPoly : MvPolynomial (Fin 3) 𝕜 →+* ovRing 𝕜 :=
  MvPolynomial.eval₂Hom (algebraMap 𝕜 (ovRing 𝕜)) (fun i : Fin 3 =>
    if i = 0 then
      algebraMap (thickRing 𝕜) (ovRing 𝕜) (thickX 𝕜) *
        algebraMap (thickRing 𝕜) (ovRing 𝕜) (thickT 𝕜)
    else if i = 1 then IsLocalization.Away.invSelf (thickT 𝕜)
    else algebraMap (thickRing 𝕜) (ovRing 𝕜) (thickE 𝕜))

lemma transPoly_X0 : transPoly 𝕜 (MvPolynomial.X 0) =
    algebraMap (thickRing 𝕜) (ovRing 𝕜) (thickX 𝕜) *
      algebraMap (thickRing 𝕜) (ovRing 𝕜) (thickT 𝕜) := by
  simp [transPoly]

lemma transPoly_X1 : transPoly 𝕜 (MvPolynomial.X 1) =
    IsLocalization.Away.invSelf (thickT 𝕜) := by
  simp [transPoly]

lemma transPoly_X2 : transPoly 𝕜 (MvPolynomial.X 2) =
    algebraMap (thickRing 𝕜) (ovRing 𝕜) (thickE 𝕜) := by
  simp [transPoly]

lemma transPoly_C (r : 𝕜) :
    transPoly 𝕜 (MvPolynomial.C r) = algebraMap 𝕜 (ovRing 𝕜) r := by
  simp [transPoly]

/-- The substitution kills the two relations `ε²` and `x·ε` defining `thickI 𝕜`. -/
lemma mem_thickI_transPoly : thickI 𝕜 ≤ RingHom.ker (transPoly 𝕜) := by
  simp only [thickI]
  rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  constructor
  · change transPoly 𝕜 (MvPolynomial.X 2 ^ 2) = 0
    rw [map_pow, transPoly_X2, ← map_pow, thickE_sq, map_zero]
  · change transPoly 𝕜 (MvPolynomial.X 0 * MvPolynomial.X 2) = 0
    rw [map_mul, transPoly_X0, transPoly_X2, mul_assoc, ← map_mul, ← map_mul]
    rw [show thickX 𝕜 * (thickT 𝕜 * thickE 𝕜) = 0 by
      rw [← mul_assoc, mul_comm (thickX 𝕜), mul_assoc, thickX_mul_thickE, mul_zero], map_zero]

/-! ### The substitution on the chart ring -/

/-- The transition substitution as a ring homomorphism `thickRing 𝕜 →+* ovRing 𝕜`, obtained by
descending `transPoly` to the quotient `R 𝕜 = 𝕜[x,t,ε]/(ε², x·ε)`. -/
def transSubst : thickRing 𝕜 →+* ovRing 𝕜 :=
  Ideal.Quotient.lift (thickI 𝕜) (transPoly 𝕜)
    (fun _a ha => RingHom.mem_ker.mp (mem_thickI_transPoly 𝕜 ha))

lemma transSubst_mk (p : MvPolynomial (Fin 3) 𝕜) :
    transSubst 𝕜 (Ideal.Quotient.mk (thickI 𝕜) p) = transPoly 𝕜 p := by
  change (Ideal.Quotient.lift (thickI 𝕜) (transPoly 𝕜) _)
    (Ideal.Quotient.mk (thickI 𝕜) p) = transPoly 𝕜 p
  rw [Ideal.Quotient.lift_mk]

lemma transSubst_X : transSubst 𝕜 (thickX 𝕜) =
    algebraMap (thickRing 𝕜) (ovRing 𝕜) (thickX 𝕜) *
      algebraMap (thickRing 𝕜) (ovRing 𝕜) (thickT 𝕜) := by
  show transSubst 𝕜 (Ideal.Quotient.mk (thickI 𝕜) (MvPolynomial.X 0)) = _
  rw [transSubst_mk, transPoly_X0]

lemma transSubst_T : transSubst 𝕜 (thickT 𝕜) =
    IsLocalization.Away.invSelf (thickT 𝕜) := by
  show transSubst 𝕜 (Ideal.Quotient.mk (thickI 𝕜) (MvPolynomial.X 1)) = _
  rw [transSubst_mk, transPoly_X1]

lemma transSubst_E : transSubst 𝕜 (thickE 𝕜) =
    algebraMap (thickRing 𝕜) (ovRing 𝕜) (thickE 𝕜) := by
  show transSubst 𝕜 (Ideal.Quotient.mk (thickI 𝕜) (MvPolynomial.X 2)) = _
  rw [transSubst_mk, transPoly_X2]

/-- `transSubst (thickT 𝕜) = (thickT 𝕜)⁻¹` is invertible, so the substitution can be lifted
through the localization `R 𝕜 → R 𝕜[1/t]`. -/
lemma hunit_transSubst : IsUnit (transSubst 𝕜 (thickT 𝕜)) := by
  rw [transSubst_T]
  exact isUnit_iff_exists_inv'.mpr ⟨_, IsLocalization.Away.mul_invSelf (thickT 𝕜)⟩

/-- The constants of `𝕜[x,t,ε]` map to the constants of `R 𝕜`. -/
lemma mk_C_eq_algebraMap (r : 𝕜) :
    Ideal.Quotient.mk (thickI 𝕜) (MvPolynomial.C r) = algebraMap 𝕜 (thickRing 𝕜) r := by
  rw [IsScalarTower.algebraMap_apply 𝕜 (MvPolynomial (Fin 3) 𝕜) (thickRing 𝕜),
    MvPolynomial.algebraMap_eq, Ideal.Quotient.algebraMap_eq]

/-! ### The induced automorphism `σ` of the overlap ring -/

/-- The endomorphism `σ` of the overlap ring `R 𝕜[1/t]` induced by the substitution
`L x ↦ L x · L t`, `L t ↦ (L t)⁻¹`, `L ε ↦ L ε`.  It is an involution (see
`transSigma_comp_self`), hence a ring automorphism. -/
def transSigma : ovRing 𝕜 →+* ovRing 𝕜 :=
  IsLocalization.Away.lift (thickT 𝕜) (g := transSubst 𝕜) (hunit_transSubst 𝕜)

lemma transSigma_algebraMap (y : thickRing 𝕜) :
    transSigma 𝕜 (algebraMap (thickRing 𝕜) (ovRing 𝕜) y) = transSubst 𝕜 y := by
  unfold transSigma
  rw [IsLocalization.Away.lift_eq]

/-- `σ` sends the three images of the generators of `R 𝕜` back to `R 𝕜`: the composite
`σ ∘ (substitution)` is the localization map `L`. -/
lemma transSigma_key : (transSigma 𝕜).comp (transPoly 𝕜) =
    (algebraMap (thickRing 𝕜) (ovRing 𝕜)).comp (Ideal.Quotient.mk (thickI 𝕜)) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · rw [RingHom.comp_apply, transPoly_C, RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply 𝕜 (thickRing 𝕜) (ovRing 𝕜) r]
    unfold transSigma
    rw [IsLocalization.Away.lift_eq]
    rw [← mk_C_eq_algebraMap 𝕜 r]
    rw [transSubst_mk, transPoly_C, mk_C_eq_algebraMap 𝕜 r,
      ← IsScalarTower.algebraMap_apply 𝕜 (thickRing 𝕜) (ovRing 𝕜) r]
  · rw [RingHom.comp_apply]
    fin_cases i
    · show transSigma 𝕜 (transPoly 𝕜 (MvPolynomial.X 0)) =
        algebraMap (thickRing 𝕜) (ovRing 𝕜) (Ideal.Quotient.mk (thickI 𝕜) (MvPolynomial.X 0))
      rw [transPoly_X0]
      unfold transSigma
      rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq, transSubst_X, transSubst_T,
        mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
      rfl
    · show transSigma 𝕜 (transPoly 𝕜 (MvPolynomial.X 1)) =
        algebraMap (thickRing 𝕜) (ovRing 𝕜) (Ideal.Quotient.mk (thickI 𝕜) (MvPolynomial.X 1))
      rw [transPoly_X1]
      have hσ : transSigma 𝕜 (algebraMap (thickRing 𝕜) (ovRing 𝕜) (thickT 𝕜)) =
          IsLocalization.Away.invSelf (thickT 𝕜) := by
        unfold transSigma
        rw [IsLocalization.Away.lift_eq, transSubst_T]
      have ha : IsLocalization.Away.invSelf (thickT 𝕜) *
          algebraMap (thickRing 𝕜) (ovRing 𝕜) (thickT 𝕜) = 1 := by
        rw [mul_comm]
        exact IsLocalization.Away.mul_invSelf (thickT 𝕜)
      have hσa : IsLocalization.Away.invSelf (thickT 𝕜) *
          transSigma 𝕜 (IsLocalization.Away.invSelf (thickT 𝕜)) = 1 := by
        have h1 : transSigma 𝕜 (algebraMap (thickRing 𝕜) (ovRing 𝕜) (thickT 𝕜) *
            IsLocalization.Away.invSelf (thickT 𝕜)) = 1 := by
          rw [IsLocalization.Away.mul_invSelf, map_one]
        rw [map_mul, hσ] at h1
        exact h1
      calc transSigma 𝕜 (IsLocalization.Away.invSelf (thickT 𝕜))
          = (IsLocalization.Away.invSelf (thickT 𝕜) *
              algebraMap (thickRing 𝕜) (ovRing 𝕜) (thickT 𝕜)) *
              transSigma 𝕜 (IsLocalization.Away.invSelf (thickT 𝕜)) := by rw [ha, one_mul]
        _ = algebraMap (thickRing 𝕜) (ovRing 𝕜) (thickT 𝕜) *
              (IsLocalization.Away.invSelf (thickT 𝕜) *
                transSigma 𝕜 (IsLocalization.Away.invSelf (thickT 𝕜))) := by
              first | refl_ring1 | ring
        _ = algebraMap (thickRing 𝕜) (ovRing 𝕜) (thickT 𝕜) * 1 := by rw [hσa]
        _ = algebraMap (thickRing 𝕜) (ovRing 𝕜) (thickT 𝕜) := mul_one _
    · show transSigma 𝕜 (transPoly 𝕜 (MvPolynomial.X 2)) =
        algebraMap (thickRing 𝕜) (ovRing 𝕜) (Ideal.Quotient.mk (thickI 𝕜) (MvPolynomial.X 2))
      rw [transPoly_X2]
      unfold transSigma
      rw [IsLocalization.Away.lift_eq, transSubst_E]
      rfl

/-- `σ` restricts to the identity of `R 𝕜 ⊂ R 𝕜[1/t]` in the sense that
`σ ∘ transSubst = L`. -/
lemma transSigma_comp_transSubst : (transSigma 𝕜).comp (transSubst 𝕜) =
    algebraMap (thickRing 𝕜) (ovRing 𝕜) := by
  apply RingHom.ext
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [RingHom.comp_apply, transSubst_mk]
  simpa using RingHom.congr_fun (transSigma_key 𝕜) p

/-- `σ` is an involution. -/
lemma transSigma_comp_self : (transSigma 𝕜).comp (transSigma 𝕜) = RingHom.id (ovRing 𝕜) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (thickT 𝕜)) (RingHom.ext (fun a => ?_))
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [transSigma_algebraMap]
  exact RingHom.congr_fun (transSigma_comp_transSubst 𝕜) a

lemma transSigma_invol (x : ovRing 𝕜) : transSigma 𝕜 (transSigma 𝕜 x) = x := by
  have h := RingHom.congr_fun (transSigma_comp_self 𝕜) x
  simpa [RingHom.comp_apply] using h

/-- `σ` as a ring equivalence (it is its own inverse). -/
def transSigmaEquiv : ovRing 𝕜 ≃+* ovRing 𝕜 where
  toFun := transSigma 𝕜
  invFun := transSigma 𝕜
  left_inv := transSigma_invol 𝕜
  right_inv := transSigma_invol 𝕜
  map_mul' := (transSigma 𝕜).map_mul
  map_add' := (transSigma 𝕜).map_add

lemma isIso_ofHom_transSigma : IsIso (CommRingCat.ofHom (transSigma 𝕜)) := by
  have h : CommRingCat.ofHom (transSigma 𝕜) =
      (RingEquiv.toCommRingCatIso (transSigmaEquiv 𝕜)).hom := by
    ext x
    rfl
  rw [h]
  infer_instance

lemma isOpenImmersion_Spec_transSigma :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (transSigma 𝕜))) := by
  rw [show CommRingCat.ofHom (transSigma 𝕜) =
      (RingEquiv.toCommRingCatIso (transSigmaEquiv 𝕜)).hom from by
    ext x
    rfl]
  infer_instance

/-! ### The transition homomorphism -/

/-- The transition homomorphism `φ : R 𝕜 →+* R 𝕜[1/t]` with `φ x = x·t`, `φ t = t⁻¹`,
`φ ε = ε`. -/
def transHom : thickRing 𝕜 →+* ovRing 𝕜 :=
  (transSigma 𝕜).comp (algebraMap (thickRing 𝕜) (ovRing 𝕜))

lemma transHom_X : transHom 𝕜 (thickX 𝕜) =
    algebraMap (thickRing 𝕜) (ovRing 𝕜) (thickX 𝕜) *
      algebraMap (thickRing 𝕜) (ovRing 𝕜) (thickT 𝕜) := by
  rw [transHom, RingHom.comp_apply, transSigma_algebraMap, transSubst_X]

lemma transHom_T : transHom 𝕜 (thickT 𝕜) = IsLocalization.Away.invSelf (thickT 𝕜) := by
  rw [transHom, RingHom.comp_apply, transSigma_algebraMap, transSubst_T]

lemma transHom_E : transHom 𝕜 (thickE 𝕜) =
    algebraMap (thickRing 𝕜) (ovRing 𝕜) (thickE 𝕜) := by
  rw [transHom, RingHom.comp_apply, transSigma_algebraMap, transSubst_E]

/-- The transition map `Spec R 𝕜[1/t] → Spec R 𝕜` is an open immersion: it is the composite of
the localization open immersion with the automorphism `σ` of the source. -/
lemma isOpenImmersion_Spec_transHom :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (transHom 𝕜))) := by
  rw [transHom, CommRingCat.ofHom_comp, Spec.map_comp]
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (transSigma 𝕜))) :=
    isOpenImmersion_Spec_transSigma 𝕜
  infer_instance

/-- **The transition homomorphism of the thickened blow-up of the plane.**  There is a ring
homomorphism `φ : R 𝕜 →+* R 𝕜[1/t]` (the transition between the two charts, restricted to the
overlap) with `Spec.map φ` an open immersion, `φ(x) = x·t`, `φ(t) = t⁻¹` and `φ(ε) = ε`. -/
theorem transHom_exists (𝕜 : Type) [Field 𝕜] : ∃ (φ : Work.CrauderKatz.BlowUp.thickRing 𝕜 →+* Work.CrauderKatz.BlowUp.ovRing 𝕜), AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) ∧ φ (Work.CrauderKatz.BlowUp.thickX 𝕜) = algebraMap _ _ (Work.CrauderKatz.BlowUp.thickX 𝕜) * algebraMap _ _ (Work.CrauderKatz.BlowUp.thickT 𝕜) ∧ φ (Work.CrauderKatz.BlowUp.thickT 𝕜) = IsLocalization.Away.invSelf (Work.CrauderKatz.BlowUp.thickT 𝕜) ∧ φ (Work.CrauderKatz.BlowUp.thickE 𝕜) = algebraMap _ _ (Work.CrauderKatz.BlowUp.thickE 𝕜) := by
  refine ⟨transHom 𝕜, isOpenImmersion_Spec_transHom 𝕜, ?_, ?_, ?_⟩
  · exact transHom_X 𝕜
  · exact transHom_T 𝕜
  · exact transHom_E 𝕜

end

end Work.CrauderKatz.BlowUp
