import Mathlib
import Submission.Work.CrauderKatz.BlowUp.LineDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

/-!
# `Work.CrauderKatz.BlowUp.lineTransHom_exists` — the transition map of the thickened blow-up
of `𝔸³` along a coordinate line

This is the exact three-dimensional analogue of `Submission/Work/CrauderKatz/BlowUp/
transHom_exists.lean` (+ `transHom_exists_alg.lean`).  The two charts of the thickened blow-up of
`𝔸³` along the `z`-axis both have ring

`R 𝕜 = 𝕜[x,t,z,ε]/(ε², x·ε)`   (`lineRing 𝕜`, with `x = lineX`, `t = lineT`, `z = lineZ`,
`ε = lineE`),

and their overlap ring is `R 𝕜[1/t] = lineOvRing 𝕜`.  The transition map between the two charts —
in the coordinates of the second chart, `(y, s, z) ↦ (y s, s, z)`, i.e. on the overlap
`y ↦ x·t`, `s ↦ t⁻¹`, `z ↦ z` — is the ring homomorphism

`φ : R 𝕜 →+* R 𝕜[1/t],   x ↦ x·t,   t ↦ t⁻¹,   z ↦ z,   ε ↦ ε`.

As in the two-dimensional case, `φ = σ ∘ L` where `L` is the localization map and `σ` is the
involutive automorphism of `R 𝕜[1/t]` sending `L x ↦ L x · L t`, `L t ↦ (L t)⁻¹`,
`L z ↦ L z`, `L ε ↦ L ε`.  The extra (inert) coordinate `z` is carried along unchanged and plays
no role.
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

/-! ### The substitution `x ↦ x·t`, `t ↦ t⁻¹`, `z ↦ z`, `ε ↦ ε` on the polynomial ring -/

/-- The polynomial substitution `x ↦ x·t`, `t ↦ t⁻¹`, `z ↦ z`, `ε ↦ ε` on
`𝕜[x,t,z,ε] = 𝕜[X0,X1,X2,X3]`, i.e. the map corresponding to the transition between the two
charts of the thickened blow-up (in the direction from the second chart's ring to the first
chart's overlap). -/
def lineTransPoly : MvPolynomial (Fin 4) 𝕜 →+* lineOvRing 𝕜 :=
  MvPolynomial.eval₂Hom (algebraMap 𝕜 (lineOvRing 𝕜)) (fun i : Fin 4 =>
    if i = 0 then
      algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineX 𝕜) *
        algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineT 𝕜)
    else if i = 1 then IsLocalization.Away.invSelf (lineT 𝕜)
    else if i = 2 then algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineZ 𝕜)
    else algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineE 𝕜))

lemma lineTransPoly_X0 : lineTransPoly 𝕜 (MvPolynomial.X 0) =
    algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineX 𝕜) *
      algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineT 𝕜) := by
  simp [lineTransPoly]

lemma lineTransPoly_X1 : lineTransPoly 𝕜 (MvPolynomial.X 1) =
    IsLocalization.Away.invSelf (lineT 𝕜) := by
  simp [lineTransPoly]

lemma lineTransPoly_X2 : lineTransPoly 𝕜 (MvPolynomial.X 2) =
    algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineZ 𝕜) := by
  simp [lineTransPoly]

lemma lineTransPoly_X3 : lineTransPoly 𝕜 (MvPolynomial.X 3) =
    algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineE 𝕜) := by
  simp [lineTransPoly]

lemma lineTransPoly_C (r : 𝕜) :
    lineTransPoly 𝕜 (MvPolynomial.C r) = algebraMap 𝕜 (lineOvRing 𝕜) r := by
  simp [lineTransPoly]

/-- The substitution kills the two relations `ε²` and `x·ε` defining `lineI 𝕜`. -/
lemma mem_lineI_lineTransPoly : lineI 𝕜 ≤ RingHom.ker (lineTransPoly 𝕜) := by
  simp only [lineI]
  rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  constructor
  · change lineTransPoly 𝕜 (MvPolynomial.X 3 ^ 2) = 0
    rw [map_pow, lineTransPoly_X3, ← map_pow, lineE_sq, map_zero]
  · change lineTransPoly 𝕜 (MvPolynomial.X 0 * MvPolynomial.X 3) = 0
    rw [map_mul, lineTransPoly_X0, lineTransPoly_X3, mul_assoc, ← map_mul, ← map_mul]
    rw [show lineX 𝕜 * (lineT 𝕜 * lineE 𝕜) = 0 by
      rw [← mul_assoc, mul_comm (lineX 𝕜), mul_assoc, lineX_mul_lineE, mul_zero], map_zero]

/-! ### The substitution on the chart ring -/

/-- The transition substitution as a ring homomorphism `lineRing 𝕜 →+* lineOvRing 𝕜`, obtained by
descending `lineTransPoly` to the quotient `R 𝕜 = 𝕜[x,t,z,ε]/(ε², x·ε)`. -/
def lineTransSubst : lineRing 𝕜 →+* lineOvRing 𝕜 :=
  Ideal.Quotient.lift (lineI 𝕜) (lineTransPoly 𝕜)
    (fun _a ha => RingHom.mem_ker.mp (mem_lineI_lineTransPoly 𝕜 ha))

lemma lineTransSubst_mk (p : MvPolynomial (Fin 4) 𝕜) :
    lineTransSubst 𝕜 (Ideal.Quotient.mk (lineI 𝕜) p) = lineTransPoly 𝕜 p := by
  change (Ideal.Quotient.lift (lineI 𝕜) (lineTransPoly 𝕜) _)
    (Ideal.Quotient.mk (lineI 𝕜) p) = lineTransPoly 𝕜 p
  rw [Ideal.Quotient.lift_mk]

lemma lineTransSubst_X : lineTransSubst 𝕜 (lineX 𝕜) =
    algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineX 𝕜) *
      algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineT 𝕜) := by
  show lineTransSubst 𝕜 (Ideal.Quotient.mk (lineI 𝕜) (MvPolynomial.X 0)) = _
  rw [lineTransSubst_mk, lineTransPoly_X0]

lemma lineTransSubst_T : lineTransSubst 𝕜 (lineT 𝕜) =
    IsLocalization.Away.invSelf (lineT 𝕜) := by
  show lineTransSubst 𝕜 (Ideal.Quotient.mk (lineI 𝕜) (MvPolynomial.X 1)) = _
  rw [lineTransSubst_mk, lineTransPoly_X1]

lemma lineTransSubst_Z : lineTransSubst 𝕜 (lineZ 𝕜) =
    algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineZ 𝕜) := by
  show lineTransSubst 𝕜 (Ideal.Quotient.mk (lineI 𝕜) (MvPolynomial.X 2)) = _
  rw [lineTransSubst_mk, lineTransPoly_X2]

lemma lineTransSubst_E : lineTransSubst 𝕜 (lineE 𝕜) =
    algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineE 𝕜) := by
  show lineTransSubst 𝕜 (Ideal.Quotient.mk (lineI 𝕜) (MvPolynomial.X 3)) = _
  rw [lineTransSubst_mk, lineTransPoly_X3]

/-- `lineTransSubst (lineT 𝕜) = (lineT 𝕜)⁻¹` is invertible, so the substitution can be lifted
through the localization `R 𝕜 → R 𝕜[1/t]`. -/
lemma hunit_lineTransSubst : IsUnit (lineTransSubst 𝕜 (lineT 𝕜)) := by
  rw [lineTransSubst_T]
  exact isUnit_iff_exists_inv'.mpr ⟨_, IsLocalization.Away.mul_invSelf (lineT 𝕜)⟩

/-- The constants of `𝕜[x,t,z,ε]` map to the constants of `R 𝕜`. -/
lemma lineMk_C_eq_algebraMap (r : 𝕜) :
    Ideal.Quotient.mk (lineI 𝕜) (MvPolynomial.C r) = algebraMap 𝕜 (lineRing 𝕜) r := by
  rw [IsScalarTower.algebraMap_apply 𝕜 (MvPolynomial (Fin 4) 𝕜) (lineRing 𝕜),
    MvPolynomial.algebraMap_eq, Ideal.Quotient.algebraMap_eq]

/-! ### The induced automorphism `σ` of the overlap ring -/

/-- The endomorphism `σ` of the overlap ring `R 𝕜[1/t]` induced by the substitution
`L x ↦ L x · L t`, `L t ↦ (L t)⁻¹`, `L z ↦ L z`, `L ε ↦ L ε`.  It is an involution (see
`lineTransSigma_comp_self`), hence a ring automorphism. -/
def lineTransSigma : lineOvRing 𝕜 →+* lineOvRing 𝕜 :=
  IsLocalization.Away.lift (lineT 𝕜) (g := lineTransSubst 𝕜) (hunit_lineTransSubst 𝕜)

lemma lineTransSigma_algebraMap (y : lineRing 𝕜) :
    lineTransSigma 𝕜 (algebraMap (lineRing 𝕜) (lineOvRing 𝕜) y) =
      lineTransSubst 𝕜 y := by
  unfold lineTransSigma
  rw [IsLocalization.Away.lift_eq]

/-- `σ` sends the images of the generators of `R 𝕜` back to `R 𝕜`: the composite
`σ ∘ (substitution)` is the localization map `L`. -/
lemma lineTransSigma_key : (lineTransSigma 𝕜).comp (lineTransPoly 𝕜) =
    (algebraMap (lineRing 𝕜) (lineOvRing 𝕜)).comp (Ideal.Quotient.mk (lineI 𝕜)) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · rw [RingHom.comp_apply, lineTransPoly_C, RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply 𝕜 (lineRing 𝕜) (lineOvRing 𝕜) r]
    unfold lineTransSigma
    rw [IsLocalization.Away.lift_eq]
    rw [← lineMk_C_eq_algebraMap 𝕜 r]
    rw [lineTransSubst_mk, lineTransPoly_C, lineMk_C_eq_algebraMap 𝕜 r,
      ← IsScalarTower.algebraMap_apply 𝕜 (lineRing 𝕜) (lineOvRing 𝕜) r]
  · rw [RingHom.comp_apply]
    fin_cases i
    · show lineTransSigma 𝕜 (lineTransPoly 𝕜 (MvPolynomial.X 0)) =
        algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (Ideal.Quotient.mk (lineI 𝕜) (MvPolynomial.X 0))
      rw [lineTransPoly_X0]
      unfold lineTransSigma
      rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq, lineTransSubst_X,
        lineTransSubst_T, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
      rfl
    · show lineTransSigma 𝕜 (lineTransPoly 𝕜 (MvPolynomial.X 1)) =
        algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (Ideal.Quotient.mk (lineI 𝕜) (MvPolynomial.X 1))
      rw [lineTransPoly_X1]
      have hσ : lineTransSigma 𝕜 (algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineT 𝕜)) =
          IsLocalization.Away.invSelf (lineT 𝕜) := by
        unfold lineTransSigma
        rw [IsLocalization.Away.lift_eq, lineTransSubst_T]
      have ha : IsLocalization.Away.invSelf (lineT 𝕜) *
          algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineT 𝕜) = 1 := by
        rw [mul_comm]
        exact IsLocalization.Away.mul_invSelf (lineT 𝕜)
      have hσa : IsLocalization.Away.invSelf (lineT 𝕜) *
          lineTransSigma 𝕜 (IsLocalization.Away.invSelf (lineT 𝕜)) = 1 := by
        have h1 : lineTransSigma 𝕜 (algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineT 𝕜) *
            IsLocalization.Away.invSelf (lineT 𝕜)) = 1 := by
          rw [IsLocalization.Away.mul_invSelf, map_one]
        rw [map_mul, hσ] at h1
        exact h1
      calc lineTransSigma 𝕜 (IsLocalization.Away.invSelf (lineT 𝕜))
          = (IsLocalization.Away.invSelf (lineT 𝕜) *
              algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineT 𝕜)) *
              lineTransSigma 𝕜 (IsLocalization.Away.invSelf (lineT 𝕜)) := by rw [ha, one_mul]
        _ = algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineT 𝕜) *
              (IsLocalization.Away.invSelf (lineT 𝕜) *
                lineTransSigma 𝕜 (IsLocalization.Away.invSelf (lineT 𝕜))) := by
              first | refl_ring1 | ring
        _ = algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineT 𝕜) * 1 := by rw [hσa]
        _ = algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineT 𝕜) := mul_one _
    · show lineTransSigma 𝕜 (lineTransPoly 𝕜 (MvPolynomial.X 2)) =
        algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (Ideal.Quotient.mk (lineI 𝕜) (MvPolynomial.X 2))
      rw [lineTransPoly_X2]
      unfold lineTransSigma
      rw [IsLocalization.Away.lift_eq, lineTransSubst_Z]
      rfl
    · show lineTransSigma 𝕜 (lineTransPoly 𝕜 (MvPolynomial.X 3)) =
        algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (Ideal.Quotient.mk (lineI 𝕜) (MvPolynomial.X 3))
      rw [lineTransPoly_X3]
      unfold lineTransSigma
      rw [IsLocalization.Away.lift_eq, lineTransSubst_E]
      rfl

/-- `σ` restricts to the identity of `R 𝕜 ⊂ R 𝕜[1/t]` in the sense that
`σ ∘ lineTransSubst = L`. -/
lemma lineTransSigma_comp_lineTransSubst : (lineTransSigma 𝕜).comp (lineTransSubst 𝕜) =
    algebraMap (lineRing 𝕜) (lineOvRing 𝕜) := by
  apply RingHom.ext
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [RingHom.comp_apply, lineTransSubst_mk]
  simpa using RingHom.congr_fun (lineTransSigma_key 𝕜) p

/-- `σ` is an involution. -/
lemma lineTransSigma_comp_self :
    (lineTransSigma 𝕜).comp (lineTransSigma 𝕜) = RingHom.id (lineOvRing 𝕜) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (lineT 𝕜)) (RingHom.ext (fun a => ?_))
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [lineTransSigma_algebraMap]
  exact RingHom.congr_fun (lineTransSigma_comp_lineTransSubst 𝕜) a

lemma lineTransSigma_invol (x : lineOvRing 𝕜) :
    lineTransSigma 𝕜 (lineTransSigma 𝕜 x) = x := by
  have h := RingHom.congr_fun (lineTransSigma_comp_self 𝕜) x
  simpa [RingHom.comp_apply] using h

/-- `σ` as a ring equivalence (it is its own inverse). -/
def lineTransSigmaEquiv : lineOvRing 𝕜 ≃+* lineOvRing 𝕜 where
  toFun := lineTransSigma 𝕜
  invFun := lineTransSigma 𝕜
  left_inv := lineTransSigma_invol 𝕜
  right_inv := lineTransSigma_invol 𝕜
  map_mul' := (lineTransSigma 𝕜).map_mul
  map_add' := (lineTransSigma 𝕜).map_add

lemma isIso_ofHom_lineTransSigma : IsIso (CommRingCat.ofHom (lineTransSigma 𝕜)) := by
  have h : CommRingCat.ofHom (lineTransSigma 𝕜) =
      (RingEquiv.toCommRingCatIso (lineTransSigmaEquiv 𝕜)).hom := by
    ext x
    rfl
  rw [h]
  infer_instance

lemma isOpenImmersion_Spec_lineTransSigma :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (lineTransSigma 𝕜))) := by
  rw [show CommRingCat.ofHom (lineTransSigma 𝕜) =
      (RingEquiv.toCommRingCatIso (lineTransSigmaEquiv 𝕜)).hom from by
    ext x
    rfl]
  infer_instance

/-! ### The transition homomorphism -/

/-- The transition homomorphism `φ : R 𝕜 →+* R 𝕜[1/t]` with `φ x = x·t`, `φ t = t⁻¹`,
`φ z = z`, `φ ε = ε`. -/
def lineTransHom : lineRing 𝕜 →+* lineOvRing 𝕜 :=
  (lineTransSigma 𝕜).comp (algebraMap (lineRing 𝕜) (lineOvRing 𝕜))

lemma lineTransHom_X : lineTransHom 𝕜 (lineX 𝕜) =
    algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineX 𝕜) *
      algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineT 𝕜) := by
  rw [lineTransHom, RingHom.comp_apply, lineTransSigma_algebraMap, lineTransSubst_X]

lemma lineTransHom_T : lineTransHom 𝕜 (lineT 𝕜) =
    IsLocalization.Away.invSelf (lineT 𝕜) := by
  rw [lineTransHom, RingHom.comp_apply, lineTransSigma_algebraMap, lineTransSubst_T]

lemma lineTransHom_Z : lineTransHom 𝕜 (lineZ 𝕜) =
    algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineZ 𝕜) := by
  rw [lineTransHom, RingHom.comp_apply, lineTransSigma_algebraMap, lineTransSubst_Z]

lemma lineTransHom_E : lineTransHom 𝕜 (lineE 𝕜) =
    algebraMap (lineRing 𝕜) (lineOvRing 𝕜) (lineE 𝕜) := by
  rw [lineTransHom, RingHom.comp_apply, lineTransSigma_algebraMap, lineTransSubst_E]

/-- The transition map `Spec R 𝕜[1/t] → Spec R 𝕜` is an open immersion: it is the composite of
the localization open immersion with the automorphism `σ` of the source. -/
lemma isOpenImmersion_Spec_lineTransHom :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (lineTransHom 𝕜))) := by
  rw [lineTransHom, CommRingCat.ofHom_comp, Spec.map_comp]
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (lineTransSigma 𝕜))) :=
    isOpenImmersion_Spec_lineTransSigma 𝕜
  infer_instance

lemma lineTransSubst_algebraMap (c : 𝕜) :
    lineTransSubst 𝕜 (algebraMap 𝕜 (lineRing 𝕜) c) = algebraMap 𝕜 (lineOvRing 𝕜) c := by
  rw [← lineMk_C_eq_algebraMap 𝕜 c, lineTransSubst_mk, lineTransPoly_C]

/-- The automorphism `lineTransSigma` of the overlap ring fixes the constants. -/
lemma lineTransSigma_algebraMap_const (c : 𝕜) :
    lineTransSigma 𝕜 (algebraMap 𝕜 (lineOvRing 𝕜) c) = algebraMap 𝕜 (lineOvRing 𝕜) c := by
  conv_lhs => rw [IsScalarTower.algebraMap_apply 𝕜 (lineRing 𝕜) (lineOvRing 𝕜) c]
  rw [lineTransSigma_algebraMap 𝕜]
  exact lineTransSubst_algebraMap 𝕜 c

/-- The transition homomorphism `lineTransHom` is `𝕜`-linear. -/
lemma lineTransHom_algebraMap (c : 𝕜) :
    lineTransHom 𝕜 (algebraMap 𝕜 (lineRing 𝕜) c) = algebraMap 𝕜 (lineOvRing 𝕜) c := by
  rw [lineTransHom, RingHom.comp_apply,
    ← IsScalarTower.algebraMap_apply 𝕜 (lineRing 𝕜) (lineOvRing 𝕜) c]
  exact lineTransSigma_algebraMap_const 𝕜 c

end

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme in
theorem lineTransHom_exists (𝕜 : Type) [Field 𝕜] :
    ∃ φ : lineRing 𝕜 →+* lineOvRing 𝕜,
      IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) ∧
      φ (lineX 𝕜) = algebraMap _ _ (lineX 𝕜) * algebraMap _ _ (lineT 𝕜) ∧
      φ (lineT 𝕜) = IsLocalization.Away.invSelf (lineT 𝕜) ∧
      φ (lineZ 𝕜) = algebraMap _ _ (lineZ 𝕜) ∧
      φ (lineE 𝕜) = algebraMap _ _ (lineE 𝕜) ∧
      (∀ c : 𝕜, φ (algebraMap 𝕜 (lineRing 𝕜) c) = algebraMap 𝕜 (lineOvRing 𝕜) c) := by
  exact ⟨lineTransHom 𝕜, isOpenImmersion_Spec_lineTransHom 𝕜, lineTransHom_X 𝕜,
    lineTransHom_T 𝕜, lineTransHom_Z 𝕜, lineTransHom_E 𝕜,
    lineTransHom_algebraMap 𝕜⟩

end Work.CrauderKatz.BlowUp
