/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The torus `T = {x ↦ a·x}`, the Weyl element and the field automorphisms

Conjugation computations for the split case of DS10a:

* `galHom_conj_smulHom`: `galHom σ` acts on the diagonal torus by `a ↦ σ a`;
* `galHom_mul_weylEl`: `galHom σ` commutes with the Weyl element `x ↦ -1/x`;
* `weylEl_conj_smulHom`: `weylEl` inverts the diagonal torus.
-/
import Mathlib
import Submission.Work.DSTR.M110.SplitCase.GaloisPart

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.DSTR.M110.SplitAux

open Work.AUTL2

variable (F : Type*) [Field F] [DecidableEq F]

/-- `galHom σ` conjugates the diagonal torus to itself, acting on the diagonal entries by `σ`. -/
theorem galHom_conj_smulHom (σ : F ≃+* F) (a : Fˣ) :
    galHom F σ * smulHom F a * (galHom F σ)⁻¹ = smulHom F (unitMap F σ a) := by
  have hinv : (galHom F σ)⁻¹ = galHom F σ.symm := by
    rw [← map_inv]; rfl
  rw [Equiv.ext_iff, OnePoint.forall, hinv]
  refine ⟨?_, fun x => ?_⟩
  · simp only [Equiv.Perm.mul_apply, smulHom_apply_infty, Normalizer.galHom_apply_infty]
  · simp only [Equiv.Perm.mul_apply, smulHom_apply_some, Normalizer.galHom_apply_coe,
      Normalizer.galHom_apply_coe, unitMap_coe, map_mul]
    congr 1
    rw [RingEquiv.apply_symm_apply]

/-- `galHom σ` commutes with the Weyl element `x ↦ -1/x`. -/
theorem galHom_mul_weylEl (σ : F ≃+* F) :
    galHom F σ * weylEl F = weylEl F * galHom F σ := by
  rw [Equiv.ext_iff, OnePoint.forall]
  refine ⟨?_, fun x => ?_⟩
  · simp only [Equiv.Perm.mul_apply, weyl_infty, weyl_zero, Normalizer.galHom_apply_coe,
      Normalizer.galHom_apply_infty, map_zero]
  · rcases eq_or_ne x 0 with rfl | hx
    · simp only [Equiv.Perm.mul_apply, weyl_zero, weyl_infty, Normalizer.galHom_apply_infty,
        Normalizer.galHom_apply_coe, map_zero]
    · have hσx : σ x ≠ 0 := by rw [← map_zero σ]; exact σ.injective.ne hx
      simp only [Equiv.Perm.mul_apply, weyl_formula F x hx, Normalizer.galHom_apply_coe,
        weyl_formula F (σ x) hσx]
      rw [map_neg, map_inv₀]

/-- The Weyl element inverts the diagonal torus. -/
theorem weylEl_conj_smulHom (a : Fˣ) :
    weylEl F * smulHom F a * weylEl F = smulHom F a⁻¹ := by
  rw [Equiv.ext_iff, OnePoint.forall]
  refine ⟨?_, fun x => ?_⟩
  · simp only [Equiv.Perm.mul_apply, weyl_infty, weyl_zero, smulHom_apply_some, smulHom_apply_infty,
      mul_zero]
  · rcases eq_or_ne x 0 with rfl | hx
    · simp only [Equiv.Perm.mul_apply, weyl_zero, weyl_infty, smulHom_apply_infty,
        smulHom_apply_some, mul_zero]
    · have hx' : (-x⁻¹ : F) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hx)
      have h2' : ((a : F) * -x⁻¹) ≠ 0 := mul_ne_zero (Units.ne_zero a) hx'
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, weyl_formula F x hx, smulHom_apply_some,
        weyl_formula F ((a : F) * -x⁻¹) h2', smulHom_apply_some, Units.val_inv_eq_inv_val]
      congr 1
      have ha : (a : F) ≠ 0 := Units.ne_zero a
      field_simp

/-- The Weyl element inverts the diagonal torus (conjugation form). -/
theorem weylEl_conj_mem_torSub (a : Fˣ) : weylEl F * smulHom F a * weylEl F ∈ torSub F :=
  ⟨a⁻¹, (weylEl_conj_smulHom F a).symm⟩

/-- `galHom σ` maps `torSub` to itself under conjugation. -/
theorem galHom_conj_mem_torSub (σ : F ≃+* F) {c : Equiv.Perm (P1 F)} (hc : c ∈ torSub F) :
    galHom F σ * c * (galHom F σ)⁻¹ ∈ torSub F := by
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hc
  exact ⟨unitMap F σ a, (galHom_conj_smulHom F σ a).symm⟩

/-- `galHom σ` preserves the coset `weylEl · torSub` under conjugation. -/
theorem galHom_conj_weyl_mem (σ : F ≃+* F) {c : Equiv.Perm (P1 F)}
    (hc : weylEl F * c ∈ torSub F) :
    weylEl F * (galHom F σ * c * (galHom F σ)⁻¹) ∈ torSub F := by
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hc
  have hc' : c = weylEl F * smulHom F a := by rw [ha, ← mul_assoc, weyl_self, one_mul]
  rw [hc']
  have hcomm : weylEl F * galHom F σ = galHom F σ * weylEl F := (galHom_mul_weylEl F σ).symm
  have hgoal : weylEl F * (galHom F σ * (weylEl F * smulHom F a) * (galHom F σ)⁻¹)
      = galHom F σ * smulHom F a * (galHom F σ)⁻¹ := by
    rw [show weylEl F * (galHom F σ * (weylEl F * smulHom F a) * (galHom F σ)⁻¹)
        = (weylEl F * galHom F σ) * weylEl F * smulHom F a * (galHom F σ)⁻¹ by group]
    rw [hcomm]
    rw [show (galHom F σ * weylEl F) * weylEl F * smulHom F a * (galHom F σ)⁻¹
        = galHom F σ * (weylEl F * weylEl F) * smulHom F a * (galHom F σ)⁻¹ by group]
    rw [weyl_self, mul_one]
  rw [hgoal]
  exact ⟨unitMap F σ a, (galHom_conj_smulHom F σ a).symm⟩

end Work.DSTR.M110.SplitAux
