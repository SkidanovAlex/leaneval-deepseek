/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Vocabulary for `card_range_dil_conj`

Split case of DS10a: the conjugates of `smulHom a * galHom σ` under the square torus
`dil u = smulHom (u²)` are the elements `smulHom (a · (u / σu)²) * galHom σ`; counting them
reduces to counting the image of the homomorphism

  `phiHom σ : Fˣ →* Fˣ,  u ↦ u * (unitMap σ u)⁻¹  =  u / σu`

whose kernel is the group of units of the fixed field of `σ`.

This file records the basic algebra of `unitMap` and the definition of `phiHom`.
-/
import Mathlib
import Submission.Work.DSTR.M110.SplitCase.Basic

namespace Work.DSTR.M110.SplitCase

open Work.AUTL2 Work.DSTR.M110.SplitAux

variable (F : Type*) [Field F]

section UnitMap

variable (σ : F ≃+* F)

lemma unitMap_mul (u v : Fˣ) :
    unitMap F σ (u * v) = unitMap F σ u * unitMap F σ v := by
  ext; simp [map_mul]

lemma unitMap_one : unitMap F σ 1 = 1 := by ext; simp

lemma unitMap_inv (u : Fˣ) : unitMap F σ u⁻¹ = (unitMap F σ u)⁻¹ := by ext; simp

lemma unitMap_pow (u : Fˣ) (n : ℕ) : unitMap F σ (u ^ n) = (unitMap F σ u) ^ n := by
  ext; simp [map_pow]

end UnitMap

/-- The homomorphism `u ↦ u / σ u` on the units of `F`. -/
noncomputable def phiHom (σ : F ≃+* F) : Fˣ →* Fˣ where
  toFun u := u * (unitMap F σ u)⁻¹
  map_one' := by rw [unitMap_one, inv_one, mul_one]
  map_mul' u v := by rw [unitMap_mul, mul_inv]; ac_rfl

@[simp] lemma phiHom_apply (σ : F ≃+* F) (u : Fˣ) :
    phiHom F σ u = u * (unitMap F σ u)⁻¹ := rfl

end Work.DSTR.M110.SplitCase
