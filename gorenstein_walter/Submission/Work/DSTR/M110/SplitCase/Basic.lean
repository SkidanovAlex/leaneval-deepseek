/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Auxiliary definitions for the split case of DS10a (`F_{2'}(C(t)) ≤ PSL(2,q)`)

Vocabulary used by `Submission/Work/DSTR/M110/splitCase.lean`:

* `negPerm F`   : the standard split involution `x ↦ -x` of `ℙ¹(F)`, an element of `pglImage F`;
* `smulHom F`   : the diagonal torus `Fˣ → Sym(ℙ¹(F))`, `a ↦ (x ↦ a·x)` (a `PGL`-subgroup);
* `torSub F`    : its image `T`, of order `|F| - 1`;
* `dilHom F`    : the *square* torus `a ↦ (x ↦ a²·x)`, whose image `dilSub F` lies in `pslImage F`
  and hence in every `Q ≥ pslImage F`.
-/
import Mathlib
import Submission.Work.DSTR.M110.All
import Submission.Work.DSTR.M110.Normalizer.Defs

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.DSTR.M110.SplitAux

open Work.AUTL2

variable (F : Type*) [Field F] [DecidableEq F]

/-! ## The standard split involution `x ↦ -x` -/

/-- The standard split involution `x ↦ -x` of `ℙ¹(F)`. -/
noncomputable def negPerm : Equiv.Perm (P1 F) :=
  Normalizer.smulPerm F (-1) (neg_ne_zero.mpr one_ne_zero)

@[simp] lemma negPerm_some (x : F) : negPerm F (x : P1 F) = ((-x : F) : P1 F) := by
  rw [negPerm, Normalizer.smulPerm_some, neg_one_mul]

@[simp] lemma negPerm_infty : negPerm F (∞ : P1 F) = ∞ := by
  rw [negPerm, Normalizer.smulPerm_infty]

lemma negPerm_mem_pglImage : negPerm F ∈ pglImage F :=
  Normalizer.smulPerm_mem_pglImage F (-1) _

lemma negPerm_mem_pgammaL : negPerm F ∈ pgammaL F :=
  (le_sup_left : pglImage F ≤ pgammaL F) (negPerm_mem_pglImage F)

lemma negPerm_involutive : negPerm F * negPerm F = 1 := by
  rw [Equiv.ext_iff, OnePoint.forall]
  refine ⟨?_, fun x => ?_⟩
  · rw [Equiv.Perm.mul_apply, negPerm_infty, negPerm_infty, Equiv.Perm.one_apply]
  · rw [Equiv.Perm.mul_apply, negPerm_some, negPerm_some, neg_neg, Equiv.Perm.one_apply]

/-- `-1 ≠ 1` in a field of characteristic `≠ 2`. -/
lemma neg_one_ne_one (h2 : (2 : F) ≠ 0) : (-1 : F) ≠ 1 := by
  intro h
  apply h2
  have h1 : (1 : F) + 1 = 0 := (neg_eq_iff_add_eq_zero).mp h
  rw [← one_add_one_eq_two]; exact h1

lemma orderOf_negPerm (h2 : (2 : F) ≠ 0) : orderOf (negPerm F) = 2 := by
  have hpow : negPerm F ^ 2 = (1 : Equiv.Perm (P1 F)) := by
    rw [pow_two, negPerm_involutive]
  refine orderOf_eq_prime hpow ?_
  intro h
  have h1 := congrFun (congrArg DFunLike.coe h) ((1 : F) : P1 F)
  rw [negPerm_some, Equiv.Perm.one_apply] at h1
  exact neg_one_ne_one F h2 (OnePoint.coe_eq_coe.mp h1)

/-! ## The diagonal torus `T = { x ↦ a·x }` -/

/-- The diagonal torus `Fˣ →* Sym(ℙ¹(F))`. -/
noncomputable def smulHom : Fˣ →* Equiv.Perm (P1 F) where
  toFun a := Normalizer.smulPerm F (a : F) (Units.ne_zero a)
  map_one' := by
    rw [Equiv.ext_iff, OnePoint.forall]
    refine ⟨?_, fun x => ?_⟩
    · rw [Normalizer.smulPerm_infty, Equiv.Perm.one_apply]
    · rw [Normalizer.smulPerm_some, Units.val_one, one_mul, Equiv.Perm.one_apply]
  map_mul' a b := by
    rw [Equiv.ext_iff, OnePoint.forall]
    refine ⟨?_, fun x => ?_⟩
    · rw [Equiv.Perm.mul_apply, Normalizer.smulPerm_infty, Normalizer.smulPerm_infty,
        Normalizer.smulPerm_infty]
    · rw [Equiv.Perm.mul_apply, Normalizer.smulPerm_some, Normalizer.smulPerm_some,
        Normalizer.smulPerm_some, Units.val_mul]
      congr 1
      ring

/-- The diagonal torus `T ≤ PGL(2,F)`. -/
noncomputable def torSub : Subgroup (Equiv.Perm (P1 F)) := (smulHom F).range

/-- The action of a field automorphism on `Fˣ`. -/
noncomputable def unitMap (σ : F ≃+* F) (a : Fˣ) : Fˣ :=
  Units.mk0 (σ (a : F)) (by simpa using σ.injective.ne a.ne_zero)

@[simp] lemma unitMap_coe (σ : F ≃+* F) (a : Fˣ) : (unitMap F σ a : F) = σ (a : F) := rfl

lemma smulHom_apply_some (a : Fˣ) (x : F) :
    smulHom F a (x : P1 F) = (((a : F) * x : F) : P1 F) :=
  Normalizer.smulPerm_some F (a : F) (Units.ne_zero a) x

lemma smulHom_apply_infty (a : Fˣ) : smulHom F a (∞ : P1 F) = ∞ :=
  Normalizer.smulPerm_infty F (a : F) (Units.ne_zero a)

lemma torSub_le_pglImage : torSub F ≤ pglImage F := by
  rintro g ⟨a, rfl⟩
  exact Normalizer.smulPerm_mem_pglImage F (a : F) (Units.ne_zero a)

lemma smulHom_injective : Function.Injective (smulHom F) := by
  intro a b h
  have h1 := congrFun (congrArg DFunLike.coe h) ((1 : F) : P1 F)
  rw [smulHom_apply_some, smulHom_apply_some, mul_one, mul_one] at h1
  exact Units.ext (OnePoint.coe_eq_coe.mp h1)

lemma card_torSub [Fintype F] : Nat.card (torSub F) = Fintype.card F - 1 := by
  have h1 : Nat.card (torSub F) = Nat.card Fˣ :=
    Nat.card_congr (MonoidHom.ofInjective (smulHom_injective F)).toEquiv.symm
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_units]

lemma torSub_comm (g h : ↥(torSub F)) : g * h = h * g := by
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp g.2
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp h.2
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul, mul_comm]

/-! ## The square torus `dilSub = T²  ⊆ PSL` -/

/-- The square torus `Fˣ →* Sym(ℙ¹(F))`, `a ↦ (x ↦ a²·x)`. -/
noncomputable def dilHom : Fˣ →* Equiv.Perm (P1 F) where
  toFun a := dil F a
  map_one' := by
    rw [Equiv.ext_iff, OnePoint.forall]
    refine ⟨?_, fun x => ?_⟩
    · rw [dil_infty, Equiv.Perm.one_apply]
    · rw [dil_formula, Units.val_one, one_pow, one_mul, Equiv.Perm.one_apply]
  map_mul' a b := by
    rw [← (dil_facts F).2.2.1 a b]

/-- The square torus `T² ≤ PSL(2,F)`. -/
noncomputable def dilSub : Subgroup (Equiv.Perm (P1 F)) := (dilHom F).range

lemma dilSub_le_pslImage : dilSub F ≤ pslImage F := by
  rintro g ⟨a, rfl⟩
  exact dil_mem F a

lemma dil_eq_smul (a : Fˣ) :
    dilHom F a = smulHom F (a ^ 2) := by
  rw [Equiv.ext_iff, OnePoint.forall]
  refine ⟨?_, fun x => ?_⟩
  · show dil F a ∞ = smulHom F (a ^ 2) ∞
    rw [dil_infty, smulHom_apply_infty]
  · show dil F a (x : P1 F) = smulHom F (a ^ 2) (x : P1 F)
    rw [dil_formula, smulHom_apply_some, Units.val_pow_eq_pow_val]


end Work.DSTR.M110.SplitAux
