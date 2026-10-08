/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 / Normalizer : the translation subgroup and the diagonal scalar

Vocabulary for the computation `N_{Sym(ℙ¹(F))}(PSL(2,F)) = PΓL(2,F)`:

* `Work.AUTL2.Normalizer.translHom`, `translSub`: the group `U = {x ↦ x + b} ≅ (F,+)`;
* `Work.AUTL2.Normalizer.smulPerm`: the permutation `x ↦ c·x` (`∞ ↦ ∞`), which lies in
  `pglImage F` (it is the image of the diagonal matrix `diag(c,1) ∈ GL(2,F)`).
-/
import Mathlib
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.Mobius
import Submission.Work.AUTL2.Stabilizer

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.AUTL2.Normalizer

variable (F : Type*) [Field F] [DecidableEq F]

/-! ## The translation subgroup `U` -/

/-- The translations, as a homomorphism `(F,+) →* Perm ℙ¹(F)`. -/
noncomputable def translHom : Multiplicative F →* Equiv.Perm (P1 F) where
  toFun b := transl F (Multiplicative.toAdd b)
  map_one' := transl_zero F
  map_mul' a b := by rw [toAdd_mul, transl_mul, add_comm]

/-- `U = {x ↦ x + b} ≤ Perm ℙ¹(F)`, a subgroup isomorphic to `(F,+)`. -/
noncomputable def translSub : Subgroup (Equiv.Perm (P1 F)) := (translHom F).range

lemma transl_mem_translSub (b : F) : transl F b ∈ translSub F :=
  ⟨Multiplicative.ofAdd b, rfl⟩

lemma mem_translSub_iff {g : Equiv.Perm (P1 F)} :
    g ∈ translSub F ↔ ∃ b : F, transl F b = g := MonoidHom.mem_range

lemma transl_injective : Function.Injective (transl F) := by
  intro a b hab
  have h := congrFun (congrArg DFunLike.coe hab) ((0 : F) : P1 F)
  rw [transl_formula, transl_formula] at h
  exact OnePoint.coe_eq_coe.mp (by simpa using h)

lemma transl_eq_iff (a b : F) : transl F a = transl F b ↔ a = b :=
  ⟨fun h => transl_injective F h, fun h => by rw [h]⟩

lemma transl_add (a b : F) : transl F a * transl F b = transl F (a + b) := by
  rw [transl_mul, add_comm]

lemma translSub_le_pslImage : translSub F ≤ pslImage F := by
  rintro g ⟨b, rfl⟩
  exact transl_mem F _

lemma mem_translSub_fixes_infty {g : Equiv.Perm (P1 F)} (hg : g ∈ translSub F) :
    g (∞ : P1 F) = ∞ := by
  obtain ⟨b, rfl⟩ := (mem_translSub_iff F).mp hg
  exact transl_infty F b

lemma mem_translSub_apply {g : Equiv.Perm (P1 F)} (hg : g ∈ translSub F) :
    ∃ b : F, ∀ x : F, g (x : P1 F) = ((x + b : F) : P1 F) := by
  obtain ⟨b, rfl⟩ := (mem_translSub_iff F).mp hg
  exact ⟨b, fun x => transl_formula F b x⟩

/-- An element of the normalizer of `pslImage F` conjugates `pslImage F` to itself. -/
lemma conj_mem_pslImage {π g : Equiv.Perm (P1 F)}
    (hπ : π ∈ Subgroup.normalizer (pslImage F : Set _)) (hg : g ∈ pslImage F) :
    π * g * π⁻¹ ∈ pslImage F :=
  (Subgroup.mem_normalizer_iff.mp hπ g).mp hg

/-! ## The scalar `x ↦ c·x` as an element of `PGL(2,F)` -/

/-- The diagonal matrix `diag(c,1)` as an element of `GL(2,F)`. -/
noncomputable def diagGL (c : F) (hc : c ≠ 0) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![c, 0; 0, 1]
    (by rw [Matrix.det_fin_two]; simpa using hc)

/-- The element `x ↦ c·x`, `∞ ↦ ∞` of `PGL(2,F)`, as a permutation of `ℙ¹(F)`. -/
noncomputable def smulPerm (c : F) (hc : c ≠ 0) : Equiv.Perm (P1 F) :=
  pglHom F (Matrix.ProjGenLinGroup.mk (diagGL F c hc))

lemma smulPerm_some (c : F) (hc : c ≠ 0) (x : F) :
    smulPerm F c hc (x : P1 F) = ((c * x : F) : P1 F) := by
  rw [smulPerm, pglHom, MulAction.toPermHom_apply, MulAction.toPerm_apply,
    Matrix.ProjGenLinGroup.mk_smul, OnePoint.smul_some_eq_ite]
  simp only [diagGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  simp [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.of_apply]

lemma smulPerm_infty (c : F) (hc : c ≠ 0) :
    smulPerm F c hc (∞ : P1 F) = ∞ := by
  rw [smulPerm, pglHom, MulAction.toPermHom_apply, MulAction.toPerm_apply,
    Matrix.ProjGenLinGroup.mk_smul, OnePoint.smul_infty_eq_ite]
  simp only [diagGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  simp [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.of_apply]

lemma smulPerm_mem_pglImage (c : F) (hc : c ≠ 0) : smulPerm F c hc ∈ pglImage F :=
  ⟨_, rfl⟩

@[simp] lemma galHom_apply_coe (σ : F ≃+* F) (x : F) :
    galHom F σ (x : P1 F) = (σ x : P1 F) := rfl

@[simp] lemma galHom_apply_infty (σ : F ≃+* F) :
    galHom F σ (∞ : P1 F) = ∞ := rfl

end Work.AUTL2.Normalizer
