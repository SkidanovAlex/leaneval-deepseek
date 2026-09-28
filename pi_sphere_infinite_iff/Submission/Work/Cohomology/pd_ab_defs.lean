import Mathlib
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.exists_relComplexMap

/-!
# The "A+B" cochain complex of two relative cochain complexes

For a space `X` and subsets `A, B ⊆ X`, Hatcher's `A+B` complex `C^*(X, A+B)` is the module of
cochains on `X` vanishing both on chains in `A` and on chains in `B`; equivalently it is the
intersection of the relative cochain complexes `C^*(X,A)` and `C^*(X,B)` inside the absolute
cochain complex `C^*(X)`.

This file defines that complex (`pdABCoh X A B`), its two inclusions
`pdABInclA`/`pdABInclB` into the relative complexes and the two maps of the short exact sequence

`0 ⟶ C^*(X, A+B) ⟶ C^*(X,A) ⊞ C^*(X,B) ⟶ C^*(X, A∩B) ⟶ 0`,

namely the diagonal `pdABDiag` and the difference `pdBiprodToInter`.

The short exactness of that sequence (the "A+B" short exact sequence, the algebraic content of
Hatcher's Lemma 3.36) is delegated separately.

## Main definitions

* `pdABKern`, `pdABDiff`, `pdABCoh` — the complex `C^*(X, A+B)`;
* `pdABInclA`, `pdABInclB`, `pdABDiag` — the inclusion into `C^*(X,A) ⊞ C^*(X,B)`;
* `pdToInterA`, `pdToInterB`, `pdBiprodToInter` — the difference map onto `C^*(X, A∩B)`.
-/

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable (X : TopCat) (A B : Set X)

/-! ## The differential preserves the intersection of the relative kernels -/

/-- The differential of the absolute complex preserves the relative kernels: the coboundary of a
cochain vanishing on `A` vanishes on `A`. -/
theorem relKern_d_mem (n : ℕ) (y : (singularCochainComplex ℤ X).X n)
    (hy : y ∈ relKern ℤ X A n) :
    ((singularCochainComplex ℤ X).d n (n+1)).hom y ∈ relKern ℤ X A (n+1) := by
  rw [relKern, LinearMap.mem_ker] at hy ⊢
  have hc := congrArg ModuleCat.Hom.hom ((restr ℤ X A).comm n (n+1))
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hc
  have hcx := LinearMap.congr_fun hc y
  simp only [LinearMap.comp_apply] at hcx
  simp only [hy, map_zero] at hcx
  exact hcx.symm

/-! ## The A+B complex -/

/-- The degree-`n` part of the `A+B` complex: the intersection of the two relative kernels. -/
abbrev pdABKern (n : ℕ) : Submodule ℤ ((singularCochainComplex ℤ X).X n) :=
  relKern ℤ X A n ⊓ relKern ℤ X B n

theorem pdABKern_mem_iff (n : ℕ) (f : (singularCochainComplex ℤ X).X n) :
    f ∈ pdABKern X A B n ↔ f ∈ relKern ℤ X A n ∧ f ∈ relKern ℤ X B n :=
  Submodule.mem_inf

/-- The differential of the `A+B` complex. -/
def pdABDiffLM (n : ℕ) : (pdABKern X A B n) →ₗ[ℤ] (pdABKern X A B (n+1)) :=
  (((singularCochainComplex ℤ X).d n (n+1)).hom.comp
      (Submodule.subtype (pdABKern X A B n))).codRestrict (pdABKern X A B (n+1))
    (fun x => Submodule.mem_inf.mpr
      ⟨relKern_d_mem X A n x.1 (Submodule.mem_inf.mp x.2).1,
       relKern_d_mem X B n x.1 (Submodule.mem_inf.mp x.2).2⟩)

/-- The underlying cochain of the differential of the `A+B` complex. -/
@[simp] theorem pdABDiffLM_coe (n : ℕ) (x : pdABKern X A B n) :
    (pdABDiffLM X A B n x).1 = ((singularCochainComplex ℤ X).d n (n+1)).hom x.1 := rfl

/-- The differential of the `A+B` complex, as a morphism of modules. -/
def pdABDiff (n : ℕ) :
    ModuleCat.of ℤ (pdABKern X A B n) ⟶ ModuleCat.of ℤ (pdABKern X A B (n+1)) :=
  ModuleCat.ofHom (pdABDiffLM X A B n)

/-- **The `A+B` cochain complex** `C^*(X, A+B) = C^*(X,A) ∩ C^*(X,B)`. -/
def pdABCoh : CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℤ (pdABKern X A B n)) (fun n => pdABDiff X A B n)
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
        Submodule.coe_zero]
      show ((pdABDiffLM X A B (n+1)) ((pdABDiffLM X A B n) x)).1 = 0
      rw [pdABDiffLM_coe, pdABDiffLM_coe]
      have h := congrArg ModuleCat.Hom.hom
        (HomologicalComplex.d_comp_d (singularCochainComplex ℤ X) n (n+1) (n+2))
      rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
      have h2 := LinearMap.congr_fun h x.1
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h2
      exact h2)

/-- The differential of the `A+B` complex is `pdABDiff`. -/
@[simp] theorem pdABCoh_d (n : ℕ) : (pdABCoh X A B).d n (n+1) = pdABDiff X A B n :=
  CochainComplex.of_d (fun n => ModuleCat.of ℤ (pdABKern X A B n)) (fun n => pdABDiff X A B n) n

/-- The underlying element of the differential of the `A+B` complex, at the level of the absolute
cochains. -/
theorem pdABCoh_d_coe (n : ℕ) (x : (pdABCoh X A B).X n) :
    (((pdABCoh X A B).d n (n+1)).hom x).1 =
      ((singularCochainComplex ℤ X).d n (n+1)).hom x.1 := by
  rw [pdABCoh_d]
  rfl

/-! ## The inclusion into the two relative complexes -/

/-- The inclusion `C^*(X,A) ∩ C^*(X,B) ⟶ C^*(X,A)`. -/
def pdABInclA : pdABCoh X A B ⟶ relComplex ℤ X A :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (Submodule.inclusion inf_le_left))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [relComplex_d, pdABCoh_d]
      rfl)

/-- The inclusion `C^*(X,A) ∩ C^*(X,B) ⟶ C^*(X,B)`. -/
def pdABInclB : pdABCoh X A B ⟶ relComplex ℤ X B :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (Submodule.inclusion inf_le_right))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [relComplex_d, pdABCoh_d]
      rfl)

/-- The diagonal `C^*(X,A) ∩ C^*(X,B) ⟶ C^*(X,A) ⊞ C^*(X,B)`. -/
def pdABDiag : pdABCoh X A B ⟶ relComplex ℤ X A ⊞ relComplex ℤ X B :=
  biprod.lift (pdABInclA X A B) (pdABInclB X A B)

/-! ## The map onto the intersection -/

/-- The restriction `C^*(X,A) ⟶ C^*(X, A∩B)`, induced by `A ∩ B ⊆ A`. -/
def pdToInterA : relComplex ℤ X A ⟶ relComplex ℤ X (A ∩ B) :=
  relComplexMap ℤ (X₁ := X) (X₂ := X) (A ∩ B) A (𝟙 X) (fun x hx => hx.1)

/-- The restriction `C^*(X,B) ⟶ C^*(X, A∩B)`, induced by `A ∩ B ⊆ B`. -/
def pdToInterB : relComplex ℤ X B ⟶ relComplex ℤ X (A ∩ B) :=
  relComplexMap ℤ (X₁ := X) (X₂ := X) (A ∩ B) B (𝟙 X) (fun x hx => hx.2)

/-- The difference map `C^*(X,A) ⊞ C^*(X,B) ⟶ C^*(X, A∩B)`. -/
def pdBiprodToInter : relComplex ℤ X A ⊞ relComplex ℤ X B ⟶ relComplex ℤ X (A ∩ B) :=
  biprod.desc (pdToInterA X A B) (-(pdToInterB X A B))

/-! ## The two maps agree on the intersection -/

/-- The two restrictions `C^*(X,A) ∩ C^*(X,B) → C^*(X,A∩B)` (via `A` and via `B`) coincide. -/
theorem pdABInclA_comp_pdToInterA :
    pdABInclA X A B ≫ pdToInterA X A B = pdABInclB X A B ≫ pdToInterB X A B := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- The composite of the diagonal with the difference map is zero. -/
theorem pdABDiag_comp_pdBiprodToInter :
    pdABDiag X A B ≫ pdBiprodToInter X A B = 0 := by
  rw [pdABDiag, pdBiprodToInter, biprod.lift_desc, pdABInclA_comp_pdToInterA,
    Preadditive.comp_neg, add_neg_cancel]

/-- The short complex of the `A+B` sequence. -/
abbrev pdABShort : ShortComplex (CochainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (pdABDiag X A B) (pdBiprodToInter X A B) (pdABDiag_comp_pdBiprodToInter X A B)

end

end Work.Cohomology
