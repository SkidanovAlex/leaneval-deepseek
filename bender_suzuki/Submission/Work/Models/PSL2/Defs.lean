import Submission.Blueprint.Interfaces

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Models.PSL2.Defs` — the SL(2) model

Concrete data for `PSL(2,2ⁿ)`, realised as `SL(2,F)` for `F` a field of characteristic 2
(the centre of `SL(2,F)` is trivial in characteristic 2, so `PSL(2,F) ≅ SL(2,F)`;
the isomorphism is `Work.Models.PSL2.pslEquiv`).

* `unip b : SL2 F` — the unipotent matrix `1 + b E₀₁`;
* `U : Subgroup (SL2 F)` — the unipotent radical of the standard Borel (order `q`);
* `D : Subgroup (SL2 F)` — the standard split torus (diagonal matrices, order `q-1`);
* `B : Subgroup (SL2 F)` — the standard Borel: the upper triangular matrices;
* `w : SL2 F` — the Weyl element `!![0,1;1,0]`.
-/

namespace Work.Models

open Matrix

/-- `SL(2,F)`. -/
abbrev SL2 (F : Type*) [Field F] : Type _ := Matrix.SpecialLinearGroup (Fin 2) F

namespace PSL2

variable {F : Type*} [Field F] [CharP F 2]

/-- The unipotent matrix `1 + b E₀₁` (upper unitriangular). -/
def unip (b : F) : SL2 F :=
  Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) b

lemma unip_zero : unip (0 : F) = 1 :=
  Matrix.SpecialLinearGroup.transvection_coeff_zero (i := (0 : Fin 2)) (j := 1) _

lemma unip_add (a b : F) : unip (a + b) = unip a * unip b :=
  Matrix.SpecialLinearGroup.transvection_add _ a b

lemma unip_mul_self (b : F) : unip b * unip b = 1 := by
  rw [← unip_add]
  have : b + b = 0 := CharTwo.add_self_eq_zero b
  rw [this, unip_zero]

/-- The unipotent radical of the standard Borel: `U = {1 + b E₀₁ | b : F}`, isomorphic to
the additive group of `F` (and of order `q = |F|`). -/
def U : Subgroup (SL2 F) where
  carrier := {A | ∃ b : F, A = unip b}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, (unip_add a b).symm⟩
  one_mem' := ⟨0, unip_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, (eq_inv_iff_mul_eq_one.mpr (unip_mul_self a)).symm⟩

@[simp] lemma mem_U_iff {A : SL2 F} : A ∈ U ↔ ∃ b : F, A = unip b := Iff.rfl

/-- `A` is upper triangular. -/
def inB (A : SL2 F) : Prop := (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0

/-- `A` is diagonal. -/
def inD (A : SL2 F) : Prop :=
  (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧ (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0

lemma inB_one : inB (1 : SL2 F) := by
  simp only [inB, Matrix.SpecialLinearGroup.coe_one]
  exact Matrix.one_apply_ne (by decide)

lemma inB_mul {A B : SL2 F} (hA : inB A) (hB : inB B) : inB (A * B) := by
  simp only [inB, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at hA hB ⊢
  simp [hA, hB]

lemma inB_inv {A : SL2 F} (hA : inB A) : inB A⁻¹ := by
  simp only [inB, Matrix.SpecialLinearGroup.SL2_inv_expl] at hA ⊢
  simpa using hA

lemma inD_one : inD (1 : SL2 F) := by
  refine ⟨?_, ?_⟩
  · simp only [Matrix.SpecialLinearGroup.coe_one]
    exact Matrix.one_apply_ne (by decide)
  · simp only [Matrix.SpecialLinearGroup.coe_one]
    exact Matrix.one_apply_ne (by decide)

lemma inD_mul {A B : SL2 F} (hA : inD A) (hB : inD B) : inD (A * B) := by
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  constructor
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp [hA1, hB1]
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp [hA2, hB2]

lemma inD_inv {A : SL2 F} (hA : inD A) : inD A⁻¹ := by
  obtain ⟨hA1, hA2⟩ := hA
  constructor
  · simp only [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simpa using hA1
  · simp only [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simpa using hA2

lemma inD_le_inB {A : SL2 F} (hA : inD A) : inB A := hA.2

/-- The standard split torus `D`: the diagonal matrices of `SL(2,F)` (cyclic of order
`q - 1`). -/
def D : Subgroup (SL2 F) where
  carrier := {A : SL2 F | inD A}
  mul_mem' := fun hA hB => inD_mul hA hB
  one_mem' := inD_one
  inv_mem' := fun hA => inD_inv hA

/-- The standard Borel of `SL(2,F)`: the upper triangular matrices. -/
def B : Subgroup (SL2 F) where
  carrier := {A : SL2 F | inB A}
  mul_mem' := fun hA hB => inB_mul hA hB
  one_mem' := inB_one
  inv_mem' := fun hA => inB_inv hA

@[simp] lemma mem_B_iff {A : SL2 F} : A ∈ B ↔ inB A := Iff.rfl

lemma mem_B_iff' {A : SL2 F} : A ∈ B ↔ (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := Iff.rfl

@[simp] lemma mem_D_iff {A : SL2 F} : A ∈ D ↔ inD A := Iff.rfl

lemma mem_D_iff' {A : SL2 F} :
    A ∈ D ↔ (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧ (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
  Iff.rfl

lemma unip_coe (b : F) : (unip b : Matrix (Fin 2) (Fin 2) F) = !![1, b; 0, 1] := by
  rw [unip, Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single_apply, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]

/-- `U ≤ B`. -/
lemma U_le_B : U (F := F) ≤ B (F := F) := by
  rintro A ⟨b, rfl⟩
  rw [mem_B_iff, inB, unip_coe]
  simp

/-- `D ≤ B`. -/
lemma D_le_B : D (F := F) ≤ B (F := F) := fun _ hA => inD_le_inB hA

/-- The Weyl element `!![0,1;1,0]` of `SL(2,F)` (characteristic 2, so its determinant is `1`). -/
def w : SL2 F :=
  ⟨(!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F), by
    rw [Matrix.det_fin_two_of]
    simp [CharTwo.neg_eq]⟩

lemma w_coe : (w (F := F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := rfl

lemma w_invol : w (F := F) * w (F := F) = 1 := by
  refine Subtype.ext (Matrix.ext ?_)
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [w_coe, Matrix.mul_apply, Fin.sum_univ_two]

end PSL2

end Work.Models
