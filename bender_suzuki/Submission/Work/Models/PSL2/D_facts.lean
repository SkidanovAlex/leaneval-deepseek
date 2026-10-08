import Mathlib
import Submission.Work.Models.PSL2.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Models.PSL2.D_facts` — the standard split torus of `SL(2,F)`

`D` is the subgroup of diagonal matrices of `SL(2,F)`.  Its elements are the matrices
`diag(a, a⁻¹)` with `a : Fˣ`; because the determinant forces the two diagonal entries to be
mutually inverse, evaluation at the `(0,0)`-entry is a group isomorphism `D ≃* Fˣ`.  Hence
`|D| = |Fˣ| = |F| - 1` and `D` is cyclic (it is a finite subgroup of the units of the field
`F`).
-/

namespace Work.Models.PSL2

open Matrix

variable {F : Type*} [Field F] [CharP F 2]

/-- The two diagonal entries of an element of `D` multiply to `1`: their product is the
determinant. -/
lemma D_diag_mul (A : SL2 F) (hA : A ∈ D (F := F)) :
    ((A : Matrix (Fin 2) (Fin 2) F) 0 0) * ((A : Matrix (Fin 2) (Fin 2) F) 1 1) = 1 := by
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det = 1 := A.2
  rw [Matrix.det_fin_two] at hdet
  rw [hA.1, hA.2, mul_zero, sub_zero] at hdet
  exact hdet

/-- The diagonal matrix `diag(a, a⁻¹)`, an element of `SL(2,F)`. -/
def diagUnit (u : Fˣ) : SL2 F :=
  ⟨!![(u : F), 0; 0, ((u⁻¹ : Fˣ) : F)], by
    rw [Matrix.det_fin_two_of]
    simp⟩

lemma diagUnit_mem (u : Fˣ) : diagUnit (F := F) u ∈ D (F := F) := by
  refine ⟨?_, ?_⟩ <;> simp [diagUnit]

/-- The `(0,0)`-entry of an element of `D`, as a unit (its inverse is the `(1,1)`-entry, by
`Work.Models.PSL2.D_diag_mul`). -/
def DToUnit (A : ↥(D (F := F))) : Fˣ :=
  ⟨((A : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0,
   ((A : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 1,
   D_diag_mul (A : SL2 F) A.2,
   by rw [mul_comm]; exact D_diag_mul (A : SL2 F) A.2⟩

@[simp] lemma DToUnit_apply (A : ↥(D (F := F))) :
    ((DToUnit A : Fˣ) : F) = ((A : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 := rfl

/-- The isomorphism `D ≃* Fˣ` given by the `(0,0)`-entry (its inverse is `diagUnit`). -/
def DUnitHom : ↥(D (F := F)) →* Fˣ where
  toFun := DToUnit
  map_one' := by ext; simp
  map_mul' := by
    intro A B
    ext
    simp only [Units.val_mul, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, DToUnit_apply]
    rw [(A.2).1, zero_mul, add_zero]

lemma DUnitHom_injective : Function.Injective (DUnitHom (F := F)) := by
  intro A B h
  have hval : ((A : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0
      = ((B : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 :=
    congrArg (fun u : Fˣ => (u : F)) h
  have hB := D_diag_mul (B : SL2 F) B.2
  have h11 : ((A : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 1
      = ((B : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    have hA := D_diag_mul (A : SL2 F) A.2
    have hb : ((B : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hB
      exact one_ne_zero hB.symm
    rw [hval] at hA
    exact mul_left_cancel₀ hb (hA.trans hB.symm)
  apply Subtype.ext
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hval, h11, (A.2).1, (A.2).2, (B.2).1, (B.2).2]

lemma DUnitHom_surjective : Function.Surjective (DUnitHom (F := F)) := by
  intro u
  exact ⟨⟨diagUnit u, diagUnit_mem u⟩, by ext; rfl⟩

theorem D_facts {F : Type*} [Field F] [CharP F 2] [Finite F] :
    Nat.card ↥(Work.Models.PSL2.D (F := F)) = Nat.card F - 1 ∧
      IsCyclic ↥(Work.Models.PSL2.D (F := F)) := by
  have hbij : Function.Bijective (DUnitHom (F := F)) :=
    ⟨DUnitHom_injective, DUnitHom_surjective⟩
  have hcard : Nat.card ↥(Work.Models.PSL2.D (F := F)) = Nat.card Fˣ :=
    Nat.card_congr (Equiv.ofBijective _ hbij)
  exact ⟨by rw [hcard, Nat.card_units],
    isCyclic_of_injective _ DUnitHom_injective⟩

end Work.Models.PSL2
