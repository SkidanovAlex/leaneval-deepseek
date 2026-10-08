import Mathlib
import Submission.Work.Models.PSL2.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Models.PSL2.card_D` — the order of the standard split torus of `SL(2,F)`

`D` is the subgroup of diagonal matrices of `SL(2,F)`.  The determinant condition forces the
two diagonal entries of an element of `D` to be mutually inverse, so an element of `D` is
determined by its `(0,0)`-entry, and that entry is a unit of `F`; conversely every `u : Fˣ`
occurs as `diag(u, u⁻¹)`.  Hence the `(0,0)`-entry is a bijection `↥D ≃ Fˣ`, giving

  `|D| = |Fˣ| = |F| - 1`.

(Note that no use of the characteristic is made: the result holds for any field.)
-/

namespace Work.Models.PSL2

open Matrix

variable {F : Type*} [Field F] [CharP F 2]

/-- The two diagonal entries of an element of `D` multiply to `1`: their product is the
determinant. -/
lemma cardD_diag_mul (A : SL2 F) (hA : A ∈ D (F := F)) :
    ((A : Matrix (Fin 2) (Fin 2) F) 0 0) * ((A : Matrix (Fin 2) (Fin 2) F) 1 1) = 1 := by
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det = 1 := A.2
  rw [Matrix.det_fin_two] at hdet
  rw [hA.1, hA.2, mul_zero, sub_zero] at hdet
  exact hdet

/-- The diagonal matrix `diag(u, u⁻¹)`, an element of `SL(2,F)`. -/
def cardD_diagUnit (u : Fˣ) : SL2 F :=
  ⟨!![(u : F), 0; 0, ((u⁻¹ : Fˣ) : F)], by
    rw [Matrix.det_fin_two_of]
    simp⟩

lemma cardD_diagUnit_mem (u : Fˣ) : cardD_diagUnit (F := F) u ∈ D (F := F) := by
  refine ⟨?_, ?_⟩ <;> simp [cardD_diagUnit]

/-- The `(0,0)`-entry of an element of `D`, as a unit of `F` (its inverse is the `(1,1)`-entry,
by `cardD_diag_mul`). -/
def cardD_DToUnits (A : ↥(D (F := F))) : Fˣ where
  val := ((A : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0
  inv := ((A : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 1
  val_inv := cardD_diag_mul (A : SL2 F) A.2
  inv_val := by rw [mul_comm]; exact cardD_diag_mul (A : SL2 F) A.2

/-- The `(0,0)`-entry determines an element of `D`. -/
lemma cardD_DToUnits_injective : Function.Injective (cardD_DToUnits (F := F)) := by
  intro A B h
  have hval : ((A : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0
      = ((B : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 :=
    congrArg (fun u : Fˣ => (u : F)) h
  have hA11 := cardD_diag_mul (A : SL2 F) A.2
  have hB11 := cardD_diag_mul (B : SL2 F) B.2
  have h11 : ((A : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 1
      = ((B : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    have hb : ((B : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hB11
      exact one_ne_zero hB11.symm
    rw [hval] at hA11
    exact mul_left_cancel₀ hb (hA11.trans hB11.symm)
  apply Subtype.ext
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hval, h11, (A.2).1, (A.2).2, (B.2).1, (B.2).2]

/-- Every unit occurs as the `(0,0)`-entry of an element of `D`, namely `diag(u, u⁻¹)`. -/
lemma cardD_DToUnits_surjective : Function.Surjective (cardD_DToUnits (F := F)) := by
  intro u
  exact ⟨⟨cardD_diagUnit u, cardD_diagUnit_mem u⟩,
    by ext; simp [cardD_DToUnits, cardD_diagUnit]⟩

theorem card_D {F : Type*} [Field F] [CharP F 2] [Finite F] :
    Nat.card ↥(Work.Models.PSL2.D (F := F)) = Nat.card F - 1 := by
  have hbij : Function.Bijective (cardD_DToUnits (F := F)) :=
    ⟨cardD_DToUnits_injective, cardD_DToUnits_surjective⟩
  have hcard : Nat.card ↥(Work.Models.PSL2.D (F := F)) = Nat.card Fˣ :=
    Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [hcard, Nat.card_units]

end Work.Models.PSL2
