import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Conic.mem_borel

/-!
# The order of the Borel subgroup of `SL(2,F)`

`Work.L2F.borel F` is the (upper triangular) Borel subgroup of `SL(2,F)`.  We compute

  `Nat.card (borel F) = Nat.card F * (Nat.card F - 1)`.

By `Work.L2F.Conic.mem_borel` the subgroup `borel F` consists exactly of the matrices with
entry `1 0` equal to `0`.  Such a matrix has the shape `!![a, b; 0, a⁻¹]` with `a ≠ 0`, so
`borel F` is in bijection with `Fˣ × F` (choose the top-left entry as a unit and the top-right
entry freely); the count is then immediate from `Nat.card_prod` and `Nat.card_units`.
-/

open Matrix

namespace Work.L2F.PSL

/-- The forward map of the bijection `borel F ≃ Fˣ × F`: an upper triangular matrix in `SL(2,F)`
is sent to the pair of its top-left entry (a unit, because the determinant is `1` and the
bottom-left entry is `0`) and its top-right entry. -/
private noncomputable def borelToUnitsProd (F : Type*) [Field F] (x : Work.L2F.borel F) :
    Fˣ × F := by
  have hdet : (x.1 : Matrix (Fin 2) (Fin 2) F).det = 1 := x.1.2
  rw [Matrix.det_fin_two] at hdet
  have h10 : (x.1 : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    (Work.L2F.Conic.mem_borel F x.1).mp x.2
  rw [h10, mul_zero, sub_zero] at hdet
  exact (Units.mk ((x.1 : Matrix (Fin 2) (Fin 2) F) 0 0)
    ((x.1 : Matrix (Fin 2) (Fin 2) F) 1 1) hdet (by rw [mul_comm]; exact hdet),
    (x.1 : Matrix (Fin 2) (Fin 2) F) 0 1)

/-- The inverse map of `borelToUnitsProd`: `(a, b) ↦ !![a, b; 0, a⁻¹]`. -/
private noncomputable def unitsProdToBorel (F : Type*) [Field F] (p : Fˣ × F) :
    Work.L2F.borel F := by
  refine ⟨⟨!![(p.1 : F), p.2; 0, ↑(p.1⁻¹)], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]; simp
  · exact (Work.L2F.Conic.mem_borel F
      ⟨!![(p.1 : F), p.2; 0, ↑(p.1⁻¹)], by rw [Matrix.det_fin_two_of]; simp⟩).mpr (by simp)

/-- The Borel subgroup of `SL(2,F)` is in bijection with `Fˣ × F`: an upper triangular
matrix `!![a, b; 0, a⁻¹]` of determinant one is determined by `(a, b) ∈ Fˣ × F`. -/
private noncomputable def borelEquivUnitsProd (F : Type*) [Field F] :
    Work.L2F.borel F ≃ Fˣ × F where
  toFun := borelToUnitsProd F
  invFun := unitsProdToBorel F
  left_inv := by
    intro x
    have h10 : (x.1 : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
      (Work.L2F.Conic.mem_borel F x.1).mp x.2
    have hdet : (x.1 : Matrix (Fin 2) (Fin 2) F).det = 1 := x.1.2
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [borelToUnitsProd, unitsProdToBorel, h10]
  right_inv := by
    intro p
    simp [borelToUnitsProd, unitsProdToBorel]

/-- The upper triangular subgroup of `SL(2,F)` has order `q(q-1)`, `q = Nat.card F`. -/
theorem natCard_borel (F : Type*) [Field F] [Fintype F] :
    Nat.card (Work.L2F.borel F) = Nat.card F * (Nat.card F - 1) := by
  rw [Nat.card_congr (borelEquivUnitsProd F), Nat.card_prod, Nat.card_units, Nat.mul_comm]

end Work.L2F.PSL
