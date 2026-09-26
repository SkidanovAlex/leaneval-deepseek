import Mathlib
import Submission.Work.Drive.qwDefs
import Submission.Work.Drive.rank_triplet_Xa

/-!
# The collinear frame of the four-point collinearity partials

At a collinear window (`qV = β • qU`, `qS = γ • qU`) the four partials of the four-point
collinearity map `quadPartial` take the form recorded in `collRow`: if `A i = qU × (velocity at the
`i`-th window parameter)`, then

* `collRow β γ A 0 = ((β - 1) • A 0, (γ - 1) • A 0)`,
* `collRow β γ A 1 = (-β • A 1, -γ • A 1)`,
* `collRow β γ A 2 = (A 2, 0)`,
* `collRow β γ A 3 = (0, A 3)`.

This is the frame in which the level-`m` rank statement `Work.Drive.rank_triplet_minors` is proved.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- **The four rows of the collinearity partial matrix in the collinear frame.** -/
def collRow (β γ : ℝ) (A : Fin 4 → Space) : Fin 4 → Space × Space :=
  ![((β - 1) • A 0, (γ - 1) • A 0), (-β • A 1, -γ • A 1), (A 2, 0), (0, A 3)]

@[simp] lemma collRow_zero (β γ : ℝ) (A : Fin 4 → Space) :
    collRow β γ A 0 = ((β - 1) • A 0, (γ - 1) • A 0) := rfl

@[simp] lemma collRow_one (β γ : ℝ) (A : Fin 4 → Space) :
    collRow β γ A 1 = (-β • A 1, -γ • A 1) := rfl

@[simp] lemma collRow_two (β γ : ℝ) (A : Fin 4 → Space) :
    collRow β γ A 2 = (A 2, 0) := rfl

@[simp] lemma collRow_three (β γ : ℝ) (A : Fin 4 → Space) :
    collRow β γ A 3 = (0, A 3) := rfl

/-- `collRow` is additive in the transverse vectors. -/
lemma collRow_add (β γ : ℝ) (A B : Fin 4 → Space) :
    collRow β γ (A + B) = collRow β γ A + collRow β γ B := by
  funext i
  fin_cases i <;>
    simp [collRow, Pi.add_apply, Prod.mk_add_mk, smul_add, neg_add_rev, add_comm, add_left_comm,
      add_assoc]

/-- `collRow` is homogeneous in the transverse vectors. -/
lemma collRow_smul (β γ : ℝ) (c : ℝ) (A : Fin 4 → Space) :
    collRow β γ (c • A) = c • collRow β γ A := by
  funext i
  fin_cases i <;>
    simp [collRow, Pi.smul_apply, smul_smul, mul_comm, mul_left_comm, mul_assoc]

/-! ## The rows at explicit `Fin 4` elements (constructor form) -/

lemma collRow_apply_zero (β γ : ℝ) (A : Fin 4 → Space) (h : 0 < 4) :
    collRow β γ A ⟨0, h⟩ = ((β - 1) • A 0, (γ - 1) • A 0) := rfl

lemma collRow_apply_one (β γ : ℝ) (A : Fin 4 → Space) (h : 1 < 4) :
    collRow β γ A ⟨1, h⟩ = (-β • A 1, -γ • A 1) := rfl

lemma collRow_apply_two (β γ : ℝ) (A : Fin 4 → Space) (h : 2 < 4) :
    collRow β γ A ⟨2, h⟩ = (A 2, 0) := rfl

lemma collRow_apply_three (β γ : ℝ) (A : Fin 4 → Space) (h : 3 < 4) :
    collRow β γ A ⟨3, h⟩ = (0, A 3) := rfl

lemma collRow_zero_fun (β γ : ℝ) :
    collRow β γ (0 : Fin 4 → Space) = 0 := by
  funext i
  fin_cases i <;> simp [collRow]

end

end Work.Drive
