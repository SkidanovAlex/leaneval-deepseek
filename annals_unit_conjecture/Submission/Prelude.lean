import ChallengeDeps
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

open UnitConjecture

set_option autoImplicit false

noncomputable section

namespace Submission

open UnitConjecture

abbrev a : P := (UnitConjecture.a : P)
abbrev b : P := (UnitConjecture.b : P)
abbrev x : P := UnitConjecture.x
abbrev y : P := UnitConjecture.y
abbrev z : P := UnitConjecture.z

lemma x_eq_a2 : x = a ^ 2 := by rfl
lemma y_eq_b2 : y = b ^ 2 := by rfl
lemma z_eq_ab2 : z = (a * b) ^ 2 := by rfl

lemma rel1 : b⁻¹ * a ^ 2 * b * a ^ 2 = 1 := by
  exact (PresentedGroup.one_of_mem (hx := by simp [relations]) :
    ((UnitConjecture.b⁻¹ * UnitConjecture.a ^ 2 * UnitConjecture.b * UnitConjecture.a ^ 2 : FreeGroup generators) : P) = 1)

lemma rel2 : a⁻¹ * b ^ 2 * a * b ^ 2 = 1 := by
  exact (PresentedGroup.one_of_mem (hx := by simp [relations]) :
    ((UnitConjecture.a⁻¹ * UnitConjecture.b ^ 2 * UnitConjecture.a * UnitConjecture.b ^ 2 : FreeGroup generators) : P) = 1)

end Submission
