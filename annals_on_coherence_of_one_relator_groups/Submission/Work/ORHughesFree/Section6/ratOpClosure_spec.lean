import Mathlib
import Submission.Work.ORHughesFree.Section6.ClosureBasic

namespace Work.ORHughesFree.Section6

theorem ratOpClosure_spec {U : Type} [Ring U] (D : Subring U) (hnt : Nontrivial ↥D) :
    (∀ (x : ↥D) (h : IsUnit x), Work.ORHughesFree.ratOpClosure D x = ↑h.unit⁻¹) ∧
    (∀ (x : ↥D) (h : IsUnit x), x * Work.ORHughesFree.ratOpClosure D x = 1) ∧
    (∀ x : ↥D, ¬ IsUnit x → Work.ORHughesFree.ratOpClosure D x = 0) ∧
    Work.ORHughesFree.ratOpClosure D 0 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x h
    unfold Work.ORHughesFree.ratOpClosure
    rw [dif_pos h]
  · intro x h
    have hx : Work.ORHughesFree.ratOpClosure D x = ↑h.unit⁻¹ := by
      unfold Work.ORHughesFree.ratOpClosure
      rw [dif_pos h]
    calc x * Work.ORHughesFree.ratOpClosure D x = x * ↑h.unit⁻¹ := by rw [hx]
      _ = ↑h.unit * ↑h.unit⁻¹ := by rw [IsUnit.unit_spec h]
      _ = 1 := Units.mul_inv h.unit
  · intro x h
    unfold Work.ORHughesFree.ratOpClosure
    rw [dif_neg h]
  · unfold Work.ORHughesFree.ratOpClosure
    rw [dif_neg (not_isUnit_zero (M₀ := ↥D))]

end Work.ORHughesFree.Section6
