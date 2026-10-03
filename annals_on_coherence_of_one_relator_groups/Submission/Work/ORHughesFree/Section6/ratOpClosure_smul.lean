import Mathlib
import Submission.Work.ORHughesFree.Section6.ClosureBasic

namespace Work.ORHughesFree.Section6

/-- The rational operation of [JZLA20, §4.3] is equivariant for multiplication by the units
`a` and `b` of `D`, in the sense that `(a x b)⋄ = b⁻¹ · x⋄ · a⁻¹`.

Indeed, if `x` is a unit then so is `a x b`, with `(a x b)⁻¹ = b⁻¹ x⁻¹ a⁻¹`; and if `x` is not a
unit then nor is `a x b`, so both sides vanish. -/
theorem ratOpClosure_smul {U : Type} [Ring U] (D : Subring U) {a b : ↥D} (ha : IsUnit a)
    (hb : IsUnit b) (x : ↥D) :
    Work.ORHughesFree.ratOpClosure D (a * x * b) =
      ↑hb.unit⁻¹ * Work.ORHughesFree.ratOpClosure D x * ↑ha.unit⁻¹ := by
  classical
  have hL : Work.ORHughesFree.ratOpClosure D (a * x * b)
      = if h : IsUnit (a * x * b) then ↑h.unit⁻¹ else 0 := rfl
  have hR : Work.ORHughesFree.ratOpClosure D x
      = if h : IsUnit x then ↑h.unit⁻¹ else 0 := rfl
  by_cases hx : IsUnit x
  · -- `x` is a unit, so `a * x * b` is a unit and the inverses multiply as claimed.
    have h1 : IsUnit (a * x * b) := (ha.mul hx).mul hb
    rw [hL, hR, dif_pos h1, dif_pos hx]
    have h1eq : h1.unit = ha.unit * hx.unit * hb.unit := by
      apply Units.ext
      simp only [Units.val_mul, IsUnit.unit_spec]
    rw [h1eq]
    simp only [mul_inv_rev, Units.val_mul, mul_assoc]
  · -- `x` is not a unit; since `a` and `b` are, neither is `a * x * b`.
    have h1 : ¬ IsUnit (a * x * b) :=
      fun h => hx ((IsUnit.mul_left_iff ha).mp ((IsUnit.mul_right_iff hb).mp h))
    rw [hL, hR, dif_neg h1, dif_neg hx]
    simp

end Work.ORHughesFree.Section6
