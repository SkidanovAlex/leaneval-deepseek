import Mathlib.Analysis.Calculus.MeanValue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect.BoundaryTime

/-- Mean value inequality on a convex set, with the increment measured against the (fixed)
derivative `L x` at the base point `x` and the error controlled by the uniform bound `η` on
`‖L z - L x‖`, `z ∈ B`.  Immediate from Mathlib's
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'`. -/
theorem norm_sub_fderiv_le_of_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : Set E} (hB : Convex ℝ B) {f : E → F} {L : E → E →L[ℝ] F} {x : E} {η : ℝ}
    (hx : x ∈ B) (hd : ∀ z ∈ B, HasFDerivAt f (L z) z)
    (hb : ∀ z ∈ B, ‖L z - L x‖ ≤ η) :
    ∀ w ∈ B, ‖f w - f x - L x (w - x)‖ ≤ η * ‖w - x‖ := by
  intro w hw
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (s := B) (f := f) (f' := L)
    (φ := L x) (C := η) (fun z hz => (hd z hz).hasFDerivWithinAt) (fun z hz => hb z hz) hB hx hw

end Work.FTS.PressureOn.Connect.BoundaryTime
