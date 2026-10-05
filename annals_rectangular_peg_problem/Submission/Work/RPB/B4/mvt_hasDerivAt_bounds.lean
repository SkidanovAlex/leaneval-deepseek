import Mathlib

namespace Work.RPB.B4

theorem mvt_hasDerivAt_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} {C a b : ℝ}
    (hf : ∀ x : ℝ, HasDerivAt f (f' x) x)
    (hbound : ∀ x ∈ Set.uIcc a b, ‖f' x‖ ≤ C) :
    ‖f a - f b‖ ≤ C * |a - b| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (𝕜 := ℝ) (G := E) (f := f) (f' := f') (s := Set.uIcc a b) (C := C)
    (fun x _ => (hf x).hasDerivWithinAt) hbound (convex_uIcc a b)
    Set.right_mem_uIcc Set.left_mem_uIcc
  simpa [Real.norm_eq_abs] using h

end Work.RPB.B4
