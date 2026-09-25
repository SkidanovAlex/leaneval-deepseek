import Mathlib
import Submission.Work.Core.Defs

namespace Work.Nijenhuis

open LeanEval.Geometry.NewlanderNirenberg
open Submission

/-- The Nijenhuis tensor is antisymmetric in its two arguments. -/
theorem antisymm {n : ℕ} {U : Set (E n)} {J : E n → E n →L[ℝ] E n} (hU : IsOpen U)
    (hJ : IsAlmostComplexOn J U) {x : E n} (hx : x ∈ U) {V W : E n → E n}
    (hV : ContDiffAt ℝ 1 V x) (hW : ContDiffAt ℝ 1 W x) :
    nijenhuis J V W x = - nijenhuis J W V x := by
  have h1 : VectorField.lieBracket ℝ (fun y => J y (W y)) (fun y => J y (V y)) x
      = - VectorField.lieBracket ℝ (fun y => J y (V y)) (fun y => J y (W y)) x :=
    VectorField.lieBracket_swap (𝕜 := ℝ)
  have h2 : VectorField.lieBracket ℝ (fun y => J y (W y)) V x
      = - VectorField.lieBracket ℝ V (fun y => J y (W y)) x :=
    VectorField.lieBracket_swap (𝕜 := ℝ)
  have h3 : VectorField.lieBracket ℝ W (fun y => J y (V y)) x
      = - VectorField.lieBracket ℝ (fun y => J y (V y)) W x :=
    VectorField.lieBracket_swap (𝕜 := ℝ)
  have h4 : VectorField.lieBracket ℝ W V x = - VectorField.lieBracket ℝ V W x :=
    VectorField.lieBracket_swap (𝕜 := ℝ)
  simp only [nijenhuis, h1, h2, h3, h4, map_neg]
  abel

end Work.Nijenhuis
