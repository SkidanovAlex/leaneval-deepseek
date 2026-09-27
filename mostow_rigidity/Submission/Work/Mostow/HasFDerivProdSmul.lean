import Mathlib
import Submission.Work.Mostow.BCGDefs

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- Product rule on a product domain, in the exact shape needed for the joint Fréchet
derivative `DGv` of the BCG gradient field: if `a` is differentiable at `x` with derivative
`a'` and `b` is differentiable at `y` with derivative `b'`, then
`(p : E n × E n) ↦ a p.1 • b p.2` is differentiable at `(x,y)` with derivative the continuous
linear map whose first component is `w ↦ (a' w) • b y` and whose second is `v ↦ a x • (b' v)`. -/
theorem HasFDerivProdSmul (n : ℕ) {a : Submission.Mostow.E n → ℝ}
    {a' : Submission.Mostow.E n →L[ℝ] ℝ}
    {b : Submission.Mostow.E n → Submission.Mostow.E n}
    {b' : Submission.Mostow.E n →L[ℝ] Submission.Mostow.E n}
    {x y : Submission.Mostow.E n}
    (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' y) :
    HasFDerivAt (fun p : Submission.Mostow.E n × Submission.Mostow.E n => a p.1 • b p.2)
      ((a'.smulRight (b y)) ∘L
          ContinuousLinearMap.fst ℝ (Submission.Mostow.E n) (Submission.Mostow.E n) +
        (a x • b') ∘L
          ContinuousLinearMap.snd ℝ (Submission.Mostow.E n) (Submission.Mostow.E n))
      (x, y) := by
  -- `a ∘ fst` and `b ∘ snd` are the two factors; each is differentiated by the chain rule
  -- (a continuous linear map is its own derivative), and then the scalar-multiplication
  -- product rule `HasFDerivAt.smul` produces the sum of the two partial contributions.
  have h1 : HasFDerivAt (fun p : Submission.Mostow.E n × Submission.Mostow.E n => a p.1)
      (a' ∘L ContinuousLinearMap.fst ℝ (Submission.Mostow.E n) (Submission.Mostow.E n)) (x, y) :=
    ha.comp (x, y)
      (ContinuousLinearMap.fst ℝ (Submission.Mostow.E n) (Submission.Mostow.E n)).hasFDerivAt
  have h2 : HasFDerivAt (fun p : Submission.Mostow.E n × Submission.Mostow.E n => b p.2)
      (b' ∘L ContinuousLinearMap.snd ℝ (Submission.Mostow.E n) (Submission.Mostow.E n)) (x, y) :=
    hb.comp (x, y)
      (ContinuousLinearMap.snd ℝ (Submission.Mostow.E n) (Submission.Mostow.E n)).hasFDerivAt
  have hsm := h1.smul h2
  -- Put the resulting derivative into the exact shape of the statement: push the projections
  -- past the scalar multiplication and the `smulRight`.
  have hd :
      a x • (b' ∘L ContinuousLinearMap.snd ℝ (Submission.Mostow.E n) (Submission.Mostow.E n)) +
          (a' ∘L ContinuousLinearMap.fst ℝ (Submission.Mostow.E n) (Submission.Mostow.E n)).smulRight
            (b y)
        = (a'.smulRight (b y)) ∘L
              ContinuousLinearMap.fst ℝ (Submission.Mostow.E n) (Submission.Mostow.E n) +
            (a x • b') ∘L
              ContinuousLinearMap.snd ℝ (Submission.Mostow.E n) (Submission.Mostow.E n) := by
    apply ContinuousLinearMap.ext
    intro v
    simp [ContinuousLinearMap.smulRight_apply, add_comm]
  rw [hd] at hsm
  exact hsm

end Work.Mostow
