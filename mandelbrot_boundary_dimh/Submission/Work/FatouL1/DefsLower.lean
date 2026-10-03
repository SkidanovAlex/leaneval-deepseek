import Mathlib

/-!
# FATOU-L1: the rectangle boundary integral

`rectB a b Y f` is the boundary integral of `f` over the rectangle `[a,b] × [-Y,Y]`, written in
exactly the orientation/normalisation used by
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn` for the corners `⟨a,-Y⟩` and `⟨b,Y⟩`.
Keeping it as a definition lets the winding-number and residue lemmas be stated without repeating
the (long) formula.
-/

namespace Work.FatouL1

noncomputable section

/-- Boundary integral of `f` over the rectangle `[a,b] × [-Y,Y]` (corners `⟨a,-Y⟩`, `⟨b,Y⟩`). -/
def rectB (a b Y : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in a..b, f ((x : ℂ) + (-Y) * Complex.I)) -
      (∫ x : ℝ in a..b, f ((x : ℂ) + Y * Complex.I)) +
    Complex.I * (∫ y : ℝ in (-Y)..Y, f ((b : ℂ) + y * Complex.I)) -
      Complex.I * (∫ y : ℝ in (-Y)..Y, f ((a : ℂ) + y * Complex.I))

end

end Work.FatouL1
