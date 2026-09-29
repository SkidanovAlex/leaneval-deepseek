import Submission.Work.TMComp.RotBasics.Defs

/-!
# An explicit positive lift of an upper triangular `SL(2,ℝ)` matrix

`upperLift r q` is an explicit positive lift (in the sense of `IsPosLift`) of the upper
triangular matrix `!![r,q;0,1/r]`, `r > 0`.

The formula is
`⌊t⌋ + arg((-1)^⌊t⌋ • z(t))/π`, where `z(t) = (r cos πt + q sin πt) + i sin πt / r`:
on the interval `t ∈ [m, m+1]` the vector `(-1)^m z(t)` stays in the closed upper half
plane, so the *principal* argument gives a manifestly continuous branch, and the `⌊t⌋`
term makes the formula match on consecutive intervals.

`conjLift B η y` is the corresponding lift of a general continuous `SL(2,ℝ)`-valued `B`,
using the first-column angle `η`.
-/

namespace Work.TMComp.RotBasics

noncomputable section

/-- The explicit positive lift of the upper triangular matrix `!![r,q;0,1/r]`, `0 < r`. -/
def upperLift (r q t : ℝ) : ℝ :=
  (⌊t⌋ : ℝ) +
    Complex.arg (((-1 : ℝ) ^ (⌊t⌋ : ℤ)) •
      (⟨r * Real.cos (Real.pi * t) + q * Real.sin (Real.pi * t), Real.sin (Real.pi * t) / r⟩ : ℂ))
      / Real.pi

/-- The length of the first column of a real `2×2` matrix. -/
def colNorm (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := Real.sqrt ((M 0 0) ^ 2 + (M 1 0) ^ 2)

/-- The `(0,1)` entry of `R_η⁻¹ M` when the first column of `M` has angle `2πη`. -/
def colQ (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ((M 0 0) * (M 0 1) + (M 1 0) * (M 1 1)) / colNorm M

/-- The lift of a continuous `SL(2,ℝ)`-valued `B` with first-column angle `2πη`. -/
def conjLift (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (η : ℝ → ℝ) (y : ℝ) : ℝ → ℝ :=
  fun t => 2 * η y + upperLift (colNorm (B y)) (colQ (B y)) t

end

end Work.TMComp.RotBasics
