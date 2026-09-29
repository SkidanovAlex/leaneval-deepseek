import Submission.Work.TMC7Core.Cocycle

/-!
# TMC7Core: the algebraic (Laurent-polynomial) transfer cocycle

Multiplying `A_n(x)` by `z^n`, `z = e^{2πix}`, turns the cocycle into a matrix of
*polynomials* in `z` of degree `≤ 2n`.  This is the structure behind
* the Herman bound (`z^n A_n(z)` has an explicit leading coefficient), and
* the Fourier decay `F1` of `ln ‖A_n‖` used by the large deviation theorem.

Conventions: `ω = e^{2πiα}`, `tmZ lam E z = z • S_{λ,E}(x)`, `iterZ` the ordered product
of the rescaled factors, `iterPoly` the same product as a matrix of polynomials.
-/

open MeasureTheory Filter Topology Set Polynomial
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core

/-- `ω = e^{2πiα}`. -/
def omega (α : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * α)

theorem omega_zero : omega 0 = 1 := by simp [omega]

/-- The algebraic transfer matrix: at `z = e^{2πix}` it equals `z • S_{λ,E}(x)`, where
`z • S = [[zE - λ(z²+1), -z], [z, 0]]`. -/
def tmZ (lam : ℝ) (E : ℂ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![E * z - (lam : ℂ) * (z ^ 2 + 1), -z; z, 0]

/-- `z^n A_n(x)` for `z = e^{2πix}`: the ordered product of the rescaled factors. -/
def iterZ (α lam : ℝ) (E : ℂ) : ℕ → ℂ → Matrix (Fin 2) (Fin 2) ℂ
  | 0, _ => 1
  | n + 1, z => tmZ lam E (z * omega α ^ n) * iterZ α lam E n z

/-- The same product, as a matrix of polynomials in `z`: the rescaled factor at step `j`
is `tmZ lam E (ω^j z)`, a polynomial of degree `≤ 2`. -/
def tmPoly (lam : ℝ) (E : ℂ) (w : ℂ) : Matrix (Fin 2) (Fin 2) (Polynomial ℂ) :=
  !![C E * (C w * X) - C (lam : ℂ) * ((C w * X) ^ 2 + 1), -(C w * X); C w * X, 0]

/-- `z^n A_n` as a matrix of polynomials of degree `≤ 2n`. -/
def iterPoly (α lam : ℝ) (E : ℂ) : ℕ → Matrix (Fin 2) (Fin 2) (Polynomial ℂ)
  | 0 => 1
  | n + 1 => tmPoly lam E (omega α ^ n) * iterPoly α lam E n

end Work.TMC7Core
