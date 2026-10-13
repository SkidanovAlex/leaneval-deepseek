/-
  WilG1 — vocabulary for the one-variable theory (used to prove `G1_generic_smooth`).

  Everything here is a *first-order* condition on the graph of `g : ℝ → ℝ`, hence Ω-definable
  (the Ω-membership lemmas are delegated).  The one-variable differentiability theorem is
  assembled from:

  * `bad_covered`    : a non-differentiability point is an oscillation point, or a corner,
                       or a point of infinite two-sided derivative;
  * `oscillation_empty` : the oscillation sets have empty interior;
  * `no_strictLocalMax_interval` : the corner sets have empty interior (given continuity);
  * `no_deriv_atTop_interval`    : the infinite-derivative sets have empty interior.
-/
import Submission.Work.WilG1.Basic

set_option autoImplicit false

noncomputable section

open Classical

namespace Work.WilG1

open WilkiesDesign WilkiesConjecture

/-- The difference quotient of `g` at `x` evaluated at `y`. -/
def dq (g : ℝ → ℝ) (x y : ℝ) : ℝ := (g y - g x) / (y - x)

/-- Oscillation set: `x` is a right-accumulation point of both `{y > x : dq x y > q}` and
`{y > x : dq x y < q}`. -/
def oscR (g : ℝ → ℝ) (q : ℝ) : Set ℝ :=
  {x | (∀ δ : ℝ, 0 < δ → ∃ y : ℝ, x < y ∧ y < x + δ ∧ q < dq g x y)
      ∧ (∀ δ : ℝ, 0 < δ → ∃ y : ℝ, x < y ∧ y < x + δ ∧ dq g x y < q)}

/-- The same on the left of `x`. -/
def oscL (g : ℝ → ℝ) (q : ℝ) : Set ℝ :=
  {x | (∀ δ : ℝ, 0 < δ → ∃ y : ℝ, x - δ < y ∧ y < x ∧ q < dq g x y)
      ∧ (∀ δ : ℝ, 0 < δ → ∃ y : ℝ, x - δ < y ∧ y < x ∧ dq g x y < q)}

/-- `x` is a strict local maximum of `g - q·x` (a "corner" of slope `q`). -/
def cornerMax (g : ℝ → ℝ) (q : ℝ) : Set ℝ :=
  {x | (∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, x < y → y < x + δ → g y - g x < q * (y - x))
     ∧ (∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, x - δ < y → y < x → g y - g x < q * (y - x))}

/-- `x` is a strict local minimum of `g - q·x`. -/
def cornerMin (g : ℝ → ℝ) (q : ℝ) : Set ℝ :=
  {x | (∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, x < y → y < x + δ → q * (y - x) < g y - g x)
     ∧ (∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, x - δ < y → y < x → q * (y - x) < g y - g x)}

/-- The two-sided difference quotient of `g` at `x` tends to `+∞` (`s = 1`) or to `-∞`
(`s = -1`). -/
def infDeriv (g : ℝ → ℝ) (s : ℝ) : Set ℝ :=
  {x | ∀ M : ℝ, 1 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ y : ℝ, y ≠ x → |y - x| < δ → M < s * dq g x y}

/-- The non-differentiability set of `g`. -/
def badSet (g : ℝ → ℝ) : Set ℝ := {x | ¬ DifferentiableAt ℝ g x}

/-- Transport of a set of reals into `Fin 1 → ℝ`. -/
def liftR (A : Set ℝ) : Set (Fin 1 → ℝ) := {z | z 0 ∈ A}

end Work.WilG1
