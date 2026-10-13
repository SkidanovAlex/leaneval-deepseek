/-
  WilG1 / Cell / JunkDefs.

  The vocabulary of the "junk partial" criterion for `C^k` smoothness of a definable function.

  For a function `h : ℝⁿ → ℝ` and a direction `i`, the *fibre* of `h` in direction `i` at the
  parameter `y` is the one-variable function `t ↦ h (update y i t)`; its (one-variable)
  derivative, with the junk value `0` wherever it does not exist, is the *junk partial*
  `junkP h i y`.  Iterating this along a word `w : List (Fin n)` gives `junkIt f w`.

  The two "bad" sets attached to `h` are

  * `fibBad h i` — the set of parameters at which the fibre in direction `i` is not
    differentiable (so that the junk partial is really junk);
  * `disc h` — the discontinuity locus of `h`.

  The main theorem is proved by showing that `f` is `C^k` on any open set on which none of the
  iterated junk partials (words of length `≤ k`) suffers either kind of failure.
-/
import Mathlib
import Submission.Work.Wilkies.Defs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG1.Cell

open WilkiesDesign

/-- The fibre of `h` in direction `i` at the parameter `y`: the one-variable function
`t ↦ h (update y i t)`. -/
def fibreMap {n : ℕ} (h : (Fin n → ℝ) → ℝ) (i : Fin n) (y : Fin n → ℝ) : ℝ → ℝ :=
  fun t => h (Function.update y i t)

/-- The junk partial of `h` in direction `i`: the one-variable derivative of the fibre, with
value `0` wherever the fibre is not differentiable. -/
def junkP {n : ℕ} (h : (Fin n → ℝ) → ℝ) (i : Fin n) : (Fin n → ℝ) → ℝ :=
  fun y => deriv (fibreMap h i y) (y i)

/-- The iterated junk partials of `f`: `junkIt f (i :: w)` differentiates `f` in direction `i`
first, then continues along `w`. -/
def junkIt {n : ℕ} (f : (Fin n → ℝ) → ℝ) : List (Fin n) → (Fin n → ℝ) → ℝ
  | [] => f
  | i :: w => junkIt (junkP f i) w

/-- The parameters at which the fibre of `h` in direction `i` fails to be differentiable. -/
def fibBad {n : ℕ} (h : (Fin n → ℝ) → ℝ) (i : Fin n) : Set (Fin n → ℝ) :=
  {y | ¬ DifferentiableAt ℝ (fibreMap h i y) (y i)}

/-- The discontinuity locus of `h`. -/
def disc {n : ℕ} (h : (Fin n → ℝ) → ℝ) : Set (Fin n → ℝ) :=
  {y | ¬ ContinuousAt h y}

/-- The linear map whose `i`-th coordinate is `v i`.  On an open set where the fibre derivatives
of `h` exist and are continuous, this is `fderiv ℝ h`. -/
def jet {n : ℕ} (v : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin n, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).smulRight (v i)

@[simp] theorem junkIt_nil {n : ℕ} (f : (Fin n → ℝ) → ℝ) : junkIt f [] = f := rfl

@[simp] theorem junkIt_cons {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n) (w : List (Fin n)) :
    junkIt f (i :: w) = junkIt (junkP f i) w := rfl

/-- A junk partial of an iterated junk partial is an iterated junk partial of the original
function along the concatenated word. -/
theorem junkIt_concat {n : ℕ} (f : (Fin n → ℝ) → ℝ) (w : List (Fin n)) (i : Fin n) :
    junkIt f (w ++ [i]) = junkP (junkIt f w) i := by
  induction w generalizing f with
  | nil => rfl
  | cons j w ih => exact ih (junkP f j)

/-- `junkP` agrees with the fibre derivative wherever the latter exists. -/
theorem junkP_eq_deriv {n : ℕ} (h : (Fin n → ℝ) → ℝ) (i : Fin n) {y : Fin n → ℝ}
    (hy : DifferentiableAt ℝ (fibreMap h i y) (y i)) :
    junkP h i y = deriv (fibreMap h i y) (y i) := rfl

/-- On an open set where the fibre derivative in direction `i` exists everywhere, `junkP h i`
is the genuine partial derivative. -/
theorem junkP_eq_of_fibre {n : ℕ} (h : (Fin n → ℝ) → ℝ) (i : Fin n) {V : Set (Fin n → ℝ)}
    (hex : ∀ z ∈ V, DifferentiableAt ℝ (fibreMap h i z) (z i)) {z : Fin n → ℝ} (hz : z ∈ V) :
    junkP h i z = deriv (fibreMap h i z) (z i) := rfl

/-- The `jet` map is the sum of its coordinates. -/
theorem jet_apply {n : ℕ} (v : Fin n → ℝ) (x : Fin n → ℝ) :
    jet v x = ∑ i : Fin n, x i * v i := by
  simp only [jet, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]
  rfl

/-- `jet (fun i => junkP h i y)` applied to a basis vector. -/
theorem jet_single {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    jet v (Pi.single i 1) = v i := by
  rw [jet_apply]
  simp [Pi.single_apply]

end Work.WilG1.Cell
