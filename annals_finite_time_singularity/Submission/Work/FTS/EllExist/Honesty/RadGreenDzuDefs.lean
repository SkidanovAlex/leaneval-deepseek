/-
# `Work.FTS.EllExist.Honesty.RadGreenDzuDefs` — the univariate operator `(z ∂_z)^i`

The radial-differentiation estimates for `radGreen` are naturally phrased for the *univariate*
operator `D_z = z ∂_z`, applied to `z`-only functions.  This file sets up that operator as `Dzu`
and records the two structural facts that every consumer needs:

* `DzIter_zOnly` — `Dzu` is the restriction of the curried operator `Work.Spaces.DzIter` to
  `z`-only functions;
* `measurable_Dzu_succ` — `Dzu i g` is Borel measurable for `i ≥ 1` **with no hypothesis on `g`**
  (each step multiplies `deriv` of the previous iterate by the continuous function `z ↦ z`, and
  `deriv` is always Borel measurable in Mathlib: `measurable_deriv`).
-/
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.EllExist.Honesty

set_option autoImplicit false

/-- The univariate operator `Dzu i = (z ∂_z)^i` on functions of the radial variable `z`. -/
def Dzu : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, g => g
  | n + 1, g => fun z => z * deriv (Dzu n g) z

@[simp] theorem Dzu_zero (g : ℝ → ℝ) : Dzu 0 g = g := rfl

@[simp] theorem Dzu_succ (n : ℕ) (g : ℝ → ℝ) :
    Dzu (n + 1) g = fun z => z * deriv (Dzu n g) z := rfl

/-- `Dzu 1 g z = z g'(z)`. -/
theorem Dzu_one_apply (g : ℝ → ℝ) (z : ℝ) : Dzu 1 g z = z * deriv g z := rfl

/-- `Dzu` is the restriction of the curried operator `DzIter` to `z`-only functions. -/
theorem DzIter_zOnly (i : ℕ) (g : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter i (fun z' _ => g z') z θ = Dzu i g z := by
  induction i generalizing z with
  | zero => rfl
  | succ n ih =>
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz, Dzu_succ]
      have hfun : (fun z' => Work.Spaces.DzIter n (fun z' _ => g z') z' θ) = Dzu n g :=
        funext fun z' => ih z'
      rw [hfun]

/-- `Dzu i g` is Borel measurable for `i ≥ 1`, with no hypothesis on `g`. -/
theorem measurable_Dzu_succ (i : ℕ) (g : ℝ → ℝ) : Measurable (Dzu (i + 1) g) := by
  cases i with
  | zero =>
      rw [show Dzu (0 + 1) g = fun z => z * deriv g z from Dzu_succ 0 g]
      exact measurable_id.mul (measurable_deriv g)
  | succ n =>
      rw [show Dzu (n + 1 + 1) g = fun z => z * deriv (Dzu (n + 1) g) z from Dzu_succ (n + 1) g]
      exact measurable_id.mul (measurable_deriv (Dzu (n + 1) g))

/-- The `AEStronglyMeasurable` form of `measurable_Dzu_succ`. -/
theorem aestronglyMeasurable_Dzu_succ (i : ℕ) (g : ℝ → ℝ) (μ : Measure ℝ) :
    AEStronglyMeasurable (Dzu (i + 1) g) μ :=
  (measurable_Dzu_succ i g).aestronglyMeasurable

end Work.FTS.EllExist.Honesty
