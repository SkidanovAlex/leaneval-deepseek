import Mathlib
import Submission.Work.Drive.CappingSpace
import Submission.Work.Drive.exists_continuous_chordDir

/-!
# The unit chord direction of a plane curve, and its relation to the doubled direction `dirC`

The configuration data of a pair of curve points `(x, y)` records the *doubled* direction
`dirC (γ x - γ y) ∈ ℝ/ℤ` of the chord (`Submission.Collision.dirC`, whose value at a vector
`v ≠ 0` is the class of `arg v / π`), i.e. the unit complex number `((γ x - γ y)/‖γ x - γ y‖) ^ 2`
with the **Euclidean** norm.

The chain route of the total-order chapter needs, instead, a *halving* of that class: an honest
complex number `u` with `u ^ 2 = circleOf (dirC (γ x - γ y))`, smooth in `(x, y)` off the diagonal and
carried as part of the parametrisation (`Submission/Work/Drive/CAPPING_ANALYSIS.md` §2).  The natural
choice is the undoubled chord direction `u = (γ x - γ y)/‖γ x - γ y‖`, which is what this file
defines as `Work.Drive.chordUnitDir`.

Warning (the reason `chordUnitDir` is written with the *complex* norm): `ℝ × ℝ` carries the **sup**
norm in Mathlib (`Prod.norm_def`), so the halving identity is false if the denominator is the norm of
the pair; it must be the Euclidean norm of the vector, i.e. `‖(⟨v.1, v.2⟩ : ℂ)‖`.
-/

namespace Work.Drive

noncomputable section

open Manifold
open scoped Manifold ContDiff

/-- The chord vector of the pair of parameters `p`, read as a complex number (so that `‖·‖` is the
**Euclidean** norm, not the sup norm of `ℝ × ℝ`). -/
def chordC (γ : Circle → ℝ × ℝ) (p : ℝ × ℝ) : ℂ :=
  ⟨(γ (Circle.exp p.1) - γ (Circle.exp p.2)).1, (γ (Circle.exp p.1) - γ (Circle.exp p.2)).2⟩

/-- The unit complex number in the direction of the chord of the pair `p`: the *halving* of the
doubled direction `dirC` of that chord. -/
def chordUnitDir (γ : Circle → ℝ × ℝ) (p : ℝ × ℝ) : ℂ :=
  chordC γ p / ((‖chordC γ p‖ : ℝ) : ℂ)

end

end Work.Drive
