/-
# Conjugating a path by `δ` and by `γ`: `(δ · p · γ⁻¹) · (γ · p⁻¹ · δ⁻¹) = 1`

This is the path-level cancellation identity behind the fact that `conjElem` sends reversals to
inverses (`isBalanced_labOf`), in a form that does not require the graph to be connected: the two
"conjugating" paths `δ : x → a` and `γ : x → b` are given independently.

When `δ = d a` and `γ = d b` for chosen paths `d y : v → y` (a connected graph) it specialises to
`pmul_conjPath_reverse`; when `a = b` and `δ = γ` it says that a conjugate of `p` cancels against
the conjugate of `p⁻¹`.

The proof is a telescoping computation: push the two factors into a single left-associated chain of
`pmul`s, cancel the backtracks `p · p⁻¹` and `γ⁻¹ · γ` (`pmul_reverse`, `pmul_reverse_left`), and
use `pmul_red_left`/`pmul_red_right` to absorb the `red`s that the cancellation introduces.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Basic
import Submission.Work.ORLocInd.Howie.LabellingAux

universe u

namespace Work.ORLocInd.Howie

theorem pmul_conj_reverse {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] {x a b : V}
    (δ : Quiver.Path x a) (γ : Quiver.Path x b) (p : Quiver.Path a b) :
    Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.pmul δ p) γ.reverse)
      (Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.pmul γ p.reverse) δ.reverse)
      = Quiver.Path.nil := by
  -- `(p · γ⁻¹) · γ` cancels to the reduced form of `p`.
  have step4 : pmul (pmul p γ.reverse) γ = red p := by
    rw [pmul_assoc p γ.reverse γ, pmul_reverse_left γ, pmul_nil_right]
  -- `p · (p⁻¹ · δ⁻¹)` cancels to the reduced form of `δ⁻¹`.
  have step6 : pmul p (pmul p.reverse δ.reverse) = red δ.reverse := by
    rw [← pmul_assoc p p.reverse δ.reverse, pmul_reverse p, pmul_nil_left]
  rw [pmul_assoc δ p γ.reverse, pmul_assoc γ p.reverse δ.reverse,
    pmul_assoc δ (pmul p γ.reverse) (pmul γ (pmul p.reverse δ.reverse)),
    ← pmul_assoc (pmul p γ.reverse) γ (pmul p.reverse δ.reverse),
    step4, pmul_red_left p (pmul p.reverse δ.reverse),
    step6, pmul_red_right δ δ.reverse, pmul_reverse δ]

end Work.ORLocInd.Howie
