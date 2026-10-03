import Mathlib
import Submission.Work.ORLocInd.Howie.Basic
import Submission.Work.ORLocInd.Howie.LabellingAux

namespace Work.ORLocInd.Howie

open _root_.Quiver

universe u

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- Associativity of `pmul` with a concatenation of paths: `(p · q) · r = p · (q ++ r)`.
Both sides are the groupoid product of `p`, `q` and `r` in this order. -/
theorem pmul_pmul_comp {a b c d : V} (p : Quiver.Path a b) (q : Quiver.Path b c)
    (r : Quiver.Path c d) : pmul (pmul p q) r = pmul p (q.comp r) := by
  rw [pmul_assoc]
  exact pmul_red_right p (q.comp r)

/-- The inverse of `γ` followed by `γ · q` reduces to `q`: this is the cancellation of the
backtrack `γ⁻¹ · γ` inside the groupoid product. -/
theorem pmul_rev_mul {x b c : V} (γ : Quiver.Path x b) (q : Quiver.Path b c) :
    pmul γ.reverse (pmul γ q) = red q := by
  rw [← pmul_assoc, pmul_reverse_left, pmul_nil_left]

/-- **Compatibility of the conjugation `p ↦ δ · p · γ⁻¹` with composition.**  Conjugating the
concatenation `p · q` by `δ` and `ε` is the same as conjugating `p` by `δ` and `γ`, conjugating
`q` by `γ` and `ε`, and multiplying the two results in the vertex group at the base point. -/
theorem pmul_conj_comp {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] {x a b c : V}
    (δ : Quiver.Path x a) (γ : Quiver.Path x b) (ε : Quiver.Path x c)
    (p : Quiver.Path a b) (q : Quiver.Path b c) :
    Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.pmul δ p) γ.reverse)
      (Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.pmul γ q) ε.reverse)
      = Work.ORLocInd.Howie.pmul (Work.ORLocInd.Howie.pmul δ (p.comp q)) ε.reverse := by
  -- Push the product `(δ · p · γ⁻¹) · (γ · q · ε⁻¹)` into a single left-associated chain of
  -- `pmul`s ending with `ε⁻¹`; the middle factor then collapses by cancellation of `γ⁻¹ · γ`.
  rw [← pmul_assoc (pmul (pmul δ p) γ.reverse) (pmul γ q) ε.reverse]
  have h : pmul (pmul (pmul δ p) γ.reverse) (pmul γ q) = pmul δ (p.comp q) := by
    rw [pmul_assoc (pmul δ p) γ.reverse (pmul γ q), pmul_rev_mul, pmul_red_right,
      pmul_pmul_comp]
  rw [h]

end Work.ORLocInd.Howie
