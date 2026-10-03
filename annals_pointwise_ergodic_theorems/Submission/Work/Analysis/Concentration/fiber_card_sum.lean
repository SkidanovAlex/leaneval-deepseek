import Mathlib
import Submission.Work.Analysis.Concentration.Basic

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The total mass of the fibre counting function

`fiber_card_sum`: for every polynomial `P : ℤ[X]` and every `Q ≠ 0`, the fibre
counting function `h(y) = polyFiberCard P Q y = #{x ∈ ℤ/Qℤ : P(x) = y}` of
Appendix C of Krause–Mirek–Tao sums to `Q` over `y ∈ ℤ/Qℤ`.

This is the double-counting identity: summing the cardinalities of the fibres of
the map `x ↦ P(x)` over all `y` counts every `x ∈ ℤ/Qℤ` exactly once, namely
via `y = P(x)`.  (Note that this is the *total* mass, `∑_y h(y) = Q`; the
interesting content of Appendix C is the *distribution* of `h`.)
-/

namespace Work.Analysis.Concentration

lemma fiber_card_sum (P : Polynomial ℤ) (Q : ℕ) [NeZero Q] :
    ∑ y : ZMod Q, polyFiberCard P Q y = Q := by
  classical
  -- Rewrite each fibre cardinality as a sum of ones over the fibre.
  have hcard : ∀ t : Finset (ZMod Q), t.card = ∑ _x ∈ t, (1 : ℕ) :=
    fun t => by simp [Finset.sum_const]
  simp only [polyFiberCard, hcard]
  -- Double counting (Finset.sum_fiberwise): summing the fibre sizes over all
  -- `y` counts every `x` exactly once, through `y = P(x)`.
  rw [Finset.sum_fiberwise (s := (Finset.univ : Finset (ZMod Q)))
      (g := fun x => polyEvalZMod P Q x) (f := fun _ => 1)]
  simp

end Work.Analysis.Concentration
