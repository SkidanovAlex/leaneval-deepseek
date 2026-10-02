/-
# ELPull — the arithmetic of the two root angles under the angle-doubling map

The two root angles `α₁ = 371/1023`, `α₂ = 404/1023` of `Work.ELPull.Defs` are exchanged by
five iterates of the angle-doubling map `T θ = Int.fract (-2 θ)`:

| `j` | `T^[j] α₁` | `T^[j] α₂` |
|-----|------------|------------|
| 0   | `371/1023` | `404/1023` |
| 1   | `281/1023` | `215/1023` |
| 2   | `461/1023` | `593/1023` |
| 3   | `101/1023` | `860/1023` |
| 4   | `821/1023` | `326/1023` |
| 5   | `404/1023` | `371/1023` |

so `T^[5]` swaps `α₁` and `α₂` (the two rays form a period-`5` portrait pair), and for
`j ≤ 5` the two `j`-th iterates are distinct and lie in `[0,1)`.  Everything is a finite
computation with `Int.fract` at rational literals, discharged by `norm_num`.
-/
import Mathlib
import Submission.Work.ELPull.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELPull

theorem alpha_iter_arith :
    (∀ j : ℕ, j ≤ 5 → (T^[j]) alpha1 ∈ Set.Ico 0 1 ∧ (T^[j]) alpha2 ∈ Set.Ico 0 1 ∧
      (T^[j]) alpha1 ≠ (T^[j]) alpha2) ∧
    (T^[5]) alpha1 = alpha2 ∧ (T^[5]) alpha2 = alpha1 := by
  constructor
  · intro j hj
    interval_cases j <;>
      refine ⟨?_, ?_, ?_⟩ <;>
      norm_num [T, alpha1, alpha2, Int.fract,
        Function.iterate_succ_apply', Function.iterate_zero]
  · constructor <;>
      norm_num [T, alpha1, alpha2, Int.fract,
        Function.iterate_succ_apply', Function.iterate_zero]

end Work.ELPull
