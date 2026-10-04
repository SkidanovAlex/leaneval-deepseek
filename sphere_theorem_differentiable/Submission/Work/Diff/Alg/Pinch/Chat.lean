import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Strict

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Böhm–Wilking/Brendle–Schoen pinching family `Ĉ(s)`

Brendle–Schoen §3 construct a one-parameter family of closed convex `O(n)`-invariant cones
`Ĉ(s)`, `s > 0`, shrinking (as `s → ∞`) to the ray `ℝ₊ · Iso` and filling up the interior of
`Ĉ` (as `s → 0⁺`), each of which is *transversally* invariant under the ODE `R' = Q(R)`:

* for `0 < s ≤ 1/2` (Brendle–Schoen Prop. 13, after Böhm–Wilking Lemma 3.4)
  `b = s`, `2a = (2s + (n-2)s²)/(1 + (n-2)s²)`, `p = 1 - 1/(1 + (n-2)s²)`;
* for `1/2 ≤ s` (Brendle–Schoen Prop. 14, after Böhm–Wilking Lemma 3.5)
  `b = 1/2`, `a = s`, `p = 1 - 4/(n - 2 + 8s)`.

Both pieces are the image of the cone `D(p) = Ĉ ∩ {Ric ≥ p·scal/n}` under `ell a b`.
This file (only) records the family; the structural and invariance statements live in the
companion modules.
-/

namespace Work.Diff.Alg.Pinch

open Submission.Diff.Alg

/-- The Brendle–Schoen pinching family of cones `Ĉ(s)`, `s > 0`. -/
noncomputable def Chat (n : ℕ) (s : ℝ) : Set (Curv4 n) :=
  if s ≤ 1 / 2 then
    Ccone (n := n) ((2 * s + ((n : ℝ) - 2) * s ^ 2) / (2 * (1 + ((n : ℝ) - 2) * s ^ 2))) s
      (1 - 1 / (1 + ((n : ℝ) - 2) * s ^ 2))
  else
    Ccone (n := n) s (1 / 2) (1 - 4 / ((n : ℝ) - 2 + 8 * s))

/-- The strict (interior) version of `Ĉ(s)`. -/
noncomputable def ChatS (n : ℕ) (s : ℝ) : Set (Curv4 n) :=
  if s ≤ 1 / 2 then
    CconeS (n := n) ((2 * s + ((n : ℝ) - 2) * s ^ 2) / (2 * (1 + ((n : ℝ) - 2) * s ^ 2))) s
      (1 - 1 / (1 + ((n : ℝ) - 2) * s ^ 2))
  else
    CconeS (n := n) s (1 / 2) (1 - 4 / ((n : ℝ) - 2 + 8 * s))

end Work.Diff.Alg.Pinch
