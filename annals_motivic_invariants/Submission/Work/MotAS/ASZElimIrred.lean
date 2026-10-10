import Mathlib
import Submission.Work.MotAS.ASZElimData
import Submission.Work.MotAS.ASZElimIrredA0
import Submission.Work.MotAS.ASZElimIrredB0
import Submission.Work.MotAS.ASZElimIrredGen

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASZElimIrred`

The eliminant `ASZElim.P a b g` of the characteristic-`5` (Artin–Schreier) residual chart is
irreducible.

The proof splits the problem into its three cases, each proved in its own module (see
`Submission/Work/MotAS/GUIDE_ASZElimIrred.md` for the mathematics):

* `Work.MotAS.ASZElimIrredA0` — `a = 0` (then `ha` forces `b ≠ 0`); there `P 0 b g = C (b ^ 5) * Q`
  and `Q` factors over the Artin–Schreier extension `K(θ)`, `θ ^ 5 - θ = g`, into five conjugate
  linear-in-`X₀` factors, whence irreducibility by the orbit argument `ASZElimSigmaIrr`;
* `Work.MotAS.ASZElimIrredB0` — `b = 0` (then `a ≠ 0`), the mirror image with the identity
  `(θ+i)^3 - (θ+i)`;
* `Work.MotAS.ASZElimIrredGen` — `a * b ≠ 0`, the general position, where `P` is even absolutely
  irreducible and a shape-lemma computation is needed.

Since in characteristic `5` the hypothesis `a ^ 2 - a * b - b ^ 2 ≠ 0` is `(a + 2 * b) ^ 2 ≠ 0`, the
case `a = b = 0` is excluded, and the three cases above are exhaustive: if `b = 0` then `a ≠ 0`; if
`b ≠ 0` and `a = 0` we are in the first case; otherwise in the third.
-/

namespace Work.MotAS

theorem ASZElimIrred (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    Irreducible (Work.MotAS.ASZElim.P a b g) := by
  by_cases hb : b = 0
  · subst hb
    refine ASZElimIrredB0 K a g ?_ hg
    intro h0
    exact ha (by rw [h0]; ring)
  · by_cases ha0 : a = 0
    · subst ha0
      exact ASZElimIrredA0 K b g hb hg
    · exact ASZElimIrredGen K a b g ha ha0 hb hg

end Work.MotAS
