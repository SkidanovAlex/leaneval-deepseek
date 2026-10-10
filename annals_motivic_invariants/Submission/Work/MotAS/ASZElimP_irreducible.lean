import Mathlib
import Submission.Work.MotAS.ASZElimData
import Submission.Work.MotAS.ASZElimIrred

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASZElimP_irreducible`

The AS eliminant `ASZElim.P a b g ∈ K[X₀,X₁]` is irreducible over any field `K` of characteristic
`5`, for `a² - ab - b² ≠ 0` and `g ∉ ℘(K) = {c⁵ - c}`.

This is `Work.MotAS.ASZElimIrred` (`Submission/Work/MotAS/ASZElimIrred.lean`, proved
sorry-free in the same generality), whose proof splits into the three cases `b = 0`,
`a = 0` and `ab ≠ 0` and uses `Work.MotAS.ASZElimIrredGen` (the Artin–Schreier extension
`K[θ]/(θ⁵-θ-g)` and a Galois/degree argument) together with the two corner lemmas
`Work.MotAS.ASZElimIrredB0` and `Work.MotAS.Corners.elimIrredA0`.
-/

namespace Work.MotAS

theorem ASZElimP_irreducible (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    Irreducible (Work.MotAS.ASZElim.P a b g) :=
  Work.MotAS.ASZElimIrred K a b g ha hg

end Work.MotAS
