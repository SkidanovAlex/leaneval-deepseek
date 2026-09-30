import Mathlib
import Submission.Work.Curvature.Basic
import Submission.Work.Curvature.Deriv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Koszul formula for the upper half space Christoffel symbol

This file verifies that the explicit symbol `chrUHS` of `Work.Curvature.Basic`
really is the Christoffel symbol of the upper half space metric `uhsMetric`:
for `s = q 3 ≠ 0` and all `a b c`,

`uhsMetric q (chrUHS q a b) c = koszulRHS uhsMetric q a b c`,

i.e. `∇_{∂_a} ∂_b` satisfies the Koszul formula against the metric.  Both sides
reduce, using `dG_uhsMetric` of `Work.Curvature.Deriv`, to the pure monomial
identity

`s⁻³ · ⟪chrUHSvec a b, c⟫ = −s⁻³ · (b₃⟪a,c⟫ + a₃⟪b,c⟫ − c₃⟪a,b⟫)`.
-/

open scoped RealInnerProductSpace

namespace Work.Curvature

noncomputable section

/-- The inner product of `chrUHSvec a b` with `c`, written out in coordinates. -/
lemma inner_chrUHSvec (a b c : E4) :
    ⟪chrUHSvec a b, c⟫
      = -(a 0 * b 3 + a 3 * b 0) * c 0 - (a 1 * b 3 + a 3 * b 1) * c 1
        - (a 2 * b 3 + a 3 * b 2) * c 2
        + (a 0 * b 0 + a 1 * b 1 + a 2 * b 2 - a 3 * b 3) * c 3 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_four, chrUHSvec]
  simp
  ring

/-- **Koszul formula for the UHS Christoffel symbol.** -/
theorem uhsMetric_chrUHS_koszul (q : E4) (hq : q 3 ≠ 0) (a b c : E4) :
    uhsMetric q (chrUHS q a b) c = koszulRHS uhsMetric q a b c := by
  rw [koszulRHS, dG_uhsMetric a c b q hq, dG_uhsMetric b c a q hq, dG_uhsMetric a b c q hq,
    uhsMetric_apply, chrUHS, real_inner_smul_left, inner_chrUHSvec]
  simp only [PiLp.inner_apply, Fin.sum_univ_four, RCLike.inner_apply, starRingEnd_apply,
    star_trivial]
  ring

end

end Work.Curvature
