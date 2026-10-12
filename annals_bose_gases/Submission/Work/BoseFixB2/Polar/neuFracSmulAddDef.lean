import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.Polar.neuFracSmulAddDef` — the `t`-parametrised `neuFrac` defect

Continuity of `t ↦ neuFrac ℓ a² u (t·f + g)` (`Work.BoseFixB2.Polar.neuFrac_continuous_smul`) is
proved by exhibiting that map as a *quadratic polynomial* in `t`.  The two ingredients are:

* `neuFracDefect ℓ a² u f g t = Q(t·f + g) − t² Q(f) − Q(g)` is **additive** in `t`
  (this is the parallelogram law `neuFrac_parallelogram` together with the `2`-homogeneity
  `neuFrac_const_mul`, re-arranged);
* `neuFracDefect` is **bounded above** on a neighbourhood of `0` (from the one-sided
  variational bound `neuFrac ≤ ∫_Λ φ²`),

and an additive function `ℝ → ℝ` that is bounded above on a neighbourhood of `0` is continuous.

This module contains only the vocabulary (`smulAdd`, `neuFracDefect`), so that the pieces of
the argument can be stated in a readable form.
-/

noncomputable section

namespace Work.BoseFixB2.Polar

set_option autoImplicit false

/-- The `t`-parametrised state `Φ_t = t·f + g` of the `neuFrac` continuity argument. -/
def smulAdd (t : ℝ) (f g : EuclideanSpace ℝ (Fin 3) → ℝ) :
    EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun z => t * f z + g z

/-- The **quadratic defect** of `neuFrac` along the line `t ↦ t·f + g`:
`R(t) = Q(t·f + g) − t²·Q(f) − Q(g)`.  `t ↦ R t` is additive (and hence linear) in `t`
by the parallelogram law; it is bounded above on a neighbourhood of `0` because
`neuFrac φ ≤ ∫_Λ φ²`. -/
def neuFracDefect (ℓ a2 : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    (f g : EuclideanSpace ℝ (Fin 3) → ℝ) (t : ℝ) : ℝ :=
  Work.BoseKinLoc.neuFrac ℓ a2 u (smulAdd t f g)
    - t ^ 2 * Work.BoseKinLoc.neuFrac ℓ a2 u f
    - Work.BoseKinLoc.neuFrac ℓ a2 u g

end Work.BoseFixB2.Polar
