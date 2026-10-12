import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxD1Pair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxPairIntGenC2.EvenC2Defs` — the indicator-free box pair fibre

The peeled box pair fibre of `Work.BoseFixB1.boxPairFibreFun` is

    `boxPairFibreFun volA ℓ A Φ i j y z = ∫_{r2 ∈ abox N ℓ} P_iP_jΦ(x)·Q_jQ_iΦ(x)`,
    `x = ins2 i j' y z r2`, `j = i.succAbove j'`,

and the two-box projection identities `Work.BoseFixB1S.boxPInd_twoMean` and
`Work.BoseFixB1S.boxQInd_boxQInd_twoMean` factor the integrand as

    `Aind A y · Aind A z · (M_iM_jΦ)(x) · (Φ(x) − M_iΦ(x) − M_jΦ(x) + M_jM_iΦ(x))`,

with `M_i = Work.BoseFixB1S.oneMean volA A i` the unwindowed slot mean and
`M_iM_j = Work.BoseFixB1S.twoMean volA A i j` the two-slot mean.

This module contains only the *indicator-free* part of that factorization, as a function of the
two distinguished values: `evenC2Integrand` is the second factor at the configuration `x`, and
`evenC2Free` is its `abox N ℓ`-integral at the double insertion `ins2 i j' y z ·`.  The point of
these definitions is that `evenC2Free`, unlike `boxPairFibreFun`, is a *continuous* function of
the pair `(y,z)` (it carries no box indicators), which is what lets a.e. identities for it be
upgraded to identities valid everywhere.

The companion lemmas (the factorization `boxPairFibreFun = Aind·Aind·evenC2Free`, the continuity
of `evenC2Free`, and the two-peel weighted symmetry of `evenC2Free`) live in the sibling modules.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1.BoxPairIntGenC2

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The *indicator-free* peeled pair integrand of the box projections at the slots
`(i, i.succAbove j')`: the product of the two-slot mean `M_iM_jΦ` and of the mean-free
combination `Φ − M_iΦ − M_jΦ + M_jM_iΦ` at the configuration `x`. -/
noncomputable def evenC2Integrand {N : ℕ} (volA : ℝ) (A : Set E3)
    (Φ : Submission.BoseGases.X (N + 2) → ℝ) (i : Fin (N + 2)) (j' : Fin (N + 1))
    (x : Submission.BoseGases.X (N + 2)) : ℝ :=
  Work.BoseFixB1S.twoMean volA A i (i.succAbove j') Φ x
    * (Φ x
        - Work.BoseFixB1S.oneMean volA A (i.succAbove j') Φ x
        - Work.BoseFixB1S.oneMean volA A i Φ x
        + Work.BoseFixB1S.twoMean volA A i (i.succAbove j') Φ x)

/-- The *indicator-free* peeled box pair fibre at the slots `(i, i.succAbove j')` and the
distinguished values `y`, `z`: the `abox N ℓ`-integral of `evenC2Integrand` at the double
insertion `ins2 i j' y z ·`. -/
noncomputable def evenC2Free {N : ℕ} (volA ℓ : ℝ) (A : Set E3)
    (Φ : Submission.BoseGases.X (N + 2) → ℝ) (i : Fin (N + 2)) (j' : Fin (N + 1))
    (y z : E3) : ℝ :=
  ∫ r2 in Submission.BoseGases.abox N ℓ,
    evenC2Integrand volA A Φ i j' (Submission.BoseGases.ins2 i j' y z r2)

end Work.BoseFixB1.BoxPairIntGenC2
