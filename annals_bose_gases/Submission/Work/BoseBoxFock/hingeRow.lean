import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.sTailRow
import Submission.Work.BoseBoxFock.tauPhi_row_lattice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.hingeRow` — the **hinge** residual of the `tauPhi_row` chapter

`Work.BoseBoxFock.tauPhi_row` asks for the lattice row at the *smoothed* profile
`c²·tauPhi(‖k_n‖/c)` against the continuum integral at the sharp symbol
`fsKinCoeff c r = (max 0 (r-c))²`.  The smoothing is supported in the frequency band
`5c/4 ≤ r ≤ 7c/4`, and the exact profile identity (`tauPhiBand.lean`) shows

    c²·tauPhi(r/c) ≤ (max 0 (r - 5c/4))²       for every `c > 0`, `r ≥ 0`

(`rescaled_tauPhi_le_conv`, PROVED in `tauPhi_row.lean`).  Hence the row is implied by the
single **elementary** statement below, in which *no smoothing profile, kernel or Bessel
function occurs*: the lattice content of the **hinge** at `5c/4` is dominated by the continuum
content of the **hinge** at `c`.

## Why the threshold `5c/4` and not `c`

* `5c/4` is the *smallest* shift for which the pointwise domination
  `c²·tauPhi(r/c) ≤ (max 0 (r−κ))²` can hold for all `r ≥ 0` (the profile is strictly positive on
  `r > 5c/4`, so `κ < 5c/4` fails there);
* `c` is the *largest* shift for which the right-hand side is the sharp symbol of the target.

So the pair `(κ, c) = (5c/4, c)` is the only pair for which the hinge statement is both implied
by the row's own pointwise data and sufficient for the row.

## This is a *known* corpus statement

`hingeRow` is exactly `Work.BoseBoxFock.sTailRow` — the reduced form `(S′)` of
`Work.BoseBoxFock.sharpShiftRow` at its worst threshold `λ = 5c/4` — with the support class
weakened from `closedBall 0 (ℓ/2)` to the target's own `ball 0 (ℓ/2)` (one line:
`Metric.ball_subset_closedBall`).  So this node is *not* a new mathematical obligation; it is the
connection between the present chapter and the corpus's `sharpShiftRow` node, and the whole
weight of the residual sits there (see `FINDING_sharpShiftRow.md` for the numerical verification,
the exact reductions `(♣)`, `(♣♣)`, `(S)`, `(S′-eq)`, the `8 % – 76 %` slack of `(S)`/`(S′)`, and
the refuted sub-statements `(H″)`, `(♡)`, `(S″)`, `λ = c`).

**Consequence for the corpus (answers the open question of `FINDING_sharpShiftRow.md` §5.1).**
That finding asked "whoever needs `(T)`: check whether the application allows `cℓ ≤ 4π`".  The
answer is: `Work.BoseBoxFock.tauPhi_row` needs `(T)` in the **`cℓ ≥ 4π`** regime (the sharp one),
at `λ = 5c/4`, with the open ball.  So `(T)` is genuinely on the critical path of the project and
cannot be replaced by its easy `cℓ ≤ 4π` relative.
-/

noncomputable section

open scoped Real BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The hinge residual**, in the exact spelling consumed by `tauPhi_row_of_hinge`.
It is `Work.BoseBoxFock.sTailRow` (the corpus's `(S′)` node) transported from the closed ball to
the open ball, and with `fsKinCoeff (5c/4)` unfolded. -/
theorem hingeRow {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (hcℓ : 4 * Real.pi ≤ c * ℓ)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g)
    (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2)) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (max 0 (‖Work.BoseBoxFock.kmomInt ℓ n‖ - 5 * c / 4)) ^ 2 *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : E3,
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  have h := sTailRow (ℓ := ℓ) (c := c) hℓ hc hcℓ hg hgc
    (hgsupp.trans Metric.ball_subset_closedBall)
  have h1 : sTailLat ℓ (5 * c / 4) g
      = ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
          (max 0 (‖Work.BoseBoxFock.kmomInt ℓ n‖ - 5 * c / 4)) ^ 2 *
          ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2 := by
    rw [sTailLat]
    refine tsum_congr (fun n => ?_)
    rw [Submission.BoseGases.fsKinCoeff, max_comm]
  have h2 : sTailCont c g
      = ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : E3,
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := rfl
  rw [h1, h2] at h
  exact h

end Work.BoseBoxFock
