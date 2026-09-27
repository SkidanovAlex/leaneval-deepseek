import Mathlib
import Submission.Work.Mostow.visualDefs
import Submission.Work.Mostow.BoostTransitive

/-!
# Transitivity of the `PO(n,1)`-action on hyperbolic space

Given the group-action interface `POActionProp n`, the projective orthogonal group `PO n 1`
acts transitively on the hyperboloid chart `E n`: every point `u` is the image of the base
point `0` under some `g : PO n 1`.

The work is done in `Submission.Work.Mostow.BoostTransitive`, where the explicit boosts
`boostO (‖u‖⁻¹ • u) ‖u‖ (tpart u)` — the matrices
`fromBlocks (1 + (t-1) • (e eᵀ)) (r e) (r eᵀ) (t)` with `t² - r² = 1` — are shown to lie in
`O(n,1)` and to send `0` to `r • e`, and the first conjunct of `BoostTransitive n hA` is
precisely the statement below.
-/

namespace Work.Mostow

theorem poTransitive (n : ℕ) (hn : 1 ≤ n) (hA : Submission.Mostow.POActionProp n) :
    ∀ u : Submission.Mostow.E n, ∃ g : LeanEval.Geometry.MostowRigidity.PO n 1,
      g • (0 : Submission.Mostow.E n) = u :=
  (BoostTransitive n hA).1

end Work.Mostow
