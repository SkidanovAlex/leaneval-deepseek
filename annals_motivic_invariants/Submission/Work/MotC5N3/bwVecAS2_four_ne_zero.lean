import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AK
import Submission.Work.MotC5N3.CensusAux
import Submission.Work.MotAS.BwASDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3

/-- **The inverse chart denominator of the generic AS census does not vanish**: for the census
coordinates `aK K D`, `bK K D` (`Submission/Work/MotC5N3/AK.lean`) and any class `g ∉ ℘(K)`,
`bwVecAS2 (aK K D) (bK K D) g 4` is a nonzero polynomial.

This is the non-vanishing input of `GdivAS2_ne_zero_of` (`Submission/Work/MotC5N3/CensusAux.lean`),
hence of the `GdivAS2 ≠ 0` conjunct of `Work.MotC5N3.CensusAS2Gen`, and the `RatFunc 𝕜 ↦ K` fork of
`Work.MotAS.censusAS2_bwVec4_ne_zero` (`g = fAS 𝕜` there).

Both reviewers established that this is a *short* corollary of results already in the workspace, and
that no Gröbner-basis argument is needed (the source's evaluation at the single chart point
`(0,0,1)` is *not* the right argument for a general `g`, but a coefficient argument is):

* `Work.MotAS.bwVecAS2_four_eq_bwASpoly` (`Submission/Work/MotAS/BwASDefs.lean`) identifies
  `bwVecAS2 a b g 4` with `bwASQ + bwASR`, a cubic form in the three chart variables whose
  coefficients do not involve `g`;
* `Work.MotAS.bwASpoly_ne_zero (hd : Work.MotAS.asDel a b ≠ 0)` proves the resulting cubic nonzero
  (its `X0 * X2`-coefficient is `-(a ^ 2 - a * b - b ^ 2) ^ 2`, resp. its `X2 ^ 3`-coefficient is
  `-g * (a ^ 2 - a * b - b ^ 2) ^ 2`).

So it suffices to transport `bwASpoly_ne_zero` along `bwVecAS2_four_eq_bwASpoly` and to supply
`Work.MotC5N3.aK_sq_sub_ne D hD` (equivalently `Work.MotAS.asDel (aK K D) (bK K D) ≠ 0`).  Note
that `g` is irrelevant to the conclusion — `hg` encodes only the census interface, and `g` is
nonzero because `u = 0` gives `0 ^ 5 - 0 = 0`.  (Careful: the coordinate form with only
`a ≠ 0, b ≠ 0` is *false* in characteristic `5`, e.g. `K = ZMod 5`, `a = 1`, `b = 2`, `g = 0`; the
hypothesis `a ^ 2 - a * b - b ^ 2 ≠ 0` is essential and is exactly what `ASGood D` supplies.)

Deliverable: namespace `Work.MotC5N3`, file `Submission/Work/MotC5N3/bwVecAS2_four_ne_zero.lean`
(helpers in sibling files), sorry-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`). -/
theorem bwVecAS2_four_ne_zero (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜]
    [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g) :
    Work.MotAS.bwVecAS2 (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g 4 ≠ 0 := by
  rw [Work.MotAS.bwVecAS2_four_eq_bwASpoly]
  refine Work.MotAS.bwASpoly_ne_zero (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g ?_ ?_
  · simpa only [Work.MotAS.asDel] using Work.MotC5N3.aK_sq_sub_ne (K := K) D hD
  · intro hg0
    exact hg ⟨0, by rw [hg0]; simp⟩

end Work.MotC5N3
