import Mathlib
import ChallengeDeps
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AK
import Submission.Work.MotC5N3.CensusAux
import Submission.Work.MotAS.censusAS2_fwVec0_ne_zero

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The non-vanishing conjuncts of the generic AS census whose engine is already generic

`Work.MotAS.censusAS2_fwVec0_ne_zero` proves `fwVecAS2 a b g 0 ≠ 0` for *free* coordinates
`(a, b, g) : K` with `a b ≠ 0` and `a ^ 2 - a * b - b ^ 2 ≠ 0`
(`Work.MotAS.fwVecAS2_zero_ne_zero_gen`), so its census specialisation to the Klein data
`(aK K D, bK K D, g)` is immediate and is given here.

The two further factors of the divisors — `sAS2` and `bwVecAS2 · 4` — are *not* covered by the
source's argument at a general class `g` (the source evaluates the polynomial at a single chart
point, which happens to be legitimate for `g = fAS 𝕜`), and are the deliverables of the
submodules `Work.MotC5N3.sAS2_ne_zero` and `Work.MotC5N3.bwVecAS2_four_ne_zero`; here they are
taken as hypotheses, so that the divisor assembly `FdivAS2_ne_zero_of` / `GdivAS2_ne_zero_of` of
`Submission/Work/MotC5N3/CensusAux.lean` can be instantiated either way.
-/

set_option autoImplicit false

namespace Work.MotC5N3
noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- **The `0`-th component of the forward chart denominator is nonzero** for the census data:
the generic `Work.MotAS.fwVecAS2_zero_ne_zero_gen` at `aK K D`, `bK K D`, `g`. -/
theorem fwVecAS2_zero_ne_zero (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜]
    [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g) :
    Work.MotAS.fwVecAS2 (aK K D) (bK K D) g 0 ≠ 0 :=
  Work.MotAS.fwVecAS2_zero_ne_zero_gen (aK K D) (bK K D) g
    (aK_ne_zero (K := K) D hD) (bK_ne_zero (K := K) D hD) (aK_sq_sub_ne D hD)

/-- **The source divisor of the generic census is nonzero**, given the non-vanishing of its middle
factor `sAS2`. -/
theorem FdivAS2_ne_zero (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜]
    [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g)
    (hs : Work.MotAS.sAS2 (aK K D) (bK K D) g ≠ 0) :
    Work.MotAS.FdivAS2 (aK K D) (bK K D) g ≠ 0 :=
  FdivAS2_ne_zero_of (aK K D) (bK K D) g (aK_sq_sub_ne D hD)
    (fwVecAS2_zero_ne_zero K D hD g hg) hs

/-- **The target divisor of the generic census is nonzero**, given the non-vanishing of its two
non-unit factors `bwVecAS2 · 4` and `sdualAS2`. -/
theorem GdivAS2_ne_zero (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜]
    [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hbw : Work.MotAS.bwVecAS2 (aK K D) (bK K D) g 4 ≠ 0)
    (hsd : Work.MotAS.sdualAS2 (aK K D) (bK K D) g ≠ 0) :
    Work.MotAS.GdivAS2 (aK K D) (bK K D) g ≠ 0 :=
  GdivAS2_ne_zero_of (aK K D) (bK K D) g (aK_sq_sub_ne D hD) hbw hsd

/-- **`sdualAS2 ≠ 0`** from the height-one clause of the census. -/
theorem sdualAS2_ne_zero (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜]
    [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) (g : K)
    (hht : Ideal.height (Ideal.span {Work.MotAS.sdualAS2 (aK K D) (bK K D) g}) = 1) :
    Work.MotAS.sdualAS2 (aK K D) (bK K D) g ≠ 0 :=
  sdualAS2_ne_zero_of_height (aK K D) (bK K D) g hht

end
end Work.MotC5N3
