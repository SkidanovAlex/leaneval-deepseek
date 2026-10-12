import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.LatVec
import Submission.Work.BoseBoxFock.PhiTaylorQuant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.AliasDefs` — the autocorrelation kernel of the aliasing identity

For `g : ℝ³ → ℂ` put `A g u = ∫_x g x · conj (g (x − u))` (the **autocorrelation**).  Its
(complex) Fourier transform in the `p`-convention of `kinFT` is `‖kinFT g p‖²`:

    F p = ‖kinFT g p‖² = ∫_u A g u · exp (−I⟪p,u⟫) .

Whenever `tsupport g ⊆ ball 0 (ℓ/2)`:

* `A g` is supported in `‖u‖ ≤ ℓ` (the overlap of the ball with its translate is empty beyond);
* `A g (ℓ • vec m) = 0` for every `m ≠ 0` (the translates of `ball 0 (ℓ/2)` touch only at single
  points, so the overlap is a null set).

Consequently the difference of the two heat contents is a *lattice sum over the images only*:

    latHeat ℓ t g − contHeat g t = Σ_{m ≠ 0} ∫_u aliasKernel g u · heatK t (ℓ • vec m − u) ,

which is the starting point of the middle-range comparison (`FINDING_deficitAlias_weak.md` §6).
-/

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators Real

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The **autocorrelation** `A g u = ∫_x g x · conj (g (x − u))`.  Its `p`-Fourier transform is
`‖kinFT g p‖²`. -/
noncomputable def autocorr (g : E3 → ℂ) (u : E3) : ℂ :=
  ∫ x : E3, g x * starRingEnd ℂ (g (x - u))

/- The integer lattice vector `latVec` (and its evaluation lemma) now live in the Mathlib-only
module `Submission.Work.BoseBoxFock.LatVec`, so that the `farKernel_*` development does not
depend on the aliasing chapter. -/

/-- The **real part** of the autocorrelation: the real kernel of the aliasing identity
`Λ(t) − R(t) = Σ_{m≠0} ∫_u aliasKernel g u · heatK t (ℓ m − u)`. -/
noncomputable def aliasKernel (g : E3 → ℂ) (u : E3) : ℝ := (autocorr g u).re

end Work.BoseBoxFock
