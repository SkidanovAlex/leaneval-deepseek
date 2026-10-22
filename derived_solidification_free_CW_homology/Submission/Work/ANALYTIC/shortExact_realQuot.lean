import Mathlib
import Submission.Work.ANALYTIC.RealSide
import Submission.Work.ANALYTIC.prodReal_rounding
import Submission.Work.ANALYTIC.exact_of_isPullback
import Submission.Work.ANALYTIC.epi_zToRealQuot
import Submission.Work.ANALYTIC.isPullback_realSide

/-!
# The short exact sequence `∏^bnd ℤ ⟶ ∏ℤ ⟶ ∏ℝ/∏^bnd ℝ` (AN2, REFS/03 §3)

The main result of this file is

`shortExact_realQuot : (ShortComplex.mk boundedSeqIncl zToRealQuot ...).ShortExact`,

i.e. the sequence

`∏^bnd ℤ --boundedSeqIncl--> ∏ℤ --zToRealQuot--> ∏ℝ/∏^bnd ℝ`

of light condensed abelian groups (`Submission/Work/ANALYTIC/RealSide.lean`, `REFS/03 §3`) is short
exact.

* `Mono boundedSeqIncl` is `mono_boundedSeqIncl` (`RealSide`);
* `Epi zToRealQuot` is `epi_zToRealQuot`: every family of continuous real-valued functions on a
  light profinite set differs from a family of continuous integer-valued functions by a uniformly
  bounded family (`prodReal_rounding`), so `∏ℝ` is covered by the images of `∏ℤ` and `∏^bnd ℝ`;
* exactness in the middle is `exact_of_isPullback` applied to the cartesian square
  `isPullback_realSide`, i.e. to

  ```
  boundedSeq  --boundedIntRealIncl-->  boundedReal
      |                                     |
  boundedSeqIncl                      boundedRealIncl
      v                                     v
  prodZModel  --prodZRealIncl-------->  prodReal
  ```

  (an integer family of continuous functions whose real image is uniformly bounded is itself
  bounded), which exhibits `boundedSeqIncl` as the kernel of
  `zToRealQuot = prodZRealIncl ≫ cokernel.π boundedRealIncl`.

Consequently `coker boundedSeqIncl ≅ ∏ℝ/∏^bnd ℝ` (`ShortComplex.ShortExact.gIsCokernel`), which is
the form of the statement used in `Work.ANALYTIC.boundedSeqIncl_solidEquiv`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open Opposite

noncomputable section

set_option linter.style.haveILetI false

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- **The sequence `∏^bnd ℤ ⟶ ∏ℤ ⟶ ∏ℝ/∏^bnd ℝ` is short exact** (AN2, REFS/03 §3). -/
theorem shortExact_realQuot :
    (CategoryTheory.ShortComplex.mk Work.ANALYTIC.boundedSeqIncl Work.ANALYTIC.zToRealQuot
      Work.ANALYTIC.boundedToRealQuot_eq_zero).ShortExact := by
  haveI : Mono boundedRealIncl := mono_boundedRealIncl
  refine ShortComplex.ShortExact.mk' ?_ mono_boundedSeqIncl epi_zToRealQuot
  exact exact_of_isPullback boundedSeqIncl boundedIntRealIncl prodZRealIncl boundedRealIncl
    isPullback_realSide _

end Work.ANALYTIC
