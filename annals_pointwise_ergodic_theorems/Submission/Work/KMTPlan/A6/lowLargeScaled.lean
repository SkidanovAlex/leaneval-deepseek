import Mathlib
import Submission.Work.KMTPlan.A6.LowFix.modApproxExact
import Submission.Work.KMTPlan.A6.LowModelGainEstimate
import Submission.Work.KMTPlan.A6.LowExceptionalEstimate

set_option autoImplicit false

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.KMTContract

/-- **The low case of area A6 at the large scales** (`Work.KMTPlan.A6.LcLarge`): the §5 columns
clamped to the large scales `N > splitCut ρ L` obey the `(2,2,1)` paraproduct estimate with the
exponential gain `2^{-c max(max l₁ l₂)(max k₁ k₂)}`.

The proof is the assembly `Work.KMTPlan.A6.lcLarge_of_inputs` (`A6/LowLargeDefs.lean`) applied to
the three estimates of §6--§8:

* `Work.KMTPlan.A6.LowModApproxExactEstimate` — §6 `mod-approx` for the model tuple
  (`LowModApprox`);
* `Work.KMTPlan.A6.LowModelGainEstimate` — §8, the model estimate with the gain (`LowModelGain`),
  i.e. the arithmetic bilinear estimate `bile` plus the integration-by-parts identity
  `integ-ident`;
* `Work.KMTPlan.A6.LowExceptionalEstimate` — the exceptional scales (`LowExceptional`).

The model inputs are the exact-height arithmetic shells with *narrow* windows
(`mdlF`, `mdlG` in `LowLargeDefs`), i.e. the paper symbols `Π_{l,≤-u} f` and `Π_{l,≤-du} g`; see
`NOTES_A6_lowLargeScaled.md` for the two corrections to the model operator found in this session. -/
theorem lowLargeScaled (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : ℝ≥0) (hr : 2 < r)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) :
    Work.KMTPlan.A6.LcLarge P r C₀ :=
  lcLarge_of_inputs P r hr C₀
    (Work.KMTPlan.A6.LowFix.LowModApproxExactEstimate P hd r hr C₀ hC₀ hA1)
    (LowModelGainEstimate P hd r hr C₀ hC₀ hA1 hI)
    (LowExceptionalEstimate P hd r hr C₀ hC₀ hA1 hI)

end Work.KMTPlan.A6
