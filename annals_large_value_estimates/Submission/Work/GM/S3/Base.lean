import Mathlib
import Submission.GM.Interfaces
import Submission.Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay
import Submission.Commons.Analysis.Fourier.poisson_summation_scaled

/-!
# Base imports for the area GM §§7, 8, 10 (`S3`)

This file only collects the imports that the lemmas of this area need, so that
`depends_on` in the delegation tooling can refer to it as `GM/S3/Base`.

* `Submission.GM.Interfaces` defines `hhat`, `hfun`, `Iterm`, `Spart`, `Rfun`, `energy`,
  `Separated`, `M` and the statements of the areas (`AffineStatement`, `S3Statement`).
* `Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay`
  (`‖𝓕 f ξ‖ ≤ C/|ξ|^j` for smooth compactly supported `f`) is GM Lemma 4.3's engine.
* `Commons.Analysis.Fourier.poisson_summation_scaled` is used for the `L⁴` bound of `R` (Lemma 8.3).
-/

/-! ## Trap: `⊤` in `ContDiff`

In this Mathlib, `ContDiff ℝ ⊤ f` (with `⊤ : WithTop ℕ∞`) means that `f` is **analytic**, and an
analytic function on `ℝ` vanishing off `[1,2]` is identically zero.  So any statement whose
hypotheses are `ContDiff ℝ ⊤ φ` together with "`φ` vanishes off `[1,2]`" is vacuous (it can only be
applied to `φ = 0`), and `ContDiff ℝ ⊤ φ` can never be proved for a bump function.  Use
`ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ` (i.e. `C^∞`) for smoothness.
-/

namespace Work.GM.S3

end Work.GM.S3
