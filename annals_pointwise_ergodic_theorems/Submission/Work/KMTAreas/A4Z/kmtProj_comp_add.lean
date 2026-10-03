import Mathlib
import Submission.Work.KMTContract.Areas

namespace Work.KMTAreas.A4Z

/-- **Translation invariance of the Ionescu--Wainger projection `Π_{≤l,≤k}`.**

`kmtProj ρ l k` is the convolution with the fixed IW kernel
`iwKernel (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)))` (see
`Work.KMTContract.kmtProj_apply`), and a convolution commutes with the shift
`(S_t u)(x) = u (x + t)` because `(n - j) + t = (n + t) - j`.  This is what lets the §5
assembly move the physical-space translation produced by the polynomial weights
`f (· + P(n))` in and out of the projections. -/
theorem kmtProj_comp_add (ρ : ℝ) (l : ℕ) (k : ℤ) (t : ℤ) (u : ℤ → ℂ) :
    Work.KMTContract.kmtProj ρ l k (fun x : ℤ => u (x + t))
      = fun x : ℤ => Work.KMTContract.kmtProj ρ l k u (x + t) := by
  funext n
  simp only [Work.KMTContract.kmtProj, Work.Analysis.IWMultiplier.iwConv]
  congr 1 with j
  rw [show n - j + t = n + t - j by ring]

end Work.KMTAreas.A4Z
