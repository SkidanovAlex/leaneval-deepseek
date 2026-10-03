/-
# Vocabulary for the lacunary-bump multiplier bound (`lacunaryBump_mult_bound_k1pos`)

This module fixes the two objects in which the pieces of
`Work.KMTAreas.A7.lacunaryBump_mult_bound_k1pos` are stated:

* `lacψ` — the mean-zero bump `ψ(ξ) = η(ξ) - η(2ξ)` attached to the KMT cutoff
  `η = Work.KMTContract.kmtEta` (`η = 1` on `[-1/2,1/2]`, `η = 0` off `[-1,1]`, even);
* `lacσ N k₁ = 2 ^ (logN N - k₁)` — the *frequency* scale of the term `φ_N` at the continuous
  scale `k₁`, so that `φ_N(ξ) = ψ(lacσ N k₁ * ξ)` for `k₁ ≥ 1`.

Both are the objects in which the shifted-Calderón–Zygmund instantiation
(`Work.Analysis.CzShift.cz_shift_lp`) of the KMT bump `φ_{N,t}(ξ) = φ_N(ξ) e(Ntξ)` is phrased:
the kernel of the term is a bump of width `lacσ N k₁` and mean zero (`lacψ 0 = 0`), which is
exactly why the bound `C * (1 + k₁)` — and not `C` — is the natural constant (the paper's
Appendix B, Theorem `cz-shift`).
-/
import Mathlib
import Submission.Work.Analysis.CzShift.Main
import Submission.Work.Analysis.CzShift.exists_isCZSeed_of_fourierInv
import Submission.Work.BourgainPlan.Maximal.main_narrow_taoSetS
import Submission.Work.BourgainPlan.Maximal.mikhlinConvolutionLp
import Submission.Work.KMTAreas.A7.LargeInterface

set_option autoImplicit false

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators FourierTransform

/-- The frequency scale `σ = 2 ^ (Log N - k₁)` of the bump `φ_N` at the continuous scale `k₁`:
`φ_N(ξ) = η(σ ξ) - η(2 σ ξ)`. -/
noncomputable def lacσ (N k₁ : ℕ) : ℝ :=
  (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℤ) - (k₁ : ℤ))

/-- The mean-zero bump `ψ(ξ) = η(ξ) - η(2ξ)`: `ψ(0) = 0`, `‖ψ‖_∞ ≤ 2`, and `ψ` is supported in
`[-1,1]` while it *vanishes* on `[-1/4,1/4]`. -/
noncomputable def lacψ (ξ : ℝ) : ℂ :=
  Work.KMTContract.kmtEta ξ - Work.KMTContract.kmtEta (2 * ξ)

end

end Work.KMTAreas.A7
