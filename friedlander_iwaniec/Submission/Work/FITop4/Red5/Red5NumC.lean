/-
# `Submission.Work.FITop4.Red5.Red5NumC` — `Red5Num` without the `τ`-range hypothesis

`Red5Num x N Pz η` (in `Red5Num.lean`) bundles every numerical inequality the final assembly of
`reduction_save` needs about the window ladder `M₀ = ⌊ϑx/N⌋ + 2`, `M_top = ⌊x/(2N)⌋`, `JJ` of
`window_setup`, plus three transcendental comparisons.  It contains **one** field that depends on
`η` in a `x`-significant way:

  `htau : tauOf x Asave ≤ x ^ (η/3)`.

That field is needed only because the round-5 plan *chose* `Pa.τ = tauOf x Asave` (the paper's
(10.11) threshold).  When the reduction is run with the *given* threshold `τ` (which the frozen
target `reduction_save` quantifies over, subject to `(log x)^{A+124} ≤ τ ≤ x^{η/3}`), every
remaining numerical input is **independent of `η`**: the only `η`-dependence of `Red5Num` enters
through the range hypothesis `N < x^{1/2} (log x)^{-BmaxBig η}` and, crucially, the exponent gap
`BmaxBig η - 1 - A ≥ 2^31` is always astronomically large, so every comparison with `ϑ = (log
x)^{-A}` is decided by `log x ≥ 1` alone.

`Red5NumC` is therefore `Red5Num` with `htau` deleted; `red5numC_proof` (a sibling file) provides
it with an `η`-**independent** threshold, which is what the frozen statement's `∃ x₀ ∀ x N Pz C τ
η` requires.
-/
import Mathlib
import Submission.Work.FITop4.Red5.window_setup
import Submission.Work.FITop4.Numeric4.numHyp_proof2

set_option autoImplicit false

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Every numerical side condition of the round-5 window decomposition **except** the `η`-dependent
`tauOf x Asave ≤ x^{η/3}`.  See the module docstring. -/
structure Red5NumC (x N Pz : ℕ) (η : ℝ) : Prop where
  hx4 : 4 ≤ x
  hlog1 : 1 ≤ Real.log (x : ℝ)
  hlog4 : 4 ≤ Real.log (x : ℝ)
  hv0 : 0 < varthetaOf x Asave
  hv14 : varthetaOf x Asave ≤ 1 / 4
  hv8 : 8 * varthetaOf x Asave ≤ 1
  hvx1 : 1 ≤ varthetaOf x Asave * (x : ℝ)
  ht0 : 0 < thetaOf x Asave
  ht14 : thetaOf x Asave ≤ 1 / 4
  hM0ge4 : 4 ≤ M0N x N
  hM0ge2N : 2 * (N : ℝ) ≤ (M0N x N : ℝ)
  hM0le3 : (M0N x N : ℝ) * (N : ℝ) ≤ 3 * varthetaOf x Asave * (x : ℝ)
  hM0hing : varthetaOf x Asave * (x : ℝ) < (M0N x N : ℝ) * (N : ℝ)
  hθsqrtN : 1 ≤ thetaOf x Asave * (N : ℝ) ^ ((1 : ℝ) / 2)
  hN2x : (N : ℝ) ^ 2 ≤ (x : ℝ)
  h2Nx : 2 * (N : ℝ) ≤ (x : ℝ)
  htop : (MtopN x N : ℝ) * (2 * (N : ℝ)) ≤ (x : ℝ)
  hMtopge2N : 2 * (N : ℝ) ≤ (MtopN x N : ℝ)
  hMtoping : varthetaOf x Asave * (x : ℝ) < (MtopN x N : ℝ) * (N : ℝ)
  hMtop1 : 1 ≤ MtopN x N
  hM0leMtop : M0N x N ≤ MtopN x N
  hpowJJN : (2 : ℝ) ^ (JJN x N) * (M0N x N : ℝ) ≤ (x : ℝ) / (N : ℝ)
  hMtoplepow : (MtopN x N : ℝ) ≤ (2 : ℝ) ^ (JJN x N) * (M0N x N : ℝ)
  hcop : (N : ℝ) ≤ varthetaOf x Asave * thetaOf x Asave * (x : ℝ) ^ ((1 : ℝ) / 2)
  hPz : (Pz : ℝ)⁻¹ ≤ varthetaOf x Asave * thetaOf x Asave * (Real.log (x : ℝ)) ^ (100 : ℕ)

end
end Work.FITop4.Red5
