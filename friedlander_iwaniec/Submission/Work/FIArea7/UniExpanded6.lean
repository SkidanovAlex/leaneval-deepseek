/-
# `Submission.Work.FIArea7.UniExpanded6` — the (17.1) reflection of the uniform (paper's `W`) cut

`Work.FIArea7.WUni6` (the paper's sharp cut `|Δ| ≤ 4dX`) is, per pair, the `Tcut` sum

  `Σ_{d : 4d ∣ |Δ|, |Δ| ≤ 4dX} (φ(d)/d)·(z₂/z₁ ∣ d)·logFac6`,

and the reflection `d ↦ e = |Δ|/(4d)` (`Work.FIArea7.WUni_inner_totient_expansion`, whose index set
is the image of `{d : 4d ∣ M, M ≤ 4dX}` under the involution, namely `{e : 4e ∣ M, e ≤ X}`) turns
it into the *uniform* sum `Work.FIArea7.WUniInner`, i.e. the (17.1) double sum over the Möbius
divisors `b` and the small divisors `e ≤ X` with `4be ∣ |Δ|`.

This file assembles the pair-level identity into the box-level one
`Work.FIArea7.WUni6_eq_WUniExpanded6 : WUni6 Pa X β = WUniExpanded6 Pa X β`,
exactly as `Work.FIArea7.Wcut6_add_Bcut6_eq_WBcutExpanded6` does for the two-cut object.  The
degenerate pairs `Δ = 0` contribute `0` on both sides (`logFac6 z z' = log (…/0) = 0` in Lean's
conventions).
-/
import Mathlib
import Submission.Work.FIArea7.UniChain6
import Submission.Work.FIArea7.WUni_inner_totient_expansion

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The (17.1) reflection of the uniform cut.**  `WUni6` — the paper's sharp `W`, cut
`|Δ| ≤ 4dX` — is the reflected, Möbius-expanded double sum `WUniExpanded6` over the small
divisors `e ≤ X` with `4be ∣ |Δ|` (the reflected `e`-range is *uniform* in the pair, which is
what the §16 expansion (17.10) needs). -/
theorem WUni6_eq_WUniExpanded6 (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) :
    WUni6 Pa X β = WUniExpanded6 Pa X β := by
  rw [WUni6, Tcut6_eq_sum_ofReal, WUniExpanded6]
  congr 1
  apply Finset.sum_congr rfl; intro z1 _
  apply Finset.sum_congr rfl; intro z2 _
  by_cases hg : Work.FIPlan.GaussCoprime z1 z2
  · simp only [hg, if_true]
    congr 1
    rw [Complex.ofReal_inj]
    by_cases hM : Work.FIPlan.absDelta z1 z2 = 0
    · have hlog : Work.FITop4.logFac6 z1 z2 = 0 := by
        simp only [Work.FITop4.logFac6, hM]
        norm_num
      rw [hM, hlog]
      simp [WUniInner]
    · exact WUni_inner_totient_expansion (Nat.pos_of_ne_zero hM)
        (fun d => Work.FIArea7.ratioSym z1 z2 d) (Work.FITop4.logFac6 z1 z2)
  · simp only [hg, if_false]

end

end Work.FIArea7
