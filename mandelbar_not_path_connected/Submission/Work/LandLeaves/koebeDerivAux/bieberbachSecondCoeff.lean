import Mathlib
import Submission.Work.LandLeaves.holoSqrt
import Submission.Work.LandLeaves.sqrtReduction
import Submission.Work.LandLeaves.circleIntegralCompInv
import Submission.Work.LandLeaves.GronwallDefs
import Submission.Work.LandLeaves.gronwallDefs
import Submission.Work.LandLeaves.approxInvSqrt
import Submission.Work.LandLeaves.koebeDerivAux.psiDefs
import Submission.Work.LandLeaves.koebeDerivAux.bco_one_le_one
import Submission.Work.LandLeaves.koebeDerivAux.bco_one_inst

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves.koebeDerivAux

open MeasureTheory

/-- The exterior `w⁻¹` Laurent coefficient bound, transported back to `f`: if `ψ` witnesses
`f` as in `bco_one_inst`, then `‖bco ψ 1‖ ≤ 1` and `bco ψ 1 = -(iteratedDeriv 2 f 0)/4`. -/
lemma bieberbachSecondCoeff_aux (f : ℂ → ℂ) (hd : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hf : Set.InjOn f (Metric.ball 0 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    ‖iteratedDeriv 2 f 0‖ / 4 ≤ 1 := by
  obtain ⟨ψ, W, C, hW, hdψ, hinjψ, hbψ, hbco⟩ := bco_one_inst f hd hf h0 h1
  have hcoeff : ‖bco ψ 1‖ ≤ 1 := bco_one_le_one ψ W C hW hdψ hinjψ hbψ
  rw [hbco, norm_div, norm_neg, Complex.norm_ofNat] at hcoeff
  exact hcoeff

/-- **Bieberbach's second-coefficient bound** (`|a₂| ≤ 2`): a holomorphic injection of the open unit ball with `f 0 = 0` and `deriv f 0 = 1` satisfies `‖iteratedDeriv 2 f 0‖ ≤ 4`.

This is Bieberbach's classical `n = 2` bound, restated under a fresh name so that
`Submission/Work/LandLeaves/koebeDerivBound.lean` (and anything below it) can be closed with a proof
that does not inherit the `sorry` currently sitting in `Submission/Work/LandLeaves/gronwallAreaWeak.lean`.
That `sorry` is the *exterior area theorem* (`Work.LandLeaves.gronwallAreaWeak`, a `sorry`-bearing
statement in that very file): it says `‖circleIntegral ψ 0 2‖ ≤ 2 * Real.pi` for `ψ` holomorphic and
injective on `{w | 1 < ‖w‖}` with `‖ψ w - w‖ ≤ C` for `‖w‖ ≥ W`.  Equivalently it is `‖b_1‖ ≤ 1` for
the Laurent expansion `ψ w = w + b_0 + b_1 / w + ...` of such an exterior-univalent `ψ`.  Filling that
gap is the whole content here; the assembly below it is mechanical and the proof body in
`Submission/Work/LandLeaves/bieberbachA2.lean` may be copied verbatim (it produces the odd univalent
square root `z ↦ z * sqrt (f (z^2)/z^2)` from `.../holoSqrt.lean` and `.../sqrtReduction.lean`,
evaluates the relevant circle integral through `.../circleIntegralCompInv.lean`, and applies the
exterior area bound).

**Avoiding Green's theorem.**  The area bound can be obtained from the multidimensional
change-of-variables formula (`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`, for
which `DifferentiableOn`/`InjOn` are the only hypotheses) as follows.  For `R > 1` let
`X R = ℂ ∖ ψ '' {z | R < ‖z‖}`, the bounded side of the simple closed curve `ψ '' {‖z‖ = R}`, and let
`K = ℂ ∖ ψ '' {z | 1 < ‖z‖}`.  Then `X R` is the disjoint union of `K`, `ψ '' {1 < ‖z‖ < R}` and the
curve itself, so `area (X R) = area K + ∫∫_{1 < ‖z‖ < R} ‖deriv ψ‖ ^ 2`, and that double integral is
`π (R ^ 2 - 1) + π ∑_n n ‖b_n‖ ^ 2 (1 - R ^ (-2n))` (expand `deriv ψ` in a Laurent series on the
annulus; the angular integration in polar coordinates is the mean square).  On the other hand
`(2i)⁻¹ ∮_{‖z‖ = R} conj (ψ z) * deriv ψ z = π (R ^ 2 - ∑_n n ‖b_n‖ ^ 2 R ^ (-2n))` by residues
(`conj z = R ^ 2 / z` on the circle).  These two functions of `R` have the same derivative and differ
by `o(1)` as `R → ∞`, hence are equal; the left one is `area (X R) ≥ 0`, so `∑_n n ‖b_n‖ ^ 2 R ^ (-2n) ≤ R ^ 2`
for every `R > 1`, and `R → 1` gives `∑_n n ‖b_n‖ ^ 2 ≤ 1`, in particular `‖b_1‖ ≤ 1`.-/
theorem bieberbachSecondCoeff (f : ℂ → ℂ) (hd : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hf : Set.InjOn f (Metric.ball 0 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    ‖iteratedDeriv 2 f 0‖ ≤ 4 := by
  have h := bieberbachSecondCoeff_aux f hd hf h0 h1
  have h4 : (0 : ℝ) < 4 := by norm_num
  have h' : ‖iteratedDeriv 2 f 0‖ ≤ 1 * 4 := (div_le_iff₀ h4).mp h
  simpa using h'

end Work.LandLeaves.koebeDerivAux
