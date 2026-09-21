import Submission.Work.OddCurve.Reduction
import Submission.Work.OddEnvelope.MainClose
import Submission.Work.OddVolterra.Assembly

/-!
# The remaining gap, and its interface with the Volterra machinery

The single remaining mathematical input of the odd-dimensional case is
`Work.OddCurve.SmallSlopeCurveExists n`: for every sufficiently small flat bump `h` there is a chord
curve `(x, y)` with `Work.OddEnvelope.IsEnvelopeCurve h x y` and the two moment equations on the
transition slopes `0 < s ≤ 1 - τ`.

The paper's route to it (Ryabogin, *A negative answer to Ulam's Problem 19 from the Scottish Book*,
§“The case of odd `d ≥ 3`”, Steps 2 and 3) is:

* **Step 2.** On a *short* slope window `[1-3τ, 1]` (a closed interval with right end `< 1` — the
  identity `Godd n 0 s (baseState s) = ∫_s^1 Θ + Ξ` is false at `s = 1` for the definitions of
  `Work.OddVolterra`, see `Work.OddVolterra.Base`), differentiate `(A)` `n+1` times and `(B)` `n`
  times, change variables `t = -x σ`, `t = y σ` on the swept parts and rewrite the result as the
  Abel system `∫_s^1 K(s,σ,z,z')/√(σ-s) = Q(s)`.  Abel-inverting it (NRZ Lemma 8; in this workspace
  `Commons.Analysis.Abel.volterra_equivalence_full` with `abel_transform_injective_on`) gives the
  integro-differential system `Godd n h s Z(s) = ∫_s^1 Theta n h s σ Z(σ) + Xi n h s`
  (`Work.OddVolterra.VolterraEqOn`), whose data are explicit in `h` and whose base solution is the
  ball's curve `baseState`.  Its linear part `D_Z G` is invertible: `Work.OddCurve.detKernel_ne_zero`
  is the paper's determinant computation (`det H111`), the sign pattern of the two rows of the
  kernel matrix.  The Volterra/implicit-function theorem of the commons then produces a solution
  close to the ball's curve for every sufficiently small bump.
* **Step 3.** The remaining (small) slopes are obtained from the spherical Radon transform
  (`Work.OddRadon`), or, in the cheaper route chosen in `Submission/Odd/PLAN.md`, by continuing the
  Volterra solution leftwards to `s → 0⁺` in the weighted norm (the base identity holds for all `s`
  in the open interval).

`Work.OddCurve.smallSlopeCurveExists_of_curveData` below is the interface between this chapter and
the Volterra machinery: it says that the two halves (a `CurveData` solution of the Volterra system,
and the bridge from the Volterra system to the two moment equations) are exactly what is missing.
The bridge itself is the content of `Work.OddVolterra.Bridge.momentEqs_of_volterra` (together with
the row identities of `Work.OddVolterra.RowIdentity`), whose first layer this chapter supplies:

* `Work.OddCurve.hasDerivAt_rad_pow_sqrt` / `hasDerivAt_max_pow_sqrt` — the pointwise derivative of
  the moment integrand in the slope (with and without the clamp `max · 0`);
* `Work.OddCurve.hasDerivAt_integral_rad_general` — its integrated form (the Leibniz rule, with no
  positivity assumption on the radicand off the section);
* `Work.OddCurve.continuous_envelopeProfile` — global continuity of the profile, which those
  Leibniz rules consume;
* `Work.OddCurve.rad_nonpos_outside` and `Work.OddCurve.moment_eqs_eq_integral_Icc` — the radicand
  is `≤ 0` off the section, so the moment integrals may be taken over a fixed interval;
* `Work.OddCurve.hasDerivAt_momentA` — the resulting first row identity: the derivative of the
  volume moment `(A)` in the slope is the integral over the section of the differentiated kernel;
* `Work.OddCurve.detKernel_ne_zero` — the paper's determinant computation `det H111` for the
  invertibility of the linear part of the system.

Iterating `hasDerivAt_momentA` `n+1` times (and the analogous statement for the centroid moment
`(B)` `n` times), then performing the change of variables `t = -x σ`, `t = y σ` on the swept parts
and Abel-inverting, is the remaining work of the bridge.
-/

namespace Work.OddCurve

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Pointwise

/-- A small flat bump vanishes at `0`. -/
lemma IsSmallFlatBump.zero {ε : ℝ} {h : ℝ → ℝ} (hb : IsSmallFlatBump ε h) : h 0 = 0 := by
  by_contra hne
  have hmem : (0 : ℝ) ∈ Function.support h := by simpa [Function.mem_support] using hne
  have hsub := hb.support_subset hmem
  have htau : tau < 1 / 2 := by norm_num [tau]
  linarith [hsub.1, htau]

/-- **The interface to the Volterra machinery.**  If every small flat bump admits a solution
`(x,y)` of the odd Volterra system in the form `Work.OddVolterra.CurveData`, and if `CurveData`
implies the two moment equations on the transition slopes with the constant `refConst n`, then the
remaining input `SmallSlopeCurveExists n` holds.

The first hypothesis is the paper's Steps 2 and 3 (the Volterra/Abel construction, plus the Radon
inversion or the leftward continuation); the second is the bridge
`Work.OddVolterra.Bridge.momentEqs_of_volterra` (row identities + Abel inversion). -/
theorem smallSlopeCurveExists_of_curveData (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (Hex : ∀ h : ℝ → ℝ, IsSmallFlatBump ε h → h ≠ 0 → ∃ x y : ℝ → ℝ,
      Work.OddVolterra.CurveData n h x y)
    (Hbridge : ∀ h x y : ℝ → ℝ, IsSmallFlatBump ε h → Work.OddVolterra.CurveData n h x y →
      SmallSlopeEqs n h x y) :
    SmallSlopeCurveExists n := by
  refine ⟨ε, hε, fun h hbump hne => ?_⟩
  obtain ⟨x, y, hdata⟩ := Hex h hbump hne
  have hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) :=
    fun s hs => ⟨le_of_lt (hbump.support_subset hs).1, le_of_lt (hbump.support_subset hs).2⟩
  have hIC : Work.OddEnvelope.IsEnvelopeCurve h x y :=
    Work.OddEnvelope.Close.isEnvelopeCurve_of_close (hδ := le_rfl)
      hdata.smooth_x hdata.smooth_y hbump.contDiff.contDiffOn
      hdata.deriv_x_neg hdata.deriv_y_neg hdata.tendsto_x hdata.tendsto_y
      hdata.tail_x hdata.tail_y hbump.zero hsupp hdata.close_x hdata.close_y hdata.close_h
  exact ⟨x, y, hIC, Hbridge h x y hbump hdata⟩

end

end Work.OddCurve
