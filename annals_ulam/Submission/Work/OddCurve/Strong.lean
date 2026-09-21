import Submission.Work.OddCurve.Defs
import Submission.Work.OddCurve.Reduction
import Submission.Work.OddCurve.Endgame
import Submission.Work.OddCurve.Crux

/-!
# The regularity-strong variant of the bump class (`C^{n+2}` smallness)

The paper's construction of the odd-dimensional chord curve needs **all** derivatives of the bump
`h` up to order `n + 2` to be small: the Jacobians `J₁`, `J₂` of the moment integrands, the data
`Θ = -∂_s G₂` and `Ξ = Q̃` of the system `(hah44)` are explicit expressions in `h^{(0)}, …, h^{(n+2)}`.

The `C²` bounds alone are *not* enough for that route: for the scaled bumps
`h_δ = ε δ^{n+1} Φ((· - s₀)/δ)` (any fixed bump shape `Φ`, any `s₀`) one has `|h|, |h'|, |h''| ≤ C ε`
while `‖h^{(n+2)}‖ ≈ ε/δ^{n+1} → ∞`; the earlier run of this project machine-checked that the
system-based statements are false under `C²` smallness alone.

This file therefore records the same development for the class in which the construction actually
works, and which the consumer's bump (`Submission.Odd.BumpData.exists_odd_bump (n+2) ε hε`) does
satisfy.  It is the form in which the deliverable of `Work.OddCurve` should be quoted; the
`C²`-only statement `Work.OddCurve.odd_curve_exists_of_smallSlopeCurveExists_written` is kept for
the literal shape of the request (see `REMAINING.md`, section 0).

## Contents

* `IsSmallFlatBumpStrong n ε h` — smooth, supported in the open window, all derivatives up to
  order `n+2` bounded by `ε`, flat at the left edge of the window;
* `IsSmallFlatBumpStrong.toIsSmallFlatBump` — the strong class is contained in the `C²` class
  (so `SmallSlopeCurveExists` implies its strong analogue);
* `exists_isSmallFlatBumpStrong` — the bump construction at regularity `n+2`;
* `OddCurveExistsStrong`, `SmallSlopeCurveExistsStrong` — the strong analogues of the chapter's
  main predicates;
* `oddCurveExistsStrong_of_smallSlopeCurveExistsStrong`,
  `oddFamilyData_of_smallSlopeCurveExistsStrong` — the endgame, for the strong class.
-/

namespace Work.OddCurve

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Pointwise Interval

/-- **The regularity-strong bump class.**  A smooth function supported in the open transition
window `(1-2τ, 1-τ)`, all of whose derivatives up to order `n + 2` are bounded by `ε`, and which
vanishes on a right neighbourhood of the left edge of the window. -/
def IsSmallFlatBumpStrong (n : ℕ) (ε : ℝ) (h : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ h ∧ Function.support h ⊆ Set.Ioo (1 - 2 * tau) (1 - tau) ∧
    (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ ε) ∧
    (∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * tau ≤ s → s < 1 - 2 * tau + η → h s = 0)

lemma IsSmallFlatBumpStrong.contDiff {n : ℕ} {ε : ℝ} {h : ℝ → ℝ}
    (hb : IsSmallFlatBumpStrong n ε h) : ContDiff ℝ ∞ h := hb.1

lemma IsSmallFlatBumpStrong.support_subset {n : ℕ} {ε : ℝ} {h : ℝ → ℝ}
    (hb : IsSmallFlatBumpStrong n ε h) :
    Function.support h ⊆ Set.Ioo (1 - 2 * tau) (1 - tau) := hb.2.1

lemma IsSmallFlatBumpStrong.deriv_bound {n : ℕ} {ε : ℝ} {h : ℝ → ℝ}
    (hb : IsSmallFlatBumpStrong n ε h) {k : ℕ} (hk : k ≤ n + 2) (s : ℝ) :
    |iteratedDeriv k h s| ≤ ε := hb.2.2.1 k hk s

lemma IsSmallFlatBumpStrong.flat {n : ℕ} {ε : ℝ} {h : ℝ → ℝ}
    (hb : IsSmallFlatBumpStrong n ε h) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * tau ≤ s → s < 1 - 2 * tau + η → h s = 0 := hb.2.2.2

/-- The regularity-strong class is contained in the `C²` class of `Work.OddCurve.Defs`. -/
lemma IsSmallFlatBumpStrong.toIsSmallFlatBump {n : ℕ} {ε : ℝ} {h : ℝ → ℝ}
    (hb : IsSmallFlatBumpStrong n ε h) : IsSmallFlatBump ε h := by
  obtain ⟨hc, hs, hbnd, hf⟩ := hb
  refine ⟨hc, hs, ?_, ?_, ?_, hf⟩
  · intro s
    simpa using hbnd 0 (by omega) s
  · intro s
    rw [← congrFun iteratedDeriv_one s]
    exact hbnd 1 (by omega) s
  · intro s
    have h2 : iteratedDeriv 2 h s = deriv (deriv h) s := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
    rw [← h2]
    exact hbnd 2 (by omega) s

/-- The strong class vanishes to the right of the window. -/
lemma IsSmallFlatBumpStrong.eventuallyEq_zero_of_gt {n : ℕ} {ε : ℝ} {h : ℝ → ℝ}
    (hb : IsSmallFlatBumpStrong n ε h) {s : ℝ} (hs : 1 - tau < s) :
    h =ᶠ[𝓝 s] (fun _ : ℝ => 0) :=
  IsSmallFlatBump.eventuallyEq_zero_of_gt hb.toIsSmallFlatBump hs

/-- The bump construction at regularity `n + 2` (`Submission.Odd.exists_odd_bump`). -/
theorem exists_isSmallFlatBumpStrong (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℝ → ℝ, IsSmallFlatBumpStrong n ε h ∧ h ≠ 0 ∧ h 0 = 0 ∧
      (∃ s : ℝ, 0 < s ∧ h s ≠ 0) := by
  obtain ⟨h, hh, hsupp, _hsuppIcc, hne, h0, hflat, hbnd, hpos⟩ :=
    Submission.Odd.exists_odd_bump (n + 2) ε hε
  exact ⟨h, ⟨hh, hsupp, fun k hk s => hbnd k (by omega) s, hflat⟩, hne, h0, hpos⟩

/-- **The conclusion of the request**, for the regularity-strong bump class. -/
def OddCurveExistsStrong (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ, IsSmallFlatBumpStrong n ε h → h ≠ 0 →
    ∃ C : ℝ, ∃ x y : ℝ → ℝ, IsOddCurve n C h x y

/-- The transition-window existence statement for the regularity-strong bump class. -/
def SmallSlopeCurveExistsStrong (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ, IsSmallFlatBumpStrong n ε h → h ≠ 0 →
    ∃ x y : ℝ → ℝ, IsOddCurveSmallSlopes n h x y

/-- The `C²` form of the existence statement implies the strong form (the strong class is
smaller). -/
theorem smallSlopeCurveExistsStrong_of_smallSlopeCurveExists (n : ℕ)
    (H : SmallSlopeCurveExists n) : SmallSlopeCurveExistsStrong n := by
  obtain ⟨ε, hε, H'⟩ := H
  exact ⟨ε, hε, fun h hb hne => H' h hb.toIsSmallFlatBump hne⟩

/-- The strong transition-window curve gives the strong form of the chapter's conclusion. -/
theorem oddCurveExistsStrong_of_smallSlopeCurveExistsStrong (n : ℕ)
    (H : SmallSlopeCurveExistsStrong n) : OddCurveExistsStrong n := by
  obtain ⟨ε, hε, H'⟩ := H
  refine ⟨ε, hε, fun h hb hne => ?_⟩
  obtain ⟨x, y, hH, hsl⟩ := H' h hb hne
  exact ⟨refConst n, x, y, hH,
    momentEqsOn_Ioc_one_of_smallSlopes n hH
      (fun s hs => hb.eventuallyEq_zero_of_gt hs) hsl⟩

/-- **The endgame for the regularity-strong class**: the odd-dimensional family data of
Ryabogin's construction, for `d = 2n+1`, `n ≥ 1`, `d ≥ 3`. -/
theorem oddFamilyData_of_smallSlopeCurveExistsStrong {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    (hdodd : Odd d) (n : ℕ) (hdn : d = 2 * n + 1) (hn : 1 ≤ n)
    (H : SmallSlopeCurveExistsStrong n) :
    Submission.Odd.OddFamilyData d := by
  obtain ⟨ε, hε, hcurve⟩ := oddCurveExistsStrong_of_smallSlopeCurveExistsStrong n H
  obtain ⟨h, hbump, hne, _h0, ⟨s₀, hs₀, hs₀ne⟩⟩ := exists_isSmallFlatBumpStrong n ε hε
  obtain ⟨C, x, y, hH, hme⟩ := hcurve h hbump hne
  obtain ⟨hA, hB⟩ :=
    (momentEqsOn_Ioc_iff n C h x y (Work.OddEnvelope.envelopeProfile h x y)).mp hme
  have hzero : ∀ s : ℝ, 1 - (1 / 10 : ℝ) ≤ s → h s = 0 := by
    intro s hs
    by_contra hne'
    have hmem : s ∈ Function.support h := by simpa [Function.mem_support] using hne'
    have hsub := hbump.support_subset hmem
    exact absurd hs (not_le.mpr hsub.2)
  exact Submission.Odd.odd_floating_family_data_of_envelope_curve (d := d) hd hdodd n hdn hn
    hbump.contDiff ⟨s₀, hs₀, hs₀ne⟩ hzero hH
    (fun s hs hs1 => hA s hs hs1) (fun s hs hs1 => hB s hs hs1)

/-- **The interface to the Volterra chain, for the regularity-strong class.**  A `CurveData`
solution of the odd Volterra system, together with the bridge from the Volterra system to the two
moment equations, gives the transition-slope curve in the strong class — the class in which the
paper's construction (and the workspace's `Work.OddVolterra` chain) produces its solution. -/
theorem smallSlopeCurveExistsStrong_of_curveData (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (Hex : ∀ h : ℝ → ℝ, IsSmallFlatBumpStrong n ε h → h ≠ 0 → ∃ x y : ℝ → ℝ,
      Work.OddVolterra.CurveData n h x y)
    (Hbridge : ∀ h x y : ℝ → ℝ, IsSmallFlatBumpStrong n ε h →
      Work.OddVolterra.CurveData n h x y → SmallSlopeEqs n h x y) :
    SmallSlopeCurveExistsStrong n := by
  refine ⟨ε, hε, fun h hbump hne => ?_⟩
  obtain ⟨x, y, hdata⟩ := Hex h hbump hne
  have hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) :=
    fun s hs => ⟨le_of_lt (hbump.support_subset hs).1, le_of_lt (hbump.support_subset hs).2⟩
  have hIC : Work.OddEnvelope.IsEnvelopeCurve h x y :=
    Work.OddEnvelope.Close.isEnvelopeCurve_of_close (hδ := le_rfl)
      hdata.smooth_x hdata.smooth_y hbump.contDiff.contDiffOn
      hdata.deriv_x_neg hdata.deriv_y_neg hdata.tendsto_x hdata.tendsto_y
      hdata.tail_x hdata.tail_y (IsSmallFlatBump.zero hbump.toIsSmallFlatBump) hsupp
      hdata.close_x hdata.close_y hdata.close_h
  exact ⟨x, y, hIC, Hbridge h x y hbump hdata⟩

end

end Work.OddCurve
