import Submission.Work.OddCurve.Reduction
import Submission.Work.OddCurve.Endgame

/-!
# The chord-curve interface *with free tips* (`Work.OddCurve.Free`)

`Work.OddEnvelope.IsEnvelopeCurve` contains the two normalisation fields

  `x_tendsto_one : Tendsto x (𝓝[>] 0) (𝓝 1)`,  `y_tendsto_one : Tendsto y (𝓝[>] 0) (𝓝 1)`,

i.e. it requires the final body to have its two **tips at `(±1, 0, …, 0)`** (the envelope profile is
supported in `[-1,1]` by definition, so `x s → 1` and `y s → 1` is exactly `ρ(-1) = ρ(1) = 1` for
the radial function `ρ` of the body).

The paper's odd-dimensional construction does **not** produce tips at `±1`: its profile is defined
on `[-r(0), R(0)]` where `R(0) = ρ(1)`, `r(0) = ρ(-1)` are the inverted data at the poles
(`W3.tex`, Step 3: `R^{d+1}(0)+r^{d+1}(0) = Φ_h(0)`, `R^d(0)-r^d(0) = Ψ_h(0)`) — determined
functionals of the datum, generically different from `1`.  See
`Submission/Work/OddCurve/NOTES_SESSION5.md` for the analysis and the `n = 1` computation.

This file provides the corrected interface: the same structure with the two tip fields replaced by
"the curve has *some* positive limit" (`x_tendsto_free`, `y_tendsto_free`), together with

* `isEnvelopeCurveFree_of_isEnvelopeCurve` — the old interface implies the new one, so **no
  earlier work is lost** if the interface is relaxed;
* `isEnvelopeCurve_of_isEnvelopeCurveFree_of_tips` — the new one plus the (separate, generally
  false) tip normalisation gives the old one;
* `OddCurveExistsFree` — the corrected deliverable, and
  `oddCurveExistsFree_of_oddCurveExists` — the old deliverable implies it.

The consumer `Submission.Odd.OddFamilyData` already *allows* `R₁, R₂ ≠ 1`, so the relaxation of the
interface does not affect the endgame's statement; only the intermediate lemmas that hard-code
`[-1,1]` (in `Submission/Odd/Final.lean`, `Submission/Odd/Assembly.lean`, `Submission/Work/OddCaps`)
need the general form.
-/

namespace Work.OddCurve
namespace Free

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Pointwise

/-- **The chord-curve hypothesis package with free tips.**  Identical to
`Work.OddEnvelope.IsEnvelopeCurve` except that the two fields `x_tendsto_one`, `y_tendsto_one` are
replaced by the existence of *some* positive limits at `0⁺`: these limits are the tips of the body,
`ρ(-1)` and `ρ(1)`, and the paper's construction does not make them `1`. -/
structure IsEnvelopeCurveFree (h x y : ℝ → ℝ) : Prop where
  /-- `h` is smooth on `(0,∞)`. -/
  smooth_h : ContDiffOn ℝ ∞ h (Set.Ioi 0)
  /-- `x` is smooth on `(0,∞)`. -/
  smooth_x : ContDiffOn ℝ ∞ x (Set.Ioi 0)
  /-- `y` is smooth on `(0,∞)`. -/
  smooth_y : ContDiffOn ℝ ∞ y (Set.Ioi 0)
  /-- `h 0 = 0`. -/
  h_zero : h 0 = 0
  /-- `h` is supported in the window `[1-2τ, 1-τ]`. -/
  h_support : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)
  /-- `x` is strictly decreasing on `(0,∞)`. -/
  x_deriv_neg : ∀ s, 0 < s → deriv x s < 0
  /-- `y` is strictly decreasing on `(0,∞)`. -/
  y_deriv_neg : ∀ s, 0 < s → deriv y s < 0
  /-- `x s` has a positive limit as `s → 0⁺` (the left tip `ρ(-1)` of the body). -/
  x_tendsto_free : ∃ a : ℝ, 0 < a ∧ Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 a)
  /-- `y s` has a positive limit as `s → 0⁺` (the right tip `ρ(1)` of the body). -/
  y_tendsto_free : ∃ b : ℝ, 0 < b ∧ Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 b)
  /-- Beyond the perturbation window the curve is the semicircle. -/
  x_tail : ∀ s, 1 - tau ≤ s → x s = Work.OddEnvelope.profileX s
  /-- Beyond the perturbation window the curve is the semicircle. -/
  y_tail : ∀ s, 1 - tau ≤ s → y s = Work.OddEnvelope.profileX s
  /-- `s ↦ s * y s + h s` is strictly increasing. -/
  mono_y : ∀ s, 0 < s → 0 < y s + s * deriv y s + deriv h s
  /-- `s ↦ s * x s - h s` is strictly increasing. -/
  mono_x : ∀ s, 0 < s → 0 < x s + s * deriv x s - deriv h s
  /-- Second-order shape condition on the right branch (concavity of `f` on `(0,1)`). -/
  shape_y : ∀ s, 0 < s →
    0 < 2 * (deriv y s) ^ 2 - y s * deriv (deriv y) s +
      deriv (deriv h) s * deriv y s - deriv h s * deriv (deriv y) s
  /-- Second-order shape condition on the left branch (concavity of `f` on `(-1,0)`). -/
  shape_x : ∀ s, 0 < s →
    0 < 2 * (deriv x s) ^ 2 - x s * deriv (deriv x) s -
      deriv (deriv h) s * deriv x s + deriv h s * deriv (deriv x) s

/-- **The old interface implies the new one** (with limits `1` and `1`): relaxing the interface
loses no proved statement. -/
theorem isEnvelopeCurveFree_of_isEnvelopeCurve {h x y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y) : IsEnvelopeCurveFree h x y where
  smooth_h := H.smooth_h
  smooth_x := H.smooth_x
  smooth_y := H.smooth_y
  h_zero := H.h_zero
  h_support := H.h_support
  x_deriv_neg := H.x_deriv_neg
  y_deriv_neg := H.y_deriv_neg
  x_tendsto_free := ⟨1, one_pos, H.x_tendsto_one⟩
  y_tendsto_free := ⟨1, one_pos, H.y_tendsto_one⟩
  x_tail := H.x_tail
  y_tail := H.y_tail
  mono_y := H.mono_y
  mono_x := H.mono_x
  shape_y := H.shape_y
  shape_x := H.shape_x

/-- **The new interface plus the tip normalisation gives the old one.**  The extra hypotheses are
exactly the two statements that the paper's construction does **not** supply. -/
theorem isEnvelopeCurve_of_isEnvelopeCurveFree_of_tips {h x y : ℝ → ℝ}
    (H : IsEnvelopeCurveFree h x y)
    (hx : Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 1))
    (hy : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    Work.OddEnvelope.IsEnvelopeCurve h x y where
  smooth_h := H.smooth_h
  smooth_x := H.smooth_x
  smooth_y := H.smooth_y
  h_zero := H.h_zero
  h_support := H.h_support
  x_deriv_neg := H.x_deriv_neg
  y_deriv_neg := H.y_deriv_neg
  x_tendsto_one := hx
  y_tendsto_one := hy
  x_tail := H.x_tail
  y_tail := H.y_tail
  mono_y := H.mono_y
  mono_x := H.mono_x
  shape_y := H.shape_y
  shape_x := H.shape_x

/-- The free-tip chord curve: the tip-relaxed `Work.OddCurve.IsOddCurve`. -/
def IsOddCurveFree (n : ℕ) (C : ℝ) (h x y : ℝ → ℝ) : Prop :=
  IsEnvelopeCurveFree h x y ∧
    MomentEqsOn n C h x y (Work.OddEnvelope.envelopeProfile h x y) (Set.Ioc 0 1)

/-- **The corrected deliverable** (`d = 2n+1`, `n ≥ 1`): for every sufficiently small flat bump
there is a chord curve with the free-tip envelope structure and the two moment equations on
`(0,1]`.  This is what the paper's Steps 2 + 3 actually produce. -/
def OddCurveExistsFree (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ, IsSmallFlatBump ε h → h ≠ 0 →
    ∃ C : ℝ, ∃ x y : ℝ → ℝ, IsOddCurveFree n C h x y

/-- The original (tip-normalised) deliverable implies the corrected one. -/
theorem oddCurveExistsFree_of_oddCurveExists (n : ℕ) (H : OddCurveExists n) :
    OddCurveExistsFree n := by
  obtain ⟨ε, hε, H'⟩ := H
  refine ⟨ε, hε, fun h hbump hne => ?_⟩
  obtain ⟨C, x, y, hIC, hme⟩ := H' h hbump hne
  exact ⟨C, x, y, isEnvelopeCurveFree_of_isEnvelopeCurve hIC, hme⟩

/-- The original deliverable *is* the corrected one plus the tip normalisation. -/
theorem oddCurveExists_of_oddCurveExistsFree_of_tips (n : ℕ) (H : OddCurveExistsFree n)
    (Htips : ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ, IsSmallFlatBump ε h → h ≠ 0 →
      ∀ (C : ℝ) (x y : ℝ → ℝ), IsOddCurveFree n C h x y →
        Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 1) ∧ Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    OddCurveExists n := by
  obtain ⟨ε, hε, H'⟩ := H
  obtain ⟨ε', hε', Htips⟩ := Htips
  refine ⟨min ε ε', lt_min hε hε', fun h hbump hne => ?_⟩
  have hmL : min ε ε' ≤ ε := min_le_left ε ε'
  have hmR : min ε ε' ≤ ε' := min_le_right ε ε'
  have hbumpε : IsSmallFlatBump ε h :=
    ⟨hbump.1, hbump.2.1, fun s => le_trans (hbump.2.2.1 s) hmL,
      fun s => le_trans (hbump.2.2.2.1 s) hmL,
      fun s => le_trans (hbump.2.2.2.2.1 s) hmL, hbump.2.2.2.2.2⟩
  have hbumpε' : IsSmallFlatBump ε' h :=
    ⟨hbump.1, hbump.2.1, fun s => le_trans (hbump.2.2.1 s) hmR,
      fun s => le_trans (hbump.2.2.2.1 s) hmR,
      fun s => le_trans (hbump.2.2.2.2.1 s) hmR, hbump.2.2.2.2.2⟩
  obtain ⟨C, x, y, hfr, hme⟩ := H' h hbumpε hne
  obtain ⟨hx, hy⟩ := Htips h hbumpε' hne C x y ⟨hfr, hme⟩
  exact ⟨C, x, y, isEnvelopeCurve_of_isEnvelopeCurveFree_of_tips hfr hx hy, hme⟩

/-- **The corrected deliverable, written out textually**, in exactly the shape of the consumer's
request with `IsEnvelopeCurve` replaced by `IsEnvelopeCurveFree`. -/
theorem odd_curve_exists_free_written (n : ℕ) (_hn : 1 ≤ n) (H : OddCurveExistsFree n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ,
      ContDiff ℝ ∞ h →
      Function.support h ⊆ Set.Ioo (1 - 2 * (1 / 10)) (1 - (1 / 10)) →
      (∀ s : ℝ, |h s| ≤ ε) → (∀ s : ℝ, |deriv h s| ≤ ε) →
      (∀ s : ℝ, |deriv (deriv h) s| ≤ ε) →
      (∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * (1 / 10) ≤ s →
        s < 1 - 2 * (1 / 10) + η → h s = 0) →
      h ≠ 0 →
      ∃ C : ℝ, ∃ x y : ℝ → ℝ,
        IsEnvelopeCurveFree h x y ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          (∫ t in (-x s)..(y s),
            (Work.OddEnvelope.envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2) ^ n *
              Real.sqrt (Work.OddEnvelope.envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2)) =
            C / Real.sqrt (1 + s ^ 2)) ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          (∫ t in (-x s)..(y s),
            (Work.OddEnvelope.envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
              Real.sqrt (Work.OddEnvelope.envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2) *
              (t + deriv h s)) = 0) := by
  obtain ⟨ε, hε, H'⟩ := H
  refine ⟨ε, hε, fun h hcont hsupp hb1 hb2 hb3 hflat hne => ?_⟩
  have hbump : IsSmallFlatBump ε h :=
    isSmallFlatBump_of_consumer hcont hsupp hb1 hb2 hb3 hflat
  obtain ⟨C, x, y, hfr, hme⟩ := H' h hbump hne
  obtain ⟨hA, hB⟩ :=
    (momentEqsOn_Ioc_iff n C h x y (Work.OddEnvelope.envelopeProfile h x y)).mp hme
  exact ⟨C, x, y, hfr, hA, hB⟩

end

end Free
end Work.OddCurve
