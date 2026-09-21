import Mathlib
import Submission.Work.OddCurve.Free.Step3Pieces
import Submission.Work.OddCurve.LowSlope.CurveDefs
import Submission.Work.OddCurve.LowSlope.radialSystem_deriv_sign
import Submission.Work.OddCurve.LowSlope.lowSlopeCurveY_derivs_sub
import Submission.Work.OddCurve.LowSlope.envelopeLeft_close_of_state_close
import Submission.Work.OddEnvelope.Close.isEnvelopeCurveFree_of_close
import Submission.Work.OddCurve.Free.radCurveClose
import Submission.Work.OddCurve.Free.lowSlopeCurveBasic
import Submission.Work.OddVolterra.Existence.curve_data_three_defs

/-!
# The curve assembly of Step 3 (the low-slope step of the odd case)

This file proves `Work.OddCurve.Free.LowSlopeCurveAssemblySpec n` (the second of the two inputs
isolated in `Free/Step3Pieces.lean`): from a radial pair `(R, r)` on `[0, π/2]` whose deviation
from `1` and whose first two derivatives are bounded by `ε`, glued to an envelope curve `(h, X, Y)`
along the window `[3/4, 4/5]` (where the chord is still centred, so the anchor's curve *is* the
radial parametrisation), the two-piece curve

* `y = lowSlopeCurveY R Y` — `R (arctan σ) cos (arctan σ)` for `σ < 3/4`, `Y σ` for `σ ≥ 3/4`,
* `x = lowSlopeCurveX r X` — `r (arctan σ) cos (arctan σ)` for `σ < 3/4`, `X σ` for `σ ≥ 3/4`,

is a free-tip envelope curve for `h`, `C²`-close to the semicircle's chord function `profileX`.

## The argument

`ε = 1/800` is small enough for everything below: the binding constraint is `8 ε ≤ 1/100`
(the second-derivative estimate), and `ε < 1` and `ε ≤ 1/100` are then automatic.  The two pieces agree on the whole interval
`(0, 4/5)` (for `σ < 3/4` by definition, for `3/4 ≤ σ ≤ 4/5` by the junction hypothesis `hjunc`),
so around every `σ < 4/5` the two-piece curve is *eventually equal* to the smooth radial
parametrisation, while for `σ ≥ 4/5` it is eventually equal to the anchor's `Y` (resp. `X`).

* **Regularity** (`Free/lowSlopeCurveBasic.lean`): `C^∞` on `(0,∞)`, positive limit at `0⁺`
  (`R 0`, which is `> 0` because `|R 0 - 1| ≤ ε < 1`), and the semicircular tail on `[1-τ, ∞)`.
* **Closeness to `profileX`** (`Free/radCurveClose.lean`): the radial parametrisation deviates from
  `cos (arctan ·) = profileX` in value, first and second derivative by at most `ε`, `2ε` and `8ε`
  respectively (the deviation formulas are the §4 formulas of `LowSlope/lowSlopeCurveY_derivs_sub`,
  valid for *all* `σ > 0`); with `8ε ≤ 1/100` this gives `CloseToProfileX`.  For `σ ≥ 4/5` the
  closeness is the anchor's (`CloseToProfileX Y`, resp. `X`), which is a hypothesis.
* **Monotonicity** on all of `(0,∞)`: for `σ < 3/4` it is the hypothesis `hmonoR`/`hmonor` (the
  ε-bounds alone cannot give it near `0`, cf. the discussion in `Step3Pieces.lean`); at `σ = 3/4`
  it follows from the deviation formula at `3/4` (where `|deriv profileX| ≥ 1/5`); for `σ > 3/4`
  it is the anchor's `x_deriv_neg`/`y_deriv_neg`.
* **The envelope fields** (`mono_*`, `shape_*`) are then supplied by
  `Work.OddEnvelope.Close.isEnvelopeCurveFree_of_close`, which derives them from the `C²`-closeness
  of the curve to `profileX` (`1/100`) and the smallness of `h` (from the bump class).
-/

namespace Work.OddCurve.Free

noncomputable section

open Set Filter
open scoped Topology ContDiff

/-- The radial parametrisation of a chord function: `σ ↦ ρ (arctan σ) * cos (arctan σ)`.
This is the low-slope piece of `LowSlope.lowSlopeCurveY ρ Y` (and of `lowSlopeCurveX ρ X`). -/
private def radPiece (ρ : ℝ → ℝ) : ℝ → ℝ := fun τ => ρ (Real.arctan τ) * Real.cos (Real.arctan τ)

/-- Transfer of the three `CloseToProfileX` estimates along an eventual equality. -/
private lemma closeTransfer {F G : ℝ → ℝ} {s : ℝ} (hev : F =ᶠ[𝓝 s] G)
    (hG : |G s - Work.OddEnvelope.profileX s| ≤ 1 / 100 ∧
      |deriv G s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv G) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 100) :
    |F s - Work.OddEnvelope.profileX s| ≤ 1 / 100 ∧
      |deriv F s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv F) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 100 := by
  have h1 := hev.eq_of_nhds
  have h2 := Filter.EventuallyEq.deriv_eq hev
  have h3 := Filter.EventuallyEq.deriv_eq (Filter.EventuallyEq.deriv hev)
  rw [h1, h2, h3]
  exact hG

/-- Below `4/5` the two-piece curve `lowSlopeCurveY R Y` is the radial parametrisation: the two
pieces agree on `[3/4, 4/5]` by the junction hypothesis. -/
private lemma lowSlopeCurveY_eventuallyEq {R Y : ℝ → ℝ}
    (hjunc : ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 4 / 5 →
      Y σ = R (Real.arctan σ) * Real.cos (Real.arctan σ))
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) (4 / 5)) :
    Work.OddCurve.LowSlope.lowSlopeCurveY R Y =ᶠ[𝓝 s] radPiece R := by
  filter_upwards [isOpen_Ioo.mem_nhds hs] with τ hτ
  rcases lt_or_ge τ (3 / 4) with h | h
  · exact Work.OddCurve.LowSlope.lowSlopeCurveY_of_lt h
  · exact (Work.OddCurve.LowSlope.lowSlopeCurveY_of_ge h).trans (hjunc τ h (le_of_lt hτ.2))

/-- The left-hand analogue of `lowSlopeCurveY_eventuallyEq`. -/
private lemma lowSlopeCurveX_eventuallyEq {r X : ℝ → ℝ}
    (hjunc : ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 4 / 5 →
      X σ = r (Real.arctan σ) * Real.cos (Real.arctan σ))
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) (4 / 5)) :
    Work.OddCurve.LowSlope.lowSlopeCurveX r X =ᶠ[𝓝 s] radPiece r := by
  filter_upwards [isOpen_Ioo.mem_nhds hs] with τ hτ
  rcases lt_or_ge τ (3 / 4) with h | h
  · exact Work.OddCurve.LowSlope.lowSlopeCurveX_of_lt h
  · exact (Work.OddCurve.LowSlope.lowSlopeCurveX_of_ge h).trans (hjunc τ h (le_of_lt hτ.2))

/-- Above `3/4` the two-piece curve is the anchor's. -/
private lemma lowSlopeCurveY_eventuallyEq_Y {R Y : ℝ → ℝ} {s : ℝ} (hs : 3 / 4 < s) :
    Work.OddCurve.LowSlope.lowSlopeCurveY R Y =ᶠ[𝓝 s] Y := by
  filter_upwards [isOpen_Ioi.mem_nhds hs] with τ hτ
  exact Work.OddCurve.LowSlope.lowSlopeCurveY_of_ge (le_of_lt hτ)

/-- The left-hand analogue of `lowSlopeCurveY_eventuallyEq_Y`. -/
private lemma lowSlopeCurveX_eventuallyEq_X {r X : ℝ → ℝ} {s : ℝ} (hs : 3 / 4 < s) :
    Work.OddCurve.LowSlope.lowSlopeCurveX r X =ᶠ[𝓝 s] X := by
  filter_upwards [isOpen_Ioi.mem_nhds hs] with τ hτ
  exact Work.OddCurve.LowSlope.lowSlopeCurveX_of_ge (le_of_lt hτ)

/-- `CloseToProfileX` of the right-hand two-piece curve, from the closeness of its low-slope piece
and the anchor's `CloseToProfileX Y`. -/
private lemma lowSlopeCurveY_closeToProfileX {R Y : ℝ → ℝ}
    (hclose : Work.OddCurve.LowSlope.CloseToProfileX (radPiece R))
    (hY : Work.OddCurve.LowSlope.CloseToProfileX Y)
    (hjunc : ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 4 / 5 → Y σ = radPiece R σ) :
    Work.OddCurve.LowSlope.CloseToProfileX (Work.OddCurve.LowSlope.lowSlopeCurveY R Y) := by
  intro s hs
  rcases lt_or_ge s (4 / 5) with hlt | hge
  · exact closeTransfer (lowSlopeCurveY_eventuallyEq hjunc ⟨hs, hlt⟩) (hclose s hs)
  · exact closeTransfer (lowSlopeCurveY_eventuallyEq_Y (lt_of_lt_of_le (by norm_num) hge)) (hY s hs)

/-- `CloseToProfileX` of the left-hand two-piece curve. -/
private lemma lowSlopeCurveX_closeToProfileX {r X : ℝ → ℝ}
    (hclose : Work.OddCurve.LowSlope.CloseToProfileX (radPiece r))
    (hX : Work.OddCurve.LowSlope.CloseToProfileX X)
    (hjunc : ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 4 / 5 → X σ = radPiece r σ) :
    Work.OddCurve.LowSlope.CloseToProfileX (Work.OddCurve.LowSlope.lowSlopeCurveX r X) := by
  intro s hs
  rcases lt_or_ge s (4 / 5) with hlt | hge
  · exact closeTransfer (lowSlopeCurveX_eventuallyEq hjunc ⟨hs, hlt⟩) (hclose s hs)
  · exact closeTransfer (lowSlopeCurveX_eventuallyEq_X (lt_of_lt_of_le (by norm_num) hge)) (hX s hs)

/-- Strict monotonicity of the right-hand two-piece curve: hypothesis on `(0, 3/4)`, the radial
estimate at `σ = 3/4`, and the anchor's monotonicity beyond. -/
private lemma lowSlopeCurveY_deriv_neg {R Y : ℝ → ℝ}
    (hY : ∀ s : ℝ, 0 < s → deriv Y s < 0)
    (hmono : ∀ σ : ℝ, 0 < σ → σ < 3 / 4 → deriv (radPiece R) σ < 0)
    (hjunc : ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 4 / 5 → Y σ = radPiece R σ)
    (h75 : deriv (radPiece R) (3 / 4) < 0) :
    ∀ s : ℝ, 0 < s → deriv (Work.OddCurve.LowSlope.lowSlopeCurveY R Y) s < 0 := by
  intro s hs
  rcases lt_trichotomy s (3 / 4) with hlt | heq | hgt
  · rw [Filter.EventuallyEq.deriv_eq
      (lowSlopeCurveY_eventuallyEq hjunc
        ⟨hs, by linarith [(by norm_num : (3 : ℝ) / 4 < 4 / 5), hlt]⟩)]
    exact hmono s hs hlt
  · subst heq
    rw [Filter.EventuallyEq.deriv_eq (lowSlopeCurveY_eventuallyEq hjunc ⟨by norm_num, by norm_num⟩)]
    exact h75
  · rw [Filter.EventuallyEq.deriv_eq (lowSlopeCurveY_eventuallyEq_Y hgt)]
    exact hY s hs

/-- Strict monotonicity of the left-hand two-piece curve. -/
private lemma lowSlopeCurveX_deriv_neg {r X : ℝ → ℝ}
    (hX : ∀ s : ℝ, 0 < s → deriv X s < 0)
    (hmono : ∀ σ : ℝ, 0 < σ → σ < 3 / 4 → deriv (radPiece r) σ < 0)
    (hjunc : ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 4 / 5 → X σ = radPiece r σ)
    (h75 : deriv (radPiece r) (3 / 4) < 0) :
    ∀ s : ℝ, 0 < s → deriv (Work.OddCurve.LowSlope.lowSlopeCurveX r X) s < 0 := by
  intro s hs
  rcases lt_trichotomy s (3 / 4) with hlt | heq | hgt
  · rw [Filter.EventuallyEq.deriv_eq
      (lowSlopeCurveX_eventuallyEq hjunc
        ⟨hs, by linarith [(by norm_num : (3 : ℝ) / 4 < 4 / 5), hlt]⟩)]
    exact hmono s hs hlt
  · subst heq
    rw [Filter.EventuallyEq.deriv_eq (lowSlopeCurveX_eventuallyEq hjunc ⟨by norm_num, by norm_num⟩)]
    exact h75
  · rw [Filter.EventuallyEq.deriv_eq (lowSlopeCurveX_eventuallyEq_X hgt)]
    exact hX s hs

/-- **The curve assembly of Step 3.**  With `ε = 1/800`: a radial pair with the sharp `ε`-bounds,
glued to an envelope curve along `[3/4, 4/5]` and monotone along the radial piece below `3/4`,
produces the two-piece curve, which is a free-tip envelope curve for `h` and `C²`-close to
`profileX`. -/
theorem lowSlopeCurveAssembly (n : ℕ) (hn : 1 ≤ n) :
    Work.OddCurve.Free.LowSlopeCurveAssemblySpec n := by
  refine ⟨1 / 800, by norm_num, ?_⟩
  intro h X Y R r hb hXY hcX hcY hRc hrc _hRend _hrend hbnd hjunc hmonoR hmonor _hshapeR _hshaper
  have hε0 : (0 : ℝ) ≤ 1 / 800 := by norm_num
  have hε8 : (8 : ℝ) * (1 / 800) ≤ 1 / 100 := by norm_num
  have hεlt : (1 / 800 : ℝ) < 1 := by norm_num
  have hR0 : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |R α - 1| ≤ (1 / 800 : ℝ) :=
    fun α hα => (hbnd α hα).1
  have hR1 : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv R α| ≤ (1 / 800 : ℝ) :=
    fun α hα => (hbnd α hα).2.1
  have hR2 : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv (deriv R) α| ≤ (1 / 800 : ℝ) :=
    fun α hα => (hbnd α hα).2.2.1
  have hr0 : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |r α - 1| ≤ (1 / 800 : ℝ) :=
    fun α hα => (hbnd α hα).2.2.2.1
  have hr1 : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv r α| ≤ (1 / 800 : ℝ) :=
    fun α hα => (hbnd α hα).2.2.2.2.1
  have hr2 : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv (deriv r) α| ≤ (1 / 800 : ℝ) :=
    fun α hα => (hbnd α hα).2.2.2.2.2
  obtain ⟨hcR, hnegR⟩ := radCurveClose R hRc hε0 hε8 hR0 hR1 hR2
  obtain ⟨hcr, hnegr⟩ := radCurveClose r hrc hε0 hε8 hr0 hr1 hr2
  obtain ⟨hsmY, hsmX, hlimY, hlimX, htailY, htailX⟩ :=
    lowSlopeCurveBasic h X Y R r hεlt hXY hRc hrc hR0 hr0 hjunc
  refine ⟨?_, ?_, ?_⟩
  · refine Work.OddEnvelope.Close.isEnvelopeCurveFree_of_close (δ := 1 / 100) (by norm_num)
      hsmX hsmY hXY.smooth_h
      (lowSlopeCurveX_deriv_neg hXY.x_deriv_neg hmonor (fun σ h1 h2 => (hjunc σ h1 h2).2)
        (hnegr (3 / 4) (by norm_num) (by norm_num)))
      (lowSlopeCurveY_deriv_neg hXY.y_deriv_neg hmonoR (fun σ h1 h2 => (hjunc σ h1 h2).1)
        (hnegR (3 / 4) (by norm_num) (by norm_num)))
      hlimX hlimY htailX htailY hXY.h_zero hXY.h_support
      (lowSlopeCurveX_closeToProfileX hcr hcX (fun σ h1 h2 => (hjunc σ h1 h2).2))
      (lowSlopeCurveY_closeToProfileX hcR hcY (fun σ h1 h2 => (hjunc σ h1 h2).1))
      (Work.OddVolterra.Existence.IsSmallFlatBumpThree.close_h (by norm_num) hb hn)
  · exact lowSlopeCurveX_closeToProfileX hcr hcX (fun σ h1 h2 => (hjunc σ h1 h2).2)
  · exact lowSlopeCurveY_closeToProfileX hcR hcY (fun σ h1 h2 => (hjunc σ h1 h2).1)

end

end Work.OddCurve.Free
