import Mathlib
import Submission.Work.OddCurve.Free.lowSlopeCurveAssembly
import Submission.Work.OddCurve.Free.Step3Pieces

/-!
# The curve assembly at the fixed smallness `ε = 1/800`

`Work.OddCurve.Free.lowSlopeCurveAssembly` proves

`∃ ε > 0, ∀ (h X Y R r), IsSmallFlatBumpThree n ε h → … → IsEnvelopeCurveFree h … ∧ …`

i.e. it produces *some* threshold `ε` (its proof takes `ε = 1/800`, so the threshold is in fact
`1/800`), but the existential is opaque: a consumer who has a bump class at the *fixed* level
`1/800` — e.g. because it constructed `h` from a `C^{2n+2}` bump of size `ε ≤ 1/800` and therefore
only knows `IsSmallFlatBumpThree n (1/800) h` (`IsSmallFlatBumpThree.mono`) — cannot apply it.

This file supplies that consumer's lemma: the same assembly, with the bump class and the radial
bounds both at the literal level `1/800`.  Its proof is the proof of
`Work.OddCurve.Free.lowSlopeCurveAssembly` with `ε` fixed at `1/800`; the auxiliary lemmas of that
file are `private`, so they are reproduced here (under the same names, in this file's namespace).

The mathematical content is unchanged: `8 · (1/800) ≤ 1/100` is the binding constraint, `1/800 < 1`
and `1/800 ≤ 1/100` are then automatic.
-/

namespace Work.OddVolterra.Free

noncomputable section

open Set Filter
open scoped Topology ContDiff

/-- The radial parametrisation of a chord function: `σ ↦ ρ (arctan σ) * cos (arctan σ)`.
This is the low-slope piece of `LowSlope.lowSlopeCurveY ρ Y` (and of `lowSlopeCurveX ρ X`). -/
private def radPiece8 (ρ : ℝ → ℝ) : ℝ → ℝ := fun τ => ρ (Real.arctan τ) * Real.cos (Real.arctan τ)

/-- Transfer of the three `CloseToProfileX` estimates along an eventual equality. -/
private lemma closeTransfer8 {F G : ℝ → ℝ} {s : ℝ} (hev : F =ᶠ[𝓝 s] G)
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
private lemma lowSlopeCurveY_eventuallyEq8 {R Y : ℝ → ℝ}
    (hjunc : ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 4 / 5 →
      Y σ = R (Real.arctan σ) * Real.cos (Real.arctan σ))
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) (4 / 5)) :
    Work.OddCurve.LowSlope.lowSlopeCurveY R Y =ᶠ[𝓝 s] radPiece8 R := by
  filter_upwards [isOpen_Ioo.mem_nhds hs] with τ hτ
  rcases lt_or_ge τ (3 / 4) with h | h
  · exact Work.OddCurve.LowSlope.lowSlopeCurveY_of_lt h
  · exact (Work.OddCurve.LowSlope.lowSlopeCurveY_of_ge h).trans (hjunc τ h (le_of_lt hτ.2))

/-- The left-hand analogue of `lowSlopeCurveY_eventuallyEq8`. -/
private lemma lowSlopeCurveX_eventuallyEq8 {r X : ℝ → ℝ}
    (hjunc : ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 4 / 5 →
      X σ = r (Real.arctan σ) * Real.cos (Real.arctan σ))
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) (4 / 5)) :
    Work.OddCurve.LowSlope.lowSlopeCurveX r X =ᶠ[𝓝 s] radPiece8 r := by
  filter_upwards [isOpen_Ioo.mem_nhds hs] with τ hτ
  rcases lt_or_ge τ (3 / 4) with h | h
  · exact Work.OddCurve.LowSlope.lowSlopeCurveX_of_lt h
  · exact (Work.OddCurve.LowSlope.lowSlopeCurveX_of_ge h).trans (hjunc τ h (le_of_lt hτ.2))

/-- Above `3/4` the two-piece curve is the anchor's. -/
private lemma lowSlopeCurveY_eventuallyEq_Y8 {R Y : ℝ → ℝ} {s : ℝ} (hs : 3 / 4 < s) :
    Work.OddCurve.LowSlope.lowSlopeCurveY R Y =ᶠ[𝓝 s] Y := by
  filter_upwards [isOpen_Ioi.mem_nhds hs] with τ hτ
  exact Work.OddCurve.LowSlope.lowSlopeCurveY_of_ge (le_of_lt hτ)

/-- The left-hand analogue of `lowSlopeCurveY_eventuallyEq_Y8`. -/
private lemma lowSlopeCurveX_eventuallyEq_X8 {r X : ℝ → ℝ} {s : ℝ} (hs : 3 / 4 < s) :
    Work.OddCurve.LowSlope.lowSlopeCurveX r X =ᶠ[𝓝 s] X := by
  filter_upwards [isOpen_Ioi.mem_nhds hs] with τ hτ
  exact Work.OddCurve.LowSlope.lowSlopeCurveX_of_ge (le_of_lt hτ)

/-- `CloseToProfileX` of the right-hand two-piece curve, from the closeness of its low-slope piece
and the anchor's `CloseToProfileX Y`. -/
private lemma lowSlopeCurveY_closeToProfileX8 {R Y : ℝ → ℝ}
    (hclose : Work.OddCurve.LowSlope.CloseToProfileX (radPiece8 R))
    (hY : Work.OddCurve.LowSlope.CloseToProfileX Y)
    (hjunc : ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 4 / 5 → Y σ = radPiece8 R σ) :
    Work.OddCurve.LowSlope.CloseToProfileX (Work.OddCurve.LowSlope.lowSlopeCurveY R Y) := by
  intro s hs
  rcases lt_or_ge s (4 / 5) with hlt | hge
  · exact closeTransfer8 (lowSlopeCurveY_eventuallyEq8 hjunc ⟨hs, hlt⟩) (hclose s hs)
  · exact closeTransfer8 (lowSlopeCurveY_eventuallyEq_Y8 (lt_of_lt_of_le (by norm_num) hge))
      (hY s hs)

/-- `CloseToProfileX` of the left-hand two-piece curve. -/
private lemma lowSlopeCurveX_closeToProfileX8 {r X : ℝ → ℝ}
    (hclose : Work.OddCurve.LowSlope.CloseToProfileX (radPiece8 r))
    (hX : Work.OddCurve.LowSlope.CloseToProfileX X)
    (hjunc : ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 4 / 5 → X σ = radPiece8 r σ) :
    Work.OddCurve.LowSlope.CloseToProfileX (Work.OddCurve.LowSlope.lowSlopeCurveX r X) := by
  intro s hs
  rcases lt_or_ge s (4 / 5) with hlt | hge
  · exact closeTransfer8 (lowSlopeCurveX_eventuallyEq8 hjunc ⟨hs, hlt⟩) (hclose s hs)
  · exact closeTransfer8 (lowSlopeCurveX_eventuallyEq_X8 (lt_of_lt_of_le (by norm_num) hge))
      (hX s hs)

/-- Strict monotonicity of the right-hand two-piece curve: hypothesis on `(0, 3/4)`, the radial
estimate at `σ = 3/4`, and the anchor's monotonicity beyond. -/
private lemma lowSlopeCurveY_deriv_neg8 {R Y : ℝ → ℝ}
    (hY : ∀ s : ℝ, 0 < s → deriv Y s < 0)
    (hmono : ∀ σ : ℝ, 0 < σ → σ < 3 / 4 → deriv (radPiece8 R) σ < 0)
    (hjunc : ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 4 / 5 → Y σ = radPiece8 R σ)
    (h75 : deriv (radPiece8 R) (3 / 4) < 0) :
    ∀ s : ℝ, 0 < s → deriv (Work.OddCurve.LowSlope.lowSlopeCurveY R Y) s < 0 := by
  intro s hs
  rcases lt_trichotomy s (3 / 4) with hlt | heq | hgt
  · rw [Filter.EventuallyEq.deriv_eq
      (lowSlopeCurveY_eventuallyEq8 hjunc
        ⟨hs, by linarith [(by norm_num : (3 : ℝ) / 4 < 4 / 5), hlt]⟩)]
    exact hmono s hs hlt
  · subst heq
    rw [Filter.EventuallyEq.deriv_eq (lowSlopeCurveY_eventuallyEq8 hjunc ⟨by norm_num, by norm_num⟩)]
    exact h75
  · rw [Filter.EventuallyEq.deriv_eq (lowSlopeCurveY_eventuallyEq_Y8 hgt)]
    exact hY s hs

/-- Strict monotonicity of the left-hand two-piece curve. -/
private lemma lowSlopeCurveX_deriv_neg8 {r X : ℝ → ℝ}
    (hX : ∀ s : ℝ, 0 < s → deriv X s < 0)
    (hmono : ∀ σ : ℝ, 0 < σ → σ < 3 / 4 → deriv (radPiece8 r) σ < 0)
    (hjunc : ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 4 / 5 → X σ = radPiece8 r σ)
    (h75 : deriv (radPiece8 r) (3 / 4) < 0) :
    ∀ s : ℝ, 0 < s → deriv (Work.OddCurve.LowSlope.lowSlopeCurveX r X) s < 0 := by
  intro s hs
  rcases lt_trichotomy s (3 / 4) with hlt | heq | hgt
  · rw [Filter.EventuallyEq.deriv_eq
      (lowSlopeCurveX_eventuallyEq8 hjunc
        ⟨hs, by linarith [(by norm_num : (3 : ℝ) / 4 < 4 / 5), hlt]⟩)]
    exact hmono s hs hlt
  · subst heq
    rw [Filter.EventuallyEq.deriv_eq (lowSlopeCurveX_eventuallyEq8 hjunc ⟨by norm_num, by norm_num⟩)]
    exact h75
  · rw [Filter.EventuallyEq.deriv_eq (lowSlopeCurveX_eventuallyEq_X8 hgt)]
    exact hX s hs

/-- **The curve assembly at a general smallness `ε`.**  This is
`Work.OddCurve.Free.lowSlopeCurveAssembly` with the threshold of the existential made explicit:
for every `ε ≥ 0` with `8 ε ≤ 1/100`, a radial pair with the `ε`-bounds, glued to an envelope curve
along `[3/4, 4/5]` and monotone along the radial piece below `3/4`, produces the two-piece curve,
which is a free-tip envelope curve for `h` and `C²`-close to `profileX`. -/
theorem lowSlopeCurveAssemblyEps (n : ℕ) (hn : 1 ≤ n) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε8 : 8 * ε ≤ 1 / 100) {h X Y R r : ℝ → ℝ}
    (hb : Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h)
    (hXY : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hcX : Work.OddCurve.LowSlope.CloseToProfileX X)
    (hcY : Work.OddCurve.LowSlope.CloseToProfileX Y)
    (hRc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hrc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hbnd : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |R α - 1| ≤ ε ∧ |deriv R α| ≤ ε ∧ |deriv (deriv R) α| ≤ ε ∧
      |r α - 1| ≤ ε ∧ |deriv r α| ≤ ε ∧ |deriv (deriv r) α| ≤ ε)
    (hjunc : ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 4 / 5 →
      Y σ = R (Real.arctan σ) * Real.cos (Real.arctan σ) ∧
      X σ = r (Real.arctan σ) * Real.cos (Real.arctan σ))
    (hmonoR : ∀ σ : ℝ, 0 < σ → σ < 3 / 4 →
      deriv (fun τ : ℝ => R (Real.arctan τ) * Real.cos (Real.arctan τ)) σ < 0)
    (hmonor : ∀ σ : ℝ, 0 < σ → σ < 3 / 4 →
      deriv (fun τ : ℝ => r (Real.arctan τ) * Real.cos (Real.arctan τ)) σ < 0)
    (hshapeR : ∀ σ : ℝ, 0 < σ → σ < 3 / 4 →
      0 < 2 * (deriv (fun τ : ℝ => R (Real.arctan τ) * Real.cos (Real.arctan τ)) σ) ^ 2 -
        (R (Real.arctan σ) * Real.cos (Real.arctan σ)) *
          deriv (deriv (fun τ : ℝ => R (Real.arctan τ) * Real.cos (Real.arctan τ))) σ)
    (hshaper : ∀ σ : ℝ, 0 < σ → σ < 3 / 4 →
      0 < 2 * (deriv (fun τ : ℝ => r (Real.arctan τ) * Real.cos (Real.arctan τ)) σ) ^ 2 -
        (r (Real.arctan σ) * Real.cos (Real.arctan σ)) *
          deriv (deriv (fun τ : ℝ => r (Real.arctan τ) * Real.cos (Real.arctan τ))) σ) :
    Work.OddCurve.Free.IsEnvelopeCurveFree h (Work.OddCurve.LowSlope.lowSlopeCurveX r X)
        (Work.OddCurve.LowSlope.lowSlopeCurveY R Y) ∧
      Work.OddCurve.LowSlope.CloseToProfileX (Work.OddCurve.LowSlope.lowSlopeCurveX r X) ∧
      Work.OddCurve.LowSlope.CloseToProfileX (Work.OddCurve.LowSlope.lowSlopeCurveY R Y) := by
  have hε800 : ε ≤ 1 / 800 := by linarith
  have hεlt : ε < 1 := lt_of_le_of_lt hε800 (by norm_num)
  have hcloseh : ∀ s : ℝ, |h s| ≤ 1 / 100 ∧ |deriv h s| ≤ 1 / 100 ∧
      |deriv (deriv h) s| ≤ 1 / 100 :=
    Work.OddVolterra.Existence.IsSmallFlatBumpThree.close_h (le_trans hε800 (by norm_num)) hb hn
  have hR0 : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |R α - 1| ≤ ε :=
    fun α hα => (hbnd α hα).1
  have hR1 : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv R α| ≤ ε :=
    fun α hα => (hbnd α hα).2.1
  have hR2 : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv (deriv R) α| ≤ ε :=
    fun α hα => (hbnd α hα).2.2.1
  have hr0 : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |r α - 1| ≤ ε :=
    fun α hα => (hbnd α hα).2.2.2.1
  have hr1 : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv r α| ≤ ε :=
    fun α hα => (hbnd α hα).2.2.2.2.1
  have hr2 : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv (deriv r) α| ≤ ε :=
    fun α hα => (hbnd α hα).2.2.2.2.2
  obtain ⟨hcR, hnegR⟩ := Work.OddCurve.Free.radCurveClose R hRc hε0 hε8 hR0 hR1 hR2
  obtain ⟨hcr, hnegr⟩ := Work.OddCurve.Free.radCurveClose r hrc hε0 hε8 hr0 hr1 hr2
  obtain ⟨hsmY, hsmX, hlimY, hlimX, htailY, htailX⟩ :=
    Work.OddCurve.Free.lowSlopeCurveBasic h X Y R r hεlt hXY hRc hrc hR0 hr0 hjunc
  have hcloseX : Work.OddCurve.LowSlope.CloseToProfileX
      (Work.OddCurve.LowSlope.lowSlopeCurveX r X) :=
    lowSlopeCurveX_closeToProfileX8 hcr hcX (fun σ h1 h2 => (hjunc σ h1 h2).2)
  have hcloseY : Work.OddCurve.LowSlope.CloseToProfileX
      (Work.OddCurve.LowSlope.lowSlopeCurveY R Y) :=
    lowSlopeCurveY_closeToProfileX8 hcR hcY (fun σ h1 h2 => (hjunc σ h1 h2).1)
  refine ⟨?_, hcloseX, hcloseY⟩
  refine Work.OddEnvelope.Close.isEnvelopeCurveFree_of_close (δ := 1 / 100) (by norm_num)
    hsmX hsmY hXY.smooth_h
    (lowSlopeCurveX_deriv_neg8 hXY.x_deriv_neg hmonor (fun σ h1 h2 => (hjunc σ h1 h2).2)
      (hnegr (3 / 4) (by norm_num) (by norm_num)))
    (lowSlopeCurveY_deriv_neg8 hXY.y_deriv_neg hmonoR (fun σ h1 h2 => (hjunc σ h1 h2).1)
      (hnegR (3 / 4) (by norm_num) (by norm_num)))
    hlimX hlimY htailX htailY hXY.h_zero hXY.h_support
    hcloseX hcloseY hcloseh

/-- **The curve assembly of Step 3 at the fixed level `1/800`.**  A radial pair with the `1/800`
bounds on its deviation from `1` and on its first two derivatives, glued to an envelope curve
`(h, X, Y)` of a `C^{n+3}` bump of size `1/800` along the window `[3/4, 4/5]`, whose two radial
pieces are monotone and concave below `3/4`, produces the two-piece curve

* `y = lowSlopeCurveY R Y` — `R (arctan σ) cos (arctan σ)` for `σ < 3/4`, `Y σ` for `σ ≥ 3/4`,
* `x = lowSlopeCurveX r X` — `r (arctan σ) cos (arctan σ)` for `σ < 3/4`, `X σ` for `σ ≥ 3/4`,

which is a free-tip envelope curve for `h` and `C²`-close to the semicircle's chord function. -/
theorem lowSlopeCurveAssembly800 (n : ℕ) (hn : 1 ≤ n) {h X Y R r : ℝ → ℝ}
    (hb : Work.OddVolterra.Existence.IsSmallFlatBumpThree n (1 / 800) h)
    (hXY : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hcX : Work.OddCurve.LowSlope.CloseToProfileX X)
    (hcY : Work.OddCurve.LowSlope.CloseToProfileX Y)
    (hRc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hrc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hRend : R (Real.pi / 2) = 1) (hrend : r (Real.pi / 2) = 1)
    (hbnd : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |R α - 1| ≤ 1 / 800 ∧ |deriv R α| ≤ 1 / 800 ∧ |deriv (deriv R) α| ≤ 1 / 800 ∧
      |r α - 1| ≤ 1 / 800 ∧ |deriv r α| ≤ 1 / 800 ∧ |deriv (deriv r) α| ≤ 1 / 800)
    (hjunc : ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 4 / 5 →
      Y σ = R (Real.arctan σ) * Real.cos (Real.arctan σ) ∧
      X σ = r (Real.arctan σ) * Real.cos (Real.arctan σ))
    (hmonoR : ∀ σ : ℝ, 0 < σ → σ < 3 / 4 →
      deriv (fun τ : ℝ => R (Real.arctan τ) * Real.cos (Real.arctan τ)) σ < 0)
    (hmonor : ∀ σ : ℝ, 0 < σ → σ < 3 / 4 →
      deriv (fun τ : ℝ => r (Real.arctan τ) * Real.cos (Real.arctan τ)) σ < 0)
    (hshapeR : ∀ σ : ℝ, 0 < σ → σ < 3 / 4 →
      0 < 2 * (deriv (fun τ : ℝ => R (Real.arctan τ) * Real.cos (Real.arctan τ)) σ) ^ 2 -
        (R (Real.arctan σ) * Real.cos (Real.arctan σ)) *
          deriv (deriv (fun τ : ℝ => R (Real.arctan τ) * Real.cos (Real.arctan τ))) σ)
    (hshaper : ∀ σ : ℝ, 0 < σ → σ < 3 / 4 →
      0 < 2 * (deriv (fun τ : ℝ => r (Real.arctan τ) * Real.cos (Real.arctan τ)) σ) ^ 2 -
        (r (Real.arctan σ) * Real.cos (Real.arctan σ)) *
          deriv (deriv (fun τ : ℝ => r (Real.arctan τ) * Real.cos (Real.arctan τ))) σ) :
    Work.OddCurve.Free.IsEnvelopeCurveFree h (Work.OddCurve.LowSlope.lowSlopeCurveX r X)
        (Work.OddCurve.LowSlope.lowSlopeCurveY R Y) ∧
      Work.OddCurve.LowSlope.CloseToProfileX (Work.OddCurve.LowSlope.lowSlopeCurveX r X) ∧
      Work.OddCurve.LowSlope.CloseToProfileX (Work.OddCurve.LowSlope.lowSlopeCurveY R Y) :=
  lowSlopeCurveAssemblyEps n hn (by norm_num) (by norm_num) hb hXY hcX hcY hRc hrc hbnd hjunc
    hmonoR hmonor hshapeR hshaper

end

end Work.OddVolterra.Free
