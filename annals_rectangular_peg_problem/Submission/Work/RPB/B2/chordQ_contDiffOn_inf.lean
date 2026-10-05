import Mathlib
import Submission.Work.RPB.B2.PhaseDefs
import Submission.Work.RPB.B2.chordW_contDiff_inf

/-!
# Smoothness of `chordQ` on `{chordW ≠ 0}` (finite/`C^∞` order)

`chordQ c τ t r = ωC (chordW c τ t r) (chordWd c τ t r) / ‖chordW c τ t r‖^2` is `C^∞` on the
open set where `chordW` does not vanish.  This is the `C^∞`-order companion of
`chordQ_contDiffOn`, whose hypothesis is the *stronger* analytic regularity of `c`; here the
curve family is only assumed `C^∞`, so the analyticity argument is unavailable and we argue
directly with the finiteness-preserving operations:

* `chordW` and its `τ`-derivative `chordWd` are `C^∞` as functions of `(τ,t,r)`
  (`chordW_contDiff_inf`);
* the pairing `ωC` is a real polynomial in the two complex arguments, hence `C^∞`;
* `‖·‖²` is `C^∞` (`ContDiff.norm_sq`);
* a quotient of `C^∞` functions with nonvanishing denominator is `C^∞` (`ContDiffOn.div`).
-/

open Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B2

theorem chordQ_contDiffOn_inf (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × ℝ => c z.1 z.2)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × (ℝ × ℝ) => Work.RPB.B2.chordQ c z.1 z.2.1 z.2.2)
      {z | Work.RPB.B2.chordW c z.1 z.2.1 z.2.2 ≠ 0} := by
  obtain ⟨hW, hWd⟩ := chordW_contDiff_inf c hc
  -- the pairing `ωC : ℂ × ℂ → ℝ` is a real polynomial, hence `C^∞`.
  have hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℂ => Work.RPV.ωC p.1 p.2) := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℂ => (starRingEnd ℂ) p.1) :=
      Complex.conjCLE.contDiff.comp contDiff_fst
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℂ => p.2) := contDiff_snd
    have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℂ => (starRingEnd ℂ) p.1 * p.2) :=
      h1.mul h2
    have h4 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℂ × ℂ => ((starRingEnd ℂ) p.1 * p.2).im) :=
      Complex.imCLM.contDiff.comp h3
    simpa [Work.RPV.ωC] using h4
  have hnum : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × (ℝ × ℝ) =>
      Work.RPV.ωC (Work.RPB.B2.chordW c z.1 z.2.1 z.2.2)
        (Work.RPB.B2.chordWd c z.1 z.2.1 z.2.2)) :=
    hω.comp (hW.prodMk hWd)
  have hden : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × (ℝ × ℝ) =>
      ‖Work.RPB.B2.chordW c z.1 z.2.1 z.2.2‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp hW
  have hne : ∀ z ∈ {z : ℝ × (ℝ × ℝ) | Work.RPB.B2.chordW c z.1 z.2.1 z.2.2 ≠ 0},
      ‖Work.RPB.B2.chordW c z.1 z.2.1 z.2.2‖ ^ 2 ≠ 0 := by
    intro z hz
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (by simpa using hz))
  have hmain := ContDiffOn.div hnum.contDiffOn hden.contDiffOn hne
  convert hmain using 1
  · ext z; simp only [Work.RPB.B2.chordQ, Pi.div_apply]

end Work.RPB.B2
