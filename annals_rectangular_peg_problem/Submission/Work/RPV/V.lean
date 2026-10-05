import Submission.Work.RPV.Defs
import Submission.Work.RPV.VBasic
import Mathlib
import Submission.Work.RPV.chordPS_circle_stdZ
import Submission.Work.RPV.chordPS_levelPt
import Submission.Work.RPV.chordPS_eq_iff_same_phase
import Submission.Work.RPV.dchord_symplectic
import Submission.Work.RPV.levelPt_omega
import Submission.Work.RPV.rect_of_tau_chord
import Submission.Work.RPV.tau_symplectic

/-!
# Rectangular peg: the full vocabulary API (`Work.RPV.V`)

**Import this module** (or, for a smaller dependency footprint, `Work.RPV.Defs` plus the
individual lemma modules) to get the whole vocabulary of the rectangular-peg development:
all definitions of the route design plus the V-lemmas and the glue.

Contents:

* `Submission.Work.RPV.Defs` — every definition and structure of the route document, verbatim:
  `PS`, `symp`, `Tk`, `Zsec`, `stdZ`, `K0`, `tau`, `uproj`, `hamVF`, `chordPS`, `levelPt`, `ωC`,
  `dchord`, `CptPerHam`, `IsFlow`, `dq`, `dP`, `IsType2GF`, `Wrot`, `chainAction`, `LagFamily`,
  `CurveIsotopy`, `HasThetaRect`, plus the extra abbreviation `IsSmoothJordan` for the hypothesis
  `IsSmoothEmbedding (𝓡 1) 𝓘(ℝ,ℂ) ∞ γ` of the challenge.
* `Submission.Work.RPV.VBasic` — elementary coordinate algebra: `symp` bilinearity and
  nondegeneracy, the `Tk`/`tau` group laws, `K0_Tk`, `uproj_Tk`, `K0_tau`, `uproj_tau`, `tau_pi`,
  `Tk_tau`, `K0_levelPt`, `uproj_levelPt`, `uproj_chordPS`, `chordPS_swap`, `ωC_skew`,
  `ωC_self`, `ωC_mul_I`, and `IsSmoothJordan.contMDiff`/`.injective`.
* `Submission.Work.RPV.chordPS_levelPt` — `chordPS z w a = levelPt ((z+w)/√2) (-‖z-w‖²/4) a`,
  the bridge between the two charts (whence `K0_chordPS` below).
* `Submission.Work.RPV.chordPS_circle` — chords of the unit circle lie on the zero section.
* `Submission.Work.RPV.rect_of_tau_chord` — two chords exchanged by `τ_θ` span a `θ`-rectangle.
* `Submission.Work.RPV.dchord_symplectic` — the chord chart is symplectic.
* `Submission.Work.RPV.levelPt_omega` — level-curve families give Lagrangian surfaces.
* `Submission.Work.RPV.eq_of_K0_uproj` — `(K0, uproj, q₂)` determines a point of `PS`
  (the "no spurious coincidences" coordinate fact).
* `Submission.Work.RPV.chordPS_eq_iff_same_phase` — the fibres of the chord chart.
* `Submission.Work.RPV.symp_hamVF` — `symp (hamVF H x) v = -fderiv ℝ H x v`; the companion
  `hamVF_symp` below.
* `Submission.Work.RPV.exists_two_points`, `Submission.Work.RPV.theorem_1_of_main` — the G1 glue.
* `Submission.Work.RPV.Glue` — the node hypotheses `CoreNode`, `CurveIsotopyNode`,
  `LagFamilyNode`, `LagIsotopyNode`, `Theorem1OfMainNode`, the reduction `main_rect_of_nodes`,
  and the final wiring `theorem_1_of_nodes`.  (Not imported here: import
  `Submission.Work.RPV.Glue` for the glue and `Submission.Work.RPV.theorem_1_of_main` for the
  G1 node; this module is the pure vocabulary API.)
-/
/-
Also in this module: `K0_chordPS`, `chordPS_eq_iff` (with `chordPS_eq_iff_same_phase`), and
`hamVF_symp` (the positive-sign companion of `symp_hamVF`).
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPV

/-- `K₀` of a chord is `|z-w|²/4 - 1`: the level of the chord. -/
theorem K0_chordPS (z w : ℂ) (a : ℝ) : K0 (chordPS z w a) = ‖z - w‖ ^ 2 / 4 - 1 := by
  rw [chordPS_levelPt, K0_levelPt]
  ring

/-- Equality of chords: the phase, the midpoint and the length of the chord determine the point
of `PS`, and conversely. -/
theorem chordPS_eq_iff {z w z' w' : ℂ} {a a' : ℝ} :
    chordPS z w a = chordPS z' w' a' ↔
      a = a' ∧ z + w = z' + w' ∧ ‖z - w‖ = ‖z' - w'‖ := by
  constructor
  · intro h
    have ha : a = a' := by
      have h1 := congrArg (fun x : PS => x.1.2) h
      simpa [chordPS] using h1
    have h' : chordPS z w a' = chordPS z' w' a' := by rw [ha] at h; exact h
    exact ⟨ha, (chordPS_eq_iff_same_phase (z := z) (w := w) (z' := z') (w' := w')).mp h'⟩
  · rintro ⟨rfl, h1, h2⟩
    exact (chordPS_eq_iff_same_phase (z := z) (w := w) (z' := z') (w' := w')).mpr ⟨h1, h2⟩

end Work.RPV
