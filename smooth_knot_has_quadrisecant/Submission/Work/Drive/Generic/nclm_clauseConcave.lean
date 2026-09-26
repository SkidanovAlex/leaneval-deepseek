import Mathlib
import Submission.Work.Drive.Generic.nclmPkg
import Submission.Work.Drive.Generic.nclmDefs
import Submission.Work.Drive.Generic.nclmDev
import Submission.Work.Drive.Generic.nclmWindow
import Submission.Work.Drive.Nclm.curv_sign
import Submission.Work.Drive.lensConcaveInChordCoord
import Submission.Work.Drive.CDC.glue
import Submission.Work.Drive.AB.windowDataSmall

namespace Work.Drive.Generic

/-!
# The chord-concavity clause of the needle's chart

The package `Work.Drive.Generic.nclmPkgConcave` asks that the profile `H̃ = nclmAH` of the retained
arc be concave *in the chord coordinate* `X̃ = nclmAX`, uniformly over the ε-window of sweep
parameters.

The proof is a packaging of three ingredients that already exist in the library:

* `Work.Drive.lensConcaveInChordCoord` — the abstract brick: `H'' x' - H' x'' ≤ 0` on the interior
  implies the chord-coordinate concavity (via the monotonicity of `H' / x'`);
* `Work.Drive.Nclm.curv_sign` — the sign of the curvature numerator
  `⟪r' ∧ r'', v ∧ chartE⟫ ≤ 0` on every retained arc of the window, which, through the second
  derivatives of `nclmAX`/`nclmAH` (`cdc_nclm_deriv2_nclmAX`, `cdc_nclm_deriv2_nclmAH`) is exactly
  the hypothesis `H'' x' - H' x'' ≤ 0` (`cdc_nclm_curv_of_cross`, `cdc_arc_concave`);
* `Work.Drive.Generic.nclm_tang` together with the window comparison `nclm_window_eps` — the
  tangent pairing `⟪r', v⟫ ≥ m/4 > 0` on the retained arcs, which gives the strict monotonicity and
  the positive derivative of the abscissa `X̃` (`cdc_arc_mono`, via `nclm_deriv_nclmAX`).

`Work.Drive.CDC.glue` (already complete) assembles these three into
`cdc_arc_concave`; this file only performs the threshold bookkeeping (a `min` of the finitely many
ε-levels and Λ-levels) and the passage from the chord direction hypothesis
`chordEndB - chordEndA = ‖…‖ • v` to the unit normalisation used by `nclm_tang`.
-/

open LeanEval.KnotTheory.Quadrisecant

theorem nclm_clauseConcave {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    Work.Drive.Generic.nclmPkgConcave r D := by
  unfold Work.Drive.Generic.nclmPkgConcave
  -- the three ε-levels: the curvature sign, the tangent pairing and the chord non-degeneracy
  obtain ⟨εc, hεc0, hεc12, hCurv⟩ := Work.Drive.Nclm.curv_sign hr hinfl D
  obtain ⟨εt, hεt0, hεt12, hTang⟩ := nclm_tang hr D
  obtain ⟨εv, hεv0, hεv1, hVwin⟩ := Work.Drive.windowDataSmall hr D 1 (by norm_num)
  refine ⟨min (min εc εt) εv, lt_min (lt_min hεc0 hεt0) hεv0, ?_⟩
  intro ε hε0 hεε₀
  have hεc : ε ≤ εc := le_trans hεε₀ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hεt : ε ≤ εt := le_trans hεε₀ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hεv : ε ≤ εv := le_trans hεε₀ (min_le_right _ _)
  have hε1 : ε < 1 := lt_of_le_of_lt hεv hεv1
  obtain ⟨Λc, hΛc0, hΛc14, hCurvΛ⟩ := hCurv ε hε0 hεc
  obtain ⟨Λw, hΛw0, hWin⟩ := nclm_window_eps D hε0 hε1
  refine ⟨min Λc Λw, lt_min hΛc0 hΛw0, ?_⟩
  intro lam δ₁ δ₂ hlam0 hlamΛ hlam12 hδ₁0 hδ₁Λ hδ₂0 hδ₂Λ hδ₂ε v hv hcv
  have hlamΛc : lam ≤ Λc := le_trans hlamΛ (min_le_left _ _)
  have hδ₁Λc : δ₁ ≤ Λc := le_trans hδ₁Λ (min_le_left _ _)
  have hδ₂Λc : δ₂ ≤ Λc := le_trans hδ₂Λ (min_le_left _ _)
  have hδ₂Λw : δ₂ ≤ Λw := le_trans hδ₂Λ (min_le_right _ _)
  have hlam0' : 0 ≤ lam := hlam0.le
  have hlam1' : lam ≤ 1 := by linarith
  -- the (non-degenerate) chord of the needle
  set C : Space := Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε with hCdef
  have hCne : C ≠ 0 := by
    rw [hCdef]
    exact sub_ne_zero.mpr (hVwin δ₂ ε hδ₂0 hδ₂ε hε0 hεv).2.1
  have hCnorm : ‖C‖ ≠ 0 := norm_ne_zero_iff.mpr hCne
  have hcv' : C = ‖C‖ • v := by
    rw [hCdef]
    exact hcv
  -- `nclm_tang` is stated for the normalised chord, which is `v`
  have hvC : v = ‖C‖⁻¹ • C := by
    have h1 : ‖C‖ • v = C := hcv'.symm
    calc v = ‖C‖⁻¹ • (‖C‖ • v) := by rw [smul_smul, inv_mul_cancel₀ hCnorm, one_smul]
      _ = ‖C‖⁻¹ • C := by rw [h1]
  have hWε : 0 < Work.Drive.sweepW' D ε := Work.Drive.wds_sweepW'_pos D hε0 hε1
  have hWfun : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → 0 < Work.Drive.sweepW' D σ := by
    intro σ h1 h2
    have h := (hWin δ₂ σ hδ₂0 hδ₂Λw hδ₂ε h1 h2).1
    linarith
  have htan : ∀ (σ x : ℝ), ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      x ∈ Set.Icc (Work.Drive.taR D σ) (Work.Drive.tbR D σ) →
      ‖velocity r (Work.Drive.taR D 0)‖ / 4 ≤ inner ℝ (velocity r x) v := by
    intro σ x h1 h2 h3
    have h := hTang δ₂ ε σ x hδ₂0 hδ₂ε hε0 hεt h1 h2 h3
    rw [hvC]
    exact h
  have hm : 0 < ‖velocity r (Work.Drive.taR D 0)‖ :=
    norm_pos_iff.mpr (hr.regular (Work.Drive.taR D 0))
  obtain ⟨hmonoF, hxposF, -, -⟩ :=
    cdc_arc_mono hr D (m := ‖velocity r (Work.Drive.taR D 0)‖) hm hlam0' hlam1' htan hWfun
  intro σ hσlo hσhi
  exact cdc_arc_concave hr D (hWfun σ hσlo hσhi) (hmonoF σ hσlo hσhi) (hxposF σ hσlo hσhi)
    (hCurvΛ lam δ₁ δ₂ hlam0 hlamΛc hlam12 hδ₁0 hδ₁Λc hδ₂0 hδ₂Λc hδ₂ε v hv hcv σ hσlo hσhi)

end Work.Drive.Generic
