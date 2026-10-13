/-
Work module for the Elgindi finite-time singularity project.

# A.e. strong measurability of the radial slice of a mixed slot against `w²`

For `f` which is `C^∞` on the open quadrant (`Work.FTS.EllipticEst.SmoothOpen f`) and for an
interior angle `σ ∈ (0, π/2)`, the radial function

  `s ↦ (D_z^j D_θ^i f (s, σ))² · w(s)²`      (`w(s) = (1 + s)²/s²`)

is a.e. strongly measurable for `volume.restrict Iz` (`Iz = [0,∞)`).

At an interior angle the `z`-slice of `f` is `C^∞` on `(0,∞)`
(`Work.FTS.EllipticEst.SmoothOpen.curry_z`, applied to `Work.Spaces.mixed j i f`), so the
weighted mixed square is continuous there and hence a.e. strongly measurable
(`ContinuousOn.aestronglyMeasurable`); the single excluded point `s = 0` of `Iz = [0,∞)` is
null, so `volume.restrict Iz = volume.restrict (Ioi 0)`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.

Note on `π`: the statement below uses the *notation* `π` for `Real.pi`, so the file opens the
`Real` scope (`open scoped Real`), exactly as every other module of the chapter does.  Without
that scope a bare `π` would be auto-bound as a free variable of type `ℝ` and the statement
would not be the intended one.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.SupPort.AuxMixSq

/-- The square of the radial weight `w` is continuous away from `0`. -/
private lemma continuousOn_w_sq :
    ContinuousOn (fun s : ℝ => (Work.Spaces.w s) ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hnum : ContinuousOn (fun s : ℝ => ((1 + s) ^ 2) ^ 2) (Set.Ioi (0 : ℝ)) :=
    ((continuousOn_const.add continuousOn_id).pow 2).pow 2
  have hden : ContinuousOn (fun s : ℝ => (s ^ 2) ^ 2) (Set.Ioi (0 : ℝ)) :=
    (continuousOn_id.pow 2).pow 2
  refine (hnum.div hden (fun z hz => ?_)).congr (fun z _ => ?_)
  · exact pow_ne_zero 2 (pow_ne_zero 2 (ne_of_gt hz))
  · show (Work.Spaces.w z) ^ 2 = ((1 + z) ^ 2) ^ 2 / (z ^ 2) ^ 2
    rw [Work.Spaces.w, div_pow]

theorem aesm_zslice_mixed_sq_w {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (j i : ℕ) {σ : ℝ} (hσ : σ ∈ Set.Ioo 0 (π / 2)) :
    MeasureTheory.AEStronglyMeasurable
      (fun s => (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn
      (fun s : ℝ => (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      (Set.Ioi (0 : ℝ)) :=
    (((hF.mixed j i).curry_z hσ).continuousOn.pow 2).mul continuousOn_w_sq
  rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
  exact hcont.aestronglyMeasurable measurableSet_Ioi

end Work.FTS.StrongEps.SupPort.AuxMixSq
