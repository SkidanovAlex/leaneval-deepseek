/-
Copyright: work module for the Elgindi finite-time singularity project.

# The one-dimensional weighted Agmon inequality in the form consumed by `TermAgmon`

`Work.FTS.EllipticEst.AgmonFts.rDz_agmon_lintegral_fts` (proved, axiom-clean, in
`Submission/Work/FTS/EllipticEst/AgmonFts/LinAgmon.lean`) is the unconditional `ℝ≥0∞`-form of
the weighted Agmon inequality for the vector field `rDz h = z ∂_z h` and Elgindi's radial weight
`w z = (1+z)²/z²`, with `ρ = w²`:

  `ofReal (α²) * ∫⁻_{Iz} ρ (rDz h)² ≤ ofReal C * (∫⁻_{Iz} ρ h² + ofReal (α⁴) * ∫⁻_{Iz} ρ (z²h'')²)`.

The interface lemma `DzAgmon1D_lintegral` below restates it in exactly the shape that
`Work.FTS.EllipticEst.Blocks.TermAgmon` (and hence `hgen_of_agmon` in
`Blocks/HkNorm_Dz_amgm`) expects: the same half-line `volume.restrict (Set.Ioi 0)` rather than
`Iz = Ici 0` (the two measures agree, `MeasureTheory.restrict_Ioi_eq_restrict_Ici`), the first
radial derivative written out as `z * deriv h z` (`rDz h z` is definitionally this), the constant
presented as a square `ofReal (C²)` (absorbing the `√`), and the two summands of the right-hand
side in the order used downstream.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AgmonFts.LinAgmon

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Blocks

/-- **The weighted Agmon inequality for `D = z∂_z` on the half-line, `lintegral` form.**

There is a universal `C > 0` such that for every `0 < α ≤ 1` and every `h` of class `C^∞` on
`(0,∞)` (in terms of `Work.Stability.smoothOrder`, the *genuine* `C^∞` order, not the analytic
order `⊤`),

`ofReal (α²) * ∫⁻_{Ioi 0} ofReal (w(z)² (z h')²) ≤ ofReal (C²) *
   (ofReal (α⁴) * ∫⁻_{Ioi 0} ofReal (w(z)² (z²h'')²) + ∫⁻_{Ioi 0} ofReal (w(z)² h²))`.

No integrability hypothesis is required: if one of the two data integrals is `⊤` the inequality is
trivial, and otherwise it also yields the finiteness of `∫⁻ ρ (zh')²`. -/
theorem DzAgmon1D_lintegral : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi (0 : ℝ)) →
      ENNReal.ofReal (α ^ 2) *
          MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
            (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2))
        ≤ ENNReal.ofReal (C ^ 2) *
            (ENNReal.ofReal (α ^ 4) *
                MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                  (fun z => ENNReal.ofReal
                    ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2))
              + MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                  (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2))) := by
  obtain ⟨C₀, hC₀, hfts⟩ := Work.FTS.EllipticEst.AgmonFts.rDz_agmon_lintegral_fts
  refine ⟨Real.sqrt C₀, Real.sqrt_pos_of_pos hC₀, ?_⟩
  rw [Real.sq_sqrt hC₀.le]
  intro α h hα hα1 hh
  -- `Iz` and `Ioi 0` carry the same measure
  have hIz : ∀ F : ℝ → ENNReal, (MeasureTheory.lintegral
        (MeasureTheory.volume.restrict Work.Spaces.Iz) F)
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) F := by
    intro F
    show MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))) F
        = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) F
    rw [← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
  have hineq := hfts α hα hα1 h hh
  -- `rDz h z = z h'(z)` definitionally
  have hrDz : ∀ z : ℝ, Work.FTS.EllipticEst.rDz h z = z * deriv h z := fun z => rfl
  simp only [hrDz] at hineq
  have e1 : (MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz)
        (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2)))
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2)) := hIz _
  have e2 : (MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz)
        (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2)))
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2)) :=
    hIz _
  have e3 : (MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz)
        (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2)))
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2)) := hIz _
  rw [e1, e2, e3] at hineq
  refine hineq.trans (le_of_eq ?_)
  rw [add_comm]

end Work.FTS.EllipticEst.Blocks
