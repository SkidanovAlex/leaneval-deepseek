/-
# `Submission/Work/FTS/StrongEps/E5Aux2/L12XnBound.lean`

`|L₁₂ f z| ≤ C · Xn α f` for an `ℋ⁴`-honest profile `f`, uniformly in `α > 0` and `z ≥ 0`.

This is the statement `Work.FTS.StrongEps.L12_abs_le_Xn` of
`Submission/Work/FTS/StrongEps/EpsWPBounds.lean`, re-derived here from its one ingredient
`Work.FTS.StrongEps.L12.L12_z_lipschitz` (whose import cone is small) so that the
`N₀`-density chapter does not have to import `EpsWPBounds` — whose transitive closure contains
the oversized `Submission/Work/FTS/RegExportIface/Defs.lean`, which the build guard refuses to
elaborate.  The proof is copied verbatim from `EpsWPBounds`: apply the Lipschitz bound at the pair
`(f, 0)` and use `L₁₂(0) = 0` and `1/√(1+z) ≤ 1`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.L12.L12_z_lipschitz
import Submission.Work.FTS.Galerkin.Inhabit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

set_option autoImplicit false

/-- **A sup bound for `L₁₂(·)(z)` on the whole domain, from the `ℋ⁴`-size of the profile.** -/
theorem L12XnBound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ f : Work.FTS.Galerkin.Fn,
    Work.FTS.VocabO.HQo α 4 f → ∀ z : ℝ, 0 ≤ z →
      |Work.Construction.L12 f z| ≤ C * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨C, hCpos, hkey⟩ := Work.FTS.StrongEps.L12.L12_z_lipschitz
  refine ⟨C, hCpos, fun α hα f hf z hz => ?_⟩
  have hzero_sm : Work.FTS.EllipticEst.SmoothOpen (fun _ _ : ℝ => (0 : ℝ)) := by
    show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (fun _ _ : ℝ => (0 : ℝ)))
      Work.FTS.EllipticEst.Q0
    exact contDiffOn_const
  have hzero : Work.FTS.VocabO.HQo α 4 (fun _ _ : ℝ => (0 : ℝ)) :=
    ⟨hzero_sm, Work.FTS.Galerkin.Inhabit.HkMem_zeroF α 4⟩
  have hdiff : (fun z θ : ℝ => f z θ - 0) = f := by
    funext z θ; rw [sub_zero]
  have h := hkey α hα f (fun _ _ : ℝ => (0 : ℝ)) hf hzero (by rw [hdiff]; exact hf) z hz
  rw [hdiff, Work.FTS.Galerkin.L12_zero_fun z, sub_zero] at h
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hden : 0 < Real.sqrt (1 + z) := Real.sqrt_pos.mpr (by linarith)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (1 + z) := by
    have h1 : (1 : ℝ) ≤ 1 + z := by linarith
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + z) := Real.sqrt_le_sqrt h1
  have hle : C / Real.sqrt (1 + z) ≤ C := by
    rw [div_le_iff₀ hden]
    calc C = C * 1 := (mul_one C).symm
      _ ≤ C * Real.sqrt (1 + z) := mul_le_mul_of_nonneg_left hsqrt1 hCpos.le
  calc |Work.Construction.L12 f z| ≤ C / Real.sqrt (1 + z) * Work.FTS.Nonlin.Xn α f := h
    _ ≤ C * Work.FTS.Nonlin.Xn α f := mul_le_mul_of_nonneg_right hle hX

end Work.FTS.StrongEps.E5Aux2
