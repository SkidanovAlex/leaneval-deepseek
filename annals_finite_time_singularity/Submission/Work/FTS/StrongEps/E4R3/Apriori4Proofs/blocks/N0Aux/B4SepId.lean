/-
# `N0Aux.B4SepId` — the separated forms of the pieces `NP4a` and `NP5a`

On the open quadrant the two `F_*`-pieces of the `N₀`-row are products of an angular profile
(`VfsA1`, `VfsA2` of `Work.FTS.StrongPersist.L3Rhs`) with a radial profile
(`VfsRad · L₁₂w`, `Hz · L₁₂w`):

  `NP4a α w z θ = VfsA1 α θ · (VfsRad z · L₁₂(w) z)`,
  `NP5a α w z θ = VfsA2 α θ · (Hz z · L₁₂(w) z)`.

Both follow from the separation of the profile `F_* = (α·VfsRad z)·VfsGc(θ)`
(`pth_Fstar_sep`, `Dz_Fstar_sep`) and `VfsRadZ z = Hz z` for `z > 0`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsSep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.N0row_defs
import Submission.Work.FTS.Nonlinear.FstarPkg.DzHzDefs
import Submission.Work.FM.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

set_option autoImplicit false

open Work.FTS.StrongPersist.H6Pair6Aux (NA1 NA4 NA5 NA6 NP3 NP4a NP4b NP5a NP5b NP6)

/-- `Zop F_* = H` on `(0,∞)`: the radial factor of `D_zF_*` is the `Zop`-derivative of the
fundamental radial profile. -/
theorem Zop_Fstar_eq_Hz {z : ℝ} (hz : 0 < z) :
    Work.Spaces.Zop Work.FM.Fstar z = Work.FTS.Nonlinear.FstarPkg.Hz z := by
  rw [Work.Spaces.Zop, Work.FM.deriv_Fstar z (by linarith)]
  simp only [Work.FTS.Nonlinear.FstarPkg.Hz]
  field_simp <;> ring

/-- `VfsRadZ` is `H` on `(0,∞)`. -/
theorem VfsRadZ_eq_Hz {z : ℝ} (hz : 0 < z) :
    Work.FTS.StrongPersist.L3Rhs.VfsRadZ z = Work.FTS.Nonlinear.FstarPkg.Hz z := by
  have h : Work.FTS.StrongPersist.L3Rhs.VfsRadZ z
      = Work.Spaces.Zop Work.FM.Fstar z := rfl
  rw [h, Zop_Fstar_eq_Hz hz]

/-- **The separated form of `NP4a` on the open quadrant.** -/
theorem NP4a_eq_sep4 {α : ℝ} (hα : 0 < α) (w : ℝ → ℝ → ℝ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      NP4a α w z θ = Work.FTS.StrongPersist.L3Rhs.VfsA1 α θ
        * (Work.FTS.StrongPersist.L3Rhs.VfsRad z * Work.Construction.L12 w z) := by
  intro z θ _ _ _
  simp only [NP4a, NA4, Work.Spaces.Dth, Work.FTS.StrongPersist.L3Rhs.VfsA1,
    Work.Spaces.dthU]
  rw [Work.FTS.StrongPersist.L3Rhs.pth_Fstar_sep]
  have hαne : α ≠ 0 := ne_of_gt hα
  field_simp <;> ring

/-- **The separated form of `NP5a` on the open quadrant.** -/
theorem NP5a_eq_sep4 {α : ℝ} (w : ℝ → ℝ → ℝ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      NP5a α w z θ = Work.FTS.StrongPersist.L3Rhs.VfsA2 α θ
        * (Work.FTS.Nonlinear.FstarPkg.Hz z * Work.Construction.L12 w z) := by
  intro z θ hz _ _
  rw [NP5a, NA5, Work.FTS.StrongPersist.L3Rhs.Dz_Fstar_sep, VfsRadZ_eq_Hz hz]
  simp only [Work.FTS.StrongPersist.L3Rhs.VfsA2]
  ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
