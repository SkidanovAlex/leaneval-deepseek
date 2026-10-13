/-
# `Work.FTS.PhiStar.Assemble` — the assembled solution `Φ_* = Model + R`

This file composes the delivered pieces of the `Φ_*` node:

* `phiStar_remainder_source` (P2, proved) applied to `Gz := GzProfile α` and the angular model
  `ψ`, using `GzProfile_ode` for the radial equation:  `bslOp α (Model α (GzProfile α) ψ)
  = F_* − RemSource α ψ`  (`bslOp_model_eq`);
* the elliptic existence node `bslOp_sol_exists`:  a weak-class solution `R` of
  `bslOp α R = RemSource α ψ` with the Dirichlet data and the decay;
* `isBslSol_of_split` (`Model.lean`):  with the differentiability of `Model`
  (`contDiffAt_model`) and of `R`, the sum `Φ_* = Model α (GzProfile α) ψ + R` is a solution of
  `bslOp α Φ_* = F_*` in the class `IsBslSol` (`isBslSol_of_rem`).
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.PhiStar.Model
import Submission.Work.FTS.PhiStar.phiStar_remainder_source
import Submission.Work.FTS.PhiStar.GzProfile_ode
import Submission.Work.FTS.PhiStar.GzProfile_smooth
import Submission.Work.FTS.PhiStar.contDiffAt_model
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## `SmoothOpen` and `ContDiffAt` -/

/-- A `SmoothOpen` function is `C^n` at every interior point of the open quadrant. -/
theorem contDiffAt_of_smoothOpen {R : Fn} (hR : Work.FTS.EllipticEst.SmoothOpen R)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) (n : ℕ) :
    ContDiffAt ℝ n (Function.uncurry R) (z, θ) :=
  (Work.FTS.EllipticEst.SmoothOpen.forall hR n).contDiffAt
    (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
    ((Work.FTS.EllipticEst.mem_Q0).mpr ⟨hz, hθ, hθ2⟩))

/-! ## The `bslOp`-image of the model part -/

/-- **The model part of the decomposition solves the profile equation up to the remainder
source**: for the explicit radial profile `GzProfile α` and an angular model `ψ`,
`bslOp α (Model α (GzProfile α) ψ) = F_* − α²(𝒜φ)ψ` on the open quadrant.  This is the
telescoping identity `phiStar_remainder_source` instantiated at `Gz = GzProfile α`. -/
theorem bslOp_model_eq {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {ψ : ℝ → ℝ}
    (hψ : AngModel α ψ) (hGzd : ContDiffOn ℝ 2 (GzProfile α) (Set.Ioi 0))
    (z θ : ℝ) (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Elliptic.bslOp α (Model α (GzProfile α) ψ) z θ
      = Work.Construction.Fstar α z θ - RemSource α ψ z θ := by
  have hψsm : ContDiffOn ℝ 2 ψ (Set.Ioo 0 (π / 2)) := hψ.smooth.of_le (by norm_num)
  have hψeq : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.FTS.EllipticEst.Lzero1 ψ θ = Work.FTS.VocabO.GamBar α θ := fun θ hθ => hψ.eq θ hθ
  have hGode : ∀ z, 0 < z →
      -(α ^ 2 * z ^ 2 * iteratedDeriv 2 (GzProfile α) z)
        - α * (5 + α) * z * deriv (GzProfile α) z
      = (5 * α / 4) * Work.FTS.VocabO.phiR z := fun z hz => GzProfile_ode hα hα4 z hz
  exact phiStar_remainder_source α hα ψ (GzProfile α) hψsm hψeq hGode hGzd z hz θ hθ hθ2

/-! ## The assembled solution -/

/-- **The assembled stream function.**  Given an angular model `ψ`, an explicit radial profile
`GzProfile α` and a solution `R` of `bslOp α R = RemSource α ψ` with the Dirichlet data at
`θ = 0, π/2` and decay, the sum `Φ_* = Model α (GzProfile α) ψ + R` is a solution of
`bslOp α Φ_* = F_*` in the class `IsBslSol`. -/
theorem isBslSol_of_rem {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {ψ : ℝ → ℝ} {R : Fn}
    {C : ℝ} (hψ : AngModel α ψ) (hGzd : ContDiffOn ℝ 2 (GzProfile α) (Set.Ioi 0))
    (hGzdec : Tendsto (GzProfile α) atTop (𝓝 0)) (hψbd : ∀ θ ∈ Work.Spaces.Iθ, |ψ θ| ≤ C)
    (hRs : Work.FTS.EllipticEst.SmoothOpen R)
    (hRx : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp α R z θ = RemSource α ψ z θ)
    (hR0 : ∀ z, R z 0 = 0) (hR1 : ∀ z, R z (π / 2) = 0)
    (hRdec : ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => R z θ) atTop (𝓝 0)) :
    Work.Elliptic.IsBslSol α (Work.Construction.Fstar α)
      (fun z θ => Model α (GzProfile α) ψ z θ + R z θ) := by
  refine isBslSol_of_split (Gz := GzProfile α) (ψ := ψ) (R := R) (C := C) ?_ hRx ?_ ?_
    hψ.bdry0 hψ.bdry1 hR0 hR1 hGzdec hψbd hRdec
  · intro z hz θ hθ hθ2
    exact bslOp_model_eq hα hα4 hψ hGzd z θ hz hθ hθ2
  · intro z θ hz hθ hθ2
    refine contDiffAt_model 2 hz (hGzd.contDiffAt (isOpen_Ioi.mem_nhds hz)) ?_
    exact (hψ.smooth.of_le (by norm_num)).contDiffAt
      (isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (π / 2) from ⟨hθ, hθ2⟩))
  · intro z θ hz hθ hθ2
    exact contDiffAt_of_smoothOpen hRs hz hθ hθ2 2

/-! ## The `hGzd`-free forms

`GzProfile_smooth` (proved) discharges the differentiability hypothesis of `GzProfile`. -/

/-- The explicit radial profile is `C²` on `(0,∞)`. -/
theorem GzProfile_contDiffOn_two {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) :
    ContDiffOn ℝ 2 (GzProfile α) (Set.Ioi 0) :=
  GzProfile_smooth hα hα4 2

/-- `bslOp_model_eq` with the differentiability of `GzProfile` discharged. -/
theorem bslOp_model_eq' {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {ψ : ℝ → ℝ}
    (hψ : AngModel α ψ) (z θ : ℝ) (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Elliptic.bslOp α (Model α (GzProfile α) ψ) z θ
      = Work.Construction.Fstar α z θ - RemSource α ψ z θ :=
  bslOp_model_eq hα hα4 hψ (GzProfile_contDiffOn_two hα hα4) z θ hz hθ hθ2

/-- `isBslSol_of_rem` with the differentiability of `GzProfile` discharged. -/
theorem isBslSol_of_rem' {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {ψ : ℝ → ℝ} {R : Fn}
    {C : ℝ} (hψ : AngModel α ψ) (hGzdec : Tendsto (GzProfile α) atTop (𝓝 0))
    (hψbd : ∀ θ ∈ Work.Spaces.Iθ, |ψ θ| ≤ C) (hRs : Work.FTS.EllipticEst.SmoothOpen R)
    (hRx : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp α R z θ = RemSource α ψ z θ)
    (hR0 : ∀ z, R z 0 = 0) (hR1 : ∀ z, R z (π / 2) = 0)
    (hRdec : ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => R z θ) atTop (𝓝 0)) :
    Work.Elliptic.IsBslSol α (Work.Construction.Fstar α)
      (fun z θ => Model α (GzProfile α) ψ z θ + R z θ) :=
  isBslSol_of_rem hα hα4 hψ (GzProfile_contDiffOn_two hα hα4) hGzdec hψbd hRs hRx hR0 hR1 hRdec

end Work.FTS.PhiStar
