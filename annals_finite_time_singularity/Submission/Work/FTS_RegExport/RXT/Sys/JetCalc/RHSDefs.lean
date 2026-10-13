import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.CoeffJetsDefs
import Submission.Work.FTS_RegExport.RXT.loc_sup4
import Submission.Work.FTS_RegExport.RXT.MixedUniform
import Submission.Work.FTS_RegExport.RXT.slice_space_lip
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS.RegPkgGal.Sup.DthIter_DzIter_comm_fin
import Submission.Work.FTS_RegExport.RXT.C2Psi
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7
import Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.mixed_mul_fin
import Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.OpFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.JetCalc.RHSDefs` — the `(E)`-form of the equation

The profile `F(σ)`, the right-hand side `RHS σ = −(Vz·D_zF + bR·D_θF + cs·F)`, and the identity
`gdot g σ = RHS σ` on the open quadrant, from the hypothesis `hEqF` (the `(E)`-form of the
equation as produced by RX-R7/S5a).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 1000000
/-! ## §2 The `(E)`-form of the equation and the right-hand side `RHS` -/

/-- The `τ`-slice of the extended profile `F_* + g̃(·,·,σ)` (`g̃` the `extG`-extension of the
sanitised family). -/
noncomputable def profExt (α : ℝ) (g : Work.FTS.Galerkin.Fam) (σ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.FTS.Regularity.profFull α
    (Work.FTS.RegPkgGal.extG (Work.FTS.RegExportIface.RXT.GR α g)) z θ σ

@[simp] theorem profExt_apply (α : ℝ) (g : Work.FTS.Galerkin.Fam) (σ z θ : ℝ) :
    profExt α g σ z θ = Work.FTS.Regularity.profFull α
      (Work.FTS.RegPkgGal.extG (Work.FTS.RegExportIface.RXT.GR α g)) z θ σ := rfl

/-- The profile `F(σ) = F_* + gS α (tauExt g)(σ)` at fake time `σ`. -/
noncomputable def FtauS (α : ℝ) (g : Work.FTS.Galerkin.Fam) (σ : ℝ) : ℝ → ℝ → ℝ :=
  Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
    (Work.FTS.RegExportIface.RXT.GR α g) σ

@[simp] theorem FtauS_apply (α : ℝ) (g : Work.FTS.Galerkin.Fam) (σ z θ : ℝ) :
    FtauS α g σ z θ = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
      + Work.FTS.RegExportIface.RXT.GR α g z θ σ := rfl

/-- **The right-hand side** `−(Vz·D_zF + bR·D_θF + cs·F)` of the `(E)`-form of the equation,
with `F = F(σ)` and `D_θ = sin(2θ)·∂_θ` (so that no division by `sin 2θ` occurs). -/
noncomputable def RHS (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn)
    (g : Work.FTS.Galerkin.Fam) (σ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    - ( Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ
          * Work.Spaces.Dz (FtauS α g σ) z θ
        + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
          * Work.Spaces.Dth (FtauS α g σ) z θ
        + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * FtauS α g σ z θ )

@[simp] theorem RHS_apply (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn)
    (g : Work.FTS.Galerkin.Fam) (σ z θ : ℝ) :
    RHS α Φs E g σ z θ
      = - ( Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ
              * Work.Spaces.Dz (FtauS α g σ) z θ
            + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
              * Work.Spaces.Dth (FtauS α g σ) z θ
            + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * FtauS α g σ z θ ) := rfl

/-- The extended profile agrees with `F(σ)` on the open quadrant. -/
theorem profExt_eq_FtauS {α : ℝ} {g : Work.FTS.Galerkin.Fam} {σ : ℝ} (hσ : 0 ≤ σ) :
    ∀ z θ : ℝ, 0 < z → profExt α g σ z θ = FtauS α g σ z θ := by
  intro z θ hz
  rw [profExt_apply, Work.FTS.Regularity.profFull_apply, FtauS_apply,
    Work.FTS.RegPkgGal.extG_of_pos hz hσ]

/-- The `z`-partials of the two profiles agree at every interior point (they agree on `z > 0`). -/
theorem pz_profExt_eq {α : ℝ} {g : Work.FTS.Galerkin.Fam} {σ : ℝ} (hσ : 0 ≤ σ) {z θ : ℝ}
    (hz : 0 < z) :
    Work.Spaces.pz (profExt α g σ) z θ = Work.Spaces.pz (FtauS α g σ) z θ := by
  rw [Work.Spaces.pz, Work.Spaces.pz]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  exact profExt_eq_FtauS (α := α) (g := g) hσ z' θ hz'

/-- The `θ`-partials of the two profiles agree at every interior point (they agree on
`0 < θ < π/2`). -/
theorem pth_profExt_eq {α : ℝ} {g : Work.FTS.Galerkin.Fam} {σ : ℝ} (hσ : 0 ≤ σ) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθπ : θ < Real.pi / 2) :
    Work.Spaces.pth (profExt α g σ) z θ = Work.Spaces.pth (FtauS α g σ) z θ := by
  rw [Work.Spaces.pth, Work.Spaces.pth]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ, hθπ⟩] with θ' hθ'
  exact profExt_eq_FtauS (α := α) (g := g) hσ z θ' hz

/-- **The `τ`-derivative of the profile is the right-hand side.**  From the `(E)`-form of the
equation (`hEqF`, with `Vθ7 = bR·sin 2θ` and `D_θ = sin 2θ·∂_θ`), on the open quadrant. -/
theorem gdot_eq_RHS {α S : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hEqF : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => profExt α g s z θ)
        (-(Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ
            * Work.Spaces.Dz (profExt α g τ) z θ
          + Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ τ
            * Work.Spaces.pth (profExt α g τ) z θ
          + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ
            * profExt α g τ z θ)) τ) :
    ∀ z θ σ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < σ → σ ≤ S →
      Work.FTS.Galerkin.gdot g σ z θ = RHS α Φs E g σ z θ := by
  intro z θ σ hz hθ hθπ hσ hσS
  have hσ0 : 0 ≤ σ := hσ.le
  have hsin : Real.sin (2 * θ) ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  -- (1) the `τ`-derivative of the extension is `gdot`
  have hderiv : deriv (fun s => profExt α g s z θ) σ = Work.FTS.Galerkin.gdot g σ z θ := by
    have hfun : (fun s => profExt α g s z θ)
        =ᶠ[nhds σ] (fun s => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
          + g z θ s) := by
      filter_upwards [isOpen_Ioi.mem_nhds hσ] with s hs
      rw [profExt_apply, Work.FTS.Regularity.profFull_apply,
        Work.FTS.RegPkgGal.extG_of_pos hz hs.le,
        Work.FTS_RegExport.RXT.ftau_GR_of_quad (α := α) (g := g) hs.le hz hθ.le hθπ.le]
    rw [hfun.deriv_eq, deriv_const_add]
    rfl
  -- (2) the jet conversions
  have hDz : Work.Spaces.Dz (profExt α g σ) z θ
      = Work.Spaces.Dz (FtauS α g σ) z θ := by
    rw [Work.Spaces.Dz, Work.Spaces.Dz, pz_profExt_eq (α := α) (g := g) hσ0 hz]
  have hpth : Work.Spaces.pth (profExt α g σ) z θ
      = Work.Spaces.pth (FtauS α g σ) z θ := pth_profExt_eq hσ0 hz hθ hθπ
  have hval : profExt α g σ z θ = FtauS α g σ z θ := profExt_eq_FtauS hσ0 z θ hz
  have hDth : Work.Spaces.Dth (FtauS α g σ) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (FtauS α g σ) z θ := rfl
  have e2 : Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ σ
        * Work.Spaces.pth (profExt α g σ) z θ
      = Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
        * Work.Spaces.Dth (FtauS α g σ) z θ := by
    have hVθ : Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ σ
        = Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ * Real.sin (2 * θ) := by
      simp only [Work.FTS.RegExportIface.RXT.bR]
      rw [div_mul_cancel₀ _ hsin]
    rw [hVθ, hpth, hDth]
    ring
  have hh := (hEqF z θ σ hz hθ hθπ hσ hσS).deriv
  rw [hderiv] at hh
  rw [hh, hDz, e2, hval, RHS_apply]

end Work.FTS_RegExport.RXT.Sys
