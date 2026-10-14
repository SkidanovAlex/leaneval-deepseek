import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.Ctx =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlin

open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  muDyn lamDyn dynLin dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `GalClass α g` gives `RegQ α 4 g` (`regQ_mono`). -/
theorem galClass_regQ4 {α : ℝ} {g : Fn} (h : GalClass α g) : RegQ α 4 g :=
  Work.FTS.GalerkinFix.RegQ.regQ_mono h.reg (by norm_num)

/-- **The context of the per-piece estimates.**  `IP` is the concrete `ℋ⁴`-inner product with
its transport interface `N4Extra`, `N4Norm` carries the norm-level facts, `α ∈ (0, min α₂ 1]`
is the small parameter, and `g`, `Φs`, `Φg` are the perturbation and the two stream functions
of `StarPkg`/`EllPkgG`. -/
structure RowCtx (IP : ℝ → Fn → Fn → ℝ) (α₂ Ci Ct Ce Cs α : ℝ) (g Φs Φg : Fn) : Prop where
  hCi : 0 < Ci
  hN : N4Norm Ci α₂
  hE : N4Extra IP α₂ Ct
  hα : 0 < α
  hαα₂ : α ≤ α₂
  hα1 : α ≤ 1
  hg : GalClass α g
  hs : StarPkg α Cs Φs
  hell : EllPkgG α Ce g Φg

variable {IP : ℝ → Fn → Fn → ℝ} {α₂ Ci Ct Ce Cs α : ℝ} {g Φs Φg : Fn}

/-- The pieces of the context, extracted once. -/
theorem RowCtx.reg4 (h : RowCtx IP α₂ Ci Ct Ce Cs α g Φs Φg) : RegQ α 4 g :=
  galClass_regQ4 h.hg

theorem RowCtx.hαIoc (h : RowCtx IP α₂ Ci Ct Ce Cs α g Φs Φg) : α ∈ Set.Ioc 0 α₂ :=
  ⟨h.hα, h.hαα₂⟩


end Work.FTS.Nonlin
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

set_option maxHeartbeats 1600000

/-! ## Elementary angular facts -/



/-- `|qfun θ| ≤ 4/3`, because `qfun θ = cos(2θ) - 1/3 ∈ [-4/3, 2/3]`. -/
private lemma abs_qfun_le (θ : ℝ) : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
  rw [Work.Spaces.qfun_apply, abs_le]
  constructor
  · linarith [Real.neg_one_le_cos (2 * θ)]
  · linarith [Real.cos_le_one (2 * θ)]


/-! ## The angular integrals of `Γ` -/




/-! ## The `c`-normalised angular integrals -/





/-! ## The radial profile `F_*` -/




/-! ## The derivatives of `F_*` -/

/-- **The pointwise factorisations of `∂_θF_*`, `D_θF_*` and `D_zF_*`.** -/
theorem FzShape (α : ℝ) (hα : 0 < α) :
    (∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 → Work.Spaces.pth (Work.Construction.Fstar α) z θ
        = α * (deriv (fun t => Work.Spaces.Gam α t) θ / Work.Spaces.c α)
            * Work.FM.Fstar z) ∧
    (∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 → Work.Spaces.Dth (Work.Construction.Fstar α) z θ
        = α ^ 2 * (Work.Spaces.qfun θ * Work.Spaces.Gam α θ / Work.Spaces.c α)
            * Work.FM.Fstar z) ∧
    (∀ z θ : ℝ, -1 < z → Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        = α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * (z * deriv Work.FM.Fstar z)) := by
  have hpth : ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (Work.Construction.Fstar α) z θ
        = α * (deriv (fun t => Work.Spaces.Gam α t) θ / Work.Spaces.c α)
            * Work.FM.Fstar z := by
    intro z θ h0 h1
    have hd : DifferentiableAt ℝ (fun t => Work.Spaces.Gam α t) θ :=
      Work.Spaces.Gam_differentiableAt α θ h0 h1
    rw [Work.Spaces.pth]
    have heq : (fun θ' => Work.Construction.Fstar α z θ')
        =ᶠ[𝓝 θ]
          (fun θ' => (α * Work.FM.Fstar z / Work.Spaces.c α) * Work.Spaces.Gam α θ') :=
      Filter.Eventually.of_forall (fun θ' => by
        simp only [Work.Construction.Fstar]; ring)
    rw [heq.deriv_eq, deriv_const_mul _ hd]
    ring
  refine ⟨hpth, ?_, ?_⟩
  · intro z θ h0 h1
    have hdt : Real.sin (2 * θ) * deriv (fun t => Work.Spaces.Gam α t) θ
        = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ := by
      simpa only [Work.Spaces.dthU_apply] using Work.Spaces.dthU_Gam α θ hα ⟨h0, h1⟩
    rw [Work.Spaces.Dth, hpth z θ h0 h1]
    rw [show Real.sin (2 * θ)
          * (α * (deriv (fun t => Work.Spaces.Gam α t) θ / Work.Spaces.c α)
              * Work.FM.Fstar z)
        = (α * Work.FM.Fstar z / Work.Spaces.c α)
            * (Real.sin (2 * θ) * deriv (fun t => Work.Spaces.Gam α t) θ) from by ring,
      hdt]
    ring
  · intro z θ hz
    have hd : DifferentiableAt ℝ Work.FM.Fstar z := (Work.FM.hasDerivAt_Fstar z hz).differentiableAt
    rw [Work.Spaces.Dz, Work.Spaces.pz]
    have heq : (fun z' => Work.Construction.Fstar α z' θ)
        =ᶠ[𝓝 z]
          (fun z' => (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * Work.FM.Fstar z') :=
      Filter.Eventually.of_forall (fun z' => by
        simp only [Work.Construction.Fstar])
    rw [heq.deriv_eq, deriv_const_mul _ hd]
    ring


end Work.FTS.Nonlinear.Pieces.rl1Tools
end
end
