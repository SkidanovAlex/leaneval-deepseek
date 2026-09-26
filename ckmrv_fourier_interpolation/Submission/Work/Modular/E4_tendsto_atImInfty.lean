import Mathlib
import Submission.Work.Modular.Basic
import Submission.Work.Modular.E4_qExpansion_coeff

namespace Work.Modular

open UpperHalfPlane ModularForm
open scoped Manifold MatrixGroups ModularForm Topology

/-- The weight-four Eisenstein series `E₄` tends to its constant term `1` at the cusp `i∞`. -/
theorem E4_tendsto_atImInfty :
    Filter.Tendsto E4 UpperHalfPlane.atImInfty (𝓝 (1 : ℂ)) := by
  -- `E₄` is periodic of period one: it is a modular form of weight four for `SL(2, ℤ)`.
  have hperi : Function.Periodic (E4 ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL
  -- `E₄` is holomorphic and bounded at the cusp.
  have hanalytic : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 E4) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hperi
      (ModularForm.holo' ModularForm.E₄) (ModularFormClass.bdd_at_infty ModularForm.E₄)
  -- Hence `E₄ = F ∘ q` with `F` analytic at `0`, so it tends to `F 0` along `i∞`.
  have hcomp : Filter.Tendsto
      (fun τ : ℍ ↦ UpperHalfPlane.cuspFunction 1 E4
        (Function.Periodic.qParam 1 (τ : ℂ)))
      UpperHalfPlane.atImInfty (𝓝 (UpperHalfPlane.cuspFunction 1 E4 0)) :=
    hanalytic.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty one_pos)
  have hfeq : (fun τ : ℍ ↦ UpperHalfPlane.cuspFunction 1 E4
      (Function.Periodic.qParam 1 (τ : ℂ))) = E4 := by
    funext τ
    exact UpperHalfPlane.eq_cuspFunction τ one_ne_zero hperi
  rw [hfeq] at hcomp
  -- The value at the cusp is the constant term of the `q`-expansion, which is `1`.
  have hval : UpperHalfPlane.cuspFunction 1 E4 0 = 1 := by
    rw [UpperHalfPlane.cuspFunction_apply_zero one_pos hanalytic hperi,
      ← UpperHalfPlane.qExpansion_coeff_zero one_pos hanalytic hperi]
    simpa using E4_qExpansion_coeff 0
  rwa [hval] at hcomp

end Work.Modular
