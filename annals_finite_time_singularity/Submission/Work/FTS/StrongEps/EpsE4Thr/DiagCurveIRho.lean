/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/DiagCurveIRho.lean` — transporting a `DiagCurveI`
# across a pointwise identity of the weights

`DiagCurveI_JfamP` produces the `L²`-route bundle for the *one-parameter family* of weights

  `ρ_c(z,θ) = w(z)² · sin(2θ)^c`      (`c ≥ -η`),

while the level-four energy `IP4` consumes the four weights of `StrongPersist`:

  `rhoEta = w² σ^{-η}`,  `rhoW = w²` (θ-free!),  `rhoGam α = w² σ^{-γ(α)}`.

The first and the third are *definitionally* `ρ_c` at `c = -η` and `c = -γ(α)`, but `rhoW` is not:
`ρ_0 = fun z θ => w z² * sin (2θ)^0`, which equals `w z²` only after `Real.rpow_zero`.  This module
supplies the transport `DiagCurveI ρ u udot τ T → DiagCurveI ρ' u udot τ T` for two weights that
agree pointwise, which is all the assembly needs (every field of `DiagCurveI` is either a.e.
measurability/nonnegativity of `ρ`, or an integral of a `ρ`-weighted product, or independent of
`ρ` altogether).

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.EnergyDiagAssemblyIoo
import Submission.Work.FTS.StrongEps.EpsE4Thr.WipEqIntegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **A `DiagCurveI` only depends on the weight through its values**: two pointwise equal weights
give the same bundle. -/
theorem DiagCurveI_congr_rho {ρ ρ' : ℝ → ℝ → ℝ} {u udot : ℝ → Fn} {τ T : ℝ}
    (hρ : ∀ z θ : ℝ, ρ z θ = ρ' z θ) (h : DiagCurveI ρ u udot τ T) :
    DiagCurveI ρ' u udot τ T := by
  have hae : (Function.uncurry ρ) =ᵐ[mup] (Function.uncurry ρ') :=
    Filter.Eventually.of_forall fun p => hρ p.1 p.2
  have hbody : ∀ A : ℝ × ℝ → ℝ,
      (fun p : ℝ × ℝ => A p * ρ p.1 p.2) =ᵐ[mup] (fun p : ℝ × ℝ => A p * ρ' p.1 p.2) :=
    fun A => Filter.Eventually.of_forall fun p => by simp only [hρ p.1 p.2]
  refine ⟨h.ρmeas.congr hae, ?_, ?_, ?_, h.aesm, h.aesmd, h.deriv, ?_, ?_, ?_⟩
  · filter_upwards [h.ρnn] with p hp
    rw [← hρ p.1 p.2]; exact hp
  · intro s hs
    exact (MeasureTheory.integrable_congr
      (hbody (fun p : ℝ × ℝ => (u s p.1 p.2) ^ 2))).mp (h.int_diag s hs)
  · intro s hs
    exact (MeasureTheory.integrable_congr
      (hbody (fun p : ℝ × ℝ => (udot s p.1 p.2) ^ 2))).mp (h.int_diagd s hs)
  · obtain ⟨K, hK0, hKb⟩ := h.bdd
    refine ⟨K, hK0, fun σ hσ => ?_⟩
    rw [← MeasureTheory.integral_congr_ae
      (hbody (fun p : ℝ × ℝ => (udot σ p.1 p.2) ^ 2))]
    exact hKb σ hσ
  · refine h.contU.congr' ?_
    filter_upwards with σ
    exact MeasureTheory.integral_congr_ae
      (hbody (fun p : ℝ × ℝ => (udot σ p.1 p.2 - udot τ p.1 p.2) ^ 2))
  · exact (MeasureTheory.integrable_congr
      (hbody (fun p : ℝ × ℝ => udot τ p.1 p.2 * u τ p.1 p.2))).mp (h.int_cross)

/-- **The `rhoW` instance**: the θ-free weight `w z²` is the weight `ρ_0` of `DiagCurveI_JfamP`
up to `Real.rpow_zero`. -/
theorem DiagCurveI_congr_rhoW {u udot : ℝ → Fn} {τ T : ℝ}
    (h : DiagCurveI (fun z θ : ℝ => Work.Spaces.w z ^ 2 * Real.sin (2 * θ) ^ (0 : ℝ)) u udot τ T) :
    DiagCurveI Work.FTS.StrongPersist.rhoW u udot τ T :=
  DiagCurveI_congr_rho (fun z θ => by
    simp only [Real.rpow_zero, mul_one, Work.FTS.StrongPersist.rhoW]) h

end Work.FTS.StrongEps.EpsE4Thr
