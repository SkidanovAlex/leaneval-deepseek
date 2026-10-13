/-
Interior regularity of `bslOp α` (weight `(5+α)/α`): the fundamental lemma of the calculus of
variations, with the pairings tested against *Schwartz* functions.

If a function `Φ` continuous on a ball and an integrable function `V` have the same integrals
against every Schwartz function supported in the ball, then they agree almost everywhere on it.
This is the bridge between the Sobolev embedding (`∫ ψ • Φ`) and the weak formulation
(`∫ ψ • V`).
-/
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.DerivNotation
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Submission.Work.EllipticEst.InteriorRegularity.VT.Assembly

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology SchwartzMap LineDeriv ContDiff

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The fundamental lemma with Schwartz pairings.** -/
theorem ae_eq_of_pairing {Φ V : E2 → ℂ} {x₀ : E2} {R : ℝ}
    (hΦc : ContinuousOn Φ (Metric.ball x₀ R)) (hV : Integrable V)
    (hpair : ∀ ψ : 𝓢(E2, ℂ), (∀ y, ψ y ≠ 0 → y ∈ Metric.ball x₀ R) →
      ∫ y, ψ y • Φ y = ∫ y, ψ y • V y) :
    V =ᵐ[volume.restrict (Metric.ball x₀ R)] Φ := by
  have hvan : ∀ g : E2 → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Metric.ball x₀ R → ∫ x, g x • (Φ x - V x) = 0 := by
    intro g hgd hgc hgsub
    have hgs : ∀ n : ℕ, ContDiff ℝ n g := contDiff_infty.mp hgd
    have hgcC : HasCompactSupport (fun x : E2 => ((g x : ℝ) : ℂ)) :=
      hasCompactSupport_ofReal hgc
    have hgsC : ∀ n : ℕ, ContDiff ℝ n (fun x : E2 => ((g x : ℝ) : ℂ)) :=
      fun n => Complex.ofRealCLM.contDiff.comp (hgs n)
    set hS : 𝓢(E2, ℂ) := hgcC.toSchwartzMap (contDiff_infty.mpr hgsC) with hSdef
    have hcoef : (⇑hS : E2 → ℂ) = fun x : E2 => ((g x : ℝ) : ℂ) := by
      rw [hSdef]
      exact funext (HasCompactSupport.toSchwartzMap_toFun hgcC (contDiff_infty.mpr hgsC))
    have hsuppS : ∀ y, hS y ≠ 0 → y ∈ Metric.ball x₀ R := by
      intro y hy
      have hy1 : y ∈ Function.support (⇑hS) := hy
      rw [hcoef] at hy1
      have hy2 : y ∈ Function.support g := by
        rw [Function.mem_support] at hy1 ⊢
        intro h0
        exact hy1 (by rw [h0]; simp)
      exact hgsub (subset_closure hy2)
    have hpairS := hpair hS hsuppS
    have hAi : Integrable (fun y : E2 => g y • Φ y) :=
      integrable_smul_of_continuousOn hgc hgs
        (Metric.isOpen_ball : IsOpen (Metric.ball x₀ R)) hgsub hΦc
    have hBi : Integrable (fun y : E2 => g y • V y) := integrable_smul_of_cc hV hgc hgs
    have hkey : ∫ y, g y • Φ y = ∫ y, g y • V y := by
      have i1 : ∫ y, g y • Φ y = ∫ y, hS y • Φ y :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => by
          rw [hcoef]
          exact (Complex.real_smul : g y • Φ y = ((g y : ℝ) : ℂ) * Φ y))
      have i2 : ∫ y, hS y • V y = ∫ y, g y • V y :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => by
          rw [hcoef]
          exact (Complex.real_smul : g y • V y = ((g y : ℝ) : ℂ) * V y).symm)
      rw [i1, hpairS, i2]
    rw [show (fun x : E2 => g x • (Φ x - V x)) = fun x => g x • Φ x - g x • V x from by
      funext x
      simp only [Pi.sub_apply, smul_sub]]
    rw [integral_sub hAi hBi, hkey, sub_self]
  have hae := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero Metric.isOpen_ball
    ((hΦc.locallyIntegrableOn Metric.isOpen_ball.measurableSet).sub
      (hV.locallyIntegrable.locallyIntegrableOn (Metric.ball x₀ R))) hvan
  rw [Filter.EventuallyEq]
  refine (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr ?_
  filter_upwards [hae] with x hx hxball
  exact (sub_eq_zero.mp (hx hxball)).symm

end Work.EllipticEst.InteriorRegularity.VT
