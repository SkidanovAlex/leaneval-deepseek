import Mathlib
import Submission.CDTPlan.InterfacesC
import Submission.Work.CLift.bridge
import Submission.Work.CLift.defs
import Submission.Work.CLift.analytic
import Submission.Work.CLift.basic_aux
import Submission.Work.CLift.Phi_small
import Submission.Work.CLift.Phi_ne_root
import Submission.Work.CLift.ode_holds
import Submission.Work.CLift.hasDerivAt_U
import Submission.Work.CLift.hasDerivAt_Vp
import Submission.Work.CLift.sys_diff
import Submission.Work.CLift.Y0_solves

/-!
Area CLift — continuation of `P` along the lift `Φ` (`PLiftCont`, InterfacesC).

Gauge (removing the apparent singularity of `M(P) = cubic` at `x = -1`):
`u = P`, `v = (P' - P/2 - β)/(x+1)` with `β = (r_a+r_b)/(2(a+b))`.  The pair `(u,v)`
satisfies the first-order affine system `(u,v)' = A(x)(u,v) + c(x)` whose coefficients are
rational with poles only at `x = 0, 1` and the roots of `Q₄` (`Mu_identity`, `Nq_identity`,
`Mc_identity` in `defs.lean`).

Pulling back along `Φ` (`Y₀ = (u,v)∘Φ`) and applying `OdeContinuation` with `k = 2` on the
annulus `r₀ < |z| < 1`, `r₀ = 3.2·10⁻⁴`, yields the holomorphic continuation `F = u∘Φ`.
-/

namespace Work.CLift

open Submission.CDTPlan Metric
open scoped BigOperators

theorem p_lift_cont (hK : OdeContinuation) (hR : PRadius) (hN : CNumerics) (hL : CLocation)
    (hM : HauptFacts) (hP : PsiCFacts) : PLiftCont := by
  intro m n ra rb rab r0 hAdm hRel Φ hΦdiff hΦeq hΦ0
  have hsolve := Y0_solves m n ra rb rab r0 hR hL hN hM hP hAdm hRel Φ hΦdiff hΦeq hΦ0
  have hsys := sys_diff m n ra rb rab r0 hL hN hM hP hAdm hRel Φ hΦdiff hΦeq hΦ0
  obtain ⟨Y, hYdiff, hYeq⟩ :=
    hK 2 (sysA m n Φ) (sysb m n ra rb rab Φ) 3.2e-4 (1 / 1000) (Y0v m n ra rb rab r0 Φ)
      (by norm_num) (by norm_num) (by norm_num) hsys.1 hsys.2 hsolve.1 hsolve.2
  refine ⟨fun z => Y z 0, ?_, ?_⟩
  · have hproj : DifferentiableOn ℂ (fun v : Fin 2 → ℂ => v 0) Set.univ :=
      (differentiable_apply (𝕜 := ℂ) (0 : Fin 2)).differentiableOn
    have : (fun z => Y z 0) = (fun v : Fin 2 → ℂ => v 0) ∘ Y := rfl
    rw [this]
    exact hproj.comp hYdiff (fun z _ => Set.mem_univ _)
  · have hPhi := Phi_small hM hP Φ hΦeq
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0:ℝ) < 1 / 1000)] with z hz
    have hz1 : ‖z‖ ≤ 1 / 1000 := by
      have := mem_ball.mp hz; simp only [dist_zero_right] at this; exact le_of_lt this
    have hPhi1 : ‖Φ z‖ ≤ 1 / 50 := hPhi z hz1
    have hPhi2 : ‖Φ z‖ ≤ 1 / 2 := by linarith
    have hYz : Y z = Y0v m n ra rb rab r0 Φ z := hYeq hz
    rw [hYz]
    have h0 : Y0v m n ra rb rab r0 Φ z 0 = U0 m n ra rb rab r0 (Φ z) := rfl
    rw [h0]
    have hsummable : Summable fun k : ℕ => coef m n ra rb rab r0 k * (Φ z) ^ k :=
      (summable_norm_U0 m n ra rb rab r0 hR hAdm hRel (Φ z) hPhi2).of_norm
    have hcoef : (fun k : ℕ => coef m n ra rb rab r0 k * (Φ z) ^ k)
        = (fun k : ℕ => ((PowerSeries.coeff k (PC m n ra rb rab r0) : ℚ) : ℂ) * (Φ z) ^ k) := by
      funext k; rw [coef]; rfl
    rw [U0, hcoef]
    rw [hcoef] at hsummable
    exact hsummable.hasSum

end Work.CLift
