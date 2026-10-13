import Mathlib
import Submission.Work.WilE3.Frame.CutSys
import Submission.Work.WilE3.Frame.eaEvalC_toC
import Submission.Work.WilE3.Frame.eq_zero_of_eventually_zero_on_real_directions
import Submission.Work.WilE3.Frame.vanish_of_straightening_of_ball_zero

namespace Work.WilE3.Frame

set_option autoImplicit false
noncomputable section
open Classical Topology
open scoped Topology
open WilkiesDesign.E

/-- The curve function `u ↦ eaEvalC c f (Ψ (u, 0))` is complex-analytic at the base point
`uCoord k ι (toC x)`: it is the composition of the analytic `Ψ` with the analytic evaluation
`eaEvalC c f` and the linear (hence analytic) inclusion `u ↦ (u, 0)`. -/
private lemma analyticAt_curve {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k)
    (f : EAPoly k r) (x : Fin k → ℝ)
    (Ψ : ((U k ι → ℂ) × (Fin j → ℂ)) → (Fin k → ℂ))
    (hΨ : IsStraightening c h ι x Ψ) :
    AnalyticAt ℂ (fun u : U k ι → ℂ => eaEvalC c f (Ψ (u, 0))) (uCoord k ι (toC x)) := by
  have h1 : AnalyticAt ℂ (fun u : U k ι → ℂ => (u, (0 : Fin j → ℂ))) (uCoord k ι (toC x)) :=
    (ContinuousLinearMap.inl ℂ (U k ι → ℂ) (Fin j → ℂ)).analyticAt (uCoord k ι (toC x))
  have h3 : AnalyticAt ℂ (fun u : U k ι → ℂ => Ψ (u, 0)) (uCoord k ι (toC x)) :=
    AnalyticAt.comp (f := fun u : U k ι → ℂ => (u, (0 : Fin j → ℂ))) hΨ.2.1 h1
  exact AnalyticAt.comp (f := fun u : U k ι → ℂ => Ψ (u, 0))
    (Work.WilE3.API.eaEvalC_fderiv_analytic c f (Ψ (uCoord k ι (toC x), 0))).1 h3

/-- **From real directions to the real germ.**  Let `Ψ` straighten `{h = 0}` at `x`, and suppose
that for every *real* direction `w : U k ι → ℝ` the one variable function
`t ↦ eaEvalC c f (Ψ (u₀ + t • w_ℂ, 0))` vanishes near `t = 0` (this is what the frame half plus the
count half deliver).  Then `eaEval c f` vanishes on `{h = 0}` near `x`.

Why real directions suffice: the conclusion only concerns *real* points, and every such point of the
germ of `{h = 0}` is `Ψ (u, 0)` with `u` a *real* point of the parameter space (conjunct 4 of
`IsStraightening`).  So it is enough to show that `G u := eaEvalC c f (Ψ (u,0))` vanishes at every
real point `u` near `u₀`.

For that, let `G` be analytic on the ball `B (u₀, ρ)` (`AnalyticAt.exists_ball_analyticOnNhd`) and let
`u ∈ B (u₀, ρ)` be a real point, i.e. `u = u₀ + q` with `q` a real vector.  If `q = 0` then
`G u = eaEvalC c f (toC x) = 0` by `hfx`.  Otherwise the one-variable function
`t ↦ G (u₀ + t • q_ℂ)` is analytic on the disc `‖t‖ < ρ / ‖q_ℂ‖` (the image of which lies in
`B (u₀, ρ)`), it vanishes near `t = 0` by `hlines` applied to the real direction `q`, so by the
identity theorem (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`, and
preconnectedness of a ball) it vanishes identically there, in particular at `t = 1` — which lies in
the disc since `‖q_ℂ‖ < ρ`.  -/
theorem vanish_of_real_points {k r j : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (h : Fin j → WilkiesDesign.E.EAPoly k r) (ι : Fin j → Fin k)
    (f : WilkiesDesign.E.EAPoly k r) (x : Fin k → ℝ)
    (Ψ : ((Work.WilE3.Frame.U k ι → ℂ) × (Fin j → ℂ)) → (Fin k → ℂ))
    (hΨ : Work.WilE3.Frame.IsStraightening c h ι x Ψ)
    (hfx : Work.WilE3.eaEvalC c f (Work.WilE3.Frame.toC x) = 0)
    (hlines : ∀ w : Work.WilE3.Frame.U k ι → ℝ, ∀ᶠ t in nhds (0 : ℂ),
      Work.WilE3.eaEvalC c f (Ψ (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x) +
        t • (fun i => (w i : ℂ)), 0)) = 0) :
    ∀ᶠ y in nhds x, (∀ a, WilkiesDesign.E.eaEval c (h a) y = 0) →
      WilkiesDesign.E.eaEval c f y = 0 := by
  classical
  -- `G u = eaEvalC c f (Ψ (u, 0))` is analytic on a ball around the base point `u₀`.
  obtain ⟨ρ, hρ, hGρ⟩ :=
    (analyticAt_curve c h ι f x Ψ hΨ).exists_ball_analyticOnNhd
  -- and takes the value `0` at `u₀`, because `Ψ (u₀, 0) = toC x` and `f` vanishes at `toC x`.
  have hG₀ : (fun u : U k ι → ℂ => eaEvalC c f (Ψ (u, 0))) (uCoord k ι (toC x)) = 0 := by
    show eaEvalC c f (Ψ (uCoord k ι (toC x), 0)) = 0
    rw [hΨ.1]
    exact hfx
  -- Hence `G` vanishes at every *real* point of that ball ("identity principle along real lines"),
  -- and the straightening turns this into the vanishing of `eaEval c f` on `{h = 0}` near `x`.
  refine vanish_of_straightening_of_ball_zero c h ι f x Ψ hΨ ρ hρ (fun w hw => ?_)
  exact eq_zero_of_eventually_zero_on_real_directions
    (fun u : U k ι → ℂ => eaEvalC c f (Ψ (u, 0))) (uCoord k ι (toC x)) ρ hρ hGρ hG₀ hlines w hw

end

end Work.WilE3.Frame
