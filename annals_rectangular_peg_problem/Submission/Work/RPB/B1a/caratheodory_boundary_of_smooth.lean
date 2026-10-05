import Mathlib
import Submission.Work.RPB.B1a.Defs
import Submission.Work.RPB.B1a.continuous_sigma_of_loop
import Submission.Work.RPB.B1a.continuous_extension_of_smooth_conformal
import Submission.Work.RPB.B1a.injOn_closedBall_of_smooth_conformal

namespace Work.RPB.B1a

-- The *boundary half* of node N6 of the conformal-map route (`RECTPEG_B1_LEAD.md` §3), split off
-- because the other half (the Riemann map itself) comes from the `lean-pool` dependency, while this
-- half is classical and can be done in-house.  Content (Carathéodory's boundary correspondence, in
-- the form the route consumes): a biholomorphism of the open unit disc onto a Jordan domain whose
-- frontier is the image of a smooth loop extends continuously and injectively to the closed disc,
-- and its boundary values traverse the curve, i.e. there is a continuous reparametrisation `σ` with
-- `Φ (exp (t·I)) = v (σ t)`.  Reviewers confirmed the statement is true as written and that `σ` need
-- not be monotone or periodic.
--
-- Hint.  Route (i): the classical Carathéodory boundary correspondence (normal families / the crosscut
-- argument) holds for *any* Jordan domain, so it suffices to know that `closure D \ interior D` is
-- homeomorphic to `Circle` (derivable from `IsSmoothLoop` + the frontier hypothesis) together with
-- the plane-separation facts; the workspace has the lead's in-house
-- `Submission/Work/RPB1a/Geometry.lean` (`IsJordanCurveSet`), the ported Jordan separation
-- (`Submission.Work.RPB.Port.Drive.smooth_jordan_separation`, `two_sided_decomposition`,
-- `isPathConnected_exterior`) and `Submission.Work.RPB.B1.jordan_separation_smooth` for the frontier
-- facts.  Route (ii, likely shorter for a *smooth* boundary): use the collar/tubular structure of the
-- smooth curve together with the Schwarz-reflection technique of
-- `Work.RPB.B1a.analytic_extension_of_collar` (proved in this directory) to produce the extension
-- directly, then read off `σ` from `Φ ∘ exp` and the embedded parametrisation `v`; the lifting tools
-- already in this area (`B1a/*` helpers, `Argument`/`arg` lemmas) produce a continuous `σ` from the
-- continuous map `t ↦ Φ (exp (t·I))` into `range v ≃ Circle` and injectivity (the covering-lifting
-- step is the real work there).
lemma caratheodory_boundary_of_smooth (v : ℝ → ℂ) (hv : Work.RPB.B1a.IsSmoothLoop v) (D : Set ℂ)
    (hDo : IsOpen D) (hDc : IsConnected D) (hDb : Bornology.IsBounded D)
    (hDfr : closure D \ interior D = Set.range v)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hfinj : Set.InjOn f (Metric.ball 0 1)) (hfim : f '' Metric.ball 0 1 = D) :
    ∃ Φ : ℂ → ℂ, ContinuousOn Φ (Metric.closedBall 0 1) ∧ Set.EqOn Φ f (Metric.ball 0 1) ∧
      Set.InjOn Φ (Metric.closedBall 0 1) ∧
      ∃ σ : ℝ → ℝ, Continuous σ ∧ ∀ t : ℝ, Φ (Complex.exp (t * Complex.I)) = v (σ t) := by
  -- The continuity half of Carathéodory's boundary correspondence (also gives that the circle is
  -- mapped into `range v`).
  obtain ⟨Φ, hΦc, hΦeq, hΦs⟩ :=
    continuous_extension_of_smooth_conformal v hv D hDo hDc hDb hDfr f hf hfinj hfim
  -- The extension is holomorphic and injective on the open disc, with image `D`.
  have hΦd : DifferentiableOn ℂ Φ (Metric.ball 0 1) := hf.congr (fun z hz => hΦeq hz)
  have hΦi_ball : Set.InjOn Φ (Metric.ball 0 1) :=
    fun z hz w hw h => hfinj hz hw (by rw [← hΦeq hz, ← hΦeq hw]; exact h)
  have hΦim : Φ '' Metric.ball 0 1 = D := by
    rw [← hfim]
    exact Set.image_congr (fun z hz => hΦeq hz)
  -- The injectivity half (Carathéodory–Torhorst).
  have hΦi : Set.InjOn Φ (Metric.closedBall 0 1) :=
    injOn_closedBall_of_smooth_conformal v hv D hDo hDc hDb hDfr Φ hΦc hΦd hΦi_ball hΦim hΦs
  -- The continuous reparametrisation of the boundary values.
  have hGc : Continuous fun t : ℝ => Φ (Complex.exp (t * Complex.I)) := by
    refine ContinuousOn.comp_continuous hΦc (by fun_prop) ?_
    intro t
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
    simp
  have hGr : ∀ t : ℝ, Φ (Complex.exp (t * Complex.I)) ∈ Set.range v := by
    intro t
    exact hΦs (by rw [Metric.mem_sphere, dist_zero_right, Complex.norm_exp]; simp)
  obtain ⟨σ, hσc, hσeq⟩ :=
    continuous_sigma_of_loop v hv (fun t : ℝ => Φ (Complex.exp (t * Complex.I))) hGc hGr
  exact ⟨Φ, hΦc, hΦeq, hΦi, σ, hσc, hσeq⟩

end Work.RPB.B1a
