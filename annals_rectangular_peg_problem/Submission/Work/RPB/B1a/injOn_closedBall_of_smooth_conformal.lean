import Mathlib
import Submission.Work.RPB.B1a.Defs
import Submission.Work.RPB1a.jordan_domain_of_loop
import Submission.Work.RPB.Port.Drive.smooth_jordan_separation
import Submission.Work.RPB1a.deriv_ne_zero_of_injOn
import Submission.Work.RPB1a.Caratheodory.not_eqOn_const_sphere_of_injOn
import Submission.Work.RPB.B1a.exists_arc_const_of_eqOn_sphere

namespace Work.RPB.B1a

open Set Metric

/-- A smooth loop's image is homeomorphic to the circle, hence its frontier form gives a Jordan
curve.  (Reduction used below, kept separate for clarity.) -/
theorem isJordanCurveSet_range_of_isSmoothLoop (v : ℝ → ℂ) (hv : IsSmoothLoop v) :
    Work.RPB1a.IsJordanCurveSet (Set.range v) := by
  obtain ⟨γ, hemb, -, -, -, hrange⟩ := Work.RPB1a.exists_smooth_embedding_descend v hv
  exact Work.RPB1a.isJordanCurveSet_range_of_descend v γ hemb hrange

/-- If `closure D \ interior D = range v` with `v` a smooth loop, then `frontier D = range v`. -/
theorem frontier_eq_range_of_isSmoothLoop {v : ℝ → ℂ} {D : Set ℂ}
    (hDfr : closure D \ interior D = Set.range v) : frontier D = Set.range v := by
  rw [frontier_eq_closure_inter_closure, closure_compl]
  rw [Set.diff_eq] at hDfr
  exact hDfr

/-- **Carathéodory–Torhorst injectivity for a conformal map of the disc onto a domain bounded by a
smooth loop.**  If `Ψ` is continuous on the closed unit disc, holomorphic and injective on the open
disc, carries the open disc onto `D` (open, connected, bounded, with `closure D \ interior D` the
image of a smooth loop `v`) and the unit circle into `range v`, then `Ψ` is injective on the closed
disc.

The three cases of the closed disc are handled separately: interior/interior points by the
hypothesis `hΨi`; an interior and a circle point by `D ∩ frontier D = ∅` (the frontier is
`range v` and `D` is open); and two circle points by the topological half of Carathéodory's boundary
correspondence (`exists_arc_const_of_eqOn_sphere`, which turns a collision into constancy of `Ψ` on
an arc of the circle) together with the Schwarz-reflection argument
(`not_eqOn_const_sphere_of_injOn`) that rules such constancy out for a holomorphic injection. -/
theorem injOn_closedBall_of_smooth_conformal (v : ℝ → ℂ) (hv : Work.RPB.B1a.IsSmoothLoop v)
    (D : Set ℂ) (hDo : IsOpen D) (hDc : IsConnected D) (hDb : Bornology.IsBounded D)
    (hDfr : closure D \ interior D = Set.range v)
    (Ψ : ℂ → ℂ) (hΨc : ContinuousOn Ψ (Metric.closedBall 0 1))
    (hΨd : DifferentiableOn ℂ Ψ (Metric.ball 0 1)) (hΨi : Set.InjOn Ψ (Metric.ball 0 1))
    (hΨim : Ψ '' Metric.ball 0 1 = D)
    (hΨs : Set.MapsTo Ψ (Metric.sphere 0 1) (Set.range v)) :
    Set.InjOn Ψ (Metric.closedBall 0 1) := by
  have hfront : frontier D = Set.range v := frontier_eq_range_of_isSmoothLoop hDfr
  have hJ : Nonempty (frontier D ≃ₜ Circle) := by
    rw [hfront]
    exact isJordanCurveSet_range_of_isSmoothLoop v hv
  have hmt : Set.MapsTo Ψ (Metric.sphere 0 1) (frontier D) := by
    rw [hfront]
    exact hΨs
  -- Injectivity on the unit circle.
  have hsphere : Set.InjOn Ψ (Metric.sphere 0 1) := by
    intro p hp q hq hpq
    by_contra hne
    obtain ⟨u, hu, δ, hδ, harc⟩ :=
      Work.RPB.B1a.exists_arc_const_of_eqOn_sphere hDo hDb hJ hΨc hΨi hΨim hmt hp hq hne hpq
    refine Work.RPB1a.Caratheodory.not_eqOn_const_sphere_of_injOn (V := Metric.ball u δ)
      isOpen_ball ⟨u, ?_, hu⟩ (Ψ p) hΨc hΨd hΨi ?_
    · simp only [Metric.mem_ball, dist_self]; exact hδ
    · intro z hz
      have hz1 : ‖z - u‖ < δ := by simpa [dist_eq_norm] using hz.1
      exact harc z hz.2 hz1
  -- The four cases of the closed disc.
  intro p hp q hq hpq
  rw [← Metric.ball_union_sphere] at hp hq
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact hΨi hp hq hpq
  · exfalso
    have h1 : Ψ p ∈ D := by rw [← hΨim]; exact ⟨p, hp, rfl⟩
    have h2 : Ψ q ∈ frontier D := hmt hq
    rw [IsOpen.frontier_eq hDo] at h2
    exact h2.2 (hpq ▸ h1)
  · exfalso
    have h1 : Ψ q ∈ D := by rw [← hΨim]; exact ⟨q, hq, rfl⟩
    have h2 : Ψ p ∈ frontier D := hmt hp
    rw [IsOpen.frontier_eq hDo] at h2
    exact h2.2 (hpq.symm ▸ h1)
  · exact hsphere hp hq hpq

end Work.RPB.B1a
