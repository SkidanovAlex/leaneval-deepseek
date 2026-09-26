import Mathlib
import Submission.Commons.AlgebraicTopology.FundamentalGroup.pi1_circle_eq_int
import Submission.Commons.Topology.Homotopy.simplyConnectedSpace_of_retraction
import Submission.Commons.Topology.Brouwer.exists_retraction_unitDisk

namespace Commons.Topology.Brouwer

open scoped RealInnerProductSpace

/-- A continuous retraction of the closed unit disk of `ℂ` onto its boundary circle is
impossible: the disk is contractible, so by
`Commons.Topology.Homotopy.simplyConnectedSpace_of_retraction` the boundary circle would be
simply connected, whereas `π₁(S¹) ≃ ℤ` is non-trivial
(`Commons.AlgebraicTopology.FundamentalGroup.pi1_circle_eq_int`). -/
theorem not_exists_retraction_unitDisk :
    ¬ ∃ ρ : C(Metric.closedBall (0 : ℂ) 1, Metric.sphere (0 : ℂ) 1),
        ∀ (z : ℂ) (hz : z ∈ Metric.closedBall (0:ℂ) 1) (hz1 : z ∈ Metric.sphere (0:ℂ) 1),
          ρ ⟨z, hz⟩ = ⟨z, hz1⟩ := by
  rintro ⟨ρ, hρ⟩
  have hincl : ∀ z : Metric.sphere (0:ℂ) 1, (z:ℂ) ∈ Metric.closedBall (0:ℂ) 1 := by
    intro z
    rw [mem_closedBall_zero_iff, mem_sphere_zero_iff_norm.mp z.2]
  let i : C(Metric.sphere (0:ℂ) 1, Metric.closedBall (0:ℂ) 1) :=
    ⟨fun z => ⟨z.1, hincl z⟩, by fun_prop⟩
  have hcomp : ρ.comp i = ContinuousMap.id (Metric.sphere (0:ℂ) 1) := by
    ext z
    simpa [i] using congrArg Subtype.val (hρ z.1 (hincl z) z.2)
  have hcontr : ContractibleSpace (Metric.closedBall (0:ℂ) 1) :=
    (convex_closedBall (0:ℂ) 1).contractibleSpace ⟨0, by simp [Metric.mem_closedBall]⟩
  have hsc : SimplyConnectedSpace (Metric.sphere (0:ℂ) 1) :=
    Commons.Topology.Homotopy.simplyConnectedSpace_of_retraction i ρ hcomp
  have hsc' : SimplyConnectedSpace Circle :=
    inferInstanceAs (SimplyConnectedSpace (Metric.sphere (0:ℂ) 1))
  obtain ⟨emul⟩ := Commons.AlgebraicTopology.FundamentalGroup.pi1_circle_eq_int
  exact (not_nontrivial_iff_subsingleton.mpr
      (inferInstance : Subsingleton (FundamentalGroup Circle (1:Circle))))
    emul.toEquiv.nontrivial

/-- Brouwer fixed point theorem for the closed unit disk of `ℂ`: every continuous self-map of
`Metric.closedBall (0 : ℂ) 1` has a fixed point.  Otherwise the ray construction
(`exists_retraction_unitDisk`) would retract the contractible disk onto its boundary circle,
which is impossible. -/
theorem brouwer_fixed_point_unitDisk
    (f : C(Metric.closedBall (0 : ℂ) 1, Metric.closedBall (0 : ℂ) 1)) : ∃ x, f x = x := by
  by_contra h
  push Not at h
  exact not_exists_retraction_unitDisk (exists_retraction_unitDisk f h)

/-- Brouwer fixed point result in dimension 2, for a closed disk of arbitrary centre and radius in the complex plane. -/
theorem brouwer_fixed_point_closedBall (c : ℂ) {r : ℝ} (hr : 0 < r)
    (f : C(Metric.closedBall c r, Metric.closedBall c r)) : ∃ x, f x = x := by
  -- transport the unit-disk statement along the similarity `x ↦ c + r * x`
  let σ : C(Metric.closedBall (0:ℂ) 1, Metric.closedBall c r) :=
    ⟨fun x => ⟨c + (r : ℂ) * (x : ℂ), by
        have hx : ‖(x : ℂ)‖ ≤ 1 := by
          have h := Metric.mem_closedBall.mp x.2
          rwa [dist_eq_norm, sub_zero] at h
        rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
        nlinarith⟩,
      by fun_prop⟩
  let τ : C(Metric.closedBall c r, Metric.closedBall (0:ℂ) 1) :=
    ⟨fun y => ⟨((y : ℂ) - c) / r, by
        have hy : ‖(y : ℂ) - c‖ ≤ r := by
          have h := Metric.mem_closedBall.mp y.2
          rwa [dist_eq_norm] at h
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
        rw [div_le_one hr]
        exact hy⟩,
      by fun_prop⟩
  obtain ⟨x, hx⟩ := brouwer_fixed_point_unitDisk (τ.comp (f.comp σ))
  refine ⟨σ x, ?_⟩
  have hx1 : (((f (σ x) : Metric.closedBall c r) : ℂ) - c) / r = (x : ℂ) := by
    have h := congrArg (fun y : Metric.closedBall (0:ℂ) 1 => (y : ℂ)) hx
    simpa [τ, ContinuousMap.comp_apply] using h
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hx3 : ((f (σ x) : Metric.closedBall c r) : ℂ) - c = (x : ℂ) * r :=
    (div_eq_iff hrC).mp hx1
  apply Subtype.ext
  show ((f (σ x) : Metric.closedBall c r) : ℂ) = c + (r : ℂ) * (x : ℂ)
  linear_combination hx3

end Commons.Topology.Brouwer
