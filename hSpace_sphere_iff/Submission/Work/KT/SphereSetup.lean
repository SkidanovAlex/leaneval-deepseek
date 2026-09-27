import Mathlib
import Submission.Work.KT.Defs

/-!
# Sphere/ball setup for `sphere_K`

Auxiliary definitions shared by `Work.KT.sphere_K` and the lemmas it delegates.

* `Euc d` = `ℝ^d`.
* `ModelSphere d` = the unit sphere `S^d`, modelled as the unit sphere of the `ℓ²`-product
  `ℝ^d × ℝ`.  This is the model in which the standard "disc modulo boundary" quotient map
  `D^d → S^d`, `x ↦ (sin (π‖x‖) • (x/‖x‖), -cos (π‖x‖))`, is written directly.
* `sphKT_northPole d` = `(0,1)`, the image of the boundary of the disc under that quotient map.
* `antipode x = -x` for `x` in a unit sphere.
-/

namespace Work.KT

noncomputable section

/-- `ℝ^d`. -/
abbrev Euc (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- The model sphere `S^d`, the unit sphere of the `ℓ²`-product `ℝ^d × ℝ`. -/
abbrev ModelSphere (d : ℕ) : Type := WithLp 2 (Euc d × ℝ)

/-- The north pole `(0,1)` of the model sphere `S^d`. -/
def sphKT_northPole (d : ℕ) : Sph (ModelSphere d) :=
  ⟨WithLp.toLp 2 ((0 : Euc d), (1 : ℝ)), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, WithLp.prod_norm_eq_of_L2]
    simp⟩

@[simp] lemma northPole_coe (d : ℕ) :
    ((sphKT_northPole d : Sph (ModelSphere d)) : ModelSphere d)
      = WithLp.toLp 2 ((0 : Euc d), (1 : ℝ)) := rfl

/-- The antipode of a point of a unit sphere. -/
def antipode {V : Type} [NormedAddCommGroup V] (x : Sph V) : Sph V :=
  ⟨-(x : V), by
    have h : ‖(x : V)‖ = 1 := by
      have h' := Metric.mem_sphere.mp x.2
      rwa [dist_eq_norm, sub_zero] at h'
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    simpa using h⟩

@[simp] lemma antipode_coe {V : Type} [NormedAddCommGroup V] (x : Sph V) :
    (antipode x : V) = -(x : V) := rfl

end

end Work.KT
