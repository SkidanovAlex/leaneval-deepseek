import Submission.Work.Collar3D.Defs

/-!
# The models in `ℝ³`: the plane with its unit circle, and the flat model disc

The two configurations in which the collar structures of this chapter are *explicit*:

* `Work.Collar3D.plane` — the plane `{p : ℝ³ | p 2 = 0}`, with the unit circle
  `Work.Collar3D.planeCircle` in it.  The model collar is the chart
  `Φ p = (unit (p 0 + p 1 · i), log ‖p 0 + p 1 · i‖, p 2)` of the complement of the `z`-axis,
  which carries the plane to the middle sheet and the circle to the core
  (`Work.Collar3D.hasCollar_planeCircle`);
* `Work.Collar3D.modelDisc` — the flat disc `z ↦ (Re z, Im z, 0)`, whose collar is the trivial
  chart `p ↦ (p 0 + p 1 · i, p 2)` of the whole space (`Work.Collar3D.hasDiscCollar_modelDisc`).

These instances are the non-vacuity certificates of `Work.Collar3D.HasCollar` and
`Work.Collar3D.HasDiscCollar`, and the base cases of the computations of the push-off
(`Work.Collar3D.DiscCollar.cap`).
-/

open Set

namespace Work.Collar3D

noncomputable section

open Classical

/-- The model plane `{p : ℝ³ | p 2 = 0}`, the locally flat surface of the chapter. -/
def plane : Set R3 := {p : R3 | p 2 = 0}

@[simp] theorem mem_plane (p : R3) : p ∈ plane ↔ p 2 = 0 := Iff.rfl

/-- The unit circle of the plane, parametrised as `θ ↦ (cos θ, sin θ, 0)`. -/
def planeCircle (θ : ℝ) : R3 :=
  WithLp.toLp 2 ![(Real.cos θ : ℝ), (Real.sin θ : ℝ), (0 : ℝ)]

@[simp] theorem planeCircle_zero (θ : ℝ) : planeCircle θ 0 = Real.cos θ := by
  simp [planeCircle, WithLp.ofLp_toLp]

@[simp] theorem planeCircle_one (θ : ℝ) : planeCircle θ 1 = Real.sin θ := by
  simp [planeCircle, WithLp.ofLp_toLp]

@[simp] theorem planeCircle_two (θ : ℝ) : planeCircle θ 2 = 0 := by
  simp [planeCircle, WithLp.ofLp_toLp]

theorem planeCircle_mem_plane (θ : ℝ) : planeCircle θ ∈ plane := by simp [plane]

theorem continuous_planeCircle : Continuous planeCircle := by
  apply (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

theorem periodic_planeCircle : Function.Periodic planeCircle (2 * Real.pi) := by
  intro θ
  ext i
  fin_cases i <;> simp [planeCircle, Real.cos_add, Real.sin_add, Real.cos_two_pi, Real.sin_two_pi]

/-- **The model flat disc**: the identity disc of the plane `{p : ℝ³ | p 2 = 0}`, parametrised by
`z ↦ (Re z, Im z, 0)`. -/
def modelDisc : C(Disc, R3) where
  toFun z := WithLp.toLp 2 ![(z : ℂ).re, (z : ℂ).im, (0 : ℝ)]
  continuous_toFun := by
    apply (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop

@[simp] theorem modelDisc_zero (z : Disc) : modelDisc z 0 = (z : ℂ).re := by
  simp [modelDisc, WithLp.ofLp_toLp]

@[simp] theorem modelDisc_one (z : Disc) : modelDisc z 1 = (z : ℂ).im := by
  simp [modelDisc, WithLp.ofLp_toLp]

@[simp] theorem modelDisc_two (z : Disc) : modelDisc z 2 = 0 := by
  simp [modelDisc, WithLp.ofLp_toLp]

theorem modelDisc_injective : Function.Injective modelDisc := by
  intro z z' h
  apply Subtype.ext
  apply Complex.ext
  · have := congrArg (fun v : R3 => v 0) h; simpa using this
  · have := congrArg (fun v : R3 => v 1) h; simpa using this

theorem modelDisc_mem_plane (z : Disc) : modelDisc z ∈ plane := by
  simp [plane]

end

end Work.Collar3D
