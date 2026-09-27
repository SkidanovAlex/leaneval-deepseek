import Mathlib
import Submission.Work.KT.Defs

/-!
# `Work.KT.Cone.RadialDefs` — radial coordinates and the radial map

Helper definitions for the stable lifting of invertible matrices from `C(T)` to the mapping-cone
algebra `coneAlg f = C(T) ×_{C(S_V)} C(D_V)` (module `Submission.Work.KT.Cone.stable_lift`).

* `sphProj x hx` is the point of the unit sphere `S_V` in the direction of a nonzero point `x` of
  the closed unit ball;
* `radialCoord x = 1 - ‖x‖ ∈ [0,1]` is the radial coordinate (`1` at the origin, `0` on the
  boundary sphere);
* `radialMapAll f t₀ x = (f x̂, 1 - ‖x‖)` for `x ≠ 0`, and `(t₀, 1)` at the origin: the map along
  which a continuous function on `T × [0,1]` that is constant on `T × {1}` is pulled back to the
  ball.
-/

namespace Work.KT.Cone

open Work.KT Matrix

noncomputable section

open Classical

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The unit vector in the direction of a nonzero point of the closed unit ball. -/
def sphProj (x : Ball V) (hx : (x : V) ≠ 0) : Sph V :=
  ⟨‖(x : V)‖⁻¹ • (x : V), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

@[simp] lemma sphProj_coe (x : Ball V) (hx : (x : V) ≠ 0) :
    (sphProj x hx : V) = ‖(x : V)‖⁻¹ • (x : V) := rfl

/-- The radial coordinate `1 - ‖x‖` of the closed unit ball, as an element of `[0,1]`. -/
def radialCoord (x : Ball V) : unitInterval :=
  ⟨1 - ‖(x : V)‖, by
    have hx := mem_closedBall_zero_iff.mp x.2
    constructor <;> linarith [norm_nonneg (x : V)]⟩

@[simp] lemma radialCoord_coe (x : Ball V) :
    ((radialCoord x : unitInterval) : ℝ) = 1 - ‖(x : V)‖ := rfl

@[simp] lemma radialCoord_zero : radialCoord (0 : Ball V) = 1 := by
  apply Subtype.ext
  simp [radialCoord]

/-- The radial map `Ball V → T × [0,1]`, `x ↦ (f x̂, 1 - ‖x‖)`, with the value `(t₀, 1)` at the
origin.  It is not continuous, but its composition with any continuous `K : C(T × [0,1], ℂ)` that
is constant on `T × {1}` is (see `Work.KT.Cone.continuous_comp_radialMap`). -/
def radialMapAll {T : Type} [TopologicalSpace T] (f : C(Sph V, T)) (t₀ : T) :
    Ball V → T × unitInterval :=
  fun x => if hx : (x : V) = 0 then (t₀, radialCoord x) else (f (sphProj x hx), radialCoord x)

@[simp] lemma radialMapAll_zero {T : Type} [TopologicalSpace T] (f : C(Sph V, T)) (t₀ : T) :
    radialMapAll f t₀ (0 : Ball V) = (t₀, 1) := by
  simp [radialMapAll]

lemma radialMapAll_of_ne {T : Type} [TopologicalSpace T] (f : C(Sph V, T)) (t₀ : T)
    (x : Ball V) (hx : (x : V) ≠ 0) :
    radialMapAll f t₀ x = (f (sphProj x hx), radialCoord x) := by
  simp [radialMapAll, hx]

end

end Work.KT.Cone
