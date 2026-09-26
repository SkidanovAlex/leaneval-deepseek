import Mathlib
import Submission.Commons.Topology.Circle.jordan_curve_separation
import Submission.Commons.Topology.Homotopy.nullHomotopic_comp_left

/-!
# A loop with a "logarithmic" lift of winding one is not nullhomotopic

Given a loop `γ : Circle → {z : ℂ // z ≠ 0}` in the punctured plane together with a
continuous `G : ℝ → ℝ × ℝ` whose second component is positive and which satisfies

* `(G t).2 * exp ((G t).1 * I) = γ (circle.exp t)` (so `(G t).2` is the modulus and
  `(G t).1` an argument of `γ (circle.exp t)`), and
* `G (t + 2π) = ((G t).1 + 2π, (G t).2)` (the argument increases by `2π` over one period),

the loop `γ` is not nullhomotopic: its winding number around the origin is `1`.

The proof retracts the punctured plane onto the unit circle and computes the degree of
the resulting map `Circle → Circle` from the given lift.
-/

namespace Commons.Topology.Plane

/-- The retraction of the punctured plane onto the unit circle, `z ↦ z / ‖z‖`. -/
noncomputable def toUnitCircle : C({z : ℂ // z ≠ 0}, Circle) where
  toFun z := ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), by
    show dist ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) 0 = 1
    rw [dist_zero_right, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    have hz : ‖(z : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr z.2
    field_simp⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro z
      exact_mod_cast (norm_ne_zero_iff.mpr z.2 : ‖(z : ℂ)‖ ≠ 0)

@[simp] lemma toUnitCircle_coe (z : {z : ℂ // z ≠ 0}) :
    ((toUnitCircle z : Circle) : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) := rfl

/-- The first coordinate of a continuous map `ℝ → ℝ × ℝ`. -/
noncomputable def stripArg (G : C(ℝ, ℝ × ℝ)) : C(ℝ, ℝ) :=
  ⟨fun t => (G t).1, continuous_fst.comp G.continuous⟩

@[simp] lemma stripArg_apply (G : C(ℝ, ℝ × ℝ)) (t : ℝ) : stripArg G t = (G t).1 := rfl

/-- The first coordinate of `G` is a lift of `toUnitCircle ∘ γ ∘ Circle.exp`. -/
lemma exp_stripArg_eq {γ : C(Circle, {z : ℂ // z ≠ 0})}
    (G : C(ℝ, ℝ × ℝ)) (hpos : ∀ t, 0 < (G t).2)
    (hG : ∀ t, ((G t).2 : ℂ) * Complex.exp (((G t).1 : ℂ) * Complex.I) = (γ (Circle.exp t) : ℂ)) :
    (fun t => Circle.exp (stripArg G t)) = (fun t => (toUnitCircle.comp γ) (Circle.exp t)) := by
  funext t
  apply Subtype.ext
  rw [Circle.coe_exp, ContinuousMap.comp_apply, toUnitCircle_coe]
  simp only [stripArg_apply]
  have hr : ((G t).2 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hpos t))
  have hnorm : ‖(γ (Circle.exp t) : ℂ)‖ = (G t).2 := by
    rw [← hG t, norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt (hpos t)),
      Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [hnorm, ← hG t]
  field_simp

/-- The degree of `toUnitCircle ∘ γ`, computed from the lift `G`, equals `1`. -/
lemma loopDegree_unitCircle_comp_eq_one {γ : C(Circle, {z : ℂ // z ≠ 0})}
    (G : C(ℝ, ℝ × ℝ)) (hpos : ∀ t, 0 < (G t).2)
    (hG : ∀ t, ((G t).2 : ℂ) * Complex.exp (((G t).1 : ℂ) * Complex.I) = (γ (Circle.exp t) : ℂ))
    (hper : ∀ t, G (t + 2 * Real.pi) = ((G t).1 + 2 * Real.pi, (G t).2)) :
    Commons.Topology.Circle.loopDegree (toUnitCircle.comp γ) = 1 := by
  let f : C(Circle, Circle) := toUnitCircle.comp γ
  have hliftF : (fun t => Circle.exp (stripArg G t)) = (fun t => f (Circle.exp t)) := by
    simpa [f] using exp_stripArg_eq G hpos hG
  have hliftL : (fun t => Circle.exp (Commons.Topology.Circle.loopLift f t))
      = (fun t => f (Circle.exp t)) := by
    funext t
    have := congr_fun (Commons.Topology.Circle.loopLift_lifts f) t
    simpa [ContinuousMap.comp_apply] using this
  obtain ⟨m, hm⟩ := Commons.Topology.Circle.diff_lift_const
    (F := stripArg G) (G := Commons.Topology.Circle.loopLift f) (hliftF.trans hliftL.symm)
  have hp : stripArg G (2 * Real.pi) = stripArg G 0 + 2 * Real.pi := by
    have := congrArg Prod.fst (hper 0)
    simpa [stripArg_apply, zero_add] using this
  have hdiff : Commons.Topology.Circle.loopLift f (2 * Real.pi)
      - Commons.Topology.Circle.loopLift f 0 = 2 * Real.pi := by
    have h1 := hm (2 * Real.pi)
    have h0 := hm 0
    linarith
  have hper2 := Commons.Topology.Circle.loopLift_period f
  have hdeg : (Commons.Topology.Circle.loopDegree f : ℝ) * (2 * Real.pi) = 2 * Real.pi := by
    linarith
  have hne : (2 * (Real.pi : ℝ)) ≠ 0 := by positivity
  have h4 : (Commons.Topology.Circle.loopDegree f : ℝ) = 1 := by
    have h : ((Commons.Topology.Circle.loopDegree f : ℝ) - 1) * (2 * Real.pi) = 0 := by
      ring_nf; linarith
    have h2 : (Commons.Topology.Circle.loopDegree f : ℝ) - 1 = 0 :=
      (mul_eq_zero.mp h).resolve_right hne
    linarith
  have h5 : Commons.Topology.Circle.loopDegree f = 1 := by exact_mod_cast h4
  simpa [f] using h5

theorem loop_of_strip_lift_not_nullhomotopic {γ : C(Circle, {z : ℂ // z ≠ 0})}
    (G : C(ℝ, ℝ × ℝ)) (hpos : ∀ t, 0 < (G t).2)
    (hG : ∀ t, ((G t).2 : ℂ) * Complex.exp (((G t).1 : ℂ) * Complex.I) = (γ (Circle.exp t) : ℂ))
    (hper : ∀ t, G (t + 2 * Real.pi) = ((G t).1 + 2 * Real.pi, (G t).2)) :
    ¬ γ.Nullhomotopic := by
  intro hnull
  have hf : (toUnitCircle.comp γ).Nullhomotopic :=
    Commons.Topology.Homotopy.nullHomotopic_comp_left toUnitCircle hnull
  have h0 := Commons.Topology.Circle.loopDegree_eq_zero_of_nullhomotopic hf
  have h1 := loopDegree_unitCircle_comp_eq_one G hpos hG hper
  rw [h1] at h0
  exact one_ne_zero h0

end Commons.Topology.Plane
