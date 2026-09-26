import Mathlib
import Submission.Work.CoreTopology.Disk

/-!
# The meridian circle bounds a compressing disc

We build the explicit embedded disc filling the meridian circle
`{θ = const}` of the standard torus of revolution (major radius `2`, minor
radius `1`).  Concretely, for `z` in the closed unit disc of `ℂ` we put

  `e z = ((2 + z.re) cos θ, (2 + z.re) sin θ, z.im)`,

a parametrisation of the meridian disc of the solid torus bounded by the
standard torus.  We verify the three requirements in
`Work.CoreTopology.IsBoundingDisk`:

* `e` is injective (`meridianDiskMap_injective`);
* the unit circle `θ' ↦ exp (i θ')` is mapped to the meridian circle
  (`meridianDiskMap_circlePoint`);
* the open unit disc is mapped off the torus surface
  (`meridianDiskMap_not_mem_carrier`).

Thus the meridian circle bounds a disc in the complement of the torus.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

noncomputable section

/-- The meridian disc of the standard torus, as a map on the closed unit disc of
`ℂ`: `e z = ((2 + z.re) cos θ, (2 + z.re) sin θ, z.im)`, written out on the
coordinates of `ℝ³`. -/
def meridianDiskMap (θ : ℝ) (z : ℂ) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i.val = 0 then (2 + z.re) * Real.cos θ
    else if i.val = 1 then (2 + z.re) * Real.sin θ
    else z.im)

/-- The coordinates of the meridian disc map. -/
lemma meridianDiskMap_apply (θ : ℝ) (z : ℂ) (i : Fin 3) :
    meridianDiskMap θ z i = (if i.val = 0 then (2 + z.re) * Real.cos θ
       else if i.val = 1 then (2 + z.re) * Real.sin θ else z.im) := by
  simp only [meridianDiskMap, WithLp.ofLp_toLp]

lemma meridianDiskMap_apply_zero (θ : ℝ) (z : ℂ) :
    meridianDiskMap θ z (0 : Fin 3) = (2 + z.re) * Real.cos θ := by
  rw [meridianDiskMap_apply]; simp

lemma meridianDiskMap_apply_one (θ : ℝ) (z : ℂ) :
    meridianDiskMap θ z (1 : Fin 3) = (2 + z.re) * Real.sin θ := by
  rw [meridianDiskMap_apply]; simp

lemma meridianDiskMap_apply_two (θ : ℝ) (z : ℂ) :
    meridianDiskMap θ z (2 : Fin 3) = z.im := by
  rw [meridianDiskMap_apply]; simp

/-- The real part of the point `exp (i θ)` of the unit circle. -/
lemma circlePoint_re (θ : ℝ) : ((circlePoint θ : ℂ)).re = Real.cos θ := by
  rw [circlePoint_coe, Complex.exp_re]; simp

/-- The imaginary part of the point `exp (i θ)` of the unit circle. -/
lemma circlePoint_im (θ : ℝ) : ((circlePoint θ : ℂ)).im = Real.sin θ := by
  rw [circlePoint_coe, Complex.exp_im]; simp

/-- The meridian disc map is continuous. -/
lemma continuous_meridianDiskMap (θ : ℝ) : Continuous (meridianDiskMap θ) := by
  have h : Continuous (fun z : ℂ => fun i : Fin 3 =>
      (if i.val = 0 then (2 + z.re) * Real.cos θ
       else if i.val = 1 then (2 + z.re) * Real.sin θ
       else z.im : ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp h

set_option linter.unusedSimpArgs false in
/-- On the unit circle, the meridian disc map is the meridian circle: it sends
`exp (i θ')` to `torusMap θ θ'`. -/
lemma meridianDiskMap_circlePoint (θ θ' : ℝ) :
    meridianDiskMap θ (circlePoint θ' : ℂ) = Work.Core.torusMap θ θ' := by
  ext i
  fin_cases i <;>
    simp [meridianDiskMap, Work.Core.torusMap, circlePoint_re, circlePoint_im]

/-- The meridian disc map is injective (on all of `ℂ`).  Indeed the projection to
the `(cos θ, sin θ)`-coordinates determines `2 + z.re`, and the third coordinate
is `z.im`. -/
lemma meridianDiskMap_injective (θ : ℝ) : Function.Injective (meridianDiskMap θ) := by
  intro z w h
  have h0 : (2 + z.re) * Real.cos θ = (2 + w.re) * Real.cos θ := by
    have hh := congrArg (fun X : R3 => X (0 : Fin 3)) h
    rwa [meridianDiskMap_apply_zero, meridianDiskMap_apply_zero] at hh
  have h1 : (2 + z.re) * Real.sin θ = (2 + w.re) * Real.sin θ := by
    have hh := congrArg (fun X : R3 => X (1 : Fin 3)) h
    rwa [meridianDiskMap_apply_one, meridianDiskMap_apply_one] at hh
  have h2 : z.im = w.im := by
    have hh := congrArg (fun X : R3 => X (2 : Fin 3)) h
    rwa [meridianDiskMap_apply_two, meridianDiskMap_apply_two] at hh
  have hsum : (2 + z.re) * (Real.cos θ ^ 2 + Real.sin θ ^ 2) =
      (2 + w.re) * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by
    linear_combination h0 * Real.cos θ + h1 * Real.sin θ
  rw [Real.cos_sq_add_sin_sq θ, mul_one, mul_one] at hsum
  exact Complex.ext (by linarith) h2

/-- No point of the open unit disc is mapped into the torus surface.  A point of
the torus whose `(cos θ, sin θ)`-coordinates agree with those of `e z` forces
`cos φ = z.re` and `sin φ = z.im`, hence `z` on the unit circle. -/
lemma meridianDiskMap_not_mem_carrier (θ : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    meridianDiskMap θ z ∉ standard.carrier := by
  rintro ⟨p, hp⟩
  have hp' : Work.Core.torusMap p.1 p.2 = meridianDiskMap θ z := hp
  have h0 : (2 + Real.cos p.2) * Real.cos p.1 = (2 + z.re) * Real.cos θ := by
    have hh := congrArg (fun X : R3 => X (0 : Fin 3)) hp'
    rwa [Work.Core.torusMap_apply_zero, meridianDiskMap_apply_zero] at hh
  have h1 : (2 + Real.cos p.2) * Real.sin p.1 = (2 + z.re) * Real.sin θ := by
    have hh := congrArg (fun X : R3 => X (1 : Fin 3)) hp'
    rwa [Work.Core.torusMap_apply_one, meridianDiskMap_apply_one] at hh
  have h2 : Real.sin p.2 = z.im := by
    have hh := congrArg (fun X : R3 => X (2 : Fin 3)) hp'
    rwa [Work.Core.torusMap_apply_two, meridianDiskMap_apply_two] at hh
  -- Comparing squared radii of the `(cos, sin)` components gives
  -- `(2 + cos p.2) ^ 2 = (2 + z.re) ^ 2`.
  have hsq : (2 + Real.cos p.2) ^ 2 = (2 + z.re) ^ 2 := by
    have key : ((2 + Real.cos p.2) * Real.cos p.1) ^ 2
          + ((2 + Real.cos p.2) * Real.sin p.1) ^ 2
        = ((2 + z.re) * Real.cos θ) ^ 2 + ((2 + z.re) * Real.sin θ) ^ 2 := by
      rw [h0, h1]
    nlinarith [key, Real.cos_sq_add_sin_sq p.1, Real.cos_sq_add_sin_sq θ]
  have hpy : 0 < 2 + Real.cos p.2 := by linarith [Real.neg_one_le_cos p.2]
  have hpz : 0 < 2 + z.re := by
    have hle : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have hlt : -1 < z.re := by linarith [(abs_le.mp hle).1, hz]
    linarith
  have hcos : Real.cos p.2 = z.re := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hh | hh <;> linarith
  have hnorm : ‖z‖ = 1 := by
    have hsq' : z.re * z.re + z.im * z.im = 1 := by
      rw [← hcos, ← h2]; nlinarith [Real.cos_sq_add_sin_sq p.2]
    have h2' : ‖z‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; exact hsq'
    nlinarith [norm_nonneg z]
  linarith

/-- The meridian circle `{θ = const}` of the standard torus of revolution is the boundary of an embedded disc lying in the solid torus it bounds: for `z` in the closed unit disc of `ℂ`, put `e z = ((2 + z.re) cos θ, (2 + z.re) sin θ, z.im)`. Then `e` is injective, maps the unit circle `θ' ↦ exp(iθ')` to the meridian circle `meridianCurve standard θ`, and no point of the open unit disc maps into the torus surface. Hence the meridian circle bounds a disc in the complement of `F`. -/
theorem meridianCurve_boundsDisk (θ : ℝ) :
    BoundsDiskInComplement standard (meridianCurve standard θ) := by
  refine ⟨{ toFun := fun z => meridianDiskMap θ (z : ℂ),
            continuous_toFun := (continuous_meridianDiskMap θ).comp continuous_subtype_val },
    ?_, ?_, ?_⟩
  · intro z w h
    exact Subtype.ext (meridianDiskMap_injective θ h)
  · intro θ'
    show meridianDiskMap θ ((circlePoint θ' : Metric.closedBall (0 : ℂ) 1) : ℂ) =
      (meridianCurve standard θ).γ θ'
    rw [meridianDiskMap_circlePoint]
    rfl
  · intro z hz
    exact meridianDiskMap_not_mem_carrier θ hz

end

end Work.CoreTopology
