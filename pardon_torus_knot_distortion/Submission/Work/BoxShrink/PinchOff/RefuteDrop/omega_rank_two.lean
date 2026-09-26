import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.Config

/-!
# The winding span of the counterexample's box region is everything

This module proves `Work.BoxShrink.PinchOff.RefuteDrop.omega_rank_two`: at the linear
configuration `ψ = dropDiffeo` of `Config.lean` — the box `PBox (7/5) 0 (swap 0 2)` of the
counterexample to `DropCase` — the winding span of the box region is the *whole* of
`ℚ² = H₁(T²; ℚ)`.

The two independent loops of the torus `F = dropDiffeo(T²)` realised inside `Ω` are

* the **innermost longitude** `{φ = π}`, `θ ↦ dropVec (torusMap θ π)`, of winding vector
  `(1, 0)` — here `torusMap θ π = (cos θ, sin θ, 0)`, and the three coordinates of its image are
  the sines/cosines `(49/100) cos θ + (31/25) sin θ`, `(81/100) cos θ + (53/50) sin θ`,
  `(-2/25) cos θ - (39/100) sin θ`, all of amplitude `< 7/5 = dropS` (Lemma `abs_cos_sin_lt`);
* the **meridian** `{θ = arccos(-12/13)}`, `φ ↦ dropVec (torusMap θ₀ φ)`, of winding vector
  `(0, 1)` — here `(cos θ₀, sin θ₀) = (-12/13, 5/13)` is rational, `torusMap θ₀ φ =
  ((2 + cos φ)(-12/13), (2 + cos φ)(5/13), sin φ)`, and the three coordinates of the image are
  affine in `(2 + cos φ, sin φ) ∈ [1,3] × [-1,1]` with coefficient bounds `< 7/5 = dropS`
  (Lemma `abs_mul_add_bound`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff.RefuteDrop

noncomputable section

/-! ## Elementary bounds -/

/-- **A bound for a trigonometric polynomial of order one.**  `|a cos θ + b sin θ|` is at most
the amplitude `√(a² + b²)`; in particular it is `< c` as soon as `a² + b² < c²` and `0 ≤ c`. -/
theorem abs_cos_sin_lt (a b c θ : ℝ) (hc : 0 ≤ c) (h : a ^ 2 + b ^ 2 < c ^ 2) :
    |a * Real.cos θ + b * Real.sin θ| < c := by
  have hs : (a * Real.cos θ + b * Real.sin θ) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    have h1 : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    nlinarith [sq_nonneg (a * Real.sin θ - b * Real.cos θ)]
  exact abs_lt_of_sq_lt_sq (lt_of_le_of_lt hs h) hc

/-- **A bound for an affine expression in `(u, v)` with `u ∈ [1,3]` and `|v| ≤ 1`.** -/
theorem abs_mul_add_bound {A B c u v : ℝ} (hu1 : 1 ≤ u) (hu3 : u ≤ 3) (hv : |v| ≤ 1)
    (h : |A| * 3 + |B| < c) : |A * u + B * v| < c := by
  have hu0 : 0 ≤ u := le_trans zero_le_one hu1
  have huabs : |u| ≤ 3 := by rw [abs_of_nonneg hu0]; exact hu3
  calc |A * u + B * v| ≤ |A * u| + |B * v| := abs_add_le _ _
    _ = |A| * |u| + |B| * |v| := by rw [abs_mul, abs_mul]
    _ ≤ |A| * 3 + |B| * 1 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left huabs (abs_nonneg A)
        · exact mul_le_mul_of_nonneg_left hv (abs_nonneg B)
    _ = |A| * 3 + |B| := by ring
    _ < c := h

theorem dropS_pos : (0 : ℝ) < dropS := by norm_num [dropS]

/-- The box side `dropS` is at most the box side `2^{1/3} · dropS`. -/
theorem dropS_le_rpow13_mul : dropS ≤ (2 : ℝ) ^ (1 / 3 : ℝ) * dropS := by
  have h : (1 : ℝ) ≤ (2 : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
  nlinarith [dropS_pos]

/-- The box side `dropS` is at most the box side `2^{2/3} · dropS`. -/
theorem dropS_le_rpow23_mul : dropS ≤ (2 : ℝ) ^ (2 / 3 : ℝ) * dropS := by
  have h : (1 : ℝ) ≤ (2 : ℝ) ^ (2 / 3 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
  nlinarith [dropS_pos]

/-! ## The box of the configuration in coordinates -/

@[simp] theorem dropCyc_zero : dropCyc (0 : Fin 3) = 2 := by decide
@[simp] theorem dropCyc_one : dropCyc (1 : Fin 3) = 1 := by decide
@[simp] theorem dropCyc_two : dropCyc (2 : Fin 3) = 0 := by decide

@[simp] theorem dropC_zero : dropC (0 : Fin 3) = 0 := by simp [dropC]
@[simp] theorem dropC_one : dropC (1 : Fin 3) = 0 := by simp [dropC]
@[simp] theorem dropC_two : dropC (2 : Fin 3) = 0 := by simp [dropC]

/-- **The box of the counterexample in coordinates**: the coordinate `z` (index `2`) carries the
short side `dropS`, `y` (index `1`) the side `2^{1/3} · dropS` and `x` (index `0`) the side
`2^{2/3} · dropS`. -/
theorem mem_PBox_drop (y : R3) :
    y ∈ Submission.PBox dropS dropC dropCyc ↔
      |y.ofLp 2| < dropS ∧ |y.ofLp 1| < (2 : ℝ) ^ (1 / 3 : ℝ) * dropS ∧
        |y.ofLp 0| < (2 : ℝ) ^ (2 / 3 : ℝ) * dropS := by
  rw [Submission.mem_PBox]
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2

/-! ## The coordinates of `dropVec` -/

theorem dropVec_coord_zero (x : R3) : (dropVec x).ofLp 0 =
    (-2 / 25) * x.ofLp 0 + (-39 / 100) * x.ofLp 1 + (97 / 100) * x.ofLp 2 := by
  rw [dropVec_apply, Fin.sum_univ_three]; simp [dropA]

theorem dropVec_coord_one (x : R3) : (dropVec x).ofLp 1 =
    (81 / 100) * x.ofLp 0 + (53 / 50) * x.ofLp 1 + (-3 / 25) * x.ofLp 2 := by
  rw [dropVec_apply, Fin.sum_univ_three]; simp [dropA]

theorem dropVec_coord_two (x : R3) : (dropVec x).ofLp 2 =
    (49 / 100) * x.ofLp 0 + (31 / 25) * x.ofLp 1 + (59 / 100) * x.ofLp 2 := by
  rw [dropVec_apply, Fin.sum_univ_three]; simp [dropA]

/-! ## The innermost longitude `{φ = π}`

Its image under `dropVec` has coordinates `A cos θ + B sin θ` of amplitude `< dropS`; this is
the loop of winding vector `(1, 0)`. -/

theorem drop_longitude_mem (t : ℝ) :
    (Work.CoreTopology.longitudeCurve (Work.Smooth.Morse.torus dropDiffeo) Real.pi) t ∈
      Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus dropDiffeo) dropS dropC dropCyc := by
  refine ⟨(Work.CoreTopology.longitudeCurve _ _).mem t, ?_⟩
  have hval : (Work.CoreTopology.longitudeCurve (Work.Smooth.Morse.torus dropDiffeo) Real.pi) t
      = dropVec (Work.Core.torusMap t Real.pi) := by
    rw [Work.CoreTopology.longitudeCurve_apply, Work.Smooth.Morse.torus_psi, param_dropDiffeo]
  rw [mem_PBox_drop, hval]
  refine ⟨?_, ?_, ?_⟩
  · have hc : (dropVec (Work.Core.torusMap t Real.pi)).ofLp 2
        = (49 / 100) * Real.cos t + (31 / 25) * Real.sin t := by
      rw [dropVec_coord_two, Work.CoreTopology.torusMap_apply_zero,
        Work.CoreTopology.torusMap_apply_one, Work.CoreTopology.torusMap_apply_two,
        Real.cos_pi, Real.sin_pi]
      ring
    rw [hc]
    exact abs_cos_sin_lt (49 / 100) (31 / 25) dropS t (by norm_num [dropS]) (by norm_num [dropS])
  · have hc : (dropVec (Work.Core.torusMap t Real.pi)).ofLp 1
        = (81 / 100) * Real.cos t + (53 / 50) * Real.sin t := by
      rw [dropVec_coord_one, Work.CoreTopology.torusMap_apply_zero,
        Work.CoreTopology.torusMap_apply_one, Work.CoreTopology.torusMap_apply_two,
        Real.cos_pi, Real.sin_pi]
      ring
    rw [hc]
    exact lt_of_lt_of_le
      (abs_cos_sin_lt (81 / 100) (53 / 50) dropS t (by norm_num [dropS]) (by norm_num [dropS]))
      dropS_le_rpow13_mul
  · have hc : (dropVec (Work.Core.torusMap t Real.pi)).ofLp 0
        = (-2 / 25) * Real.cos t + (-39 / 100) * Real.sin t := by
      rw [dropVec_coord_zero, Work.CoreTopology.torusMap_apply_zero,
        Work.CoreTopology.torusMap_apply_one, Work.CoreTopology.torusMap_apply_two,
        Real.cos_pi, Real.sin_pi]
      ring
    rw [hc]
    exact lt_of_lt_of_le
      (abs_cos_sin_lt (-2 / 25) (-39 / 100) dropS t (by norm_num [dropS]) (by norm_num [dropS]))
      dropS_le_rpow23_mul

/-! ## The meridian `{θ = arccos(-12/13)}`

The rational point `(cos θ₀, sin θ₀) = (-12/13, 5/13)` of the unit circle makes the meridian lie
in the box; this is the loop of winding vector `(0, 1)`. -/

/-- The longitude parameter of the meridian of the counterexample. -/
def dropTheta : ℝ := Real.arccos (-(12 / 13))

theorem dropTheta_cos : Real.cos dropTheta = -(12 / 13) := by
  rw [dropTheta, Real.cos_arccos] <;> norm_num

theorem dropTheta_sin : Real.sin dropTheta = 5 / 13 := by
  rw [dropTheta, Real.sin_arccos]
  have h : (1 : ℝ) - (-(12 / 13)) ^ 2 = (5 / 13) ^ 2 := by norm_num
  rw [h, Real.sqrt_sq (by norm_num)]

theorem drop_meridian_mem (t : ℝ) :
    (Work.CoreTopology.meridianCurve (Work.Smooth.Morse.torus dropDiffeo) dropTheta) t ∈
      Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus dropDiffeo) dropS dropC dropCyc := by
  refine ⟨(Work.CoreTopology.meridianCurve _ _).mem t, ?_⟩
  have hval : (Work.CoreTopology.meridianCurve (Work.Smooth.Morse.torus dropDiffeo) dropTheta) t
      = dropVec (Work.Core.torusMap dropTheta t) := by
    rw [Work.CoreTopology.meridianCurve_apply, Work.Smooth.Morse.torus_psi, param_dropDiffeo]
  rw [mem_PBox_drop, hval]
  refine ⟨?_, ?_, ?_⟩
  · have hc : (dropVec (Work.Core.torusMap dropTheta t)).ofLp 2
        = (8 / 325) * (2 + Real.cos t) + (59 / 100) * Real.sin t := by
      rw [dropVec_coord_two, Work.CoreTopology.torusMap_apply_zero,
        Work.CoreTopology.torusMap_apply_one, Work.CoreTopology.torusMap_apply_two,
        dropTheta_cos, dropTheta_sin]
      ring
    rw [hc]
    exact abs_mul_add_bound (by linarith [Real.neg_one_le_cos t])
      (by linarith [Real.cos_le_one t]) (Real.abs_sin_le_one t) (by norm_num [dropS])
  · have hc : (dropVec (Work.Core.torusMap dropTheta t)).ofLp 1
        = (-17 / 50) * (2 + Real.cos t) + (-3 / 25) * Real.sin t := by
      rw [dropVec_coord_one, Work.CoreTopology.torusMap_apply_zero,
        Work.CoreTopology.torusMap_apply_one, Work.CoreTopology.torusMap_apply_two,
        dropTheta_cos, dropTheta_sin]
      ring
    rw [hc]
    exact lt_of_lt_of_le
      (abs_mul_add_bound (by linarith [Real.neg_one_le_cos t])
        (by linarith [Real.cos_le_one t]) (Real.abs_sin_le_one t) (by norm_num [dropS]))
      dropS_le_rpow13_mul
  · have hc : (dropVec (Work.Core.torusMap dropTheta t)).ofLp 0
        = (-99 / 1300) * (2 + Real.cos t) + (97 / 100) * Real.sin t := by
      rw [dropVec_coord_zero, Work.CoreTopology.torusMap_apply_zero,
        Work.CoreTopology.torusMap_apply_one, Work.CoreTopology.torusMap_apply_two,
        dropTheta_cos, dropTheta_sin]
      ring
    rw [hc]
    exact lt_of_lt_of_le
      (abs_mul_add_bound (by linarith [Real.neg_one_le_cos t])
        (by linarith [Real.cos_le_one t]) (Real.abs_sin_le_one t) (by norm_num [dropS]))
      dropS_le_rpow23_mul

/-! ## The winding span is everything -/

/-- **`W(Ω) = ⊤` at the counterexample's configuration.**  The innermost longitude and the
meridian of `dropTheta` lie in the box region and realise the two independent winding vectors
`(1, 0)` and `(0, 1)` of `H₁(T²; ℚ)`. -/
theorem omega_rank_two :
    Work.SurgeryInvariance.WindingSpan
      (Work.Smooth.Morse.torus Work.BoxShrink.PinchOff.RefuteDrop.dropDiffeo)
      (Work.BoxShrink.Core.boxRegion
        (Work.Smooth.Morse.torus Work.BoxShrink.PinchOff.RefuteDrop.dropDiffeo)
        Work.BoxShrink.PinchOff.RefuteDrop.dropS
        Work.BoxShrink.PinchOff.RefuteDrop.dropC
        Work.BoxShrink.PinchOff.RefuteDrop.dropCyc) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  have hL : ((((1 : ℤ) : ℚ), ((0 : ℤ) : ℚ)) : ℚ × ℚ) ∈
      Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus dropDiffeo)
        (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus dropDiffeo) dropS dropC
          dropCyc) := by
    apply Submodule.subset_span
    refine ⟨Work.CoreTopology.longitudeCurve (Work.Smooth.Morse.torus dropDiffeo) Real.pi,
      drop_longitude_mem, ?_⟩
    rw [Work.SurgeryInvariance.windingOf_eq _ _ (Work.CoreTopology.longitudeLift _ _),
      Work.CoreTopology.longitudeLift_winding]
  have hM : ((((0 : ℤ) : ℚ), ((1 : ℤ) : ℚ)) : ℚ × ℚ) ∈
      Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus dropDiffeo)
        (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus dropDiffeo) dropS dropC
          dropCyc) := by
    apply Submodule.subset_span
    refine ⟨Work.CoreTopology.meridianCurve (Work.Smooth.Morse.torus dropDiffeo) dropTheta,
      drop_meridian_mem, ?_⟩
    rw [Work.SurgeryInvariance.windingOf_eq _ _ (Work.CoreTopology.meridianLift _ _),
      Work.CoreTopology.meridianLift_winding]
  have hv : v = v.1 • ((((1 : ℤ) : ℚ), ((0 : ℤ) : ℚ)) : ℚ × ℚ) +
      v.2 • ((((0 : ℤ) : ℚ), ((1 : ℤ) : ℚ)) : ℚ × ℚ) := by
    ext <;> simp
  rw [hv]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hL) (Submodule.smul_mem _ _ hM)

end

end Work.BoxShrink.PinchOff.RefuteDrop
