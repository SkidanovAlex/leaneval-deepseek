import Mathlib
import Submission.Work.BoxShrink.Bubble.standard_counterexample

/-!
# The tangent-trace configuration of the standard torus: coordinates and shape lemma

This module fixes one configuration of the standard torus of revolution and proves the elementary
facts about it on which the four parts of
`Work.BoxShrink.PinchOff.tangent_trace_counterexample_data` rest.

The configuration is

* the standard torus `Work.CoreTopology.standard` (`ψ u v = ((2+cos v) cos u, (2+cos v) sin u,
  sin v)`),
* the box centre `c = (1,0,0)`, which is the point `ψ 0 π` of the torus: the plane `{x = 1}` is
  *tangent* to the torus there,
* the coordinate permutation `σ = (0 1 2)` (`σ 0 = 1`, `σ 1 = 2`, `σ 2 = 0`), so that the box is
  `{|y 1| < 13/10, |y 2| < (13/10)·2^{1/3}, |y 0 - 1| < (13/10)·2^{2/3}}`,
* box radius `s = 13/10` and cutting plane `{y 0 = 1}` (`u = 0`).

Contents:

* the **toolkit**: a one-sided bound `c < cos (f t)` (`-1 < c < 1`) on a continuous function forces
  `|f t - f s| < 2 arccos c`, and avoiding a lattice `a + 2πℤ` forces `|f t - f s| < 2π`; in both
  cases an integer multiple of `2π` (a winding increment) must vanish (`int_eq_zero_of_cos_gt`,
  `int_eq_zero_of_notMem_lattice`);
* the **box in coordinates** (`mem_PBox_tangent`, `boxNorm_tangent`) and the numeric bounds;
* the **shape lemma for the box sphere** (`sphereSet_shape`): a point of the torus on the box
  sphere has `cos v > -0.95` and `cos (u - π) > -0.92`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-! ## The configuration -/

/-- The cyclic permutation `(0 1 2)` of the three coordinates, written as a product of two
transpositions: `0 ↦ 1`, `1 ↦ 2`, `2 ↦ 0`. -/
def tangentCyc3 : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2

/-- The centre `(1, 0, 0)`: the point `ψ 0 π` of the standard torus, where the plane `{x = 1}` is
tangent to the torus. -/
def tangentCtr : R3 := WithLp.toLp 2 (![1, 0, 0] : Fin 3 → ℝ)

/-- The box radius `13/10`. -/
def tangentRad : ℝ := 13 / 10

@[simp] theorem tangentCyc3_zero : tangentCyc3 0 = 1 := by decide
@[simp] theorem tangentCyc3_one : tangentCyc3 1 = 2 := by decide
@[simp] theorem tangentCyc3_two : tangentCyc3 2 = 0 := by decide

@[simp] theorem tangentCtr_zero : tangentCtr 0 = 1 := by simp [tangentCtr]
@[simp] theorem tangentCtr_one : tangentCtr 1 = 0 := by simp [tangentCtr]
@[simp] theorem tangentCtr_two : tangentCtr 2 = 0 := by simp [tangentCtr]

theorem tangentRad_eq : tangentRad = (13 : ℝ) / 10 := rfl

/-! ## The toolkit -/

/-- **A one-sided bound on the cosine confines the argument.**  If `c < cos (f t)` for all `t`,
with `-1 < c < 1`, then over one period the image of `f` lies in an interval of length
`2 arccos c < 2π`: `cos x > c` says that the distance from `x` to `2πℤ` is `< arccos c`. -/
theorem abs_sub_lt_of_cos_gt {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ} (hc1 : -1 < c) (hc2 : c < 1)
    (h : ∀ t : ℝ, c < Real.cos (f t)) :
    ∀ s t : ℝ, |f t - f s| < 2 * Real.arccos c := by
  have hθ0 : 0 < Real.arccos c := Real.arccos_pos.mpr hc2
  have hθπ : Real.arccos c < Real.pi := Real.arccos_lt_pi.mpr hc1
  have hcosθ : Real.cos (Real.arccos c) = c := Real.cos_arccos (le_of_lt hc1) (le_of_lt hc2)
  have hmain : ∀ s t : ℝ, |f t - f s| <
      2 * Real.pi - ((2 * Real.pi - Real.arccos c) - Real.arccos c) := by
    refine Work.BoxShrink.Bubble.cex_abs_sub_lt_of_forall_notMem_Icc (f := f) hf
      (L := 2 * Real.pi) (a := Real.arccos c) (b := 2 * Real.pi - Real.arccos c)
      (by positivity) (by linarith) (by linarith) ?_
    intro t k hmem
    have h1 : Real.arccos c + (k : ℝ) * (2 * Real.pi) ≤ f t := hmem.1
    have h2 : f t ≤ (2 * Real.pi - Real.arccos c) + (k : ℝ) * (2 * Real.pi) := hmem.2
    have hx1 : Real.arccos c ≤ f t - (k : ℝ) * (2 * Real.pi) := by linarith
    have hx2 : f t - (k : ℝ) * (2 * Real.pi) ≤ 2 * Real.pi - Real.arccos c := by linarith
    have hcos_eq : Real.cos (f t) = Real.cos (f t - (k : ℝ) * (2 * Real.pi)) := by
      conv_lhs => rw [show f t = (f t - (k : ℝ) * (2 * Real.pi)) + (k : ℝ) * (2 * Real.pi)
        by ring]
      rw [Real.cos_add_int_mul_two_pi]
    have hle : Real.cos (f t - (k : ℝ) * (2 * Real.pi)) ≤ Real.cos (Real.arccos c) := by
      rcases le_total (f t - (k : ℝ) * (2 * Real.pi)) Real.pi with hcase | hcase
      · exact Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hθ0) hcase hx1
      · have hy1 : Real.arccos c ≤ 2 * Real.pi - (f t - (k : ℝ) * (2 * Real.pi)) := by linarith
        have hy2 : 2 * Real.pi - (f t - (k : ℝ) * (2 * Real.pi)) ≤ Real.pi := by linarith
        have h3 := Real.cos_le_cos_of_nonneg_of_le_pi (x := Real.arccos c)
          (y := 2 * Real.pi - (f t - (k : ℝ) * (2 * Real.pi))) (le_of_lt hθ0) hy2 hy1
        rwa [Real.cos_two_pi_sub] at h3
    rw [hcosθ, ← hcos_eq] at hle
    linarith [h t]
  intro s t
  have := hmain s t
  linarith

/-- **An integer winding increment below `2 arccos c` vanishes.** -/
theorem int_eq_zero_of_cos_gt {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ} (hc1 : -1 < c)
    (hc2 : c < 1) (h : ∀ t : ℝ, c < Real.cos (f t)) {m : ℤ}
    (hdiff : f (2 * Real.pi) - f 0 = (m : ℝ) * (2 * Real.pi)) : m = 0 := by
  have hb := abs_sub_lt_of_cos_gt hf hc1 hc2 h 0 (2 * Real.pi)
  rw [hdiff] at hb
  exact Work.BoxShrink.Bubble.cex_int_eq_zero_of_abs_mul_two_pi_lt
    (b := 2 * Real.arccos c) (by linarith [Real.arccos_le_pi c]) hb

/-- **A continuous function avoiding a lattice `a + 2πℤ` is confined over one period.** -/
theorem abs_sub_lt_two_pi_of_notMem_lattice {f : ℝ → ℝ} (hf : Continuous f) {a : ℝ}
    (h : ∀ t : ℝ, ∀ k : ℤ, f t ≠ a + (k : ℝ) * (2 * Real.pi)) :
    ∀ s t : ℝ, |f t - f s| < 2 * Real.pi := by
  have hmain : ∀ s t : ℝ, |f t - f s| < 2 * Real.pi - (a - a) :=
    Work.BoxShrink.Bubble.cex_abs_sub_lt_of_forall_notMem_Icc (f := f) hf
      (L := 2 * Real.pi) (a := a) (b := a) (by positivity) (le_refl _)
      (by linarith [Real.pi_pos])
      (fun t k hmem => h t k (le_antisymm hmem.2 hmem.1))
  intro s t
  have := hmain s t
  linarith

/-- **An integer winding increment of a function avoiding a lattice vanishes.** -/
theorem int_eq_zero_of_notMem_lattice {f : ℝ → ℝ} (hf : Continuous f) {a : ℝ} {m : ℤ}
    (h : ∀ t : ℝ, ∀ k : ℤ, f t ≠ a + (k : ℝ) * (2 * Real.pi))
    (hdiff : f (2 * Real.pi) - f 0 = (m : ℝ) * (2 * Real.pi)) : m = 0 := by
  have hb := abs_sub_lt_two_pi_of_notMem_lattice hf h 0 (2 * Real.pi)
  rw [hdiff] at hb
  exact Work.BoxShrink.Bubble.cex_int_eq_zero_of_abs_mul_two_pi_lt (le_refl _) hb

/-! ## The box in coordinates -/

/-- **The box of the configuration in coordinates.** -/
theorem mem_PBox_tangent (y : R3) :
    y ∈ Submission.PBox tangentRad tangentCtr tangentCyc3 ↔
      |y 1| < tangentRad ∧ |y 2| < (2 : ℝ) ^ (1 / 3 : ℝ) * tangentRad ∧
        |y 0 - 1| < (2 : ℝ) ^ (2 / 3 : ℝ) * tangentRad := by
  rw [Submission.mem_PBox]
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2

/-- **The box norm of the configuration in coordinates.** -/
theorem boxNorm_tangent (y : R3) :
    Submission.boxNorm tangentCtr tangentCyc3 y =
      max (max |y 1| (|y 2| / (2 : ℝ) ^ (1 / 3 : ℝ)))
        (|y 0 - 1| / (2 : ℝ) ^ (2 / 3 : ℝ)) := by
  rw [Submission.boxNorm, tangentCyc3_zero, tangentCyc3_one, tangentCyc3_two,
    tangentCtr_one, tangentCtr_two, tangentCtr_zero, Submission.boxSide_zero,
    Submission.boxSide_one, Submission.boxSide_two]
  simp

/-! ## Numeric bounds -/

theorem tangent_rad_pos : (0 : ℝ) < tangentRad := by norm_num [tangentRad]

/-- `1 < (13/10) · 2^{1/3}`: the `z`-direction of the box is longer than the whole diameter of
the torus in that direction, so the `z`-coordinate never attains the box norm on the torus. -/
theorem one_lt_rpow_one_third_mul : (1 : ℝ) < (2 : ℝ) ^ (1 / 3 : ℝ) * tangentRad := by
  have h : (10 / 13 : ℝ) < (2 : ℝ) ^ (1 / 3 : ℝ) := by
    have hcube : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 2 := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (1 / 3 : ℝ)) 3,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hlt : (10 / 13 : ℝ) ^ 3 < ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 := by
      rw [hcube]; norm_num
    exact lt_of_pow_lt_pow_left₀ 3 (by positivity) hlt
  rw [tangentRad]
  nlinarith [h]

/-- `2 < (13/10) · 2^{2/3}`: the `x`-face of the box is far enough from the centre. -/
theorem two_lt_rpow_two_thirds_mul : (2 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) * tangentRad := by
  have h : (20 / 13 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) := by
    have hcube : ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = 4 := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (2 / 3 : ℝ)) 3,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hlt : (20 / 13 : ℝ) ^ 3 < ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 := by
      rw [hcube]; norm_num
    exact lt_of_pow_lt_pow_left₀ 3 (by positivity) hlt
  rw [tangentRad]
  nlinarith [h]

/-- `(13/10) · 2^{2/3} - 1 > 1.05`: the offset of the `x`-face `{x = 1 - a}` of the box from the
centre exceeds `1.05`. -/
theorem rpow_two_thirds_mul_sub_one_gt :
    (105 / 100 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) * tangentRad - 1 := by
  have h : (41 / 26 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) := by
    have hcube : ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = 4 := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (2 / 3 : ℝ)) 3,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hlt : (41 / 26 : ℝ) ^ 3 < ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 := by
      rw [hcube]; norm_num
    exact lt_of_pow_lt_pow_left₀ 3 (by positivity) hlt
  rw [tangentRad]
  nlinarith [h]

/-- `(13/10) · 2^{2/3} < 2.1`: the `x`-face of the box is not further than `2.1` from the
centre. -/
theorem rpow_two_thirds_mul_lt : (2 : ℝ) ^ (2 / 3 : ℝ) * tangentRad < 21 / 10 := by
  have h : (2 : ℝ) ^ (2 / 3 : ℝ) < 21 / 13 := by
    have hcube : ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = 4 := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (2 / 3 : ℝ)) 3,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hlt : ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 < (21 / 13 : ℝ) ^ 3 := by
      rw [hcube]; norm_num
    exact lt_of_pow_lt_pow_left₀ 3 (by norm_num) hlt
  rw [tangentRad]
  nlinarith [h]

/-- The `x`-coordinate of a point of the standard torus is at most `3`. -/
theorem torusMap_zero_le_three (u v : ℝ) : (Work.Core.torusMap u v) 0 ≤ 3 := by
  rw [Work.CoreTopology.torusMap_apply_zero]
  have h1 : Real.cos v ≤ 1 := Real.cos_le_one v
  have h2 : Real.cos u ≤ 1 := Real.cos_le_one u
  have h3 : -1 ≤ Real.cos u := Real.neg_one_le_cos u
  have h4 : -1 ≤ Real.cos v := Real.neg_one_le_cos v
  nlinarith

/-! ## The shape lemma for the box sphere -/

/-- **The box sphere of the configuration confines the parameters of a point of the torus.**

For `ψ u v` on the sphere `{boxNorm = 13/10}`: either `y₁ = (2+cos v) sin u` attains the box norm
(and then `2 + cos v ≥ 13/10` and `|sin u| ≥ 13/30`), or `x = (2+cos v) cos u` does (and then
`2 + cos v ≥ (13/10)·2^{2/3} - 1 > 1.05` and `cos u < 0`).  Both cases give `cos v > -0.95`, and
both give `cos (u - π) > -0.92`. -/
theorem sphereSet_shape {u v : ℝ}
    (h : Work.Core.torusMap u v ∈
      Work.BoxShrink.Core.sphereSet tangentCtr tangentCyc3 tangentRad) :
    (-0.95 : ℝ) < Real.cos v ∧ (-0.92 : ℝ) < Real.cos (u - Real.pi) := by
  have hbn : Submission.boxNorm tangentCtr tangentCyc3 (Work.Core.torusMap u v) = tangentRad := h
  have hmain : max (max |(Work.Core.torusMap u v) 1|
      (|(Work.Core.torusMap u v) 2| / (2 : ℝ) ^ (1 / 3 : ℝ)))
      (|(Work.Core.torusMap u v) 0 - 1| / (2 : ℝ) ^ (2 / 3 : ℝ)) = 13 / 10 := by
    have h := hbn
    rw [boxNorm_tangent, tangentRad_eq] at h
    exact h
  have hx0 : (Work.Core.torusMap u v) 0 = (2 + Real.cos v) * Real.cos u :=
    Work.CoreTopology.torusMap_apply_zero u v
  have hy1 : (Work.Core.torusMap u v) 1 = (2 + Real.cos v) * Real.sin u :=
    Work.CoreTopology.torusMap_apply_one u v
  have hρ1 : (1 : ℝ) ≤ 2 + Real.cos v := by linarith [Real.neg_one_le_cos v]
  have hρ3 : 2 + Real.cos v ≤ 3 := by linarith [Real.cos_le_one v]
  have hsin : |Real.sin u| ≤ 1 := Real.abs_sin_le_one u
  have hcos : |Real.cos u| ≤ 1 := Real.abs_cos_le_one u
  have hz_lt : |(Work.Core.torusMap u v) 2| / (2 : ℝ) ^ (1 / 3 : ℝ) < 13 / 10 := by
    rw [Work.CoreTopology.torusMap_apply_two]
    have hle : |Real.sin v| ≤ 1 := Real.abs_sin_le_one v
    have hp : (0 : ℝ) < (2 : ℝ) ^ (1 / 3 : ℝ) := by positivity
    have h1 : (1 : ℝ) < (2 : ℝ) ^ (1 / 3 : ℝ) * tangentRad := one_lt_rpow_one_third_mul
    rw [tangentRad_eq] at h1
    rw [div_lt_iff₀ hp]
    nlinarith
  have hA_le : |(Work.Core.torusMap u v) 1| ≤ 13 / 10 := by
    calc |(Work.Core.torusMap u v) 1|
        ≤ max (max |(Work.Core.torusMap u v) 1|
            (|(Work.Core.torusMap u v) 2| / (2 : ℝ) ^ (1 / 3 : ℝ)))
            (|(Work.Core.torusMap u v) 0 - 1| / (2 : ℝ) ^ (2 / 3 : ℝ)) :=
          le_trans (le_max_left _ _) (le_max_left _ _)
      _ = 13 / 10 := hmain
  have hC_le : |(Work.Core.torusMap u v) 0 - 1| / (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 13 / 10 := by
    calc |(Work.Core.torusMap u v) 0 - 1| / (2 : ℝ) ^ (2 / 3 : ℝ)
        ≤ max (max |(Work.Core.torusMap u v) 1|
            (|(Work.Core.torusMap u v) 2| / (2 : ℝ) ^ (1 / 3 : ℝ)))
            (|(Work.Core.torusMap u v) 0 - 1| / (2 : ℝ) ^ (2 / 3 : ℝ)) := le_max_right _ _
      _ = 13 / 10 := hmain
  have hcase : |(Work.Core.torusMap u v) 1| = 13 / 10 ∨
      |(Work.Core.torusMap u v) 0 - 1| / (2 : ℝ) ^ (2 / 3 : ℝ) = 13 / 10 := by
    by_contra hc
    push_neg at hc
    have hlt : max (max |(Work.Core.torusMap u v) 1|
        (|(Work.Core.torusMap u v) 2| / (2 : ℝ) ^ (1 / 3 : ℝ)))
        (|(Work.Core.torusMap u v) 0 - 1| / (2 : ℝ) ^ (2 / 3 : ℝ)) < 13 / 10 :=
      max_lt (max_lt (lt_of_le_of_ne hA_le hc.1) hz_lt) (lt_of_le_of_ne hC_le hc.2)
    rw [hmain] at hlt
    exact lt_irrefl _ hlt
  -- the `y`-case
  have hy_eq (hA : |(Work.Core.torusMap u v) 1| = 13 / 10) :
      (2 + Real.cos v) * |Real.sin u| = 13 / 10 := by
    have h1 : |(2 + Real.cos v) * Real.sin u| = 13 / 10 := by rw [← hy1]; exact hA
    rwa [abs_mul, abs_of_nonneg (by linarith)] at h1
  have hsin_ge_of (hA : |(Work.Core.torusMap u v) 1| = 13 / 10) :
      (13 : ℝ) / 30 ≤ |Real.sin u| := by
    have hy := hy_eq hA
    nlinarith [hy, hρ1, hρ3, abs_nonneg (Real.sin u)]
  -- the `x`-case
  have hxval_of (hC : |(Work.Core.torusMap u v) 0 - 1| / (2 : ℝ) ^ (2 / 3 : ℝ) = 13 / 10) :
      (Work.Core.torusMap u v) 0 = 1 - (2 : ℝ) ^ (2 / 3 : ℝ) * (13 / 10) := by
    have hp : (0 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) := by positivity
    have hx : |(Work.Core.torusMap u v) 0 - 1| = (2 : ℝ) ^ (2 / 3 : ℝ) * (13 / 10) := by
      rw [div_eq_iff (ne_of_gt hp)] at hC
      linarith [hC]
    have hxle : (Work.Core.torusMap u v) 0 - 1 ≤ 2 := by
      have := torusMap_zero_le_three u v
      linarith
    have hgt : (2 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) * (13 / 10) := by
      have := two_lt_rpow_two_thirds_mul
      rw [tangentRad_eq] at this
      linarith
    rcases abs_cases ((Work.Core.torusMap u v) 0 - 1) with h1 | h1
    · rw [h1.1] at hx; linarith
    · rw [h1.1] at hx; linarith
  have hR_gt_one : (1 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) * (13 / 10) := by
    have := two_lt_rpow_two_thirds_mul
    rw [tangentRad_eq] at this
    linarith
  have hρ_ge_of (hC : |(Work.Core.torusMap u v) 0 - 1| / (2 : ℝ) ^ (2 / 3 : ℝ) = 13 / 10) :
      (2 : ℝ) ^ (2 / 3 : ℝ) * (13 / 10) - 1 ≤ 2 + Real.cos v := by
    have hxval := hxval_of hC
    have h1 : (2 + Real.cos v) * Real.cos u = 1 - (2 : ℝ) ^ (2 / 3 : ℝ) * (13 / 10) := by
      rw [← hx0]
      linarith [hxval]
    have h2 : |(2 + Real.cos v) * Real.cos u| = (2 : ℝ) ^ (2 / 3 : ℝ) * (13 / 10) - 1 := by
      rw [h1, abs_of_neg (by linarith [hR_gt_one])]
      ring
    have h3 : (2 + Real.cos v) * |Real.cos u| = (2 : ℝ) ^ (2 / 3 : ℝ) * (13 / 10) - 1 := by
      rw [abs_mul, abs_of_nonneg (by linarith)] at h2
      exact h2
    nlinarith [h3, hcos, hρ1, abs_nonneg (Real.cos u)]
  have hcosu_neg_of (hC : |(Work.Core.torusMap u v) 0 - 1| / (2 : ℝ) ^ (2 / 3 : ℝ) = 13 / 10) :
      Real.cos u < 0 := by
    have hxval := hxval_of hC
    have h1 : (2 + Real.cos v) * Real.cos u = 1 - (2 : ℝ) ^ (2 / 3 : ℝ) * (13 / 10) := by
      rw [← hx0]
      linarith [hxval]
    have hρ1' : (0 : ℝ) < 2 + Real.cos v := by linarith
    nlinarith [h1, hρ1', hR_gt_one]
  have hcospi : Real.cos (u - Real.pi) = -Real.cos u := by
    rw [show u - Real.pi = -(Real.pi - u) by ring, Real.cos_neg, Real.cos_pi_sub]
  have hcu_A (hA : |(Work.Core.torusMap u v) 1| = 13 / 10) :
      (-0.92 : ℝ) < Real.cos (u - Real.pi) := by
    have hsin_ge := hsin_ge_of hA
    have hsq : (Real.sin u) ^ 2 ≥ (13 / 30 : ℝ) ^ 2 := by
      have h0 : (0 : ℝ) ≤ |Real.sin u| := abs_nonneg _
      have h1 : |Real.sin u| ^ 2 = (Real.sin u) ^ 2 := sq_abs _
      nlinarith [hsin_ge, h0, h1]
    have hcos2 : (Real.cos u) ^ 2 < (0.92 : ℝ) ^ 2 := by
      have h1 : Real.sin u ^ 2 + Real.cos u ^ 2 = 1 := Real.sin_sq_add_cos_sq u
      nlinarith
    have hlt : |Real.cos u| < 0.92 := by
      have h2 : |Real.cos u| ^ 2 < (0.92 : ℝ) ^ 2 := by rw [sq_abs]; exact hcos2
      nlinarith [h2, abs_nonneg (Real.cos u)]
    rw [hcospi]
    linarith [le_abs_self (Real.cos u), hlt]
  have hcu_C (hC : |(Work.Core.torusMap u v) 0 - 1| / (2 : ℝ) ^ (2 / 3 : ℝ) = 13 / 10) :
      (-0.92 : ℝ) < Real.cos (u - Real.pi) := by
    have hneg := hcosu_neg_of hC
    rw [hcospi]
    linarith
  have hcv_A (hA : |(Work.Core.torusMap u v) 1| = 13 / 10) : (-0.95 : ℝ) < Real.cos v := by
    have hy := hy_eq hA
    nlinarith [hy, hsin, hρ1]
  have hcv_C (hC : |(Work.Core.torusMap u v) 0 - 1| / (2 : ℝ) ^ (2 / 3 : ℝ) = 13 / 10) :
      (-0.95 : ℝ) < Real.cos v := by
    have hρge := hρ_ge_of hC
    have hbig := rpow_two_thirds_mul_sub_one_gt
    rw [tangentRad_eq] at hbig
    linarith
  rcases hcase with hA | hC
  · exact ⟨hcv_A hA, hcu_A hA⟩
  · exact ⟨hcv_C hC, hcu_C hC⟩

/-! ## The shape lemmas for the slice and the two half-regions -/

/-- **The slice of the configuration confines the parameters of its points.**  A point `ψ u v` of
the slice (the trace of the plane `{x = 1}` inside the box) has `cos u > 0` — indeed
`(2 + cos v) cos u = 1` — and `cos (v - π) > 0`, since `(2 + cos v)² = 1 + y₁² < 2.69 < 4`. -/
theorem sliceRegion_shape {u v : ℝ}
    (h : Work.Core.torusMap u v ∈ Work.BoxShrink.Core.sliceRegion Work.CoreTopology.standard
      tangentRad tangentCtr tangentCyc3 0) :
    0 < Real.cos u ∧ 0 < Real.cos (v - Real.pi) := by
  obtain ⟨-, hbox, hy0⟩ := (Work.BoxShrink.Core.mem_sliceRegion).mp h
  have hy1_lt : |(Work.Core.torusMap u v) 1| < tangentRad := ((mem_PBox_tangent _).mp hbox).1
  have hx0 : (Work.Core.torusMap u v) 0 = (2 + Real.cos v) * Real.cos u :=
    Work.CoreTopology.torusMap_apply_zero u v
  have hy1 : (Work.Core.torusMap u v) 1 = (2 + Real.cos v) * Real.sin u :=
    Work.CoreTopology.torusMap_apply_one u v
  have hρpos : (0 : ℝ) < 2 + Real.cos v := by linarith [Real.neg_one_le_cos v]
  have hx : (2 + Real.cos v) * Real.cos u = 1 := by rw [← hx0]; simpa using hy0
  have hcosu : 0 < Real.cos u := by nlinarith [hx, hρpos]
  have hρsq : (2 + Real.cos v) ^ 2 < 4 := by
    have h1 : ((Work.Core.torusMap u v) 1) ^ 2 < (13 / 10 : ℝ) ^ 2 := by
      have h2 : |(Work.Core.torusMap u v) 1| < 13 / 10 := by rwa [tangentRad_eq] at hy1_lt
      nlinarith [h2, abs_nonneg ((Work.Core.torusMap u v) 1),
        sq_abs ((Work.Core.torusMap u v) 1)]
    have h2 : ((Work.Core.torusMap u v) 1) ^ 2 = ((2 + Real.cos v) * Real.sin u) ^ 2 := by
      rw [hy1]
    have h3 : Real.sin u ^ 2 + Real.cos u ^ 2 = 1 := Real.sin_sq_add_cos_sq u
    nlinarith [h1, h2, h3, hx]
  have hcospi : Real.cos (v - Real.pi) = -Real.cos v := by
    rw [show v - Real.pi = -(Real.pi - v) by ring, Real.cos_neg, Real.cos_pi_sub]
  exact ⟨hcosu, by rw [hcospi]; nlinarith [hρsq, hρpos]⟩

/-- **The upper half-region confines the parameters of its points**: `x = (2+cos v) cos u > 1`
gives `cos u > 0`, and `v ≡ π` is impossible (it would force `x = cos u ≤ 1`). -/
theorem upperRegion_shape {u v : ℝ}
    (h : Work.Core.torusMap u v ∈ Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard
      tangentRad tangentCtr tangentCyc3 0) :
    0 < Real.cos u ∧ ∀ k : ℤ, v ≠ Real.pi + (k : ℝ) * (2 * Real.pi) := by
  obtain ⟨-, -, hy0⟩ := (Work.BoxShrink.Core.mem_upperRegion).mp h
  have hy0' : (1 : ℝ) < (Work.Core.torusMap u v) 0 := by simpa using hy0
  have hx0 : (Work.Core.torusMap u v) 0 = (2 + Real.cos v) * Real.cos u :=
    Work.CoreTopology.torusMap_apply_zero u v
  have hρpos : (0 : ℝ) < 2 + Real.cos v := by linarith [Real.neg_one_le_cos v]
  have hx : (2 + Real.cos v) * Real.cos u = (Work.Core.torusMap u v) 0 := hx0.symm
  have hcosu : 0 < Real.cos u := by nlinarith [hx, hρpos, hy0']
  have hlattice : ∀ k : ℤ, v ≠ Real.pi + (k : ℝ) * (2 * Real.pi) := by
    intro k hv
    have hcv : Real.cos v = -1 := by
      rw [hv, Real.cos_add_int_mul_two_pi, Real.cos_pi]
    have hρ : (2 + Real.cos v) = 1 := by linarith
    have hx1 : (Work.Core.torusMap u v) 0 = Real.cos u := by rw [hx0, hρ, one_mul]
    nlinarith [hy0', hx1, Real.cos_le_one u]
  exact ⟨hcosu, hlattice⟩

/-- **The lower half-region confines the parameters of its points.**  Here `x = (2+cos v) cos u < 1`
and `|x - 1| < (13/10)·2^{2/3}` bound `|x| < 1.07`, while `|y₁| < 1.3`; hence
`(2 + cos v)² = x² + y₁² < 4`, so `2 + cos v < 2` and `cos (v - π) > 0`.  Moreover `u ≡ 0` is
impossible (it would force `x = 2 + cos v ≥ 1`). -/
theorem lowerRegion_shape {u v : ℝ}
    (h : Work.Core.torusMap u v ∈ Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard
      tangentRad tangentCtr tangentCyc3 0) :
    0 < Real.cos (v - Real.pi) ∧ ∀ k : ℤ, u ≠ (k : ℝ) * (2 * Real.pi) := by
  obtain ⟨-, hbox, hy0⟩ := (Work.BoxShrink.Core.mem_lowerRegion).mp h
  have hbox' := (mem_PBox_tangent _).mp hbox
  have hy1_lt : |(Work.Core.torusMap u v) 1| < tangentRad := hbox'.1
  have hx_lt : |(Work.Core.torusMap u v) 0 - 1| < (2 : ℝ) ^ (2 / 3 : ℝ) * tangentRad := hbox'.2.2
  have hy0' : (Work.Core.torusMap u v) 0 < 1 := by simpa using hy0
  have hx0 : (Work.Core.torusMap u v) 0 = (2 + Real.cos v) * Real.cos u :=
    Work.CoreTopology.torusMap_apply_zero u v
  have hy1 : (Work.Core.torusMap u v) 1 = (2 + Real.cos v) * Real.sin u :=
    Work.CoreTopology.torusMap_apply_one u v
  have hρpos : (0 : ℝ) < 2 + Real.cos v := by linarith [Real.neg_one_le_cos v]
  have hxabs : |(Work.Core.torusMap u v) 0| < 1.1 := by
    have hR := rpow_two_thirds_mul_lt
    have hlow : (1 : ℝ) - (2 : ℝ) ^ (2 / 3 : ℝ) * tangentRad < (Work.Core.torusMap u v) 0 := by
      rw [abs_lt] at hx_lt
      linarith [hx_lt.1]
    rw [abs_lt]
    constructor <;> linarith
  have hy1abs : |(Work.Core.torusMap u v) 1| < 1.3 := by
    rw [tangentRad_eq] at hy1_lt
    linarith
  have hρsq : (2 + Real.cos v) ^ 2 < 4 := by
    have h1 : (2 + Real.cos v) ^ 2 =
        ((Work.Core.torusMap u v) 0) ^ 2 + ((Work.Core.torusMap u v) 1) ^ 2 := by
      rw [hx0, hy1]
      have h3 : Real.sin u ^ 2 + Real.cos u ^ 2 = 1 := Real.sin_sq_add_cos_sq u
      nlinarith [h3]
    rw [h1]
    nlinarith [hxabs, hy1abs, sq_abs ((Work.Core.torusMap u v) 0),
      sq_abs ((Work.Core.torusMap u v) 1), abs_nonneg ((Work.Core.torusMap u v) 0),
      abs_nonneg ((Work.Core.torusMap u v) 1)]
  have hcospi : Real.cos (v - Real.pi) = -Real.cos v := by
    rw [show v - Real.pi = -(Real.pi - v) by ring, Real.cos_neg, Real.cos_pi_sub]
  have hcosv : 0 < Real.cos (v - Real.pi) := by
    rw [hcospi]
    nlinarith [hρsq, hρpos]
  have hlattice : ∀ k : ℤ, u ≠ (k : ℝ) * (2 * Real.pi) := by
    intro k hu
    have hcu : Real.cos u = 1 := by rw [hu, Real.cos_int_mul_two_pi]
    have hx : (2 + Real.cos v) * Real.cos u = (Work.Core.torusMap u v) 0 := hx0.symm
    have hρ1 : (1 : ℝ) ≤ 2 + Real.cos v := by linarith [Real.neg_one_le_cos v]
    nlinarith [hx, hcu, hy0', hρ1]
  exact ⟨hcosv, hlattice⟩

end

end Work.BoxShrink.PinchOff
