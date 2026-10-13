/-
# The weighted bound for the `D_z`-iterates of the radial profile `2z²/(1+z)³`

This module proves that the weighted `D_z`-iterates of the radial profile
`bcoefRad z = 2z²/(1+z)³` of the projector coefficient are bounded by `120/(1+z)`:

`|(Zop^[j] bcoefRad) z · w z| ≤ 120/(1+z)` for `j ≤ 3`, `z ≥ 0`,

where `w z = (1+z)²/z²` is the radial weight and `Zop u z = z·u'(z)`.

The computation is explicit: `Zop^j (2z²/(1+z)³) = 2z²·P_j(z)/(1+z)^(3+j)` with

`P_0 = 1`, `P_1 = 2-z`, `P_2 = z²-7z+4`, `P_3 = -z³+18z²-33z+8`

(so that, after multiplying by `w(1+z)`, the quotients are `2P_j(z)/(1+z)^j`), and each
`|P_j(z)|` is bounded on `z ≥ 0` by the sum of its coefficients times `(1+z)^j`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefPrep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Aux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary bounds for monic polynomials on `z ≥ 0` -/

lemma abs_le_lin (z b : ℝ) (hz : 0 ≤ z) : |z + b| ≤ (1 + |b|) * (1 + z) := by
  have h1 : |z| ≤ 1 + z := by rw [abs_of_nonneg hz]; linarith
  have h2 : (1 : ℝ) ≤ 1 + z := by linarith
  have hb : |b| ≤ |b| * (1 + z) := by
    have := mul_le_mul_of_nonneg_left h2 (abs_nonneg b)
    linarith
  calc |z + b| ≤ |z| + |b| := abs_add_le _ _
    _ ≤ (1 + |b|) * (1 + z) := by linarith

lemma abs_le_quad (z b c : ℝ) (hz : 0 ≤ z) :
    |z ^ 2 + b * z + c| ≤ (1 + |b| + |c|) * (1 + z) ^ 2 := by
  have hz' : |z| = z := abs_of_nonneg hz
  have h1z : (1 : ℝ) ≤ 1 + z := by linarith
  have h2 : (1 : ℝ) ≤ (1 + z) ^ 2 := one_le_pow₀ h1z
  have hz2 : |z| ^ 2 ≤ (1 + z) ^ 2 := by
    rw [hz']; exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hz1 : |z| ≤ (1 + z) ^ 2 := by rw [hz']; nlinarith
  have h3 : |z ^ 2 + b * z + c| ≤ |z ^ 2| + |b * z| + |c| := by
    have h := abs_add_le (z ^ 2 + b * z) c
    have h' := abs_add_le (z ^ 2) (b * z)
    linarith
  have h4 : |z ^ 2| + |b * z| + |c| = |z| ^ 2 + |b| * |z| + |c| := by
    rw [abs_pow, abs_mul]
  have hb : |b| * |z| ≤ |b| * (1 + z) ^ 2 := mul_le_mul_of_nonneg_left hz1 (abs_nonneg b)
  have hc : |c| ≤ |c| * (1 + z) ^ 2 := by
    have := mul_le_mul_of_nonneg_left h2 (abs_nonneg c)
    linarith
  have hmain : |z| ^ 2 + |b| * |z| + |c| ≤ (1 + |b| + |c|) * (1 + z) ^ 2 := by
    nlinarith [hz2, hb, hc, h2, abs_nonneg b, abs_nonneg c]
  calc |z ^ 2 + b * z + c| ≤ |z ^ 2| + |b * z| + |c| := h3
    _ = |z| ^ 2 + |b| * |z| + |c| := h4
    _ ≤ (1 + |b| + |c|) * (1 + z) ^ 2 := hmain

lemma abs_le_cubic (z b c d : ℝ) (hz : 0 ≤ z) :
    |z ^ 3 + b * z ^ 2 + c * z + d| ≤ (1 + |b| + |c| + |d|) * (1 + z) ^ 3 := by
  have hz' : |z| = z := abs_of_nonneg hz
  have h1z : (1 : ℝ) ≤ 1 + z := by linarith
  have h3 : (1 : ℝ) ≤ (1 + z) ^ 3 := one_le_pow₀ h1z
  have hz3 : |z| ^ 3 ≤ (1 + z) ^ 3 := by
    rw [hz']; exact pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hz2 : |z| ^ 2 ≤ (1 + z) ^ 3 := by
    rw [hz']
    have h : z ^ 2 ≤ (1 + z) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h' : (1 + z) ^ 2 ≤ (1 + z) ^ 3 := by nlinarith [h3, h1z]
    linarith
  have hz1 : |z| ≤ (1 + z) ^ 3 := by rw [hz']; nlinarith [h3, hz]
  have h5 : |z ^ 3 + b * z ^ 2 + c * z + d|
      ≤ |z ^ 3| + |b * z ^ 2| + |c * z| + |d| := by
    have h := abs_add_le (z ^ 3 + b * z ^ 2 + c * z) d
    have h' := abs_add_le (z ^ 3 + b * z ^ 2) (c * z)
    have h'' := abs_add_le (z ^ 3) (b * z ^ 2)
    linarith
  have h6 : |z ^ 3| + |b * z ^ 2| + |c * z| + |d|
      = |z| ^ 3 + |b| * |z| ^ 2 + |c| * |z| + |d| := by
    rw [abs_pow, abs_mul, abs_pow, abs_mul]
  have hb : |b| * |z| ^ 2 ≤ |b| * (1 + z) ^ 3 := mul_le_mul_of_nonneg_left hz2 (abs_nonneg b)
  have hc : |c| * |z| ≤ |c| * (1 + z) ^ 3 := mul_le_mul_of_nonneg_left hz1 (abs_nonneg c)
  have hd : |d| ≤ |d| * (1 + z) ^ 3 := by
    have := mul_le_mul_of_nonneg_left h3 (abs_nonneg d)
    linarith
  have hmain : |z| ^ 3 + |b| * |z| ^ 2 + |c| * |z| + |d|
      ≤ (1 + |b| + |c| + |d|) * (1 + z) ^ 3 := by
    nlinarith [hz3, hb, hc, hd, h3, abs_nonneg b, abs_nonneg c, abs_nonneg d]
  calc |z ^ 3 + b * z ^ 2 + c * z + d| ≤ |z ^ 3| + |b * z ^ 2| + |c * z| + |d| := h5
    _ = |z| ^ 3 + |b| * |z| ^ 2 + |c| * |z| + |d| := h6
    _ ≤ (1 + |b| + |c| + |d|) * (1 + z) ^ 3 := hmain

/-! ## The derivatives of the rational profiles -/

lemma deriv1 (z : ℝ) (hz : z ≠ -1) :
    HasDerivAt (fun y : ℝ => 2 * y ^ 2 / (1 + y) ^ 3) (2 * z * (2 - z) / (1 + z) ^ 4) z := by
  have hdenne : (1 + z) ^ 3 ≠ 0 := by
    intro h
    exact hz (by have := pow_eq_zero_iff (by norm_num : 3 ≠ 0) |>.mp h; linarith)
  have hnum : HasDerivAt (fun y : ℝ => 2 * y ^ 2) (4 * z) z := by
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by
      have h := (hasDerivAt_id z).pow 2
      have hfun : (id : ℝ → ℝ) ^ 2 = fun y : ℝ => y ^ 2 := by funext y; simp
      rw [hfun] at h
      convert h using 1
      simp
    have h2 := h1.const_mul (2 : ℝ)
    convert h2 using 1
    ring
  have hden : HasDerivAt (fun y : ℝ => (1 + y) ^ 3) (3 * (1 + z) ^ 2) z := by
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 z := (hasDerivAt_id z).const_add (1 : ℝ)
    have h2 := h1.pow 3
    have hfun : ((fun y : ℝ => 1 + y) ^ 3) = fun y : ℝ => (1 + y) ^ 3 := by funext y; simp
    rw [hfun] at h2
    convert h2 using 1
    ring
  have h := hnum.div hden hdenne
  have hval : (4 * z * (1 + z) ^ 3 - 2 * z ^ 2 * (3 * (1 + z) ^ 2)) / ((1 + z) ^ 3) ^ 2
      = 2 * z * (2 - z) / (1 + z) ^ 4 := by
    field_simp
    ring
  rw [hval] at h
  exact h

lemma deriv2 (z : ℝ) (hz : z ≠ -1) :
    HasDerivAt (fun y : ℝ => 2 * y ^ 2 * (2 - y) / (1 + y) ^ 4)
      (2 * z * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5) z := by
  have hdenne : (1 + z) ^ 4 ≠ 0 := by
    intro h
    exact hz (by have := pow_eq_zero_iff (by norm_num : 4 ≠ 0) |>.mp h; linarith)
  have hnum : HasDerivAt (fun y : ℝ => 2 * y ^ 2 * (2 - y)) (8 * z - 6 * z ^ 2) z := by
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by
      have h := (hasDerivAt_id z).pow 2
      have hfun : (id : ℝ → ℝ) ^ 2 = fun y : ℝ => y ^ 2 := by funext y; simp
      rw [hfun] at h
      convert h using 1
      simp
    have h2 := h1.const_mul (2 : ℝ)
    have h3 : HasDerivAt (fun y : ℝ => 2 - y) (-1) z := by
      have h := (hasDerivAt_const (x := z) (2 : ℝ)).sub (hasDerivAt_id z)
      have hf : ((fun _ : ℝ => (2 : ℝ)) - id) = fun y : ℝ => 2 - y := by
        funext y; simp
      rw [hf] at h
      convert h using 1
      ring
    have h4 := h2.mul h3
    convert h4 using 1
    ring
  have hden : HasDerivAt (fun y : ℝ => (1 + y) ^ 4) (4 * (1 + z) ^ 3) z := by
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 z := (hasDerivAt_id z).const_add (1 : ℝ)
    have h2 := h1.pow 4
    have hfun : ((fun y : ℝ => 1 + y) ^ 4) = fun y : ℝ => (1 + y) ^ 4 := by funext y; simp
    rw [hfun] at h2
    convert h2 using 1
    ring
  have h := hnum.div hden hdenne
  have hval : ((8 * z - 6 * z ^ 2) * (1 + z) ^ 4 - 2 * z ^ 2 * (2 - z) * (4 * (1 + z) ^ 3))
        / ((1 + z) ^ 4) ^ 2 = 2 * z * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5 := by
    field_simp
    ring
  rw [hval] at h
  exact h

lemma deriv3 (z : ℝ) (hz : z ≠ -1) :
    HasDerivAt (fun y : ℝ => 2 * y ^ 2 * (y ^ 2 - 7 * y + 4) / (1 + y) ^ 5)
      (2 * z * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6) z := by
  have hdenne : (1 + z) ^ 5 ≠ 0 := by
    intro h
    exact hz (by have := pow_eq_zero_iff (by norm_num : 5 ≠ 0) |>.mp h; linarith)
  have hnum : HasDerivAt (fun y : ℝ => 2 * y ^ 2 * (y ^ 2 - 7 * y + 4))
      (8 * z ^ 3 - 42 * z ^ 2 + 16 * z) z := by
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by
      have h := (hasDerivAt_id z).pow 2
      have hfun : (id : ℝ → ℝ) ^ 2 = fun y : ℝ => y ^ 2 := by funext y; simp
      rw [hfun] at h
      convert h using 1
      simp
    have h2 := h1.const_mul (2 : ℝ)
    have hq : HasDerivAt (fun y : ℝ => y ^ 2 - 7 * y + 4) (2 * z - 7) z := by
      have h3 : HasDerivAt (fun y : ℝ => y ^ 2 - 7 * y) (2 * z - 7 * 1) z :=
        h1.sub ((hasDerivAt_id z).const_mul 7)
      have h4 := h3.add_const 4
      convert h4 using 1
      ring
    have h5 := h2.mul hq
    convert h5 using 1
    ring
  have hden : HasDerivAt (fun y : ℝ => (1 + y) ^ 5) (5 * (1 + z) ^ 4) z := by
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 z := (hasDerivAt_id z).const_add (1 : ℝ)
    have h2 := h1.pow 5
    have hfun : ((fun y : ℝ => 1 + y) ^ 5) = fun y : ℝ => (1 + y) ^ 5 := by funext y; simp
    rw [hfun] at h2
    convert h2 using 1
    ring
  have h := hnum.div hden hdenne
  have hval : ((8 * z ^ 3 - 42 * z ^ 2 + 16 * z) * (1 + z) ^ 5
        - 2 * z ^ 2 * (z ^ 2 - 7 * z + 4) * (5 * (1 + z) ^ 4)) / ((1 + z) ^ 5) ^ 2
      = 2 * z * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6 := by
    field_simp
    ring
  rw [hval] at h
  exact h

/-! ## The `Zop`-iterates of the radial profile -/

lemma Zop_one_eq {z : ℝ} (hz : -1 < z) :
    Work.Spaces.Zop bcoefRad z = 2 * z ^ 2 * (2 - z) / (1 + z) ^ 4 := by
  have hzne : z ≠ -1 := by linarith
  show z * deriv (fun y : ℝ => 2 * y ^ 2 / (1 + y) ^ 3) z
    = 2 * z ^ 2 * (2 - z) / (1 + z) ^ 4
  rw [(deriv1 z hzne).deriv]
  field_simp
  try ring

lemma Zop_two_eq {z : ℝ} (hz : -1 < z) :
    Work.Spaces.Zop^[2] bcoefRad z = 2 * z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5 := by
  have hzne : z ≠ -1 := by linarith
  have hev : Work.Spaces.Zop bcoefRad =ᶠ[𝓝 z]
      (fun y : ℝ => 2 * y ^ 2 * (2 - y) / (1 + y) ^ 4) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact Zop_one_eq hy
  change Work.Spaces.Zop (Work.Spaces.Zop bcoefRad) z
    = 2 * z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5
  show z * deriv (Work.Spaces.Zop bcoefRad) z
    = 2 * z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5
  rw [hev.deriv_eq, (deriv2 z hzne).deriv]
  field_simp
  try ring

lemma Zop_three_eq {z : ℝ} (hz : -1 < z) :
    Work.Spaces.Zop^[3] bcoefRad z
      = 2 * z ^ 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6 := by
  have hzne : z ≠ -1 := by linarith
  have hev : Work.Spaces.Zop^[2] bcoefRad =ᶠ[𝓝 z]
      (fun y : ℝ => 2 * y ^ 2 * (y ^ 2 - 7 * y + 4) / (1 + y) ^ 5) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact Zop_two_eq hy
  change Work.Spaces.Zop (Work.Spaces.Zop^[2] bcoefRad) z
    = 2 * z ^ 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6
  show z * deriv (Work.Spaces.Zop^[2] bcoefRad) z
    = 2 * z ^ 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6
  rw [hev.deriv_eq, (deriv3 z hzne).deriv]
  field_simp
  try ring

/-! ## The weighted bound -/

/-- **The weighted `D_z`-iterates of `2z²/(1+z)³` are bounded by `120/(1+z)`.** -/
theorem bcoefRad_zop_bound : ∃ K : ℝ, 0 < K ∧ ∀ (j : ℕ), j ≤ 3 → ∀ z ∈ Set.Ici (0 : ℝ),
      |(Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z| ≤ K / (1 + z) := by
  refine ⟨120, by norm_num, fun j hj z hz => ?_⟩
  have hz0 : (0 : ℝ) ≤ z := hz
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hw : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
  by_cases hz0' : z = 0
  · rw [hz0']
    have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
    rw [hw0, mul_zero, abs_zero]
    norm_num
  have hpos : 0 < z := lt_of_le_of_ne hz0 (Ne.symm hz0')
  have hzIoi : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  rw [hw, le_div_iff₀ h1z]
  interval_cases j
  · -- `j = 0`
    show |bcoefRad z * ((1 + z) ^ 2 / z ^ 2)| * (1 + z) ≤ 120
    have hval : |bcoefRad z * ((1 + z) ^ 2 / z ^ 2)| * (1 + z) = 2 := by
      have hAB : bcoefRad z * ((1 + z) ^ 2 / z ^ 2) * (1 + z) = 2 := by
        rw [bcoefRad_eq]
        field_simp
        try ring
      calc |bcoefRad z * ((1 + z) ^ 2 / z ^ 2)| * (1 + z)
          = |bcoefRad z * ((1 + z) ^ 2 / z ^ 2)| * |1 + z| := by rw [abs_of_pos h1z]
        _ = |bcoefRad z * ((1 + z) ^ 2 / z ^ 2) * (1 + z)| := (abs_mul _ _).symm
        _ = |2| := by rw [hAB]
        _ = 2 := by norm_num
    rw [hval]
    norm_num
  · -- `j = 1`
    show |Work.Spaces.Zop bcoefRad z * ((1 + z) ^ 2 / z ^ 2)| * (1 + z) ≤ 120
    rw [Zop_one_eq hzIoi]
    have hAB : 2 * z ^ 2 * (2 - z) / (1 + z) ^ 4 * ((1 + z) ^ 2 / z ^ 2) * (1 + z)
        = 2 * (2 - z) / (1 + z) := by
      field_simp
      try ring
    calc |2 * z ^ 2 * (2 - z) / (1 + z) ^ 4 * ((1 + z) ^ 2 / z ^ 2)| * (1 + z)
        = |2 * z ^ 2 * (2 - z) / (1 + z) ^ 4 * ((1 + z) ^ 2 / z ^ 2)| * |1 + z| := by
          rw [abs_of_pos h1z]
      _ = |2 * z ^ 2 * (2 - z) / (1 + z) ^ 4 * ((1 + z) ^ 2 / z ^ 2) * (1 + z)| :=
          (abs_mul _ _).symm
      _ = |2 * (2 - z) / (1 + z)| := by rw [hAB]
      _ ≤ 120 := by
          rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos h1z]
          rw [div_le_iff₀ h1z]
          have hb : |2 - z| ≤ 3 * (1 + z) := by
            have h := abs_le_lin z (-2) hz0
            have he : z + (-2) = -(2 - z) := by ring
            rw [he, abs_neg] at h
            have h2 : (1 : ℝ) + |(-2 : ℝ)| = 3 := by norm_num
            rwa [h2] at h
          linarith [abs_nonneg (2 - z)]
  · -- `j = 2`
    show |Work.Spaces.Zop^[2] bcoefRad z * ((1 + z) ^ 2 / z ^ 2)| * (1 + z) ≤ 120
    rw [Zop_two_eq hzIoi]
    have hAB : 2 * z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5 * ((1 + z) ^ 2 / z ^ 2)
        * (1 + z) = 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 2 := by
      field_simp
      try ring
    calc |2 * z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5 * ((1 + z) ^ 2 / z ^ 2)| * (1 + z)
        = |2 * z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5 * ((1 + z) ^ 2 / z ^ 2)| * |1 + z| := by
          rw [abs_of_pos h1z]
      _ = |2 * z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5 * ((1 + z) ^ 2 / z ^ 2)
            * (1 + z)| := (abs_mul _ _).symm
      _ = |2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 2| := by rw [hAB]
      _ ≤ 120 := by
          rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
            abs_of_pos (pow_pos h1z 2)]
          rw [div_le_iff₀ (pow_pos h1z 2)]
          have hb : |z ^ 2 - 7 * z + 4| ≤ 12 * (1 + z) ^ 2 := by
            have h := abs_le_quad z (-7) 4 hz0
            have he : z ^ 2 + (-7) * z + 4 = z ^ 2 - 7 * z + 4 := by ring
            rw [he] at h
            have h2 : (1 : ℝ) + |(-7 : ℝ)| + |(4 : ℝ)| = 12 := by norm_num
            rwa [h2] at h
          linarith [abs_nonneg (z ^ 2 - 7 * z + 4)]
  · -- `j = 3`
    show |Work.Spaces.Zop^[3] bcoefRad z * ((1 + z) ^ 2 / z ^ 2)| * (1 + z) ≤ 120
    rw [Zop_three_eq hzIoi]
    have hAB : 2 * z ^ 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6
        * ((1 + z) ^ 2 / z ^ 2) * (1 + z)
        = 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 3 := by
      field_simp
      try ring
    calc |2 * z ^ 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6
          * ((1 + z) ^ 2 / z ^ 2)| * (1 + z)
        = |2 * z ^ 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6
            * ((1 + z) ^ 2 / z ^ 2)| * |1 + z| := by rw [abs_of_pos h1z]
      _ = |2 * z ^ 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6
            * ((1 + z) ^ 2 / z ^ 2) * (1 + z)| := (abs_mul _ _).symm
      _ = |2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 3| := by rw [hAB]
      _ ≤ 120 := by
          have he : 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8)
              = -(2 * (z ^ 3 - 18 * z ^ 2 + 33 * z - 8)) := by ring
          rw [he, abs_div, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
            abs_of_pos (pow_pos h1z 3)]
          rw [div_le_iff₀ (pow_pos h1z 3)]
          have hb : |z ^ 3 - 18 * z ^ 2 + 33 * z - 8| ≤ 60 * (1 + z) ^ 3 := by
            have h := abs_le_cubic z (-18) 33 (-8) hz0
            have he2 : z ^ 3 + (-18) * z ^ 2 + 33 * z + (-8)
                = z ^ 3 - 18 * z ^ 2 + 33 * z - 8 := by ring
            rw [he2] at h
            have h2 : (1 : ℝ) + |(-18 : ℝ)| + |(33 : ℝ)| + |(-8 : ℝ)| = 60 := by norm_num
            rwa [h2] at h
          linarith [abs_nonneg (z ^ 3 - 18 * z ^ 2 + 33 * z - 8)]

end Work.FTS.StrongPersist.L3Aux
