import Mathlib
import Submission.Work.Drive.encodedShear

/-!
# The twist of the level interval is a box self-map with a non-degenerate parameter

`Work.Drive.thetaS s x = x + clamp1 s * hb x` is the *twist* of the shear family of
`encodedShear.lean`, `clamp1 s = s / (2 √(1+s²))` being the clamped parameter (`|clamp1 s| ≤ 1/2`).

This file proves `Work.Drive.thetaS_props`:

* `thetaS s` maps `[0,1]` **bijectively** onto `[0,1]`, with the two ends of the interval fixed
  (`thetaS s x = 0 ↔ x = 0`, `thetaS s x = 1 ↔ x = 1` for `x ∈ [0,1]`);
* the parameter direction is nowhere degenerate: for every `x` with `hb x ≠ 0` the derivative of
  `s ↦ thetaS s x` is non-zero **everywhere** (the clamped parameter has strictly positive
  derivative everywhere, `d/ds clamp1 s = 1 / (2 (1+s²)^{3/2})`).

The estimates behind the first part are the elementary ones: writing `a = clamp1 s`, `|a| ≤ 1/2`
forces `0 < 1 + a * (1 - x - y)` for `x, y ∈ [0,1]`, whence strict monotonicity of `θ_s` on `[0,1]`
and the two factorisations `θ_s x = x * (1 + a (1-x))`, `1 - θ_s x = (1 - x) * (1 - a x)`.
-/

namespace Work.Drive

noncomputable section

/-! ## The size of the clamped parameter -/

/-- The clamped parameter lies in `[-1/2, 1/2]`: `|clamp1 s| = |s| / (2 √(1+s²)) ≤ 1/2`. -/
lemma abs_clamp1_le (s : ℝ) : |clamp1 s| ≤ 1 / 2 := by
  rw [clamp1, abs_mul, abs_of_nonneg (by positivity)]
  have hs : |s| ≤ Real.sqrt (1 + s ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs s]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_abs s]
  calc (2 * Real.sqrt (1 + s ^ 2))⁻¹ * |s|
      ≤ (2 * Real.sqrt (1 + s ^ 2))⁻¹ * Real.sqrt (1 + s ^ 2) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 1 / 2 := by
        rw [inv_mul_eq_div]
        field_simp

/-- `0 < 1 + a * b` as soon as `|a| ≤ 1/2` and `|b| ≤ 1`. -/
lemma one_add_mul_pos_of_abs_le_half {a b : ℝ} (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1) :
    0 < 1 + a * b := by
  have h : |a * b| ≤ 1 / 2 := by
    rw [abs_mul]
    calc |a| * |b| ≤ (1 / 2) * 1 := mul_le_mul ha hb (abs_nonneg b) (by norm_num)
      _ = 1 / 2 := by norm_num
  have := (abs_le.mp h).1
  linarith

/-! ## The twist, factored at the two ends of the interval -/

/-- `θ_s x = x (1 + a (1-x))` with `a = clamp1 s`. -/
lemma thetaS_eq_mul (s x : ℝ) : thetaS s x = x * (1 + clamp1 s * (1 - x)) := by
  unfold thetaS hb; ring

/-- `1 - θ_s x = (1-x) (1 - a x)` with `a = clamp1 s`. -/
lemma one_sub_thetaS (s x : ℝ) : 1 - thetaS s x = (1 - x) * (1 - clamp1 s * x) := by
  unfold thetaS hb; ring

/-- The difference `θ_s y - θ_s x = (y - x) (1 + a (1 - y - x))`. -/
lemma thetaS_sub (s x y : ℝ) :
    thetaS s y - thetaS s x = (y - x) * (1 + clamp1 s * (1 - y - x)) := by
  unfold thetaS hb; ring

/-- The twist is strictly monotone on the unit interval. -/
lemma thetaS_lt_thetaS (s : ℝ) {x y : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hy : y ∈ Set.Icc (0:ℝ) 1) (hxy : x < y) : thetaS s x < thetaS s y := by
  have hyx : |1 - y - x| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have h2 : 0 < 1 + clamp1 s * (1 - y - x) :=
    one_add_mul_pos_of_abs_le_half (abs_clamp1_le s) hyx
  have hprod : 0 < (y - x) * (1 + clamp1 s * (1 - y - x)) := mul_pos (sub_pos.mpr hxy) h2
  have h := thetaS_sub s y x
  linarith [h]

/-- The twist maps the unit interval into itself. -/
lemma thetaS_mem_Icc (s : ℝ) {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    thetaS s x ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · rw [thetaS_eq_mul]
    have : 0 < 1 + clamp1 s * (1 - x) :=
      one_add_mul_pos_of_abs_le_half (abs_clamp1_le s)
        (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2])
    exact mul_nonneg hx.1 (le_of_lt this)
  · rw [← sub_nonneg, one_sub_thetaS]
    have : 0 < 1 - clamp1 s * x := by
      have h : |clamp1 s * x| ≤ 1 / 2 := by
        rw [abs_mul]
        calc |clamp1 s| * |x| ≤ (1 / 2) * 1 :=
              mul_le_mul (abs_clamp1_le s)
                (by rw [abs_of_nonneg hx.1]; exact hx.2) (abs_nonneg x) (by norm_num)
          _ = 1 / 2 := by norm_num
      have := (abs_le.mp h).2
      linarith
    exact mul_nonneg (by linarith [hx.2]) (le_of_lt this)

/-- The twist is continuous. -/
lemma continuous_thetaS (s : ℝ) : Continuous (thetaS s) := by
  unfold thetaS hb
  fun_prop

/-! ## The parameter direction is non-degenerate everywhere -/

/-- `d/ds clamp1 s = 1 / (2 (1+s²)^{3/2}) > 0`. -/
lemma hasDerivAt_clamp1 (x : ℝ) :
    HasDerivAt clamp1 (1 / (2 * (1 + x ^ 2) * Real.sqrt (1 + x ^ 2))) x := by
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x := by
    have h := hasDerivAt_pow 2 x
    rw [show (↑(2:ℕ) : ℝ) * x ^ (2 - 1) = 2 * x by norm_num] at h
    exact h
  have h2 : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * x) x :=
    (hsq.const_add 1).congr_deriv (by ring)
  have h3 : HasDerivAt (fun s : ℝ => Real.sqrt (1 + s ^ 2))
      ((2 * x) / (2 * Real.sqrt (1 + x ^ 2))) x :=
    h2.sqrt (by positivity)
  have h4 : HasDerivAt (fun s : ℝ => (2 * Real.sqrt (1 + s ^ 2))⁻¹)
      (-(2 * ((2 * x) / (2 * Real.sqrt (1 + x ^ 2)))) / (2 * Real.sqrt (1 + x ^ 2)) ^ 2) x :=
    (h3.const_mul 2).inv (by positivity)
  have h5 : HasDerivAt (fun s : ℝ => (2 * Real.sqrt (1 + s ^ 2))⁻¹ * s)
      (-(2 * ((2 * x) / (2 * Real.sqrt (1 + x ^ 2)))) / (2 * Real.sqrt (1 + x ^ 2)) ^ 2 * x
        + (2 * Real.sqrt (1 + x ^ 2))⁻¹ * 1) x :=
    h4.mul (hasDerivAt_id x)
  unfold clamp1
  refine h5.congr_deriv ?_
  field_simp
  rw [Real.sq_sqrt (by positivity)]
  ring

/-- The clamped parameter has non-vanishing derivative everywhere. -/
lemma deriv_clamp1_ne_zero (x : ℝ) : deriv clamp1 x ≠ 0 := by
  rw [(hasDerivAt_clamp1 x).deriv]
  positivity

/-! ## The main statement -/

theorem thetaS_props (s : ℝ) :
    Set.BijOn (Work.Drive.thetaS s) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) ∧
    (∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
      (Work.Drive.thetaS s x = 0 ↔ x = 0) ∧ (Work.Drive.thetaS s x = 1 ↔ x = 1)) ∧
    (∀ x x₀ : ℝ, Work.Drive.hb x ≠ 0 →
      deriv (fun s' : ℝ => Work.Drive.thetaS s' x) x₀ ≠ 0) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact thetaS_mem_Icc s hx
    · intro x hx y hy hxy
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h := thetaS_lt_thetaS s hx hy hlt
        rw [hxy] at h
        exact lt_irrefl _ h
      · have h := thetaS_lt_thetaS s hy hx hgt
        rw [hxy] at h
        exact lt_irrefl _ h
    · intro y hy
      have hivt := intermediate_value_Icc (show (0:ℝ) ≤ 1 by norm_num)
        (continuous_thetaS s).continuousOn
      have hy' : y ∈ Set.Icc (thetaS s 0) (thetaS s 1) := by
        simpa [thetaS, hb] using hy
      obtain ⟨a, ha, hae⟩ := hivt hy'
      exact ⟨a, ha, hae⟩
  · intro x hx
    constructor
    · constructor
      · intro h
        rw [thetaS_eq_mul] at h
        have h1 : 1 + clamp1 s * (1 - x) ≠ 0 :=
          ne_of_gt (one_add_mul_pos_of_abs_le_half (abs_clamp1_le s)
            (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]))
        rcases mul_eq_zero.mp h with h' | h'
        · exact h'
        · exact absurd h' h1
      · intro h
        rw [h]
        simp [thetaS, hb]
    · constructor
      · intro h
        have h' : 1 - thetaS s x = 0 := by linarith
        rw [one_sub_thetaS] at h'
        have h1 : 1 - clamp1 s * x ≠ 0 := by
          have h2 : |clamp1 s * x| ≤ 1 / 2 := by
            rw [abs_mul]
            calc |clamp1 s| * |x| ≤ (1 / 2) * 1 :=
                  mul_le_mul (abs_clamp1_le s)
                    (by rw [abs_of_nonneg hx.1]; exact hx.2) (abs_nonneg x) (by norm_num)
              _ = 1 / 2 := by norm_num
          have := (abs_le.mp h2).2
          intro hc
          linarith
        rcases mul_eq_zero.mp h' with h'' | h''
        · linarith
        · exact absurd h'' h1
      · intro h
        rw [h]
        simp [thetaS, hb]
  · intro x x₀ hx
    have hc : HasDerivAt (fun s' : ℝ => thetaS s' x) (deriv clamp1 x₀ * hb x) x₀ := by
      have h1 : HasDerivAt (fun s' : ℝ => clamp1 s' * hb x)
          ((1 / (2 * (1 + x₀ ^ 2) * Real.sqrt (1 + x₀ ^ 2))) * hb x) x₀ :=
        (hasDerivAt_clamp1 x₀).mul_const (hb x)
      have h2 := (hasDerivAt_const x₀ (x : ℝ)).add h1
      unfold thetaS
      refine h2.congr_deriv ?_
      rw [(hasDerivAt_clamp1 x₀).deriv]
      ring
    rw [hc.deriv]
    exact mul_ne_zero (deriv_clamp1_ne_zero x₀) hx

end

end Work.Drive
