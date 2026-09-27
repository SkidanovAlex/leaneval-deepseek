import Mathlib

/-!
# Elementary model for the local dynamics of the equichordal half-map near `A₁`

This file contains the elementary real-analysis toolkit and the "model" functions used in
`Submission/Work/EQ/loc_estimates.lean`.

For `w = (1+a)/2` (the distance from the fixed point `A₁ = -1/2` to `O₂ = a/2`), the
equichordal half-map `eqU` in the coordinates `ζ = x+iy = P - A₁` reads (up to `eqU_add`)

  `locU a ζ = 1 - ζ + (ζ - w)/|ζ - w|`.

Writing `u = x - w`, `R = √(u²+v²)` and `1 ≤ w < 1`-type bounds, every quantity of interest is a
rational function of `R`:
* `mR w u v = R`,
* `mE w u v = (1-R)/R` (the `v`-multiplier of one step, equal to `locLy`),
* `mA w u v = R (R + w - u)` (note `1 + u/R = v²/mA`, the key algebraic identity),
* `mIA = 1/mA`,
* `mX w u v = -u + v²/mA` (the `x`-coordinate of one step, equal to `locX` when `u ≤ w`),
* `mY w u v = v · mE` (the `v`-coordinate of one step, equal to `locY`).

The estimates are proved on the box `MBox w h u v` (`|u| ≤ (1-w)/4`, `0 ≤ v ≤ h`,
`h ≤ w²/100`, `h² ≤ (1-w)(5w+3)/16`): on it `3w/4 ≤ R ≤ (1+w)/2 < 1`, so that `0 < mE ≤ 3`,
`9w²/8 ≤ mA ≤ 2`, `|mX| ≤ |u| + 2h²/w²` and `0 ≤ mY ≤ 3h`.
-/

namespace Work.EQ
namespace LocEst

/-! ## Elementary toolkit -/

/-- `x ↦ √((x-p)² + y²)` is 1-Lipschitz. -/
theorem sqrt_sq_lip (X₁ X₂ y : ℝ) :
    |Real.sqrt (X₁^2 + y^2) - Real.sqrt (X₂^2 + y^2)| ≤ |X₁ - X₂| := by
  have hA : 0 ≤ X₁^2 + y^2 := by positivity
  have hB : 0 ≤ X₂^2 + y^2 := by positivity
  have hr₁ : 0 ≤ Real.sqrt (X₁^2+y^2) := Real.sqrt_nonneg _
  have hr₂ : 0 ≤ Real.sqrt (X₂^2+y^2) := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ Real.sqrt (X₁^2+y^2) + Real.sqrt (X₂^2+y^2) by
      linarith) with h | h
  · have e1 : Real.sqrt (X₁^2+y^2) = 0 := by linarith
    have e2 : Real.sqrt (X₂^2+y^2) = 0 := by linarith
    have hx1 : X₁ = 0 := by
      have hh1 : X₁^2 + y^2 = 0 := by nlinarith [Real.sq_sqrt hA]
      have : X₁^2 = 0 := by nlinarith [sq_nonneg y]
      exact pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp this
    have hx2 : X₂ = 0 := by
      have hh2 : X₂^2 + y^2 = 0 := by nlinarith [Real.sq_sqrt hB]
      have : X₂^2 = 0 := by nlinarith [sq_nonneg y]
      exact pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp this
    rw [hx1, hx2]; simp
  · have key : Real.sqrt (X₁^2+y^2) - Real.sqrt (X₂^2+y^2)
        = (X₁ - X₂) * (X₁ + X₂) / (Real.sqrt (X₁^2+y^2) + Real.sqrt (X₂^2+y^2)) := by
      rw [eq_div_iff (ne_of_gt h)]
      nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB]
    have hsum : |X₁ + X₂| ≤ Real.sqrt (X₁^2+y^2) + Real.sqrt (X₂^2+y^2) := by
      have e1 : |X₁| ≤ Real.sqrt (X₁^2+y^2) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y])
      have e2 : |X₂| ≤ Real.sqrt (X₂^2+y^2) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y])
      calc |X₁ + X₂| ≤ |X₁| + |X₂| := abs_add_le _ _
        _ ≤ _ := by linarith
    rw [key, abs_div, abs_mul, abs_of_pos h, div_le_iff₀ h]
    calc |X₁ - X₂| * |X₁ + X₂|
        ≤ |X₁ - X₂| * (Real.sqrt (X₁^2+y^2) + Real.sqrt (X₂^2+y^2)) :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      _ = |X₁ - X₂| * (Real.sqrt (X₁^2+y^2) + Real.sqrt (X₂^2+y^2)) := rfl

/-- `y ↦ √(p² + y²)` is 1-Lipschitz. -/
theorem sqrt_sq_lip_y (p y₁ y₂ : ℝ) :
    |Real.sqrt (p^2 + y₁^2) - Real.sqrt (p^2 + y₂^2)| ≤ |y₁ - y₂| := by
  have h := sqrt_sq_lip y₁ y₂ p
  rw [add_comm (y₁^2) (p^2), add_comm (y₂^2) (p^2)] at h
  exact h

/-- `x ↦ 1/x` is `1/m²`-Lipschitz on `[m,∞)`. -/
theorem inv_sub_le {a b m : ℝ} (ha : m ≤ a) (hb : m ≤ b) (hm : 0 < m) :
    |1/a - 1/b| ≤ |a - b| / m^2 := by
  have hapos : 0 < a := lt_of_lt_of_le hm ha
  have hbpos : 0 < b := lt_of_lt_of_le hm hb
  have hab : 0 < a*b := mul_pos hapos hbpos
  have key : 1/a - 1/b = -(a - b)/(a*b) := by field_simp; ring
  rw [key, abs_div, abs_neg, abs_of_pos hab]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by nlinarith)

/-! ## The model functions -/

/-- `mR w u v = √((u-w)²+v²)`. -/
noncomputable def mR (w u v : ℝ) : ℝ := Real.sqrt ((u - w)^2 + v^2)

/-- `mE w u v = (1-R)/R`: the `v`-multiplier of one step. -/
noncomputable def mE (w u v : ℝ) : ℝ := (1 - mR w u v) / mR w u v

/-- `mA w u v = R (R + w - u)`; the point of it is `1 + (u-w)/R = v²/mA`. -/
noncomputable def mA (w u v : ℝ) : ℝ := mR w u v * (mR w u v + w - u)

/-- `mIA = 1/mA`. -/
noncomputable def mIA (w u v : ℝ) : ℝ := (mA w u v)⁻¹

/-- `mX w u v = -u + v²/mA`: the `x`-coordinate of one step. -/
noncomputable def mX (w u v : ℝ) : ℝ := -u + v^2 / mA w u v

/-- `mY w u v = v · mE`: the `v`-coordinate of one step. -/
noncomputable def mY (w u v : ℝ) : ℝ := v * mE w u v

/-- The box on which all estimates below hold: `|u| ≤ (1-w)/4`, `0 ≤ v ≤ h`, and `h` small
enough that `R ≤ (1+w)/2 < 1`. -/
structure MBox (w h u v : ℝ) : Prop where
  hw0 : 1/2 ≤ w
  hw1 : w < 1
  hu : |u| ≤ (1-w)/4
  hv0 : 0 ≤ v
  hvh : v ≤ h
  hh : h ≤ w^2/100
  hh2 : h^2 ≤ (1-w)*(5*w+3)/16

/-- `MBox` from the cruder hypotheses used in the assembly: `|x| ≤ 4ρ`, `0 ≤ y ≤ h`, `4ρ ≤ (1-w)/4`
and the smallness of `h`. -/
theorem MBox_of_bounds {w h ρ x y : ℝ} (hw0 : 1/2 ≤ w) (hw1 : w < 1) (hρ : 4*ρ ≤ (1-w)/4)
    (hx : |x| ≤ 4*ρ) (hy0 : 0 ≤ y) (hyh : y ≤ h) (hh : h ≤ w^2/100)
    (hh2 : h^2 ≤ (1-w)*(5*w+3)/16) : MBox w h x y :=
  ⟨hw0, hw1, le_trans hx hρ, hy0, hyh, hh, hh2⟩

/-! ## Pointwise bounds on the box -/

theorem mR_bounds {w h u v : ℝ} (B : MBox w h u v) :
    3*w/4 ≤ mR w u v ∧ mR w u v ≤ (1+w)/2 := by
  obtain ⟨hw0, hw1, hu, hv0, hvh, hh, hh2⟩ := B
  have hu' := abs_le.mp hu
  constructor
  · have h1 : (3*w/4)^2 ≤ (u-w)^2 + v^2 := by nlinarith [sq_nonneg v, hu'.1, hu'.2]
    have h2 : 0 ≤ 3*w/4 := by linarith
    calc 3*w/4 = Real.sqrt ((3*w/4)^2) := (Real.sqrt_sq h2).symm
      _ ≤ Real.sqrt ((u-w)^2 + v^2) := Real.sqrt_le_sqrt h1
      _ = mR w u v := by rw [mR]
  · have h1 : (u-w)^2 + v^2 ≤ ((1+w)/2)^2 := by nlinarith [hu'.1, hu'.2, hh2]
    calc mR w u v = Real.sqrt ((u-w)^2+v^2) := by rw [mR]
      _ ≤ Real.sqrt (((1+w)/2)^2) := Real.sqrt_le_sqrt h1
      _ = (1+w)/2 := Real.sqrt_sq (by linarith)

theorem mE_bounds {w h u v : ℝ} (B : MBox w h u v) : 0 < mE w u v ∧ mE w u v ≤ 3 := by
  obtain ⟨hRlo, hRhi⟩ := mR_bounds B
  obtain ⟨hw0, hw1, hu, hv0, hvh, hh, hh2⟩ := B
  have hRpos : 0 < mR w u v := by linarith
  have h1 : 0 < 1 - mR w u v := by linarith
  have h2 : 1 - mR w u v ≤ 3 * mR w u v := by linarith
  constructor
  · rw [mE]; exact div_pos h1 hRpos
  · rw [mE, div_le_iff₀ hRpos]; linarith

theorem mA_bounds {w h u v : ℝ} (B : MBox w h u v) : 9*w^2/8 ≤ mA w u v ∧ mA w u v ≤ 2 := by
  obtain ⟨hRlo, hRhi⟩ := mR_bounds B
  obtain ⟨hw0, hw1, hu, hv0, hvh, hh, hh2⟩ := B
  have hu' := abs_le.mp hu
  have hwu : 3*w/2 ≤ mR w u v + w - u := by linarith [hu'.2, hw0]
  have hRle : mR w u v ≤ 1 := by linarith
  have h1 : mR w u v + w - u ≤ 2 := by linarith [hu'.1, hw1]
  constructor
  · rw [mA]
    calc 9*w^2/8 = (3*w/4)*(3*w/2) := by ring
      _ ≤ mR w u v * (mR w u v + w - u) :=
          mul_le_mul hRlo hwu (by linarith) (by linarith)
  · rw [mA]
    calc mR w u v * (mR w u v + w - u) ≤ 1 * 2 :=
          mul_le_mul hRle h1 (by linarith) (by norm_num)
      _ = 2 := by norm_num

theorem mIA_bounds {w h u v : ℝ} (B : MBox w h u v) : 0 < mIA w u v ∧ mIA w u v ≤ 4 := by
  obtain ⟨hAlo, hAhi⟩ := mA_bounds B
  obtain ⟨hw0, hw1, hu, hv0, hvh, hh, hh2⟩ := B
  have hApos : 0 < mA w u v := by nlinarith
  constructor
  · rw [mIA]; exact inv_pos.mpr hApos
  · rw [mIA, inv_eq_one_div, div_le_iff₀ hApos]
    nlinarith [hAlo, hw0]

theorem mX_bound {w h u v : ℝ} (B : MBox w h u v) : |mX w u v| ≤ |u| + 2*h^2/w^2 := by
  obtain ⟨hAlo, hAhi⟩ := mA_bounds B
  obtain ⟨hw0, hw1, hu, hv0, hvh, hh, hh2⟩ := B
  have hApos : 0 < mA w u v := by nlinarith
  have hw2 : (0:ℝ) < w^2 := by positivity
  have h1 : v^2 / mA w u v ≤ 2*h^2/w^2 := by
    rw [div_le_iff₀ hApos, div_mul_eq_mul_div, le_div_iff₀ hw2]
    have hv2 : v^2 ≤ h^2 := by nlinarith
    have hh0 : 0 ≤ h := by linarith
    have h3 : v^2 * w^2 ≤ h^2 * w^2 := mul_le_mul_of_nonneg_right hv2 (sq_nonneg w)
    nlinarith [h3, hAlo, hw0, hh0]
  rw [mX]
  calc |-(u) + v^2/mA w u v| ≤ |-u| + |v^2/mA w u v| := abs_add_le _ _
    _ = |u| + v^2/mA w u v := by
        rw [abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ v^2/mA w u v)]
    _ ≤ |u| + 2*h^2/w^2 := by linarith

theorem mY_bounds {w h u v : ℝ} (B : MBox w h u v) : 0 ≤ mY w u v ∧ mY w u v ≤ 3*h := by
  obtain ⟨hElo, hEhi⟩ := mE_bounds B
  obtain ⟨hw0, hw1, hu, hv0, hvh, hh, hh2⟩ := B
  constructor
  · rw [mY]; positivity
  · rw [mY]; nlinarith

/-! ## One-variable Lipschitz estimates on the box -/

set_option linter.unusedVariables false

theorem mR_lip_u {w h u₁ u₂ v : ℝ} (B₁ : MBox w h u₁ v) (B₂ : MBox w h u₂ v) :
    |mR w u₁ v - mR w u₂ v| ≤ |u₁ - u₂| := by
  have h := sqrt_sq_lip (u₁ - w) (u₂ - w) v
  rw [sub_sub_sub_cancel_right u₁ u₂ w] at h
  exact h

theorem mR_lip_v {w h u v₁ v₂ : ℝ} (B₁ : MBox w h u v₁) (B₂ : MBox w h u v₂) :
    |mR w u v₁ - mR w u v₂| ≤ |v₁ - v₂| := sqrt_sq_lip_y (u - w) v₁ v₂

theorem mE_lip_u {w h u₁ u₂ v : ℝ} (B₁ : MBox w h u₁ v) (B₂ : MBox w h u₂ v) :
    |mE w u₁ v - mE w u₂ v| ≤ 4/w^2 * |u₁ - u₂| := by
  obtain ⟨hR₁lo, -⟩ := mR_bounds B₁
  obtain ⟨hR₂lo, -⟩ := mR_bounds B₂
  have hw0 := B₁.hw0
  have hm : (0:ℝ) < 3*w/4 := by linarith
  have h1 : |1/mR w u₁ v - 1/mR w u₂ v| ≤ |u₁ - u₂| / (3*w/4)^2 :=
    le_trans (inv_sub_le hR₁lo hR₂lo hm)
      (div_le_div_of_nonneg_right (mR_lip_u B₁ B₂) (by positivity))
  have h2 : mE w u₁ v - mE w u₂ v = 1/mR w u₁ v - 1/mR w u₂ v := by
    have e₁ : mR w u₁ v ≠ 0 := by linarith
    have e₂ : mR w u₂ v ≠ 0 := by linarith
    rw [mE, mE, div_eq_mul_inv, div_eq_mul_inv, sub_mul, sub_mul, one_mul, one_mul,
        mul_inv_cancel₀ e₁, mul_inv_cancel₀ e₂]
    ring
  rw [h2]
  have hconst : |u₁ - u₂| / (3*w/4)^2 ≤ 4/w^2 * |u₁ - u₂| := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (3*w/4)^2)]
    rw [mul_assoc, div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < w^2)]
    nlinarith [abs_nonneg (u₁ - u₂), hw0]
  linarith [h1, hconst]

theorem mE_lip_v {w h u v₁ v₂ : ℝ} (B₁ : MBox w h u v₁) (B₂ : MBox w h u v₂) :
    |mE w u v₁ - mE w u v₂| ≤ 4/w^2 * |v₁ - v₂| := by
  obtain ⟨hR₁lo, -⟩ := mR_bounds B₁
  obtain ⟨hR₂lo, -⟩ := mR_bounds B₂
  have hw0 := B₁.hw0
  have hm : (0:ℝ) < 3*w/4 := by linarith
  have h1 : |1/mR w u v₁ - 1/mR w u v₂| ≤ |v₁ - v₂| / (3*w/4)^2 :=
    le_trans (inv_sub_le hR₁lo hR₂lo hm)
      (div_le_div_of_nonneg_right (mR_lip_v B₁ B₂) (by positivity))
  have h2 : mE w u v₁ - mE w u v₂ = 1/mR w u v₁ - 1/mR w u v₂ := by
    have e₁ : mR w u v₁ ≠ 0 := by linarith
    have e₂ : mR w u v₂ ≠ 0 := by linarith
    rw [mE, mE, div_eq_mul_inv, div_eq_mul_inv, sub_mul, sub_mul, one_mul, one_mul,
        mul_inv_cancel₀ e₁, mul_inv_cancel₀ e₂]
    ring
  rw [h2]
  have hconst : |v₁ - v₂| / (3*w/4)^2 ≤ 4/w^2 * |v₁ - v₂| := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (3*w/4)^2)]
    rw [mul_assoc, div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < w^2)]
    nlinarith [abs_nonneg (v₁ - v₂), hw0]
  linarith [h1, hconst]

theorem mA_lip_u {w h u₁ u₂ v : ℝ} (B₁ : MBox w h u₁ v) (B₂ : MBox w h u₂ v) :
    |mA w u₁ v - mA w u₂ v| ≤ 8 * |u₁ - u₂| := by
  obtain ⟨hR₁lo, hR₁hi⟩ := mR_bounds B₁
  obtain ⟨hR₂lo, hR₂hi⟩ := mR_bounds B₂
  have hw0 := B₁.hw0
  have hlip := mR_lip_u B₁ B₂
  have hu₁ := abs_le.mp B₁.hu
  have hkey : mA w u₁ v - mA w u₂ v
      = (mR w u₁ v - mR w u₂ v) * (mR w u₁ v + mR w u₂ v + w - u₁)
        - mR w u₂ v * (u₁ - u₂) := by
    rw [mA, mA]; ring
  have hb : |mR w u₁ v + mR w u₂ v + w - u₁| ≤ 4 := by
    rw [abs_le]; constructor <;> linarith [hR₁hi, hR₂hi, hR₁lo, hR₂lo, hu₁.1, hu₁.2, B₁.hw1]
  have hR₂le : mR w u₂ v ≤ 1 := by linarith
  have hR₂pos : 0 < mR w u₂ v := by linarith
  have e1 : |(mR w u₁ v - mR w u₂ v) * (mR w u₁ v + mR w u₂ v + w - u₁)|
      ≤ |u₁ - u₂| * 4 := by
    rw [abs_mul]; exact mul_le_mul hlip hb (abs_nonneg _) (abs_nonneg _)
  have e2 : |mR w u₂ v * (u₁ - u₂)| ≤ 1 * |u₁ - u₂| := by
    rw [abs_mul, abs_of_pos hR₂pos]
    exact mul_le_mul hR₂le le_rfl (abs_nonneg _) zero_le_one
  rw [hkey]
  calc |(mR w u₁ v - mR w u₂ v) * (mR w u₁ v + mR w u₂ v + w - u₁)
        - mR w u₂ v * (u₁ - u₂)|
      = |(mR w u₁ v - mR w u₂ v) * (mR w u₁ v + mR w u₂ v + w - u₁)
        + -(mR w u₂ v * (u₁ - u₂))| := by ring_nf
    _ ≤ |(mR w u₁ v - mR w u₂ v) * (mR w u₁ v + mR w u₂ v + w - u₁)|
        + |mR w u₂ v * (u₁ - u₂)| := by
        have h := abs_add_le ((mR w u₁ v - mR w u₂ v) * (mR w u₁ v + mR w u₂ v + w - u₁))
          (-(mR w u₂ v * (u₁ - u₂)))
        rwa [abs_neg] at h
    _ ≤ |u₁ - u₂| * 4 + 1 * |u₁ - u₂| := by linarith [e1, e2]
    _ ≤ 8 * |u₁ - u₂| := by nlinarith [abs_nonneg (u₁ - u₂)]

theorem mA_lip_v {w h u v₁ v₂ : ℝ} (B₁ : MBox w h u v₁) (B₂ : MBox w h u v₂) :
    |mA w u v₁ - mA w u v₂| ≤ 8 * |v₁ - v₂| := by
  obtain ⟨hR₁lo, hR₁hi⟩ := mR_bounds B₁
  obtain ⟨hR₂lo, hR₂hi⟩ := mR_bounds B₂
  have hw0 := B₁.hw0
  have hlip := mR_lip_v B₁ B₂
  have hu := abs_le.mp B₁.hu
  have hkey : mA w u v₁ - mA w u v₂
      = (mR w u v₁ - mR w u v₂) * (mR w u v₁ + mR w u v₂ + w - u) := by
    rw [mA, mA]; ring
  have hb : |mR w u v₁ + mR w u v₂ + w - u| ≤ 4 := by
    rw [abs_le]; constructor <;> linarith [hR₁hi, hR₂hi, hR₁lo, hR₂lo, hu.1, hu.2, B₁.hw1]
  rw [hkey, abs_mul]
  calc |mR w u v₁ - mR w u v₂| * |mR w u v₁ + mR w u v₂ + w - u|
      ≤ |v₁ - v₂| * 4 := mul_le_mul hlip hb (abs_nonneg _) (abs_nonneg _)
    _ ≤ 8 * |v₁ - v₂| := by nlinarith [abs_nonneg (v₁ - v₂)]

theorem mIA_lip_u {w h u₁ u₂ v : ℝ} (B₁ : MBox w h u₁ v) (B₂ : MBox w h u₂ v) :
    |mIA w u₁ v - mIA w u₂ v| ≤ 16/w^4 * |u₁ - u₂| := by
  obtain ⟨hA₁lo, -⟩ := mA_bounds B₁
  obtain ⟨hA₂lo, -⟩ := mA_bounds B₂
  have hw0 := B₁.hw0
  have hm : (0:ℝ) < 9*w^2/8 := by nlinarith
  have h1 : |1/mA w u₁ v - 1/mA w u₂ v| ≤ |mA w u₁ v - mA w u₂ v| / (9*w^2/8)^2 :=
    inv_sub_le hA₁lo hA₂lo hm
  have h2 : |mA w u₁ v - mA w u₂ v| / (9*w^2/8)^2 ≤ (8 * |u₁ - u₂|) / (9*w^2/8)^2 :=
    div_le_div_of_nonneg_right (mA_lip_u B₁ B₂) (by positivity)
  have h3 : (8 * |u₁ - u₂|) / (9*w^2/8)^2 ≤ 16/w^4 * |u₁ - u₂| := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (9*w^2/8)^2)]
    rw [mul_assoc, div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < w^4)]
    nlinarith [abs_nonneg (u₁ - u₂), hw0]
  have hIA : mIA w u₁ v - mIA w u₂ v = 1/mA w u₁ v - 1/mA w u₂ v := by
    rw [mIA, mIA, inv_eq_one_div, inv_eq_one_div]
  rw [hIA]
  linarith [h1, h2, h3]

theorem mIA_lip_v {w h u v₁ v₂ : ℝ} (B₁ : MBox w h u v₁) (B₂ : MBox w h u v₂) :
    |mIA w u v₁ - mIA w u v₂| ≤ 16/w^4 * |v₁ - v₂| := by
  obtain ⟨hA₁lo, -⟩ := mA_bounds B₁
  obtain ⟨hA₂lo, -⟩ := mA_bounds B₂
  have hw0 := B₁.hw0
  have hm : (0:ℝ) < 9*w^2/8 := by nlinarith
  have h1 : |1/mA w u v₁ - 1/mA w u v₂| ≤ |mA w u v₁ - mA w u v₂| / (9*w^2/8)^2 :=
    inv_sub_le hA₁lo hA₂lo hm
  have h2 : |mA w u v₁ - mA w u v₂| / (9*w^2/8)^2 ≤ (8 * |v₁ - v₂|) / (9*w^2/8)^2 :=
    div_le_div_of_nonneg_right (mA_lip_v B₁ B₂) (by positivity)
  have h3 : (8 * |v₁ - v₂|) / (9*w^2/8)^2 ≤ 16/w^4 * |v₁ - v₂| := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (9*w^2/8)^2)]
    rw [mul_assoc, div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < w^4)]
    nlinarith [abs_nonneg (v₁ - v₂), hw0]
  have hIA : mIA w u v₁ - mIA w u v₂ = 1/mA w u v₁ - 1/mA w u v₂ := by
    rw [mIA, mIA, inv_eq_one_div, inv_eq_one_div]
  rw [hIA]
  linarith [h1, h2, h3]

theorem mX_lip_u {w h u₁ u₂ v : ℝ} (B₁ : MBox w h u₁ v) (B₂ : MBox w h u₂ v) :
    |mX w u₁ v - mX w u₂ v| ≤ 2 * |u₁ - u₂| := by
  have hw0 := B₁.hw0
  have hIA := mIA_lip_u B₁ B₂
  have hkey : mX w u₁ v - mX w u₂ v
      = -(u₁ - u₂) + v^2 * (mIA w u₁ v - mIA w u₂ v) := by
    rw [mX, mX, mIA, mIA]; ring
  have hv2 : v^2 ≤ h^2 := by nlinarith [B₁.hv0, B₁.hvh]
  have hh4 : h^2 ≤ w^4/10^4 := by
    have h2 : (0:ℝ) ≤ h := by linarith [B₁.hv0, B₁.hvh]
    have h3 : h^2 ≤ (w^2/100)^2 := by nlinarith [B₁.hh, h2, sq_nonneg w]
    calc h^2 ≤ (w^2/100)^2 := h3
      _ = w^4/10^4 := by ring
  have hv4 : v^2 ≤ w^4/10^4 := le_trans hv2 hh4
  have hfac : v^2 * (16/w^4) ≤ 1 := by
    calc v^2 * (16/w^4) ≤ (w^4/10^4) * (16/w^4) := mul_le_mul_of_nonneg_right hv4 (by positivity)
      _ = 16/10^4 := by field_simp
      _ ≤ 1 := by norm_num
  have hstep : v^2 * |mIA w u₁ v - mIA w u₂ v| ≤ |u₁ - u₂| := by
    have h2 : v^2 * |mIA w u₁ v - mIA w u₂ v| ≤ v^2 * (16/w^4 * |u₁ - u₂|) :=
      mul_le_mul_of_nonneg_left hIA (sq_nonneg v)
    have h3 : v^2 * (16/w^4 * |u₁ - u₂|) ≤ |u₁ - u₂| := by
      calc v^2 * (16/w^4 * |u₁ - u₂|) = (v^2 * (16/w^4)) * |u₁ - u₂| := by ring
        _ ≤ 1 * |u₁ - u₂| := mul_le_mul_of_nonneg_right hfac (abs_nonneg _)
        _ = |u₁ - u₂| := one_mul _
    linarith [h2, h3]
  rw [hkey]
  calc |-(u₁ - u₂) + v^2 * (mIA w u₁ v - mIA w u₂ v)|
      ≤ |-(u₁ - u₂)| + |v^2 * (mIA w u₁ v - mIA w u₂ v)| := abs_add_le _ _
    _ = |u₁ - u₂| + v^2 * |mIA w u₁ v - mIA w u₂ v| := by
        rw [abs_neg, abs_mul, abs_of_nonneg (sq_nonneg v)]
    _ ≤ |u₁ - u₂| + |u₁ - u₂| := by linarith [hstep]
    _ = 2 * |u₁ - u₂| := by ring

theorem mX_lip_v {w h u v₁ v₂ : ℝ} (B₁ : MBox w h u v₁) (B₂ : MBox w h u v₂) :
    |mX w u v₁ - mX w u v₂| ≤ |v₁ - v₂| := by
  obtain ⟨hIA₁lo, hIA₁hi⟩ := mIA_bounds B₁
  obtain ⟨hIA₂lo, -⟩ := mIA_bounds B₂
  have hw0 := B₁.hw0
  have hIA := mIA_lip_v B₁ B₂
  have hkey : mX w u v₁ - mX w u v₂
      = (v₁ - v₂) * (v₁ + v₂) * mIA w u v₁ + v₂^2 * (mIA w u v₁ - mIA w u v₂) := by
    rw [mX, mX, mIA, mIA]; ring
  have hvsum : |v₁ + v₂| ≤ 2*h := by
    rw [abs_le]; constructor <;> linarith [B₁.hv0, B₁.hvh, B₂.hv0, B₂.hvh]
  have hv2 : v₂^2 ≤ h^2 := by nlinarith [B₂.hv0, B₂.hvh]
  have hh4 : h^2 ≤ w^4/10^4 := by
    have h2 : (0:ℝ) ≤ h := by linarith [B₁.hv0, B₁.hvh]
    have h3 : h^2 ≤ (w^2/100)^2 := by nlinarith [B₁.hh, h2, sq_nonneg w]
    calc h^2 ≤ (w^2/100)^2 := h3
      _ = w^4/10^4 := by ring
  have hv4 : v₂^2 ≤ w^4/10^4 := le_trans hv2 hh4
  have hh0 : (0:ℝ) ≤ h := by linarith [B₁.hv0, B₁.hvh]
  have h1 : |(v₁ - v₂) * (v₁ + v₂) * mIA w u v₁| ≤ |v₁ - v₂| * (2*h*4) := by
    rw [abs_mul, abs_mul, abs_of_pos hIA₁lo]
    calc |v₁ - v₂| * |v₁ + v₂| * mIA w u v₁ ≤ |v₁ - v₂| * (2*h) * 4 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hvsum (abs_nonneg _)) hIA₁hi
            (le_of_lt hIA₁lo) (mul_nonneg (abs_nonneg _) (by linarith))
      _ = |v₁ - v₂| * (2*h*4) := by ring
  have h2 : |v₂^2 * (mIA w u v₁ - mIA w u v₂)| ≤ |v₁ - v₂| * (16/10^4) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg v₂)]
    have hfac : v₂^2 * (16/w^4) ≤ 16/10^4 := by
      calc v₂^2 * (16/w^4) ≤ (w^4/10^4) * (16/w^4) := mul_le_mul_of_nonneg_right hv4 (by positivity)
        _ = 16/10^4 := by field_simp
    calc v₂^2 * |mIA w u v₁ - mIA w u v₂| ≤ v₂^2 * (16/w^4 * |v₁ - v₂|) :=
          mul_le_mul_of_nonneg_left hIA (sq_nonneg v₂)
      _ = (v₂^2 * (16/w^4)) * |v₁ - v₂| := by ring
      _ ≤ (16/10^4) * |v₁ - v₂| := mul_le_mul_of_nonneg_right hfac (abs_nonneg _)
      _ = |v₁ - v₂| * (16/10^4) := by ring
  rw [hkey]
  calc |(v₁ - v₂) * (v₁ + v₂) * mIA w u v₁ + v₂^2 * (mIA w u v₁ - mIA w u v₂)|
      ≤ |(v₁ - v₂) * (v₁ + v₂) * mIA w u v₁| + |v₂^2 * (mIA w u v₁ - mIA w u v₂)| := abs_add_le _ _
    _ ≤ |v₁ - v₂| * (2*h*4) + |v₁ - v₂| * (16/10^4) := add_le_add h1 h2
    _ = |v₁ - v₂| * (2*h*4 + 16/10^4) := by ring
    _ ≤ |v₁ - v₂| * 1 := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have h' : h ≤ 1/100 := by
          have hw2 : w^2 ≤ 1 := by nlinarith [B₁.hw0, B₁.hw1]
          nlinarith [B₁.hh]
        nlinarith [h']
    _ = |v₁ - v₂| := by ring

theorem mY_lip_u {w h u₁ u₂ v : ℝ} (B₁ : MBox w h u₁ v) (B₂ : MBox w h u₂ v) :
    |mY w u₁ v - mY w u₂ v| ≤ 2 * |u₁ - u₂| := by
  have hE := mE_lip_u B₁ B₂
  have hkey : mY w u₁ v - mY w u₂ v = v * (mE w u₁ v - mE w u₂ v) := by
    rw [mY, mY]; ring
  have hvw : v ≤ h := B₁.hvh
  have hfac : h * (4/w^2) ≤ 2 := by
    have hw2 : w^2 ≤ 1 := by nlinarith [B₁.hw0, B₁.hw1]
    have hh' : h ≤ w^2/100 := B₁.hh
    rw [← mul_div_assoc, div_le_iff₀ (by nlinarith [B₁.hw0] : (0:ℝ) < w^2)]
    nlinarith [hh', hw2]
  rw [hkey, abs_mul, abs_of_nonneg B₁.hv0]
  calc v * |mE w u₁ v - mE w u₂ v| ≤ h * (4/w^2 * |u₁ - u₂|) :=
        mul_le_mul hvw hE (abs_nonneg _) (by linarith [B₁.hv0, B₁.hvh])
    _ = h * (4/w^2) * |u₁ - u₂| := by ring
    _ ≤ 2 * |u₁ - u₂| := mul_le_mul_of_nonneg_right hfac (abs_nonneg _)

theorem mY_lip_v {w h u v₁ v₂ : ℝ} (B₁ : MBox w h u v₁) (B₂ : MBox w h u v₂) :
    |mY w u v₁ - mY w u v₂| ≤ 4 * |v₁ - v₂| := by
  obtain ⟨hE₁lo, hE₁hi⟩ := mE_bounds B₁
  obtain ⟨hE₂lo, hE₂hi⟩ := mE_bounds B₂
  have hE := mE_lip_v B₁ B₂
  have hkey : mY w u v₁ - mY w u v₂
      = (v₁ - v₂) * mE w u v₁ + v₂ * (mE w u v₁ - mE w u v₂) := by
    rw [mY, mY]; ring
  have hfac : h * (4/w^2) ≤ 1 := by
    have hw2 : w^2 ≤ 1 := by nlinarith [B₁.hw0, B₁.hw1]
    have hh' : h ≤ w^2/100 := B₁.hh
    rw [← mul_div_assoc, div_le_iff₀ (by nlinarith [B₁.hw0] : (0:ℝ) < w^2)]
    nlinarith [hh', hw2]
  have h1 : |(v₁ - v₂) * mE w u v₁| ≤ |v₁ - v₂| * 3 := by
    rw [abs_mul, abs_of_pos hE₁lo]
    exact mul_le_mul_of_nonneg_left hE₁hi (abs_nonneg _)
  have h2 : |v₂ * (mE w u v₁ - mE w u v₂)| ≤ |v₁ - v₂| * 1 := by
    rw [abs_mul, abs_of_nonneg B₂.hv0]
    calc v₂ * |mE w u v₁ - mE w u v₂| ≤ h * (4/w^2 * |v₁ - v₂|) :=
          mul_le_mul B₂.hvh hE (abs_nonneg _) (by linarith [B₂.hv0, B₂.hvh])
      _ = (h * (4/w^2)) * |v₁ - v₂| := by ring
      _ ≤ 1 * |v₁ - v₂| := mul_le_mul_of_nonneg_right hfac (abs_nonneg _)
      _ = |v₁ - v₂| * 1 := by ring
  rw [hkey]
  calc |(v₁ - v₂) * mE w u v₁ + v₂ * (mE w u v₁ - mE w u v₂)|
      ≤ |(v₁ - v₂) * mE w u v₁| + |v₂ * (mE w u v₁ - mE w u v₂)| := abs_add_le _ _
    _ ≤ |v₁ - v₂| * 3 + |v₁ - v₂| * 1 := by linarith [h1, h2]
    _ = 4 * |v₁ - v₂| := by ring

/-! ## Two-variable Lipschitz estimates -/

theorem two_slice_lip {f : ℝ → ℝ → ℝ} {K₁ K₂ w h : ℝ}
    (h1 : ∀ u₁ u₂ v, MBox w h u₁ v → MBox w h u₂ v → |f u₁ v - f u₂ v| ≤ K₁ * |u₁ - u₂|)
    (h2 : ∀ u v₁ v₂, MBox w h u v₁ → MBox w h u v₂ → |f u v₁ - f u v₂| ≤ K₂ * |v₁ - v₂|)
    {u₁ v₁ u₂ v₂ : ℝ} (B₁ : MBox w h u₁ v₁) (B₂ : MBox w h u₂ v₂) :
    |f u₁ v₁ - f u₂ v₂| ≤ K₁ * |u₁ - u₂| + K₂ * |v₁ - v₂| := by
  have B : MBox w h u₂ v₁ := ⟨B₂.hw0, B₂.hw1, B₂.hu, B₁.hv0, B₁.hvh, B₂.hh, B₂.hh2⟩
  have e : f u₁ v₁ - f u₂ v₂ = (f u₁ v₁ - f u₂ v₁) + (f u₂ v₁ - f u₂ v₂) := by ring
  rw [e]
  have h := abs_add_le (f u₁ v₁ - f u₂ v₁) (f u₂ v₁ - f u₂ v₂)
  linarith [h1 u₁ u₂ v₁ B₁ B, h2 u₂ v₁ v₂ B B₂]

theorem mE_lip {w h u₁ v₁ u₂ v₂ : ℝ} (B₁ : MBox w h u₁ v₁) (B₂ : MBox w h u₂ v₂) :
    |mE w u₁ v₁ - mE w u₂ v₂| ≤ 4/w^2 * |u₁ - u₂| + 4/w^2 * |v₁ - v₂| :=
  two_slice_lip (K₁ := 4/w^2) (K₂ := 4/w^2) (f := mE w) (fun _ _ _ B₁ B₂ => mE_lip_u B₁ B₂)
    (fun _ _ _ B₁ B₂ => mE_lip_v B₁ B₂) B₁ B₂

theorem mIA_lip {w h u₁ v₁ u₂ v₂ : ℝ} (B₁ : MBox w h u₁ v₁) (B₂ : MBox w h u₂ v₂) :
    |mIA w u₁ v₁ - mIA w u₂ v₂| ≤ 16/w^4 * |u₁ - u₂| + 16/w^4 * |v₁ - v₂| :=
  two_slice_lip (K₁ := 16/w^4) (K₂ := 16/w^4) (f := mIA w) (fun _ _ _ B₁ B₂ => mIA_lip_u B₁ B₂)
    (fun _ _ _ B₁ B₂ => mIA_lip_v B₁ B₂) B₁ B₂

theorem mX_lip {w h u₁ v₁ u₂ v₂ : ℝ} (B₁ : MBox w h u₁ v₁) (B₂ : MBox w h u₂ v₂) :
    |mX w u₁ v₁ - mX w u₂ v₂| ≤ 2 * |u₁ - u₂| + |v₁ - v₂| := by
  have h := two_slice_lip (K₁ := 2) (K₂ := 1) (f := mX w) (fun _ _ _ B₁ B₂ => mX_lip_u B₁ B₂)
    (fun _ _ _ B₁ B₂ => by simpa using mX_lip_v B₁ B₂) B₁ B₂
  simpa using h

theorem mY_lip {w h u₁ v₁ u₂ v₂ : ℝ} (B₁ : MBox w h u₁ v₁) (B₂ : MBox w h u₂ v₂) :
    |mY w u₁ v₁ - mY w u₂ v₂| ≤ 2 * |u₁ - u₂| + 4 * |v₁ - v₂| :=
  two_slice_lip (K₁ := 2) (K₂ := 4) (f := mY w) (fun _ _ _ B₁ B₂ => mY_lip_u B₁ B₂)
    (fun _ _ _ B₁ B₂ => mY_lip_v B₁ B₂) B₁ B₂

end LocEst
end Work.EQ
