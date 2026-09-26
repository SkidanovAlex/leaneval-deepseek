import Mathlib
import Submission.Work.Smooth.JordanSeparation.Defs

/-!
# The model estimate for the winding-jump integrand

This file proves the pointwise estimate that controls the difference between the integrand of the
winding-jump integral at a nearby parameter `τ` and at `0`.  Writing `a = γ'(0)`, `u = γ'(0)/‖γ'(0)‖`
and `d = γ(τ) - γ(0)`, the two quantities compared are

`s·γ'(τ) / (d² + s²u²)`  and  `s·γ'(0) / (a²τ² + s²u²)`,

and the statement bounds the norm of their difference by the "model" expression
`4ηs / (((‖γ'(0)‖²)/2)τ² + s²)`.

The proof is the elementary but fiddly estimate from Pardon's paper.  Everything is carried out in
the abstract form `norm_integrand_sub_model_aux`, stated for complex numbers `a, aτ, u, d` and reals
`ρ, η, τ, s`, and then instantiated at `a = γ'(0)`, `aτ = γ'(τ)`, `u = unitTangent c 0`,
`d = γ(τ) - γ(0)`, `ρ = ‖γ'(0)‖`.

The ingredients are:

* `a = ρ·u` with `‖u‖ = 1`, hence `‖a‖ = ρ` and `a²τ² + s²u² = u²(ρ²τ² + s²)`, so the second
  denominator has norm exactly `ρ²τ² + s²`;
* `d = τ·a + w` with `‖w‖ ≤ η|τ|`, so `‖(d² + s²u²) - (a²τ² + s²u²)‖ = ‖2·(τa)·w + w²‖ ≤ η(2ρ+η)τ²`;
* the first denominator therefore has norm at least `(ρ²/2)τ² + s²` because `η ≤ ρ/8` forces
  `η(2ρ+η) ≤ ρ²/2`;
* splitting `s·aτ/P₁ - s·a/P₀ = s(aτ-a)/P₁ + s·a(P₀-P₁)/(P₁P₀)` and applying `div_le_div₀` twice
  reduces everything to the arithmetic lemma `arith_main`.
-/

namespace Work.Smooth.JordanSeparation

noncomputable section

open Work.Smooth.Jordan

/-- The elementary algebraic identity behind the estimate: the difference of two quotients with the
same numerator family is controlled by the difference of the denominators. -/
theorem div_sub_div_eq (x y w z : ℂ) (hw : w ≠ 0) (hz : z ≠ 0) :
    x / z - y / w = (x - y) / z + y * (w - z) / (z * w) := by
  field_simp
  ring

/-- The norm of a squared unit complex number times a nonnegative real scalar. -/
theorem norm_unit_sq_mul_real (u : ℂ) (r : ℝ) (hu : ‖u‖ = 1) (hr : 0 ≤ r) :
    ‖u ^ 2 * (r : ℂ)‖ = r := by
  rw [norm_mul, norm_pow, hu, one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr]

/-- A `τ²` bookkeeping identity used in the estimate for `‖P₁ - P₀‖`. -/
theorem tau_sq_arith (τ η ρ : ℝ) :
    2 * |τ| * ρ * (η * |τ|) + (η * |τ|) ^ 2 = η * (2 * ρ + η) * τ ^ 2 := by
  ring_nf
  rw [sq_abs]
  ring

/-- The pure-arithmetic heart of the estimate: with `Q = (ρ²/2)τ² + s²` and `R = ρ²τ² + s²` the two
fractions produced by the two `div_le_div₀` applications are bounded by the model expression. -/
theorem arith_main {ρ η τ s : ℝ} (hρ : 0 < ρ) (hη : 0 ≤ η) (hs : 0 < s) (h8 : η ≤ ρ / 8) :
    s * η / ((ρ ^ 2 / 2) * τ ^ 2 + s ^ 2)
      + s * ρ * η * (2 * ρ + η) * τ ^ 2
          / (((ρ ^ 2 / 2) * τ ^ 2 + s ^ 2) * (ρ ^ 2 * τ ^ 2 + s ^ 2))
    ≤ 4 * η * s / ((ρ ^ 2 / 2) * τ ^ 2 + s ^ 2) := by
  have hQ : 0 < (ρ ^ 2 / 2) * τ ^ 2 + s ^ 2 := by nlinarith [sq_nonneg ρ, sq_nonneg τ, hs]
  have hR : 0 < ρ ^ 2 * τ ^ 2 + s ^ 2 := by nlinarith [sq_nonneg ρ, sq_nonneg τ, hs]
  have hkey : ρ * (2 * ρ + η) * τ ^ 2 ≤ 3 * (ρ ^ 2 * τ ^ 2 + s ^ 2) := by
    nlinarith [h8, hη, hρ, sq_nonneg τ]
  rw [div_add_div _ _ (ne_of_gt hQ) (ne_of_gt (mul_pos hQ hR)),
      div_le_iff₀ (mul_pos hQ (mul_pos hQ hR))]
  have hsimp : (4 * η * s / ((ρ ^ 2 / 2) * τ ^ 2 + s ^ 2))
      * (((ρ ^ 2 / 2) * τ ^ 2 + s ^ 2)
          * (((ρ ^ 2 / 2) * τ ^ 2 + s ^ 2) * (ρ ^ 2 * τ ^ 2 + s ^ 2)))
      = 4 * η * s * (((ρ ^ 2 / 2) * τ ^ 2 + s ^ 2) * (ρ ^ 2 * τ ^ 2 + s ^ 2)) := by
    field_simp
  rw [hsimp]
  have hX : s * ρ * η * (2 * ρ + η) * τ ^ 2 ≤ 3 * η * (s * (ρ ^ 2 * τ ^ 2 + s ^ 2)) := by
    have h2 : (s * η) * (ρ * (2 * ρ + η) * τ ^ 2)
        ≤ (s * η) * (3 * (ρ ^ 2 * τ ^ 2 + s ^ 2)) :=
      mul_le_mul_of_nonneg_left hkey (mul_nonneg hs.le hη)
    nlinarith [h2]
  have hBX : ((ρ ^ 2 / 2) * τ ^ 2 + s ^ 2) * (s * ρ * η * (2 * ρ + η) * τ ^ 2)
      ≤ ((ρ ^ 2 / 2) * τ ^ 2 + s ^ 2) * (3 * η * (s * (ρ ^ 2 * τ ^ 2 + s ^ 2))) :=
    mul_le_mul_of_nonneg_left hX hQ.le
  nlinarith [hBX]

/-- The abstract model estimate.  This is the target statement with the curve `c` replaced by its
data: `a = γ'(0)`, `aτ = γ'(τ)`, `u = unitTangent c 0`, `d = γ(τ) - γ(0)`, `ρ = ‖γ'(0)‖`. -/
theorem norm_integrand_sub_model_aux {a aτ u d : ℂ} {ρ η τ s : ℝ}
    (hρ : 0 < ρ) (hη : 0 ≤ η) (hηρ : η ≤ ρ / 8) (hs : 0 < s)
    (hua : a = (ρ : ℂ) * u) (hnu : ‖u‖ = 1)
    (hw : ‖d - (τ : ℂ) * a‖ ≤ η * |τ|)
    (hder : ‖aτ - a‖ ≤ η)
    (hden : d ^ 2 + (s : ℂ) ^ 2 * u ^ 2 ≠ 0) :
    ‖(s : ℂ) * aτ / (d ^ 2 + (s : ℂ) ^ 2 * u ^ 2)
        - (s : ℂ) * a / (a ^ 2 * (τ : ℂ) ^ 2 + (s : ℂ) ^ 2 * u ^ 2)‖
      ≤ 4 * η * s / (((ρ ^ 2) / 2) * τ ^ 2 + s ^ 2) := by
  set P1 := d ^ 2 + (s : ℂ) ^ 2 * u ^ 2 with hP1def
  set P0 := a ^ 2 * (τ : ℂ) ^ 2 + (s : ℂ) ^ 2 * u ^ 2 with hP0def
  set w := d - (τ : ℂ) * a with hwdef
  set R := ρ ^ 2 * τ ^ 2 + s ^ 2 with hRdef
  set Q := (ρ ^ 2 / 2) * τ ^ 2 + s ^ 2 with hQdef
  have hna : ‖a‖ = ρ := by
    rw [hua, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, hnu, mul_one]
  have hwle : ‖w‖ ≤ η * |τ| := by rw [hwdef]; exact hw
  have hRpos : 0 < R := by rw [hRdef]; nlinarith [sq_nonneg ρ, sq_nonneg τ, hs]
  have hQpos : 0 < Q := by rw [hQdef]; nlinarith [sq_nonneg ρ, sq_nonneg τ, hs]
  have hP0eq : P0 = u ^ 2 * (R : ℂ) := by rw [hP0def, hua, hRdef]; push_cast; ring
  have hP0norm : ‖P0‖ = R := by rw [hP0eq]; exact norm_unit_sq_mul_real u R hnu hRpos.le
  have hP0ne : P0 ≠ 0 := by
    intro hz
    have : ‖P0‖ = 0 := by rw [hz]; simp
    rw [hP0norm] at this
    exact absurd this (ne_of_gt hRpos)
  have hP1ne : P1 ≠ 0 := by rw [hP1def]; exact hden
  have hdeq : d = w + (τ : ℂ) * a := by rw [hwdef]; ring
  have hP1P0 : P1 - P0 = 2 * ((τ : ℂ) * a) * w + w ^ 2 := by
    rw [hP1def, hP0def, hdeq]; ring
  have hnorm2 : ‖(2 : ℂ) * ((τ : ℂ) * a) * w‖ = 2 * |τ| * ρ * ‖w‖ := by
    rw [norm_mul, norm_mul, norm_mul, hna, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs]
    ring
  have hEbound : ‖P1 - P0‖ ≤ η * (2 * ρ + η) * τ ^ 2 := by
    rw [hP1P0]
    calc ‖2 * ((τ : ℂ) * a) * w + w ^ 2‖
        ≤ ‖2 * ((τ : ℂ) * a) * w‖ + ‖w ^ 2‖ := norm_add_le _ _
      _ = 2 * |τ| * ρ * ‖w‖ + ‖w‖ ^ 2 := by rw [hnorm2, norm_pow]
      _ ≤ 2 * |τ| * ρ * (η * |τ|) + (η * |τ|) ^ 2 := by
            have hA' : 2 * |τ| * ρ * ‖w‖ ≤ 2 * |τ| * ρ * (η * |τ|) :=
              mul_le_mul_of_nonneg_left hwle (by positivity)
            have hB' : ‖w‖ ^ 2 ≤ (η * |τ|) ^ 2 := by
              nlinarith [hwle, mul_nonneg hη (abs_nonneg τ), norm_nonneg w]
            linarith
      _ = η * (2 * ρ + η) * τ ^ 2 := tau_sq_arith τ η ρ
  have hkey : η * (2 * ρ + η) ≤ ρ ^ 2 / 2 := by nlinarith [hηρ, hη, hρ]
  have hP1lower : Q ≤ ‖P1‖ := by
    have hsub : ‖P0‖ - ‖P1 - P0‖ ≤ ‖P1‖ := by
      have h := norm_sub_le P1 (P1 - P0)
      have he : P1 - (P1 - P0) = P0 := by ring
      rw [he] at h
      linarith
    rw [hP0norm] at hsub
    have h2 : R - η * (2 * ρ + η) * τ ^ 2 ≤ ‖P1‖ := by linarith [hsub, hEbound]
    have h3 : Q ≤ R - η * (2 * ρ + η) * τ ^ 2 := by
      rw [hQdef, hRdef]
      nlinarith [hkey, sq_nonneg τ]
    linarith
  have hA : ‖(s : ℂ) * (aτ - a) / P1‖ ≤ s * η / Q := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hder hs.le) hQpos hP1lower
  have hB : ‖(s : ℂ) * a * (P0 - P1) / (P1 * P0)‖
      ≤ s * ρ * η * (2 * ρ + η) * τ ^ 2 / (Q * R) := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, hna, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs, hP0norm]
    have hab : s * ρ * ‖P0 - P1‖ ≤ s * ρ * η * (2 * ρ + η) * τ ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hEbound (by positivity : (0 : ℝ) ≤ s * ρ)
      rw [norm_sub_rev] at h
      nlinarith [h]
    have hcd : Q * R ≤ ‖P1‖ * R := mul_le_mul_of_nonneg_right hP1lower hRpos.le
    exact div_le_div₀ (by positivity) hab (mul_pos hQpos hRpos) hcd
  have hsplit : (s : ℂ) * aτ / P1 - (s : ℂ) * a / P0
      = (s : ℂ) * (aτ - a) / P1 + (s : ℂ) * a * (P0 - P1) / (P1 * P0) := by
    field_simp
    ring
  have harith : s * η / Q + s * ρ * η * (2 * ρ + η) * τ ^ 2 / (Q * R) ≤ 4 * η * s / Q := by
    simpa only [hQdef, hRdef] using arith_main hρ hη hs hηρ
  calc ‖(s : ℂ) * aτ / P1 - (s : ℂ) * a / P0‖
      = ‖(s : ℂ) * (aτ - a) / P1 + (s : ℂ) * a * (P0 - P1) / (P1 * P0)‖ := by rw [hsplit]
    _ ≤ ‖(s : ℂ) * (aτ - a) / P1‖ + ‖(s : ℂ) * a * (P0 - P1) / (P1 * P0)‖ := norm_add_le _ _
    _ ≤ s * η / Q + s * ρ * η * (2 * ρ + η) * τ ^ 2 / (Q * R) := add_le_add hA hB
    _ ≤ 4 * η * s / Q := harith

/-- `γ'(t) = ‖γ'(t)‖ · unitTangent c t` for an immersion. -/
theorem deriv_eq_norm_mul_unitTangent (c : SmoothPlaneCurve) (h : c.IsImmersion) (t : ℝ) :
    deriv c.γ t = ((‖deriv c.γ t‖ : ℝ) : ℂ) * unitTangent c t := by
  have hp : ((‖deriv c.γ t‖ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, norm_eq_zero]
    exact h t
  rw [unitTangent]
  exact (mul_div_cancel₀ (deriv c.γ t) hp).symm

theorem norm_integrand_sub_model_le (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    (h : Work.Smooth.Jordan.SmoothPlaneCurve.IsImmersion c) {η τ s : ℝ}
    (hη : 0 ≤ η) (hηρ : η ≤ ‖deriv c.γ 0‖ / 8)
    (hexp : ‖(c.γ τ - c.γ 0) - (τ : ℂ) * deriv c.γ 0‖ ≤ η * |τ|)
    (hder : ‖deriv c.γ τ - deriv c.γ 0‖ ≤ η)
    (hden : (c.γ τ - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (Work.Smooth.JordanSeparation.unitTangent c 0) ^ 2 ≠ 0)
    (hs : 0 < s) :
    ‖(s : ℂ) * deriv c.γ τ / ((c.γ τ - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (Work.Smooth.JordanSeparation.unitTangent c 0) ^ 2)
      - (s : ℂ) * deriv c.γ 0 / ((deriv c.γ 0) ^ 2 * (τ : ℂ) ^ 2
          + (s : ℂ) ^ 2 * (Work.Smooth.JordanSeparation.unitTangent c 0) ^ 2)‖
    ≤ 4 * η * s / (((‖deriv c.γ 0‖ ^ 2) / 2) * τ ^ 2 + s ^ 2) := by
  have hρ : 0 < ‖deriv c.γ 0‖ := norm_pos_iff.mpr (h 0)
  exact norm_integrand_sub_model_aux hρ hη hηρ hs
    (deriv_eq_norm_mul_unitTangent c h 0) (norm_unitTangent c h 0) hexp hder hden

end

end Work.Smooth.JordanSeparation
