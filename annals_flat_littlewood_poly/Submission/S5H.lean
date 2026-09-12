import Mathlib

/-! Monotonicity + continuity of `H(u) := 1/sin u − 1/u` on `[−π/2, π/2]`.

`H` is the continuous extension of `1/sin u − 1/u` across `u = 0` (in Lean,
`(0 : ℝ)⁻¹ = 0`, so the expression already takes value `0` at `u = 0`).
`H` is odd, vanishes at 0, and is strictly increasing on `[−π/2, π/2]`. -/

noncomputable section
set_option autoImplicit false

namespace Submission
namespace S5H

open scoped Topology

/-- `H(u) := 1/sin u − 1/u` (Lean division: value `0` at `u = 0`). -/
def H (u : ℝ) : ℝ := 1 / Real.sin u - 1 / u

lemma H_zero : H 0 = 0 := by simp [H]

/-- `H` is odd. -/
lemma H_neg (u : ℝ) : H (-u) = -H u := by
  simp [H, Real.sin_neg, div_neg]
  ring

/-- `H` as a quotient away from the zeros of `u` and `sin u`. -/
lemma H_eq_div {u : ℝ} (hu : u ≠ 0) (hsu : Real.sin u ≠ 0) :
    H u = (u - Real.sin u) / (u * Real.sin u) := by
  unfold H
  field_simp [hu, hsu]

/-! ### Elementary bounds used below -/

lemma xle2 {x : ℝ} (_hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi / 2) : x ≤ 2 := by
  linarith [Real.pi_lt_four]

lemma xsq_le4 {x : ℝ} (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi / 2) : x ^ 2 ≤ 4 := by
  have hx2 := xle2 hx0 hxpi
  nlinarith

/-- order-4 Taylor upper bound for `cos` on `[0, π/2]` -/
lemma cos_le_one_sub_sq_add {x : ℝ} (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi / 2) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let t : ℝ := x / 2
  have hsin : t - t ^ 3 / 6 ≤ Real.sin t := by
    exact Real.sin_ge_sub_cube (by positivity)
  have hb0 : 0 ≤ t - t ^ 3 / 6 := by
    have hx2 : x ^ 2 ≤ 24 := by
      have h := xsq_le4 hx0 hxpi
      nlinarith
    dsimp [t]
    nlinarith
  have hsq : (t - t ^ 3 / 6) ^ 2 ≤ Real.sin t ^ 2 :=
    pow_le_pow_left₀ hb0 hsin 2
  have hcos : Real.cos x = 1 - 2 * Real.sin t ^ 2 := by
    dsimp [t]
    have hs := Real.sin_sq_eq_half_sub (x / 2)
    rw [hs]
    ring_nf
  calc
    Real.cos x = 1 - 2 * Real.sin t ^ 2 := hcos
    _ ≤ 1 - 2 * (t - t ^ 3 / 6) ^ 2 := by
      nlinarith
    _ = 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 1152 := by
      dsimp [t]
      ring
    _ ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
      have hx6 : 0 ≤ x ^ 6 / 1152 := by positivity
      nlinarith

/-- `cos x ≤ (1 − x²/6)²` on `[0, π/2]` -/
lemma cos_le_sub_six_sq {x : ℝ} (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi / 2) :
    Real.cos x ≤ (1 - x ^ 2 / 6) ^ 2 := by
  have hc := cos_le_one_sub_sq_add hx0 hxpi
  have hx2 : x ^ 2 ≤ 12 := by
    have h := xsq_le4 hx0 hxpi
    nlinarith
  have halg : 1 - x ^ 2 / 2 + x ^ 4 / 24 ≤ (1 - x ^ 2 / 6) ^ 2 := by
    nlinarith
  exact hc.trans halg

/-- `x²·cos x ≤ sin²x` on `[0, π/2]` -/
lemma sin_sq_ge_mul_sq_cos {x : ℝ} (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi / 2) :
    x ^ 2 * Real.cos x ≤ Real.sin x ^ 2 := by
  by_cases hx : x = 0
  · subst x
    simp
  · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
    have hsin : x - x ^ 3 / 6 ≤ Real.sin x := Real.sin_ge_sub_cube hx0
    have hb0 : 0 ≤ x - x ^ 3 / 6 := by
      have hx2 : x ^ 2 ≤ 6 := by
        have h := xsq_le4 hx0 hxpi
        nlinarith
      nlinarith
    have hsq : (x - x ^ 3 / 6) ^ 2 ≤ Real.sin x ^ 2 := pow_le_pow_left₀ hb0 hsin 2
    have hcos := cos_le_sub_six_sq hx0 hxpi
    calc
      x ^ 2 * Real.cos x ≤ x ^ 2 * (1 - x ^ 2 / 6) ^ 2 :=
        mul_le_mul_of_nonneg_left hcos (sq_nonneg x)
      _ = (x - x ^ 3 / 6) ^ 2 := by ring
      _ ≤ Real.sin x ^ 2 := hsq

/-! ### Derivative of `H` on `(0, π/2)` -/

/-- derivative of `H` away from the zeros of `u` and `sin u` -/
lemma hasDerivAt_H {u : ℝ} (hu0 : u ≠ 0) (hsu : Real.sin u ≠ 0) :
    HasDerivAt H (1 / u ^ 2 - Real.cos u / Real.sin u ^ 2) u := by
  have h1 : HasDerivAt (fun t : ℝ => (Real.sin t)⁻¹) (-Real.cos u / Real.sin u ^ 2) u := by
    change HasDerivAt (Real.sin⁻¹) (-Real.cos u / Real.sin u ^ 2) u
    exact (Real.hasDerivAt_sin u).inv hsu
  have h2 : HasDerivAt (fun t : ℝ => t⁻¹) (-1 / u ^ 2) u := by
    change HasDerivAt ((fun t : ℝ => t)⁻¹) (-1 / u ^ 2) u
    exact (hasDerivAt_id u).inv hu0
  have hc : HasDerivAt (fun t : ℝ => (Real.sin t)⁻¹ - t⁻¹)
      (-Real.cos u / Real.sin u ^ 2 - (-1 / u ^ 2)) u := h1.sub h2
  have hH_eq : H = fun t : ℝ => (Real.sin t)⁻¹ - t⁻¹ := by
    funext t
    simp [H]
  rw [← hH_eq] at hc
  convert hc using 1
  ring

/-- the derivative of `H` is nonnegative on `(0, π/2)` -/
lemma deriv_H_nonneg {u : ℝ} (hu : u ∈ Set.Ioo 0 (Real.pi / 2)) : 0 ≤ deriv H u := by
  have hx0 : u ≠ 0 := ne_of_gt hu.1
  have hsin_pos : 0 < Real.sin u :=
    Real.sin_pos_of_pos_of_lt_pi hu.1 (lt_trans hu.2 (by linarith [Real.pi_pos]))
  have hsin0 : Real.sin u ≠ 0 := ne_of_gt hsin_pos
  have hd := hasDerivAt_H hx0 hsin0
  have hmaineq := sin_sq_ge_mul_sq_cos (le_of_lt hu.1) (le_of_lt hu.2)
  have hu2 : 0 < u ^ 2 := sq_pos_of_ne_zero hx0
  have hs2 : 0 < Real.sin u ^ 2 := sq_pos_of_ne_zero hsin0
  have hval : 1 / u ^ 2 - Real.cos u / Real.sin u ^ 2 =
      (Real.sin u ^ 2 - u ^ 2 * Real.cos u) / (u ^ 2 * Real.sin u ^ 2) := by
    field_simp [ne_of_gt hu2, ne_of_gt hs2]
  have hnum : 0 ≤ Real.sin u ^ 2 - u ^ 2 * Real.cos u := sub_nonneg.mpr hmaineq
  have hden : 0 < u ^ 2 * Real.sin u ^ 2 := mul_pos hu2 hs2
  rw [hd.deriv]
  rw [hval]
  exact div_nonneg hnum hden.le

/-! ### Continuity -/

/-- `|H u| ≤ |u|` on the unit ball (gives continuity at `0`) -/
lemma abs_H_le_of_abs_le_one {u : ℝ} (hu : |u| ≤ 1) : |H u| ≤ |u| := by
  by_cases hu0 : u = 0
  · subst u
    simp [H]
  · have hlepi2 : |u| ≤ Real.pi / 2 := by
      have h1 : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
      linarith
    have hsin_abs : 2 / Real.pi * |u| ≤ |Real.sin u| := Real.mul_abs_le_abs_sin hlepi2
    have hsin_ne : Real.sin u ≠ 0 := by
      have hpos : 0 < |u| := abs_pos.mpr hu0
      have hpi : 0 < 2 / Real.pi := by positivity
      have hlt : 0 < 2 / Real.pi * |u| := mul_pos hpi hpos
      intro hs
      have : |Real.sin u| = 0 := by simp [hs]
      linarith
    have hq : H u = (u - Real.sin u) / (u * Real.sin u) := H_eq_div hu0 hsin_ne
    have hdenpos : 0 < |u| * |Real.sin u| := mul_pos (abs_pos.mpr hu0) (abs_pos.mpr hsin_ne)
    have hmain : |u - Real.sin u| ≤ |u| * (|u| * |Real.sin u|) := by
      have hnum : |u - Real.sin u| ≤ |u| ^ 3 / 6 := Real.abs_sub_sin_le u
      have hpi12 : Real.pi ≤ 12 := by linarith [Real.pi_lt_four]
      have hfrac : (1 : ℝ) / 6 ≤ 2 / Real.pi := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 6) (by positivity : (0 : ℝ) < Real.pi)]
        nlinarith
      have ht3 : 0 ≤ |u| ^ 3 := by positivity
      have hnum2 : |u| ^ 3 / 6 ≤ (2 / Real.pi) * |u| ^ 3 := by nlinarith
      have hsin_mul : (2 / Real.pi) * |u| ^ 2 ≤ |Real.sin u| * |u| := by
        have hm := mul_le_mul_of_nonneg_right hsin_abs (abs_nonneg u)
        simpa [pow_two, mul_assoc] using hm
      have hsin_mul2 : (2 / Real.pi) * |u| ^ 3 ≤ |u| ^ 2 * |Real.sin u| := by
        have hm2 := mul_le_mul_of_nonneg_right hsin_mul (abs_nonneg u)
        nlinarith [hm2]
      calc
        |u - Real.sin u| ≤ |u| ^ 3 / 6 := hnum
        _ ≤ (2 / Real.pi) * |u| ^ 3 := hnum2
        _ ≤ |u| ^ 2 * |Real.sin u| := hsin_mul2
        _ = |u| * (|u| * |Real.sin u|) := by ring
    rw [hq, abs_div, abs_mul]
    exact (div_le_iff₀ hdenpos).2 hmain

/-- `H` is continuous at `0` -/
lemma continuousAt_H_zero : ContinuousAt H 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min 1 ε, lt_min (by norm_num) hε, ?_⟩
  intro x hx
  have hxlt1 : |x| < 1 := by
    have : dist x 0 < 1 := lt_of_lt_of_le hx (min_le_left _ _)
    simpa [Real.dist_eq] using this
  have hxlte : |x| < ε := by
    have : dist x 0 < ε := lt_of_lt_of_le hx (min_le_right _ _)
    simpa [Real.dist_eq] using this
  have hb := abs_H_le_of_abs_le_one (u := x) (le_of_lt hxlt1)
  have hmain : |H x| < ε := lt_of_le_of_lt hb hxlte
  simpa [Real.dist_eq, H_zero] using hmain

/-- `H` is continuous away from the zeros of `u` and `sin u` -/
lemma continuousAt_H_ne_zero {x : ℝ} (hx0 : x ≠ 0) (hsin : Real.sin x ≠ 0) :
    ContinuousAt H x := by
  have h1 : ContinuousAt (fun t : ℝ => (Real.sin t)⁻¹) x :=
    Real.continuous_sin.continuousAt.inv₀ hsin
  have h2 : ContinuousAt (fun t : ℝ => t⁻¹) x :=
    (continuousAt_id : ContinuousAt (fun t : ℝ => t) x).inv₀ hx0
  have hc : ContinuousAt (fun t : ℝ => (Real.sin t)⁻¹ - t⁻¹) x := h1.sub h2
  have hH_eq : H = fun t : ℝ => (Real.sin t)⁻¹ - t⁻¹ := by
    funext t
    simp [H]
  rwa [hH_eq]

/-- `H` is continuous on `[−π/2, π/2]` -/
lemma continuousOn_H : ContinuousOn H (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  by_cases hx0 : x = 0
  · subst x
    exact continuousAt_H_zero
  · have hmem : x ∈ Set.Ioo (-Real.pi) Real.pi := by
      constructor <;> linarith [hx.1, hx.2, Real.pi_pos]
    have hsin : Real.sin x ≠ 0 := by
      intro hs
      have hxeq : x = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt hmem.1 hmem.2).1 hs
      exact hx0 hxeq
    exact continuousAt_H_ne_zero hx0 hsin

/-! ### Monotonicity -/

/-- `H` is increasing on `[0, π/2]` -/
lemma H_monoOn_Icc_nonneg : MonotoneOn H (Set.Icc 0 (Real.pi / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (Real.pi / 2))
  · intro x hx
    apply ContinuousAt.continuousWithinAt
    by_cases hx0 : x = 0
    · subst x
      exact continuousAt_H_zero
    · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
      have hlt : x < Real.pi := lt_of_le_of_lt hx.2 (by linarith [Real.pi_pos])
      have hsp : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hxpos hlt
      exact continuousAt_H_ne_zero hx0 (ne_of_gt hsp)
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have hsin_pos : 0 < Real.sin x :=
      Real.sin_pos_of_pos_of_lt_pi hx.1 (lt_trans hx.2 (by linarith [Real.pi_pos]))
    exact (hasDerivAt_H hx0 (ne_of_gt hsin_pos)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact deriv_H_nonneg hx

/-- `H` is increasing on `[−π/2, π/2]` -/
lemma H_monoOn : MonotoneOn H (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) := by
  intro u hu v hv huv
  by_cases h0u : 0 ≤ u
  · have hu' : u ∈ Set.Icc 0 (Real.pi / 2) := ⟨h0u, hu.2⟩
    have hv' : v ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_trans h0u huv, hv.2⟩
    exact H_monoOn_Icc_nonneg hu' hv' huv
  · have hul : u < 0 := lt_of_not_ge h0u
    by_cases h0v : v ≤ 0
    · have ha : -v ∈ Set.Icc 0 (Real.pi / 2) := ⟨by linarith [h0v], by linarith [hv.1]⟩
      have hb : -u ∈ Set.Icc 0 (Real.pi / 2) := ⟨by linarith [hul], by linarith [hu.1]⟩
      have hle : -v ≤ -u := by linarith [huv]
      have hab := H_monoOn_Icc_nonneg ha hb hle
      have hvneg : H (-v) = -H v := H_neg v
      have huneg : H (-u) = -H u := H_neg u
      linarith
    · have hvpos : 0 < v := lt_of_not_ge h0v
      have hHu : H u ≤ 0 := by
        have hz : 0 ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
        have hu' : -u ∈ Set.Icc 0 (Real.pi / 2) := ⟨by linarith [hul], by linarith [hu.1]⟩
        have hge : 0 ≤ -u := by linarith [hul]
        have hnn := H_monoOn_Icc_nonneg hz hu' hge
        have hnonneg_mu : 0 ≤ H (-u) := by simpa [H_zero] using hnn
        have hnegrel : H (-u) = -H u := H_neg u
        linarith
      have hHv : 0 ≤ H v := by
        have hz : 0 ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
        have hv' : v ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_of_lt hvpos, hv.2⟩
        have hnn := H_monoOn_Icc_nonneg hz hv' (le_of_lt hvpos)
        simpa [H_zero] using hnn
      linarith

/-- `H` is continuous and increasing on `[−π/2, π/2]`. -/
theorem H_contMono :
    ContinuousOn H (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) ∧
      MonotoneOn H (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) := by
  exact ⟨continuousOn_H, H_monoOn⟩

/-- value at `π/2`. -/
theorem H_pi_div_two : H (Real.pi / 2) = 1 - 2 / Real.pi := by
  simp [H]

/-- value at `-π/2`. -/
theorem H_neg_pi_div_two : H (-(Real.pi / 2)) = -(1 - 2 / Real.pi) := by
  simp [H]
  ring

end S5H
end Submission
