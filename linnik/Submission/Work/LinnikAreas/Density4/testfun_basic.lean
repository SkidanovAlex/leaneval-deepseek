/-
# Area 4 / HB §12 — basic analytic facts about the §7 test function `fT`

The test function `fT` of Heath-Brown's §7 (used in §12) is defined as the closed form of
`g ⊛ g`, clamped to its support `[0, 2γ]`.  This file supplies the elementary facts that are
needed about it:

* it is non-negative on the whole line;
* it vanishes for `x < 0` and for `x ≥ 2γ`;
* its value at `0`, and the value of its Laplace transform `FT` at `0`.

Everything is proved from the explicit closed form: on its support `fT` is reduced to the
trigonometric bracket `brT`, which is written as
`∫_{s-θ}^{θ} (cos u - cos θ)(cos(s-u) - cos θ) du` — an integral of a product of two
non-negative factors (giving non-negativity) and, integrated over `[0,2θ]`, an elementary
antiderivative computation (giving the value of `FT` at `0`).
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.TestFun

open scoped BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

/-! ### The trigonometric bracket `(2θ-s)(cos s/2 + cos²θ) + sin(2θ-s)/2 - sin(2θ) + 2cosθ sin(s-θ)` -/

/-- The bracket that `fT` reduces to on its support, in the variable `s = ζ x`. -/
def brT (θ s : ℝ) : ℝ :=
  (2 * θ - s) * (Real.cos s / 2 + Real.cos θ ^ 2) + Real.sin (2 * θ - s) / 2
    - Real.sin (2 * θ) + 2 * Real.cos θ * Real.sin (s - θ)

lemma brT_def (θ s : ℝ) : brT θ s = (2 * θ - s) * (Real.cos s / 2 + Real.cos θ ^ 2)
    + Real.sin (2 * θ - s) / 2 - Real.sin (2 * θ) + 2 * Real.cos θ * Real.sin (s - θ) := rfl

/-- `cos` is decreasing on `[0,π]`: if `|x| ≤ θ ≤ π` then `cos θ ≤ cos x`. -/
lemma cos_theta_le_cos_of_abs_le {θ x : ℝ} (_hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (hx : |x| ≤ θ) : Real.cos θ ≤ Real.cos x := by
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := |x|) (y := θ) (abs_nonneg x) hθπ hx
  rwa [Real.cos_abs] at h

/-- The bracket as an integral of a product of two non-negative factors. -/
lemma brT_eq_integral (θ s : ℝ) : brT θ s =
    ∫ u in (s - θ)..θ, (Real.cos u - Real.cos θ) * (Real.cos (s - u) - Real.cos θ) := by
  rw [brT_def]
  set P : ℝ → ℝ := fun v : ℝ =>
      (1/2) * v * Real.cos s + Real.sin (2*v - s) / 4 + (-(Real.cos θ)) * Real.sin v
        + Real.cos θ * Real.sin (s - v) + Real.cos θ ^ 2 * v with hP
  have hder : ∀ u ∈ Set.uIcc (s - θ) θ,
      HasDerivAt P ((Real.cos u - Real.cos θ) * (Real.cos (s - u) - Real.cos θ)) u := by
    intro u _
    rw [hP]
    have hcos : Real.cos s / 2 + Real.cos (2 * u - s) / 2 = Real.cos u * Real.cos (s - u) := by
      have h := Real.two_mul_cos_mul_cos u (s - u)
      rw [show u - (s - u) = 2 * u - s from by ring, show u + (s - u) = s from by ring] at h
      linarith
    have h1 : HasDerivAt (fun v : ℝ => (1/2) * v * Real.cos s) ((1/2) * Real.cos s) u := by
      simpa using ((hasDerivAt_id' u).const_mul ((1:ℝ)/2)).mul_const (Real.cos s)
    have h2 : HasDerivAt (fun v : ℝ => Real.sin (2*v - s) / 4) (Real.cos (2*u - s) / 2) u := by
      have h := ((((hasDerivAt_id' u).const_mul (2:ℝ)).sub_const s).sin).div_const 4
      refine h.congr_deriv ?_
      ring
    have h3 : HasDerivAt (fun v : ℝ => (-(Real.cos θ)) * Real.sin v)
        ((-(Real.cos θ)) * Real.cos u) u := by
      simpa using (Real.hasDerivAt_sin u).const_mul (-(Real.cos θ))
    have h4 : HasDerivAt (fun v : ℝ => Real.cos θ * Real.sin (s - v))
        (Real.cos θ * (Real.cos (s - u) * (-1))) u := by
      have h : HasDerivAt (fun v : ℝ => Real.sin (s - v)) (Real.cos (s - u) * (-1)) u := by
        simpa using ((hasDerivAt_id' u).const_sub s).sin
      simpa using h.const_mul (Real.cos θ)
    have h5 : HasDerivAt (fun v : ℝ => Real.cos θ ^ 2 * v) (Real.cos θ ^ 2) u := by
      simpa using (hasDerivAt_id' u).const_mul (Real.cos θ ^ 2)
    have hbig := (((h1.add h2).add h3).add h4).add h5
    have hD : ((((1/2) * Real.cos s + Real.cos (2*u - s)/2) + ((-(Real.cos θ)) * Real.cos u))
        + Real.cos θ * (Real.cos (s - u) * (-1))) + Real.cos θ ^ 2
        = (Real.cos u - Real.cos θ) * (Real.cos (s - u) - Real.cos θ) := by
      linear_combination hcos
    exact hbig.congr_deriv hD
  have hint : (∫ u in (s - θ)..θ, (Real.cos u - Real.cos θ) * (Real.cos (s - u) - Real.cos θ))
      = P θ - P (s - θ) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (a := s - θ) (b := θ) hder
      (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [hint, hP]
  simp only
  rw [show s - (s - θ) = θ from by ring,
      show 2 * (s - θ) - s = -(2 * θ - s) from by ring, Real.sin_neg, Real.sin_two_mul]
  ring

/-- The bracket is non-negative on `[0, 2θ]` (for `0 ≤ θ ≤ π`). -/
lemma brT_nonneg {θ s : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) (hs0 : 0 ≤ s)
    (hs : s ≤ 2 * θ) : 0 ≤ brT θ s := by
  rw [brT_eq_integral]
  refine intervalIntegral.integral_nonneg (by linarith) (fun u hu => mul_nonneg ?_ ?_)
  · have h : Real.cos θ ≤ Real.cos u :=
      cos_theta_le_cos_of_abs_le hθ0 hθπ (abs_le.mpr ⟨by linarith [hu.1, hs0], hu.2⟩)
    linarith
  · have h : Real.cos θ ≤ Real.cos (s - u) :=
      cos_theta_le_cos_of_abs_le hθ0 hθπ
        (abs_le.mpr ⟨by linarith [hu.2, hs0], by linarith [hu.1]⟩)
    linarith

/-- The integral of the bracket over `[0,2θ]` (an elementary antiderivative computation). -/
lemma brT_integral (θ : ℝ) :
    (∫ s in (0:ℝ)..(2*θ), brT θ s) = 2 * (θ * Real.cos θ - Real.sin θ)^2 := by
  have hfun : (fun s : ℝ => brT θ s) = (fun s : ℝ =>
      (2 * θ - s) * (Real.cos s / 2 + Real.cos θ ^ 2) + Real.sin (2 * θ - s) / 2
        - Real.sin (2 * θ) + 2 * Real.cos θ * Real.sin (s - θ)) := funext fun s => brT_def θ s
  rw [hfun]
  set P2 : ℝ → ℝ := fun s : ℝ => ((2*θ - s) * Real.sin s - Real.cos s)/2
      - Real.cos θ^2/2 * ((2*θ - s) * (2*θ - s)) + Real.cos (2*θ - s)/2 - s * Real.sin (2*θ)
      - 2*Real.cos θ * Real.cos (s - θ) with hP2
  have hder : ∀ x ∈ Set.uIcc 0 (2*θ), HasDerivAt P2
      ((2 * θ - x) * (Real.cos x / 2 + Real.cos θ ^ 2) + Real.sin (2 * θ - x) / 2
        - Real.sin (2 * θ) + 2 * Real.cos θ * Real.sin (x - θ)) x := by
    intro x _
    rw [hP2]
    have h1 : HasDerivAt (fun s : ℝ => ((2*θ - s) * Real.sin s - Real.cos s)/2)
        ((2*θ - x) * Real.cos x / 2) x := by
      have h := ((((hasDerivAt_id' x).const_sub (2*θ)).mul ((hasDerivAt_id' x).sin)).sub
        (Real.hasDerivAt_cos x)).div_const 2
      refine h.congr_deriv ?_
      ring
    have h2 : HasDerivAt (fun s : ℝ => Real.cos θ^2/2 * ((2*θ - s) * (2*θ - s)))
        (-((2*θ - x) * Real.cos θ^2)) x := by
      have h := (((hasDerivAt_id' x).const_sub (2*θ)).mul
        ((hasDerivAt_id' x).const_sub (2*θ))).const_mul (Real.cos θ^2/2)
      refine h.congr_deriv ?_
      ring
    have h3 : HasDerivAt (fun s : ℝ => Real.cos (2*θ - s)/2) (Real.sin (2*θ - x)/2) x := by
      have h := (((hasDerivAt_id' x).const_sub (2*θ)).cos).div_const 2
      refine h.congr_deriv ?_
      ring
    have h4 : HasDerivAt (fun s : ℝ => s * Real.sin (2*θ)) (Real.sin (2*θ)) x := by
      simpa using (hasDerivAt_id' x).mul_const (Real.sin (2*θ))
    have h5 : HasDerivAt (fun s : ℝ => 2*Real.cos θ * Real.cos (s - θ))
        (2*Real.cos θ * (-(Real.sin (x - θ)))) x := by
      have h : HasDerivAt (fun s : ℝ => Real.cos (s - θ)) (-(Real.sin (x - θ))) x := by
        simpa using ((hasDerivAt_id' x).sub_const θ).cos
      simpa using h.const_mul (2*Real.cos θ)
    have hbig := (((h1.sub h2).add h3).sub h4).sub h5
    refine hbig.congr_deriv ?_
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 2*θ) hder
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [hint, hP2]
  simp only
  rw [show 2*θ - 2*θ = 0 from by ring, show 2*θ - 0 = 2*θ from by ring,
      show 0 - θ = -θ from by ring, show 2*θ - θ = θ from by ring,
      Real.sin_zero, Real.cos_zero, Real.cos_neg, Real.sin_two_mul, Real.cos_two_mul]
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-! ### Two algebraic identities for `tan θ` -/

lemma tan_sq_mul_cos_sq {θ : ℝ} (hc : Real.cos θ ≠ 0) :
    (1 + Real.tan θ ^ 2) * Real.cos θ ^ 2 = 1 := by
  have h := Real.inv_one_add_tan_sq hc
  rw [← h]
  field_simp

lemma tan_sq_mul_sin_cos {θ : ℝ} (hc : Real.cos θ ≠ 0) :
    (1 + Real.tan θ ^ 2) * (Real.sin θ * Real.cos θ) = Real.tan θ := by
  have h1 : (1 + Real.tan θ ^ 2) * Real.cos θ ^ 2 = 1 := tan_sq_mul_cos_sq hc
  calc (1 + Real.tan θ ^ 2) * (Real.sin θ * Real.cos θ)
      = ((1 + Real.tan θ ^ 2) * Real.cos θ ^ 2) * (Real.sin θ / Real.cos θ) := by field_simp
    _ = 1 * (Real.sin θ / Real.cos θ) := by rw [h1]
    _ = Real.tan θ := by rw [Real.tan_eq_sin_div_cos]; ring

/-- `(1+tan²θ)(θ(1+2cos²θ) - 3 sinθcosθ) = 3θ + θ tan²θ - 3 tanθ`. -/
lemma tan_key {θ : ℝ} (hc : Real.cos θ ≠ 0) :
    (1 + Real.tan θ ^ 2) * (θ * (1 + 2 * Real.cos θ ^ 2) - 3 * (Real.sin θ * Real.cos θ))
      = 3 * θ + θ * Real.tan θ ^ 2 - 3 * Real.tan θ := by
  have h1 := tan_sq_mul_cos_sq hc
  have h2 := tan_sq_mul_sin_cos hc
  have h3 : (1 + Real.tan θ ^ 2) * (θ * (1 + 2 * Real.cos θ ^ 2)
        - 3 * (Real.sin θ * Real.cos θ))
      = θ * (1 + Real.tan θ ^ 2) + 2 * θ * ((1 + Real.tan θ ^ 2) * Real.cos θ ^ 2)
        - 3 * ((1 + Real.tan θ ^ 2) * (Real.sin θ * Real.cos θ)) := by ring
  rw [h3, h1, h2]
  ring

/-! ### `fT` on its support -/

/-- On its support, `fT` is `(λ̂²(1+tan²θ)²/ζ) · brT (ζ x)`. -/
lemma fT_eq_brT {θ lam x : ℝ} (hζ : zetaT θ lam ≠ 0) (hx0 : 0 ≤ x)
    (hx2 : x ≤ 2 * gammaT θ lam) :
    fT θ lam x = lam ^ 2 * (1 + Real.tan θ ^ 2) ^ 2 / zetaT θ lam
      * brT θ (zetaT θ lam * x) := by
  rw [fT, if_pos ⟨hx0, hx2⟩, brT_def, gammaT]
  field_simp

/-- `ζ · 2γ = 2θ`. -/
lemma zetaT_mul_two_gammaT {θ lam : ℝ} (hζ : zetaT θ lam ≠ 0) :
    zetaT θ lam * (2 * gammaT θ lam) = 2 * θ := by
  rw [gammaT]
  field_simp

lemma brT_zero (θ : ℝ) :
    brT θ 0 = θ * (1 + 2 * Real.cos θ ^ 2) - 3 * (Real.sin θ * Real.cos θ) := by
  rw [brT_def]
  simp only [sub_zero, Real.cos_zero, zero_sub, Real.sin_neg]
  rw [Real.sin_two_mul]
  ring

lemma brT_two_theta (θ : ℝ) : brT θ (2 * θ) = 0 := by
  rw [brT_def, show 2*θ - 2*θ = 0 from by ring, show 2*θ - θ = θ from by ring]
  simp only [Real.sin_zero, zero_div, Real.sin_two_mul]
  ring

/-! ### The five assertions -/

lemma fT_nonneg (θ lam : ℝ) (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi) (hlam : 0 < lam) :
    ∀ x : ℝ, 0 ≤ fT θ lam x := by
  have hζ := zetaT_pos hθ1 hθ2 hlam
  have hθ0 : 0 ≤ θ := le_of_lt (lt_trans (by linarith [Real.pi_pos]) hθ1)
  have hθπ : θ ≤ Real.pi := le_of_lt hθ2
  intro x
  by_cases h : 0 ≤ x ∧ x ≤ 2 * gammaT θ lam
  · rw [fT_eq_brT (ne_of_gt hζ) h.1 h.2]
    refine mul_nonneg (div_nonneg (by positivity) hζ.le) ?_
    refine brT_nonneg hθ0 hθπ (mul_nonneg hζ.le h.1) ?_
    have h1 : zetaT θ lam * x ≤ zetaT θ lam * (2 * gammaT θ lam) :=
      mul_le_mul_of_nonneg_left h.2 hζ.le
    rwa [zetaT_mul_two_gammaT (ne_of_gt hζ)] at h1
  · rw [fT, if_neg h]

lemma fT_eq_zero_of_two_gammaT_le (θ lam : ℝ) (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi)
    (hlam : 0 < lam) : ∀ x : ℝ, 2 * gammaT θ lam ≤ x → fT θ lam x = 0 := by
  have hζ := zetaT_pos hθ1 hθ2 hlam
  intro x hx
  by_cases h : 0 ≤ x ∧ x ≤ 2 * gammaT θ lam
  · have hx2 : x = 2 * gammaT θ lam := le_antisymm h.2 hx
    rw [fT_eq_brT (ne_of_gt hζ) h.1 h.2, hx2, zetaT_mul_two_gammaT (ne_of_gt hζ), brT_two_theta,
      mul_zero]
  · rw [fT, if_neg h]

lemma fT_eq_zero_of_neg (θ lam : ℝ) : ∀ x : ℝ, x < 0 → fT θ lam x = 0 := by
  intro x hx
  rw [fT, if_neg]
  intro h
  exact absurd h.1 (not_le.mpr hx)

lemma fT_zero (θ lam : ℝ) (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi) (hlam : 0 < lam) :
    fT θ lam 0 = lam * (1 + Real.tan θ ^ 2) * (3 - θ * Real.tan θ - 3 * θ / Real.tan θ) := by
  have hζ := zetaT_pos hθ1 hθ2 hlam
  have hγ := gammaT_pos hθ1 hθ2 hlam
  have hc : Real.cos θ ≠ 0 := ne_of_lt (cos_neg_of_gt_half_pi hθ1 hθ2)
  have hT : Real.tan θ ≠ 0 := ne_of_lt (tan_neg_of_half_pi_lt hθ1 hθ2)
  have hkey := tan_key hc
  rw [fT_eq_brT (ne_of_gt hζ) le_rfl (by linarith), mul_zero, brT_zero]
  have hL : lam^2*(1+Real.tan θ^2)^2/zetaT θ lam
        * (θ*(1+2*Real.cos θ^2) - 3*(Real.sin θ*Real.cos θ))
      = -(lam*(1+Real.tan θ^2)/Real.tan θ)
        * ((1+Real.tan θ^2)*(θ*(1+2*Real.cos θ^2) - 3*(Real.sin θ*Real.cos θ))) := by
    rw [zetaT]; field_simp
  rw [hL, hkey]
  have hR : 3*θ + θ*Real.tan θ^2 - 3*Real.tan θ
      = Real.tan θ * (3*θ/Real.tan θ + θ*Real.tan θ - 3) := by
    field_simp
  rw [hR]
  field_simp
  ring

lemma FT_zero (θ lam : ℝ) (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi) (hlam : 0 < lam) :
    FT θ lam 0 = 2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2 := by
  have hζ := zetaT_pos hθ1 hθ2 hlam
  have hγ := gammaT_pos hθ1 hθ2 hlam
  have hc : Real.cos θ ≠ 0 := ne_of_lt (cos_neg_of_gt_half_pi hθ1 hθ2)
  have hT : Real.tan θ ≠ 0 := ne_of_lt (tan_neg_of_half_pi_lt hθ1 hθ2)
  have h1 : (1 + Real.tan θ ^ 2) * Real.cos θ ^ 2 = 1 := tan_sq_mul_cos_sq hc
  have hz2 : zetaT θ lam * (2 * gammaT θ lam) = 2 * θ := zetaT_mul_two_gammaT (ne_of_gt hζ)
  rw [FT]
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul]
  have hcongr : (∫ t in (0:ℝ)..(2*gammaT θ lam), fT θ lam t)
      = ∫ t in (0:ℝ)..(2*gammaT θ lam),
          lam^2*(1+Real.tan θ^2)^2/zetaT θ lam * brT θ (zetaT θ lam * t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    exact fT_eq_brT (ne_of_gt hζ) ht.1 ht.2
  rw [hcongr, intervalIntegral.integral_const_mul]
  have hsub : (∫ t in (0:ℝ)..(2*gammaT θ lam), brT θ (zetaT θ lam * t))
      = (zetaT θ lam)⁻¹ * ∫ s in (0:ℝ)..(2*θ), brT θ s := by
    rw [intervalIntegral.integral_comp_mul_left (fun s => brT θ s) (ne_of_gt hζ)]
    rw [mul_zero, hz2]
    ring
  rw [hsub, brT_integral]
  rw [show lam^2*(1+Real.tan θ^2)^2/zetaT θ lam
        * ((zetaT θ lam)⁻¹ * (2*(θ*Real.cos θ - Real.sin θ)^2))
      = lam^2*(1+Real.tan θ^2)^2/(zetaT θ lam)^2
        * (2*(θ*Real.cos θ - Real.sin θ)^2) from by
    field_simp]
  rw [show Real.sin θ = Real.tan θ * Real.cos θ from (Real.tan_mul_cos hc).symm]
  rw [zetaT]
  field_simp
  rw [h1]
  ring

theorem testfun_basic (θ lam : ℝ) (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi) (hlam : 0 < lam) :
    (∀ x : ℝ, 0 ≤ Work.LinnikAreas.Density4.fT θ lam x) ∧
    (∀ x : ℝ, 2 * Work.LinnikAreas.Density4.gammaT θ lam ≤ x →
        Work.LinnikAreas.Density4.fT θ lam x = 0) ∧
    (∀ x : ℝ, x < 0 → Work.LinnikAreas.Density4.fT θ lam x = 0) ∧
    (Work.LinnikAreas.Density4.fT θ lam 0 =
      lam * (1 + Real.tan θ ^ 2) * (3 - θ * Real.tan θ - 3 * θ / Real.tan θ)) ∧
    (Work.LinnikAreas.Density4.FT θ lam 0 =
      2 * (1 + Real.tan θ ^ 2) * (1 - θ / Real.tan θ) ^ 2) := by
  exact ⟨fT_nonneg θ lam hθ1 hθ2 hlam, fT_eq_zero_of_two_gammaT_le θ lam hθ1 hθ2 hlam,
    fT_eq_zero_of_neg θ lam, fT_zero θ lam hθ1 hθ2 hlam, FT_zero θ lam hθ1 hθ2 hlam⟩

end Work.LinnikAreas.Density4
