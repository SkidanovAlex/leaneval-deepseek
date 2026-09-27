import Mathlib
import Submission.Work.Drive.N2Lead.mobius_lowerProfile
import Submission.Work.Drive.N2Lead.twistDefs
import Submission.Work.Drive.N2Lead.twistToolkit
import Submission.Work.Drive.N2Lead.smoothTransition_mul_deriv_le
import Submission.Work.Drive.N2Lead.mobiusPhiE_mem_Icc
import Submission.Work.Drive.N2.saddleWindowBlock

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-!
# The pushed polar bridges of the Möbius park are star-shaped about the origin

This file proves `Work.Drive.N2Lead.mobius_bridgeStar`, the bridge-zone companion of
`Work.Drive.N2Lead.mobius_pushedStar`.

The polar point of the bridge zone is `P φ = cE3 (r φ · e^{iφ})`, whose planar coordinates are
`X φ = r φ · cos φ` and `Y φ = r φ · sin φ`, and the push `pushY D εp 1` replaces the height `Y φ`
by `ψ (Y φ)`, where `ψ = pushProf D εp 1 = id + D·G` and `G y = 2·τ ((y+εp)/(2εp)) - 1`
(`τ = smoothTransition`).  The angular rate of the pushed curve is

`rate φ = X φ · (ψ ∘ Y)'(φ) - ψ (Y φ) · X'(φ) = ψ'(Y) · (X Y' - Y X') + (ψ'(Y)·Y - ψ Y) · X'`

and `X Y' - Y X' = r φ ^ 2` is the rate of the polar curve itself.  On `[0, φE]` we have
`cos φ ≥ 0`, `sin φ ≥ 0`, `deriv r φ ≤ 0` (the hypothesis `hrdec`), hence `X' ≤ 0` and `Y ≥ 0`; and
`1 ≤ ψ'` (`Work.Drive.N2Lead.deriv_pushProf_ge_one`) together with `ψ'(y)·y ≤ ψ y` for `y ≥ 0`
(the concavity of `ψ`, obtained from the concavity inequality of `smoothTransition`,
`Work.Drive.N2Lead.smoothTransition_mul_deriv_le`) make both summands positive.  The whole interval
`[-φE, φE]` follows because the rate is an even function of `φ` (`hreven` makes `r` even, hence
`r'` odd, and `ψ` is odd), and `φE ≤ π/2` is the delegated bound
`Work.Drive.N2Lead.mobiusPhiE_mem_Icc`.
-/

/-! ### basic smoothTransition facts -/

theorem smoothTransition_one_half : Real.smoothTransition (1/2 : ℝ) = 1/2 := by
  have h2 : (1 : ℝ) - 1/2 = 1/2 := by norm_num
  have h : Real.smoothTransition (1/2 : ℝ)
      = expNegInvGlue (1/2) / (expNegInvGlue (1/2) + expNegInvGlue (1/2)) := by
    simp only [Real.smoothTransition, h2]
  rw [h]
  have hne : expNegInvGlue (1/2 : ℝ) ≠ 0 :=
    (expNegInvGlue.pos_of_pos (by norm_num)).ne'
  field_simp
  ring

theorem smoothTransition_one_sub (x : ℝ) :
    Real.smoothTransition (1 - x) = 1 - Real.smoothTransition x := by
  have h1 : (1 : ℝ) - (1 - x) = x := by ring
  have hne : expNegInvGlue x + expNegInvGlue (1 - x) ≠ 0 :=
    (Real.smoothTransition.pos_denom x).ne'
  rw [Real.smoothTransition, Real.smoothTransition, h1, eq_sub_iff_add_eq']
  simp only [add_comm (expNegInvGlue (1 - x)) (expNegInvGlue x)]
  rw [← add_div, div_self hne]

/-! ### the vertical profile `G` -/

noncomputable def bridgeG (εp : ℝ) (y : ℝ) : ℝ :=
  2 * Real.smoothTransition ((y + εp) / (2 * εp)) - 1

theorem pushProf_one_eq (D εp y : ℝ) : pushProf D εp 1 y = y + D * bridgeG εp y := by
  simp only [pushProf, bridgeG, Real.smoothTransition.one, one_mul]

theorem pushProf_odd {D εp s y : ℝ} (hεp : εp ≠ 0) :
    pushProf D εp s (-y) = -pushProf D εp s y := by
  have h2ε : (2 * εp) ≠ 0 := by positivity
  have hx : (-y + εp) / (2 * εp) = 1 - (y + εp) / (2 * εp) := by
    rw [eq_sub_iff_add_eq', ← add_div, div_eq_one_iff_eq h2ε]
    ring
  rw [pushProf, pushProf, hx, smoothTransition_one_sub]
  ring

theorem hasDerivAt_bridgeG {εp : ℝ} (hεp : 0 < εp) (y : ℝ) :
    HasDerivAt (bridgeG εp) (deriv Real.smoothTransition ((y + εp) / (2 * εp)) / εp) y := by
  have h2ε : (0:ℝ) < 2 * εp := by linarith
  have hinner : HasDerivAt (fun z : ℝ => (z + εp) / (2 * εp)) (1 / (2 * εp)) y := by
    simpa using ((hasDerivAt_id y).add_const εp).div_const (2 * εp)
  have hdτ : DifferentiableAt ℝ Real.smoothTransition ((y + εp) / (2 * εp)) :=
    ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)).differentiableAt
  have hτ : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((y + εp) / (2 * εp))) ((y + εp) / (2 * εp)) :=
    hdτ.hasDerivAt
  have hcomp := hτ.comp y hinner
  have h2 : (2 : ℝ) * (deriv Real.smoothTransition ((y + εp) / (2 * εp)) * (1 / (2 * εp)))
      = deriv Real.smoothTransition ((y + εp) / (2 * εp)) / εp := by
    field_simp
  have hsub : HasDerivAt (fun z : ℝ => 2 * Real.smoothTransition ((z + εp) / (2 * εp)) - 1)
      (2 * (deriv Real.smoothTransition ((y + εp) / (2 * εp)) * (1 / (2 * εp)))) y := by
    simpa [Function.comp_def] using (hcomp.const_mul (2 : ℝ)).sub_const (1 : ℝ)
  rw [h2] at hsub
  exact hsub

theorem deriv_bridgeG_eq {εp : ℝ} (hεp : 0 < εp) (y : ℝ) :
    deriv (bridgeG εp) y = deriv Real.smoothTransition ((y + εp) / (2 * εp)) / εp :=
  (hasDerivAt_bridgeG hεp y).deriv

theorem bridgeG_mul_deriv_le {εp : ℝ} (hεp : 0 < εp) {y : ℝ} (hy : 0 ≤ y) :
    deriv (bridgeG εp) y * y ≤ bridgeG εp y := by
  set x : ℝ := (y + εp) / (2 * εp) with hx
  have h2ε : (0:ℝ) < 2 * εp := by linarith
  have hxhalf : (1/2 : ℝ) ≤ x := by
    rw [hx, le_div_iff₀ h2ε]; linarith
  have hyx : y / εp = 2 * x - 1 := by
    rw [hx]; field_simp; ring
  rw [deriv_bridgeG_eq hεp y, bridgeG, ← hx]
  have hconv : deriv Real.smoothTransition x / εp * y
      = deriv Real.smoothTransition x * (y / εp) := by field_simp
  rw [hconv, hyx]
  by_cases hx1 : x ≤ 1
  · have h := smoothTransition_mul_deriv_le (Set.mem_Icc.mpr ⟨hxhalf, hx1⟩)
    rw [mul_comm (2 * x - 1) (deriv Real.smoothTransition x)] at h
    exact h
  · have hx1' : 1 < x := not_le.mp hx1
    have hτ : Real.smoothTransition x = 1 := Real.smoothTransition.one_of_one_le hx1'.le
    have hev : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => 1) := by
      filter_upwards [lt_mem_nhds hx1'] with u hu
      exact Real.smoothTransition.one_of_one_le hu.le
    have hd : deriv Real.smoothTransition x = 0 := by
      rw [hev.deriv_eq, deriv_const]
    rw [hτ, hd]
    norm_num

theorem pushProf_mul_deriv_le {D εp : ℝ} (hεp : 0 < εp) (hD : 0 ≤ D) {y : ℝ} (hy : 0 ≤ y) :
    deriv (pushProf D εp 1) y * y ≤ pushProf D εp 1 y := by
  have hfun : pushProf D εp 1 = fun z : ℝ => z + D * bridgeG εp z := by
    funext z; exact pushProf_one_eq D εp z
  have hderiv : deriv (pushProf D εp 1) y = 1 + D * deriv (bridgeG εp) y := by
    rw [hfun, deriv_bridgeG_eq hεp y]
    exact ((hasDerivAt_id y).add ((hasDerivAt_bridgeG hεp y).const_mul D)).deriv
  rw [hderiv, hfun]
  have hkey := bridgeG_mul_deriv_le hεp hy
  nlinarith [hkey, hD, hy]

/-! ### the bridge curve -/

theorem bridgePt_zero (r : ℝ → ℝ) (φ : ℝ) :
    (Work.Drive.N2.cE3 (r φ * Complex.exp ((φ : ℂ) * Complex.I))) 0 = r φ * Real.cos φ := by
  rw [Work.Drive.N2.cE3_apply_zero, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

theorem bridgePt_one (r : ℝ → ℝ) (φ : ℝ) :
    (Work.Drive.N2.cE3 (r φ * Complex.exp ((φ : ℂ) * Complex.I))) 1 = r φ * Real.sin φ := by
  rw [Work.Drive.N2.cE3_apply_one, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

theorem bridgePt_two (r : ℝ → ℝ) (φ : ℝ) :
    (Work.Drive.N2.cE3 (r φ * Complex.exp ((φ : ℂ) * Complex.I))) 2 = 0 := by
  rw [Work.Drive.N2.cE3_apply_two]

/-- The polar point of the bridge zone, pushed by `pushY D εp 1`. -/
noncomputable def bridgeCurve (r : ℝ → ℝ) (D εp : ℝ) : ℝ → E3 :=
  fun φ => pushY D εp 1 (Work.Drive.N2.cE3 (r φ * Complex.exp ((φ : ℂ) * Complex.I)))

@[simp] theorem bridgeCurve_zero (r : ℝ → ℝ) (D εp φ : ℝ) :
    bridgeCurve r D εp φ 0 = r φ * Real.cos φ := by
  simp only [bridgeCurve, pushY_apply_zero, bridgePt_zero]

@[simp] theorem bridgeCurve_one (r : ℝ → ℝ) (D εp φ : ℝ) :
    bridgeCurve r D εp φ 1 = pushProf D εp 1 (r φ * Real.sin φ) := by
  simp only [bridgeCurve, pushY_apply_one, bridgePt_one]

theorem hasDerivAt_mul_cos {r : ℝ → ℝ} {φ : ℝ} (hr : DifferentiableAt ℝ r φ) :
    HasDerivAt (fun u : ℝ => r u * Real.cos u) (deriv r φ * Real.cos φ - r φ * Real.sin φ) φ := by
  have h := hr.hasDerivAt.mul (Real.hasDerivAt_cos φ)
  have hval : deriv r φ * Real.cos φ + r φ * (-Real.sin φ)
      = deriv r φ * Real.cos φ - r φ * Real.sin φ := by ring
  rwa [hval] at h

theorem hasDerivAt_mul_sin {r : ℝ → ℝ} {φ : ℝ} (hr : DifferentiableAt ℝ r φ) :
    HasDerivAt (fun u : ℝ => r u * Real.sin u) (deriv r φ * Real.sin φ + r φ * Real.cos φ) φ := by
  exact hr.hasDerivAt.mul (Real.hasDerivAt_sin φ)

theorem hasDerivAt_bridgeCurve_zero {r : ℝ → ℝ} {D εp φ : ℝ} (hr : DifferentiableAt ℝ r φ) :
    HasDerivAt (fun u : ℝ => bridgeCurve r D εp u 0)
      (deriv r φ * Real.cos φ - r φ * Real.sin φ) φ := by
  have hfun : (fun u : ℝ => bridgeCurve r D εp u 0) = fun u : ℝ => r u * Real.cos u :=
    funext (fun u => bridgeCurve_zero r D εp u)
  rw [hfun]
  exact hasDerivAt_mul_cos hr

theorem hasDerivAt_bridgeCurve_one {r : ℝ → ℝ} {D εp φ : ℝ} (hr : DifferentiableAt ℝ r φ) :
    HasDerivAt (fun u : ℝ => bridgeCurve r D εp u 1)
      (deriv (pushProf D εp 1) (r φ * Real.sin φ)
        * (deriv r φ * Real.sin φ + r φ * Real.cos φ)) φ := by
  have hfun : (fun u : ℝ => bridgeCurve r D εp u 1)
      = fun u : ℝ => pushProf D εp 1 (r u * Real.sin u) :=
    funext (fun u => bridgeCurve_one r D εp u)
  rw [hfun]
  exact (differentiable_pushProf D εp 1 (r φ * Real.sin φ)).hasDerivAt.comp φ (hasDerivAt_mul_sin hr)

theorem deriv_bridgeCurve_zero {r : ℝ → ℝ} {D εp φ : ℝ} (hr : DifferentiableAt ℝ r φ) :
    deriv (fun u : ℝ => bridgeCurve r D εp u 0) φ = deriv r φ * Real.cos φ - r φ * Real.sin φ :=
  (hasDerivAt_bridgeCurve_zero (D := D) (εp := εp) hr).deriv

theorem deriv_bridgeCurve_one {r : ℝ → ℝ} {D εp φ : ℝ} (hr : DifferentiableAt ℝ r φ) :
    deriv (fun u : ℝ => bridgeCurve r D εp u 1) φ
      = deriv (pushProf D εp 1) (r φ * Real.sin φ)
        * (deriv r φ * Real.sin φ + r φ * Real.cos φ) :=
  (hasDerivAt_bridgeCurve_one (D := D) (εp := εp) hr).deriv

theorem bridgeCurve_neg_zero {r : ℝ → ℝ} (hreven : ∀ φ : ℝ, r (-φ) = r φ) (D εp φ : ℝ) :
    bridgeCurve r D εp (-φ) 0 = bridgeCurve r D εp φ 0 := by
  rw [bridgeCurve_zero, bridgeCurve_zero, hreven, Real.cos_neg]

theorem bridgeCurve_neg_one {r : ℝ → ℝ} (hreven : ∀ φ : ℝ, r (-φ) = r φ) {D εp : ℝ}
    (hεp : εp ≠ 0) (φ : ℝ) :
    bridgeCurve r D εp (-φ) 1 = -bridgeCurve r D εp φ 1 := by
  rw [bridgeCurve_one, bridgeCurve_one, hreven, Real.sin_neg, mul_neg, pushProf_odd (D := D) hεp]

theorem differentiable_bridgeCurve_zero {r : ℝ → ℝ} {D εp : ℝ} (hr : ∀ φ : ℝ, DifferentiableAt ℝ r φ)
    (φ : ℝ) : DifferentiableAt ℝ (fun u : ℝ => bridgeCurve r D εp u 0) φ :=
  (hasDerivAt_bridgeCurve_zero (D := D) (εp := εp) (hr φ)).differentiableAt

theorem differentiable_bridgeCurve_one {r : ℝ → ℝ} {D εp : ℝ} (hr : ∀ φ : ℝ, DifferentiableAt ℝ r φ)
    (φ : ℝ) : DifferentiableAt ℝ (fun u : ℝ => bridgeCurve r D εp u 1) φ :=
  (hasDerivAt_bridgeCurve_one (D := D) (εp := εp) (hr φ)).differentiableAt

/-! ### parity of derivatives -/

theorem deriv_even_eq_neg {A : ℝ → ℝ} (hA : ∀ φ : ℝ, A (-φ) = A φ)
    (hd : ∀ φ : ℝ, DifferentiableAt ℝ A φ) (φ : ℝ) : deriv A (-φ) = -deriv A φ := by
  have h1 : deriv (fun u : ℝ => A (-u)) φ = -deriv A (-φ) := by
    have h := ((hd (-φ)).hasDerivAt.comp φ ((hasDerivAt_id φ).neg)).deriv
    rw [show (A ∘ Neg.neg) = (fun u : ℝ => A (-u)) from rfl] at h
    simpa using h
  have h2 : deriv (fun u : ℝ => A (-u)) φ = deriv A φ := by
    rw [show (fun u : ℝ => A (-u)) = A from funext hA]
  linarith

theorem deriv_odd_eq {B : ℝ → ℝ} (hB : ∀ φ : ℝ, B (-φ) = -B φ)
    (hd : ∀ φ : ℝ, DifferentiableAt ℝ B φ) (φ : ℝ) : deriv B (-φ) = deriv B φ := by
  have h1 : deriv (fun u : ℝ => B (-u)) φ = -deriv B (-φ) := by
    have h := ((hd (-φ)).hasDerivAt.comp φ ((hasDerivAt_id φ).neg)).deriv
    rw [show (B ∘ Neg.neg) = (fun u : ℝ => B (-u)) from rfl] at h
    simpa using h
  have h2 : deriv (fun u : ℝ => B (-u)) φ = -deriv B φ := by
    have hx : (fun u : ℝ => B (-u)) = -B := by
      funext u
      simp [hB u]
    rw [hx]
    exact ((hd φ).hasDerivAt.neg).deriv
  linarith

/-! ### the angular rate -/

/-- The angular rate `x · y' - y · x'` of the pushed bridge curve. -/
noncomputable def bridgeRate (r : ℝ → ℝ) (D εp : ℝ) (φ : ℝ) : ℝ :=
  bridgeCurve r D εp φ 0 * deriv (fun u : ℝ => bridgeCurve r D εp u 1) φ
    - bridgeCurve r D εp φ 1 * deriv (fun u : ℝ => bridgeCurve r D εp u 0) φ

theorem bridgeRate_even {r : ℝ → ℝ} (hreven : ∀ φ : ℝ, r (-φ) = r φ) {D εp : ℝ} (hεp : εp ≠ 0)
    (hr : ∀ φ : ℝ, DifferentiableAt ℝ r φ) (φ : ℝ) :
    bridgeRate r D εp (-φ) = bridgeRate r D εp φ := by
  have hA : ∀ ψ : ℝ, (fun u : ℝ => bridgeCurve r D εp u 0) (-ψ)
      = (fun u : ℝ => bridgeCurve r D εp u 0) ψ := fun ψ => bridgeCurve_neg_zero hreven D εp ψ
  have hB : ∀ ψ : ℝ, (fun u : ℝ => bridgeCurve r D εp u 1) (-ψ)
      = -(fun u : ℝ => bridgeCurve r D εp u 1) ψ := fun ψ => bridgeCurve_neg_one hreven hεp ψ
  have e1 := deriv_even_eq_neg hA (differentiable_bridgeCurve_zero (D := D) (εp := εp) hr) φ
  have e2 := deriv_odd_eq hB (differentiable_bridgeCurve_one (D := D) (εp := εp) hr) φ
  rw [bridgeRate, bridgeCurve_neg_zero hreven, bridgeCurve_neg_one hreven hεp, e1, e2, bridgeRate]
  ring

theorem bridgeRate_pos {r : ℝ → ℝ} {D εp φE : ℝ}
    (hrpos : ∀ φ : ℝ, 0 < r φ)
    (hrdec : ∀ φ ∈ Set.Icc 0 φE, deriv r φ ≤ 0)
    (hr : ∀ φ : ℝ, DifferentiableAt ℝ r φ)
    (hD : 0 ≤ D) (hεp : 0 < εp) (hφE : φE ≤ Real.pi / 2)
    {φ : ℝ} (hφ : φ ∈ Set.Icc 0 φE) : 0 < bridgeRate r D εp φ := by
  have hφ0 : 0 ≤ φ := hφ.1
  have hφπ : φ ≤ Real.pi / 2 := le_trans hφ.2 hφE
  have hcos : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hφπ⟩
  have hsin : 0 ≤ Real.sin φ := Real.sin_nonneg_of_mem_Icc ⟨hφ0, by linarith [Real.pi_pos]⟩
  have hdr : deriv r φ ≤ 0 := hrdec φ hφ
  have hA' : deriv r φ * Real.cos φ - r φ * Real.sin φ ≤ 0 := by
    have h2 : 0 ≤ r φ * Real.sin φ := mul_nonneg (le_of_lt (hrpos φ)) hsin
    have h1 : deriv r φ * Real.cos φ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hdr hcos
    linarith
  have hY : 0 ≤ r φ * Real.sin φ := mul_nonneg (le_of_lt (hrpos φ)) hsin
  have hkey : (r φ * Real.cos φ) * (deriv r φ * Real.sin φ + r φ * Real.cos φ)
      - (r φ * Real.sin φ) * (deriv r φ * Real.cos φ - r φ * Real.sin φ) = (r φ)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq φ]
  have hrate : bridgeRate r D εp φ
      = deriv (pushProf D εp 1) (r φ * Real.sin φ) * (r φ)^2
        + (deriv (pushProf D εp 1) (r φ * Real.sin φ) * (r φ * Real.sin φ)
            - pushProf D εp 1 (r φ * Real.sin φ))
          * (deriv r φ * Real.cos φ - r φ * Real.sin φ) := by
    rw [bridgeRate, bridgeCurve_zero, bridgeCurve_one, deriv_bridgeCurve_zero (hr φ),
      deriv_bridgeCurve_one (hr φ)]
    linear_combination (deriv (pushProf D εp 1) (r φ * Real.sin φ)) * hkey
  rw [hrate]
  have h1 : 1 * (r φ)^2 ≤ deriv (pushProf D εp 1) (r φ * Real.sin φ) * (r φ)^2 :=
    mul_le_mul_of_nonneg_right (deriv_pushProf_ge_one D εp 1 hεp hD (r φ * Real.sin φ))
      (sq_nonneg (r φ))
  have h2 : 0 ≤ (deriv (pushProf D εp 1) (r φ * Real.sin φ) * (r φ * Real.sin φ)
        - pushProf D εp 1 (r φ * Real.sin φ))
      * (deriv r φ * Real.cos φ - r φ * Real.sin φ) :=
    mul_nonneg_of_nonpos_of_nonpos
      (by linarith [pushProf_mul_deriv_le (D := D) (εp := εp) hεp hD hY]) hA'
  have h3 : 0 < (r φ)^2 := pow_pos (hrpos φ) 2
  have h4 : (1:ℝ) * (r φ)^2 ≤ deriv (pushProf D εp 1) (r φ * Real.sin φ) * (r φ)^2 := h1
  linarith


open scoped Manifold ContDiff Topology in
/-- **The pushed polar bridges of the Möbius park are star-shaped about the origin.**

Let `r` be the radial profile of `Work.Drive.N2Lead.mobius_lowerProfile` — smooth, positive, even, and
**nonincreasing on `[0, φE]`** (`hrdec`, the third row of that theorem) — and let
`P φ = cE3 (r φ · exp (i φ))` be the polar point of the bridge zone `[-φE, φE]`.  Then for every push
size `D ≥ 0` and every half-width `εp > 0` the angular rate of the pushed curve `pushY D εp 1 ∘ P`
is **strictly positive** on `[-φE, φE]`.

This is the bridge-zone companion of `Work.Drive.N2Lead.mobius_pushedStar`, which needs a constant
sign of the height `x₁`; on a bridge the height `r φ · sin φ` vanishes at `φ = 0`, so the push there
is not the rigid shift.  Writing `G(y) = 2 * smoothTransition ((y + εp)/(2εp)) - 1` (odd, `G' ≥ 0`,
`G'` maximal at `0`), the rate is `r φ ^ 2 + D * (G' * r φ ^ 2 + (G' * y - G) * x')`, and each factor
of the second term has the right sign: `sign x' = -sign y` (which is where `hrdec` and `hreven` are
used) and `sign (G' * y - G) = -sign y`.  So the rate is `≥ r φ ^ 2 > 0`, and the *positive* disjunct
of `StarAboutZero` holds, with no threshold on `D`. -/
theorem mobius_bridgeStar {r : ℝ → ℝ} {η m D εp : ℝ}
    (hrsm : ContDiff ℝ 1 r) (hrpos : ∀ φ : ℝ, 0 < r φ)
    (hreven : ∀ φ : ℝ, r (-φ) = r φ)
    (hrdec : ∀ φ ∈ Set.Icc 0 (Work.Drive.N2Lead.mobiusPhiE η m), deriv r φ ≤ 0)
    (hD : 0 ≤ D) (hεp : 0 < εp) :
    Work.Drive.N2Lead.StarAboutZero (fun φ : ℝ =>
        Work.Drive.N2Lead.pushY D εp 1
          (Work.Drive.N2.cE3 (r φ * Complex.exp ((φ : ℂ) * Complex.I))))
      (Set.Icc (-(Work.Drive.N2Lead.mobiusPhiE η m)) (Work.Drive.N2Lead.mobiusPhiE η m)) := by
  have hφE := mobiusPhiE_mem_Icc η m
  have hr : ∀ φ : ℝ, DifferentiableAt ℝ r φ :=
    fun φ => (hrsm.differentiable (by simp)).differentiableAt
  refine Or.inl ?_
  intro t ht
  change 0 < bridgeRate r D εp t
  rcases lt_or_ge t 0 with htneg | htpos
  · have hlt : 0 < -t := neg_pos.mpr htneg
    have hle : -t ≤ mobiusPhiE η m := by linarith [ht.1]
    have hpos := bridgeRate_pos (r := r) (D := D) (εp := εp) (φE := mobiusPhiE η m)
      hrpos hrdec hr hD hεp hφE.2 ⟨le_of_lt hlt, hle⟩
    have heven := bridgeRate_even (D := D) (εp := εp) hreven (ne_of_gt hεp) hr t
    rw [← heven]
    exact hpos
  · exact bridgeRate_pos (r := r) (D := D) (εp := εp) (φE := mobiusPhiE η m)
      hrpos hrdec hr hD hεp hφE.2 ⟨htpos, ht.2⟩

end

end Work.Drive.N2Lead
