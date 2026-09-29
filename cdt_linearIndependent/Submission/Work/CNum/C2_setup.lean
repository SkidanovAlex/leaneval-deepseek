import Mathlib
import Submission.Work.CNum.Basic

/-!
# `Work.CNum.C2_setup`

Definitions and exact constants underlying the lemma `C2_clockwise`.

For `c = 23/10` the point `ψ_C(e^{iθ})` runs on the circle `C₂` (centre `c₂ = a/b`,
radius `ρ₂`) as `θ` runs over the "large" arc `(α, 2π - α)`, `α = alpR = arccos γ`.
Writing `t = θ/2`, `s = sin t`, `σ = sin(α/2) = 429/629`, `c₂/ρ₂ = 1/C` with
`C = cos(α/2) = 460/629`, one has the completely explicit formula

  `Vof θ = -((C2u θ) + (C2v θ) · I)/C`,  `C2u θ = cos²t + s·w`, `C2v θ = (s - w)·cos t`,
  `w = √(s² - σ²)`,

and `(C2u θ + C2v θ · I)/C = exp (I · C2Psi (θ/2))` with

  `C2Psi t = t - π/2 + arcsin (cos t / C)`.

`C2Psi` is strictly antitone on `(α/2, π - α/2)` with `Ψ'(t) = 1 - sin t/√(sin²t - σ²) < 0`,
so `C2_clockwise` follows.

This file only contains the definitions and the *exact* (rational) constants.
-/

namespace Work.CNum

open Complex

noncomputable section

/-- `C = cos(α/2) = 460/629`. -/
noncomputable def C2C : ℝ := 460 / 629

/-- `σ = sin(α/2) = 429/629`. -/
noncomputable def C2σ : ℝ := 429 / 629

/-- `T(θ) = √(2·A·(γ - cos θ))`, the modulus of `√(Ra (e^{iθ}))`. -/
noncomputable def C2T (θ : ℝ) : ℝ := Real.sqrt (2 * AR * (gamR - Real.cos θ))

/-- `w(θ) = √(sin²(θ/2) - σ²)`. -/
noncomputable def C2w (θ : ℝ) : ℝ := Real.sqrt (Real.sin (θ/2) ^ 2 - C2σ ^ 2)

/-- `Ψ(t) = t - π/2 + arcsin (cos t / C)`, the argument of `-Vof (2t)`. -/
noncomputable def C2Psi (t : ℝ) : ℝ := t - Real.pi / 2 + Real.arcsin (Real.cos t / C2C)

/-- Real part of `C · exp (I · Ψ(θ/2))`. -/
noncomputable def C2u (θ : ℝ) : ℝ := Real.cos (θ/2) ^ 2 + Real.sin (θ/2) * C2w θ

/-- Imaginary part of `C · exp (I · Ψ(θ/2))`. -/
noncomputable def C2v (θ : ℝ) : ℝ := (Real.sin (θ/2) - C2w θ) * Real.cos (θ/2)

lemma C2C_pos : 0 < C2C := by norm_num [C2C]
lemma C2σ_pos : 0 < C2σ := by norm_num [C2σ]
lemma C2C_ne_zero : C2C ≠ 0 := ne_of_gt C2C_pos
lemma C2σ_ne_zero : C2σ ≠ 0 := ne_of_gt C2σ_pos

lemma C2C_sq_add : C2C ^ 2 + C2σ ^ 2 = 1 := by norm_num [C2C, C2σ]

lemma one_sub_C2σ_sq : 1 - C2σ ^ 2 = C2C ^ 2 := by
  have h := C2C_sq_add; linarith

lemma C2σ_lt_C2C : C2σ < C2C := by norm_num [C2C, C2σ]

/-- `γ = 8c²/A - 1 = 27559/395641`. -/
lemma gamR_eq : gamR = 27559 / 395641 := by
  simp only [gamR, cR, AR]; norm_num

lemma cos_alpR : Real.cos alpR = gamR :=
  Real.cos_arccos (by rw [gamR_eq]; norm_num) (by rw [gamR_eq]; norm_num)

lemma gamR_bounds : gamR ∈ Set.Ioo (-1 : ℝ) 1 := by
  rw [gamR_eq]; norm_num

lemma alpR_bounds : alpR ∈ Set.Icc (0 : ℝ) Real.pi := by
  rw [alpR]; exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

lemma alpR_pos : 0 < alpR := by
  rw [alpR, Real.arccos_pos, gamR_eq]; norm_num

lemma alpR_lt_pi : alpR < Real.pi := by
  rw [alpR, Real.arccos_lt_pi, gamR_eq]; norm_num

lemma alpR_nonneg : 0 ≤ alpR := le_of_lt alpR_pos

/-- `cos(α/2) = 460/629`. -/
lemma cos_half_alpR : Real.cos (alpR / 2) = C2C := by
  rw [Real.cos_half (by linarith [alpR_pos, Real.pi_pos]) (le_of_lt alpR_lt_pi), cos_alpR,
    gamR_eq]
  have : (1 + 27559 / 395641 : ℝ) / 2 = C2C ^ 2 := by norm_num [C2C]
  rw [this, Real.sqrt_sq C2C_pos.le]

/-- `sin(α/2) = 429/629`. -/
lemma sin_half_alpR : Real.sin (alpR / 2) = C2σ := by
  rw [Real.sin_half_eq_sqrt alpR_nonneg (by linarith [alpR_lt_pi, Real.pi_pos]), cos_alpR,
    gamR_eq]
  have : (1 - 27559 / 395641 : ℝ) / 2 = C2σ ^ 2 := by norm_num [C2σ]
  rw [this, Real.sqrt_sq C2σ_pos.le]

/-- `2Aγ = B - 2A`. -/
lemma two_AR_gamR : 2 * AR * gamR = BR - 2 * AR := by
  simp only [gamR, AR, BR, cR]; norm_num

/-- `c₂ = a/b = 629/572`. -/
lemma cenC2_eq : cenC2 = 629 / 572 := by
  simp only [cenC2, aR, bR, kR, cR]; norm_num

/-- `ρ₂² = (115/143)²`. -/
lemma rho2sq_eq : rho2sq = (115 / 143) ^ 2 := by
  simp only [rho2sq, aR, bR, c0R, kR, cR]; norm_num

lemma sqrt_rho2sq : Real.sqrt rho2sq = 115 / 143 := by
  rw [rho2sq_eq, Real.sqrt_sq (by norm_num)]

lemma sqrt_rho2sq_pos : 0 < Real.sqrt rho2sq := by
  rw [sqrt_rho2sq]; norm_num

/-- `c₂/(115/143) = 1/C`. -/
lemma cenC2_div_sqrt_rho2sq : cenC2 / Real.sqrt rho2sq = 1 / C2C := by
  rw [cenC2_eq, sqrt_rho2sq]; norm_num [C2C]

lemma half_mem {θ : ℝ} (h : θ ∈ Set.Ioo alpR (2 * Real.pi - alpR)) :
    θ / 2 ∈ Set.Ioo (alpR / 2) (Real.pi - alpR / 2) := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨by linarith, by linarith⟩

/-- On the arc, `sin(θ/2) > σ`. -/
lemma C2σ_lt_sin_half {θ : ℝ} (h : θ ∈ Set.Ioo alpR (2 * Real.pi - alpR)) :
    C2σ < Real.sin (θ / 2) := by
  obtain ⟨h1, h2⟩ := h
  have hpi := alpR_lt_pi
  have hpos := alpR_pos
  have hsin : Real.sin (θ / 2) = Real.cos (θ / 2 - Real.pi / 2) := by
    have hh := Real.cos_pi_div_two_sub (θ / 2)
    rw [show Real.pi / 2 - θ / 2 = -(θ / 2 - Real.pi / 2) by ring, Real.cos_neg] at hh
    exact hh.symm
  have habs : |θ / 2 - Real.pi / 2| < Real.pi / 2 - alpR / 2 := by
    rw [abs_lt]; constructor <;> linarith
  have hcos : Real.cos (Real.pi / 2 - alpR / 2) < Real.cos |θ / 2 - Real.pi / 2| :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [hpos]) habs
  rw [Real.cos_abs] at hcos
  rw [hsin, ← sin_half_alpR, ← Real.cos_pi_div_two_sub (alpR / 2)]
  exact hcos

lemma C2w_pos {θ : ℝ} (h : θ ∈ Set.Ioo alpR (2 * Real.pi - alpR)) : 0 < C2w θ := by
  rw [C2w, Real.sqrt_pos]
  have h1 := C2σ_lt_sin_half h
  nlinarith [C2σ_pos]

lemma C2_cos_sq_half_le {θ : ℝ} (h : θ ∈ Set.Ioo alpR (2 * Real.pi - alpR)) :
    Real.cos (θ / 2) ^ 2 ≤ C2C ^ 2 := by
  have h1 := C2σ_lt_sin_half h
  have h2 : C2σ ^ 2 < Real.sin (θ / 2) ^ 2 := by nlinarith [C2σ_pos]
  have h3 : Real.cos (θ / 2) ^ 2 = 1 - Real.sin (θ / 2) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (θ / 2)]
  rw [h3, ← one_sub_C2σ_sq]; linarith

end

end Work.CNum
