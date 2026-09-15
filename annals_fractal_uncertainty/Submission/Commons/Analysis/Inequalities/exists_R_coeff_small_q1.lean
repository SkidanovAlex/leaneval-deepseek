import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option maxHeartbeats 4000000

namespace Commons.Analysis.Inequalities

/-! ## Tooling for `exists_R_coeff_small` -/

/-- The truncation scale `Λ = (log(2+R))^α`. -/
private noncomputable def ersLam (α : ℝ) (R : ℝ) : ℝ := (Real.log (2 + R)) ^ α

/-- The constant `K₀ = 16π²/c₃`. -/
private noncomputable def ersK0 (c₃ : ℝ) : ℝ := 16 * Real.pi ^ 2 / c₃

/-- The small parameter `ε = δ = e^{-K₀ Λ}/8`. -/
private noncomputable def ersEps (c₃ α : ℝ) (R : ℝ) : ℝ :=
  Real.exp (-(ersK0 c₃ * ersLam α R)) / 8

/-- The lens parameter `u = (1-ε)(1-3δ)`. -/
private noncomputable def ersU (c₃ α : ℝ) (R : ℝ) : ℝ :=
  (1 - ersEps c₃ α R) * (1 - 3 * ersEps c₃ α R)

/-- The log-ratio `C = log((1+u)/(1-u))`. -/
private noncomputable def ersC (c₃ α : ℝ) (R : ℝ) : ℝ :=
  Real.log ((1 + ersU c₃ α R) / (1 - ersU c₃ α R))

/-- The strip half-width parameter `ρ = c₃/(4πΛ)`. -/
private noncomputable def ersRho (c₃ α : ℝ) (R : ℝ) : ℝ := c₃ / (4 * Real.pi * ersLam α R)

/-- The lens parameter `η = (π/(2C) + ρ)/2`. -/
private noncomputable def ersEta (c₃ α : ℝ) (R : ℝ) : ℝ :=
  (Real.pi / (2 * ersC c₃ α R) + ersRho c₃ α R) / 2

/-- The strip extra parameter `r = (ρ-η)/2`. -/
private noncomputable def ersR (c₃ α : ℝ) (R : ℝ) : ℝ :=
  (ersRho c₃ α R - ersEta c₃ α R) / 2

/-- The quantity `η·4q/(πε)` occurring in the cube condition. -/
private noncomputable def ersHV (c₃ α : ℝ) (R : ℝ) : ℝ :=
  ersEta c₃ α R * (4 * 1 / (Real.pi * ersEps c₃ α R))

/-- The cube-dominating constant `H`. -/
private noncomputable def ersH (d : ℕ) (c₁ c₃ α : ℝ) (R : ℝ) : ℝ :=
  (c₁ / 2) ^ d / (4 * 20 ^ d * (ersHV c₃ α R) ^ d)

/-- The sum `X = 1 + 2δ^{-3}log(2/δ) + δ^{-2}log(2e/H)`. -/
private noncomputable def ersXv (d : ℕ) (c₁ c₃ α : ℝ) (R : ℝ) : ℝ :=
  1 + 2 * (ersEps c₃ α R)⁻¹ ^ 3 * Real.log (2 / ersEps c₃ α R)
      + (ersEps c₃ α R)⁻¹ ^ 2 * Real.log (2 * Real.exp 1 / ersH d c₁ c₃ α R)

/-- The Cartan exponent `κ`. -/
private noncomputable def ersKap (d : ℕ) (c₁ c₃ α : ℝ) (R : ℝ) : ℝ :=
  (ersXv d c₁ c₃ α R)⁻¹ ^ d

/-- The lattice constant `CW = (40(d+1))^d`. -/
private noncomputable def ersCW (d : ℕ) : ℝ := (40 * ((d : ℝ) + 1)) ^ d

/-- The Cartan constant `B`. -/
private noncomputable def ersB (d : ℕ) (c₁ c₃ α : ℝ) (R : ℝ) : ℝ :=
  (ersEta c₃ α R * (4 * 1 / (Real.pi * ersEps c₃ α R))) ^ d
    * (2 * (1 - 3 * ersEps c₃ α R)) ^ d * (2 : ℝ) ^ (ersKap d c₁ c₃ α R) *
    (((ersEta c₃ α R * ((1 - ersEps c₃ α R) * 1 / Real.pi)) ^ (-(d : ℝ))
        * (ersEta c₃ α R * (4 * 1 / (Real.pi * ersEps c₃ α R))) ^ d
        / (2 * (c₁ / 4)) ^ d) ^ (ersKap d c₁ c₃ α R))

/-- The potential-theory constant `U`. -/
private noncomputable def ersUc (d : ℕ) (c₁ c₃ α : ℝ) (R : ℝ) : ℝ :=
  (ersEta c₃ α R * ((2 / Real.pi) * Real.log ((1 + (1 - ersEps c₃ α R))
        / (1 - (1 - ersEps c₃ α R)))) + ersR c₃ α R + 1) ^ d *
    ((Real.pi * (ersR c₃ α R) ^ 2) ^ d)⁻¹

/-- The weight `t`. -/
private noncomputable def ersT (d : ℕ) (c₃ α : ℝ) (R : ℝ) : ℝ :=
  Real.exp (-(c₃ * R / (Real.log (2 + R)) ^ α)) * (1 + R ^ 2) ^ ((d : ℝ) / 2)

/-! ## Explicit constants used in the estimates -/

/-- An upper bound for `4η/π`. -/
private noncomputable def ersEtaUB (c₃ : ℝ) : ℝ := 2 + c₃ / (2 * Real.pi ^ 2)

/-- An upper bound for `2(ηq+r) = η+ρ`. -/
private noncomputable def ersEtaR (c₃ : ℝ) : ℝ := ersEtaUB c₃ * Real.pi / 4 + c₃ / (4 * Real.pi)

/-- An upper bound for `log (2e/H) - d K₀ Λ`. -/
private noncomputable def ersC1 (d : ℕ) (c₁ c₃ : ℝ) : ℝ :=
  Real.log 2 + 1 + Real.log 4 + (d : ℝ) * Real.log 20 + (d : ℝ) * ersEtaUB c₃
    + (d : ℝ) * Real.log 8 + (d : ℝ) * Real.log (2 / c₁)

/-- An upper bound for `X = 1 + 2δ^{-3}log(2/δ) + δ^{-2}log(2e/H)` divided by `Λ e^{3K₀Λ}`. -/
private noncomputable def ersCx (d : ℕ) (c₁ c₃ : ℝ) : ℝ :=
  1 + 1024 * (ersK0 c₃ + Real.log 16) + 64 * ((d : ℝ) * ersK0 c₃ + ersC1 d c₁ c₃)

private noncomputable def ersCB (d : ℕ) (c₁ c₃ : ℝ) : ℝ :=
  2 * (2048 * ersEtaUB c₃ / c₁) ^ d

/-- An upper bound for `U / Λ^{3d}`. -/
private noncomputable def ersCU (d : ℕ) (c₃ : ℝ) : ℝ :=
  ((ersEtaUB c₃ / 2) * (ersK0 c₃ + Real.log 16) + c₃ / (16 * Real.pi) + 1) ^ d
    * (128 ^ 2 * Real.pi / (49 * c₃ ^ 2)) ^ d

/-- An upper bound for `4^d · X / (e^{2dK₀Λ} Λ^{3d} R^{2d} e^{-2κc₃R/Λ})`. -/
private noncomputable def ersCX (d : ℕ) (c₁ c₃ Clat : ℝ) : ℝ :=
  (4 : ℝ) ^ d * ersCB d c₁ c₃ * (1 + ersCU d c₃) * (1 + ersEtaR c₃) ^ d * (2 : ℝ) ^ d * 2
    * (ersCW d) ^ 3 * Clat ^ 2

/-- An upper bound for `4^d · Y / (R^{2d} e^{-2κc₃R/Λ})`. -/
private noncomputable def ersCY (d : ℕ) (Clat : ℝ) : ℝ := (4 : ℝ) ^ d * (2 : ℝ) ^ d * ersCW d * Clat

/-- A common upper bound for `4^d (X+Y) / (e^{2dK₀Λ} Λ^{3d} R^{2d} e^{-2κc₃R/Λ})`. -/
private noncomputable def ersCT (d : ℕ) (c₁ c₃ Clat : ℝ) : ℝ := ersCX d c₁ c₃ Clat + ersCY d Clat

/-- The log of the RHS of the final inequality, in normalised form. -/
private noncomputable def ersLc (d : ℕ) (c₁ c₂ c₃ Clat : ℝ) : ℝ :=
  Real.log (2 * ersCT d c₁ c₃ Clat / c₂ ^ 2)

/-- A lower bound for `2c₃ Cx^{-d}`. -/
private noncomputable def ersKb (d : ℕ) (c₁ c₃ : ℝ) : ℝ :=
  2 * c₃ * (ersCx d c₁ c₃) ^ (-(d : ℝ))

/-- The constant `K₂` in the domination estimate. -/
private noncomputable def ersK2 (d : ℕ) (c₁ c₂ c₃ Clat : ℝ) : ℝ :=
  (|ersLc d c₁ c₂ c₃ Clat| + 2 * (d : ℝ) * ersK0 c₃ + 5 * (d : ℝ) + 1) / ersKb d c₁ c₃

/-- The sufficient condition for the parameters. -/
private def ersSuff (d : ℕ) (c₁ c₂ c₃ α Clat : ℝ) (R : ℝ) : Prop :=
  2 ≤ R ∧ (2 * (d : ℝ) / c₃) ^ 2 ≤ R ∧
  12 * (d : ℝ) * ersK0 c₃ * ersLam α R ≤ Real.log R ∧
  4 * ((d : ℝ) + 1) * Real.log (ersLam α R) ≤ Real.log R ∧
  4 * Real.log (ersLam α R + Real.log R + 1) ≤ Real.log R ∧
  4 * Real.log (ersK2 d c₁ c₂ c₃ Clat) ≤ Real.log R ∧
  1 ≤ ersHV c₃ α R


section BasicBounds

variable {c₁ c₂ c₃ α R : ℝ} {d : ℕ}

private lemma ersK0_pos (hc₃ : 0 < c₃) : 0 < ersK0 c₃ := by
  rw [ersK0]; positivity

private lemma log2R_ge_one (hR : 2 ≤ R) : 1 ≤ Real.log (2 + R) := by
  have hle : Real.log 4 ≤ Real.log (2 + R) := Real.log_le_log (by norm_num) (by linarith)
  have h4 : (1 : ℝ) < Real.log 4 := by
    have h45 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [h45]; linarith [Real.log_two_gt_d9]
  linarith

private lemma ersLam_pos {α : ℝ} (hα0 : 0 < α) {R : ℝ} (hR : 2 ≤ R) : 0 < ersLam α R := by
  rw [ersLam]
  exact Real.rpow_pos_of_pos (Real.log_pos (by linarith)) α

private lemma ersLam_ge_one {α : ℝ} (hα0 : 0 < α) {R : ℝ} (hR : 2 ≤ R) : 1 ≤ ersLam α R := by
  rw [ersLam]
  have := Real.rpow_le_rpow (show (0 : ℝ) ≤ 1 by norm_num) (log2R_ge_one hR) hα0.le
  simpa using this

private lemma ersLam_le_log {α : ℝ} (hα1 : α ≤ 1) {R : ℝ} (hR : 2 ≤ R) :
    ersLam α R ≤ Real.log (2 + R) := by
  rw [ersLam]
  calc (Real.log (2 + R)) ^ α ≤ (Real.log (2 + R)) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (log2R_ge_one hR) hα1
    _ = Real.log (2 + R) := Real.rpow_one _

private lemma ersEps_pos (hc₃ : 0 < c₃) {R : ℝ} : 0 < ersEps c₃ α R := by
  rw [ersEps]; positivity

private lemma ersEps_le_eighth (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    ersEps c₃ α R ≤ 1 / 8 := by
  rw [ersEps]
  have hΛ : 0 < ersLam α R := ersLam_pos hα0 hR
  have hK : 0 < ersK0 c₃ := ersK0_pos hc₃
  have h : Real.exp (-(ersK0 c₃ * ersLam α R)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  linarith

private lemma ersEps_le_half (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    ersEps c₃ α R ≤ 1 / 2 := by
  have := ersEps_le_eighth (α := α) hc₃ hα0 hR; linarith

private lemma ersEps_lt_third (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    ersEps c₃ α R < 1 / 3 := by
  have := ersEps_le_eighth (α := α) hc₃ hα0 hR; linarith

private lemma one_sub_ersEps_pos (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    0 < 1 - ersEps c₃ α R := by
  have := ersEps_le_eighth (α := α) hc₃ hα0 hR; linarith

private lemma ersU_eq : ersU c₃ α R = (1 - ersEps c₃ α R) * (1 - 3 * ersEps c₃ α R) := rfl

private lemma one_sub_ersU_eq :
    1 - ersU c₃ α R = 4 * ersEps c₃ α R - 3 * (ersEps c₃ α R) ^ 2 := by
  rw [ersU]; ring

private lemma ersU_pos (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) : 0 < ersU c₃ α R := by
  rw [ersU]
  have h1 : 0 < 1 - ersEps c₃ α R := one_sub_ersEps_pos hc₃ hα0 hR
  have h2 : 0 < 1 - 3 * ersEps c₃ α R := by
    have := ersEps_lt_third (α := α) hc₃ hα0 hR; linarith
  positivity

private lemma ersU_lt_one (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) : ersU c₃ α R < 1 := by
  rw [ersU]
  have hp := ersEps_pos (α := α) hc₃ (R := R)
  have h := ersEps_le_eighth (α := α) hc₃ hα0 hR
  nlinarith [hp, h, sq_nonneg (ersEps c₃ α R)]

private lemma one_sub_ersU_pos (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    0 < 1 - ersU c₃ α R := by
  have := ersU_lt_one (α := α) hc₃ hα0 hR; linarith

private lemma one_sub_ersU_le (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    1 - ersU c₃ α R ≤ 4 * ersEps c₃ α R := by
  rw [one_sub_ersU_eq]
  nlinarith [sq_nonneg (ersEps c₃ α R)]

private lemma ersEps_le_one_sub_ersU (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    ersEps c₃ α R ≤ 1 - ersU c₃ α R := by
  rw [one_sub_ersU_eq]
  have h := ersEps_le_eighth (α := α) hc₃ hα0 hR
  have hp := ersEps_pos (α := α) hc₃ (R := R)
  nlinarith

private lemma log_ersEps (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    Real.log (ersEps c₃ α R) = -(ersK0 c₃ * ersLam α R) - Real.log 8 := by
  rw [ersEps, Real.log_div (by positivity) (by norm_num), Real.log_exp]

end BasicBounds

section BasicBounds2

variable {c₁ c₂ c₃ α R : ℝ} {d : ℕ}

private lemma ersC_pos (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) : 0 < ersC c₃ α R := by
  rw [ersC]
  apply Real.log_pos
  have h1u := one_sub_ersU_pos hc₃ hα0 hR
  have hu := ersU_pos hc₃ hα0 hR
  rw [lt_div_iff₀ h1u]
  linarith

private lemma ersC_lower (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    ersK0 c₃ * ersLam α R + Real.log 2 ≤ ersC c₃ α R := by
  rw [ersC]
  have h1u := one_sub_ersU_pos hc₃ hα0 hR
  have hu := ersU_pos hc₃ hα0 hR
  have hle := one_sub_ersU_le hc₃ hα0 hR
  have hep := ersEps_pos (α := α) hc₃ (R := R)
  have hquot : 1 / (4 * ersEps c₃ α R) ≤ (1 + ersU c₃ α R) / (1 - ersU c₃ α R) := by
    have h1 : 1 / (4 * ersEps c₃ α R) ≤ 1 / (1 - ersU c₃ α R) :=
      one_div_le_one_div_of_le h1u hle
    have h2 : 1 / (1 - ersU c₃ α R) ≤ (1 + ersU c₃ α R) / (1 - ersU c₃ α R) := by
      rw [div_le_div_iff₀ h1u h1u]; nlinarith
    linarith
  have hlog := Real.log_le_log (div_pos (by linarith [hu]) (mul_pos (by norm_num) hep)) hquot
  have hval : Real.log (1 / (4 * ersEps c₃ α R)) = ersK0 c₃ * ersLam α R + Real.log 2 := by
    have h4e : 4 * ersEps c₃ α R = Real.exp (-(ersK0 c₃ * ersLam α R)) / 2 := by
      rw [ersEps]; ring
    rw [h4e, one_div, Real.log_inv, Real.log_div (by positivity) (by norm_num), Real.log_exp]
    ring
  rwa [hval] at hlog

private lemma ersC_upper (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    ersC c₃ α R ≤ ersK0 c₃ * ersLam α R + Real.log 16 := by
  rw [ersC]
  have h1u := one_sub_ersU_pos hc₃ hα0 hR
  have hge := ersEps_le_one_sub_ersU hc₃ hα0 hR
  have hep := ersEps_pos (α := α) hc₃ (R := R)
  have hu1 := ersU_lt_one hc₃ hα0 hR
  have hu := ersU_pos hc₃ hα0 hR
  have hquot : (1 + ersU c₃ α R) / (1 - ersU c₃ α R) ≤ 2 / ersEps c₃ α R := by
    have h1 : (1 + ersU c₃ α R) / (1 - ersU c₃ α R) ≤ 2 / (1 - ersU c₃ α R) := by
      rw [div_le_div_iff₀ h1u h1u]; nlinarith
    have h2 : 2 / (1 - ersU c₃ α R) ≤ 2 / ersEps c₃ α R := by
      rw [div_le_div_iff₀ h1u hep]; nlinarith
    linarith
  have hlog := Real.log_le_log (div_pos (by linarith [hu]) h1u) hquot
  have hlog16 : Real.log 16 = Real.log 2 + Real.log 8 := by
    rw [show (16 : ℝ) = 2 * 8 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [hlog16]
  rw [Real.log_div (by norm_num) (ne_of_gt hep), log_ersEps hc₃ hα0 hR] at hlog
  linarith

private lemma ersEps_inv (hc₃ : 0 < c₃) :
    (ersEps c₃ α R)⁻¹ = 8 * Real.exp (ersK0 c₃ * ersLam α R) := by
  rw [ersEps, inv_div, Real.exp_neg, div_inv_eq_mul]

private lemma ersC_inv_le_two (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    1 / ersC c₃ α R ≤ 2 := by
  have hC := ersC_pos hc₃ hα0 hR
  rw [div_le_iff₀ hC]
  have h := ersC_lower hc₃ hα0 hR
  have hK := ersK0_pos hc₃
  have hL := ersLam_pos hα0 hR
  have hKL : 0 < ersK0 c₃ * ersLam α R := mul_pos hK hL
  linarith [Real.log_two_gt_d9, hKL]

private lemma ersRho_pos (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) : 0 < ersRho c₃ α R := by
  rw [ersRho]
  exact div_pos hc₃ (mul_pos (by positivity) (ersLam_pos hα0 hR))

private lemma ersRho_le (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    ersRho c₃ α R ≤ c₃ / (4 * Real.pi) := by
  rw [ersRho]
  apply div_le_div_of_nonneg_left (le_of_lt hc₃) (by positivity)
  nlinarith [ersLam_ge_one hα0 hR, Real.pi_pos]

private lemma ersEta_pos (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) : 0 < ersEta c₃ α R := by
  rw [ersEta]
  have hC := ersC_pos hc₃ hα0 hR
  have hρ := ersRho_pos hc₃ hα0 hR
  exact div_pos (add_pos (div_pos Real.pi_pos (mul_pos (by norm_num) hC)) hρ) (by norm_num)

private lemma ersEta_ge_half_rho (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    ersRho c₃ α R / 2 ≤ ersEta c₃ α R := by
  rw [ersEta]
  have hC := ersC_pos hc₃ hα0 hR
  have hnn : 0 ≤ Real.pi / (2 * ersC c₃ α R) :=
    div_nonneg Real.pi_pos.le (by positivity)
  linarith

private lemma ersEta_le (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    ersEta c₃ α R ≤ ersEtaUB c₃ * Real.pi / 4 := by
  have hρ := ersRho_le hc₃ hα0 hR
  have hinv := ersC_inv_le_two hc₃ hα0 hR
  have hC := ersC_pos hc₃ hα0 hR
  have hrhs : (2 + c₃ / (2 * Real.pi ^ 2)) * Real.pi / 4 = Real.pi / 2 + c₃ / (8 * Real.pi) := by
    field_simp
    ring
  rw [ersEta, ersEtaUB, hrhs]
  have hA : Real.pi / (2 * ersC c₃ α R) / 2 ≤ Real.pi / 2 := by
    have he : Real.pi / (2 * ersC c₃ α R) / 2 = (Real.pi / 4) * (1 / ersC c₃ α R) := by ring
    rw [he]; nlinarith [hinv, Real.pi_pos]
  have hB : ersRho c₃ α R / 2 ≤ c₃ / (8 * Real.pi) := by
    have h2 : c₃ / (8 * Real.pi) = c₃ / (4 * Real.pi) / 2 := by rw [div_div]; ring
    rw [h2]; linarith [hρ]
  have hsplit : (Real.pi / (2 * ersC c₃ α R) + ersRho c₃ α R) / 2
      = Real.pi / (2 * ersC c₃ α R) / 2 + ersRho c₃ α R / 2 := by ring
  rw [hsplit]
  linarith [hA, hB, Real.pi_pos]

end BasicBounds2

section BasicBounds3

variable {c₁ c₂ c₃ α R : ℝ} {d : ℕ}

private lemma c₃_mul_ersC_ge (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    16 * Real.pi ^ 2 * ersLam α R ≤ c₃ * ersC c₃ α R := by
  have hlower := ersC_lower hc₃ hα0 hR
  have h1 : 16 * Real.pi ^ 2 * ersLam α R = c₃ * (ersK0 c₃ * ersLam α R) := by
    rw [ersK0]; field_simp
  have h2 : c₃ * (ersK0 c₃ * ersLam α R) ≤ c₃ * ersC c₃ α R := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hc₃)
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  linarith [h1]

private lemma ersR_eq (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    ersR c₃ α R = ersRho c₃ α R / 4 - Real.pi / (8 * ersC c₃ α R) := by
  have hC := ersC_pos hc₃ hα0 hR
  rw [ersR, ersEta]
  field_simp
  ring

private lemma ersR_ge (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    7 * c₃ / (128 * Real.pi * ersLam α R) ≤ ersR c₃ α R := by
  have h16 := c₃_mul_ersC_ge hc₃ hα0 hR
  have hΛ := ersLam_pos hα0 hR
  have hC := ersC_pos hc₃ hα0 hR
  rw [ersR_eq hc₃ hα0 hR, ersRho]
  have h1 : Real.pi / (8 * ersC c₃ α R) ≤ c₃ / (128 * Real.pi * ersLam α R) := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hC) (mul_pos (by positivity) hΛ)]
    nlinarith [h16, Real.pi_pos]
  have h2 : c₃ / (4 * Real.pi * ersLam α R) / 4 = 8 * c₃ / (128 * Real.pi * ersLam α R) := by
    rw [div_div]; ring
  rw [h2]
  have h3 : 8 * c₃ / (128 * Real.pi * ersLam α R) - 7 * c₃ / (128 * Real.pi * ersLam α R)
      = c₃ / (128 * Real.pi * ersLam α R) := by ring
  linarith [h1, h3]

private lemma ersR_pos (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) : 0 < ersR c₃ α R := by
  have h := ersR_ge hc₃ hα0 hR
  have hΛ := ersLam_pos hα0 hR
  have : 0 < 7 * c₃ / (128 * Real.pi * ersLam α R) := by positivity
  linarith

private lemma ersR_le (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    ersR c₃ α R ≤ c₃ / (16 * Real.pi) := by
  have hC := ersC_pos hc₃ hα0 hR
  rw [ersR_eq hc₃ hα0 hR, ersRho]
  have h1 : 0 ≤ Real.pi / (8 * ersC c₃ α R) :=
    div_nonneg Real.pi_pos.le (mul_nonneg (by norm_num) (le_of_lt hC))
  have he : c₃ / (4 * Real.pi * ersLam α R) / 4 = c₃ / (16 * Real.pi * ersLam α R) := by
    rw [div_div]; ring
  rw [he]
  have h2 : c₃ / (16 * Real.pi * ersLam α R) ≤ c₃ / (16 * Real.pi) := by
    apply div_le_div_of_nonneg_left (le_of_lt hc₃) (by positivity)
    nlinarith [ersLam_ge_one hα0 hR, Real.pi_pos]
  linarith

end BasicBounds3

section BasicBounds4

variable {c₁ c₂ c₃ α R : ℝ} {d : ℕ}

private lemma ersHV_eq : ersHV c₃ α R = ersEta c₃ α R * (4 * 1 / (Real.pi * ersEps c₃ α R)) := rfl

private lemma four_eta_div_pi_le (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    4 * ersEta c₃ α R / Real.pi ≤ ersEtaUB c₃ := by
  have hC := ersC_pos hc₃ hα0 hR
  have hinv := ersC_inv_le_two hc₃ hα0 hR
  have hρ := ersRho_le hc₃ hα0 hR
  have hΛ := ersLam_pos hα0 hR
  have he : 4 * ersEta c₃ α R / Real.pi = 1 / ersC c₃ α R + 2 * ersRho c₃ α R / Real.pi := by
    rw [ersEta]; field_simp; ring
  rw [he, ersEtaUB]
  have h2 : 2 * ersRho c₃ α R / Real.pi ≤ c₃ / (2 * Real.pi ^ 2) := by
    rw [ersRho]
    rw [show 2 * (c₃ / (4 * Real.pi * ersLam α R)) / Real.pi = c₃ / (2 * Real.pi ^ 2 * ersLam α R)
        by field_simp; ring]
    apply div_le_div_of_nonneg_left (le_of_lt hc₃) (by positivity)
    nlinarith [ersLam_ge_one hα0 hR, Real.pi_pos]
  linarith

private lemma log_two_div_ersEps (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    Real.log (2 / ersEps c₃ α R) = ersK0 c₃ * ersLam α R + Real.log 16 := by
  have hep := ersEps_pos (α := α) hc₃ (R := R)
  rw [Real.log_div (by norm_num) (ne_of_gt hep), log_ersEps hc₃ hα0 hR]
  have h16 : Real.log 16 = Real.log 2 + Real.log 8 := by
    rw [show (16 : ℝ) = 2 * 8 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith

private lemma ersH_pos (hc₁ : 0 < c₁) (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    0 < ersH d c₁ c₃ α R := by
  rw [ersH]
  have hη := ersEta_pos hc₃ hα0 hR
  have hep := ersEps_pos (α := α) hc₃ (R := R)
  have hnum : 0 < (c₁ / 2) ^ d := by positivity
  have hHVpos : 0 < ersHV c₃ α R := by rw [ersHV]; positivity
  exact div_pos hnum (by positivity)

private lemma ersH_le_one (hc₁ : 0 < c₁) (hc₁2 : c₁ ≤ 1 / 2) (hc₃ : 0 < c₃) (hα0 : 0 < α)
    (hR : 2 ≤ R) (h7 : 1 ≤ ersHV c₃ α R) : ersH d c₁ c₃ α R ≤ 1 := by
  rw [ersH]
  have hη := ersEta_pos hc₃ hα0 hR
  have hep := ersEps_pos (α := α) hc₃ (R := R)
  have hHVpos : 0 < ersHV c₃ α R := by rw [ersHV]; positivity
  rw [div_le_one (by positivity)]
  have hcp : (c₁ / 2) ^ d ≤ 1 := by
    have h0 : (0 : ℝ) ≤ c₁ / 2 := by positivity
    calc (c₁ / 2) ^ d ≤ 1 ^ d := pow_le_pow_left₀ h0 (by linarith) d
      _ = 1 := one_pow d
  have h4 : (4 : ℝ) * 20 ^ d * (ersHV c₃ α R) ^ d ≤ (4 : ℝ) * 20 ^ d * (ersHV c₃ α R) ^ d := le_refl _
  have h20 : (1 : ℝ) ≤ 4 * 20 ^ d * (ersHV c₃ α R) ^ d := by
    have h20d : (1 : ℝ) ≤ 20 ^ d := one_le_pow₀ (by norm_num)
    have hHVd : (1 : ℝ) ≤ (ersHV c₃ α R) ^ d := one_le_pow₀ h7
    nlinarith [h20d, hHVd, h7]
  linarith

end BasicBounds4

section BasicBounds5

variable {c₁ c₂ c₃ α R : ℝ} {d : ℕ}

private lemma log_four_eta_div_pi_le (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    Real.log (4 * ersEta c₃ α R / Real.pi) ≤ ersEtaUB c₃ := by
  have hη := ersEta_pos hc₃ hα0 hR
  have hpos : 0 < 4 * ersEta c₃ α R / Real.pi := by positivity
  have h1 := Real.log_le_sub_one_of_pos hpos
  have h2 := four_eta_div_pi_le hc₃ hα0 hR
  have h3 : 0 ≤ ersEtaUB c₃ := by rw [ersEtaUB]; positivity
  linarith

private lemma log_ersHV_le (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    Real.log (ersHV c₃ α R) ≤ ersEtaUB c₃ + (ersK0 c₃ * ersLam α R + Real.log 8) := by
  have hη := ersEta_pos hc₃ hα0 hR
  have hep := ersEps_pos (α := α) hc₃ (R := R)
  have hlog := log_four_eta_div_pi_le hc₃ hα0 hR
  have hfac : ersHV c₃ α R = (4 * ersEta c₃ α R / Real.pi) * (ersEps c₃ α R)⁻¹ := by
    rw [ersHV]; field_simp
  rw [hfac, Real.log_mul (by positivity) (by positivity)]
  have hlogeps : Real.log ((ersEps c₃ α R)⁻¹) = ersK0 c₃ * ersLam α R + Real.log 8 := by
    rw [Real.log_inv, log_ersEps hc₃ hα0 hR]; ring
  rw [hlogeps]
  linarith

private lemma log_one_div_ersH (hc₁ : 0 < c₁) (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    Real.log ((ersH d c₁ c₃ α R)⁻¹)
      = Real.log 4 + (d : ℝ) * Real.log 20 + (d : ℝ) * Real.log (ersHV c₃ α R)
        + (d : ℝ) * Real.log (2 / c₁) := by
  have hHpos := ersH_pos (d := d) hc₁ hc₃ hα0 hR
  have hη := ersEta_pos hc₃ hα0 hR
  have hep := ersEps_pos (α := α) hc₃ (R := R)
  have hHVpos : 0 < ersHV c₃ α R := by rw [ersHV]; positivity
  have hfac : (ersH d c₁ c₃ α R)⁻¹ = (4 * 20 ^ d) * ((ersHV c₃ α R) ^ d * (2 / c₁) ^ d) := by
    rw [ersH, inv_div, div_eq_mul_inv, ← inv_pow, inv_div]; ring
  have hnz1 : (4 * (20 : ℝ) ^ d) ≠ 0 := by positivity
  have hnz2 : ((ersHV c₃ α R) ^ d * (2 / c₁) ^ d) ≠ 0 := by positivity
  have hnz3 : (ersHV c₃ α R) ^ d ≠ 0 := by positivity
  have hnz4 : ((2 : ℝ) / c₁) ^ d ≠ 0 := by positivity
  rw [hfac, Real.log_mul hnz1 hnz2,
      Real.log_mul (by norm_num) (by positivity : (20 : ℝ) ^ d ≠ 0),
      Real.log_pow, Real.log_mul hnz3 hnz4, Real.log_pow, Real.log_pow]
  ring

private lemma log_two_e_div_ersH_le (hc₁ : 0 < c₁) (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    Real.log (2 * Real.exp 1 / ersH d c₁ c₃ α R)
      ≤ (d : ℝ) * ersK0 c₃ * ersLam α R + ersC1 d c₁ c₃ := by
  have hHpos := ersH_pos (d := d) hc₁ hc₃ hα0 hR
  have hlog1H := log_one_div_ersH (d := d) hc₁ hc₃ hα0 hR
  have hlogHV := log_ersHV_le hc₃ hα0 hR
  have hfac : 2 * Real.exp 1 / ersH d c₁ c₃ α R = (2 * Real.exp 1) * (ersH d c₁ c₃ α R)⁻¹ := by
    rw [div_eq_mul_inv]
  rw [hfac, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_exp, hlog1H, ersC1]
  have hd : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  nlinarith [hlogHV, hd]

private lemma ersC1_nonneg (hd : 1 ≤ d) (hc₁ : 0 < c₁) (hc₁2 : c₁ ≤ 1 / 2) (hc₃ : 0 < c₃) :
    0 ≤ ersC1 d c₁ c₃ := by
  rw [ersC1]
  have hl2c1 : 0 ≤ Real.log (2 / c₁) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hc₁]; linarith
  have hd' : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have heub : 0 ≤ ersEtaUB c₃ := by rw [ersEtaUB]; positivity
  have h1 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h2 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h3 : 0 ≤ Real.log 20 := Real.log_nonneg (by norm_num)
  have h4 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have h5 := mul_nonneg hd' heub
  have h6 := mul_nonneg hd' hl2c1
  have h7 := mul_nonneg hd' h3
  have h8 := mul_nonneg hd' h4
  linarith

private lemma ersCx_pos (hd : 1 ≤ d) (hc₁ : 0 < c₁) (hc₁2 : c₁ ≤ 1 / 2) (hc₃ : 0 < c₃) :
    0 < ersCx d c₁ c₃ := by
  rw [ersCx]
  have h1 := ersC1_nonneg hd hc₁ hc₁2 hc₃
  have h2 : 0 < ersK0 c₃ := ersK0_pos hc₃
  have h3 : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have h4 : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have h5 : 0 ≤ (d : ℝ) * ersK0 c₃ := mul_nonneg h4 (le_of_lt h2)
  have h6 : 0 ≤ 64 * ((d : ℝ) * ersK0 c₃ + ersC1 d c₁ c₃) :=
    mul_nonneg (by norm_num) (by linarith)
  have h7 : 0 ≤ 1024 * (ersK0 c₃ + Real.log 16) :=
    mul_nonneg (by norm_num) (by linarith)
  linarith

private lemma ersXv_le (hd : 1 ≤ d) (hc₁ : 0 < c₁) (hc₁2 : c₁ ≤ 1 / 2) (hc₃ : 0 < c₃)
    (hα0 : 0 < α) (hR : 2 ≤ R) :
    ersXv d c₁ c₃ α R ≤ ersCx d c₁ c₃ * ersLam α R * Real.exp (3 * (ersK0 c₃ * ersLam α R)) := by
  have hep := ersEps_pos (α := α) hc₃ (R := R)
  have hΛ := ersLam_pos hα0 hR
  have hK := ersK0_pos hc₃
  have hΛ1 : 1 ≤ ersLam α R := ersLam_ge_one hα0 hR
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hlog16 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  have hKΛ : 0 < ersK0 c₃ * ersLam α R := mul_pos hK hΛ
  have hE3 : (ersEps c₃ α R)⁻¹ ^ 3 = 512 * Real.exp (3 * (ersK0 c₃ * ersLam α R)) := by
    rw [ersEps_inv hc₃, mul_pow, ← Real.exp_nat_mul]; norm_num
  have hE2 : (ersEps c₃ α R)⁻¹ ^ 2 = 64 * Real.exp (2 * (ersK0 c₃ * ersLam α R)) := by
    rw [ersEps_inv hc₃, mul_pow, ← Real.exp_nat_mul]; norm_num
  have hE1 : (1 : ℝ) ≤ Real.exp (3 * (ersK0 c₃ * ersLam α R)) :=
    Real.one_le_exp (by nlinarith)
  have hE23 : Real.exp (2 * (ersK0 c₃ * ersLam α R)) ≤ Real.exp (3 * (ersK0 c₃ * ersLam α R)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hC1nn : 0 ≤ ersC1 d c₁ c₃ := ersC1_nonneg hd hc₁ hc₁2 hc₃
  have hb1 : 2 * (512 * Real.exp (3 * (ersK0 c₃ * ersLam α R)))
        * (ersK0 c₃ * ersLam α R + Real.log 16)
      ≤ 1024 * (ersK0 c₃ + Real.log 16) * ersLam α R
          * Real.exp (3 * (ersK0 c₃ * ersLam α R)) := by
    have hfac : 2 * (512 * Real.exp (3 * (ersK0 c₃ * ersLam α R)))
        * (ersK0 c₃ * ersLam α R + Real.log 16)
        = 1024 * Real.exp (3 * (ersK0 c₃ * ersLam α R))
          * (ersK0 c₃ * ersLam α R + Real.log 16) := by ring
    rw [hfac]
    have hkey : ersK0 c₃ * ersLam α R + Real.log 16 ≤ (ersK0 c₃ + Real.log 16) * ersLam α R := by
      nlinarith [hlog16, hΛ1, hK, hΛ]
    have hstep := mul_le_mul_of_nonneg_left hkey
      (by positivity : (0 : ℝ) ≤ 1024 * Real.exp (3 * (ersK0 c₃ * ersLam α R)))
    calc 1024 * Real.exp (3 * (ersK0 c₃ * ersLam α R))
            * (ersK0 c₃ * ersLam α R + Real.log 16)
        ≤ 1024 * Real.exp (3 * (ersK0 c₃ * ersLam α R))
            * ((ersK0 c₃ + Real.log 16) * ersLam α R) := hstep
      _ = 1024 * (ersK0 c₃ + Real.log 16) * ersLam α R
            * Real.exp (3 * (ersK0 c₃ * ersLam α R)) := by ring
  have hb2 : 64 * Real.exp (2 * (ersK0 c₃ * ersLam α R))
        * Real.log (2 * Real.exp 1 / ersH d c₁ c₃ α R)
      ≤ 64 * ((d : ℝ) * ersK0 c₃ + ersC1 d c₁ c₃) * ersLam α R
          * Real.exp (3 * (ersK0 c₃ * ersLam α R)) := by
    have hlog := log_two_e_div_ersH_le (d := d) hc₁ hc₃ hα0 hR
    have hkey : (d : ℝ) * ersK0 c₃ * ersLam α R + ersC1 d c₁ c₃
        ≤ ((d : ℝ) * ersK0 c₃ + ersC1 d c₁ c₃) * ersLam α R := by
      nlinarith [hC1nn, hΛ1, hdnn, hK, hΛ]
    have hstep1 := mul_le_mul_of_nonneg_left hlog
      (by positivity : (0 : ℝ) ≤ 64 * Real.exp (2 * (ersK0 c₃ * ersLam α R)))
    have hstep2 := mul_le_mul_of_nonneg_left hkey
      (by positivity : (0 : ℝ) ≤ 64 * Real.exp (2 * (ersK0 c₃ * ersLam α R)))
    have hstep3 := mul_le_mul_of_nonneg_left hE23
      (by positivity : (0 : ℝ) ≤ 64 * (((d : ℝ) * ersK0 c₃ + ersC1 d c₁ c₃) * ersLam α R))
    calc 64 * Real.exp (2 * (ersK0 c₃ * ersLam α R))
            * Real.log (2 * Real.exp 1 / ersH d c₁ c₃ α R)
        ≤ 64 * Real.exp (2 * (ersK0 c₃ * ersLam α R))
            * ((d : ℝ) * ersK0 c₃ * ersLam α R + ersC1 d c₁ c₃) := hstep1
      _ ≤ 64 * Real.exp (2 * (ersK0 c₃ * ersLam α R))
            * (((d : ℝ) * ersK0 c₃ + ersC1 d c₁ c₃) * ersLam α R) := hstep2
      _ = 64 * (((d : ℝ) * ersK0 c₃ + ersC1 d c₁ c₃) * ersLam α R)
            * Real.exp (2 * (ersK0 c₃ * ersLam α R)) := by ring
      _ ≤ 64 * (((d : ℝ) * ersK0 c₃ + ersC1 d c₁ c₃) * ersLam α R)
            * Real.exp (3 * (ersK0 c₃ * ersLam α R)) := hstep3
      _ = 64 * ((d : ℝ) * ersK0 c₃ + ersC1 d c₁ c₃) * ersLam α R
            * Real.exp (3 * (ersK0 c₃ * ersLam α R)) := by ring
  have hb0 : (1 : ℝ) ≤ 1 * ersLam α R * Real.exp (3 * (ersK0 c₃ * ersLam α R)) := by
    nlinarith [hΛ1, hE1]
  rw [ersXv, hE3, hE2, log_two_div_ersEps hc₃ hα0 hR]
  rw [ersCx]
  linarith [hb0, hb1, hb2]

end BasicBounds5

section KappaBounds

variable {c₁ c₂ c₃ α R : ℝ} {d : ℕ}

private lemma exp_neg_natmul (a : ℝ) (n : ℕ) :
    (Real.exp a) ^ (-(n : ℝ)) = Real.exp (-((n : ℝ) * a)) := by
  rw [Real.rpow_neg (Real.exp_pos a).le, Real.rpow_natCast, ← Real.exp_nat_mul, Real.exp_neg]

private lemma ersXv_ge_one (hc₁ : 0 < c₁) (hc₁2 : c₁ ≤ 1 / 2) (hc₃ : 0 < c₃) (hα0 : 0 < α)
    (hR : 2 ≤ R) (h7 : 1 ≤ ersHV c₃ α R) : 1 ≤ ersXv d c₁ c₃ α R := by
  rw [ersXv]
  have hep := ersEps_pos (α := α) hc₃ (R := R)
  have hH := ersH_le_one (d := d) hc₁ hc₁2 hc₃ hα0 hR h7
  have hHpos := ersH_pos (d := d) hc₁ hc₃ hα0 hR
  have hlog1 : 0 ≤ Real.log (2 / ersEps c₃ α R) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hep]; nlinarith [ersEps_le_eighth hc₃ hα0 hR]
  have hlog2 : 0 ≤ Real.log (2 * Real.exp 1 / ersH d c₁ c₃ α R) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hHpos]
    have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith
  have h3 : 0 ≤ (ersEps c₃ α R)⁻¹ ^ 3 := by positivity
  have h2 : 0 ≤ (ersEps c₃ α R)⁻¹ ^ 2 := by positivity
  have hA : 0 ≤ 2 * (ersEps c₃ α R)⁻¹ ^ 3 * Real.log (2 / ersEps c₃ α R) :=
    mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * (ersEps c₃ α R)⁻¹ ^ 3) hlog1
  have hB : 0 ≤ (ersEps c₃ α R)⁻¹ ^ 2 * Real.log (2 * Real.exp 1 / ersH d c₁ c₃ α R) :=
    mul_nonneg h2 hlog2
  linarith

private lemma ersKap_ge (hd : 1 ≤ d) (hc₁ : 0 < c₁) (hc₁2 : c₁ ≤ 1 / 2) (hc₃ : 0 < c₃)
    (hα0 : 0 < α) (hR : 2 ≤ R) (h7 : 1 ≤ ersHV c₃ α R) :
    (ersCx d c₁ c₃) ^ (-(d : ℝ)) * (ersLam α R) ^ (-(d : ℝ))
      * Real.exp (-(3 * ((d : ℝ) * (ersK0 c₃ * ersLam α R)))) ≤ ersKap d c₁ c₃ α R := by
  have hXle := ersXv_le hd hc₁ hc₁2 hc₃ hα0 hR
  have hXge := ersXv_ge_one (d := d) hc₁ hc₁2 hc₃ hα0 hR h7
  have hΛ := ersLam_pos hα0 hR
  have hcxpos : 0 < ersCx d c₁ c₃ := ersCx_pos hd hc₁ hc₁2 hc₃
  have hBpos : 0 < ersCx d c₁ c₃ * ersLam α R * Real.exp (3 * (ersK0 c₃ * ersLam α R)) := by
    positivity
  have hXpos : 0 < ersXv d c₁ c₃ α R := lt_of_lt_of_le one_pos hXge
  have step1 : (ersCx d c₁ c₃ * ersLam α R * Real.exp (3 * (ersK0 c₃ * ersLam α R)))⁻¹
      ≤ (ersXv d c₁ c₃ α R)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hXpos hXle
  have step2 : ((ersCx d c₁ c₃ * ersLam α R * Real.exp (3 * (ersK0 c₃ * ersLam α R)))⁻¹) ^ d
      ≤ (ersXv d c₁ c₃ α R)⁻¹ ^ d :=
    pow_le_pow_left₀ (inv_nonneg.mpr (le_of_lt hBpos)) step1 d
  have heq : (ersCx d c₁ c₃) ^ (-(d : ℝ)) * (ersLam α R) ^ (-(d : ℝ))
      * Real.exp (-(3 * ((d : ℝ) * (ersK0 c₃ * ersLam α R))))
      = ((ersCx d c₁ c₃ * ersLam α R * Real.exp (3 * (ersK0 c₃ * ersLam α R)))⁻¹) ^ d := by
    rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg (le_of_lt hBpos) (d : ℝ)]
    rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity)]
    rw [exp_neg_natmul]
    rw [show -((d : ℝ) * (3 * (ersK0 c₃ * ersLam α R))) = -(3 * ((d : ℝ) * (ersK0 c₃ * ersLam α R)))
        by ring]
  rw [ersKap, heq]
  exact step2

private lemma ersKap_nonneg (hd : 1 ≤ d) (hc₁ : 0 < c₁) (hc₁2 : c₁ ≤ 1 / 2) (hc₃ : 0 < c₃)
    (hα0 : 0 < α) (hR : 2 ≤ R) (h7 : 1 ≤ ersHV c₃ α R) : 0 ≤ ersKap d c₁ c₃ α R := by
  rw [ersKap]
  have hXge := ersXv_ge_one (d := d) hc₁ hc₁2 hc₃ hα0 hR h7
  have hXpos : 0 < ersXv d c₁ c₃ α R := lt_of_lt_of_le one_pos hXge
  exact pow_nonneg (inv_nonneg.mpr (le_of_lt hXpos)) d

private lemma ersKap_le_one (hd : 1 ≤ d) (hc₁ : 0 < c₁) (hc₁2 : c₁ ≤ 1 / 2) (hc₃ : 0 < c₃)
    (hα0 : 0 < α) (hR : 2 ≤ R) (h7 : 1 ≤ ersHV c₃ α R) : ersKap d c₁ c₃ α R ≤ 1 := by
  rw [ersKap]
  have hXge := ersXv_ge_one (d := d) hc₁ hc₁2 hc₃ hα0 hR h7
  have hXpos : 0 < ersXv d c₁ c₃ α R := lt_of_lt_of_le one_pos hXge
  calc (ersXv d c₁ c₃ α R)⁻¹ ^ d ≤ 1 ^ d :=
        pow_le_pow_left₀ (inv_nonneg.mpr (le_of_lt hXpos)) (inv_le_one_of_one_le₀ hXge) d
    _ = 1 := one_pow d

end KappaBounds

section Limits

open Filter
open scoped Topology

private lemma tendsto_log2R : Tendsto (fun R : ℝ => Real.log (2 + R)) atTop atTop :=
  Real.tendsto_log_atTop.comp
    (Filter.tendsto_atTop_add_const_left atTop 2 Filter.tendsto_id)

private lemma tendsto_lam {α : ℝ} (hα0 : 0 < α) :
    Tendsto (fun R : ℝ => ersLam α R) atTop atTop :=
  (tendsto_rpow_atTop hα0).comp tendsto_log2R

private lemma tendsto_rpow_alpha_sub_one {α : ℝ} (hα1 : α < 1) :
    Tendsto (fun R : ℝ => (Real.log (2 + R)) ^ (α - 1)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 - α by linarith)).comp tendsto_log2R
  refine h.congr' ?_
  filter_upwards with R
  simp only [Function.comp_apply]
  ring_nf

private lemma tendsto_lam_div_log {α : ℝ} (hα1 : α < 1) :
    Tendsto (fun R : ℝ => ersLam α R / Real.log R) atTop (𝓝 0) := by
  have hpow0 := tendsto_rpow_alpha_sub_one hα1
  have hpow : Tendsto (fun R : ℝ => 2 * (Real.log (2 + R)) ^ (α - 1)) atTop (𝓝 0) := by
    simpa using hpow0.const_mul 2
  have hbound : ∀ᶠ R : ℝ in atTop,
      ersLam α R / Real.log R ≤ 2 * (Real.log (2 + R)) ^ (α - 1) := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ),
      tendsto_log2R.eventually_ge_atTop 2] with R hR hlog2
    have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
    have hx : (0 : ℝ) < Real.log (2 + R) := by linarith
    have hhalf : Real.log (2 + R) / 2 ≤ Real.log R := by
      have h1 : Real.log (2 + R) = Real.log R + Real.log ((2 + R) / R) := by
        rw [← Real.log_mul (by linarith : (R : ℝ) ≠ 0)
          (by positivity : ((2 + R) / R) ≠ 0)]
        congr 1
        field_simp
      have h2 : Real.log ((2 + R) / R) ≤ 1 := by
        rw [show (2 + R) / R = 1 + 2 / R by field_simp; ring]
        calc Real.log (1 + 2 / R) ≤ 1 + 2 / R - 1 := Real.log_le_sub_one_of_pos (by positivity)
          _ = 2 / R := by ring
          _ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    rw [ersLam, div_le_iff₀ hlogR]
    have hxx : (Real.log (2 + R)) ^ α = (Real.log (2 + R)) ^ (α - 1) * Real.log (2 + R) := by
      conv_lhs => rw [show α = (α - 1) + 1 by ring]
      rw [Real.rpow_add hx, Real.rpow_one]
    rw [hxx]
    nlinarith [Real.rpow_nonneg (le_of_lt hx) (α - 1), hhalf]
  have hnn : ∀ᶠ R : ℝ in atTop, 0 ≤ ersLam α R / Real.log R := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with R hR
    exact div_nonneg (by rw [ersLam]; exact Real.rpow_nonneg (Real.log_nonneg (by linarith)) α)
      (le_of_lt (Real.log_pos (by linarith)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hpow hnn hbound

private lemma tendsto_log_div_self :
    Tendsto (fun s : ℝ => Real.log s / s) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero

private lemma tendsto_loglog2R_div_logR :
    Tendsto (fun R : ℝ => Real.log (Real.log (2 + R)) / Real.log R) atTop (𝓝 0) := by
  have hcomp : Tendsto (fun R : ℝ => Real.log (Real.log (2 + R)) / Real.log (2 + R))
      atTop (𝓝 0) := tendsto_log_div_self.comp tendsto_log2R
  have hbound : ∀ᶠ R : ℝ in atTop,
      Real.log (Real.log (2 + R)) / Real.log R ≤ 2 * (Real.log (Real.log (2 + R)) / Real.log (2 + R)) := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ),
      tendsto_log2R.eventually_ge_atTop 2] with R hR hlog2
    have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
    have hx : (0 : ℝ) < Real.log (2 + R) := by linarith
    have hhalf : Real.log (2 + R) / 2 ≤ Real.log R := by
      have h1 : Real.log (2 + R) = Real.log R + Real.log ((2 + R) / R) := by
        rw [← Real.log_mul (by linarith : (R : ℝ) ≠ 0)
          (by positivity : ((2 + R) / R) ≠ 0)]
        congr 1
        field_simp
      have h2 : Real.log ((2 + R) / R) ≤ 1 := by
        rw [show (2 + R) / R = 1 + 2 / R by field_simp; ring]
        calc Real.log (1 + 2 / R) ≤ 1 + 2 / R - 1 := Real.log_le_sub_one_of_pos (by positivity)
          _ = 2 / R := by ring
          _ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    have hnn1 : 0 ≤ Real.log (Real.log (2 + R)) := Real.log_nonneg (by linarith)
    rw [div_le_iff₀ hlogR]
    have hkey : (1 : ℝ) ≤ 2 * Real.log R / Real.log (2 + R) := by
      rw [le_div_iff₀ hx]; linarith
    have hrw : 2 * (Real.log (Real.log (2 + R)) / Real.log (2 + R)) * Real.log R
        = Real.log (Real.log (2 + R)) * (2 * Real.log R / Real.log (2 + R)) := by ring
    rw [hrw]
    simpa using mul_le_mul_of_nonneg_left hkey hnn1
  have hnn : ∀ᶠ R : ℝ in atTop,
      0 ≤ Real.log (Real.log (2 + R)) / Real.log R := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with R hR
    exact div_nonneg (Real.log_nonneg (by have := log2R_ge_one hR; linarith))
      (le_of_lt (Real.log_pos (by linarith)))
  have h2comp : Tendsto (fun R : ℝ => 2 * (Real.log (Real.log (2 + R)) / Real.log (2 + R)))
      atTop (𝓝 0) := by simpa using hcomp.const_mul 2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2comp hnn hbound

private lemma tendsto_loglam_div_log {α : ℝ} (hα0 : 0 < α) :
    Tendsto (fun R : ℝ => Real.log (ersLam α R) / Real.log R) atTop (𝓝 0) := by
  have h : Tendsto (fun R : ℝ => α * (Real.log (Real.log (2 + R)) / Real.log R))
      atTop (𝓝 0) := by simpa using (tendsto_loglog2R_div_logR.const_mul α)
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with R hR
  have hx : (0 : ℝ) < Real.log (2 + R) := Real.log_pos (by linarith)
  rw [ersLam, Real.log_rpow hx]
  ring

private lemma log_eight_gt_two : (2 : ℝ) < Real.log 8 := by
  have h : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  rw [h]; linarith [Real.log_two_gt_d9]

private lemma tendsto_log_arg_div_log {α : ℝ} (hα1 : α < 1) :
    Tendsto (fun R : ℝ => Real.log (ersLam α R + Real.log R + 1) / Real.log R)
      atTop (𝓝 0) := by
  have hll : Tendsto (fun R : ℝ => Real.log (Real.log R) / Real.log R) atTop (𝓝 0) :=
    tendsto_log_div_self.comp Real.tendsto_log_atTop
  have h1 : Tendsto (fun R : ℝ => Real.log 3 / Real.log R) atTop (𝓝 0) := by
    have h := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    simpa [div_eq_mul_inv] using h.const_mul (Real.log 3)
  have hsum : Tendsto (fun R : ℝ => (Real.log 3 + Real.log (Real.log R)) / Real.log R)
      atTop (𝓝 0) := by
    have := h1.add hll
    simpa [add_div] using this
  have hbound : ∀ᶠ R : ℝ in atTop,
      Real.log (ersLam α R + Real.log R + 1) / Real.log R
        ≤ (Real.log 3 + Real.log (Real.log R)) / Real.log R := by
    filter_upwards [Filter.eventually_ge_atTop (8 : ℝ)] with R hR
    have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
    have hlogR2 : 2 ≤ Real.log R :=
      le_trans (le_of_lt log_eight_gt_two) (Real.log_le_log (by norm_num) hR)
    have hlog2R : Real.log (2 + R) ≤ Real.log R + 1 := by
      have h1 : Real.log (2 + R) = Real.log R + Real.log ((2 + R) / R) := by
        rw [← Real.log_mul (by linarith : (R : ℝ) ≠ 0)
          (by positivity : ((2 + R) / R) ≠ 0)]
        congr 1
        field_simp
      have h2 : Real.log ((2 + R) / R) ≤ 1 := by
        rw [show (2 + R) / R = 1 + 2 / R by field_simp; ring]
        calc Real.log (1 + 2 / R) ≤ 1 + 2 / R - 1 := Real.log_le_sub_one_of_pos (by positivity)
          _ = 2 / R := by ring
          _ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    have hΛle : ersLam α R ≤ Real.log (2 + R) := ersLam_le_log (le_of_lt hα1) (by linarith)
    have hΛnn : 0 ≤ ersLam α R := by
      rw [ersLam]; exact Real.rpow_nonneg (Real.log_nonneg (by linarith)) α
    have harg : ersLam α R + Real.log R + 1 ≤ 3 * Real.log R := by
      nlinarith [hΛle, hlog2R, hlogR2]
    have hargpos : 0 < ersLam α R + Real.log R + 1 := by linarith
    have hlog3R : Real.log (3 * Real.log R) = Real.log 3 + Real.log (Real.log R) :=
      Real.log_mul (by norm_num) (ne_of_gt hlogR)
    rw [← hlog3R]
    exact div_le_div_of_nonneg_right (Real.log_le_log hargpos harg) (le_of_lt hlogR)
  have hnn : ∀ᶠ R : ℝ in atTop,
      0 ≤ Real.log (ersLam α R + Real.log R + 1) / Real.log R := by
    filter_upwards [Filter.eventually_ge_atTop (3 : ℝ)] with R hR
    have hΛnn : 0 ≤ ersLam α R := by
      rw [ersLam]; exact Real.rpow_nonneg (Real.log_nonneg (by linarith)) α
    have hlogR : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
    exact div_nonneg (Real.log_nonneg (by linarith)) hlogR
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum hnn hbound

private lemma tendsto_exp_lam_div_lam {c₃ α : ℝ} (hc₃ : 0 < c₃) (hα0 : 0 < α) :
    Tendsto (fun R : ℝ => Real.exp (ersK0 c₃ * ersLam α R) / ersLam α R) atTop atTop := by
  have h1 : Tendsto (fun R : ℝ => ersK0 c₃ * ersLam α R) atTop atTop :=
    (tendsto_lam hα0).const_mul_atTop (ersK0_pos hc₃)
  have h2 : Tendsto (fun s : ℝ => Real.exp s / s) atTop atTop := by
    simpa using tendsto_exp_div_rpow_atTop (1 : ℝ)
  have h3 : Tendsto (fun R : ℝ => Real.exp (ersK0 c₃ * ersLam α R) / (ersK0 c₃ * ersLam α R))
      atTop atTop := h2.comp h1
  have h4 : Tendsto (fun R : ℝ => (ersK0 c₃) *
      (Real.exp (ersK0 c₃ * ersLam α R) / (ersK0 c₃ * ersLam α R))) atTop atTop :=
    h3.const_mul_atTop (ersK0_pos hc₃)
  refine h4.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with R hR
  have hΛ := ersLam_pos hα0 hR
  have hK := ersK0_pos hc₃
  field_simp

end Limits

section ParamConds

variable {c₁ c₂ c₃ α R : ℝ} {d : ℕ}

private lemma cC_ge (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    2 * Real.pi ^ 2 * ersLam α R ≤ (ersC c₃ α R) * c₃ := by
  have hCge := ersC_lower hc₃ hα0 hR
  have hΛ := ersLam_pos hα0 hR
  have h1 : (ersK0 c₃ * ersLam α R) * c₃ = 16 * Real.pi ^ 2 * ersLam α R := by
    rw [ersK0]; field_simp
  have h2 : (ersK0 c₃ * ersLam α R) * c₃ ≤ (ersC c₃ α R) * c₃ := by
    apply mul_le_mul_of_nonneg_right _ (le_of_lt hc₃)
    linarith [hCge, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hpinn : 0 ≤ Real.pi ^ 2 * ersLam α R := by positivity
  linarith [h1, h2, hpinn]

private lemma ers_lens (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    1 ≤ ersEta c₃ α R * ((2 * 1 / Real.pi) * ersC c₃ α R) := by
  have hC := ersC_pos hc₃ hα0 hR
  have hΛ := ersLam_pos hα0 hR
  have hkey := cC_ge hc₃ hα0 hR
  have he : ersEta c₃ α R * ((2 * 1 / Real.pi) * ersC c₃ α R)
      = (1 + 2 * (ersC c₃ α R) * (ersRho c₃ α R) / Real.pi) / 2 := by
    rw [ersEta]; field_simp
  rw [he]
  have hcr : 1 ≤ 2 * (ersC c₃ α R) * (ersRho c₃ α R) / Real.pi := by
    rw [ersRho]
    rw [show 2 * (ersC c₃ α R) * (c₃ / (4 * Real.pi * ersLam α R)) / Real.pi
        = (ersC c₃ α R) * c₃ / (2 * Real.pi ^ 2 * ersLam α R) by field_simp; ring]
    rw [le_div_iff₀ (by positivity)]
    linarith [hkey]
  linarith

private lemma ers_strip (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    4 * Real.pi * (ersEta c₃ α R * 1 + ersR c₃ α R) ≤ c₃ * (Real.log (2 + R)) ^ (-α) := by
  have hC := ersC_pos hc₃ hα0 hR
  have hΛ := ersLam_pos hα0 hR
  have hkey := cC_ge hc₃ hα0 hR
  have hlogpos : 0 < Real.log (2 + R) := Real.log_pos (by linarith)
  have hrw : (Real.log (2 + R)) ^ (-α) = 1 / ersLam α R := by
    rw [Real.rpow_neg (le_of_lt hlogpos), ersLam, one_div]
  rw [hrw]
  rw [show c₃ * (1 / ersLam α R) = c₃ / ersLam α R by ring]
  rw [le_div_iff₀ hΛ]
  have he : ersEta c₃ α R * 1 + ersR c₃ α R = (ersEta c₃ α R + ersRho c₃ α R) / 2 := by
    rw [ersR]; ring
  rw [he]
  have hcalc : 4 * Real.pi * ((ersEta c₃ α R + ersRho c₃ α R) / 2) * ersLam α R
      = Real.pi ^ 2 * ersLam α R / (2 * ersC c₃ α R) + 3 * c₃ / 4 := by
    rw [ersEta, ersRho]; field_simp; ring
  rw [hcalc]
  have h2 : Real.pi ^ 2 * ersLam α R / (2 * ersC c₃ α R) ≤ c₃ / 4 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [hkey]
  linarith

private lemma ers_cube (hc₁ : 0 < c₁) (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    (ersHV c₃ α R) ^ d * (2 * (20 ^ d * ersH d c₁ c₃ α R)) ≤ (c₁ / 2) ^ d := by
  have hη := ersEta_pos hc₃ hα0 hR
  have hep := ersEps_pos (α := α) hc₃ (R := R)
  have hHVpos : 0 < ersHV c₃ α R := by rw [ersHV]; positivity
  have heq : (ersHV c₃ α R) ^ d * (2 * (20 ^ d * ersH d c₁ c₃ α R)) = (c₁ / 2) ^ d / 2 := by
    rw [ersH]
    field_simp
    ring
  rw [heq]
  have hnn : 0 ≤ (c₁ / 2) ^ d := by positivity
  linarith

end ParamConds

section BoundB

variable {c₁ c₂ c₃ α R : ℝ} {d : ℕ}

private lemma two_etaR_le (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    2 * (ersEta c₃ α R * 1 + ersR c₃ α R) ≤ ersEtaR c₃ := by
  have hη := ersEta_le hc₃ hα0 hR
  have hρ := ersRho_le hc₃ hα0 hR
  have he : 2 * (ersEta c₃ α R * 1 + ersR c₃ α R) = ersEta c₃ α R + ersRho c₃ α R := by
    rw [ersR]; ring
  rw [he, ersEtaR]
  linarith

private lemma exp_nat_mul_eq (x : ℝ) (n : ℕ) :
    (Real.exp x) ^ n = Real.exp ((n : ℝ) * x) := (Real.exp_nat_mul x n).symm

private lemma CB_eq (d : ℕ) (c₁ c₃ : ℝ) :
    (8 * ersEtaUB c₃) ^ d * 2 ^ d * 2 * (128 / c₁) ^ d = ersCB d c₁ c₃ := by
  rw [ersCB]
  have h : (2048 : ℝ) = 8 * 2 * 128 := by norm_num
  rw [h, mul_div_assoc]
  rw [mul_pow, div_pow, mul_pow, mul_pow, mul_pow, div_pow]
  ring

private lemma ersB_le (hd : 1 ≤ d) (hc₁ : 0 < c₁) (hc₁2 : c₁ ≤ 1 / 2) (hc₃ : 0 < c₃)
    (hα0 : 0 < α) (hR : 2 ≤ R) (h7 : 1 ≤ ersHV c₃ α R) :
    ersB d c₁ c₃ α R ≤ ersCB d c₁ c₃ * Real.exp (2 * ((d : ℝ) * (ersK0 c₃ * ersLam α R))) := by
  have hκle := ersKap_le_one hd hc₁ hc₁2 hc₃ hα0 hR h7
  have hep := ersEps_pos (α := α) hc₃ (R := R)
  have hδ := ersEps_le_eighth hc₃ hα0 hR
  have h1e : 0 < 1 - ersEps c₃ α R := by linarith
  have hfour := four_eta_div_pi_le hc₃ hα0 hR
  have hη := ersEta_pos hc₃ hα0 hR
  have hA : ersEta c₃ α R * (4 * 1 / (Real.pi * ersEps c₃ α R))
      ≤ ersEtaUB c₃ * (8 * Real.exp (ersK0 c₃ * ersLam α R)) := by
    have heq : ersEta c₃ α R * (4 * 1 / (Real.pi * ersEps c₃ α R))
        = (4 * ersEta c₃ α R / Real.pi) * (ersEps c₃ α R)⁻¹ := by field_simp
    rw [heq, ersEps_inv hc₃]
    exact mul_le_mul_of_nonneg_right hfour (by positivity)
  have hAd : (ersEta c₃ α R * (4 * 1 / (Real.pi * ersEps c₃ α R))) ^ d
      ≤ (8 * ersEtaUB c₃) ^ d * Real.exp ((d : ℝ) * (ersK0 c₃ * ersLam α R)) := by
    have h1 : (ersEtaUB c₃ * (8 * Real.exp (ersK0 c₃ * ersLam α R))) ^ d
        = (8 * ersEtaUB c₃) ^ d * Real.exp ((d : ℝ) * (ersK0 c₃ * ersLam α R)) := by
      rw [show ersEtaUB c₃ * (8 * Real.exp (ersK0 c₃ * ersLam α R))
          = (8 * ersEtaUB c₃) * Real.exp (ersK0 c₃ * ersLam α R) by ring, mul_pow,
          exp_nat_mul_eq]
    exact le_trans (pow_le_pow_left₀ (by positivity) hA d) (le_of_eq h1)
  have hinner : Real.pi / (ersEta c₃ α R * (1 - ersEps c₃ α R))
        * (ersEta c₃ α R * (4 * 1 / (Real.pi * ersEps c₃ α R))) / (c₁ / 2)
      = 8 / (ersEps c₃ α R * (1 - ersEps c₃ α R) * c₁) := by
    field_simp
    ring
  have hXrat : ((ersEta c₃ α R * ((1 - ersEps c₃ α R) * 1 / Real.pi)) ^ (-(d : ℝ))
        * (ersEta c₃ α R * (4 * 1 / (Real.pi * ersEps c₃ α R))) ^ d
        / (2 * (c₁ / 4)) ^ d) = (8 / (ersEps c₃ α R * (1 - ersEps c₃ α R) * c₁)) ^ d := by
    have h1 : (ersEta c₃ α R * ((1 - ersEps c₃ α R) * 1 / Real.pi)) ^ (-(d : ℝ))
        = (Real.pi / (ersEta c₃ α R * (1 - ersEps c₃ α R))) ^ d := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← inv_pow]
      congr 1
      rw [inv_eq_one_div]
      field_simp
    rw [h1, show 2 * (c₁ / 4) = c₁ / 2 by ring, ← mul_pow, ← div_pow, hinner]
  have hXrat1 : 1 ≤ (8 / (ersEps c₃ α R * (1 - ersEps c₃ α R) * c₁)) ^ d := by
    apply one_le_pow₀
    rw [le_div_iff₀ (mul_pos (mul_pos hep h1e) hc₁)]
    nlinarith [mul_nonneg (le_of_lt hep) (le_of_lt h1e), mul_nonneg (le_of_lt hc₁) (le_of_lt hep),
      mul_le_mul hδ (by linarith : (1 - ersEps c₃ α R) ≤ 1) (by linarith) (by norm_num)]
  have hXratub : (8 / (ersEps c₃ α R * (1 - ersEps c₃ α R) * c₁)) ^ d
      ≤ (128 / c₁) ^ d * Real.exp ((d : ℝ) * (ersK0 c₃ * ersLam α R)) := by
    have hle : 8 / (ersEps c₃ α R * (1 - ersEps c₃ α R) * c₁)
        ≤ (128 / c₁) * Real.exp (ersK0 c₃ * ersLam α R) := by
      have hb : 8 / (ersEps c₃ α R * (1 - ersEps c₃ α R) * c₁)
          = (8 / (ersEps c₃ α R * c₁)) * (1 / (1 - ersEps c₃ α R)) := by field_simp
      have h2 : 1 / (1 - ersEps c₃ α R) ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      have h3 : (8 / (ersEps c₃ α R * c₁)) * (1 / (1 - ersEps c₃ α R))
          ≤ (8 / (ersEps c₃ α R * c₁)) * 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have h4 : (8 / (ersEps c₃ α R * c₁)) * 2
          = (128 / c₁) * Real.exp (ersK0 c₃ * ersLam α R) := by
        rw [show 8 / (ersEps c₃ α R * c₁) * 2 = 16 * (ersEps c₃ α R)⁻¹ / c₁ by
          field_simp; ring]
        rw [ersEps_inv hc₃]; ring
      calc 8 / (ersEps c₃ α R * (1 - ersEps c₃ α R) * c₁)
          = (8 / (ersEps c₃ α R * c₁)) * (1 / (1 - ersEps c₃ α R)) := hb
        _ ≤ (8 / (ersEps c₃ α R * c₁)) * 2 := h3
        _ = (128 / c₁) * Real.exp (ersK0 c₃ * ersLam α R) := h4
    exact le_trans (pow_le_pow_left₀ (by positivity) hle d) (le_of_eq (by
      rw [mul_pow, exp_nat_mul_eq]))
  have h13 : (2 * (1 - 3 * ersEps c₃ α R)) ^ d ≤ 2 ^ d := by
    apply pow_le_pow_left₀ (by linarith [hδ])
    linarith [hep]
  have h2k : (2 : ℝ) ^ (ersKap d c₁ c₃ α R) ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hκle
    simpa using this
  have hXkpos : 0 < (ersEta c₃ α R * ((1 - ersEps c₃ α R) * 1 / Real.pi)) ^ (-(d : ℝ))
        * (ersEta c₃ α R * (4 * 1 / (Real.pi * ersEps c₃ α R))) ^ d
        / (2 * (c₁ / 4)) ^ d := by positivity
  have hXk : ((ersEta c₃ α R * ((1 - ersEps c₃ α R) * 1 / Real.pi)) ^ (-(d : ℝ))
        * (ersEta c₃ α R * (4 * 1 / (Real.pi * ersEps c₃ α R))) ^ d
        / (2 * (c₁ / 4)) ^ d) ^ (ersKap d c₁ c₃ α R)
      ≤ (128 / c₁) ^ d * Real.exp ((d : ℝ) * (ersK0 c₃ * ersLam α R)) := by
    rw [hXrat]
    calc ((8 / (ersEps c₃ α R * (1 - ersEps c₃ α R) * c₁)) ^ d) ^ (ersKap d c₁ c₃ α R)
        ≤ ((8 / (ersEps c₃ α R * (1 - ersEps c₃ α R) * c₁)) ^ d) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hXrat1 hκle
      _ = (8 / (ersEps c₃ α R * (1 - ersEps c₃ α R) * c₁)) ^ d := Real.rpow_one _
      _ ≤ _ := hXratub
  rw [ersB]
  have h13nn : (0:ℝ) ≤ (2 * (1 - 3 * ersEps c₃ α R)) ^ d := by
    exact pow_nonneg (by linarith [hδ, hep]) d
  have hEpos : (0:ℝ) < Real.exp ((d : ℝ) * (ersK0 c₃ * ersLam α R)) := Real.exp_pos _
  have hUBpos : 0 < ersEtaUB c₃ := by rw [ersEtaUB]; positivity
  have hAd_nn : (0:ℝ) ≤ (8 * ersEtaUB c₃) ^ d * Real.exp ((d : ℝ) * (ersK0 c₃ * ersLam α R)) :=
    mul_nonneg (pow_nonneg (by positivity) d) (le_of_lt hEpos)
  have s1 := mul_le_mul hAd h13 h13nn hAd_nn
  have hκnn : (0:ℝ) ≤ (2:ℝ) ^ (ersKap d c₁ c₃ α R) := Real.rpow_nonneg (by norm_num) _
  have hAd2_nn : (0:ℝ) ≤ ((8 * ersEtaUB c₃) ^ d * Real.exp ((d : ℝ) * (ersK0 c₃ * ersLam α R))) * 2 ^ d :=
    mul_nonneg hAd_nn (pow_nonneg (by norm_num) d)
  have s2 := mul_le_mul s1 h2k hκnn hAd2_nn
  have hAd3_nn : (0:ℝ) ≤ ((((8 * ersEtaUB c₃) ^ d * Real.exp ((d : ℝ) * (ersK0 c₃ * ersLam α R))) * 2 ^ d) * 2) :=
    mul_nonneg hAd2_nn (by norm_num)
  have s3 := mul_le_mul s2 hXk (Real.rpow_nonneg (le_of_lt hXkpos) _) hAd3_nn
  refine le_trans s3 (le_of_eq ?_)
  have hexp : Real.exp ((d : ℝ) * (ersK0 c₃ * ersLam α R))
      * Real.exp ((d : ℝ) * (ersK0 c₃ * ersLam α R))
      = Real.exp (2 * ((d : ℝ) * (ersK0 c₃ * ersLam α R))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [show ((((8 * ersEtaUB c₃) ^ d * Real.exp ((d : ℝ) * (ersK0 c₃ * ersLam α R))) * 2 ^ d) * 2)
        * ((128 / c₁) ^ d * Real.exp ((d : ℝ) * (ersK0 c₃ * ersLam α R)))
      = ((8 * ersEtaUB c₃) ^ d * 2 ^ d * 2 * (128 / c₁) ^ d)
        * (Real.exp ((d : ℝ) * (ersK0 c₃ * ersLam α R))
           * Real.exp ((d : ℝ) * (ersK0 c₃ * ersLam α R))) by ring]
  rw [hexp, CB_eq]

end BoundB

section BoundU

variable {c₁ c₂ c₃ α R : ℝ} {d : ℕ}

private lemma ersUc_le (hc₁ : 0 < c₁) (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    ersUc d c₁ c₃ α R ≤ ersCU d c₃ * (ersLam α R) ^ (3 * d) := by
  have hep := ersEps_pos (α := α) hc₃ (R := R)
  have hΛ := ersLam_pos hα0 hR
  have hΛ1 := ersLam_ge_one hα0 hR
  have hη := ersEta_pos hc₃ hα0 hR
  have hηle := ersEta_le hc₃ hα0 hR
  have hrle := ersR_le hc₃ hα0 hR
  have hrpos := ersR_pos hc₃ hα0 hR
  have hr := ersR_ge hc₃ hα0 hR
  have hδ := ersEps_le_eighth hc₃ hα0 hR
  have hlog16 : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have harg1 : (1 + (1 - ersEps c₃ α R)) / (1 - (1 - ersEps c₃ α R))
      = (2 - ersEps c₃ α R) / (ersEps c₃ α R) := by ring
  have hlogL : Real.log ((1 + (1 - ersEps c₃ α R)) / (1 - (1 - ersEps c₃ α R)))
      ≤ (ersK0 c₃ + Real.log 16) * ersLam α R := by
    rw [harg1]
    have h2 : (2 - ersEps c₃ α R) / (ersEps c₃ α R) ≤ 2 / ersEps c₃ α R := by
      rw [div_le_div_iff₀ hep hep]; nlinarith [sq_nonneg (ersEps c₃ α R)]
    calc Real.log ((2 - ersEps c₃ α R) / (ersEps c₃ α R))
        ≤ Real.log (2 / ersEps c₃ α R) :=
          Real.log_le_log (div_pos (by linarith [hep]) hep) h2
      _ = ersK0 c₃ * ersLam α R + Real.log 16 := log_two_div_ersEps hc₃ hα0 hR
      _ ≤ (ersK0 c₃ + Real.log 16) * ersLam α R := by nlinarith [hlog16, hΛ1]
  have hLnn : 0 ≤ Real.log ((1 + (1 - ersEps c₃ α R)) / (1 - (1 - ersEps c₃ α R))) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by linarith [hδ])]
    nlinarith [hδ]
  have hη2 : ersEta c₃ α R * (2 / Real.pi) ≤ ersEtaUB c₃ / 2 := by
    have hpos : 0 < 2 / Real.pi := by positivity
    have := mul_le_mul_of_nonneg_right hηle (le_of_lt hpos)
    rw [show ersEtaUB c₃ * Real.pi / 4 * (2 / Real.pi) = ersEtaUB c₃ / 2 by field_simp; ring] at this
    exact this
  have hnum1 : ersEta c₃ α R * (2 / Real.pi)
        * Real.log ((1 + (1 - ersEps c₃ α R)) / (1 - (1 - ersEps c₃ α R)))
      ≤ (ersEtaUB c₃ / 2) * ((ersK0 c₃ + Real.log 16) * ersLam α R) :=
    mul_le_mul hη2 hlogL hLnn (by rw [ersEtaUB]; positivity)
  have hr1 : ersR c₃ α R + 1 ≤ (c₃ / (16 * Real.pi) + 1) * ersLam α R := by
    have hc3nn : 0 ≤ c₃ / (16 * Real.pi) := by positivity
    nlinarith [hrle, hΛ1, hc3nn]
  have hnum : ersEta c₃ α R * ((2 / Real.pi) * Real.log ((1 + (1 - ersEps c₃ α R)) / (1 - (1 - ersEps c₃ α R))))
        + ersR c₃ α R + 1
      ≤ ((ersEtaUB c₃ / 2) * (ersK0 c₃ + Real.log 16) + c₃ / (16 * Real.pi) + 1) * ersLam α R := by
    have hrhs : (ersEtaUB c₃ / 2) * ((ersK0 c₃ + Real.log 16) * ersLam α R)
        = ((ersEtaUB c₃ / 2) * (ersK0 c₃ + Real.log 16)) * ersLam α R := by ring
    rw [← mul_assoc]
    rw [hrhs] at hnum1
    nlinarith [hnum1, hr1, hΛ1]
  have hbase : 49 * c₃ ^ 2 / (128 ^ 2 * Real.pi * (ersLam α R) ^ 2)
      ≤ Real.pi * (ersR c₃ α R) ^ 2 := by
    have hr2 : (7 * c₃ / (128 * Real.pi * ersLam α R)) ^ 2 ≤ (ersR c₃ α R) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hr 2
    have hsq : (7 * c₃ / (128 * Real.pi * ersLam α R)) ^ 2
        = 49 * c₃ ^ 2 / (128 ^ 2 * Real.pi ^ 2 * (ersLam α R) ^ 2) := by field_simp; ring
    rw [hsq] at hr2
    have hmul := mul_le_mul_of_nonneg_left hr2 (le_of_lt Real.pi_pos)
    have heq2 : Real.pi * (49 * c₃ ^ 2 / (128 ^ 2 * Real.pi ^ 2 * (ersLam α R) ^ 2))
        = 49 * c₃ ^ 2 / (128 ^ 2 * Real.pi * (ersLam α R) ^ 2) := by field_simp
    rw [heq2] at hmul
    exact hmul
  have hden : ((Real.pi * (ersR c₃ α R) ^ 2) ^ d)⁻¹
      ≤ (128 ^ 2 * Real.pi / (49 * c₃ ^ 2)) ^ d * (ersLam α R) ^ (2 * d) := by
    have hinv : (Real.pi * (ersR c₃ α R) ^ 2)⁻¹
        ≤ (49 * c₃ ^ 2 / (128 ^ 2 * Real.pi * (ersLam α R) ^ 2))⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le (show 0 < 49 * c₃ ^ 2 / (128 ^ 2 * Real.pi * (ersLam α R) ^ 2) by positivity) hbase
    have hinv' : (Real.pi * (ersR c₃ α R) ^ 2)⁻¹
        ≤ 128 ^ 2 * Real.pi * (ersLam α R) ^ 2 / (49 * c₃ ^ 2) := by
      simpa [one_div, one_div_div] using hinv
    have hfac : 128 ^ 2 * Real.pi * (ersLam α R) ^ 2 / (49 * c₃ ^ 2)
        = (128 ^ 2 * Real.pi / (49 * c₃ ^ 2)) * (ersLam α R) ^ 2 := by ring
    calc ((Real.pi * (ersR c₃ α R) ^ 2) ^ d)⁻¹
        = ((Real.pi * (ersR c₃ α R) ^ 2)⁻¹) ^ d := by rw [inv_pow]
      _ ≤ (128 ^ 2 * Real.pi * (ersLam α R) ^ 2 / (49 * c₃ ^ 2)) ^ d :=
          pow_le_pow_left₀ (by positivity) hinv' d
      _ = (128 ^ 2 * Real.pi / (49 * c₃ ^ 2)) ^ d * (ersLam α R) ^ (2 * d) := by
          rw [hfac, mul_pow, show ((ersLam α R) ^ 2) ^ d = (ersLam α R) ^ (2 * d) by rw [pow_mul]]
  rw [ersUc]
  have hnumpos : 0 ≤ ersEta c₃ α R * ((2 / Real.pi) * Real.log ((1 + (1 - ersEps c₃ α R)) / (1 - (1 - ersEps c₃ α R))))
        + ersR c₃ α R + 1 := by
    have h1 : 0 ≤ (2 / Real.pi) * Real.log ((1 + (1 - ersEps c₃ α R)) / (1 - (1 - ersEps c₃ α R))) :=
      mul_nonneg (by positivity) hLnn
    nlinarith [hη, hrpos]
  have hnum_d : (ersEta c₃ α R * ((2 / Real.pi) * Real.log ((1 + (1 - ersEps c₃ α R)) / (1 - (1 - ersEps c₃ α R))))
        + ersR c₃ α R + 1) ^ d
      ≤ (((ersEtaUB c₃ / 2) * (ersK0 c₃ + Real.log 16) + c₃ / (16 * Real.pi) + 1) * ersLam α R) ^ d :=
    pow_le_pow_left₀ hnumpos hnum d
  have hUBpos : 0 < ersEtaUB c₃ := by rw [ersEtaUB]; positivity
  have hbracket : 0 ≤ (ersEtaUB c₃ / 2) * (ersK0 c₃ + Real.log 16) + c₃ / (16 * Real.pi) + 1 := by
    have h1 : 0 ≤ (ersEtaUB c₃ / 2) * (ersK0 c₃ + Real.log 16) :=
      mul_nonneg (by positivity) (by linarith [ersK0_pos hc₃, hlog16])
    have h2 : 0 ≤ c₃ / (16 * Real.pi) := by positivity
    linarith
  have hU_rhs_nn : 0 ≤ (((ersEtaUB c₃ / 2) * (ersK0 c₃ + Real.log 16) + c₃ / (16 * Real.pi) + 1) * ersLam α R) ^ d :=
    pow_nonneg (mul_nonneg hbracket (le_of_lt hΛ)) d
  have hden_inv_nn : 0 ≤ ((Real.pi * (ersR c₃ α R) ^ 2) ^ d)⁻¹ :=
    inv_nonneg.mpr (pow_nonneg (by positivity) d)
  calc (_) ^ d * ((Real.pi * (ersR c₃ α R) ^ 2) ^ d)⁻¹
      ≤ ((((ersEtaUB c₃ / 2) * (ersK0 c₃ + Real.log 16) + c₃ / (16 * Real.pi) + 1) * ersLam α R) ^ d)
        * ((128 ^ 2 * Real.pi / (49 * c₃ ^ 2)) ^ d * (ersLam α R) ^ (2 * d)) :=
        mul_le_mul hnum_d hden hden_inv_nn hU_rhs_nn
    _ = ersCU d c₃ * (ersLam α R) ^ (3 * d) := by
        rw [ersCU, mul_pow]
        have hpow : (ersLam α R) ^ d * (ersLam α R) ^ (2 * d) = (ersLam α R) ^ (3 * d) := by
          rw [← pow_add]; ring_nf
        calc (ersEtaUB c₃ / 2 * (ersK0 c₃ + Real.log 16) + c₃ / (16 * Real.pi) + 1) ^ d
              * (ersLam α R) ^ d
              * ((128 ^ 2 * Real.pi / (49 * c₃ ^ 2)) ^ d * (ersLam α R) ^ (2 * d))
            = (ersEtaUB c₃ / 2 * (ersK0 c₃ + Real.log 16) + c₃ / (16 * Real.pi) + 1) ^ d
              * (128 ^ 2 * Real.pi / (49 * c₃ ^ 2)) ^ d
              * ((ersLam α R) ^ d * (ersLam α R) ^ (2 * d)) := by ring
          _ = (ersEtaUB c₃ / 2 * (ersK0 c₃ + Real.log 16) + c₃ / (16 * Real.pi) + 1) ^ d
              * (128 ^ 2 * Real.pi / (49 * c₃ ^ 2)) ^ d * (ersLam α R) ^ (3 * d) := by rw [hpow]

end BoundU

section Eventually

open Filter
open scoped Topology

variable {c₁ c₂ c₃ α Clat : ℝ} {d : ℕ}

private lemma ev_two : ∀ᶠ R : ℝ in atTop, 2 ≤ R := Filter.eventually_ge_atTop 2

private lemma ev_Rsq : ∀ᶠ R : ℝ in atTop, (2 * (d : ℝ) / c₃) ^ 2 ≤ R :=
  Filter.eventually_ge_atTop _

private lemma ev_crux (hc₃ : 0 < c₃) (hα1 : α < 1) :
    ∀ᶠ R : ℝ in atTop, 12 * (d : ℝ) * ersK0 c₃ * ersLam α R ≤ Real.log R := by
  have h : Tendsto (fun R : ℝ => 12 * (d : ℝ) * ersK0 c₃ * (ersLam α R / Real.log R))
      atTop (𝓝 0) := by
    simpa using (tendsto_lam_div_log hα1).const_mul (12 * (d : ℝ) * ersK0 c₃)
  have hle := (h.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  filter_upwards [hle, Filter.eventually_gt_atTop (1 : ℝ)] with R hR hRgt
  have hlogR : 0 < Real.log R := Real.log_pos hRgt
  have h2 : 12 * (d : ℝ) * ersK0 c₃ * ersLam α R / Real.log R ≤ 1 := by
    rw [show 12 * (d : ℝ) * ersK0 c₃ * ersLam α R / Real.log R
        = 12 * (d : ℝ) * ersK0 c₃ * (ersLam α R / Real.log R) by ring]
    linarith
  have h3 := (div_le_iff₀ hlogR).mp h2
  simpa using h3

private lemma ev_loglam (hc₃ : 0 < c₃) (hα0 : 0 < α) :
    ∀ᶠ R : ℝ in atTop, 4 * ((d : ℝ) + 1) * Real.log (ersLam α R) ≤ Real.log R := by
  have h : Tendsto (fun R : ℝ => 4 * ((d : ℝ) + 1) * (Real.log (ersLam α R) / Real.log R))
      atTop (𝓝 0) := by
    simpa using (tendsto_loglam_div_log hα0).const_mul (4 * ((d : ℝ) + 1))
  have hle := (h.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  filter_upwards [hle, Filter.eventually_gt_atTop (1 : ℝ)] with R hR hRgt
  have hlogR : 0 < Real.log R := Real.log_pos hRgt
  have h2 : 4 * ((d : ℝ) + 1) * Real.log (ersLam α R) / Real.log R ≤ 1 := by
    rw [show 4 * ((d : ℝ) + 1) * Real.log (ersLam α R) / Real.log R
        = 4 * ((d : ℝ) + 1) * (Real.log (ersLam α R) / Real.log R) by ring]
    linarith
  have h3 := (div_le_iff₀ hlogR).mp h2
  simpa using h3

private lemma ev_logarg (hα1 : α < 1) :
    ∀ᶠ R : ℝ in atTop, 4 * Real.log (ersLam α R + Real.log R + 1) ≤ Real.log R := by
  have h : Tendsto (fun R : ℝ => 4 * (Real.log (ersLam α R + Real.log R + 1) / Real.log R))
      atTop (𝓝 0) := by
    simpa using (tendsto_log_arg_div_log hα1).const_mul 4
  have hle := (h.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  filter_upwards [hle, Filter.eventually_gt_atTop (1 : ℝ)] with R hR hRgt
  have hlogR : 0 < Real.log R := Real.log_pos hRgt
  have h2 : 4 * Real.log (ersLam α R + Real.log R + 1) / Real.log R ≤ 1 := by
    rw [show 4 * Real.log (ersLam α R + Real.log R + 1) / Real.log R
        = 4 * (Real.log (ersLam α R + Real.log R + 1) / Real.log R) by ring]
    linarith
  have h3 := (div_le_iff₀ hlogR).mp h2
  simpa using h3

private lemma ev_logK2 :
    ∀ᶠ R : ℝ in atTop, 4 * Real.log (ersK2 d c₁ c₂ c₃ Clat) ≤ Real.log R := by
  have hinv : Tendsto (fun R : ℝ => (Real.log R)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have h : Tendsto (fun R : ℝ => (4 * Real.log (ersK2 d c₁ c₂ c₃ Clat)) * (Real.log R)⁻¹)
      atTop (𝓝 0) := by
    simpa using hinv.const_mul (4 * Real.log (ersK2 d c₁ c₂ c₃ Clat))
  have hle := (h.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  filter_upwards [hle, Filter.eventually_gt_atTop (1 : ℝ)] with R hR hRgt
  have hlogR : 0 < Real.log R := Real.log_pos hRgt
  have h2 : 4 * Real.log (ersK2 d c₁ c₂ c₃ Clat) / Real.log R ≤ 1 := by
    rw [show 4 * Real.log (ersK2 d c₁ c₂ c₃ Clat) / Real.log R
        = (4 * Real.log (ersK2 d c₁ c₂ c₃ Clat)) * (Real.log R)⁻¹ by ring]
    linarith
  have h3 := (div_le_iff₀ hlogR).mp h2
  simpa using h3

private lemma ersHV_lower {R : ℝ} (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    (8 / (ersK0 c₃ + Real.log 16)) * (Real.exp (ersK0 c₃ * ersLam α R) / ersLam α R)
      ≤ ersHV c₃ α R := by
  have hep := ersEps_pos (α := α) hc₃ (R := R)
  have hΛ := ersLam_pos hα0 hR
  have hΛ1 := ersLam_ge_one hα0 hR
  have hC := ersC_pos hc₃ hα0 hR
  have hCu := ersC_upper hc₃ hα0 hR
  have hη := ersEta_pos hc₃ hα0 hR
  have hρ := ersRho_pos hc₃ hα0 hR
  have hK := ersK0_pos hc₃
  have hlog16 : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have hlow : 1 / ((ersK0 c₃ + Real.log 16) * ersLam α R) ≤ 4 * ersEta c₃ α R / Real.pi := by
    have h1 : 1 / ((ersK0 c₃ + Real.log 16) * ersLam α R)
        ≤ 1 / (ersK0 c₃ * ersLam α R + Real.log 16) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith [hlog16, hΛ1])
    have h2 : 1 / (ersK0 c₃ * ersLam α R + Real.log 16) ≤ 1 / ersC c₃ α R :=
      one_div_le_one_div_of_le hC hCu
    have h3 : 1 / ersC c₃ α R ≤ 4 * ersEta c₃ α R / Real.pi := by
      have he : 4 * ersEta c₃ α R / Real.pi = 1 / ersC c₃ α R + 2 * ersRho c₃ α R / Real.pi := by
        rw [ersEta]; field_simp; ring
      rw [he]
      have hnn : 0 ≤ 2 * ersRho c₃ α R / Real.pi := by positivity
      linarith
    linarith
  have hfac : ersHV c₃ α R = (4 * ersEta c₃ α R / Real.pi) * (8 * Real.exp (ersK0 c₃ * ersLam α R)) := by
    rw [ersHV, show 8 * Real.exp (ersK0 c₃ * ersLam α R) = (ersEps c₃ α R)⁻¹ from
      (ersEps_inv hc₃).symm]
    field_simp
  have hgoal : (8 / (ersK0 c₃ + Real.log 16)) * (Real.exp (ersK0 c₃ * ersLam α R) / ersLam α R)
      = (1 / ((ersK0 c₃ + Real.log 16) * ersLam α R)) * (8 * Real.exp (ersK0 c₃ * ersLam α R)) := by
    field_simp
  rw [hgoal, hfac]
  exact mul_le_mul_of_nonneg_right hlow (by positivity)

private lemma ev_ersHV (hc₃ : 0 < c₃) (hα0 : 0 < α) :
    ∀ᶠ R : ℝ in atTop, 1 ≤ ersHV c₃ α R := by
  have hK := ersK0_pos hc₃
  have hlog16 : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have hcoef : 0 < 8 / (ersK0 c₃ + Real.log 16) := by positivity
  have hbig := ((tendsto_exp_lam_div_lam hc₃ hα0).const_mul_atTop hcoef).eventually_ge_atTop 1
  filter_upwards [hbig, Filter.eventually_ge_atTop (2 : ℝ)] with R hRbig hR
  exact le_trans hRbig (ersHV_lower hc₃ hα0 hR)

private lemma ev_suff (hd : 1 ≤ d) (hc₃ : 0 < c₃) (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ᶠ R : ℝ in atTop, ersSuff d c₁ c₂ c₃ α Clat R := by
  filter_upwards [ev_two, ev_Rsq (d := d) (c₃ := c₃),
    ev_crux (d := d) hc₃ hα1, ev_loglam (d := d) hc₃ hα0,
    ev_logarg hα1, ev_logK2 (d := d) (c₁ := c₁) (c₂ := c₂) (c₃ := c₃) (Clat := Clat),
    ev_ersHV (c₃ := c₃) hc₃ hα0] with R h1 h2 h3 h4 h5 h6 h7
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

end Eventually

section Derivation

open Filter

variable {d : ℕ} {c₁ c₂ c₃ Clat : ℝ}

private lemma rpow_exp_form {x : ℝ} (hx : 0 < x) (n : ℝ) :
    x ^ n = Real.exp (n * Real.log x) := by
  rw [Real.rpow_def_of_pos hx]; congr 1; ring

private lemma ersKb_pos (hd : 1 ≤ d) (hc₁ : 0 < c₁) (hc₁2 : c₁ ≤ 1 / 2) (hc₃ : 0 < c₃) :
    0 < ersKb d c₁ c₃ := by
  rw [ersKb]
  exact mul_pos (mul_pos (by norm_num) hc₃)
    (Real.rpow_pos_of_pos (ersCx_pos hd hc₁ hc₁2 hc₃) _)

private lemma ersK2_pos (hd : 1 ≤ d) (hc₁ : 0 < c₁) (hc₁2 : c₁ ≤ 1 / 2) (hc₂ : 0 < c₂)
    (hc₃ : 0 < c₃) : 0 < ersK2 d c₁ c₂ c₃ Clat := by
  have hKb := ersKb_pos hd hc₁ hc₁2 hc₃
  rw [ersK2]
  refine div_pos ?_ hKb
  have hdnn : (0:ℝ) ≤ (d:ℝ) := by exact_mod_cast Nat.zero_le d
  have h1 : 0 ≤ 2 * (d:ℝ) * ersK0 c₃ :=
    mul_nonneg (mul_nonneg (by norm_num) hdnn) (le_of_lt (ersK0_pos hc₃))
  have h2 : 0 ≤ 5 * (d:ℝ) := mul_nonneg (by norm_num) hdnn
  have h3 : 0 ≤ |ersLc d c₁ c₂ c₃ Clat| := abs_nonneg _
  linarith

private lemma ersKb_mul_ersK2 (hd : 1 ≤ d) (hc₁ : 0 < c₁) (hc₁2 : c₁ ≤ 1 / 2) (hc₃ : 0 < c₃) :
    ersKb d c₁ c₃ * ersK2 d c₁ c₂ c₃ Clat
      = |ersLc d c₁ c₂ c₃ Clat| + 2 * (d : ℝ) * ersK0 c₃ + 5 * (d : ℝ) + 1 := by
  rw [ersK2]
  have hKb : ersKb d c₁ c₃ ≠ 0 := ne_of_gt (ersKb_pos hd hc₁ hc₁2 hc₃)
  field_simp

end Derivation

section FactorLemmas

variable {R c₃ α κ : ℝ} {d : ℕ}

private lemma t_rpow_eq (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R) :
    (ersT d c₃ α R) ^ (2 * κ)
      = Real.exp (-(2 * κ * (c₃ * R / ersLam α R))) * (1 + R ^ 2) ^ ((d : ℝ) * κ) := by
  have hpos : 0 < 1 + R ^ 2 := by positivity
  rw [ersT, show (Real.log (2 + R)) ^ α = ersLam α R from rfl,
      Real.mul_rpow (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt hpos) _)]
  rw [show (Real.exp (-(c₃ * R / ersLam α R))) ^ (2 * κ)
      = Real.exp (-(2 * κ * (c₃ * R / ersLam α R))) by
    rw [← Real.exp_mul]; congr 1; ring]
  rw [show ((1 + R ^ 2) ^ ((d : ℝ) / 2)) ^ (2 * κ) = (1 + R ^ 2) ^ ((d : ℝ) * κ) by
    rw [← Real.rpow_mul (le_of_lt hpos)]; congr 1; ring]

private lemma Z_rpow_eq (hc₃ : 0 < c₃) (hα0 : 0 < α) (hR : 2 ≤ R)
    {Uv Cw : ℝ} (hUv : 0 ≤ Uv) (hCw : 0 ≤ Cw) :
    (Uv * (((2 * (ersEta c₃ α R * 1 + ersR c₃ α R)) ^ d) * (((1 + R ^ 2) ^ d) * Cw))) ^ (1 - κ)
      = Uv ^ (1 - κ) * (2 * (ersEta c₃ α R * 1 + ersR c₃ α R)) ^ (d * (1 - κ))
        * (1 + R ^ 2) ^ (d * (1 - κ)) * Cw ^ (1 - κ) := by
  have h1 : (0:ℝ) ≤ 2 * (ersEta c₃ α R * 1 + ersR c₃ α R) := by
    have hη := ersEta_pos hc₃ hα0 hR
    have hr := ersR_pos hc₃ hα0 hR
    positivity
  have h2 : (0:ℝ) ≤ (1 + R ^ 2) := by positivity
  rw [Real.mul_rpow hUv (by positivity)]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [show ((2 * (ersEta c₃ α R * 1 + ersR c₃ α R)) ^ d) ^ (1 - κ)
        = (2 * (ersEta c₃ α R * 1 + ersR c₃ α R)) ^ (d * (1 - κ)) by
      rw [← Real.rpow_natCast (2 * (ersEta c₃ α R * 1 + ersR c₃ α R)) d,
          ← Real.rpow_mul h1]]
  rw [show ((1 + R ^ 2) ^ d) ^ (1 - κ) = (1 + R ^ 2) ^ (d * (1 - κ)) by
      rw [← Real.rpow_natCast (1 + R ^ 2) d, ← Real.rpow_mul h2]]
  ring

private lemma cancel_rpow (hR : 2 ≤ R) (hα0 : 0 < α) (hκ : 0 ≤ κ) :
    (1 + R ^ 2) ^ (d * (1 - κ)) * (1 + R ^ 2) ^ ((d : ℝ) * κ) = (1 + R ^ 2) ^ d := by
  have h2 : (0:ℝ) < 1 + R ^ 2 := by positivity
  rw [← Real.rpow_add h2, ← Real.rpow_natCast (1 + R ^ 2) d]
  congr 1; ring

end FactorLemmas

section BigBound

open Filter

variable {Uv κ A B : ℝ} {d : ℕ}

private lemma rpow_one_sub_le (hU : 0 < Uv) (hκnn : 0 ≤ κ) (hκle : κ ≤ 1) :
    Uv ^ (1 - κ) ≤ 1 + Uv := by
  by_cases h : 1 ≤ Uv
  · have h1 : Uv ^ (1 - κ) ≤ Uv ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le h (by linarith)
    rw [Real.rpow_one] at h1; linarith
  · push Not at h
    have h1 : Uv ^ (1 - κ) ≤ (1:ℝ) ^ (1 - κ) :=
      Real.rpow_le_rpow (le_of_lt hU) (le_of_lt h) (by linarith)
    have h2 : ((1:ℝ) ^ (1 - κ)) = 1 := Real.one_rpow _
    rw [h2] at h1; linarith

private lemma rpow_le_self (hA1 : 1 ≤ A) (hκle : κ ≤ 1) : A ^ κ ≤ A := by
  have h1 : A ^ κ ≤ A ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hA1 hκle
  rwa [Real.rpow_one] at h1

private lemma rpow_le_of_le_one {A B κ : ℝ} (hA0 : 0 < A) (hA : A ≤ B) (hB1 : 1 ≤ B)
    (hκnn : 0 ≤ κ) (hκle : κ ≤ 1) : A ^ κ ≤ B := by
  by_cases h : 1 ≤ A
  · have h1 : A ^ κ ≤ A ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le h hκle
    rw [Real.rpow_one] at h1; linarith
  · push_neg at h
    have h1 : A ^ κ ≤ (1:ℝ) ^ κ := Real.rpow_le_rpow (le_of_lt hA0) (le_of_lt h) hκnn
    have h2 : ((1:ℝ) ^ κ) = 1 := Real.one_rpow _
    rw [h2] at h1; linarith

private lemma pow_rpow_le (hA0 : 0 < A) (hA : A ≤ B) (hB1 : 1 ≤ B) (hκnn : 0 ≤ κ)
    (hκle : κ ≤ 1) : A ^ (d * (1 - κ)) ≤ B ^ d := by
  by_cases h : 1 ≤ A
  · have hd : (d:ℝ) * (1 - κ) ≤ (d:ℝ) := by
      have hdnn : (0:ℝ) ≤ (d:ℝ) := by exact_mod_cast Nat.zero_le d
      nlinarith
    have h1 : A ^ (d * (1 - κ)) ≤ A ^ ((d:ℝ)) := Real.rpow_le_rpow_of_exponent_le h hd
    rw [Real.rpow_natCast] at h1
    exact le_trans h1 (pow_le_pow_left₀ (le_of_lt hA0) hA d)
  · push Not at h
    have h1 : A ^ (d * (1 - κ)) ≤ ((1:ℝ)) ^ (d * (1 - κ)) :=
      Real.rpow_le_rpow (le_of_lt hA0) (le_of_lt h) (by positivity)
    have h2 : ((1:ℝ) ^ (d * (1 - κ))) = 1 := Real.one_rpow _
    rw [h2] at h1
    have h3 : (1:ℝ) ≤ B ^ d := one_le_pow₀ hB1
    linarith

end BigBound

section BigBoundMain

open Filter

variable {d : ℕ} {c₁ c₂ c₃ α Clat : ℝ}

private lemma ersEtaUB_pos {c₃ : ℝ} (hc₃ : 0 < c₃) : 0 < ersEtaUB c₃ := by
  rw [ersEtaUB]; positivity

private lemma ersCB_pos {c₁ c₃ : ℝ} {d : ℕ} (hc₁ : 0 < c₁) (hc₃ : 0 < c₃) :
    0 < ersCB d c₁ c₃ := by
  rw [ersCB]
  exact mul_pos (by norm_num)
    (pow_pos (div_pos (mul_pos (by norm_num) (ersEtaUB_pos hc₃)) hc₁) d)

private lemma ersCU_nn {c₃ : ℝ} {d : ℕ} (hc₃ : 0 < c₃) : 0 ≤ ersCU d c₃ := by
  rw [ersCU]
  apply mul_nonneg
  · refine pow_nonneg ?_ d
    have h6 : 0 ≤ (ersEtaUB c₃ / 2) * (ersK0 c₃ + Real.log 16) :=
      mul_nonneg (div_nonneg (le_of_lt (ersEtaUB_pos hc₃)) (by norm_num))
        (by linarith [ersK0_pos hc₃, Real.log_pos (by norm_num : (1:ℝ) < 16)])
    have h8 : 0 ≤ c₃ / (16 * Real.pi) := by positivity
    linarith
  · exact pow_nonneg (by positivity) d

private lemma ersCY_nn {Clat : ℝ} {d : ℕ} (hClat : 1 ≤ Clat) : 0 ≤ ersCY d Clat := by
  rw [ersCY]
  have hCw : 0 < ersCW d := by rw [ersCW]; positivity
  positivity

private lemma ersCX_pos {c₁ c₃ Clat : ℝ} {d : ℕ} (hd : 1 ≤ d) (hc₁ : 0 < c₁) (hc₁2 : c₁ ≤ 1/2)
    (hc₃ : 0 < c₃) (hClat : 1 ≤ Clat) : 0 < ersCX d c₁ c₃ Clat := by
  rw [ersCX]
  have h1 := ersCB_pos (d := d) hc₁ hc₃
  have h2 := ersCU_nn (d := d) hc₃
  have h3 : 0 < 1 + ersCU d c₃ := by linarith
  have h4 : 0 < 1 + ersEtaR c₃ := by
    have : 0 ≤ ersEtaR c₃ := by
      rw [ersEtaR]
      have h1' : 0 ≤ ersEtaUB c₃ * Real.pi / 4 := by have := ersEtaUB_pos hc₃; positivity
      have h2' : 0 ≤ c₃ / (4 * Real.pi) := by positivity
      linarith
    linarith
  have hCw : 0 < ersCW d := by rw [ersCW]; positivity
  positivity

private lemma ersCT_pos {c₁ c₃ Clat : ℝ} {d : ℕ} (hd : 1 ≤ d) (hc₁ : 0 < c₁) (hc₁2 : c₁ ≤ 1/2)
    (hc₃ : 0 < c₃) (hClat : 1 ≤ Clat) : 0 < ersCT d c₁ c₃ Clat := by
  rw [ersCT]
  exact add_pos_of_pos_of_nonneg (ersCX_pos hd hc₁ hc₁2 hc₃ hClat) (ersCY_nn (d := d) hClat)

private lemma big_bound (hd : 1 ≤ d) (hc₁ : 0 < c₁) (hc₁2 : c₁ ≤ 1 / 2) (hc₂ : 0 < c₂)
    (hc₂1 : c₂ < 1) (hc₃ : 0 < c₃) (hα0 : 0 < α) (hα1 : α < 1) (hClat : 1 ≤ Clat) {R : ℝ}
    (hS : ersSuff d c₁ c₂ c₃ α Clat R) :
    4 ^ d * (ersB d c₁ c₃ α R * (ersUc d c₁ c₃ α R * ((2 * (ersEta c₃ α R * 1 + ersR c₃ α R)) ^ d * ((1 + R ^ 2) ^ d * ersCW d))) ^ (1 - ersKap d c₁ c₃ α R) *
        Clat ^ (1 - ersKap d c₁ c₃ α R) * (2 * (ersCW d) ^ 2 * Clat) ^ (ersKap d c₁ c₃ α R) * (ersT d c₃ α R) ^ (2 * ersKap d c₁ c₃ α R)
      + (ersT d c₃ α R) ^ 2 * ersCW d * Clat) ≤ c₂ ^ 2 / 2 := by
  obtain ⟨hR2, hRsq, hK0L, hlogL, hlogA, hlogK2, h7⟩ := hS
  have hΛ := ersLam_pos hα0 hR2
  have hΛ1 := ersLam_ge_one hα0 hR2
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hκnn := ersKap_nonneg hd hc₁ hc₁2 hc₃ hα0 hR2 h7
  have hκle := ersKap_le_one hd hc₁ hc₁2 hc₃ hα0 hR2 h7
  have hBnd := ersB_le hd hc₁ hc₁2 hc₃ hα0 hR2 h7
  have hUnd := ersUc_le (d := d) hc₁ hc₃ hα0 hR2
  have h2er := two_etaR_le hc₃ hα0 hR2
  have hUpos : 0 < ersUc d c₁ c₃ α R := by
    rw [ersUc]
    have hη := ersEta_pos hc₃ hα0 hR2
    have hr := ersR_pos hc₃ hα0 hR2
    have h1 : 0 < Real.pi * (ersR c₃ α R) ^ 2 := mul_pos Real.pi_pos (pow_pos hr 2)
    have hLnn : 0 ≤ Real.log ((1 + (1 - ersEps c₃ α R)) / (1 - (1 - ersEps c₃ α R))) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by have hp := ersEps_pos (α := α) hc₃ (R := R); linarith)]
      nlinarith [ersEps_pos (α := α) hc₃ (R := R), ersEps_le_half hc₃ hα0 hR2]
    exact div_pos (pow_pos (by positivity) d) (pow_pos h1 d)
  have hCwpos : 0 < ersCW d := by rw [ersCW]; positivity
  have hCw1 : 1 ≤ ersCW d := by
    rw [ersCW]
    apply one_le_pow₀
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have hUp : (ersUc d c₁ c₃ α R) ^ (1 - ersKap d c₁ c₃ α R)
      ≤ (1 + ersCU d c₃) * (ersLam α R) ^ (3 * d) := by
    have h1 : (ersUc d c₁ c₃ α R) ^ (1 - ersKap d c₁ c₃ α R) ≤ 1 + ersUc d c₁ c₃ α R :=
      rpow_one_sub_le hUpos hκnn hκle
    have h2 : 1 + ersUc d c₁ c₃ α R ≤ 1 + ersCU d c₃ * (ersLam α R) ^ (3 * d) := by linarith
    have h3 : (1 : ℝ) ≤ (ersLam α R) ^ (3 * d) := one_le_pow₀ hΛ1
    have h4 : 0 ≤ ersCU d c₃ := by
      rw [ersCU]
      have h5 : 0 ≤ (ersEtaUB c₃ / 2) * (ersK0 c₃ + Real.log 16) + c₃ / (16 * Real.pi) + 1 := by
        have h6 : 0 ≤ (ersEtaUB c₃ / 2) * (ersK0 c₃ + Real.log 16) :=
          mul_nonneg (div_nonneg (le_of_lt (ersEtaUB_pos hc₃)) (by norm_num))
            (by linarith [ersK0_pos hc₃, Real.log_pos (by norm_num : (1:ℝ) < 16)])
        have h7' : 0 ≤ c₃ / (16 * Real.pi) := by positivity
        linarith
      exact mul_nonneg (pow_nonneg h5 d) (pow_nonneg (by positivity) d)
    nlinarith [h1, h2, h3, h4]
  have hWy : (2 * (ersEta c₃ α R * 1 + ersR c₃ α R)) ^ (d * (1 - ersKap d c₁ c₃ α R))
      ≤ (1 + ersEtaR c₃) ^ d := by
    have hApos : 0 < 2 * (ersEta c₃ α R * 1 + ersR c₃ α R) := by
      have hη := ersEta_pos hc₃ hα0 hR2
      have hr := ersR_pos hc₃ hα0 hR2
      positivity
    have hB1 : 1 ≤ 1 + ersEtaR c₃ := by
      have hh : 0 ≤ ersEtaR c₃ := by
        rw [ersEtaR]
        have h1 : 0 ≤ ersEtaUB c₃ * Real.pi / 4 := by have := ersEtaUB_pos hc₃; positivity
        have h2 : 0 ≤ c₃ / (4 * Real.pi) := by positivity
        linarith
      linarith
    exact pow_rpow_le hApos (by linarith [h2er]) hB1 hκnn hκle
  have hCwp : (ersCW d) ^ (1 - ersKap d c₁ c₃ α R) ≤ ersCW d := rpow_le_self hCw1 (by linarith [hκnn])
  have hClp : Clat ^ (1 - ersKap d c₁ c₃ α R) ≤ Clat := rpow_le_self hClat (by linarith [hκnn])
  have hCl2 : (2 * (ersCW d) ^ 2 * Clat) ^ (ersKap d c₁ c₃ α R) ≤ 2 * (ersCW d) ^ 2 * Clat :=
    rpow_le_self (by nlinarith [hCw1, hClat]) (by linarith [hκnn])
  have hSd : (1 + R ^ 2) ^ d ≤ 2 ^ d * R ^ (2 * d) := by
    have h1 : 1 + R ^ 2 ≤ 2 * R ^ 2 := by nlinarith
    calc (1 + R ^ 2) ^ d ≤ (2 * R ^ 2) ^ d := pow_le_pow_left₀ (by positivity) h1 d
      _ = 2 ^ d * (R ^ 2) ^ d := by rw [mul_pow]
      _ = 2 ^ d * R ^ (2 * d) := by rw [← pow_mul]
  have hZpos : 0 < (ersUc d c₁ c₃ α R * ((2 * (ersEta c₃ α R * 1 + ersR c₃ α R)) ^ d * ((1 + R ^ 2) ^ d * ersCW d))) := by
    have h2 : 0 < 2 * (ersEta c₃ α R * 1 + ersR c₃ α R) := by
      have hη := ersEta_pos hc₃ hα0 hR2
      have hr := ersR_pos hc₃ hα0 hR2
      positivity
    positivity
  have hZt : (ersUc d c₁ c₃ α R * ((2 * (ersEta c₃ α R * 1 + ersR c₃ α R)) ^ d * ((1 + R ^ 2) ^ d * ersCW d))) ^ (1 - ersKap d c₁ c₃ α R)
        * (ersT d c₃ α R) ^ (2 * ersKap d c₁ c₃ α R)
      = (ersUc d c₁ c₃ α R) ^ (1 - ersKap d c₁ c₃ α R)
        * (2 * (ersEta c₃ α R * 1 + ersR c₃ α R)) ^ (d * (1 - ersKap d c₁ c₃ α R))
        * (ersCW d) ^ (1 - ersKap d c₁ c₃ α R)
        * Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R))) * (1 + R ^ 2) ^ d := by
    rw [Z_rpow_eq hc₃ hα0 hR2 (le_of_lt hUpos) (le_of_lt hCwpos), t_rpow_eq hc₃ hα0 hR2]
    rw [show (ersUc d c₁ c₃ α R) ^ (1 - ersKap d c₁ c₃ α R)
            * (2 * (ersEta c₃ α R * 1 + ersR c₃ α R)) ^ (d * (1 - ersKap d c₁ c₃ α R))
            * (1 + R ^ 2) ^ (d * (1 - ersKap d c₁ c₃ α R)) * (ersCW d) ^ (1 - ersKap d c₁ c₃ α R)
            * (Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R)))
               * (1 + R ^ 2) ^ ((d : ℝ) * ersKap d c₁ c₃ α R))
          = (ersUc d c₁ c₃ α R) ^ (1 - ersKap d c₁ c₃ α R)
            * (2 * (ersEta c₃ α R * 1 + ersR c₃ α R)) ^ (d * (1 - ersKap d c₁ c₃ α R))
            * (ersCW d) ^ (1 - ersKap d c₁ c₃ α R)
            * Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R)))
            * ((1 + R ^ 2) ^ (d * (1 - ersKap d c₁ c₃ α R))
               * (1 + R ^ 2) ^ ((d : ℝ) * ersKap d c₁ c₃ α R)) by ring]
    rw [cancel_rpow hR2 hα0 hκnn]
  have hEe_nn : (0:ℝ) ≤ Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R))) := le_of_lt (Real.exp_pos _)
  have hXb0 : ersB d c₁ c₃ α R * (ersUc d c₁ c₃ α R * ((2 * (ersEta c₃ α R * 1 + ersR c₃ α R)) ^ d * ((1 + R ^ 2) ^ d * ersCW d))) ^ (1 - ersKap d c₁ c₃ α R)
        * Clat ^ (1 - ersKap d c₁ c₃ α R) * (2 * (ersCW d) ^ 2 * Clat) ^ (ersKap d c₁ c₃ α R) * (ersT d c₃ α R) ^ (2 * ersKap d c₁ c₃ α R)
      ≤ (ersCB d c₁ c₃ * Real.exp (2 * ((d : ℝ) * (ersK0 c₃ * ersLam α R))))
        * (((1 + ersCU d c₃) * (ersLam α R) ^ (3 * d)) * (1 + ersEtaR c₃) ^ d * (ersCW d)
           * Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R))) * (2 ^ d * R ^ (2 * d)))
        * Clat * (2 * (ersCW d) ^ 2 * Clat) := by
    rw [show ersB d c₁ c₃ α R * (ersUc d c₁ c₃ α R * ((2 * (ersEta c₃ α R * 1 + ersR c₃ α R)) ^ d * ((1 + R ^ 2) ^ d * ersCW d))) ^ (1 - ersKap d c₁ c₃ α R)
          * Clat ^ (1 - ersKap d c₁ c₃ α R) * (2 * (ersCW d) ^ 2 * Clat) ^ (ersKap d c₁ c₃ α R) * (ersT d c₃ α R) ^ (2 * ersKap d c₁ c₃ α R)
        = ersB d c₁ c₃ α R * ((ersUc d c₁ c₃ α R * ((2 * (ersEta c₃ α R * 1 + ersR c₃ α R)) ^ d * ((1 + R ^ 2) ^ d * ersCW d))) ^ (1 - ersKap d c₁ c₃ α R)
              * (ersT d c₃ α R) ^ (2 * ersKap d c₁ c₃ α R)) * Clat ^ (1 - ersKap d c₁ c₃ α R) * (2 * (ersCW d) ^ 2 * Clat) ^ (ersKap d c₁ c₃ α R) by ring]
    rw [hZt]
    have hCU_nn : 0 ≤ ersCU d c₃ := by
      rw [ersCU]
      have h5 : 0 ≤ (ersEtaUB c₃ / 2) * (ersK0 c₃ + Real.log 16) + c₃ / (16 * Real.pi) + 1 := by
        have h6 : 0 ≤ (ersEtaUB c₃ / 2) * (ersK0 c₃ + Real.log 16) :=
          mul_nonneg (div_nonneg (le_of_lt (ersEtaUB_pos hc₃)) (by norm_num))
            (by linarith [ersK0_pos hc₃, Real.log_pos (by norm_num : (1:ℝ) < 16)])
        have h8 : 0 ≤ c₃ / (16 * Real.pi) := by positivity
        linarith
      exact mul_nonneg (pow_nonneg h5 d) (pow_nonneg (by positivity) d)
    have hER_nn : 0 ≤ ersEtaR c₃ := by
      rw [ersEtaR]
      have h1 : 0 ≤ ersEtaUB c₃ * Real.pi / 4 := by have := ersEtaUB_pos hc₃; positivity
      have h2 : 0 ≤ c₃ / (4 * Real.pi) := by positivity
      linarith
    have hA2nn : 0 ≤ 2 * (ersEta c₃ α R * 1 + ersR c₃ α R) := by
      have hη := ersEta_pos hc₃ hα0 hR2
      have hr := ersR_pos hc₃ hα0 hR2
      positivity
    have n1 : (0:ℝ) ≤ (2 * (ersEta c₃ α R * 1 + ersR c₃ α R)) ^ (d * (1 - ersKap d c₁ c₃ α R)) :=
      Real.rpow_nonneg hA2nn _
    have n2 : (0:ℝ) ≤ (ersCW d) ^ (1 - ersKap d c₁ c₃ α R) := Real.rpow_nonneg (le_of_lt hCwpos) _
    have n3 : (0:ℝ) ≤ Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R))) := le_of_lt (Real.exp_pos _)
    have n4 : (0:ℝ) ≤ (1 + R ^ 2) ^ d := pow_nonneg (by positivity) d
    have n5 : (0:ℝ) ≤ Clat ^ (1 - ersKap d c₁ c₃ α R) := Real.rpow_nonneg (by linarith) _
    have n6 : (0:ℝ) ≤ (2 * (ersCW d) ^ 2 * Clat) ^ (ersKap d c₁ c₃ α R) :=
      Real.rpow_nonneg (by nlinarith [hCw1, hClat]) _
    have m1 : (0:ℝ) ≤ (1 + ersCU d c₃) * (ersLam α R) ^ (3 * d) :=
      mul_nonneg (by linarith [hCU_nn]) (pow_nonneg (le_of_lt hΛ) _)
    have m2 : (0:ℝ) ≤ (1 + ersEtaR c₃) ^ d := pow_nonneg (by linarith [hER_nn]) d
    have m3 : (0:ℝ) ≤ ersCW d := le_of_lt hCwpos
    have m5 : (0:ℝ) ≤ Clat := by linarith
    have hCBs : (0:ℝ) ≤ ersCB d c₁ c₃ * Real.exp (2 * ((d : ℝ) * (ersK0 c₃ * ersLam α R))) := by
      have h1 : 0 < ersCB d c₁ c₃ := by rw [ersCB]; have := ersEtaUB_pos hc₃; positivity
      exact mul_nonneg (le_of_lt h1) (le_of_lt (Real.exp_pos _))
    have e1 := mul_le_mul hUp hWy n1 m1
    have e2 := mul_le_mul e1 hCwp n2 (mul_nonneg m1 m2)
    have e3 := mul_le_mul e2 (le_refl _) n3 (mul_nonneg (mul_nonneg m1 m2) m3)
    have e4 := mul_le_mul e3 hSd n4 (mul_nonneg (mul_nonneg (mul_nonneg m1 m2) m3) n3)
    have e5 := mul_le_mul hBnd e4 (by positivity) hCBs
    have e6 := mul_le_mul e5 hClp n5 (mul_nonneg hCBs (by positivity))
    have e7 := mul_le_mul e6 hCl2 n6 (mul_nonneg (mul_nonneg hCBs (by positivity)) m5)
    exact e7
  have hXb : 4 ^ d * (ersB d c₁ c₃ α R * (ersUc d c₁ c₃ α R * ((2 * (ersEta c₃ α R * 1 + ersR c₃ α R)) ^ d * ((1 + R ^ 2) ^ d * ersCW d))) ^ (1 - ersKap d c₁ c₃ α R) *
        Clat ^ (1 - ersKap d c₁ c₃ α R) * (2 * (ersCW d) ^ 2 * Clat) ^ (ersKap d c₁ c₃ α R) * (ersT d c₃ α R) ^ (2 * ersKap d c₁ c₃ α R))
      ≤ ersCX d c₁ c₃ Clat * (Real.exp (2 * ((d : ℝ) * (ersK0 c₃ * ersLam α R))) * (ersLam α R) ^ (3 * d) * R ^ (2 * d)
          * Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R)))) := by
    calc 4 ^ d * (ersB d c₁ c₃ α R * (ersUc d c₁ c₃ α R * ((2 * (ersEta c₃ α R * 1 + ersR c₃ α R)) ^ d * ((1 + R ^ 2) ^ d * ersCW d))) ^ (1 - ersKap d c₁ c₃ α R) *
          Clat ^ (1 - ersKap d c₁ c₃ α R) * (2 * (ersCW d) ^ 2 * Clat) ^ (ersKap d c₁ c₃ α R) * (ersT d c₃ α R) ^ (2 * ersKap d c₁ c₃ α R))
        ≤ 4 ^ d * ((ersCB d c₁ c₃ * Real.exp (2 * ((d : ℝ) * (ersK0 c₃ * ersLam α R))))
          * ((((1 + ersCU d c₃) * (ersLam α R) ^ (3 * d)) * (1 + ersEtaR c₃) ^ d * (ersCW d)
             * Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R))) * (2 ^ d * R ^ (2 * d))))
          * Clat * (2 * (ersCW d) ^ 2 * Clat)) := mul_le_mul_of_nonneg_left hXb0 (by positivity)
      _ = ersCX d c₁ c₃ Clat * (Real.exp (2 * ((d : ℝ) * (ersK0 c₃ * ersLam α R))) * (ersLam α R) ^ (3 * d) * R ^ (2 * d)
          * Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R)))) := by
          rw [ersCX]; ring_nf
  -- Y bound
  have hT2 : (ersT d c₃ α R) ^ 2 = Real.exp (-(2 * (c₃ * R / ersLam α R))) * (1 + R ^ 2) ^ d := by
    have h := t_rpow_eq (κ := 1) (d := d) hc₃ hα0 hR2
    simpa [Real.rpow_natCast] using h
  have hYb : 4 ^ d * ((ersT d c₃ α R) ^ 2 * ersCW d * Clat)
      ≤ ersCY d Clat * (Real.exp (2 * ((d : ℝ) * (ersK0 c₃ * ersLam α R))) * (ersLam α R) ^ (3 * d) * R ^ (2 * d)
          * Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R)))) := by
    have hEe_le : Real.exp (-(2 * (c₃ * R / ersLam α R)))
        ≤ Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R))) := by
      apply Real.exp_le_exp.mpr
      have hcR : 0 ≤ c₃ * R / ersLam α R := by positivity
      nlinarith [hκle, hcR]
    rw [hT2]
    have n7 : (0:ℝ) ≤ Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R))) := le_of_lt (Real.exp_pos _)
    have m4 : (0:ℝ) ≤ (1 + R ^ 2) ^ d := pow_nonneg (by positivity) d
    have m3 : (0:ℝ) ≤ ersCW d := le_of_lt hCwpos
    have m5 : (0:ℝ) ≤ Clat := by linarith
    have m6 : (0:ℝ) ≤ 2 ^ d * R ^ (2 * d) := by positivity
    have e1 := mul_le_mul hEe_le hSd m4 n7
    have e2 := mul_le_mul e1 (le_refl (ersCW d)) m3 (mul_nonneg n7 m6)
    have e3 := mul_le_mul e2 (le_refl Clat) m5 (mul_nonneg (mul_nonneg n7 m6) m3)
    have hpos1 : (0:ℝ) ≤ 2 * ((d : ℝ) * (ersK0 c₃ * ersLam α R)) := by
      have hdnn : (0:ℝ) ≤ (d:ℝ) := by exact_mod_cast Nat.zero_le d
      exact mul_nonneg (by norm_num) (mul_nonneg hdnn (mul_nonneg (le_of_lt (ersK0_pos hc₃)) (le_of_lt hΛ)))
    have heΛ1 : (1:ℝ) ≤ Real.exp (2 * ((d : ℝ) * (ersK0 c₃ * ersLam α R))) * (ersLam α R) ^ (3 * d) := by
      have h := mul_le_mul (Real.one_le_exp hpos1)
        (one_le_pow₀ hΛ1 : (1:ℝ) ≤ (ersLam α R) ^ (3 * d)) (by positivity) (by positivity)
      simpa using h
    have hbase_nn : (0:ℝ) ≤ Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R))) * (2 ^ d * R ^ (2 * d)) * ersCW d * Clat := by
      have h1 : (0:ℝ) ≤ 2 ^ d * R ^ (2 * d) := by positivity
      positivity
    calc 4 ^ d * (Real.exp (-(2 * (c₃ * R / ersLam α R))) * (1 + R ^ 2) ^ d * ersCW d * Clat)
        = 4 ^ d * (Real.exp (-(2 * (c₃ * R / ersLam α R))) * (1 + R ^ 2) ^ d * ersCW d * Clat) := rfl
      _ ≤ 4 ^ d * (Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R))) * (2 ^ d * R ^ (2 * d)) * ersCW d * Clat) :=
          mul_le_mul_of_nonneg_left e3 (by positivity)
      _ ≤ 4 ^ d * (Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R))) * (2 ^ d * R ^ (2 * d)) * ersCW d * Clat)
            * (Real.exp (2 * ((d : ℝ) * (ersK0 c₃ * ersLam α R))) * (ersLam α R) ^ (3 * d)) := by
          have h := mul_le_mul_of_nonneg_left heΛ1
            (show (0:ℝ) ≤ 4 ^ d * (Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R))) * (2 ^ d * R ^ (2 * d)) * ersCW d * Clat) by positivity)
          simpa using h
      _ = ersCY d Clat * (Real.exp (2 * ((d : ℝ) * (ersK0 c₃ * ersLam α R))) * (ersLam α R) ^ (3 * d) * R ^ (2 * d)
          * Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R)))) := by
          rw [ersCY]; ring
  -- combine X and Y
  have hsum : 4 ^ d * (ersB d c₁ c₃ α R * (ersUc d c₁ c₃ α R * ((2 * (ersEta c₃ α R * 1 + ersR c₃ α R)) ^ d * ((1 + R ^ 2) ^ d * ersCW d))) ^ (1 - ersKap d c₁ c₃ α R) *
        Clat ^ (1 - ersKap d c₁ c₃ α R) * (2 * (ersCW d) ^ 2 * Clat) ^ (ersKap d c₁ c₃ α R) * (ersT d c₃ α R) ^ (2 * ersKap d c₁ c₃ α R)
      + (ersT d c₃ α R) ^ 2 * ersCW d * Clat)
      ≤ ersCT d c₁ c₃ Clat * (Real.exp (2 * ((d : ℝ) * (ersK0 c₃ * ersLam α R))) * (ersLam α R) ^ (3 * d) * R ^ (2 * d)
          * Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R)))) := by
    rw [mul_add]
    rw [ersCT]
    linarith [hXb, hYb]
  -- final log estimate
  have hlogineq : Real.log (ersK2 d c₁ c₂ c₃ Clat) + 3 * (d : ℝ) * (ersK0 c₃ * ersLam α R)
        + ((d : ℝ) + 1) * Real.log (ersLam α R) + Real.log (ersLam α R + Real.log R + 1) ≤ Real.log R := by
    have h1 : Real.log (ersK2 d c₁ c₂ c₃ Clat) ≤ Real.log R / 4 := by linarith
    have h2 : 3 * (d : ℝ) * (ersK0 c₃ * ersLam α R) ≤ Real.log R / 4 := by linarith
    have h3 : ((d : ℝ) + 1) * Real.log (ersLam α R) ≤ Real.log R / 4 := by linarith
    have h4 : Real.log (ersLam α R + Real.log R + 1) ≤ Real.log R / 4 := by linarith
    linarith
  have hK2p := ersK2_pos (d := d) (Clat := Clat) hd hc₁ hc₁2 hc₂ hc₃
  have hexpR : ersK2 d c₁ c₂ c₃ Clat * Real.exp (3 * (d : ℝ) * (ersK0 c₃ * ersLam α R))
        * (ersLam α R) ^ ((d : ℝ) + 1) * (ersLam α R + Real.log R + 1) ≤ R := by
    have h1 := Real.exp_le_exp.mpr hlogineq
    rw [Real.exp_log (by linarith : (0 : ℝ) < R), Real.exp_add, Real.exp_add, Real.exp_add,
        Real.exp_log hK2p,
        Real.exp_log (by have h := Real.log_nonneg hR1; linarith [hΛ] : (0 : ℝ) < ersLam α R + Real.log R + 1)] at h1
    rw [show Real.exp (((d : ℝ) + 1) * Real.log (ersLam α R)) = (ersLam α R) ^ ((d : ℝ) + 1) by
        rw [show ((d : ℝ) + 1) * Real.log (ersLam α R) = Real.log (ersLam α R) * ((d : ℝ) + 1)
              by ring, Real.exp_mul, Real.exp_log hΛ]] at h1
    exact h1
  have hE3 := Real.exp_pos (3 * (d : ℝ) * (ersK0 c₃ * ersLam α R))
  have hP1 : 0 < (ersLam α R) ^ ((d : ℝ) + 1) := Real.rpow_pos_of_pos hΛ _
  have hRrecip : ersK2 d c₁ c₂ c₃ Clat * (ersLam α R + Real.log R + 1)
      ≤ R * Real.exp (-(3 * (d : ℝ) * (ersK0 c₃ * ersLam α R))) * (ersLam α R) ^ (-(d : ℝ)) / ersLam α R := by
    have hpos : 0 < Real.exp (3 * (d : ℝ) * (ersK0 c₃ * ersLam α R)) * (ersLam α R) ^ ((d : ℝ) + 1) :=
      mul_pos hE3 hP1
    have h2 : ersK2 d c₁ c₂ c₃ Clat * (ersLam α R + Real.log R + 1)
        = ersK2 d c₁ c₂ c₃ Clat * Real.exp (3 * (d : ℝ) * (ersK0 c₃ * ersLam α R)) * (ersLam α R) ^ ((d : ℝ) + 1)
          * (ersLam α R + Real.log R + 1)
          / (Real.exp (3 * (d : ℝ) * (ersK0 c₃ * ersLam α R)) * (ersLam α R) ^ ((d : ℝ) + 1)) := by
      field_simp
    rw [h2]
    have h3 := div_le_div_of_nonneg_right hexpR (le_of_lt hpos)
    refine le_trans h3 (le_of_eq ?_)
    rw [div_eq_mul_inv, mul_inv, ← Real.exp_neg, ← Real.rpow_neg hΛ.le]
    rw [show -((d : ℝ) + 1) = -(d : ℝ) + (-1) by ring, Real.rpow_add hΛ, Real.rpow_neg_one]
    rw [div_eq_mul_inv]
    ring
  have hklow : 2 * c₃ * (ersCx d c₁ c₃) ^ (-(d : ℝ))
        * (R * Real.exp (-(3 * (d : ℝ) * (ersK0 c₃ * ersLam α R))) * (ersLam α R) ^ (-(d : ℝ)) / ersLam α R)
      ≤ 2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R) := by
    have hK := ersKap_ge hd hc₁ hc₁2 hc₃ hα0 hR2 h7
    have h2 := mul_le_mul_of_nonneg_left hK (by positivity : (0 : ℝ) ≤ 2 * (c₃ * R / ersLam α R))
    rw [show (3 : ℝ) * ((d : ℝ) * (ersK0 c₃ * ersLam α R)) = 3 * (d : ℝ) * (ersK0 c₃ * ersLam α R)
        by ring] at h2
    calc 2 * c₃ * (ersCx d c₁ c₃) ^ (-(d : ℝ))
          * (R * Real.exp (-(3 * (d : ℝ) * (ersK0 c₃ * ersLam α R))) * (ersLam α R) ^ (-(d : ℝ)) / ersLam α R)
        = 2 * (c₃ * R / ersLam α R)
          * ((ersCx d c₁ c₃) ^ (-(d : ℝ)) * (ersLam α R) ^ (-(d : ℝ))
              * Real.exp (-(3 * (d : ℝ) * (ersK0 c₃ * ersLam α R)))) := by ring
      _ ≤ 2 * (c₃ * R / ersLam α R) * (ersKap d c₁ c₃ α R) := h2
      _ = 2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R) := by ring
  have hposCx : (0:ℝ) ≤ 2 * c₃ * (ersCx d c₁ c₃) ^ (-(d : ℝ)) :=
    mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hc₃))
      (Real.rpow_nonneg (le_of_lt (ersCx_pos hd hc₁ hc₁2 hc₃)) _)
  have hbig : 2 * c₃ * (ersCx d c₁ c₃) ^ (-(d : ℝ)) * (ersK2 d c₁ c₂ c₃ Clat * (ersLam α R + Real.log R + 1))
      ≤ 2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R) :=
    le_trans (mul_le_mul_of_nonneg_left hRrecip hposCx) hklow
  have hKb2 := ersKb_mul_ersK2 (d := d) (c₂ := c₂) (Clat := Clat) hd hc₁ hc₁2 hc₃
  have hKbdef : 2 * c₃ * (ersCx d c₁ c₃) ^ (-(d : ℝ)) = ersKb d c₁ c₃ := by rw [ersKb]
  rw [hKbdef] at hbig
  have hres : (|ersLc d c₁ c₂ c₃ Clat| + 2 * (d : ℝ) * ersK0 c₃ + 5 * (d : ℝ) + 1) * (ersLam α R + Real.log R + 1)
      ≤ 2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R) := by
    rw [← hKb2]
    simpa [mul_assoc] using hbig
  have hone_pos : 0 < ersLam α R + Real.log R + 1 := by
    have hlogRnn : 0 ≤ Real.log R := Real.log_nonneg hR1
    linarith
  have hlogdiff : ersLc d c₁ c₂ c₃ Clat + 2 * (d : ℝ) * (ersK0 c₃ * ersLam α R)
        + 3 * (d : ℝ) * Real.log (ersLam α R) + 2 * (d : ℝ) * Real.log R
      ≤ (|ersLc d c₁ c₂ c₃ Clat| + 2 * (d : ℝ) * ersK0 c₃ + 5 * (d : ℝ) + 1) * (ersLam α R + Real.log R + 1) := by
    have hdnn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
    have hlogRnn : (0 : ℝ) ≤ Real.log R := Real.log_nonneg hR1
    have hK0nn : 0 ≤ ersK0 c₃ := le_of_lt (ersK0_pos hc₃)
    have hX : (0:ℝ) ≤ ersLam α R + Real.log R + 1 := le_of_lt hone_pos
    have hX1 : (1:ℝ) ≤ ersLam α R + Real.log R + 1 := by linarith
    have hlogL_le : Real.log (ersLam α R) ≤ ersLam α R := by
      have h := Real.log_le_sub_one_of_pos hΛ; linarith
    have e1 : 2 * (d:ℝ) * (ersK0 c₃ * ersLam α R) ≤ 2 * (d:ℝ) * ersK0 c₃ * (ersLam α R + Real.log R + 1) := by
      rw [show 2 * (d:ℝ) * (ersK0 c₃ * ersLam α R) = (2 * (d:ℝ) * ersK0 c₃) * ersLam α R by ring]
      exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (mul_nonneg (by norm_num) hdnn) hK0nn)
    have e2 : 3 * (d:ℝ) * Real.log (ersLam α R) ≤ 3 * (d:ℝ) * (ersLam α R + Real.log R + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by norm_num) hdnn)
    have e3 : 2 * (d:ℝ) * Real.log R ≤ 2 * (d:ℝ) * (ersLam α R + Real.log R + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by norm_num) hdnn)
    have e4 : |ersLc d c₁ c₂ c₃ Clat| ≤ |ersLc d c₁ c₂ c₃ Clat| * (ersLam α R + Real.log R + 1) :=
      le_mul_of_one_le_right (abs_nonneg _) hX1
    have hRHS : (|ersLc d c₁ c₂ c₃ Clat| + 2*(d:ℝ)*ersK0 c₃ + 5*(d:ℝ) + 1) * (ersLam α R + Real.log R + 1)
        = |ersLc d c₁ c₂ c₃ Clat| * (ersLam α R + Real.log R + 1)
          + (2*(d:ℝ)*ersK0 c₃ + 5*(d:ℝ) + 1) * (ersLam α R + Real.log R + 1) := by ring
    have hRHS2 : (2*(d:ℝ)*ersK0 c₃ + 5*(d:ℝ) + 1) * (ersLam α R + Real.log R + 1)
        ≥ 2*(d:ℝ)*ersK0 c₃ * (ersLam α R + Real.log R + 1) + 3*(d:ℝ)*(ersLam α R + Real.log R + 1)
          + 2*(d:ℝ)*(ersLam α R + Real.log R + 1) := by
      nlinarith [hX, hdnn, hK0nn]
    have hLc_le : ersLc d c₁ c₂ c₃ Clat ≤ |ersLc d c₁ c₂ c₃ Clat| := le_abs_self _
    linarith [e1, e2, e3, e4, hRHS, hRHS2, hLc_le]

  have h2kR : ersLc d c₁ c₂ c₃ Clat + 2 * (d : ℝ) * (ersK0 c₃ * ersLam α R)
        + 3 * (d : ℝ) * Real.log (ersLam α R) + 2 * (d : ℝ) * Real.log R
      ≤ 2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R) := le_trans hlogdiff hres
  have hlogF : Real.log (Real.exp (2 * ((d : ℝ) * (ersK0 c₃ * ersLam α R))) * (ersLam α R) ^ (3 * d) * R ^ (2 * d)
        * Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R))))
      = 2 * ((d : ℝ) * (ersK0 c₃ * ersLam α R)) + 3 * (d : ℝ) * Real.log (ersLam α R) + 2 * (d : ℝ) * Real.log R
        - 2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp, Real.log_exp,
        Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hCTpos : 0 < ersCT d c₁ c₃ Clat := ersCT_pos hd hc₁ hc₁2 hc₃ hClat
  have hFbound : Real.exp (2 * ((d : ℝ) * (ersK0 c₃ * ersLam α R))) * (ersLam α R) ^ (3 * d) * R ^ (2 * d)
        * Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R))) ≤ c₂ ^ 2 / (2 * ersCT d c₁ c₃ Clat) := by
    have hLHSpos : 0 < Real.exp (2 * ((d : ℝ) * (ersK0 c₃ * ersLam α R))) * (ersLam α R) ^ (3 * d) * R ^ (2 * d)
        * Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R))) := by
      have h1 : 0 < (ersLam α R) ^ (3 * d) := pow_pos hΛ _
      have h2 : 0 < R ^ (2 * d) := pow_pos (by linarith) _
      positivity
    have hRHSpos : 0 < c₂ ^ 2 / (2 * ersCT d c₁ c₃ Clat) :=
      div_pos (pow_pos hc₂ 2) (by linarith)
    have hlogs : Real.log (Real.exp (2 * ((d : ℝ) * (ersK0 c₃ * ersLam α R))) * (ersLam α R) ^ (3 * d) * R ^ (2 * d)
        * Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R))))
        ≤ Real.log (c₂ ^ 2 / (2 * ersCT d c₁ c₃ Clat)) := by
      rw [hlogF]
      have hlog2 : Real.log (c₂ ^ 2 / (2 * ersCT d c₁ c₃ Clat)) = -ersLc d c₁ c₂ c₃ Clat := by
        rw [ersLc, Real.log_div (by positivity) (by positivity),
            Real.log_div (by positivity) (by positivity)]
        ring
      rw [hlog2]
      linarith [h2kR]
    have h1 := Real.exp_le_exp.mpr hlogs
    rwa [Real.exp_log hLHSpos, Real.exp_log hRHSpos] at h1
  calc 4 ^ d * (ersB d c₁ c₃ α R * (ersUc d c₁ c₃ α R * ((2 * (ersEta c₃ α R * 1 + ersR c₃ α R)) ^ d * ((1 + R ^ 2) ^ d * ersCW d))) ^ (1 - ersKap d c₁ c₃ α R) *
        Clat ^ (1 - ersKap d c₁ c₃ α R) * (2 * (ersCW d) ^ 2 * Clat) ^ (ersKap d c₁ c₃ α R) * (ersT d c₃ α R) ^ (2 * ersKap d c₁ c₃ α R)
      + (ersT d c₃ α R) ^ 2 * ersCW d * Clat)
      ≤ ersCT d c₁ c₃ Clat * (Real.exp (2 * ((d : ℝ) * (ersK0 c₃ * ersLam α R))) * (ersLam α R) ^ (3 * d) * R ^ (2 * d)
          * Real.exp (-(2 * ersKap d c₁ c₃ α R * (c₃ * R / ersLam α R)))) := hsum
    _ ≤ ersCT d c₁ c₃ Clat * (c₂ ^ 2 / (2 * ersCT d c₁ c₃ Clat)) :=
        mul_le_mul_of_nonneg_left hFbound (le_of_lt hCTpos)
    _ = c₂ ^ 2 / 2 := by field_simp

end BigBoundMain

section MainTheorem

open Filter

theorem exists_R_coeff_small_q1 {d : ℕ} (hd : 1 ≤ d) {c₁ c₂ c₃ α Clat : ℝ}
    (hc₁ : 0 < c₁) (hc₁2 : c₁ ≤ 1 / 2) (hc₂ : 0 < c₂) (hc₂1 : c₂ < 1)
    (hc₃ : 0 < c₃) (hα0 : 0 < α) (hα1 : α < 1) (hClat : 1 ≤ Clat) :
    ∃ (R q ε δ H η r κ CW B U t : ℝ), 2 ≤ R ∧ (2 * (d : ℝ) / c₃) ^ 2 ≤ R ∧ q = 1 ∧
      0 < q ∧ 0 < ε ∧ ε ≤ 1 / 2 ∧ 0 < δ ∧ δ < 1 / 3 ∧ 0 < H ∧ H ≤ 1 ∧ 0 < η ∧ 0 < r ∧
      1 ≤ η * ((2 * q / Real.pi) *
        Real.log ((1 + (1 - ε) * (1 - 3 * δ)) / (1 - (1 - ε) * (1 - 3 * δ)))) ∧
      4 * Real.pi * (η * q + r) ≤ c₃ * (Real.log (2 + R)) ^ (-α) ∧
      (η * (4 * q / (Real.pi * ε))) ^ d * (2 * (20 ^ d * H)) ≤ (c₁ / 2) ^ d ∧
      κ = ((1 + 2 * δ⁻¹ ^ 3 * Real.log (2 / δ)
            + δ⁻¹ ^ 2 * Real.log (2 * Real.exp 1 / H))⁻¹) ^ d ∧
      CW = (40 * ((d : ℝ) + 1)) ^ d ∧
      B = (η * (4 * q / (Real.pi * ε))) ^ d * (2 * (1 - 3 * δ)) ^ d * (2 : ℝ) ^ κ *
          (((η * ((1 - ε) * q / Real.pi)) ^ (-(d : ℝ)) * (η * (4 * q / (Real.pi * ε))) ^ d
            / (2 * (c₁ / 4)) ^ d) ^ κ) ∧
      U = (η * ((2 / Real.pi) * Real.log ((1 + (1 - ε)) / (1 - (1 - ε)))) + r + 1) ^ d *
            ((Real.pi * r ^ 2) ^ d)⁻¹ ∧
      t = Real.exp (-(c₃ * R / (Real.log (2 + R)) ^ α)) * (1 + R ^ 2) ^ ((d : ℝ) / 2) ∧
      4 ^ d * (B * (U * ((2 * (η * q + r)) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ) *
            Clat ^ (1 - κ) * (2 * CW ^ 2 * Clat) ^ κ * t ^ (2 * κ) + t ^ 2 * CW * Clat)
        ≤ c₂ ^ 2 / 2 := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ersSuff d c₁ c₂ c₃ α Clat R :=
    (ev_suff (d := d) (c₁ := c₁) (c₂ := c₂) (c₃ := c₃) (α := α) (Clat := Clat) hd hc₃ hα0 hα1).exists
  obtain ⟨hR2, hRsq, hK0L, hlogL, hlogA, hlogK2, h7⟩ := hR
  refine ⟨R, 1, ersEps c₃ α R, ersEps c₃ α R, ersH d c₁ c₃ α R, ersEta c₃ α R, ersR c₃ α R,
    ersKap d c₁ c₃ α R, ersCW d, ersB d c₁ c₃ α R, ersUc d c₁ c₃ α R, ersT d c₃ α R, ?_⟩
  exact ⟨hR2, hRsq, rfl, one_pos, ersEps_pos (α := α) hc₃, ersEps_le_half hc₃ hα0 hR2,
      ersEps_pos (α := α) hc₃, ersEps_lt_third hc₃ hα0 hR2, ersH_pos (d := d) hc₁ hc₃ hα0 hR2,
      ersH_le_one (d := d) hc₁ hc₁2 hc₃ hα0 hR2 h7, ersEta_pos hc₃ hα0 hR2, ersR_pos hc₃ hα0 hR2,
      ers_lens hc₃ hα0 hR2, ers_strip hc₃ hα0 hR2, ers_cube (d := d) hc₁ hc₃ hα0 hR2,
      rfl, rfl, rfl, rfl, rfl,
      big_bound hd hc₁ hc₁2 hc₂ hc₂1 hc₃ hα0 hα1 hClat
        ⟨hR2, hRsq, hK0L, hlogL, hlogA, hlogK2, h7⟩⟩

end MainTheorem