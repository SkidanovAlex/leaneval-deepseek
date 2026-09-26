import Mathlib
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.MiddleRange.exists_bound_Kfun_of_coincidence
import Submission.Work.Asymptotics.KaxisMid.exists_bound_Kfun_of_coincidence

namespace Work.Asymptotics

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Manifold Bundle

open Work.Kernels

/-!
# The diagonal value of the CKMRV kernel `K^{(d)}(τ,τ)` on the imaginary axis

The kernel `K^{(d)}(τ,z)` has a simple pole on the diagonal `τ = z` (`j(τ) = j(z)`); in the
formalisation (`Work.Kernels.Kfun`) the value there is the finite one obtained from the
convention `0⁻¹ = 0` for the reciprocal `(j(τ)−j(z))⁻¹` appearing in `Υ_±^{(d)}`.

This file bounds that finite diagonal value on the imaginary axis `τ = it`, `t ≥ 2`:

  `‖K^{(d)}(τ,τ)‖ ≤ C · (scale τ)^N`.

For `d = 8` the value is `0` (`Υ_+^{(8)}` and `Υ_-^{(8)}` both collapse on the diagonal).  For
`d = 24` the value is a *polynomial* expression in `τ, E₂, E₄, E₆, Δ` despite the individual
terms of the defining sum being exponentially large: after multiplying by the constant
`c₀ = 36·1728·π⁻²·i` and by `Δ(τ)` the sum collapses to

  `c₀ · Δ(τ) · K_+^{(24)}(τ,τ) = τ² · Ξ(τ)`,   `Ξ = 6E₄(E₄ − (E₂|₂S)²)W + 1728Δφ₀(5E₄ − 7(E₂|₂S)²)`,

with `W = E₆(E₄φ_{-2} + φ₂) − 2E₄²φ₀` (see `Work.Asymptotics.diagW`, `diagX`).  The bracket `W`
is `O(q·τ)` and `Ξ` is `O(q·τ²)` because `E₄ − E₂²` and `E₄² − E₆E₂` are `O(q)` at the cusp
(`delta1_isBigOq`, `eps_isBigOq`), while `Δ ≍ q` (`DeltaFun_lower`, `DeltaFun_upper`).
-/

/-! ## §1  The diagonal value as an explicit rational expression -/

/-- The constant `c₀ = 36·1728·π⁻²·i` of the coefficient matrix `Υ_+^{(24)}`. -/
abbrev c0 : ℂ := (36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I

/-- The matrix `Δ(τ)·M` where `M` is the constant matrix of `Υ_+^{(24)}` at a coincidence;
the relation `Δ·j = E₄³` has been used to clear the denominators. -/
def Mpos24Delta (τ : ℍ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![6 * DeltaFun τ, 0, -6 * DeltaFun τ;
     -12 * E4Fun τ ^ 3 + 5 * c1728 * DeltaFun τ, 0, 12 * E4Fun τ ^ 3 - 7 * c1728 * DeltaFun τ;
     6 * DeltaFun τ, 0, -6 * DeltaFun τ]

/-- The bracket `W = E₆(E₄φ_{-2} + φ₂) − 2E₄²φ₀` of the diagonal computation. -/
def diagW (τ : ℍ) : ℂ :=
  E6Fun τ * (E4Fun τ * phiNeg2 τ + phi2 τ) - 2 * E4Fun τ ^ 2 * phi0 τ

/-- The numerator `Ξ = 6E₄(E₄ − (E₂|₂S)²)W + 1728Δφ₀(5E₄ − 7(E₂|₂S)²)`. -/
def diagX (τ : ℍ) : ℂ :=
  6 * E4Fun τ * (E4Fun τ - E2S τ ^ 2) * diagW τ +
    1728 * DeltaFun τ * phi0 τ * (5 * E4Fun τ - 7 * E2S τ ^ 2)

private lemma c0_ne_zero : c0 ≠ 0 := by
  rw [c0]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (by rw [c1728]; norm_num))
      (zpow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))) Complex.I_ne_zero

private lemma c0_mul_DeltaFun_mul_inv3 (τ : ℍ) (x y z : ℂ) :
    c0 * (DeltaFun τ * ((c0 * DeltaFun τ)⁻¹ * x * y * z)) = x * y * z := by
  have h : c0 * DeltaFun τ ≠ 0 := mul_ne_zero c0_ne_zero (ClassicalFacts.DeltaFun_ne_zero τ)
  rw [show c0 * (DeltaFun τ * ((c0 * DeltaFun τ)⁻¹ * x * y * z))
      = (c0 * DeltaFun τ) * ((c0 * DeltaFun τ)⁻¹ * (x * y * z)) from by ring,
    ← mul_assoc, mul_inv_cancel₀ h, one_mul]

/-- `c₀·Δ(τ)·Υ_+^{(24)}(τ,τ)_{ij}` is the cleared entry `fk·M·fk`. -/
private lemma c0_mul_DeltaFun_mul_UpsilonPlus24_diag (τ : ℍ) (i j : Fin 3) :
    c0 * (DeltaFun τ * UpsilonPlus 24 τ τ i j) =
      fk (![14, 12, 10] i) τ * MiddleRange.Mpos24 (jInvariantFun τ) i j *
        fk (![4, 2, 0] j) τ := by
  rw [MiddleRange.UpsilonPlus24_entry_of_coincidence τ τ rfl i j]
  exact c0_mul_DeltaFun_mul_inv3 τ _ _ _

/-- `c₀·Δ(τ)·K_+^{(24)}(τ,τ)` as the cleared sum over the entries. -/
private lemma c0_mul_DeltaFun_mul_sum_KPlus24 (τ : ℍ) :
    c0 * (DeltaFun τ * KPlus 24 τ τ) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        phiVec τ i * (fk (![14, 12, 10] i) τ * MiddleRange.Mpos24 (jInvariantFun τ) i j *
          fk (![4, 2, 0] j) τ) * phitVec τ j := by
  rw [KPlus]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show c0 * (DeltaFun τ * (phiVec τ i * UpsilonPlus 24 τ τ i j * phitVec τ j)) =
      phiVec τ i * (c0 * (DeltaFun τ * UpsilonPlus 24 τ τ i j)) * phitVec τ j from by ring,
    c0_mul_DeltaFun_mul_UpsilonPlus24_diag]

/-- Multiplication by `Δ(τ)` replaces the matrix `M` of `Υ_+^{(24)}` at a coincidence by its
cleared form `Mpos24Delta`. -/
private lemma DeltaFun_mul_sum_Mpos24_diag (τ : ℍ) :
    DeltaFun τ * (∑ i : Fin 3, ∑ j : Fin 3,
        phiVec τ i * (fk (![14, 12, 10] i) τ * MiddleRange.Mpos24 (jInvariantFun τ) i j *
          fk (![4, 2, 0] j) τ) * phitVec τ j)
      = ∑ i : Fin 3, ∑ j : Fin 3,
        phiVec τ i * (fk (![14, 12, 10] i) τ * Mpos24Delta τ i j *
          fk (![4, 2, 0] j) τ) * phitVec τ j := by
  have hΔ : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  simp only [Fin.sum_univ_three, Fin.isValue, Int.reduceEq, reduceIte, MiddleRange.Mpos24,
    Mpos24Delta, phiVec, phitVec, fk, phiNeg2, phi0, phi2, E8Fun, E10Fun, E14Fun, c1728,
    jInvariantFun, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply, mul_zero, zero_mul]
  field_simp
  ring

/-- The cleared sum is a polynomial expression in `τ, E₂, E₄, E₆, Δ` and `(E₂|₂S)`. -/
private lemma diag_sum_identity (τ : ℍ) :
    (∑ i : Fin 3, ∑ j : Fin 3,
        phiVec τ i * (fk (![14, 12, 10] i) τ * Mpos24Delta τ i j *
          fk (![4, 2, 0] j) τ) * phitVec τ j)
      = (τ : ℂ) ^ 2 * DeltaFun τ * diagX τ := by
  simp only [Fin.sum_univ_three, Fin.isValue, Int.reduceEq, reduceIte, Mpos24Delta, phiVec,
    phitVec, fk, phiNeg2, phi0, phi2, E8Fun, E10Fun, E14Fun, c1728, diagX, diagW,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.of_apply, mul_zero, zero_mul]
  ring

/-- **The diagonal value of `K_+^{(24)}`.**  `c₀Δ(τ)K_+^{(24)}(τ,τ) = τ²Ξ(τ)`. -/
theorem c0_mul_DeltaFun_mul_KPlus24_diag (τ : ℍ) :
    c0 * (DeltaFun τ * KPlus 24 τ τ) = (τ : ℂ) ^ 2 * diagX τ := by
  have hΔ : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have h1 : DeltaFun τ * (c0 * (DeltaFun τ * KPlus 24 τ τ)) =
      DeltaFun τ * ((τ : ℂ) ^ 2 * diagX τ) := by
    rw [c0_mul_DeltaFun_mul_sum_KPlus24, DeltaFun_mul_sum_Mpos24_diag, diag_sum_identity]
    ring
  exact mul_left_cancel₀ hΔ h1


/-! ## §2  Bounds for the atoms and for the numerator `Ξ` -/

private lemma one_le_coe_norm {τ : ℍ} (hτ : 1 ≤ τ.im) : 1 ≤ ‖(τ : ℂ)‖ :=
  le_trans hτ (im_le_coe_norm τ)

private lemma norm_six_I_div : ∀ τ : ℍ,
    ‖(6 : ℂ) * Complex.I / ((Real.pi : ℂ) * (τ : ℂ))‖
      = 6 / (Real.pi * ‖(τ : ℂ)‖) := by
  intro τ
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]

/-- `‖(E₂|₂S) τ‖` is bounded on `{1 ≤ Im τ}`. -/
private lemma exists_norm_E2S_le :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖E2S τ‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := E2Fun_bound
  refine ⟨C + 6 / Real.pi, by positivity, fun τ hτ => ?_⟩
  have hτ1 := one_le_coe_norm hτ
  have h6 : ‖(6 : ℂ) * Complex.I / ((Real.pi : ℂ) * (τ : ℂ))‖ ≤ 6 / Real.pi := by
    rw [norm_six_I_div τ]
    exact div_le_div_of_nonneg_left (by norm_num) Real.pi_pos (by nlinarith [Real.pi_pos, hτ1])
  rw [TildeFacts.E2S_eq]
  calc ‖E2Fun τ - 6 * Complex.I / ((Real.pi : ℂ) * (τ : ℂ))‖
      ≤ ‖E2Fun τ‖ + ‖(6 : ℂ) * Complex.I / ((Real.pi : ℂ) * (τ : ℂ))‖ := norm_sub_le _ _
    _ ≤ C + 6 / Real.pi := add_le_add (h τ hτ) h6

/-- `‖E₂ τ − (E₂|₂S) τ‖ = ‖6i/(πτ)‖ → 0` at the cusp. -/
private lemma norm_E2_sub_E2S_le : ∀ τ : ℍ,
    ‖E2Fun τ - E2S τ‖ = 6 / (Real.pi * ‖(τ : ℂ)‖) := by
  intro τ
  rw [TildeFacts.E2S_eq,
    show E2Fun τ - (E2Fun τ - 6 * Complex.I / ((Real.pi : ℂ) * (τ : ℂ)))
      = 6 * Complex.I / ((Real.pi : ℂ) * (τ : ℂ)) from by ring]
  exact norm_six_I_div τ

/-- `E₄ − (E₂|₂S)²` is bounded on `{1 ≤ Im τ}`. -/
private lemma exists_norm_E4_sub_E2S_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖E4Fun τ - E2S τ ^ 2‖ ≤ C := by
  obtain ⟨C1, hC1, h1⟩ := delta1_isBigOq
  obtain ⟨C2, hC2, h2⟩ := E2Fun_bound
  obtain ⟨C3, hC3, h3⟩ := exists_norm_E2S_le
  refine ⟨C1 + (6 / Real.pi) * (C2 + C3), by positivity, fun τ hτ => ?_⟩
  have hq : ‖qParamFun τ‖ ≤ 1 := norm_qParamFun_le_one τ hτ
  have hd : ‖E4Fun τ - E2Fun τ ^ 2‖ ≤ C1 := by
    calc ‖E4Fun τ - E2Fun τ ^ 2‖ ≤ C1 * ‖qParamFun τ‖ ^ 1 := h1 τ hτ
      _ = C1 * ‖qParamFun τ‖ := by rw [pow_one]
      _ ≤ C1 * 1 := mul_le_mul_of_nonneg_left hq hC1.le
      _ = C1 := mul_one C1
  have hfac : E4Fun τ - E2S τ ^ 2
      = (E4Fun τ - E2Fun τ ^ 2) + (E2Fun τ - E2S τ) * (E2Fun τ + E2S τ) := by ring
  have h6 : ‖E2Fun τ - E2S τ‖ ≤ 6 / Real.pi := by
    rw [norm_E2_sub_E2S_le τ]
    exact div_le_div_of_nonneg_left (by norm_num) Real.pi_pos
      (by nlinarith [Real.pi_pos, one_le_coe_norm hτ])
  have hsum : ‖E2Fun τ + E2S τ‖ ≤ C2 + C3 := by
    calc ‖E2Fun τ + E2S τ‖ ≤ ‖E2Fun τ‖ + ‖E2S τ‖ := norm_add_le _ _
      _ ≤ C2 + C3 := add_le_add (h2 τ hτ) (h3 τ hτ)
  rw [hfac]
  calc ‖(E4Fun τ - E2Fun τ ^ 2) + (E2Fun τ - E2S τ) * (E2Fun τ + E2S τ)‖
      ≤ ‖E4Fun τ - E2Fun τ ^ 2‖ + ‖(E2Fun τ - E2S τ) * (E2Fun τ + E2S τ)‖ := norm_add_le _ _
    _ = ‖E4Fun τ - E2Fun τ ^ 2‖ + ‖E2Fun τ - E2S τ‖ * ‖E2Fun τ + E2S τ‖ := by rw [norm_mul]
    _ ≤ C1 + (6 / Real.pi) * (C2 + C3) := by
        refine add_le_add hd (mul_le_mul h6 hsum (norm_nonneg _) (by positivity))

/-- `5E₄ − 7(E₂|₂S)²` is bounded on `{1 ≤ Im τ}`. -/
private lemma exists_norm_five_E4_sub_seven_E2S_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖5 * E4Fun τ - 7 * E2S τ ^ 2‖ ≤ C := by
  obtain ⟨C1, hC1, h1⟩ := E4Fun_bound
  obtain ⟨C2, hC2, h2⟩ := exists_norm_E2S_le
  refine ⟨5 * C1 + 7 * C2 ^ 2, by positivity, fun τ hτ => ?_⟩
  have h : 5 * E4Fun τ - 7 * E2S τ ^ 2
      = 5 * E4Fun τ - 7 * (E2S τ * E2S τ) := by ring
  calc ‖5 * E4Fun τ - 7 * E2S τ ^ 2‖
      = ‖5 * E4Fun τ - 7 * (E2S τ * E2S τ)‖ := by rw [h]
    _ ≤ ‖5 * E4Fun τ‖ + ‖7 * (E2S τ * E2S τ)‖ := norm_sub_le _ _
    _ = 5 * ‖E4Fun τ‖ + 7 * ‖E2S τ‖ * ‖E2S τ‖ := by
        simp only [norm_mul, Complex.norm_ofNat]
        ring
    _ ≤ 5 * C1 + 7 * C2 * C2 := by
        have hA : ‖E4Fun τ‖ ≤ C1 := h1 τ hτ
        have hB : ‖E2S τ‖ ≤ C2 := h2 τ hτ
        have hB0 : (0:ℝ) ≤ ‖E2S τ‖ := norm_nonneg _
        nlinarith [hA, hB, hB0, hC1.le, hC2.le, mul_nonneg hB0 hB0,
          mul_le_mul hB hB hB0 hC2.le]
    _ = 5 * C1 + 7 * C2 ^ 2 := by ring

/-- `‖φ₀ τ‖ ≤ C(1 + ‖τ‖)`. -/
private lemma exists_norm_phi0_le :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖phi0 τ‖ ≤ C * (1 + ‖(τ : ℂ)‖) := by
  obtain ⟨C1, hC1, h1⟩ := E2Fun_bound
  refine ⟨C1 + 3 / Real.pi, by positivity, fun τ hτ => ?_⟩
  have hb : ‖E2Fun τ‖ ≤ C1 := h1 τ hτ
  have h : phi0 τ = (τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ) := rfl
  rw [h]
  have h3 : ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 3 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  calc ‖(τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)‖
      ≤ ‖(τ : ℂ) * E2Fun τ‖ + ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ := norm_sub_le _ _
    _ = ‖(τ : ℂ)‖ * ‖E2Fun τ‖ + 3 / Real.pi := by rw [norm_mul, h3]
    _ ≤ (C1 + 3 / Real.pi) * (1 + ‖(τ : ℂ)‖) := by
        have hτnn : (0:ℝ) ≤ ‖(τ : ℂ)‖ := norm_nonneg _
        have h3nn : (0:ℝ) ≤ 3 / Real.pi := by positivity
        have h1' : ‖(τ : ℂ)‖ * ‖E2Fun τ‖ ≤ ‖(τ : ℂ)‖ * C1 :=
          mul_le_mul_of_nonneg_left hb hτnn
        nlinarith [h1', hC1, hτnn, h3nn]

/-- `W` is `O(q·τ)`. -/
private lemma diagW_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖diagW τ‖ ≤ C * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖ := by
  obtain ⟨C1, hC1, h1⟩ := delta1_isBigOq
  obtain ⟨C2, hC2, h2⟩ := eps_isBigOq
  obtain ⟨C3, hC3, h3⟩ := E2Fun_bdd
  obtain ⟨C4, hC4, h4⟩ := E6Fun_bdd
  have hG : ∀ τ : ℍ, 1 ≤ τ.im →
      ‖E6Fun τ * (E4Fun τ + E2Fun τ ^ 2) - 2 * E4Fun τ ^ 2 * E2Fun τ‖
        ≤ (C4 * C1 + 2 * C3 * C2) * ‖qParamFun τ‖ := by
    intro τ hτ
    have hA : ‖E2Fun τ ^ 2 - E4Fun τ‖ ≤ C1 * ‖qParamFun τ‖ := by
      have := h1 τ hτ
      rwa [pow_one, norm_sub_rev] at this
    have hB : ‖E4Fun τ ^ 2 - E6Fun τ * E2Fun τ‖ ≤ C2 * ‖qParamFun τ‖ := by
      have := h2 τ hτ
      rwa [pow_one] at this
    have hE2 : ‖E2Fun τ‖ ≤ C3 := by
      have := h3 τ hτ
      simpa [Real.rpow_zero] using this
    have hE6 : ‖E6Fun τ‖ ≤ C4 := by
      have := h4 τ hτ
      simpa [Real.rpow_zero] using this
    have hfac : E6Fun τ * (E4Fun τ + E2Fun τ ^ 2) - 2 * E4Fun τ ^ 2 * E2Fun τ
        = -(E6Fun τ * (E2Fun τ ^ 2 - E4Fun τ))
          - 2 * E2Fun τ * (E4Fun τ ^ 2 - E6Fun τ * E2Fun τ) := by ring
    rw [hfac]
    calc ‖-(E6Fun τ * (E2Fun τ ^ 2 - E4Fun τ))
            - 2 * E2Fun τ * (E4Fun τ ^ 2 - E6Fun τ * E2Fun τ)‖
        ≤ ‖-(E6Fun τ * (E2Fun τ ^ 2 - E4Fun τ))‖
            + ‖2 * E2Fun τ * (E4Fun τ ^ 2 - E6Fun τ * E2Fun τ)‖ := norm_sub_le _ _
      _ = ‖E6Fun τ‖ * ‖E2Fun τ ^ 2 - E4Fun τ‖
            + 2 * ‖E2Fun τ‖ * ‖E4Fun τ ^ 2 - E6Fun τ * E2Fun τ‖ := by
          simp only [norm_neg, norm_mul, Complex.norm_ofNat]
      _ ≤ C4 * (C1 * ‖qParamFun τ‖) + 2 * C3 * (C2 * ‖qParamFun τ‖) := by
          refine add_le_add
            (mul_le_mul hE6 hA (norm_nonneg _) hC4.le) ?_
          refine mul_le_mul ?_ hB (norm_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hE2 (by norm_num)
      _ = (C4 * C1 + 2 * C3 * C2) * ‖qParamFun τ‖ := by ring
  refine ⟨(C4 * C1 + 2 * C3 * C2) + (6 / Real.pi) * C2, by positivity, fun τ hτ => ?_⟩
  have hH : ‖E4Fun τ ^ 2 - E6Fun τ * E2Fun τ‖ ≤ C2 * ‖qParamFun τ‖ := by
    have := h2 τ hτ
    rwa [pow_one] at this
  rw [show diagW τ = (τ : ℂ) * (E6Fun τ * (E4Fun τ + E2Fun τ ^ 2) - 2 * E4Fun τ ^ 2 * E2Fun τ)
      + (6 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 2 - E6Fun τ * E2Fun τ) from by
    simp only [diagW, phiNeg2, phi0, phi2]; ring]
  have h6 : ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 6 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  calc ‖(τ : ℂ) * (E6Fun τ * (E4Fun τ + E2Fun τ ^ 2) - 2 * E4Fun τ ^ 2 * E2Fun τ)
          + (6 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 2 - E6Fun τ * E2Fun τ)‖
      ≤ ‖(τ : ℂ) * (E6Fun τ * (E4Fun τ + E2Fun τ ^ 2) - 2 * E4Fun τ ^ 2 * E2Fun τ)‖
          + ‖(6 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 2 - E6Fun τ * E2Fun τ)‖ :=
        norm_add_le _ _
    _ = ‖(τ : ℂ)‖ * ‖E6Fun τ * (E4Fun τ + E2Fun τ ^ 2) - 2 * E4Fun τ ^ 2 * E2Fun τ‖
          + (6 / Real.pi) * ‖E4Fun τ ^ 2 - E6Fun τ * E2Fun τ‖ := by rw [norm_mul, norm_mul, h6]
    _ ≤ ‖(τ : ℂ)‖ * ((C4 * C1 + 2 * C3 * C2) * ‖qParamFun τ‖)
          + (6 / Real.pi) * (C2 * ‖qParamFun τ‖) := by
        refine add_le_add (mul_le_mul_of_nonneg_left (hG τ hτ) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hH (by positivity))
    _ ≤ ((C4 * C1 + 2 * C3 * C2) + (6 / Real.pi) * C2) * (1 + ‖(τ : ℂ)‖) *
          ‖qParamFun τ‖ := by
        have hqpos : 0 < ‖qParamFun τ‖ := norm_pos_iff.mpr (qParamFun_ne_zero' τ)
        have hτnn : (0:ℝ) ≤ ‖(τ : ℂ)‖ := norm_nonneg _
        have hK : (0:ℝ) ≤ C4 * C1 + 2 * C3 * C2 := by positivity
        have hK2 : (0:ℝ) ≤ (6 / Real.pi) * C2 := by positivity
        rw [show ‖(τ : ℂ)‖ * ((C4 * C1 + 2 * C3 * C2) * ‖qParamFun τ‖)
              + (6 / Real.pi) * (C2 * ‖qParamFun τ‖)
            = ((C4 * C1 + 2 * C3 * C2) * ‖(τ : ℂ)‖ + (6 / Real.pi) * C2) *
                ‖qParamFun τ‖ from by ring]
        rw [mul_le_mul_iff_of_pos_right hqpos]
        nlinarith [hK, hK2, hτnn, mul_nonneg hK hτnn, mul_nonneg hK2 hτnn]

/-- `Ξ` is `O(q·τ²)`. -/
private lemma diagX_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖diagX τ‖ ≤ C * (1 + ‖(τ : ℂ)‖) ^ 2 * ‖qParamFun τ‖ := by
  obtain ⟨CW, hCW, hW⟩ := diagW_bound
  obtain ⟨CA, hCA, hA⟩ := E4Fun_bound
  obtain ⟨C2, hC2, h2⟩ := exists_norm_E4_sub_E2S_sq_le
  obtain ⟨C5, hC5, h5⟩ := exists_norm_five_E4_sub_seven_E2S_sq_le
  obtain ⟨Cp, hCp, hp⟩ := exists_norm_phi0_le
  obtain ⟨CD, hCD, hD⟩ := DeltaFun_upper
  refine ⟨6 * CA * C2 * CW + 1728 * CD * Cp * C5, by positivity, fun τ hτ => ?_⟩
  have hq := norm_nonneg (qParamFun τ)
  have hS : (1:ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by linarith [norm_nonneg (τ : ℂ)]
  rw [diagX]
  calc ‖6 * E4Fun τ * (E4Fun τ - E2S τ ^ 2) * diagW τ
        + 1728 * DeltaFun τ * phi0 τ * (5 * E4Fun τ - 7 * E2S τ ^ 2)‖
      ≤ ‖6 * E4Fun τ * (E4Fun τ - E2S τ ^ 2) * diagW τ‖
        + ‖1728 * DeltaFun τ * phi0 τ * (5 * E4Fun τ - 7 * E2S τ ^ 2)‖ := norm_add_le _ _
    _ = 6 * ‖E4Fun τ‖ * ‖E4Fun τ - E2S τ ^ 2‖ * ‖diagW τ‖
        + 1728 * ‖DeltaFun τ‖ * ‖phi0 τ‖ * ‖5 * E4Fun τ - 7 * E2S τ ^ 2‖ := by
        simp only [norm_mul, Complex.norm_ofNat]
    _ ≤ 6 * CA * C2 * CW * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖
        + 1728 * CD * Cp * C5 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖ := by
        refine add_le_add ?_ ?_
        · calc 6 * ‖E4Fun τ‖ * ‖E4Fun τ - E2S τ ^ 2‖ * ‖diagW τ‖
              = (6 * ‖E4Fun τ‖ * ‖E4Fun τ - E2S τ ^ 2‖) * ‖diagW τ‖ := by ring
            _ ≤ (6 * CA * C2) * (CW * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖) := by
                refine mul_le_mul ?_ (hW τ hτ) (norm_nonneg _) (by positivity)
                exact mul_le_mul (mul_le_mul_of_nonneg_left (hA τ hτ) (by norm_num))
                  (h2 τ hτ) (norm_nonneg _) (by positivity)
            _ = 6 * CA * C2 * CW * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖ := by ring
        · calc 1728 * ‖DeltaFun τ‖ * ‖phi0 τ‖ * ‖5 * E4Fun τ - 7 * E2S τ ^ 2‖
              = (1728 * ‖DeltaFun τ‖ * ‖5 * E4Fun τ - 7 * E2S τ ^ 2‖) * ‖phi0 τ‖ := by ring
            _ ≤ (1728 * (CD * ‖qParamFun τ‖) * C5) * (Cp * (1 + ‖(τ : ℂ)‖)) := by
                refine mul_le_mul ?_ (hp τ hτ) (norm_nonneg _) (by positivity)
                exact mul_le_mul (mul_le_mul_of_nonneg_left (hD τ hτ) (by norm_num))
                  (h5 τ hτ) (norm_nonneg _) (by positivity)
            _ = 1728 * CD * Cp * C5 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖ := by ring
    _ ≤ (6 * CA * C2 * CW + 1728 * CD * Cp * C5) * (1 + ‖(τ : ℂ)‖) ^ 2 *
          ‖qParamFun τ‖ := by
        have hK : (0:ℝ) ≤ 6 * CA * C2 * CW + 1728 * CD * Cp * C5 := by positivity
        have hSS : (1 + ‖(τ : ℂ)‖) ≤ (1 + ‖(τ : ℂ)‖) ^ 2 := by nlinarith [hS]
        calc 6 * CA * C2 * CW * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖
              + 1728 * CD * Cp * C5 * (1 + ‖(τ : ℂ)‖) * ‖qParamFun τ‖
            = (6 * CA * C2 * CW + 1728 * CD * Cp * C5) * (1 + ‖(τ : ℂ)‖) *
                ‖qParamFun τ‖ := by ring
          _ ≤ (6 * CA * C2 * CW + 1728 * CD * Cp * C5) * (1 + ‖(τ : ℂ)‖) ^ 2 *
                ‖qParamFun τ‖ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSS hK) hq

/-- `‖c₀·Δ·K_+^{(24)}(τ,τ)‖` in terms of the norms of the three factors. -/
private lemma norm_c0_mul_KPlus24 (τ : ℍ) :
    ‖c0 * (DeltaFun τ * KPlus 24 τ τ)‖
      = ‖c0‖ * (‖DeltaFun τ‖ * ‖KPlus 24 τ τ‖) := by
  conv_lhs => rw [norm_mul]
  congr 1
  rw [norm_mul]

/-- `‖K_+^{(24)}(τ,τ)‖ = O(τ⁴)` on the imaginary axis. -/
private theorem KPlus24_diag_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖KPlus 24 τ τ‖ ≤ C * (1 + ‖(τ : ℂ)‖) ^ 4 := by
  obtain ⟨CX, hCX, hX⟩ := diagX_bound
  obtain ⟨cd, hcd, hcd'⟩ := DeltaFun_lower
  have hc0 : 0 < ‖c0‖ := norm_pos_iff.mpr c0_ne_zero
  refine ⟨CX / (‖c0‖ * cd) + 1, by positivity, fun τ hτ => ?_⟩
  have hq : 0 < ‖qParamFun τ‖ := norm_pos_iff.mpr (qParamFun_ne_zero' τ)
  have hΔ : ‖DeltaFun τ‖ ≠ 0 := norm_ne_zero_iff.mpr (ClassicalFacts.DeltaFun_ne_zero τ)
  have hnorm : ‖c0‖ * (‖DeltaFun τ‖ * ‖KPlus 24 τ τ‖)
      = ‖(τ : ℂ)‖ ^ 2 * ‖diagX τ‖ := by
    calc ‖c0‖ * (‖DeltaFun τ‖ * ‖KPlus 24 τ τ‖)
        = ‖c0 * (DeltaFun τ * KPlus 24 τ τ)‖ := (norm_c0_mul_KPlus24 τ).symm
      _ = ‖(τ : ℂ) ^ 2 * diagX τ‖ := by rw [c0_mul_DeltaFun_mul_KPlus24_diag]
      _ = ‖(τ : ℂ)‖ ^ 2 * ‖diagX τ‖ := by rw [norm_mul, norm_pow]
  have h3 : ‖KPlus 24 τ τ‖ * (cd * ‖qParamFun τ‖)
      ≤ ‖(τ : ℂ)‖ ^ 2 * (CX * (1 + ‖(τ : ℂ)‖) ^ 2 * ‖qParamFun τ‖) / ‖c0‖ := by
    calc ‖KPlus 24 τ τ‖ * (cd * ‖qParamFun τ‖)
        ≤ ‖KPlus 24 τ τ‖ * ‖DeltaFun τ‖ :=
          mul_le_mul_of_nonneg_left (hcd' τ hτ) (norm_nonneg _)
      _ = ‖(τ : ℂ)‖ ^ 2 * ‖diagX τ‖ / ‖c0‖ := by
          rw [eq_div_iff (ne_of_gt hc0)]
          simpa [mul_comm, mul_left_comm, mul_assoc] using hnorm
      _ ≤ ‖(τ : ℂ)‖ ^ 2 * (CX * (1 + ‖(τ : ℂ)‖) ^ 2 * ‖qParamFun τ‖) / ‖c0‖ := by
          gcongr
          exact hX τ hτ
  have h4 : ‖KPlus 24 τ τ‖ ≤ CX / (‖c0‖ * cd) * (1 + ‖(τ : ℂ)‖) ^ 2 * ‖(τ : ℂ)‖ ^ 2 := by
    have h5 := le_div_iff₀ (by positivity : (0:ℝ) < cd * ‖qParamFun τ‖) |>.mpr h3
    refine h5.trans ?_
    have h6 : ‖(τ : ℂ)‖ ^ 2 * (CX * (1 + ‖(τ : ℂ)‖) ^ 2 * ‖qParamFun τ‖) / ‖c0‖
        / (cd * ‖qParamFun τ‖)
        = CX / (‖c0‖ * cd) * (1 + ‖(τ : ℂ)‖) ^ 2 * ‖(τ : ℂ)‖ ^ 2 := by
      field_simp [ne_of_gt hc0, ne_of_gt hcd, ne_of_gt hq]
    exact le_of_eq h6
  calc ‖KPlus 24 τ τ‖
      ≤ CX / (‖c0‖ * cd) * (1 + ‖(τ : ℂ)‖) ^ 2 * ‖(τ : ℂ)‖ ^ 2 := h4
    _ ≤ CX / (‖c0‖ * cd) * (1 + ‖(τ : ℂ)‖) ^ 4 := by
        have hK : (0:ℝ) ≤ CX / (‖c0‖ * cd) := by positivity
        have hs2 : ‖(τ : ℂ)‖ ^ 2 ≤ (1 + ‖(τ : ℂ)‖) ^ 2 := by
          nlinarith [norm_nonneg (τ : ℂ)]
        calc CX / (‖c0‖ * cd) * (1 + ‖(τ : ℂ)‖) ^ 2 * ‖(τ : ℂ)‖ ^ 2
            = (CX / (‖c0‖ * cd) * (1 + ‖(τ : ℂ)‖) ^ 2) * ‖(τ : ℂ)‖ ^ 2 := by ring
          _ ≤ (CX / (‖c0‖ * cd) * (1 + ‖(τ : ℂ)‖) ^ 2) * (1 + ‖(τ : ℂ)‖) ^ 2 :=
              mul_le_mul_of_nonneg_left hs2 (mul_nonneg hK (by positivity))
          _ = CX / (‖c0‖ * cd) * (1 + ‖(τ : ℂ)‖) ^ 4 := by ring
    _ ≤ (CX / (‖c0‖ * cd) + 1) * (1 + ‖(τ : ℂ)‖) ^ 4 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- **The diagonal bound for `K^{(d)}` on `{1 ≤ Im τ}`.** -/
private theorem Kfun_diag_bound_im_one (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖Kfun ℓ d τ τ‖ ≤ C * (scale τ) ^ N := by
  rcases hd with rfl | rfl
  · refine ⟨1, 0, one_pos, le_refl 0, fun τ _ => ?_⟩
    rw [Kfun, MiddleRange.KPlus_eight_eq_zero rfl,
      MiddleRange.KMinus_eq_zero_of_coincidence ℓ (Or.inl rfl) rfl, add_zero, zero_div,
      norm_zero, Real.rpow_zero, mul_one]
    exact zero_le_one
  · obtain ⟨C4, hC4, h4⟩ := KPlus24_diag_bound
    refine ⟨C4 * 8 + 1, 4, by positivity, by norm_num, fun τ hτ => ?_⟩
    have hK : Kfun ℓ 24 τ τ = KPlus 24 τ τ / 2 := by
      rw [Kfun, MiddleRange.KMinus_eq_zero_of_coincidence ℓ (Or.inr rfl) rfl, add_zero]
    have hS : (1:ℝ) ≤ scale τ := one_le_scale τ
    have hτle : 1 + ‖(τ : ℂ)‖ ≤ 2 * scale τ := by
      have := coe_norm_le_scale τ; linarith
    have h4' := h4 τ hτ
    have hmain : ‖Kfun ℓ 24 τ τ‖ ≤ (C4 * 8 + 1) * (scale τ) ^ 4 := by
      rw [hK, norm_div, Complex.norm_ofNat]
      calc ‖KPlus 24 τ τ‖ / 2 ≤ (C4 * (1 + ‖(τ : ℂ)‖) ^ 4) / 2 := by linarith
        _ ≤ (C4 * (2 * scale τ) ^ 4) / 2 := by
            have hpow : (1 + ‖(τ : ℂ)‖) ^ 4 ≤ (2 * scale τ) ^ 4 :=
              pow_le_pow_left₀ (by positivity) hτle 4
            linarith [mul_le_mul_of_nonneg_left hpow hC4.le]
        _ = C4 * 8 * (scale τ) ^ 4 := by ring
        _ ≤ (C4 * 8 + 1) * (scale τ) ^ 4 := by
            have hsp : (1:ℝ) ≤ (scale τ) ^ 4 := one_le_pow₀ hS
            nlinarith [hC4.le, hsp]
    have hconv : (C4 * 8 + 1) * (scale τ) ^ (4:ℕ)
        = (C4 * 8 + 1) * (scale τ) ^ (((4:ℕ)) : ℝ) := by
      rw [Real.rpow_natCast]
    exact hmain.trans (le_of_eq hconv)

/-- **Asymptotic bound for the diagonal of the CKMRV kernel.** -/
theorem Funnel_Kfun_diag_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane), τ.re = 0 → 2 ≤ τ.im →
      ‖Work.Kernels.Kfun ℓ d τ τ‖ ≤ C * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨C, N, hC, hN, h⟩ := Kfun_diag_bound_im_one ℓ d hd
  exact ⟨C, N, hC, hN, fun τ _ h2 => h τ (by linarith)⟩

end

end Work.Asymptotics
