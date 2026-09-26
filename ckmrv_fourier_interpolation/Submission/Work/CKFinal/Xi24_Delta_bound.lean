import Mathlib
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.KPlusFunnel.Atoms
import Submission.Work.Asymptotics.KPlusFunnel.ZFacts
import Submission.Work.Asymptotics.ZAtomsThird.cusp_forms
import Submission.Work.Asymptotics.ZAtomsThird.first_order
import Submission.Work.Asymptotics.Xi24_bound_E
import Submission.Work.Asymptotics.Xi24_low_bound
import Submission.Work.CKFinal.Xi8_Delta_bound
import Submission.Work.CKFinal.Xi24_G_bounds

/-
# The moderate-growth bound for `Δ(τ)Ξ₂₄(τ,z)` on the strip `{Im ≥ 1/3}`

This file proves `Work.CKFinal.Xi24_Delta_bound`:

`∃ C A, 0 < C ∧ 0 ≤ A ∧ ∀ τ z, 1/3 ≤ Im τ → 1/3 ≤ Im z →`
`  ‖Δ(τ) Ξ₂₄(τ,z)‖ ≤ C (1+‖τ‖)^A (1+‖z‖)^A exp(-π(4 Im τ + Im z))`,

the moderate-growth input for the Fourier interpolation formula of CKMRV,
Ann. of Math. 196 (2022).  Since `Ξ₂₄` carries the simple pole of the kernel `K₊^{(24)}` at
`j(τ) = j(z)`, the factor `Δ(τ)` alone is *not* enough to make the inequality elementary: the
naive term-by-term estimate only gives `O(q_τq_z)`, while the truth is `O(q_τ²q_z)`.

## Structure of the argument

Write `q(τ) = exp(2πiτ)` and, at `τ` resp. `z`,

`ζ = E₂E₆ - E₄²`, `η = E₂E₄ - E₆`, `δ = E₄ - E₂²`, `rr = 5E₄² - 7E₄E₂² + 2E₆E₂`,
`Φ₈ = E₄(τE₆ - 2φ₀E₄) + E₆φ₂`, `σ = j(z)δ(z) - 288`.

1. `Work.Asymptotics.Xi24_cancelled` writes `Ξ₂₄` as six products of `τ`-atoms and `z`-atoms.
   Multiplying by `Δ(τ)` and using `Δ(τ)j(τ) = E₄(τ)³`, together with `1728Δ = E₄³ - E₆²`,
   the whole cleared expression is, in one `field_simp; ring` step,

   `Δ(τ)Ξ₂₄(τ,z) = (P₁+P₂) - (P₃+P₄) - (P₅+P₆)`, where

   * `P₁ = 6τδ·W₁` with `W₁ = E₄(τ)⁴(ζE₂-ηE₄) + 1728Δ(τ) = O(q_τ²)`,
   * `P₂ = 1728τΔ(τ)·(G₁-6δ)` with `G₁ = E₂E₄³F₃ + E₄²E₆F₄ + E₂²E₄E₆F₅ = 6δ + O(q_τq_z)`,
   * `P₃ = (36i/π)δ·W₂` with `W₂ = E₄(τ)⁴ζ + 1008Δ(τ) = O(q_τ²)`,
   * `P₄ = (5184i/π)Δ(τ)·(G₂-7δ)` with `G₂ = E₄³F₃ + 2E₂E₄E₆F₅ = 7δ + O(q_τq_z)`,
   * `P₅ = 6Δ(τ)E₄(τ)Φ₈(τ)σ(z)`,
   * `P₆ = 1728Δ(τ)²φ₀(τ)·rr(z)E₄(z)²/Δ(z)`.

   Here `F₃ = 5E₄(z) - 7E₂(z)² + 2`, `F₄ = E₂(z)² - 1`, `F₅ = E₄(z) - 1` are the three
   `z`-atoms, all `O(q_z)`.

   The two cancellations `W₁ = O(q_τ²)`, `W₂ = O(q_τ²)` (the coefficients `1728` and `1008`
   are exactly the values killing the `q_τ`-terms) and `G₁ - 6δ = O(q_τq_z)`,
   `G₂ - 7δ = O(q_τq_z)` are the content of the helper lemmas `Xi24_W1_bound`,
   `Xi24_W2_bound`, `Xi24_G_bounds` (and `Xi24_z_atom_bounds` for `rr(z)E₄(z)²/Δ(z)`).

2. With `‖Δ(τ)‖ ≤ C_d q_τ`, `‖E₄(τ)‖ ≤ B`, `‖φ₀(τ)‖ ≤ E(1+‖τ‖)`,
   `‖Φ₈(τ)‖ ≤ C_ph(1+‖τ‖)q_τ` (`Work.CKFinal.phi8_bound_third`, proved for `Ξ₈` in
   `Xi8_Delta_bound.lean`), `‖δ(z)‖ ≤ C_c q_z`, `‖σ(z)‖ ≤ C_σ q_z`
   (`Work.Asymptotics.jz_sigma_third`) and `‖rr(z)E₄(z)²/Δ(z)‖ ≤ C_za q_z`, every piece is
   `≤ K_j (1+‖τ‖) q_τ² q_z`, hence `‖Δ(τ)Ξ₂₄(τ,z)‖ ≤ K (1+‖τ‖) q_τ² q_z`.

3. Finally `‖q(τ)‖² = exp(-4π Im τ)` and `‖q(z)‖ ≤ exp(-π Im z)` give the assertion with
   `A = 1` (the given form allows the extra factor `1+‖z‖ ≥ 1`).

The constants are existential and large (the leading numerical factors come from
`E₄`-atoms at height `1/3`); no attempt is made to optimise them.
-/

namespace Work.CKFinal

open UpperHalfPlane
open Work.Kernels

set_option maxHeartbeats 4000000

noncomputable section

/-- `1728 Δ(τ) = E₄(τ)³ - E₆(τ)²`. -/
private lemma DeltaFun_1728 (τ : UpperHalfPlane) :
    (1728 : ℂ) * Work.Kernels.DeltaFun τ
      = Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.E6Fun τ ^ 2 := by
  have h : Work.Kernels.DeltaFun τ
      = (Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.E6Fun τ ^ 2) / 1728 := by
    rw [show Work.Kernels.DeltaFun τ = ModularForm.discriminant τ from rfl,
      ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
  rw [h]
  field_simp

private lemma norm_36i_pi : ‖(36 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 36 / Real.pi := by
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
    Complex.norm_of_nonneg Real.pi_pos.le]

private lemma norm_5184i_pi : ‖(5184 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 5184 / Real.pi := by
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
    Complex.norm_of_nonneg Real.pi_pos.le]

private lemma q_le_one_third {z : ℍ} (hz : (1 : ℝ) / 3 ≤ z.im) : ‖qParamFun z‖ ≤ 1 :=
  le_trans (Work.Asymptotics.norm_qParam_le_third hz) (by norm_num)

private lemma E_bound {C : ℝ} {z : ℍ} (h : ‖E2Fun z - 1‖ ≤ C * ‖qParamFun z‖)
    (hC : 0 ≤ C) (hq : ‖qParamFun z‖ ≤ 1) : ‖E2Fun z‖ ≤ 1 + C := by
  calc ‖E2Fun z‖ = ‖(E2Fun z - 1) + 1‖ := by ring_nf
    _ ≤ ‖E2Fun z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ C * ‖qParamFun z‖ + 1 := by rw [norm_one]; linarith
    _ ≤ C * 1 + 1 := by nlinarith [hq, hC]
    _ = 1 + C := by ring

private lemma E_bound4 {C : ℝ} {z : ℍ} (h : ‖E4Fun z - 1‖ ≤ C * ‖qParamFun z‖)
    (hC : 0 ≤ C) (hq : ‖qParamFun z‖ ≤ 1) : ‖E4Fun z‖ ≤ 1 + C := by
  calc ‖E4Fun z‖ = ‖(E4Fun z - 1) + 1‖ := by ring_nf
    _ ≤ ‖E4Fun z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ C * ‖qParamFun z‖ + 1 := by rw [norm_one]; linarith
    _ ≤ C * 1 + 1 := by nlinarith [hq, hC]
    _ = 1 + C := by ring

/-- `E₄(τ)⁴ - 1 = O(q(τ))` on `{Im τ ≥ 1/3}`, with an explicit constant. -/
private lemma E4p4_sub_one {τ : ℍ} {B : ℝ} (hB : ‖E4Fun τ‖ ≤ B) {C1 : ℝ} (hC1 : 0 ≤ C1)
    (h4 : ‖E4Fun τ - 1‖ ≤ C1 * ‖qParamFun τ‖) :
    ‖E4Fun τ ^ 4 - 1‖ ≤ C1 * (B ^ 3 + B ^ 2 + B + 1) * ‖qParamFun τ‖ := by
  have hkey : E4Fun τ ^ 4 - 1
      = (E4Fun τ - 1) * (E4Fun τ ^ 3 + E4Fun τ ^ 2 + E4Fun τ + 1) := by ring
  rw [hkey, norm_mul]
  have hin : ‖E4Fun τ ^ 3 + E4Fun τ ^ 2 + E4Fun τ + 1‖ ≤ B ^ 3 + B ^ 2 + B + 1 := by
    have s1 := norm_add_le (E4Fun τ ^ 3 + E4Fun τ ^ 2 + E4Fun τ) 1
    have s2 := norm_add_le (E4Fun τ ^ 3 + E4Fun τ ^ 2) (E4Fun τ)
    have s3 := norm_add_le (E4Fun τ ^ 3) (E4Fun τ ^ 2)
    have h3 : ‖E4Fun τ ^ 3‖ ≤ B ^ 3 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hB 3
    have h2 : ‖E4Fun τ ^ 2‖ ≤ B ^ 2 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hB 2
    have h1 : ‖(1 : ℂ)‖ = 1 := norm_one
    linarith [s1, s2, s3, h3, h2, h1, norm_nonneg (E4Fun τ ^ 3 + E4Fun τ ^ 2 + E4Fun τ),
      norm_nonneg (E4Fun τ ^ 3 + E4Fun τ ^ 2), norm_nonneg (E4Fun τ ^ 3)]
  calc ‖E4Fun τ - 1‖ * ‖E4Fun τ ^ 3 + E4Fun τ ^ 2 + E4Fun τ + 1‖
      ≤ (C1 * ‖qParamFun τ‖) * (B ^ 3 + B ^ 2 + B + 1) :=
        mul_le_mul h4 hin (norm_nonneg _) (by positivity)
    _ = C1 * (B ^ 3 + B ^ 2 + B + 1) * ‖qParamFun τ‖ := by ring

/-- Triangle inequality for a left-associated six-term sum. -/
private lemma norm_sum6_le (a b c d e f : ℂ) :
    ‖a + b + c + d + e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  have s1 := norm_add_le (a + b + c + d + e) f
  have s2 := norm_add_le (a + b + c + d) e
  have s3 := norm_add_le (a + b + c) d
  have s4 := norm_add_le (a + b) c
  have s5 := norm_add_le a b
  linarith [s1, s2, s3, s4, s5, norm_nonneg a, norm_nonneg b, norm_nonneg c,
    norm_nonneg d, norm_nonneg e, norm_nonneg f]

/-- `5E₄ - 7E₂² + 2`, `E₂² - 1`, `E₄ - 1` and `rr(z)E₄(z)²/Δ(z)` are `O(q(z))` on `{Im ≥ 1/3}`. -/
theorem z_atom_sub :
    ∃ C : ℝ, 0 < C ∧
      (∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im →
        ‖5 * E4Fun z - 7 * E2Fun z ^ 2 + 2‖ ≤ C * ‖qParamFun z‖) ∧
      (∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im →
        ‖E2Fun z ^ 2 - 1‖ ≤ C * ‖qParamFun z‖) ∧
      (∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im →
        ‖E4Fun z - 1‖ ≤ C * ‖qParamFun z‖) ∧
      (∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im →
        ‖(5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
          * E4Fun z ^ 2 / DeltaFun z‖ ≤ C * ‖qParamFun z‖) := by
  obtain ⟨C1, hC1, hE2b, hE4b, hE6b, hDb⟩ := Work.Asymptotics.ZAtomsThird.first_order
  obtain ⟨Cc, hCc, hc1, hc2, hc3, hc4⟩ := Work.Asymptotics.ZAtomsThird.cusp_forms
  obtain ⟨cl, hcl, hlb⟩ := Work.Asymptotics.delta_lower_third
  set B : ℝ := 1 + C1 with hB
  have hB0 : 0 < B := by rw [hB]; linarith
  set K : ℝ := (5 * C1 + 14 * C1 + 7 * C1 ^ 2) + (2 * C1 + C1 ^ 2) + C1
      + (Cc * B ^ 2 / cl) + 1 with hK
  have hpq : (0 : ℝ) ≤ Cc * B ^ 2 / cl := by positivity
  have hK0 : 0 < K := by rw [hK]; positivity
  have hK1 : 5 * C1 + 14 * C1 + 7 * C1 ^ 2 ≤ K := by rw [hK]; linarith [hpq, sq_nonneg C1]
  have hK2 : 2 * C1 + C1 ^ 2 ≤ K := by rw [hK]; linarith [hpq, sq_nonneg C1]
  have hK3 : C1 ≤ K := by rw [hK]; linarith [hpq, sq_nonneg C1]
  have hK4 : Cc * B ^ 2 / cl ≤ K := by rw [hK]; linarith [hpq, sq_nonneg C1]
  have hZ1 : ∀ z : ℍ, (1 : ℝ) / 3 ≤ z.im →
      ‖5 * E4Fun z - 7 * E2Fun z ^ 2 + 2‖ ≤ K * ‖qParamFun z‖ := by
    intro z hz
    have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
    have hq1 : ‖qParamFun z‖ ≤ 1 := q_le_one_third hz
    have hq2 : ‖qParamFun z‖ ^ 2 ≤ ‖qParamFun z‖ := by nlinarith
    have h2 := hE2b z hz
    have h4 := hE4b z hz
    have hkey : 5 * E4Fun z - 7 * E2Fun z ^ 2 + 2
        = 5 * (E4Fun z - 1) - 14 * (E2Fun z - 1) - 7 * (E2Fun z - 1) ^ 2 := by ring
    rw [hkey]
    have h5 : ‖(5 : ℂ) * (E4Fun z - 1)‖ ≤ 5 * (C1 * ‖qParamFun z‖) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left h4 (by norm_num)
    have h14 : ‖(14 : ℂ) * (E2Fun z - 1)‖ ≤ 14 * (C1 * ‖qParamFun z‖) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    have h7 : ‖(7 : ℂ) * (E2Fun z - 1) ^ 2‖ ≤ 7 * (C1 * ‖qParamFun z‖) ^ 2 := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h2 2) (by norm_num)
    have htot : ‖(5 : ℂ) * (E4Fun z - 1) - 14 * (E2Fun z - 1) - 7 * (E2Fun z - 1) ^ 2‖
        ≤ 5 * (C1 * ‖qParamFun z‖) + 14 * (C1 * ‖qParamFun z‖)
          + 7 * (C1 * ‖qParamFun z‖) ^ 2 := by
      have s1 := norm_sub_le ((5 : ℂ) * (E4Fun z - 1) - 14 * (E2Fun z - 1))
        (7 * (E2Fun z - 1) ^ 2)
      have s2 := norm_sub_le ((5 : ℂ) * (E4Fun z - 1)) (14 * (E2Fun z - 1))
      linarith [s1, s2, h5, h14, h7, norm_nonneg ((5 : ℂ) * (E4Fun z - 1)),
        norm_nonneg ((14 : ℂ) * (E2Fun z - 1))]
    refine le_trans htot ?_
    have hq2' : (C1 * ‖qParamFun z‖) ^ 2 ≤ C1 ^ 2 * ‖qParamFun z‖ := by
      have h := mul_le_mul_of_nonneg_left hq2 (by positivity : (0 : ℝ) ≤ C1 ^ 2)
      nlinarith [h]
    nlinarith [hK1, hpq, hq0, hq1, hq2', hC1.le]
  have hZ2 : ∀ z : ℍ, (1 : ℝ) / 3 ≤ z.im →
      ‖E2Fun z ^ 2 - 1‖ ≤ K * ‖qParamFun z‖ := by
    intro z hz
    have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
    have hq1 : ‖qParamFun z‖ ≤ 1 := q_le_one_third hz
    have hq2 : ‖qParamFun z‖ ^ 2 ≤ ‖qParamFun z‖ := by nlinarith
    have h2 := hE2b z hz
    have hkey : E2Fun z ^ 2 - 1 = 2 * (E2Fun z - 1) + (E2Fun z - 1) ^ 2 := by ring
    rw [hkey]
    have h2' : ‖(2 : ℂ) * (E2Fun z - 1)‖ ≤ 2 * (C1 * ‖qParamFun z‖) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    have h1' : ‖(E2Fun z - 1) ^ 2‖ ≤ (C1 * ‖qParamFun z‖) ^ 2 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h2 2
    have hq2' : (C1 * ‖qParamFun z‖) ^ 2 ≤ C1 ^ 2 * ‖qParamFun z‖ := by
      have h := mul_le_mul_of_nonneg_left hq2 (by positivity : (0 : ℝ) ≤ C1 ^ 2)
      nlinarith [h]
    refine le_trans (norm_add_le _ _) ?_
    nlinarith [h2', h1', hK2, hpq, hq0, hq1, hq2', hC1.le]
  have hZ3 : ∀ z : ℍ, (1 : ℝ) / 3 ≤ z.im →
      ‖E4Fun z - 1‖ ≤ K * ‖qParamFun z‖ := by
    intro z hz
    have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
    exact le_trans (hE4b z hz) (mul_le_mul_of_nonneg_right hK3 hq0)
  have hZ4 : ∀ z : ℍ, (1 : ℝ) / 3 ≤ z.im →
      ‖(5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
        * E4Fun z ^ 2 / DeltaFun z‖ ≤ K * ‖qParamFun z‖ := by
    intro z hz
    have hq0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
    have hq1 : ‖qParamFun z‖ ≤ 1 := q_le_one_third hz
    have hq2 : ‖qParamFun z‖ ^ 2 ≤ ‖qParamFun z‖ := by nlinarith
    have hqz : 0 < ‖qParamFun z‖ := by
      rw [Work.Asymptotics.norm_qParamFun]; exact Real.exp_pos _
    have hDz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
    have hlb' := hlb z hz
    have hDpos : 0 < ‖DeltaFun z‖ := lt_of_lt_of_le (mul_pos hcl hqz) hlb'
    have hE4z : ‖E4Fun z‖ ≤ B := E_bound4 (hE4b z hz) hC1.le hq1
    rw [norm_div]
    have hnum : ‖(5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
        * E4Fun z ^ 2‖ ≤ Cc * ‖qParamFun z‖ ^ 2 * B ^ 2 := by
      rw [norm_mul]
      have hsq : ‖E4Fun z ^ 2‖ ≤ B ^ 2 := by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hE4z 2
      exact mul_le_mul (hc4 z hz) hsq (norm_nonneg _) (by positivity)
    rw [div_le_iff₀ hDpos]
    calc ‖(5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
            * E4Fun z ^ 2‖
        ≤ Cc * ‖qParamFun z‖ ^ 2 * B ^ 2 := hnum
      _ = (Cc * B ^ 2 / cl) * (cl * ‖qParamFun z‖) * ‖qParamFun z‖ := by
          field_simp
      _ ≤ (Cc * B ^ 2 / cl) * ‖DeltaFun z‖ * ‖qParamFun z‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlb' hpq) hq0
      _ ≤ K * ‖DeltaFun z‖ * ‖qParamFun z‖ := by
          have h0 : (0 : ℝ) ≤ ‖DeltaFun z‖ := norm_nonneg _
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK4 h0) hq0
      _ = K * ‖qParamFun z‖ * ‖DeltaFun z‖ := by ring
  exact ⟨K, hK0, hZ1, hZ2, hZ3, hZ4⟩

theorem W1_sub :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, (1 : ℝ) / 3 ≤ τ.im →
      ‖E4Fun τ ^ 4 * ((E2Fun τ * E6Fun τ - E4Fun τ ^ 2) * E2Fun τ
            - (E2Fun τ * E4Fun τ - E6Fun τ) * E4Fun τ)
        + (E4Fun τ ^ 3 - E6Fun τ ^ 2)‖ ≤ C * ‖qParamFun τ‖ ^ 2 := by
  obtain ⟨C1, hC1, hE2b, hE4b, hE6b, hDb⟩ := Work.Asymptotics.ZAtomsThird.first_order
  obtain ⟨Cc, hCc, hc1, hc2, hc3, hc4⟩ := Work.Asymptotics.ZAtomsThird.cusp_forms
  set B : ℝ := 1 + C1 with hB
  have hB0 : 0 < B := by rw [hB]; linarith
  set K : ℝ := C1 * (B ^ 3 + B ^ 2 + B + 1) * (2 * Cc * B)
      + (2 * Cc * C1 + 7 * C1 ^ 2 + C1 ^ 3) + 1 with hK
  have hK0 : 0 < K := by
    rw [hK]
    have hb1 : 0 < B ^ 3 + B ^ 2 + B + 1 := by
      nlinarith [hB0, pow_pos hB0 2, pow_pos hB0 3]
    have hb2 : 0 < 2 * Cc * B := by nlinarith [hCc, hB0]
    have h1 : 0 < C1 * (B ^ 3 + B ^ 2 + B + 1) * (2 * Cc * B) :=
      mul_pos (mul_pos hC1 hb1) hb2
    have h2 : 0 ≤ 2 * Cc * C1 + 7 * C1 ^ 2 + C1 ^ 3 := by
      nlinarith [hCc, hC1, sq_nonneg C1, pow_pos hC1 3]
    linarith
  refine ⟨K, hK0, fun τ hτ => ?_⟩
  have hq0 : (0 : ℝ) ≤ ‖qParamFun τ‖ := norm_nonneg _
  have hq1 : ‖qParamFun τ‖ ≤ 1 := q_le_one_third hτ
  have hq2 : ‖qParamFun τ‖ ^ 2 ≤ ‖qParamFun τ‖ := by nlinarith
  have hq3 : ‖qParamFun τ‖ ^ 3 ≤ ‖qParamFun τ‖ ^ 2 := by nlinarith
  have h2 := hE2b τ hτ
  have h4 := hE4b τ hτ
  have h6 := hE6b τ hτ
  have hE2 : ‖E2Fun τ‖ ≤ B := E_bound h2 hC1.le hq1
  have hE4 : ‖E4Fun τ‖ ≤ B := E_bound4 h4 hC1.le hq1
  set e2 : ℂ := E2Fun τ - 1 with he2
  set e4 : ℂ := E4Fun τ - 1 with he4
  set e6 : ℂ := E6Fun τ - 1 with he6
  set zeta : ℂ := E2Fun τ * E6Fun τ - E4Fun τ ^ 2 with hzeta
  set eta : ℂ := E2Fun τ * E4Fun τ - E6Fun τ with heta
  set T1 : ℂ := (E4Fun τ ^ 4 - 1) * (zeta * E2Fun τ - eta * E4Fun τ) with hT1
  set T2 : ℂ := e2 * e6 with hT2
  set T3 : ℂ := -(e4 ^ 2) with hT3
  set T4 : ℂ := -(e2 * e4) with hT4
  set T5 : ℂ := zeta * e2 - eta * e4 with hT5
  set T6 : ℂ := 3 * e4 ^ 2 + e4 ^ 3 - e6 ^ 2 with hT6
  have he2b : ‖e2‖ ≤ C1 * ‖qParamFun τ‖ := by rw [he2]; exact h2
  have he4b : ‖e4‖ ≤ C1 * ‖qParamFun τ‖ := by rw [he4]; exact h4
  have he6b : ‖e6‖ ≤ C1 * ‖qParamFun τ‖ := by rw [he6]; exact h6
  have hzetab : ‖zeta‖ ≤ Cc * ‖qParamFun τ‖ := by rw [hzeta]; exact hc2 τ hτ
  have hetab : ‖eta‖ ≤ Cc * ‖qParamFun τ‖ := by rw [heta]; exact hc3 τ hτ
  have hB1b : ‖zeta * E2Fun τ - eta * E4Fun τ‖ ≤ 2 * Cc * B * ‖qParamFun τ‖ := by
    have h1 : ‖zeta * E2Fun τ‖ ≤ (Cc * ‖qParamFun τ‖) * B := by
      rw [norm_mul]; exact mul_le_mul hzetab hE2 (norm_nonneg _) (by positivity)
    have h2' : ‖eta * E4Fun τ‖ ≤ (Cc * ‖qParamFun τ‖) * B := by
      rw [norm_mul]; exact mul_le_mul hetab hE4 (norm_nonneg _) (by positivity)
    calc ‖zeta * E2Fun τ - eta * E4Fun τ‖
        ≤ ‖zeta * E2Fun τ‖ + ‖eta * E4Fun τ‖ := norm_sub_le _ _
      _ ≤ (Cc * ‖qParamFun τ‖) * B + (Cc * ‖qParamFun τ‖) * B := add_le_add h1 h2'
      _ = 2 * Cc * B * ‖qParamFun τ‖ := by ring
  have hkey : E4Fun τ ^ 4 * (zeta * E2Fun τ - eta * E4Fun τ) + (E4Fun τ ^ 3 - E6Fun τ ^ 2)
      = T1 + T2 + T3 + T4 + T5 + T6 := by
    rw [hT1, hT2, hT3, hT4, hT5, hT6, he2, he4, he6, hzeta, heta]; ring
  have hb1 : ‖T1‖ ≤ C1 * (B ^ 3 + B ^ 2 + B + 1) * (2 * Cc * B) * ‖qParamFun τ‖ ^ 2 := by
    rw [hT1, norm_mul]
    calc ‖E4Fun τ ^ 4 - 1‖ * ‖zeta * E2Fun τ - eta * E4Fun τ‖
        ≤ (C1 * (B ^ 3 + B ^ 2 + B + 1) * ‖qParamFun τ‖) * (2 * Cc * B * ‖qParamFun τ‖) :=
          mul_le_mul (E4p4_sub_one hE4 hC1.le h4) hB1b (norm_nonneg _) (by positivity)
      _ = C1 * (B ^ 3 + B ^ 2 + B + 1) * (2 * Cc * B) * ‖qParamFun τ‖ ^ 2 := by ring
  have hb2 : ‖T2‖ ≤ C1 ^ 2 * ‖qParamFun τ‖ ^ 2 := by
    rw [hT2, norm_mul]
    calc ‖e2‖ * ‖e6‖ ≤ (C1 * ‖qParamFun τ‖) * (C1 * ‖qParamFun τ‖) :=
          mul_le_mul he2b he6b (norm_nonneg _) (by positivity)
      _ = C1 ^ 2 * ‖qParamFun τ‖ ^ 2 := by ring
  have hb3 : ‖T3‖ ≤ C1 ^ 2 * ‖qParamFun τ‖ ^ 2 := by
    rw [hT3, norm_neg, norm_pow]
    calc ‖e4‖ ^ 2 ≤ (C1 * ‖qParamFun τ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) he4b 2
      _ = C1 ^ 2 * ‖qParamFun τ‖ ^ 2 := by ring
  have hb4 : ‖T4‖ ≤ C1 ^ 2 * ‖qParamFun τ‖ ^ 2 := by
    rw [hT4, norm_neg, norm_mul]
    calc ‖e2‖ * ‖e4‖ ≤ (C1 * ‖qParamFun τ‖) * (C1 * ‖qParamFun τ‖) :=
          mul_le_mul he2b he4b (norm_nonneg _) (by positivity)
      _ = C1 ^ 2 * ‖qParamFun τ‖ ^ 2 := by ring
  have hb5 : ‖T5‖ ≤ 2 * Cc * C1 * ‖qParamFun τ‖ ^ 2 := by
    rw [hT5]
    have ha : ‖zeta * e2‖ ≤ (Cc * ‖qParamFun τ‖) * (C1 * ‖qParamFun τ‖) := by
      rw [norm_mul]; exact mul_le_mul hzetab he2b (norm_nonneg _) (by positivity)
    have hb : ‖eta * e4‖ ≤ (Cc * ‖qParamFun τ‖) * (C1 * ‖qParamFun τ‖) := by
      rw [norm_mul]; exact mul_le_mul hetab he4b (norm_nonneg _) (by positivity)
    calc ‖zeta * e2 - eta * e4‖ ≤ ‖zeta * e2‖ + ‖eta * e4‖ := norm_sub_le _ _
      _ ≤ (Cc * ‖qParamFun τ‖) * (C1 * ‖qParamFun τ‖)
            + (Cc * ‖qParamFun τ‖) * (C1 * ‖qParamFun τ‖) := add_le_add ha hb
      _ = 2 * Cc * C1 * ‖qParamFun τ‖ ^ 2 := by ring
  have hb6 : ‖T6‖ ≤ (4 * C1 ^ 2 + C1 ^ 3) * ‖qParamFun τ‖ ^ 2 := by
    rw [hT6]
    have ha : ‖(3 : ℂ) * e4 ^ 2‖ ≤ 3 * (C1 * ‖qParamFun τ‖) ^ 2 := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) he4b 2) (by norm_num)
    have hb : ‖e4 ^ 3‖ ≤ (C1 * ‖qParamFun τ‖) ^ 3 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) he4b 3
    have hc : ‖e6 ^ 2‖ ≤ (C1 * ‖qParamFun τ‖) ^ 2 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) he6b 2
    have s1 := norm_sub_le ((3 : ℂ) * e4 ^ 2 + e4 ^ 3) (e6 ^ 2)
    have s2 := norm_add_le ((3 : ℂ) * e4 ^ 2) (e4 ^ 3)
    have hq2' : (C1 * ‖qParamFun τ‖) ^ 2 ≤ C1 ^ 2 * ‖qParamFun τ‖ ^ 2 := by rw [mul_pow]
    have hq3' : (C1 * ‖qParamFun τ‖) ^ 3 ≤ C1 ^ 3 * ‖qParamFun τ‖ ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hq3 (by positivity : (0 : ℝ) ≤ C1 ^ 3)
      nlinarith [h]
    nlinarith [s1, s2, ha, hb, hc, hq2', hq3', norm_nonneg ((3 : ℂ) * e4 ^ 2),
      norm_nonneg (e4 ^ 3), hC1.le]
  rw [show E4Fun τ ^ 4 * ((E2Fun τ * E6Fun τ - E4Fun τ ^ 2) * E2Fun τ
        - (E2Fun τ * E4Fun τ - E6Fun τ) * E4Fun τ) + (E4Fun τ ^ 3 - E6Fun τ ^ 2)
      = E4Fun τ ^ 4 * (zeta * E2Fun τ - eta * E4Fun τ) + (E4Fun τ ^ 3 - E6Fun τ ^ 2)
      from by rw [hzeta, heta], hkey]
  have hsum := norm_sum6_le T1 T2 T3 T4 T5 T6
  refine le_trans hsum ?_
  have hKbig : C1 * (B ^ 3 + B ^ 2 + B + 1) * (2 * Cc * B)
      + 2 * Cc * C1 + 7 * C1 ^ 2 + C1 ^ 3 ≤ K := by rw [hK]; linarith
  have hq2' : (0 : ℝ) ≤ ‖qParamFun τ‖ ^ 2 := by positivity
  nlinarith [hb1, hb2, hb3, hb4, hb5, hb6, hKbig, hq2',
    norm_nonneg T1, norm_nonneg T2, norm_nonneg T3, norm_nonneg T4, norm_nonneg T5,
    norm_nonneg T6]

/-- `E₄(τ)⁴ζ + 1008Δ(τ) = O(q(τ)²)` on `{Im τ ≥ 1/3}`, where `ζ = E₂E₆ - E₄²`. -/
theorem W2_sub :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, (1 : ℝ) / 3 ≤ τ.im →
      ‖E4Fun τ ^ 4 * (E2Fun τ * E6Fun τ - E4Fun τ ^ 2)
        + 1008 * DeltaFun τ‖ ≤ C * ‖qParamFun τ‖ ^ 2 := by
  obtain ⟨C1, hC1, hE2b, hE4b, hE6b, hDb⟩ := Work.Asymptotics.ZAtomsThird.first_order
  obtain ⟨C2, hC2, hE2t⟩ := Work.Asymptotics.ZAtomsThird.E2Fun_two_term_third
  obtain ⟨C4, hC4, hE4t⟩ := Work.Asymptotics.ZAtomsThird.E4Fun_two_term_third
  obtain ⟨C6, hC6, hE6t⟩ := Work.Asymptotics.ZAtomsThird.E6Fun_two_term_third
  obtain ⟨Cc, hCc, hc1, hc2, hc3, hc4⟩ := Work.Asymptotics.ZAtomsThird.cusp_forms
  set B : ℝ := 1 + C1 with hB
  have hB0 : 0 < B := by rw [hB]; linarith
  set K : ℝ := C1 * (B ^ 3 + B ^ 2 + B + 1) * Cc
      + (C2 + C6 + 2 * C4 + 2 * C1 ^ 2 + 1008 * C1) + 1 with hK
  have hK0 : 0 < K := by
    rw [hK]
    have hb1 : 0 < B ^ 3 + B ^ 2 + B + 1 := by
      nlinarith [hB0, pow_pos hB0 2, pow_pos hB0 3]
    have h1 : 0 < C1 * (B ^ 3 + B ^ 2 + B + 1) * Cc :=
      mul_pos (mul_pos hC1 hb1) hCc
    have h2 : 0 ≤ C2 + C6 + 2 * C4 + 2 * C1 ^ 2 + 1008 * C1 := by
      nlinarith [hC2, hC4, hC6, hC1, sq_nonneg C1]
    linarith
  refine ⟨K, hK0, fun τ hτ => ?_⟩
  have hq0 : (0 : ℝ) ≤ ‖qParamFun τ‖ := norm_nonneg _
  have hq1 : ‖qParamFun τ‖ ≤ 1 := q_le_one_third hτ
  have hq2 : ‖qParamFun τ‖ ^ 2 ≤ ‖qParamFun τ‖ := by nlinarith
  have h2 := hE2b τ hτ
  have h4 := hE4b τ hτ
  have hE4 : ‖E4Fun τ‖ ≤ B := E_bound4 h4 hC1.le hq1
  set e2 : ℂ := E2Fun τ - 1 with he2
  set e4 : ℂ := E4Fun τ - 1 with he4
  set e6 : ℂ := E6Fun τ - 1 with he6
  set zeta : ℂ := E2Fun τ * E6Fun τ - E4Fun τ ^ 2 with hzeta
  set T1 : ℂ := (E4Fun τ ^ 4 - 1) * zeta with hT1
  set T2 : ℂ := E2Fun τ - 1 + 24 * qParamFun τ with hT2
  set T3 : ℂ := E6Fun τ - 1 + 504 * qParamFun τ with hT3
  set T4 : ℂ := -(2 * (E4Fun τ - 1 - 240 * qParamFun τ)) with hT4
  set T5 : ℂ := e2 * e6 - e4 ^ 2 with hT5
  set T6 : ℂ := 1008 * (DeltaFun τ - qParamFun τ) with hT6
  have he2b : ‖e2‖ ≤ C1 * ‖qParamFun τ‖ := by rw [he2]; exact h2
  have he4b : ‖e4‖ ≤ C1 * ‖qParamFun τ‖ := by rw [he4]; exact h4
  have he6b : ‖e6‖ ≤ C1 * ‖qParamFun τ‖ := by rw [he6]; exact hE6b τ hτ
  have hzetab : ‖zeta‖ ≤ Cc * ‖qParamFun τ‖ := by rw [hzeta]; exact hc2 τ hτ
  have hkey : E4Fun τ ^ 4 * zeta + 1008 * DeltaFun τ = T1 + T2 + T3 + T4 + T5 + T6 := by
    rw [hT1, hT2, hT3, hT4, hT5, hT6, he2, he4, he6, hzeta]; ring
  have hb1 : ‖T1‖ ≤ C1 * (B ^ 3 + B ^ 2 + B + 1) * Cc * ‖qParamFun τ‖ ^ 2 := by
    rw [hT1, norm_mul]
    calc ‖E4Fun τ ^ 4 - 1‖ * ‖zeta‖
        ≤ (C1 * (B ^ 3 + B ^ 2 + B + 1) * ‖qParamFun τ‖) * (Cc * ‖qParamFun τ‖) :=
          mul_le_mul (E4p4_sub_one hE4 hC1.le h4) hzetab (norm_nonneg _) (by positivity)
      _ = C1 * (B ^ 3 + B ^ 2 + B + 1) * Cc * ‖qParamFun τ‖ ^ 2 := by ring
  have hb2 : ‖T2‖ ≤ C2 * ‖qParamFun τ‖ ^ 2 := by rw [hT2]; exact hE2t τ hτ
  have hb3 : ‖T3‖ ≤ C6 * ‖qParamFun τ‖ ^ 2 := by rw [hT3]; exact hE6t τ hτ
  have hb4 : ‖T4‖ ≤ 2 * C4 * ‖qParamFun τ‖ ^ 2 := by
    rw [hT4, norm_neg, norm_mul, Complex.norm_ofNat]
    calc (2 : ℝ) * ‖E4Fun τ - 1 - 240 * qParamFun τ‖ ≤ 2 * (C4 * ‖qParamFun τ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hE4t τ hτ) (by norm_num)
      _ = 2 * C4 * ‖qParamFun τ‖ ^ 2 := by ring
  have hb5 : ‖T5‖ ≤ 2 * C1 ^ 2 * ‖qParamFun τ‖ ^ 2 := by
    rw [hT5]
    have ha : ‖e2 * e6‖ ≤ (C1 * ‖qParamFun τ‖) * (C1 * ‖qParamFun τ‖) := by
      rw [norm_mul]; exact mul_le_mul he2b he6b (norm_nonneg _) (by positivity)
    have hb : ‖e4 ^ 2‖ ≤ (C1 * ‖qParamFun τ‖) ^ 2 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) he4b 2
    calc ‖e2 * e6 - e4 ^ 2‖ ≤ ‖e2 * e6‖ + ‖e4 ^ 2‖ := norm_sub_le _ _
      _ ≤ (C1 * ‖qParamFun τ‖) * (C1 * ‖qParamFun τ‖) + (C1 * ‖qParamFun τ‖) ^ 2 :=
          add_le_add ha hb
      _ = 2 * C1 ^ 2 * ‖qParamFun τ‖ ^ 2 := by ring
  have hb6 : ‖T6‖ ≤ 1008 * C1 * ‖qParamFun τ‖ ^ 2 := by
    rw [hT6, norm_mul, Complex.norm_ofNat]
    calc (1008 : ℝ) * ‖DeltaFun τ - qParamFun τ‖ ≤ 1008 * (C1 * ‖qParamFun τ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hDb τ hτ) (by norm_num)
      _ = 1008 * C1 * ‖qParamFun τ‖ ^ 2 := by ring
  rw [hkey]
  have hsum := norm_sum6_le T1 T2 T3 T4 T5 T6
  refine le_trans hsum ?_
  have hKbig : C1 * (B ^ 3 + B ^ 2 + B + 1) * Cc
      + C2 + C6 + 2 * C4 + 2 * C1 ^ 2 + 1008 * C1 ≤ K := by rw [hK]; linarith
  have hq2' : (0 : ℝ) ≤ ‖qParamFun τ‖ ^ 2 := by positivity
  nlinarith [hb1, hb2, hb3, hb4, hb5, hb6, hKbig, hq2',
    norm_nonneg T1, norm_nonneg T2, norm_nonneg T3, norm_nonneg T4, norm_nonneg T5,
    norm_nonneg T6]


theorem Xi24_Delta_bound :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ τ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ τ.im → (1 : ℝ) / 3 ≤ z.im →
      ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Xi24 τ z‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A *
            Real.exp (-(Real.pi * (4 * τ.im + z.im))) := by
  obtain ⟨CW1, hCW1, hW1b⟩ := W1_sub
  obtain ⟨CW2, hCW2, hW2b⟩ := W2_sub
  obtain ⟨CG, hCG, hG1b, hG2b⟩ := Xi24_G_bounds
  obtain ⟨Cza, hCza, hF3b, hF4b, hF5b, hrrb⟩ := z_atom_sub
  obtain ⟨Cc, hCc, hc1, hc2, hc3, hc4⟩ := Work.Asymptotics.ZAtomsThird.cusp_forms
  obtain ⟨C1, hC1, hE2b, hE4b, hE6b, hDb⟩ := Work.Asymptotics.ZAtomsThird.first_order
  obtain ⟨Cd, hCd, hDub⟩ := Work.Asymptotics.delta_upper_third
  obtain ⟨Csig, hCsig, hsigb⟩ := Work.Asymptotics.jz_sigma_third
  obtain ⟨Cph, hCph, hphb⟩ := phi8_bound_third
  set B : ℝ := 1 + C1 with hB
  set E0 : ℝ := 1 + C1 + 3 / Real.pi with hE0
  set K : ℝ := 6 * Cc * CW1 + 1728 * Cd * CG + (36 / Real.pi) * Cc * CW2
      + (5184 / Real.pi) * Cd * CG + 6 * Cd * B * Cph * Csig + 1728 * Cd ^ 2 * E0 * Cza with hK
  have hB0 : 0 < B := by rw [hB]; linarith
  have hE00 : 0 < E0 := by rw [hE0]; positivity
  have hK0 : 0 < K := by rw [hK]; positivity
  refine ⟨K, 1, hK0, by norm_num, fun τ z hτ hz => ?_⟩
  have hDt : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hDz : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  have hqt0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hqz0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hqt1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 :=
    le_trans (Work.Asymptotics.norm_qParam_le_third hτ) (by norm_num)
  have hqz1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 :=
    le_trans (Work.Asymptotics.norm_qParam_le_third hz) (by norm_num)
  have hτn0 : (0 : ℝ) ≤ ‖(τ : ℂ)‖ := norm_nonneg _
  have hzn0 : (0 : ℝ) ≤ ‖(z : ℂ)‖ := norm_nonneg _
  have hτn1 : ‖(τ : ℂ)‖ ≤ 1 + ‖(τ : ℂ)‖ := by linarith
  have hzn1 : (1 : ℝ) ≤ 1 + ‖(z : ℂ)‖ := by linarith
  have hE4t : ‖Work.Kernels.E4Fun τ‖ ≤ B := by
    have h := hE4b τ hτ
    calc ‖Work.Kernels.E4Fun τ‖ = ‖(Work.Kernels.E4Fun τ - 1) + 1‖ := by ring_nf
      _ ≤ ‖Work.Kernels.E4Fun τ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ C1 * ‖Work.Kernels.qParamFun τ‖ + 1 := by rw [norm_one]; linarith
      _ ≤ C1 * 1 + 1 := by nlinarith [hqt1, hC1.le]
      _ = B := by rw [hB]; ring
  have hE6t : ‖Work.Kernels.E6Fun τ‖ ≤ B := by
    have h := hE6b τ hτ
    calc ‖Work.Kernels.E6Fun τ‖ = ‖(Work.Kernels.E6Fun τ - 1) + 1‖ := by ring_nf
      _ ≤ ‖Work.Kernels.E6Fun τ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ C1 * ‖Work.Kernels.qParamFun τ‖ + 1 := by rw [norm_one]; linarith
      _ ≤ C1 * 1 + 1 := by nlinarith [hqt1, hC1.le]
      _ = B := by rw [hB]; ring
  have hE2t : ‖Work.Kernels.E2Fun τ‖ ≤ B := by
    have h := hE2b τ hτ
    calc ‖Work.Kernels.E2Fun τ‖ = ‖(Work.Kernels.E2Fun τ - 1) + 1‖ := by ring_nf
      _ ≤ ‖Work.Kernels.E2Fun τ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ C1 * ‖Work.Kernels.qParamFun τ‖ + 1 := by rw [norm_one]; linarith
      _ ≤ C1 * 1 + 1 := by nlinarith [hqt1, hC1.le]
      _ = B := by rw [hB]; ring
  have hE4z : ‖Work.Kernels.E4Fun z‖ ≤ B := by
    have h := hE4b z hz
    calc ‖Work.Kernels.E4Fun z‖ = ‖(Work.Kernels.E4Fun z - 1) + 1‖ := by ring_nf
      _ ≤ ‖Work.Kernels.E4Fun z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ C1 * ‖Work.Kernels.qParamFun z‖ + 1 := by rw [norm_one]; linarith
      _ ≤ C1 * 1 + 1 := by nlinarith [hqz1, hC1.le]
      _ = B := by rw [hB]; ring
  have h3pi : ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 3 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_of_nonneg Real.pi_pos.le]
  have hphi0 : ‖Work.Kernels.phi0 τ‖ ≤ E0 * (1 + ‖(τ : ℂ)‖) := by
    have heq : Work.Kernels.phi0 τ
        = (τ : ℂ) * Work.Kernels.E2Fun τ - 3 * Complex.I / (Real.pi : ℂ) := by
      simp only [Work.Kernels.phi0]
    rw [heq]
    have h3pn : (0 : ℝ) ≤ 3 / Real.pi := by positivity
    have h1 : B ≤ E0 := by rw [hB, hE0]; linarith
    have h2 : 3 / Real.pi ≤ E0 := by rw [hE0]; linarith [hC1.le]
    calc ‖(τ : ℂ) * Work.Kernels.E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)‖
        ≤ ‖(τ : ℂ) * Work.Kernels.E2Fun τ‖ + ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ :=
          norm_sub_le _ _
      _ = ‖(τ : ℂ)‖ * ‖Work.Kernels.E2Fun τ‖ + 3 / Real.pi := by rw [norm_mul, h3pi]
      _ ≤ ‖(τ : ℂ)‖ * B + 3 / Real.pi := by
          have := mul_le_mul_of_nonneg_left hE2t hτn0
          linarith
      _ ≤ ‖(τ : ℂ)‖ * E0 + E0 := add_le_add (mul_le_mul_of_nonneg_left h1 hτn0) h2
      _ = E0 * (1 + ‖(τ : ℂ)‖) := by ring
  have hDut : ‖Work.Kernels.DeltaFun τ‖ ≤ Cd * ‖Work.Kernels.qParamFun τ‖ := hDub τ hτ
  have hDuz : ‖Work.Kernels.DeltaFun z‖ ≤ Cd * ‖Work.Kernels.qParamFun z‖ := hDub z hz
  have hdelz : ‖Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2‖
      ≤ Cc * ‖Work.Kernels.qParamFun z‖ := hc1 z hz
  have hsigz : ‖Work.Kernels.jInvariantFun z * (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2)
      - 288‖ ≤ Csig * ‖Work.Kernels.qParamFun z‖ := hsigb z hz
  have hrrz : ‖(5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2
      + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z) * Work.Kernels.E4Fun z ^ 2
      / Work.Kernels.DeltaFun z‖ ≤ Cza * ‖Work.Kernels.qParamFun z‖ := hrrb z hz
  have hph8 : ‖Work.Asymptotics.phi8 τ‖
      ≤ Cph * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ := hphb τ hτ
  have hW1 : ‖Work.Kernels.E4Fun τ ^ 4
        * ((Work.Kernels.E2Fun τ * Work.Kernels.E6Fun τ - Work.Kernels.E4Fun τ ^ 2)
            * Work.Kernels.E2Fun τ
          - (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - Work.Kernels.E6Fun τ)
            * Work.Kernels.E4Fun τ)
      + 1728 * Work.Kernels.DeltaFun τ‖ ≤ CW1 * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
    have h := hW1b τ hτ
    rwa [← DeltaFun_1728 τ] at h
  have hW2 : ‖Work.Kernels.E4Fun τ ^ 4
        * (Work.Kernels.E2Fun τ * Work.Kernels.E6Fun τ - Work.Kernels.E4Fun τ ^ 2)
      + 1008 * Work.Kernels.DeltaFun τ‖ ≤ CW2 * ‖Work.Kernels.qParamFun τ‖ ^ 2 := hW2b τ hτ
  have hG1 := hG1b τ z hτ hz
  have hG2 := hG2b τ z hτ hz
  -- abbreviations for the pieces of the decomposition
  set dz : ℂ := Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2 with hdzdef
  set zeta : ℂ := Work.Kernels.E2Fun τ * Work.Kernels.E6Fun τ - Work.Kernels.E4Fun τ ^ 2
    with hzetadef
  set eta : ℂ := Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - Work.Kernels.E6Fun τ
    with hetadef
  set B1 : ℂ := zeta * Work.Kernels.E2Fun τ - eta * Work.Kernels.E4Fun τ with hB1def
  set W1e : ℂ := Work.Kernels.E4Fun τ ^ 4 * B1 + 1728 * Work.Kernels.DeltaFun τ with hW1def
  set W2e : ℂ := Work.Kernels.E4Fun τ ^ 4 * zeta + 1008 * Work.Kernels.DeltaFun τ with hW2def
  set F3 : ℂ := 5 * Work.Kernels.E4Fun z - 7 * Work.Kernels.E2Fun z ^ 2 + 2 with hF3def
  set F4 : ℂ := Work.Kernels.E2Fun z ^ 2 - 1 with hF4def
  set F5 : ℂ := Work.Kernels.E4Fun z - 1 with hF5def
  set G1e : ℂ := Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ ^ 3 * F3
      + Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ * F4
      + Work.Kernels.E2Fun τ ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * F5
    with hG1def
  set G2e : ℂ := Work.Kernels.E4Fun τ ^ 3 * F3
      + 2 * Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * F5
    with hG2def
  set sge : ℂ := Work.Kernels.jInvariantFun z * dz - 288 with hsgdef
  set rre : ℂ := (5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2
      + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z) * Work.Kernels.E4Fun z ^ 2
      / Work.Kernels.DeltaFun z with hrrdef
  have hdzb : ‖dz‖ ≤ Cc * ‖Work.Kernels.qParamFun z‖ := by rw [hdzdef]; exact hdelz
  have hW1e : ‖W1e‖ ≤ CW1 * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
    rw [hW1def, hB1def, hzetadef, hetadef]; exact hW1
  have hW2e : ‖W2e‖ ≤ CW2 * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
    rw [hW2def, hzetadef]; exact hW2
  have hG1e : ‖G1e - 6 * dz‖ ≤ CG * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖ := by
    rw [hG1def, hF3def, hF4def, hF5def, hdzdef]; exact hG1
  have hG2e : ‖G2e - 7 * dz‖ ≤ CG * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖ := by
    rw [hG2def, hF3def, hF5def, hdzdef]; exact hG2
  have hsge : ‖sge‖ ≤ Csig * ‖Work.Kernels.qParamFun z‖ := by rw [hsgdef, hdzdef]; exact hsigz
  have hrre : ‖rre‖ ≤ Cza * ‖Work.Kernels.qParamFun z‖ := by rw [hrrdef]; exact hrrz
  set P1 : ℂ := 6 * (τ : ℂ) * dz * W1e with hP1def
  set P2 : ℂ := 1728 * (τ : ℂ) * Work.Kernels.DeltaFun τ * (G1e - 6 * dz) with hP2def
  set P3 : ℂ := (36 * Complex.I / (Real.pi : ℂ)) * dz * W2e with hP3def
  set P4 : ℂ := (5184 * Complex.I / (Real.pi : ℂ)) * Work.Kernels.DeltaFun τ * (G2e - 7 * dz)
    with hP4def
  set P5 : ℂ := 6 * Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ * Work.Asymptotics.phi8 τ * sge
    with hP5def
  set P6 : ℂ := 1728 * Work.Kernels.DeltaFun τ ^ 2 * Work.Kernels.phi0 τ * rre with hP6def
  have hidexp : Work.Kernels.DeltaFun τ * Work.Asymptotics.Xi24 τ z
      = P1 + P2 - P3 - P4 - P5 - P6 := by
    simp only [hP1def, hP2def, hP3def, hP4def, hP5def, hP6def, hdzdef, hW1def, hW2def,
      hG1def, hG2def, hsgdef, hrrdef, hB1def, hzetadef, hetadef, hF3def, hF4def, hF5def]
    rw [Work.Asymptotics.Xi24_cancelled τ z hDt hDz]
    simp only [Work.Kernels.jInvariantFun, Work.Kernels.phi0, Work.Kernels.phi2,
      Work.Asymptotics.phi8_eq]
    field_simp [hDt, hDz, Real.pi_ne_zero]
    ring
  have htri : ‖P1 + P2 - P3 - P4 - P5 - P6‖
      ≤ ‖P1‖ + ‖P2‖ + ‖P3‖ + ‖P4‖ + ‖P5‖ + ‖P6‖ := by
    have s1 := norm_sub_le (P1 + P2 - P3 - P4 - P5) P6
    have s2 := norm_sub_le (P1 + P2 - P3 - P4) P5
    have s3 := norm_sub_le (P1 + P2 - P3) P4
    have s4 := norm_sub_le (P1 + P2) P3
    have s5 := norm_add_le P1 P2
    have n1 := norm_nonneg P1
    have n2 := norm_nonneg P2
    have n3 := norm_nonneg P3
    have n4 := norm_nonneg P4
    have n5 := norm_nonneg P5
    have n6 := norm_nonneg P6
    linarith
  have hP1b : ‖P1‖ ≤ 6 * Cc * CW1 * (1 + ‖(τ : ℂ)‖)
      * ‖Work.Kernels.qParamFun τ‖ ^ 2 * ‖Work.Kernels.qParamFun z‖ := by
    rw [hP1def]
    have hp : ‖6 * (τ : ℂ) * dz * W1e‖ = 6 * ‖(τ : ℂ)‖ * ‖dz‖ * ‖W1e‖ := by
      simp only [norm_mul, Complex.norm_ofNat]
    rw [hp]
    have h1 : ‖(τ : ℂ)‖ * ‖dz‖ * ‖W1e‖
        ≤ (1 + ‖(τ : ℂ)‖) * (Cc * ‖Work.Kernels.qParamFun z‖)
          * (CW1 * ‖Work.Kernels.qParamFun τ‖ ^ 2) :=
      mul_le_mul (mul_le_mul hτn1 hdzb (norm_nonneg _) (by linarith))
        hW1e (norm_nonneg _) (by positivity)
    calc 6 * ‖(τ : ℂ)‖ * ‖dz‖ * ‖W1e‖
        = 6 * (‖(τ : ℂ)‖ * ‖dz‖ * ‖W1e‖) := by ring
      _ ≤ 6 * ((1 + ‖(τ : ℂ)‖) * (Cc * ‖Work.Kernels.qParamFun z‖)
            * (CW1 * ‖Work.Kernels.qParamFun τ‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 6 * Cc * CW1 * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ ^ 2
            * ‖Work.Kernels.qParamFun z‖ := by ring
  have hP2b : ‖P2‖ ≤ 1728 * Cd * CG * (1 + ‖(τ : ℂ)‖)
      * ‖Work.Kernels.qParamFun τ‖ ^ 2 * ‖Work.Kernels.qParamFun z‖ := by
    rw [hP2def]
    have hp : ‖1728 * (τ : ℂ) * Work.Kernels.DeltaFun τ * (G1e - 6 * dz)‖
        = 1728 * ‖(τ : ℂ)‖ * ‖Work.Kernels.DeltaFun τ‖ * ‖G1e - 6 * dz‖ := by
      simp only [norm_mul, Complex.norm_ofNat]
    rw [hp]
    have h1 : ‖(τ : ℂ)‖ * ‖Work.Kernels.DeltaFun τ‖ * ‖G1e - 6 * dz‖
        ≤ (1 + ‖(τ : ℂ)‖) * (Cd * ‖Work.Kernels.qParamFun τ‖)
          * (CG * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖) :=
      mul_le_mul (mul_le_mul hτn1 hDut (norm_nonneg _) (by linarith))
        hG1e (norm_nonneg _) (by positivity)
    calc 1728 * ‖(τ : ℂ)‖ * ‖Work.Kernels.DeltaFun τ‖ * ‖G1e - 6 * dz‖
        = 1728 * (‖(τ : ℂ)‖ * ‖Work.Kernels.DeltaFun τ‖ * ‖G1e - 6 * dz‖) := by ring
      _ ≤ 1728 * ((1 + ‖(τ : ℂ)‖) * (Cd * ‖Work.Kernels.qParamFun τ‖)
            * (CG * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖)) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 1728 * Cd * CG * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ ^ 2
            * ‖Work.Kernels.qParamFun z‖ := by ring
  have hP3b : ‖P3‖ ≤ (36 / Real.pi) * Cc * CW2 * (1 + ‖(τ : ℂ)‖)
      * ‖Work.Kernels.qParamFun τ‖ ^ 2 * ‖Work.Kernels.qParamFun z‖ := by
    rw [hP3def]
    have hp : ‖(36 * Complex.I / (Real.pi : ℂ)) * dz * W2e‖
        = 36 / Real.pi * ‖dz‖ * ‖W2e‖ := by
      simp only [norm_mul, norm_36i_pi]
    rw [hp]
    have hnn : (0 : ℝ) ≤ 36 / Real.pi := by positivity
    have h1 : ‖dz‖ * ‖W2e‖ ≤ (Cc * ‖Work.Kernels.qParamFun z‖)
        * (CW2 * ‖Work.Kernels.qParamFun τ‖ ^ 2) :=
      mul_le_mul hdzb hW2e (norm_nonneg _) (by positivity)
    have h2 : ‖dz‖ * ‖W2e‖ * (1 + ‖(τ : ℂ)‖)
        ≤ (Cc * ‖Work.Kernels.qParamFun z‖) * (CW2 * ‖Work.Kernels.qParamFun τ‖ ^ 2)
          * (1 + ‖(τ : ℂ)‖) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    calc 36 / Real.pi * ‖dz‖ * ‖W2e‖
        = 36 / Real.pi * (‖dz‖ * ‖W2e‖) := by ring
      _ ≤ 36 / Real.pi * ((Cc * ‖Work.Kernels.qParamFun z‖)
            * (CW2 * ‖Work.Kernels.qParamFun τ‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 hnn
      _ ≤ 36 / Real.pi * ((Cc * ‖Work.Kernels.qParamFun z‖)
            * (CW2 * ‖Work.Kernels.qParamFun τ‖ ^ 2)) * (1 + ‖(τ : ℂ)‖) := by
          have h0 : (0 : ℝ) ≤ 36 / Real.pi * ((Cc * ‖Work.Kernels.qParamFun z‖)
              * (CW2 * ‖Work.Kernels.qParamFun τ‖ ^ 2)) := by positivity
          nlinarith [h0, hτn0]
      _ = (36 / Real.pi) * Cc * CW2 * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ ^ 2
            * ‖Work.Kernels.qParamFun z‖ := by ring
  have hP4b : ‖P4‖ ≤ (5184 / Real.pi) * Cd * CG * (1 + ‖(τ : ℂ)‖)
      * ‖Work.Kernels.qParamFun τ‖ ^ 2 * ‖Work.Kernels.qParamFun z‖ := by
    rw [hP4def]
    have hp : ‖(5184 * Complex.I / (Real.pi : ℂ)) * Work.Kernels.DeltaFun τ * (G2e - 7 * dz)‖
        = 5184 / Real.pi * ‖Work.Kernels.DeltaFun τ‖ * ‖G2e - 7 * dz‖ := by
      simp only [norm_mul, norm_5184i_pi]
    rw [hp]
    have hnn : (0 : ℝ) ≤ 5184 / Real.pi := by positivity
    have h1 : ‖Work.Kernels.DeltaFun τ‖ * ‖G2e - 7 * dz‖
        ≤ (Cd * ‖Work.Kernels.qParamFun τ‖)
          * (CG * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖) :=
      mul_le_mul hDut hG2e (norm_nonneg _) (by positivity)
    calc 5184 / Real.pi * ‖Work.Kernels.DeltaFun τ‖ * ‖G2e - 7 * dz‖
        = 5184 / Real.pi * (‖Work.Kernels.DeltaFun τ‖ * ‖G2e - 7 * dz‖) := by ring
      _ ≤ 5184 / Real.pi * ((Cd * ‖Work.Kernels.qParamFun τ‖)
            * (CG * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖)) :=
          mul_le_mul_of_nonneg_left h1 hnn
      _ ≤ 5184 / Real.pi * ((Cd * ‖Work.Kernels.qParamFun τ‖)
            * (CG * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖))
            * (1 + ‖(τ : ℂ)‖) := by
          have h0 : (0 : ℝ) ≤ 5184 / Real.pi * ((Cd * ‖Work.Kernels.qParamFun τ‖)
              * (CG * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖)) := by positivity
          nlinarith [h0, hτn0]
      _ = (5184 / Real.pi) * Cd * CG * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ ^ 2
            * ‖Work.Kernels.qParamFun z‖ := by ring
  have hP5b : ‖P5‖ ≤ 6 * Cd * B * Cph * Csig * (1 + ‖(τ : ℂ)‖)
      * ‖Work.Kernels.qParamFun τ‖ ^ 2 * ‖Work.Kernels.qParamFun z‖ := by
    rw [hP5def]
    have hp : ‖6 * Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ * Work.Asymptotics.phi8 τ
          * sge‖ = 6 * ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.E4Fun τ‖
            * ‖Work.Asymptotics.phi8 τ‖ * ‖sge‖ := by
      simp only [norm_mul, Complex.norm_ofNat]
    rw [hp]
    have h1 : ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.E4Fun τ‖ * ‖Work.Asymptotics.phi8 τ‖
          * ‖sge‖
        ≤ (Cd * ‖Work.Kernels.qParamFun τ‖) * B
          * (Cph * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖)
          * (Csig * ‖Work.Kernels.qParamFun z‖) :=
      mul_le_mul (mul_le_mul (mul_le_mul hDut hE4t (norm_nonneg _) (by positivity)) hph8
        (norm_nonneg _) (by positivity)) hsge (norm_nonneg _) (by positivity)
    calc 6 * ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.E4Fun τ‖ * ‖Work.Asymptotics.phi8 τ‖
          * ‖sge‖
        = 6 * (‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.E4Fun τ‖
            * ‖Work.Asymptotics.phi8 τ‖ * ‖sge‖) := by ring
      _ ≤ 6 * ((Cd * ‖Work.Kernels.qParamFun τ‖) * B
            * (Cph * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖)
            * (Csig * ‖Work.Kernels.qParamFun z‖)) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 6 * Cd * B * Cph * Csig * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ ^ 2
            * ‖Work.Kernels.qParamFun z‖ := by ring
  have hP6b : ‖P6‖ ≤ 1728 * Cd ^ 2 * E0 * Cza * (1 + ‖(τ : ℂ)‖)
      * ‖Work.Kernels.qParamFun τ‖ ^ 2 * ‖Work.Kernels.qParamFun z‖ := by
    rw [hP6def]
    have hp : ‖1728 * Work.Kernels.DeltaFun τ ^ 2 * Work.Kernels.phi0 τ * rre‖
        = 1728 * ‖Work.Kernels.DeltaFun τ‖ ^ 2 * ‖Work.Kernels.phi0 τ‖ * ‖rre‖ := by
      simp only [norm_mul, norm_pow, Complex.norm_ofNat]
    rw [hp]
    have h1 : ‖Work.Kernels.DeltaFun τ‖ ^ 2 * ‖Work.Kernels.phi0 τ‖ * ‖rre‖
        ≤ (Cd * ‖Work.Kernels.qParamFun τ‖) ^ 2 * (E0 * (1 + ‖(τ : ℂ)‖))
          * (Cza * ‖Work.Kernels.qParamFun z‖) :=
      mul_le_mul (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hDut 2) hphi0
        (norm_nonneg _) (by positivity)) hrre (norm_nonneg _) (by positivity)
    calc 1728 * ‖Work.Kernels.DeltaFun τ‖ ^ 2 * ‖Work.Kernels.phi0 τ‖ * ‖rre‖
        = 1728 * (‖Work.Kernels.DeltaFun τ‖ ^ 2 * ‖Work.Kernels.phi0 τ‖ * ‖rre‖) := by ring
      _ ≤ 1728 * ((Cd * ‖Work.Kernels.qParamFun τ‖) ^ 2 * (E0 * (1 + ‖(τ : ℂ)‖))
            * (Cza * ‖Work.Kernels.qParamFun z‖)) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 1728 * Cd ^ 2 * E0 * Cza * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ ^ 2
            * ‖Work.Kernels.qParamFun z‖ := by ring
  have hmain : ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Xi24 τ z‖
      ≤ K * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ ^ 2 * ‖Work.Kernels.qParamFun z‖ := by
    rw [hidexp]
    calc ‖P1 + P2 - P3 - P4 - P5 - P6‖
        ≤ ‖P1‖ + ‖P2‖ + ‖P3‖ + ‖P4‖ + ‖P5‖ + ‖P6‖ := htri
      _ ≤ 6 * Cc * CW1 * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ ^ 2
              * ‖Work.Kernels.qParamFun z‖
            + 1728 * Cd * CG * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ ^ 2
              * ‖Work.Kernels.qParamFun z‖
            + (36 / Real.pi) * Cc * CW2 * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ ^ 2
              * ‖Work.Kernels.qParamFun z‖
            + (5184 / Real.pi) * Cd * CG * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ ^ 2
              * ‖Work.Kernels.qParamFun z‖
            + 6 * Cd * B * Cph * Csig * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ ^ 2
              * ‖Work.Kernels.qParamFun z‖
            + 1728 * Cd ^ 2 * E0 * Cza * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ ^ 2
              * ‖Work.Kernels.qParamFun z‖ := by
          linarith [hP1b, hP2b, hP3b, hP4b, hP5b, hP6b]
      _ = K * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ ^ 2 * ‖Work.Kernels.qParamFun z‖ := by
          rw [hK]; ring
  have hfinal : ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Xi24 τ z‖
      ≤ K * (1 + ‖(τ : ℂ)‖) * (1 + ‖(z : ℂ)‖)
          * Real.exp (-(Real.pi * (4 * τ.im + z.im))) := by
    have hX : (0 : ℝ) ≤ K * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ ^ 2
        * ‖Work.Kernels.qParamFun z‖ := by positivity
    have he2 : ‖Work.Kernels.qParamFun z‖ ≤ Real.exp (-(Real.pi * z.im)) := by
      rw [Work.Asymptotics.norm_qParamFun]
      exact Real.exp_le_exp.mpr (by nlinarith [z.im_pos, Real.pi_pos])
    have he4 : ‖Work.Kernels.qParamFun τ‖ ^ 2 = Real.exp (-(4 * Real.pi * τ.im)) := by
      rw [Work.Asymptotics.norm_qParamFun, sq, ← Real.exp_add]
      congr 1
      ring
    calc ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Xi24 τ z‖
        ≤ K * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ ^ 2
            * ‖Work.Kernels.qParamFun z‖ := hmain
      _ ≤ K * (1 + ‖(τ : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ ^ 2 * ‖Work.Kernels.qParamFun z‖
            * (1 + ‖(z : ℂ)‖) := le_mul_of_one_le_right hX hzn1
      _ = K * (1 + ‖(τ : ℂ)‖) * (1 + ‖(z : ℂ)‖) * ‖Work.Kernels.qParamFun τ‖ ^ 2
            * ‖Work.Kernels.qParamFun z‖ := by ring
      _ ≤ K * (1 + ‖(τ : ℂ)‖) * (1 + ‖(z : ℂ)‖)
            * Real.exp (-(4 * Real.pi * τ.im)) * Real.exp (-(Real.pi * z.im)) := by
          rw [he4]
          have hA : (0 : ℝ) ≤ K * (1 + ‖(τ : ℂ)‖) * (1 + ‖(z : ℂ)‖)
              * Real.exp (-(4 * Real.pi * τ.im)) := by positivity
          exact mul_le_mul_of_nonneg_left he2 hA
      _ = K * (1 + ‖(τ : ℂ)‖) * (1 + ‖(z : ℂ)‖)
            * Real.exp (-(Real.pi * (4 * τ.im + z.im))) := by
          rw [show K * (1 + ‖(τ : ℂ)‖) * (1 + ‖(z : ℂ)‖)
                * Real.exp (-(4 * Real.pi * τ.im)) * Real.exp (-(Real.pi * z.im))
              = K * (1 + ‖(τ : ℂ)‖) * (1 + ‖(z : ℂ)‖)
                * (Real.exp (-(4 * Real.pi * τ.im)) * Real.exp (-(Real.pi * z.im))) from by ring,
            show Real.exp (-(4 * Real.pi * τ.im)) * Real.exp (-(Real.pi * z.im))
              = Real.exp (-(Real.pi * (4 * τ.im + z.im))) from by
                rw [← Real.exp_add]; congr 1; ring]
  simpa [Real.rpow_one] using hfinal

end

end Work.CKFinal
