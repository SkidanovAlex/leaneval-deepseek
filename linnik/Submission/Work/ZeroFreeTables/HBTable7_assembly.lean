/-
# ZeroFreeTables — HBTable7_assembly

The assembly of Heath-Brown's Table 7 from its three analytic/numerical inputs:

* the engine `lemma8_7` (HB (8.11), the third method of HB §8) — in the integral form of
  `Submission/Work/ZeroFreeTables/lemma8_7_v2.lean`;
* the row certificate `table7_rows_cert` (`HBTable7_defs.CertRow` for each row of
  `hbTable7`), stated in terms of the Laplace transform `tfF` of the `θ = π/4` member of
  the HB Lemma 7.1 family;
* the bridge `tfF_eq_laplace` (`tfF` is the Laplace transform of `tf71f (π/4) λ`).

This file contains the *extraction*: the engine's inequality at the true pair
`(λ₁, λ₂)` together with the strict failure of the same inequality at the row's
`(b, c)` (the certificate) forces `λ₂ > c`, by the monotonicity proved in
`HBTable7_extract`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBTable7_defs
import Submission.Work.ZeroFreeTables.HBTable7_extract
import Submission.Work.ZeroFreeTables.testFn7_1
import Submission.Work.ZeroFreeTables.Engine

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- The sign of `λ = π/4` inside `(0, π/2)`. -/
theorem pi_div_four_mem : (0:ℝ) < Real.pi / 4 ∧ Real.pi / 4 < Real.pi / 2 :=
  ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- `f(0)` for the `θ = π/4` member of the HB Lemma 7.1 family: `2λ(π - 3)`. -/
theorem tf71f_pi_div_four_at_zero (lam : ℝ) (hlam : 0 < lam) :
    tf71f (Real.pi / 4) lam 0 = 2 * lam * (Real.pi - 3) := by
  rw [tf71f_at_zero (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hlam,
    Real.tan_pi_div_four]
  have hpi : Real.pi - 3 = Real.pi / 4 + 3 * (Real.pi / 4) - 3 := by ring
  rw [hpi]
  ring

/-- The constant of the engine `lemma8_7` at `c₁ = 1/8`, `c = 1/6` is `ψ(k) + 2(k+1)²ε`,
the constant of the certificate `CertRow` written with `f(0) = 2λ(π-3)`. -/
theorem engine_coeff_eq (k ε : ℝ) :
    (k ^ 2 + 1/2) * ((1:ℝ)/8 + 2 * ε) + 2 * k * (2 * ((1:ℝ)/6) + 2 * ε) + ((1:ℝ)/6 + ε)
      = (psi87 k + tfSlack k ε) := by
  unfold psi87 tfSlack
  ring

/-- The integral form of `tfF lam z` at the exponent shape needed by the engine. -/
theorem tfF_eq_exp {lam : ℝ}
    (hbridge : ∀ z : ℝ, tfF lam z =
      ∫ t in (0:ℝ)..(2 * tf71γ (Real.pi/4) lam), Real.exp (-(z * t)) * tf71f (Real.pi/4) lam t)
    (z : ℝ) :
    tfF lam (-z) = ∫ t in (0:ℝ)..(2 * tf71γ (Real.pi/4) lam),
      Real.exp (z * t) * tf71f (Real.pi/4) lam t := by
  rw [hbridge (-z)]
  exact intervalIntegral.integral_congr (fun t _ => by
    rw [show -((-z) * t) = z * t by ring])

/-- The integral form of `tfF lam z` at the reflected exponent `e^{(z'-z)t}`. -/
theorem tfF_eq_exp_sub {lam : ℝ}
    (hbridge : ∀ z : ℝ, tfF lam z =
      ∫ t in (0:ℝ)..(2 * tf71γ (Real.pi/4) lam), Real.exp (-(z * t)) * tf71f (Real.pi/4) lam t)
    (z z' : ℝ) :
    tfF lam (z - z') = ∫ t in (0:ℝ)..(2 * tf71γ (Real.pi/4) lam),
      Real.exp ((z' - z) * t) * tf71f (Real.pi/4) lam t := by
  rw [hbridge (z - z')]
  exact intervalIntegral.integral_congr (fun t _ => by
    rw [show -((z - z') * t) = (z' - z) * t by ring])

/-- **The extraction of one row.**  If the engine's inequality (HB (8.11), in `tfF` form) holds
at the true pair `(z₁, z₂)` and the row certificate strictly violates it at the row's
`(b, c)`, while `0 ≤ z₁ ≤ b` and `z₂ ≤ c`, then we have a contradiction: hence `z₂ > c`. -/
theorem cert_forces (lam k ε b c z₁ z₂ : ℝ) (hlam : 0 < lam) (hk : 0 ≤ k)
    (hcont : ContinuousOn (tf71f (Real.pi/4) lam) (Set.Icc 0 (2 * tf71γ (Real.pi/4) lam)))
    (hfnn : ∀ t ∈ Set.Icc 0 (2 * tf71γ (Real.pi/4) lam), 0 ≤ tf71f (Real.pi/4) lam t)
    (hbridge : ∀ z : ℝ, tfF lam z =
      ∫ t in (0:ℝ)..(2 * tf71γ (Real.pi/4) lam), Real.exp (-(z * t)) * tf71f (Real.pi/4) lam t)
    (heng : 0 ≤ (k ^ 2 + 1/2) * (tfF lam (-z₂) - tfF lam (z₁ - z₂)) - 2 * k * tfF lam 0
      + (2 * lam * (Real.pi - 3)) * (psi87 k + tfSlack k ε))
    (hcert : CertRow b c k lam ε) (h1 : 0 ≤ z₁) (hz₁ : z₁ ≤ b) (hz₂ : z₂ ≤ c) : False := by
  obtain ⟨hlam', hk', hcert'⟩ := hcert
  have hx₀ : 0 ≤ 2 * tf71γ (Real.pi/4) lam := by
    have h := tf71γ_pos pi_div_four_mem.1 pi_div_four_mem.2 hlam
    linarith
  have hF0 : tfF lam 0 =
      ∫ t in (0:ℝ)..(2 * tf71γ (Real.pi/4) lam), tf71f (Real.pi/4) lam t := by
    rw [hbridge 0]
    exact intervalIntegral.integral_congr (fun t _ => by rw [zero_mul, neg_zero, Real.exp_zero, one_mul])
  rw [tfF_eq_exp hbridge z₂, tfF_eq_exp_sub hbridge z₁ z₂, hF0] at heng
  rw [tfF_eq_exp hbridge c, tfF_eq_exp_sub hbridge b c, hF0] at hcert'
  exact row_extract (A := (2 * lam * (Real.pi - 3)) * (psi87 k + tfSlack k ε))
    hx₀ hcont hfnn h1 hz₁ hz₂ heng hcert' hk

end Work.ZeroFreeTables

namespace Work.ZeroFreeTables

/-- The engine `lemma8_7` requires `0 < ε`, while the certificate
(`table7_rows_cert`) is proved at `ε = 0`.  Since the left hand side of `CertRow` is
*affine* in `ε` with positive slope `(2λ(π-3))·2(k+1)²`, a strictly negative value at
`ε = 0` upgrades to a strictly negative value at a (tiny) positive `ε`. -/
theorem CertRow.eps_pos {b c k lam : ℝ} (h : CertRow b c k lam 0) (hlam : 0 < lam) (hk : 0 ≤ k) :
    ∃ ε : ℝ, 0 < ε ∧ CertRow b c k lam ε := by
  obtain ⟨hlam', hk', hineq⟩ := h
  have hpi : (0:ℝ) < Real.pi - 3 := by linarith [Real.pi_gt_three]
  have hk1 : (0:ℝ) < (k + 1) ^ 2 := by positivity
  have hD : (0:ℝ) < (2 * lam * (Real.pi - 3)) * (2 * (k + 1) ^ 2) := by positivity
  set P : ℝ := (k ^ 2 + 1/2) * (tfF lam (-c) - tfF lam (b - c)) - 2 * k * tfF lam 0
    + (2 * lam * (Real.pi - 3)) * psi87 k with hP
  have hPneg : P < 0 := by
    have h0 : tfSlack k (0:ℝ) = 0 := by simp [tfSlack]
    rw [hP]
    have := hineq
    rw [h0, add_zero] at this
    linarith [this]
  refine ⟨-P / (2 * ((2 * lam * (Real.pi - 3)) * (2 * (k + 1) ^ 2))), ?_, ?_⟩
  · exact div_pos (neg_pos.mpr hPneg) (by positivity)
  · refine ⟨hlam', hk', ?_⟩
    have hkey : tfSlack k (-P / (2 * ((2 * lam * (Real.pi - 3)) * (2 * (k + 1) ^ 2))))
        = 2 * (k + 1) ^ 2 * (-P / (2 * ((2 * lam * (Real.pi - 3)) * (2 * (k + 1) ^ 2)))) := rfl
    rw [hkey, hP]
    have hdiv : ((2 * lam * (Real.pi - 3)) * (2 * (k + 1) ^ 2))
        * (-P / (2 * ((2 * lam * (Real.pi - 3)) * (2 * (k + 1) ^ 2)))) = -P / 2 := by
      field_simp
    linarith [hdiv, hPneg]

end Work.ZeroFreeTables

namespace Work.ZeroFreeTables

/-- Conversion of the engine's conclusion (`lemma8_7`, an inequality between integrals of the
test function `tf71f (π/4) lam`) into the `tfF` form consumed by `cert_forces`, using the bridge
`tfF_eq_laplace` and `f(0) = 2λ(π-3)`. -/
theorem heng_of_engine {lam k ε z₁ z₂ : ℝ} (hlam : 0 < lam)
    (hbridge : ∀ z : ℝ, tfF lam z =
      ∫ t in (0:ℝ)..(2 * tf71γ (Real.pi/4) lam), Real.exp (-(z * t)) * tf71f (Real.pi/4) lam t)
    (h : 0 ≤ (k ^ 2 + 1/2) *
          ((∫ t in (0:ℝ)..(2 * tf71γ (Real.pi/4) lam),
              Real.exp (z₂ * t) * tf71f (Real.pi/4) lam t)
            - (∫ t in (0:ℝ)..(2 * tf71γ (Real.pi/4) lam),
              Real.exp ((z₂ - z₁) * t) * tf71f (Real.pi/4) lam t))
        - 2 * k * (∫ t in (0:ℝ)..(2 * tf71γ (Real.pi/4) lam), tf71f (Real.pi/4) lam t)
        + tf71f (Real.pi/4) lam 0 * (psi87 k + tfSlack k ε)) :
    0 ≤ (k ^ 2 + 1/2) * (tfF lam (-z₂) - tfF lam (z₁ - z₂)) - 2 * k * tfF lam 0
      + (2 * lam * (Real.pi - 3)) * (psi87 k + tfSlack k ε) := by
  have h0 : tfF lam 0 = ∫ t in (0:ℝ)..(2 * tf71γ (Real.pi/4) lam),
      tf71f (Real.pi/4) lam t := by
    rw [hbridge 0]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [zero_mul, neg_zero, Real.exp_zero, one_mul]
  rw [tf71f_pi_div_four_at_zero lam hlam] at h
  rw [tfF_eq_exp hbridge z₂, tfF_eq_exp_sub hbridge z₁ z₂, h0]
  exact h

end Work.ZeroFreeTables
