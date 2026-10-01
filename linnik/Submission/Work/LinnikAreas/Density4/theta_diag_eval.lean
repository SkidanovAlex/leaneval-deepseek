/-
# Area 4 / HB §11 — the diagonal evaluation (HB (11.17))

This file assembles `Work.LinnikAreas.Density4.theta_diag_eval` from the pieces in
`Submission/Work/LinnikAreas/Density4/`.

## The decomposition

With `M = w*L`, `W = e^M`, `A = e^{xL}`, `B₀ = e^{uL}/L²`, `σ = 2-2β`, `κ = Γ(σ)A^σ`,
`a n = (Σ_{d|n} θ_M(W) d)²`, `h n = n^{σ-1}e^{-n/A}`, `h' n = n^{σ-1}e^{-n/B₀}`, `k = h - h'`:

* `Σ' a n * k n = Σ' a n * h n - Σ' a n * h' n`  (`k ≥ 0` since `B₀ ≤ A`);
* `Σ' a n * h n` is bounded by the envelope/Abel argument (`thetaDiag_abel_env`) from
  `S N ≤ 1 + tdF 1 ε M N`, together with `Σ_{n≥2} Δg(n) h n ≤ Mκ - Q + κ`
  (`thetaDiag_Dg_le`, `tdDg_sum_le`) and `Σ_{n≥2} h n ≤ κ` (`thetaDiag_sum_le_kappa`);
* `Σ' a n * h' n ≥ h' 1` since the partial sums `S N` are `≥ a 1 = 1`;
* the resulting inequality is closed by `thetaDiag_final_arith2`, using
  `thetaDiag_Q_lower` (`Q₀ ≥ 0.34 M²` for large `M`) and `thetaDiag_Q1_lower`
  (`Q ≥ Q₀ - e·e^{σM}`), plus `W_pow_le_kappa`, `Gamma_ge_one`, `one_sub_exp_neg_le`.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.Defs
import Submission.Work.LinnikAreas.Density4.thetaDiag_eval_defs
import Submission.Work.LinnikAreas.Density4.thetaDiag_kappa_lower
import Submission.Work.LinnikAreas.Density4.thetaDiag_sum_bounds
import Submission.Work.LinnikAreas.Density4.thetaDiag_Dg_le
import Submission.Work.LinnikAreas.Density4.thetaDiag_abel_env
import Submission.Work.LinnikAreas.Density4.tdDg_sum_le
import Submission.Work.LinnikAreas.Density4.thetaDiag_sum_le_kappa
import Submission.Work.LinnikAreas.Density4.thetaDiag_Q_lower
import Submission.Work.LinnikAreas.Density4.thetaDiag_Q1_lower
import Submission.Work.LinnikAreas.Density4.thetaDiag_final_arith2
import Submission.Work.LinnikAreas.Density4.one_sub_exp_neg_le
import Submission.Work.LinnikAreas.Density4.Gamma_ge_one
import Submission.Work.LinnikAreas.Density4.W_pow_le_kappa
import Submission.Work.LinnikAreas.Density4.tdH_le_one
import Submission.Work.LinnikAreas.Density4.tdQ_summand_nonneg
import Submission.Work.LinnikAreas.Density4.tdQ_full_range_lower
import Submission.Work.LinnikAreas.Density4.summable_and_tsum_shift_two_le

open scoped BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

/-! ## Elementary facts about the vocabulary -/

/-- `a 1 = 1`: the only divisor of `1` is `1`, and `θ_1 = 1`. -/
lemma tdA_one (W : ℝ) (hW : 1 < W) : tdA W 1 = 1 := by
  have hlog : Real.log W ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) (ne_of_gt hW)
  have hmu : (ArithmeticFunction.moebius 1 : ℝ) = 1 := by
    rw [ArithmeticFunction.moebius_apply_one]; norm_num
  have hth : thetaM W 1 = 1 := by
    unfold thetaM
    rw [if_pos (by push_cast; linarith : ((1:ℕ):ℝ) ≤ W)]
    norm_num [hmu, hlog, div_self hlog]
  unfold tdA
  rw [Nat.divisors_one, Finset.sum_singleton, hth, one_pow]

/-- The majorant `tdH σ A` is antitone on the positive integers. -/
lemma tdH_antitone_nat (σ A : ℝ) (hσ1 : σ ≤ 1) (hA : 0 < A) :
    ∀ m n : ℕ, 1 ≤ m → m ≤ n → tdH σ A n ≤ tdH σ A m := by
  intro m n hm hmn
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hmn' : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le hm0 hmn'
  have h1 : (n:ℝ)^(σ-1) ≤ (m:ℝ)^(σ-1) := by
    have h2 : (m:ℝ)^((1:ℝ)-σ) ≤ (n:ℝ)^(1-σ) := Real.rpow_le_rpow hm0.le hmn' (by linarith)
    have h3 : (m:ℝ)^(σ-1) = ((m:ℝ)^(1-σ))⁻¹ := by
      rw [show σ-1 = -((1:ℝ)-σ) by ring, Real.rpow_neg hm0.le]
    have h4 : (n:ℝ)^(σ-1) = ((n:ℝ)^(1-σ))⁻¹ := by
      rw [show σ-1 = -((1:ℝ)-σ) by ring, Real.rpow_neg hn0.le]
    rw [h3, h4]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hn0 _) (Real.rpow_pos_of_pos hm0 _)).mpr h2
  have h5 : Real.exp (-(n:ℝ)/A) ≤ Real.exp (-(m:ℝ)/A) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ hA.le; linarith
  exact mul_le_mul h1 h5 (Real.exp_pos _).le (Real.rpow_nonneg hm0.le _)

lemma tdH_nonneg (σ A : ℝ) (hσ1 : σ ≤ 1) (hA : 0 < A) (n : ℕ) : 0 ≤ tdH σ A n := by
  unfold tdH
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Real.exp_pos _).le

/-- `tdH σ A n ≤ 1` for `n ≥ 1`. -/
lemma tdH_le_one' (σ A : ℝ) (hσ1 : σ ≤ 1) (hA : 0 < A) (n : ℕ) (hn : 1 ≤ n) :
    tdH σ A n ≤ 1 := by
  unfold tdH
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have h1 : (n:ℝ)^(σ-1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)
  have h2 : Real.exp (-(n:ℝ)/A) ≤ 1 := by
    rw [Real.exp_le_one_iff]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hA.le
  calc (n:ℝ)^(σ-1) * Real.exp (-(n:ℝ)/A) ≤ 1 * 1 :=
        mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
    _ = 1 := by ring

/-- `tdA` is nonnegative (it is a square). -/
lemma tdA_nonneg (W : ℝ) (n : ℕ) : 0 ≤ tdA W n := by
  unfold tdA; exact sq_nonneg _

/-- `tdF ε C₁ M 1 = C₁/M²`. -/
lemma tdF_one (ε C₁ M : ℝ) (hM : 0 < M) : tdF ε C₁ M 1 = C₁ / M^2 := by
  unfold tdF tdG
  norm_num [Real.log_one, min_eq_left hM.le]

/-- The increment of the envelope: `tdF ε C₁ M n - tdF ε C₁ M (n-1) = ((1+ε) tdDg M n + C₁)/M²`. -/
lemma tdF_sub (ε C₁ M : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    tdF ε C₁ M n - tdF ε C₁ M (n-1) = ((1+ε)*tdDg M n + C₁)/M^2 := by
  unfold tdF tdDg tdG
  have hcast : ((n:ℝ) - 1) = ((n-1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn]; ring
  rw [← hcast]
  ring

/-- `tdH σ A 1 = e^{-1/A}`. -/
lemma tdH_one_apply (σ A : ℝ) : tdH σ A 1 = Real.exp (-(1:ℝ)/A) := by
  unfold tdH
  rw [Nat.cast_one, Real.one_rpow, one_mul]

/-- `k 1 = e^{-1/A} - e^{-1/B₀} ≤ 1 - e^{-ε}` when `B₀ ≥ 1/ε`. -/
lemma k1_le (σ ε A B0 : ℝ) (hA : 0 < A) (hB0 : 0 < B0) (hεB0 : 1/B0 ≤ ε) :
    tdH σ A 1 - tdH σ B0 1 ≤ 1 - Real.exp (-ε) := by
  rw [tdH_one_apply, tdH_one_apply]
  have h1 : Real.exp (-(1:ℝ)/A) ≤ 1 := Real.exp_le_one_iff.mpr (by
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hA.le)
  have h2 : Real.exp (-ε) ≤ Real.exp (-(1:ℝ)/B0) := by
    apply Real.exp_le_exp.mpr
    have : -(1:ℝ)/B0 = -(1/B0) := by ring
    rw [this]; linarith
  linarith

/-- `κ = Γ(σ)A^σ ≥ 1`. -/
lemma kappa_ge_one (σ A : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hA : 1 ≤ A) :
    1 ≤ Real.Gamma σ * A^σ := by
  have h1 : 1 ≤ Real.Gamma σ := Gamma_ge_one σ hσ hσ1
  have h2 : (1:ℝ) ≤ A^σ := Real.one_le_rpow hA hσ.le
  have h3 : 0 < Real.Gamma σ := lt_of_lt_of_le one_pos h1
  calc (1:ℝ) = 1 * 1 := by ring
    _ ≤ Real.Gamma σ * A^σ := mul_le_mul h1 h2 zero_le_one h3.le
/-! ## The tail of the `h'`-series is bounded below by its first term -/

/-- `Σ' n, a n * tdH σ B₀ n ≥ tdH σ B₀ 1` when `a ≥ 0` and `a 1 = 1`. -/
lemma tdSum_h'_ge (σ B0 : ℝ) (a : ℕ → ℝ) (hσ1 : σ ≤ 1) (hB0 : 0 < B0)
    (ha1 : a 1 = 1) (ha : ∀ n, 0 ≤ a n)
    (hsumm : Summable (fun n => a n * tdH σ B0 n)) :
    tdH σ B0 1 ≤ ∑' n : ℕ, a n * tdH σ B0 n := by
  have hle : (∑ n ∈ Finset.Icc 1 1, a n * tdH σ B0 n) ≤ ∑' n, a n * tdH σ B0 n :=
    Summable.sum_le_tsum (Finset.Icc 1 1)
      (fun i _ => mul_nonneg (ha i) (tdH_nonneg σ B0 hσ1 hB0 i)) hsumm
  have heq : (∑ n ∈ Finset.Icc 1 1, a n * tdH σ B0 n) = tdH σ B0 1 := by
    rw [Finset.Icc_self, Finset.sum_singleton, ha1, one_mul]
  rw [heq] at hle
  exact hle

/-- **The `h`-part of the diagonal evaluation.**  Under the envelope hypothesis
`S n ≤ 1 + tdF ε 1 M n` the whole tail `Σ'_{n≥2} a n · tdH σ A n` is bounded by the Abel/envelope
expression, using `Σ Δg(n) h n ≤ Mκ - Q + κ` (`tdDg_sum_le`) and `Σ h n ≤ κ`. -/
theorem tdSum_h_le_from_envelope (ε σ M A : ℝ) (a : ℕ → ℝ) (hε : 0 < ε) (hM : 0 < M)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hA : 1 ≤ A)
    (ha1 : a 1 = 1) (ha : ∀ n : ℕ, 0 ≤ a n)
    (hS : ∀ n : ℕ, 1 ≤ n → (∑ k ∈ Finset.Icc 1 n, a k) ≤ 1 + tdF ε 1 M n) :
    Summable (fun n : ℕ => a n * tdH σ A n) ∧
    (∑' n : ℕ, a (n+2) * tdH σ A (n+2))
      ≤ (1+ε)*(Real.Gamma σ * A^σ)/M
        - (1+ε)*(∑ n ∈ Finset.Icc 2 ⌊Real.exp M⌋₊, (M - Real.log (n:ℝ) - 1)*tdH σ A n)/M^2
        + (1+ε)*(Real.Gamma σ * A^σ)/M^2 + 2*(Real.Gamma σ * A^σ)/M^2 := by
  have hApos : (0:ℝ) < A := lt_of_lt_of_le one_pos hA
  have hM2pos : (0:ℝ) < M^2 := by positivity
  have h1M2pos : (0:ℝ) < 1/M^2 := by positivity
  have hκ1 : 1 ≤ Real.Gamma σ * A^σ := kappa_ge_one σ A hσ hσ1 hA
  have hf_nn : ∀ n : ℕ, 0 ≤ a n * tdH σ A n :=
    fun n => mul_nonneg (ha n) (tdH_nonneg σ A hσ1 hApos n)
  have hpart : ∀ N : ℕ, 2 ≤ N →
      (∑ n ∈ Finset.Icc 2 N, a n * tdH σ A n)
        ≤ (1+ε)*(Real.Gamma σ * A^σ)/M
          - (1+ε)*(∑ n ∈ Finset.Icc 2 ⌊Real.exp M⌋₊, (M - Real.log (n:ℝ) - 1)*tdH σ A n)/M^2
          + (1+ε)*(Real.Gamma σ * A^σ)/M^2 + 2*(Real.Gamma σ * A^σ)/M^2 := by
    intro N hN
    let N' : ℕ := max N ⌊Real.exp M⌋₊
    have hN'2 : 2 ≤ N' := le_trans hN (le_max_left _ _)
    have hmono : (∑ n ∈ Finset.Icc 2 N, a n * tdH σ A n)
        ≤ ∑ n ∈ Finset.Icc 2 N', a n * tdH σ A n :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc le_rfl (le_max_left _ _)) (fun i _ _ => hf_nn i)
    have habel := thetaDiag_abel_env ε 1 M σ A a hM hσ1 hApos (by rw [ha1]) ha hS N' hN'2
    have hincr : ∀ n ∈ Finset.Icc 2 N',
        tdF ε 1 M n - tdF ε 1 M (n-1) = ((1+ε)*tdDg M n + 1)/M^2 := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      exact tdF_sub ε 1 M n (by omega)
    have hsum1 : (∑ n ∈ Finset.Icc 2 N', (tdF ε 1 M n - tdF ε 1 M (n-1)) * tdH σ A n)
        = ((1+ε)/M^2) * (∑ n ∈ Finset.Icc 2 N', tdDg M n * tdH σ A n)
          + (1/M^2) * (∑ n ∈ Finset.Icc 2 N', tdH σ A n) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      rw [hincr n hn]
      ring
    have hDg := tdDg_sum_le M σ A hM hσ hσ1 hA N' hN'2
    have hQeq : (∑ n ∈ Finset.Icc 2 (min N' ⌊Real.exp M⌋₊),
          (M - Real.log (n:ℝ) - 1)*tdH σ A n)
        = ∑ n ∈ Finset.Icc 2 ⌊Real.exp M⌋₊, (M - Real.log (n:ℝ) - 1)*tdH σ A n := by
      rw [show min N' ⌊Real.exp M⌋₊ = ⌊Real.exp M⌋₊ from min_eq_right (le_max_right _ _)]
    rw [hQeq] at hDg
    have hK : (∑ n ∈ Finset.Icc 2 N', tdH σ A n) ≤ Real.Gamma σ * A^σ :=
      thetaDiag_sum_le_kappa σ A hσ hσ1 hA N'
    have hF1 : tdF ε 1 M 1 = 1/M^2 := tdF_one ε 1 M hM
    have hH2 : tdH σ A 2 ≤ 1 := tdH_le_one' σ A hσ1 hApos 2 (by norm_num)
    have hstep : (∑ n ∈ Finset.Icc 2 N', a n * tdH σ A n)
        ≤ (1+ε)/M^2 * (M*(Real.Gamma σ * A^σ)
            - (∑ n ∈ Finset.Icc 2 ⌊Real.exp M⌋₊, (M - Real.log (n:ℝ) - 1)*tdH σ A n)
            + (Real.Gamma σ * A^σ))
          + (1/M^2)*(Real.Gamma σ * A^σ) + 1/M^2 := by
      have h1 : (∑ n ∈ Finset.Icc 2 N', (tdF ε 1 M n - tdF ε 1 M (n-1)) * tdH σ A n)
          ≤ (1+ε)/M^2 * (M*(Real.Gamma σ * A^σ)
              - (∑ n ∈ Finset.Icc 2 ⌊Real.exp M⌋₊, (M - Real.log (n:ℝ) - 1)*tdH σ A n)
              + (Real.Gamma σ * A^σ))
            + (1/M^2)*(Real.Gamma σ * A^σ) := by
        rw [hsum1]
        have h2 : (1+ε)/M^2 * (∑ n ∈ Finset.Icc 2 N', tdDg M n * tdH σ A n)
            ≤ (1+ε)/M^2 * (M*(Real.Gamma σ * A^σ)
                - (∑ n ∈ Finset.Icc 2 ⌊Real.exp M⌋₊, (M - Real.log (n:ℝ) - 1)*tdH σ A n)
                + (Real.Gamma σ * A^σ)) :=
          mul_le_mul_of_nonneg_left hDg (by positivity)
        have h3 : (1/M^2) * (∑ n ∈ Finset.Icc 2 N', tdH σ A n)
            ≤ (1/M^2)*(Real.Gamma σ * A^σ) :=
          mul_le_mul_of_nonneg_left hK (by positivity)
        linarith
      have h4 : tdF ε 1 M 1 * tdH σ A 2 ≤ 1/M^2 := by
        rw [hF1]
        nlinarith [hH2, h1M2pos]
      linarith [habel, h1, h4]
    have hstep' : (1+ε)/M^2 * (M*(Real.Gamma σ * A^σ)
          - (∑ n ∈ Finset.Icc 2 ⌊Real.exp M⌋₊, (M - Real.log (n:ℝ) - 1)*tdH σ A n)
          + (Real.Gamma σ * A^σ))
        + (1/M^2)*(Real.Gamma σ * A^σ) + 1/M^2
        ≤ (1+ε)*(Real.Gamma σ * A^σ)/M
          - (1+ε)*(∑ n ∈ Finset.Icc 2 ⌊Real.exp M⌋₊, (M - Real.log (n:ℝ) - 1)*tdH σ A n)/M^2
          + (1+ε)*(Real.Gamma σ * A^σ)/M^2 + 2*(Real.Gamma σ * A^σ)/M^2 := by
      have heq : (1+ε)/M^2 * (M*(Real.Gamma σ * A^σ)
            - (∑ n ∈ Finset.Icc 2 ⌊Real.exp M⌋₊, (M - Real.log (n:ℝ) - 1)*tdH σ A n)
            + (Real.Gamma σ * A^σ))
          = (1+ε)*(Real.Gamma σ * A^σ)/M
            - (1+ε)*(∑ n ∈ Finset.Icc 2 ⌊Real.exp M⌋₊, (M - Real.log (n:ℝ) - 1)*tdH σ A n)/M^2
            + (1+ε)*(Real.Gamma σ * A^σ)/M^2 := by
        have hMne : M ≠ 0 := ne_of_gt hM
        field_simp
        try ring
      rw [heq]
      have hle : (1/M^2)*(Real.Gamma σ * A^σ) + 1/M^2 ≤ 2*(Real.Gamma σ * A^σ)/M^2 := by
        rw [show (1/M^2)*(Real.Gamma σ * A^σ) + 1/M^2
              = ((Real.Gamma σ * A^σ) + 1)/M^2 by ring,
            show 2*(Real.Gamma σ * A^σ)/M^2 = (2*(Real.Gamma σ * A^σ))/M^2 by ring]
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      linarith
    linarith [hmono, hstep, hstep']
  exact summable_and_tsum_shift_two_le (fun n => a n * tdH σ A n) hf_nn _
    (fun N hN => hpart N hN)

/-! **HB (11.17), the diagonal evaluation.** -/

theorem theta_diag_eval (ε : ℝ) (hε : 0 < ε) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (u w x L β : ℝ), 0 < u → 1/10 ≤ w → w ≤ 1/2 → w < x → x ≤ 3 → 2 ≤ L →
      L^2 ≤ ε * Real.exp (u*L) → Real.exp (u*L) ≤ Real.exp (x*L) → (1/2:ℝ) ≤ β → β < 1 →
      (∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ Real.exp (w*L) →
        (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM (Real.exp (w*L)) d)^2)
          ≤ 1 + (1+ε)*(N:ℝ)*Real.log (N:ℝ)/(Real.log (Real.exp (w*L)))^2
              + C₁*(N:ℝ)/(Real.log (Real.exp (w*L)))^2) →
      (∀ N : ℕ, Real.exp (w*L) ≤ (N:ℝ) →
        (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM (Real.exp (w*L)) d)^2)
          ≤ 1 + (1+ε)*(N:ℝ)/Real.log (Real.exp (w*L))
              + C₁*(N:ℝ)/(Real.log (Real.exp (w*L)))^2) →
      (∑' n : ℕ, ((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM (Real.exp (w*L)) d)^2)
          * (n:ℝ)^(1-2*β)
          * (Real.exp (-(n:ℝ)/Real.exp (x*L)) - Real.exp (-(n:ℝ)*L^2/Real.exp (u*L))))
        ≤ (1+ε) * (Real.Gamma (2-2*β) / Real.log (Real.exp (w*L))) * (Real.exp (x*L))^(2-2*β)
            + C₂ * ((Real.Gamma (2-2*β) / Real.log (Real.exp (w*L))) * (Real.exp (x*L))^(2-2*β))
                / Real.log (Real.exp (w*L))
            + C₂ / L := by
  refine ⟨1, 10^9 + 2001*(1+ε) + 10, one_pos, by positivity, ?_⟩
  intro u w x L β hu hw10 hw12 hwx hx3 hL2 hLeps huLxL hβ1 hβ2 h1 h2
  -- Abbreviations -------------------------------------------------------------
  obtain ⟨M, hMdef⟩ : ∃ c : ℝ, c = w * L := ⟨_, rfl⟩
  rw [← hMdef] at h1 h2 ⊢
  obtain ⟨W, hWdef⟩ : ∃ c : ℝ, c = Real.exp M := ⟨_, rfl⟩
  rw [← hWdef] at h1 h2 ⊢
  obtain ⟨σ, hσdef⟩ : ∃ c : ℝ, c = 2 - 2*β := ⟨_, rfl⟩
  rw [← hσdef] at ⊢
  obtain ⟨A, hAdef⟩ : ∃ c : ℝ, c = Real.exp (x*L) := ⟨_, rfl⟩
  rw [← hAdef] at huLxL ⊢
  -- Elementary positivity and size facts --------------------------------------
  have hw_pos : 0 < w := by linarith
  have hx_pos : 0 < x := by linarith
  have hL_pos : 0 < L := by linarith
  have hM_pos : 0 < M := by rw [hMdef]; exact mul_pos hw_pos hL_pos
  have hW_gt : 1 < W := by rw [hWdef]; exact Real.one_lt_exp_iff.mpr hM_pos
  have hlogW : Real.log W = M := by rw [hWdef]; exact Real.log_exp M
  have hA_pos : 0 < A := by rw [hAdef]; exact Real.exp_pos _
  have hA_one : 1 ≤ A := by
    rw [hAdef]
    exact Real.one_le_exp_iff.mpr (mul_nonneg hx_pos.le hL_pos.le)
  have hB0_pos : 0 < Real.exp (u*L)/L^2 := div_pos (Real.exp_pos _) (by positivity)
  have hσ_pos : 0 < σ := by rw [hσdef]; linarith
  have hσ_le : σ ≤ 1 := by rw [hσdef]; linarith
  have hAexp : Real.exp M ≤ A := by
    rw [hAdef]
    refine Real.exp_le_exp.mpr ?_
    rw [hMdef]
    exact mul_le_mul_of_nonneg_right hwx.le hL_pos.le
  have hB0_le_A : Real.exp (u*L)/L^2 ≤ A := by
    have hLs1 : (1:ℝ) ≤ L^2 := by nlinarith [hL_pos]
    have hdiv : Real.exp (u*L)/L^2 ≤ Real.exp (u*L) := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < L^2)]
      nlinarith [Real.exp_pos (u*L)]
    exact le_trans hdiv huLxL
  have hB0inv : 1/(Real.exp (u*L)/L^2) ≤ ε := by
    rw [one_div, inv_div, div_le_iff₀ (Real.exp_pos (u*L))]
    linarith [hLeps]
  -- The envelope hypothesis ---------------------------------------------------
  have ha1 : tdA W 1 = 1 := tdA_one W hW_gt
  have ha : ∀ n, 0 ≤ tdA W n := fun n => tdA_nonneg W n
  have hS : ∀ n : ℕ, 1 ≤ n → (∑ k ∈ Finset.Icc 1 n, tdA W k) ≤ 1 + tdF ε 1 M n := by
    intro n hn
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    by_cases hc : (n:ℝ) ≤ W
    · have hlog : Real.log (n:ℝ) ≤ M :=
        (Real.log_le_iff_le_exp hnpos).mpr (by rw [← hWdef]; exact hc)
      have hg : tdG M n = Real.log (n:ℝ) := by rw [tdG]; exact min_eq_left hlog
      have hb := h1 n hn hc
      rw [hlogW] at hb
      have hkey : (1:ℝ) + (1+ε)*(n:ℝ)*Real.log (n:ℝ)/M^2 + 1*(n:ℝ)/M^2
          = 1 + tdF ε 1 M n := by
        rw [tdF, hg]; ring
      rw [← hkey]
      simpa only [tdA] using hb
    · push_neg at hc
      have hlog : M ≤ Real.log (n:ℝ) :=
        (Real.le_log_iff_exp_le hnpos).mpr (by rw [← hWdef]; exact hc.le)
      have hg : tdG M n = M := by rw [tdG]; exact min_eq_right hlog
      have hb := h2 n hc.le
      rw [hlogW] at hb
      have hkey : (1:ℝ) + (1+ε)*(n:ℝ)/M + 1*(n:ℝ)/M^2 = 1 + tdF ε 1 M n := by
        rw [tdF, hg]
        have hMne : M ≠ 0 := ne_of_gt hM_pos
        field_simp
        try ring
      rw [← hkey]
      simpa only [tdA] using hb
  -- The h-part -----------------------------------------------------------------
  obtain ⟨hsumm_h, hbound_h⟩ :=
    tdSum_h_le_from_envelope ε σ M A (fun n => tdA W n) hε hM_pos hσ_pos hσ_le hA_one ha1 ha hS
  obtain ⟨κ, hκdef⟩ : ∃ c : ℝ, c = Real.Gamma σ * A^σ := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ c : ℝ, c = ∑ n ∈ Finset.Icc 2 ⌊Real.exp M⌋₊,
      (M - Real.log (n:ℝ) - 1)*tdH σ A n := ⟨_, rfl⟩
  rw [← hκdef, ← hQdef] at hbound_h
  have hκ_one : 1 ≤ κ := by rw [hκdef]; exact kappa_ge_one σ A hσ_pos hσ_le hA_one
  -- The h'-part ----------------------------------------------------------------
  have hsumm_h' : Summable (fun n : ℕ => tdA W n * tdH σ (Real.exp (u*L)/L^2) n) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hsumm_h
    · intro n
      exact mul_nonneg (ha n) (tdH_nonneg σ _ hσ_le hB0_pos n)
    · intro n
      apply mul_le_mul_of_nonneg_left _ (ha n)
      rw [tdH, tdH]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg n) hB0_pos hB0_le_A
  have h_tsum_h' : tdH σ (Real.exp (u*L)/L^2) 1
      ≤ ∑' n : ℕ, tdA W n * tdH σ (Real.exp (u*L)/L^2) n :=
    tdSum_h'_ge σ (Real.exp (u*L)/L^2) (fun n => tdA W n) hσ_le hB0_pos ha1 ha hsumm_h'
  -- Combined -------------------------------------------------------------------
  have hsplit : (∑' n : ℕ, tdA W n * (tdH σ A n - tdH σ (Real.exp (u*L)/L^2) n))
      = (∑' n, tdA W n * tdH σ A n)
        - (∑' n, tdA W n * tdH σ (Real.exp (u*L)/L^2) n) := by
    rw [← Summable.tsum_sub hsumm_h hsumm_h']
    exact tsum_congr (fun n => by ring)
  have hprefix : (∑' n : ℕ, tdA W n * tdH σ A n)
      = tdH σ A 1 + ∑' n : ℕ, tdA W (n+2) * tdH σ A (n+2) := by
    have hzero : tdA W 0 * tdH σ A 0 = 0 := by
      have h0 : tdA W 0 = 0 := by
        unfold tdA; rw [Nat.divisors_zero, Finset.sum_empty]; ring
      rw [h0, zero_mul]
    have hone : tdA W 1 * tdH σ A 1 = tdH σ A 1 := by rw [ha1, one_mul]
    have hsum1 : Summable (fun n : ℕ => tdA W (n+1) * tdH σ A (n+1)) :=
      (summable_nat_add_iff 1).mpr hsumm_h
    rw [Summable.tsum_eq_zero_add hsumm_h, hzero, zero_add]
    rw [Summable.tsum_eq_zero_add hsum1, hone]
  have hchain : (∑' n : ℕ, tdA W n * (tdH σ A n - tdH σ (Real.exp (u*L)/L^2) n))
      ≤ (tdH σ A 1 - tdH σ (Real.exp (u*L)/L^2) 1)
        + ((1+ε)*κ/M - (1+ε)*Q/M^2 + (1+ε)*κ/M^2 + 2*κ/M^2) := by
    rw [hsplit, hprefix]
    linarith [hbound_h, h_tsum_h']
  -- The final real arithmetic --------------------------------------------------
  have harith : (tdH σ A 1 - tdH σ (Real.exp (u*L)/L^2) 1)
        + (1+ε)*κ/M - (1+ε)*Q/M^2 + (1+ε)*κ/M^2 + 2*1*κ/M^2
      ≤ (1+ε)*κ/M + (10^9 + 2001*(1+ε) + 10)*κ/M^2 + (10^9 + 2001*(1+ε) + 10)/L := by
    have hk1 : tdH σ A 1 - tdH σ (Real.exp (u*L)/L^2) 1 ≤ 1 - Real.exp (-ε) :=
      k1_le σ ε A (Real.exp (u*L)/L^2) hA_pos hB0_pos hB0inv
    have hC2le : (1+ε) + 1 + 10^9 + 2000*(1+ε) ≤ 10^9 + 2001*(1+ε) + 10 := by linarith
    by_cases hMbig : 15000 ≤ M
    · have hQbig : 0.34 * M^2 ≤ tdQ σ A M := thetaDiag_Q_lower M σ A hMbig hσ_pos hσ_le hAexp
      have hQge : tdQ σ A M - Real.exp 1 * Real.exp (σ*M) ≤ Q := by
        rw [hQdef]
        exact thetaDiag_Q1_lower M σ A (by linarith) hσ_pos hσ_le hAexp
      have hQ0 : 0 ≤ tdQ σ A M := by
        unfold tdQ
        exact Finset.sum_nonneg (fun n hn => tdQ_summand_nonneg M σ A hMbig n hn)
      have hs : Real.exp 1 * Real.exp (σ*M) ≤ 1000 * κ := by
        have h1' := W_pow_le_kappa M σ A hσ_pos hσ_le hAexp
        rw [← hκdef] at h1'
        have he3 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
        have hk0 : 0 ≤ κ := le_trans zero_le_one hκ_one
        have h2' : Real.exp 1 * Real.exp (σ*M) ≤ Real.exp 1 * (3*κ) :=
          mul_le_mul_of_nonneg_left h1' (Real.exp_pos 1).le
        have h3' : Real.exp 1 * (3*κ) ≤ 1000*κ := by
          calc Real.exp 1 * (3*κ) = (Real.exp 1 * 3) * κ := by ring
            _ ≤ (3*3)*κ := mul_le_mul_of_nonneg_right (by linarith) hk0
            _ = 9*κ := by ring
            _ ≤ 1000*κ := mul_le_mul_of_nonneg_right (by norm_num) hk0
        linarith
      exact thetaDiag_final_arith2 ε 1 (10^9 + 2001*(1+ε) + 10) M L κ Q (tdQ σ A M)
        (Real.exp 1 * Real.exp (σ*M)) (tdH σ A 1 - tdH σ (Real.exp (u*L)/L^2) 1)
        hε hM_pos hL_pos hκ_one hQge hQ0 hs (fun _ => hQbig) hk1 le_rfl zero_le_one hC2le
    · push_neg at hMbig
      have hQge : -1000*κ ≤ Q := by
        rw [hQdef, hκdef]
        exact tdQ_full_range_lower σ A M hσ_pos hσ_le hAexp
      exact thetaDiag_final_arith2 ε 1 (10^9 + 2001*(1+ε) + 10) M L κ Q 0 (1000*κ)
        (tdH σ A 1 - tdH σ (Real.exp (u*L)/L^2) 1)
        hε hM_pos hL_pos hκ_one (by linarith) le_rfl le_rfl
        (fun h => absurd h (not_le.mpr hMbig)) hk1 le_rfl zero_le_one hC2le
  have hfin : (∑' n : ℕ, tdA W n * (tdH σ A n - tdH σ (Real.exp (u*L)/L^2) n))
      ≤ (1+ε)*κ/M + (10^9 + 2001*(1+ε) + 10)*κ/M^2 + (10^9 + 2001*(1+ε) + 10)/L := by
    rw [show (2:ℝ)*1*κ/M^2 = 2*κ/M^2 from by ring] at harith
    linarith [hchain, harith]
  -- Identification of the target ----------------------------------------------
  have hLHS : (∑' n : ℕ, (∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM W d)^2 * (n:ℝ)^(1-2*β)
        * (Real.exp (-(n:ℝ)/A) - Real.exp (-(n:ℝ)*L^2/Real.exp (u*L))))
      = ∑' n : ℕ, tdA W n * (tdH σ A n - tdH σ (Real.exp (u*L)/L^2) n) := by
    apply tsum_congr
    intro n
    have hβ : (1:ℝ) - 2*β = σ - 1 := by rw [hσdef]; ring
    have hdiv : (n:ℝ)*L^2/Real.exp (u*L) = (n:ℝ)/(Real.exp (u*L)/L^2) := by
      have hLne : L ≠ 0 := ne_of_gt hL_pos
      have hene : Real.exp (u*L) ≠ 0 := ne_of_gt (Real.exp_pos _)
      field_simp
    have harg : (-(n:ℝ))*L^2/Real.exp (u*L) = (-(n:ℝ))/(Real.exp (u*L)/L^2) := by
      rw [show (-(n:ℝ))*L^2 = -((n:ℝ)*L^2) by ring, neg_div, neg_div, hdiv]
    simp only [tdA, tdH]
    rw [hβ, harg]
    ring
  have hRHS : (1+ε) * (Real.Gamma σ / Real.log W) * A^σ
        + (10^9 + 2001*(1+ε) + 10) * ((Real.Gamma σ / Real.log W) * A^σ) / Real.log W
        + (10^9 + 2001*(1+ε) + 10) / L
      = (1+ε)*κ/M + (10^9 + 2001*(1+ε) + 10)*κ/M^2 + (10^9 + 2001*(1+ε) + 10)/L := by
    rw [hlogW, hκdef]
    ring
  rw [hLHS, hRHS]
  exact hfin

end Work.LinnikAreas.Density4
