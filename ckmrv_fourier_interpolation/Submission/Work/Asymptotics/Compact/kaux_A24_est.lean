/-
# The atom `A₂₄` is `O(1 + ‖z‖)` for `τ` in a compact set

The bracket atom
`A24 ℓ τ z = -3456 Δ(τ) E14(z) 𝓛(z) - (ψ₂(τ)E₁₀(τ) - ψ₄(τ)E₈(τ)) E₁₀(z) (U(z)² - V(z)²)`
grows at most like `1 + ‖z‖` as `z → i∞`, uniformly for `τ` in a compact `K ⊆ ℍ`.

The `z`-growth comes from the single factor `𝓛(z) = πi z + C + O(e^{-π z.im})` (the constants
of `𝓛` are `O(1+‖z‖)`, `cuspC_spec`), multiplied by the *bounded* atoms `Δ(τ)`, `E14(z)`.  The
second summand is a product of the bounded atoms `E₁₀(z)` and `U(z)² - V(z)² = W(z)(W(z)+2V(z))`.

This file proves the estimate by exposing plain (non-asymptotic) bounds for the individual
factors: `cuspEst_bdd` converts a `CuspEst` statement into a uniform bound, `L_bound` bounds
`𝓛` by `C(1+‖z‖)` via `cuspC_spec` and `norm_Xc_le`, and compactness of `K` supplies the
`τ`-bounds from the continuity lemmas of `Ncusp_bound_ball`.
-/
import Mathlib
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Compact.kminus_tail_bounds
import Submission.Work.Asymptotics.KMinusCuspBallLimit
import Submission.Work.Asymptotics.Ncusp_bound_ball

namespace Work.Asymptotics.Compact

open UpperHalfPlane

open Work.Kernels
open Work.Residues (Ept)

noncomputable section

/-! ## Turning a `CuspEst` into an honest bound -/

/-- A `CuspEst f k` gives `‖f z‖ ≤ C` for all large `z.im` (since `tpar z ≤ 1`). -/
lemma cuspEst_bdd {f : ℍ → ℂ} {k : ℕ} (h : Work.Asymptotics.CuspEst f k) :
    ∃ H C : ℝ, 0 < C ∧ ∀ z : ℍ, H ≤ z.im → ‖f z‖ ≤ C := by
  obtain ⟨H, C, hC, hb⟩ := h
  refine ⟨H, C, hC, fun z hz => ?_⟩
  have ht : Work.Residues.tpar z ^ k ≤ 1 :=
    pow_le_one₀ (Work.Residues.tpar_nonneg z) (Work.Residues.tpar_le_one z)
  have hle : C * Work.Residues.tpar z ^ k ≤ C := mul_le_of_le_one_right hC.le ht
  linarith [hb z hz, hle]

/-! ## Elementary products estimates -/

/-- `‖a * b * c‖ ≤ A * B * C` from factorwise bounds. -/
lemma norm_mul_three_le {a b c : ℂ} {A B C : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B)
    (hc : ‖c‖ ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B) : ‖a * b * c‖ ≤ A * B * C := by
  rw [norm_mul, norm_mul]
  have h1 : ‖a‖ * ‖b‖ ≤ A * B := mul_le_mul ha hb (norm_nonneg _) hA
  exact mul_le_mul h1 hc (norm_nonneg _) (mul_nonneg hA hB)

/-- `‖a * b * c * d‖ ≤ A * B * C * D` from factorwise bounds. -/
lemma norm_mul_four_le {a b c d : ℂ} {A B C D : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B)
    (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    ‖a * b * c * d‖ ≤ A * B * C * D := by
  rw [norm_mul, norm_mul, norm_mul]
  have h1 : ‖a‖ * ‖b‖ ≤ A * B := mul_le_mul ha hb (norm_nonneg _) hA
  have h2 : ‖a‖ * ‖b‖ * ‖c‖ ≤ A * B * C :=
    mul_le_mul h1 hc (norm_nonneg _) (mul_nonneg hA hB)
  exact mul_le_mul h2 hd (norm_nonneg _) (mul_nonneg (mul_nonneg hA hB) hC)

/-! ## Bounds for the `z`-atoms -/

/-- `E₁₀(z)` is bounded on the cusp. -/
lemma E10Fun_bound : ∃ H C : ℝ, 0 < C ∧ ∀ z : ℍ, H ≤ z.im → ‖E10Fun z‖ ≤ C :=
  cuspEst_bdd Work.Asymptotics.cuspEst_E10Fun

/-- `E₁₄(z)` is bounded on the cusp. -/
lemma E14Fun_bound : ∃ H C : ℝ, 0 < C ∧ ∀ z : ℍ, H ≤ z.im → ‖E14Fun z‖ ≤ C :=
  cuspEst_bdd Work.Asymptotics.cuspEst_E14Fun

/-- `U(z)² - V(z)² = W(z)·(W(z) + 2V(z))` is bounded on the cusp. -/
lemma UFun_sq_sub_VFun_sq_bound :
    ∃ H C : ℝ, 0 < C ∧ ∀ z : ℍ, H ≤ z.im → ‖UFun z ^ 2 - VFun z ^ 2‖ ≤ C := by
  obtain ⟨H1, C1, hC1, h1⟩ := cuspEst_bdd Work.Asymptotics.cuspEst_WFun
  obtain ⟨H2, C2, hC2, h2⟩ := cuspEst_bdd Work.Asymptotics.cuspEst_VFun
  refine ⟨max H1 H2, C1 * (C1 + 2 * C2), by positivity, fun z hz => ?_⟩
  have hz1 : H1 ≤ z.im := le_trans (le_max_left _ _) hz
  have hz2 : H2 ≤ z.im := le_trans (le_max_right _ _) hz
  have hq : UFun z = WFun z + VFun z := Work.Kernels.TildeFacts.theta_quartic z
  have hb1 := h1 z hz1
  have hb2 := h2 z hz2
  have hb3 : ‖WFun z + 2 * VFun z‖ ≤ C1 + 2 * C2 := by
    have hsplit : ‖WFun z + 2 * VFun z‖ ≤ ‖WFun z‖ + ‖(2 : ℂ) * VFun z‖ := norm_add_le _ _
    have h2' : ‖(2 : ℂ) * VFun z‖ = 2 * ‖VFun z‖ := by rw [norm_mul]; norm_num
    rw [h2'] at hsplit
    linarith
  rw [show UFun z ^ 2 - VFun z ^ 2 = WFun z * (WFun z + 2 * VFun z) by rw [hq]; ring]
  rw [norm_mul]
  exact mul_le_mul hb1 hb3 (norm_nonneg _) hC1.le

/-! ## The bound for `𝓛` -/

/-- The deviation of `𝓛` from its main term `Xc` is bounded on the cusp. -/
lemma L_sub_Xc_bound (ℓ : LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖ℓ.L z - Xc ℓ z‖ ≤ C := by
  obtain ⟨C0, hC0, h0⟩ := cuspC_spec ℓ
  refine ⟨C0 + 20, by positivity, fun z hz => ?_⟩
  have hE : ‖Ept z‖ ≤ 1 := norm_Ept_le_one hz
  have hE3 : ‖Ept z‖ ^ 3 ≤ 1 := pow_le_one₀ (norm_nonneg _) hE
  have hE2 : ‖Ept z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hE
  have hb1 : ‖ℓ.L z - (Xc ℓ z - 8 * Ept z + 12 * (Ept z) ^ 2)‖ ≤ C0 := by
    have h1 := h0 z hz
    calc ‖ℓ.L z - (Xc ℓ z - 8 * Ept z + 12 * (Ept z) ^ 2)‖
        ≤ C0 * ‖Ept z‖ ^ 3 := h1
      _ ≤ C0 * 1 := mul_le_mul_of_nonneg_left hE3 hC0.le
      _ = C0 := by ring
  have hb2 : ‖12 * (Ept z) ^ 2 - 8 * Ept z‖ ≤ 20 := by
    have hsplit : ‖12 * (Ept z) ^ 2 - 8 * Ept z‖
        ≤ ‖(12 : ℂ) * (Ept z) ^ 2‖ + ‖(8 : ℂ) * Ept z‖ := norm_sub_le _ _
    have e1 : ‖(8 : ℂ) * Ept z‖ = 8 * ‖Ept z‖ := by rw [norm_mul]; norm_num
    have e2 : ‖(12 : ℂ) * (Ept z) ^ 2‖ = 12 * ‖Ept z‖ ^ 2 := by rw [norm_mul, norm_pow]; norm_num
    rw [e1, e2] at hsplit
    linarith [hE, hE2, norm_nonneg (Ept z)]
  have hdec : ℓ.L z - Xc ℓ z
      = (ℓ.L z - (Xc ℓ z - 8 * Ept z + 12 * (Ept z) ^ 2)) + (12 * (Ept z) ^ 2 - 8 * Ept z) := by
    ring
  rw [hdec]
  linarith [norm_add_le (ℓ.L z - (Xc ℓ z - 8 * Ept z + 12 * (Ept z) ^ 2))
    (12 * (Ept z) ^ 2 - 8 * Ept z), hb1, hb2]

/-- `‖𝓛 z‖ ≤ C(1 + ‖z‖)` for `z.im ≥ 1`. -/
lemma L_bound (ℓ : LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im → ‖ℓ.L z‖ ≤ C * (1 + ‖(z : ℂ)‖) := by
  obtain ⟨Ldev, hLdev, hdev⟩ := L_sub_Xc_bound ℓ
  refine ⟨Real.pi + ‖cuspC ℓ‖ + Ldev, by positivity, fun z hz => ?_⟩
  have h1 : ‖Xc ℓ z‖ ≤ (Real.pi + ‖cuspC ℓ‖) * (1 + ‖(z : ℂ)‖) := norm_Xc_le ℓ z
  have h2 : ‖ℓ.L z - Xc ℓ z‖ ≤ Ldev := hdev z hz
  have h3 : ‖ℓ.L z‖ ≤ ‖ℓ.L z - Xc ℓ z‖ + ‖Xc ℓ z‖ := by
    have h := norm_add_le (ℓ.L z - Xc ℓ z) (Xc ℓ z)
    simpa using h
  have hnn : (0 : ℝ) ≤ ‖(z : ℂ)‖ := norm_nonneg _
  have hone : (1 : ℝ) ≤ 1 + ‖(z : ℂ)‖ := by linarith
  refine le_trans h3 ?_
  have hsum : ‖ℓ.L z - Xc ℓ z‖ + ‖Xc ℓ z‖
      ≤ Ldev + (Real.pi + ‖cuspC ℓ‖) * (1 + ‖(z : ℂ)‖) := add_le_add h2 h1
  refine le_trans hsum ?_
  nlinarith [hLdev.le, hone, hnn]

/-! ## The main estimate -/

theorem kaux_A24_est (ℓ : Work.Kernels.LogLambdaData) {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ (τ z : UpperHalfPlane), τ ∈ K → H ≤ z.im →
      ‖Work.Asymptotics.Compact.A24 ℓ τ z‖ ≤ C * (1 + ‖(z : ℂ)‖) := by
  obtain ⟨CL, hCL, hLb⟩ := L_bound ℓ
  obtain ⟨H14, C14, hC14, hb14⟩ := E14Fun_bound
  obtain ⟨H10, C10, hC10, hb10⟩ := E10Fun_bound
  obtain ⟨Huv, Cuv, hCuv, hbuv⟩ := UFun_sq_sub_VFun_sq_bound
  have hE10cont : Continuous (fun τ : ℍ => E10Fun τ) :=
    continuous_E4Fun_ub.mul continuous_E6Fun_ub
  have hE8cont : Continuous (fun τ : ℍ => E8Fun τ) := continuous_E4Fun_ub.pow 2
  have hψcont : Continuous (fun τ : ℍ => psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) :=
    ((continuous_psi2_ub ℓ).mul hE10cont).sub ((continuous_psi4_ub ℓ).mul hE8cont)
  obtain ⟨Bd, hBd⟩ := hK.exists_bound_of_continuousOn continuous_DeltaFun_ub.continuousOn
  obtain ⟨Bψ, hBψ⟩ := hK.exists_bound_of_continuousOn hψcont.continuousOn
  set MΔ : ℝ := max Bd 1 with hMΔdef
  set Mψ : ℝ := max Bψ 1 with hMψdef
  have hMΔ0 : 0 < MΔ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hMψ0 : 0 < Mψ := lt_of_lt_of_le one_pos (le_max_right _ _)
  set H : ℝ := max 1 (max (max H14 H10) Huv) with hHdef
  have hHpos : 0 < H := by rw [hHdef]; positivity
  have hH1 : (1 : ℝ) ≤ H := by rw [hHdef]; exact le_max_left _ _
  have hH14 : H14 ≤ H := by
    rw [hHdef]
    exact le_trans (le_max_left H14 H10)
      (le_trans (le_max_left (max H14 H10) Huv) (le_max_right 1 _))
  have hH10 : H10 ≤ H := by
    rw [hHdef]
    exact le_trans (le_max_right H14 H10)
      (le_trans (le_max_left (max H14 H10) Huv) (le_max_right 1 _))
  have hHuv : Huv ≤ H := by
    rw [hHdef]
    exact le_trans (le_max_right (max H14 H10) Huv) (le_max_right 1 _)
  refine ⟨H, 3456 * MΔ * C14 * CL + Mψ * C10 * Cuv, hHpos, ?_, ?_⟩
  · have h1 : 0 < 3456 * MΔ * C14 * CL := by positivity
    have h2 : 0 < Mψ * C10 * Cuv := by positivity
    linarith
  · intro τ z hτ hz
    have hz1 : 1 ≤ z.im := le_trans hH1 hz
    have hz14 : H14 ≤ z.im := le_trans hH14 hz
    have hz10 : H10 ≤ z.im := le_trans hH10 hz
    have hzuv : Huv ≤ z.im := le_trans hHuv hz
    have bE14 : ‖E14Fun z‖ ≤ C14 := hb14 z hz14
    have bE10 : ‖E10Fun z‖ ≤ C10 := hb10 z hz10
    have buv : ‖UFun z ^ 2 - VFun z ^ 2‖ ≤ Cuv := hbuv z hzuv
    have bL : ‖ℓ.L z‖ ≤ CL * (1 + ‖(z : ℂ)‖) := hLb z hz1
    have bΔ : ‖DeltaFun τ‖ ≤ MΔ := le_trans (hBd τ hτ) (le_max_left _ _)
    have bψ : ‖psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ‖ ≤ Mψ :=
      le_trans (hBψ τ hτ) (le_max_left _ _)
    have h3456norm : ‖(-3456 : ℂ)‖ ≤ 3456 := by norm_num
    have t1 : ‖-3456 * DeltaFun τ * E14Fun z * ℓ.L z‖
        ≤ 3456 * MΔ * C14 * (CL * (1 + ‖(z : ℂ)‖)) :=
      norm_mul_four_le h3456norm bΔ bE14 bL (by norm_num) hMΔ0.le hC14.le
    have t1' : ‖-3456 * DeltaFun τ * E14Fun z * ℓ.L z‖
        ≤ 3456 * MΔ * C14 * CL * (1 + ‖(z : ℂ)‖) :=
      le_trans t1 (le_of_eq (by ring))
    have t2 : ‖(psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) * E10Fun z
        * (UFun z ^ 2 - VFun z ^ 2)‖ ≤ Mψ * C10 * Cuv * (1 + ‖(z : ℂ)‖) := by
      have hbase : ‖(psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) * E10Fun z
          * (UFun z ^ 2 - VFun z ^ 2)‖ ≤ Mψ * C10 * Cuv :=
        norm_mul_three_le bψ bE10 buv hMψ0.le hC10.le
      calc ‖(psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) * E10Fun z
            * (UFun z ^ 2 - VFun z ^ 2)‖
          ≤ Mψ * C10 * Cuv := hbase
        _ ≤ Mψ * C10 * Cuv * (1 + ‖(z : ℂ)‖) := by
          have hnn : (0 : ℝ) ≤ Mψ * C10 * Cuv := by positivity
          have hge : (1 : ℝ) ≤ 1 + ‖(z : ℂ)‖ := by linarith [norm_nonneg (z : ℂ)]
          have hstep : Mψ * C10 * Cuv * 1 ≤ Mψ * C10 * Cuv * (1 + ‖(z : ℂ)‖) :=
            mul_le_mul_of_nonneg_left hge hnn
          rw [mul_one] at hstep
          exact hstep
    rw [A24]
    refine le_trans (norm_sub_le _ _) ?_
    refine le_trans (add_le_add t1' t2) ?_
    have heq : 3456 * MΔ * C14 * CL * (1 + ‖(z : ℂ)‖) + Mψ * C10 * Cuv * (1 + ‖(z : ℂ)‖)
        = (3456 * MΔ * C14 * CL + Mψ * C10 * Cuv) * (1 + ‖(z : ℂ)‖) := by ring
    rw [heq]

end

end Work.Asymptotics.Compact
