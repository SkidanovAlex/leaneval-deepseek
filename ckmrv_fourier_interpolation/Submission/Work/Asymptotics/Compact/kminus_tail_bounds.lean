/-
# Bounds for the reference expansion and the cusp deviations of `K_-`

With `e = Ept z` (`‖e‖ = e^{-π z.im}`) the reference part `Tref` of the estimate satisfies
`Tref = e · R` (`Tref8_eq`, `Tref24_eq` in `kminus_tail_core`), and `R` is an explicit
polynomial in `e` whose `e^k`-coefficient is `Xc·(q_k τ) + p_k τ` with `p_k, q_k` polynomials
in the `τ`-atoms (`E4, E6, E8, E10, E14/Δ, Δ, j, ψ₂, ψ₄`).  This file bounds `R`:
`coeffSum24`/`coeffSum8` are the sums of the absolute values of the coefficients (as functions
of `τ` only), continuous by the continuity lemmas of `Ncusp_bound_ball` and hence bounded on
the compact `K`.
-/
import Mathlib
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Ncusp_bound_ball

noncomputable section

open UpperHalfPlane

namespace Work.Asymptotics.Compact

open Work.Kernels
open Work.Residues (Ept Ept_ne_zero norm_Ept)

/-- The sum of the norms of the coefficients of `R24` (a function of `τ` only). -/
def coeffSum24 (ℓ : LogLambdaData) (τ : ℍ) : ℝ :=
  (‖R24_q0 ℓ τ‖ + ‖R24_p0 ℓ τ‖) + (‖R24_q1 ℓ τ‖ + ‖R24_p1 ℓ τ‖)
    + (‖R24_q2 ℓ τ‖ + ‖R24_p2 ℓ τ‖) + (‖R24_q3 ℓ τ‖ + ‖R24_p3 ℓ τ‖)
    + (‖R24_q4 ℓ τ‖ + ‖R24_p4 ℓ τ‖) + (‖R24_q5 ℓ τ‖ + ‖R24_p5 ℓ τ‖)

/-- The sum of the norms of the coefficients of `R8`. -/
def coeffSum8 (ℓ : LogLambdaData) (τ : ℍ) : ℝ :=
  (‖R8_q0 ℓ τ‖ + ‖R8_p0 ℓ τ‖) + (‖R8_q1 ℓ τ‖ + ‖R8_p1 ℓ τ‖)
    + (‖R8_q2 ℓ τ‖ + ‖R8_p2 ℓ τ‖) + (‖R8_q3 ℓ τ‖ + ‖R8_p3 ℓ τ‖)
    + (‖R8_q4 ℓ τ‖ + ‖R8_p4 ℓ τ‖) + (‖R8_q5 ℓ τ‖ + ‖R8_p5 ℓ τ‖)

lemma continuous_coeffSum24 (ℓ : LogLambdaData) : Continuous (fun τ : ℍ => coeffSum24 ℓ τ) := by
  have h1 : Continuous (fun τ : ℍ => psi2 ℓ τ) := continuous_psi2_ub ℓ
  have h2 : Continuous (fun τ : ℍ => psi4 ℓ τ) := continuous_psi4_ub ℓ
  have h3 : Continuous (fun τ : ℍ => E4Fun τ) := continuous_E4Fun_ub
  have h4 : Continuous (fun τ : ℍ => E6Fun τ) := continuous_E6Fun_ub
  have h5 : Continuous (fun τ : ℍ => E14Fun τ / DeltaFun τ) := continuous_fk_two_ub
  have h6 : Continuous (fun τ : ℍ => jInvariantFun τ) := continuous_jInvariantFun_ub
  have h7 : Continuous (fun τ : ℍ => DeltaFun τ) := continuous_DeltaFun_ub
  have h8 : ∀ τ : ℍ, DeltaFun τ ≠ 0 := fun τ => ClassicalFacts.DeltaFun_ne_zero τ
  simp only [coeffSum24, R24_p0, R24_p1, R24_p2, R24_p3, R24_p4, R24_p5,
    R24_q0, R24_q1, R24_q2, R24_q3, R24_q4, R24_q5]
  fun_prop

lemma continuous_coeffSum8 (ℓ : LogLambdaData) : Continuous (fun τ : ℍ => coeffSum8 ℓ τ) := by
  have h1 : Continuous (fun τ : ℍ => psi2 ℓ τ) := continuous_psi2_ub ℓ
  have h2 : Continuous (fun τ : ℍ => psi4 ℓ τ) := continuous_psi4_ub ℓ
  have h3 : Continuous (fun τ : ℍ => E4Fun τ) := continuous_E4Fun_ub
  have h4 : Continuous (fun τ : ℍ => E6Fun τ) := continuous_E6Fun_ub
  have h5 : Continuous (fun τ : ℍ => E14Fun τ / DeltaFun τ) := continuous_fk_two_ub
  have h6 : Continuous (fun τ : ℍ => jInvariantFun τ) := continuous_jInvariantFun_ub
  have h7 : Continuous (fun τ : ℍ => DeltaFun τ) := continuous_DeltaFun_ub
  have h8 : ∀ τ : ℍ, DeltaFun τ ≠ 0 := fun τ => ClassicalFacts.DeltaFun_ne_zero τ
  simp only [coeffSum8, R8_p0, R8_p1, R8_p2, R8_p3, R8_p4, R8_p5,
    R8_q0, R8_q1, R8_q2, R8_q3, R8_q4, R8_q5]
  fun_prop

/-! ## Elementary term estimates -/

/-- A single term of the reference polynomial. -/
lemma norm_eterm_le {E : ℂ} (hE : ‖E‖ ≤ 1) (k : ℕ) (x p q : ℂ) :
    ‖E ^ k * (x * q + p)‖ ≤ (1 + ‖x‖) * (‖q‖ + ‖p‖) := by
  have h1 : ‖E ^ k‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg E) hE
  calc ‖E ^ k * (x * q + p)‖ ≤ ‖E ^ k‖ * ‖x * q + p‖ := norm_mul_le _ _
    _ ≤ 1 * (‖x * q‖ + ‖p‖) := by
        refine mul_le_mul h1 (norm_add_le _ _) (by positivity) (by norm_num)
    _ = ‖x‖ * ‖q‖ + ‖p‖ := by rw [norm_mul]; ring
    _ ≤ (1 + ‖x‖) * (‖q‖ + ‖p‖) := by
        nlinarith [norm_nonneg x, norm_nonneg p, norm_nonneg q]

/-- The triangle inequality for a left-associated sum of six terms. -/
lemma norm_six_le {a b c d e f : ℂ} {A B C D E F : ℝ}
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) (he : ‖e‖ ≤ E)
    (hf : ‖f‖ ≤ F) : ‖a + b + c + d + e + f‖ ≤ A + B + C + D + E + F := by
  have h1 : ‖a + b + c + d + e + f‖ ≤ ‖a + b + c + d + e‖ + ‖f‖ := norm_add_le _ _
  have h2 : ‖a + b + c + d + e‖ ≤ ‖a + b + c + d‖ + ‖e‖ := norm_add_le _ _
  have h3 : ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
  have h4 : ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
  have h5 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
  linarith

/-- `‖Xc ℓ z‖ ≤ (Real.pi + ‖cuspC ℓ‖)(1+‖z‖)`. -/
lemma norm_Xc_le (ℓ : LogLambdaData) (z : ℍ) :
    ‖Xc ℓ z‖ ≤ (Real.pi + ‖cuspC ℓ‖) * (1 + ‖(z : ℂ)‖) := by
  have hX : ‖Xc ℓ z‖ ≤ Real.pi * ‖(z : ℂ)‖ + ‖cuspC ℓ‖ := by
    rw [Xc]
    calc ‖(Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspC ℓ‖
        ≤ ‖(Real.pi : ℂ) * Complex.I * (z : ℂ)‖ + ‖cuspC ℓ‖ := norm_add_le _ _
      _ = Real.pi * ‖(z : ℂ)‖ + ‖cuspC ℓ‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
  nlinarith [hX, Real.pi_pos, norm_nonneg (cuspC ℓ), norm_nonneg (z : ℂ)]

/-- For `z.im ≥ 1`, `‖Ept z‖ ≤ 1`. -/
lemma norm_Ept_le_one {z : ℍ} (hz : 1 ≤ z.im) : ‖Ept z‖ ≤ 1 := by
  rw [norm_Ept]
  exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hz])

/-! ## The bound on the reference parts -/

theorem norm_Tref24_le (ℓ : LogLambdaData) {K : Set ℍ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ), τ ∈ K → 1 ≤ z.im →
      ‖Tref24 ℓ τ z‖ ≤ C * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ := by
  obtain ⟨B, hb⟩ := hK.exists_bound_of_continuousOn
    (continuous_coeffSum24 ℓ).continuousOn
  refine ⟨(max B 1) * (1 + Real.pi + ‖cuspC ℓ‖), by positivity, fun τ z hτ hz => ?_⟩
  have hS : coeffSum24 ℓ τ ≤ max B 1 := le_trans (le_abs_self _) (le_trans (hb τ hτ) (le_max_left _ _))
  have hSnn : 0 ≤ coeffSum24 ℓ τ := by
    simp only [coeffSum24]; positivity
  have hX := norm_Xc_le ℓ z
  have he1 := norm_Ept_le_one hz
  rw [Tref24_eq, norm_mul]
  have hR : ‖R24 ℓ τ z‖ ≤ (1 + ‖Xc ℓ z‖) * coeffSum24 ℓ τ := by
    have t0 := norm_eterm_le he1 0 (Xc ℓ z) (R24_p0 ℓ τ) (R24_q0 ℓ τ)
    have t1 := norm_eterm_le he1 1 (Xc ℓ z) (R24_p1 ℓ τ) (R24_q1 ℓ τ)
    have t2 := norm_eterm_le he1 2 (Xc ℓ z) (R24_p2 ℓ τ) (R24_q2 ℓ τ)
    have t3 := norm_eterm_le he1 3 (Xc ℓ z) (R24_p3 ℓ τ) (R24_q3 ℓ τ)
    have t4 := norm_eterm_le he1 4 (Xc ℓ z) (R24_p4 ℓ τ) (R24_q4 ℓ τ)
    have t5 := norm_eterm_le he1 5 (Xc ℓ z) (R24_p5 ℓ τ) (R24_q5 ℓ τ)
    simp only [pow_zero, pow_one, one_mul] at t0 t1 t2 t3 t4 t5
    simp only [R24, coeffSum24]
    refine le_trans (norm_six_le t0 t1 t2 t3 t4 t5) (le_of_eq ?_)
    ring
  refine le_trans (mul_le_mul_of_nonneg_left hR (norm_nonneg _)) ?_
  have h1X : 1 + ‖Xc ℓ z‖ ≤ (1 + Real.pi + ‖cuspC ℓ‖) * (1 + ‖(z : ℂ)‖) := by
    nlinarith [hX, norm_nonneg (z : ℂ), norm_nonneg (cuspC ℓ), Real.pi_pos]
  have h1Xnn : 0 ≤ 1 + ‖Xc ℓ z‖ := by positivity
  calc ‖Ept z‖ * ((1 + ‖Xc ℓ z‖) * coeffSum24 ℓ τ)
      ≤ ‖Ept z‖ * (((1 + Real.pi + ‖cuspC ℓ‖) * (1 + ‖(z : ℂ)‖)) * (max B 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact mul_le_mul h1X hS hSnn (by positivity)
    _ = (max B 1) * (1 + Real.pi + ‖cuspC ℓ‖) * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ := by ring

theorem norm_Tref8_le (ℓ : LogLambdaData) {K : Set ℍ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ), τ ∈ K → 1 ≤ z.im →
      ‖Tref8 ℓ τ z‖ ≤ C * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ := by
  obtain ⟨B, hb⟩ := hK.exists_bound_of_continuousOn
    (continuous_coeffSum8 ℓ).continuousOn
  refine ⟨(max B 1) * (1 + Real.pi + ‖cuspC ℓ‖), by positivity, fun τ z hτ hz => ?_⟩
  have hS : coeffSum8 ℓ τ ≤ max B 1 := le_trans (le_abs_self _) (le_trans (hb τ hτ) (le_max_left _ _))
  have hSnn : 0 ≤ coeffSum8 ℓ τ := by
    simp only [coeffSum8]; positivity
  have hX := norm_Xc_le ℓ z
  have he1 := norm_Ept_le_one hz
  rw [Tref8_eq, norm_mul]
  have hR : ‖R8 ℓ τ z‖ ≤ (1 + ‖Xc ℓ z‖) * coeffSum8 ℓ τ := by
    have t0 := norm_eterm_le he1 0 (Xc ℓ z) (R8_p0 ℓ τ) (R8_q0 ℓ τ)
    have t1 := norm_eterm_le he1 1 (Xc ℓ z) (R8_p1 ℓ τ) (R8_q1 ℓ τ)
    have t2 := norm_eterm_le he1 2 (Xc ℓ z) (R8_p2 ℓ τ) (R8_q2 ℓ τ)
    have t3 := norm_eterm_le he1 3 (Xc ℓ z) (R8_p3 ℓ τ) (R8_q3 ℓ τ)
    have t4 := norm_eterm_le he1 4 (Xc ℓ z) (R8_p4 ℓ τ) (R8_q4 ℓ τ)
    have t5 := norm_eterm_le he1 5 (Xc ℓ z) (R8_p5 ℓ τ) (R8_q5 ℓ τ)
    simp only [pow_zero, pow_one, one_mul] at t0 t1 t2 t3 t4 t5
    simp only [R8, coeffSum8]
    refine le_trans (norm_six_le t0 t1 t2 t3 t4 t5) (le_of_eq ?_)
    ring
  refine le_trans (mul_le_mul_of_nonneg_left hR (norm_nonneg _)) ?_
  have h1X : 1 + ‖Xc ℓ z‖ ≤ (1 + Real.pi + ‖cuspC ℓ‖) * (1 + ‖(z : ℂ)‖) := by
    nlinarith [hX, norm_nonneg (z : ℂ), norm_nonneg (cuspC ℓ), Real.pi_pos]
  have h1Xnn : 0 ≤ 1 + ‖Xc ℓ z‖ := by positivity
  calc ‖Ept z‖ * ((1 + ‖Xc ℓ z‖) * coeffSum8 ℓ τ)
      ≤ ‖Ept z‖ * (((1 + Real.pi + ‖cuspC ℓ‖) * (1 + ‖(z : ℂ)‖)) * (max B 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact mul_le_mul h1X hS hSnn (by positivity)
    _ = (max B 1) * (1 + Real.pi + ‖cuspC ℓ‖) * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ := by ring

/-! ## Deviation bounds -/

lemma inv_Sh (τ z : ℍ) :
    (Sh τ z)⁻¹ = -((DeltaFun z * (jInvariantFun τ - jInvariantFun z)))⁻¹ := by
  rw [Sh_eq τ z, inv_neg]

lemma qParamFun_eq_Ept_sq (z : ℍ) : Work.Kernels.qParamFun z = (Ept z) ^ 2 := by
  rw [Work.Residues.Ept, Work.Kernels.qParamFun, sq, ← Complex.exp_add]
  ring_nf

/-- `E₄ = 1 + 240 e² + O(e⁴)`. -/
lemma E4_two :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
      ‖E4Fun z - 1 - 240 * (Ept z) ^ 2‖ ≤ C * ‖Ept z‖ ^ 4 := by
  obtain ⟨C, hC, h⟩ := E4_two_term_core
  refine ⟨C, hC, fun z hz => ?_⟩
  have h' := h z hz
  rw [qParamFun_eq_Ept_sq z, norm_pow] at h'
  have h2 : (‖Ept z‖ ^ 2) ^ 2 = ‖Ept z‖ ^ 4 := by ring
  rwa [h2] at h'

/-- `E₆ = 1 - 504 e² + O(e⁴)`. -/
lemma E6_two :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
      ‖E6Fun z - 1 + 504 * (Ept z) ^ 2‖ ≤ C * ‖Ept z‖ ^ 4 := by
  obtain ⟨C, hC, h⟩ := E6_two_term_core
  refine ⟨C, hC, fun z hz => ?_⟩
  have h' := h z hz
  rw [qParamFun_eq_Ept_sq z, norm_pow] at h'
  have h2 : (‖Ept z‖ ^ 2) ^ 2 = ‖Ept z‖ ^ 4 := by ring
  have he : E6Fun z - 1 + 504 * (Ept z) ^ 2 = E6Fun z - 1 - -(504 * (Ept z) ^ 2) := by ring
  rw [he] at h' ⊢
  rwa [h2] at h'

/-- `‖dSinv τ z‖ ≤ C‖Ept z‖⁴` for `z.im ≥ H`, uniformly on `K`. -/
theorem dSinv_bound (ℓ : LogLambdaData) {K : Set ℍ} (hK : IsCompact K) :
    ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ (τ z : ℍ), τ ∈ K → H ≤ z.im →
      ‖dSinv τ z‖ ≤ C * ‖Ept z‖ ^ 4 := by
  obtain ⟨T, hT, C, hC, h⟩ := Work.Asymptotics.cusp_inv_divisor_second (K := K) hK
  refine ⟨T, C, hT, hC, fun τ z hτ hz => ?_⟩
  have h1 := h τ hτ z hz
  have hd : dSinv τ z = -((DeltaFun z * (jInvariantFun τ - jInvariantFun z))⁻¹ + 1
      - (720 - jInvariantFun τ) * (Ept z) ^ 2) := by
    rw [dSinv, Sinvref, inv_Sh τ z]; ring
  rw [hd, norm_neg]
  exact h1

end Work.Asymptotics.Compact
