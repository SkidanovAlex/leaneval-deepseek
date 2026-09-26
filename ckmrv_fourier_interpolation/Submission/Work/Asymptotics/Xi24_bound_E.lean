import Mathlib
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.Funnel_Kfun_diag_bound
import Submission.Work.Kernels.Kernels

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm

noncomputable section

set_option maxHeartbeats 8000000

/-!
## The `τ`-atoms of `Ξ₂₄` and the decomposition used for the cusp bound

`Ξ₂₄(τ,z)` is a `ℂ`-linear combination (with `z`-dependent coefficients) of the `τ`-atoms

* `Xi24r0 τ = τ E₁₄(τ)`,
* `Xi24r1 τ = φ₀(τ) Δ(τ)`,
* `Xi24r2 τ = φ₂(τ) E₁₀(τ)`,
* `Xi24R0 τ = φ₀(τ) E₄(τ)³ = Xi24r1 τ · j(τ)`,

together with `j(τ)`.  The point of the last identity is that `R0` is bounded by a power of
`scale τ` even though `j(τ)` is not.
-/

/-- `r0 τ = τ E₁₄(τ)`. -/
def Xi24r0 (t : ℍ) : ℂ := (t : ℂ) * Work.Kernels.E14Fun t

/-- `r1 τ = φ₀(τ) Δ(τ)`. -/
def Xi24r1 (t : ℍ) : ℂ := Work.Kernels.phi0 t * Work.Kernels.DeltaFun t

/-- `r2 τ = φ₂(τ) E₁₀(τ)`. -/
def Xi24r2 (t : ℍ) : ℂ := Work.Kernels.phi2 t * Work.Kernels.E10Fun t

/-- `R0 τ = φ₀(τ) E₄(τ)³ = r1 τ · j(τ)`. -/
def Xi24R0 (t : ℍ) : ℂ := Work.Kernels.phi0 t * Work.Kernels.E4Fun t ^ 3

/-- `δ(z) = E₄(z) - E₂(z)² = O(q_z)`. -/
def Xi24delta (z : ℍ) : ℂ := Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2

/-- `r(z) = 5E₄(z)² - 7E₄(z)E₂(z)² + 2E₆(z)E₂(z) = O(q_z²)`. -/
def Xi24rr (z : ℍ) : ℂ :=
  5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2
    + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z

/-- `r1 τ · j(τ) = R0 τ`. -/
lemma Xi24r1_mul_jInvariantFun (t : ℍ) :
    Xi24r1 t * Work.Kernels.jInvariantFun t = Xi24R0 t := by
  have hDt : Work.Kernels.DeltaFun t ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero t
  simp only [Xi24r1, Xi24R0, Work.Kernels.jInvariantFun]
  field_simp

/-- **The decomposition of `Ξ₂₄`.**  Writing `A = r0 + r2 - 2R0` and
`B = 6δ(z)(j(τ)-j(z)) + 1728E₄(z)`,  we have
`Ξ₂₄(τ,z) = A·B + 1728(7R0-r0)δ(z) - 1728 r1 E₄(z)² r(z) / Δ(z)`. -/
theorem Xi24_decomp (τ z : ℍ) :
    Xi24 τ z =
      (Xi24r0 τ + Xi24r2 τ - 2 * Xi24R0 τ)
          * (6 * Xi24delta z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
              + 1728 * Work.Kernels.E4Fun z)
        + 1728 * (7 * Xi24R0 τ - Xi24r0 τ) * Xi24delta z
        - 1728 * Xi24r1 τ * Work.Kernels.E4Fun z ^ 2 * Xi24rr z / Work.Kernels.DeltaFun z := by
  have hDz : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  have hDt : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  simp only [Xi24, Xi24r0, Xi24r1, Xi24r2, Xi24R0, Xi24delta, Xi24rr,
    Fin.sum_univ_three, Work.Kernels.phiVec, Work.Kernels.c1728, Work.Kernels.E14Fun,
    Work.Kernels.E10Fun, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one, mul_one]
  rw [show Work.Kernels.fk (4 : ℤ) z = Work.Kernels.E4Fun z from rfl,
    show Work.Kernels.fk (2 : ℤ) z
      = Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z / Work.Kernels.DeltaFun z from rfl,
    show Work.Kernels.fk (0 : ℤ) z = 1 from rfl,
    show Work.Kernels.fk (14 : ℤ) τ = Work.Kernels.E14Fun τ from rfl,
    show Work.Kernels.fk (12 : ℤ) τ = Work.Kernels.DeltaFun τ from rfl,
    show Work.Kernels.fk (10 : ℤ) τ = Work.Kernels.E10Fun τ from rfl]
  simp only [Work.Kernels.phiNeg2, Work.Kernels.jInvariantFun]
  field_simp [hDz, hDt]
  ring

/-! ## The `z`-side cusp bounds -/

private lemma E4E2_sub_E6_two_term :
    IsBigOq (fun τ => Work.Kernels.E4Fun τ * Work.Kernels.E2Fun τ
      - Work.Kernels.E6Fun τ - 720 * Work.Kernels.qParamFun τ) 2 := by
  have hu := E4Fun_isBigOq
  have hv := E2Fun_isBigOq
  have hw := E6Fun_isBigOq
  have h1 : IsBigOq (fun τ => -5760 * Work.Kernels.qParamFun τ ^ 2) 2 :=
    qParamFun_sq_isBigOq.const_mul (-5760)
  have h2 : IsBigOq (fun τ => (1 + 240 * Work.Kernels.qParamFun τ)
      * (Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ)) 2 :=
    (isBigOq_one_add_const_mul_q 240).mul hv
  have h3 : IsBigOq (fun τ => (1 + (-24) * Work.Kernels.qParamFun τ)
      * (Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ)) 2 :=
    (isBigOq_one_add_const_mul_q (-24)).mul hu
  have h4 : IsBigOq (fun τ => (Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ)
      * (Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ)) 2 :=
    (hu.mul hv).mono (by norm_num)
  refine (((h1.add h2).add h3).add h4).add hw.neg |>.congr (fun τ => ?_)
  ring

private lemma Xi24rr_isBigOq : IsBigOq Xi24rr 2 := by
  have h1 : IsBigOq (fun τ => 5 * (Work.Kernels.E4Fun τ ^ 2
      - Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ - 1008 * Work.Kernels.qParamFun τ)) 2 :=
    eps_two_term.const_mul 5
  have h2 : IsBigOq (fun τ => -7 * Work.Kernels.E2Fun τ * (Work.Kernels.E4Fun τ * Work.Kernels.E2Fun τ
      - Work.Kernels.E6Fun τ - 720 * Work.Kernels.qParamFun τ)) 2 :=
    ((E2Fun_bdd.mul E4E2_sub_E6_two_term).const_mul (-7)).congr (fun τ => by ring)
  have h3 : IsBigOq (fun τ => 5040 * (1 - Work.Kernels.E2Fun τ)
      * Work.Kernels.qParamFun τ) 2 :=
    ((E2_minus_one.neg.mul qParamFun_isBigOq).const_mul 5040).congr (fun τ => by ring)
  refine ((h1.add h2).add h3).congr (fun τ => ?_)
  rw [Xi24rr]; ring

private lemma Xi24_288_delta_isBigOq :
    IsBigOq (fun τ => 288 * Work.Kernels.DeltaFun τ
      - (Work.Kernels.E4Fun τ - Work.Kernels.E2Fun τ ^ 2) * Work.Kernels.E4Fun τ ^ 2) 2 := by
  have h1 : IsBigOq (fun τ => 288 * (Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ)) 2 :=
    DeltaFun_isBigOq.const_mul 288
  have h2 : IsBigOq (fun τ => -(Work.Kernels.E4Fun τ - Work.Kernels.E2Fun τ ^ 2
      - 288 * Work.Kernels.qParamFun τ) * Work.Kernels.E4Fun τ ^ 2) 2 :=
    delta1_two_term.neg.mul E4sq_bdd
  have h3 : IsBigOq (fun τ => -(288 * Work.Kernels.qParamFun τ
      * (Work.Kernels.E4Fun τ ^ 2 - 1))) 2 :=
    ((qParamFun_isBigOq.mul E4sq_minus_one).const_mul (-288)).congr (fun τ => by ring)
  refine ((h1.add h2).add h3).congr (fun τ => ?_)
  ring

/-- All the `z`-side cusp bounds needed for the `Ξ₂₄` estimate. -/
theorem Xi24_z_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ∧
      ‖5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2
          + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z‖
        ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 2 ∧
      ‖288 * Work.Kernels.DeltaFun z
          - (Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2) * Work.Kernels.E4Fun z ^ 2‖
        ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 2 ∧
      ‖Work.Kernels.E4Fun z‖ ≤ C ∧
      ‖Work.Kernels.jInvariantFun z‖ * ‖Work.Kernels.qParamFun z‖ ≤ C ∧
      ‖Work.Kernels.E2Fun z‖ ≤ C ∧
      ‖Work.Kernels.E6Fun z‖ ≤ C := by
  obtain ⟨Cd, hCd, hδ⟩ := delta1_isBigOq
  obtain ⟨Cr, hCr, hrr⟩ := Xi24rr_isBigOq
  obtain ⟨Ck, hCk, h288⟩ := Xi24_288_delta_isBigOq
  obtain ⟨C4, hC4, hE4⟩ := E4Fun_bdd
  obtain ⟨C2, hC2, hE2⟩ := E2Fun_bdd
  obtain ⟨C6, hC6, hE6⟩ := E6Fun_bdd
  obtain ⟨cj, hcj, hj⟩ := DeltaFun_lower
  simp only [pow_zero, mul_one] at hE4 hE2 hE6
  simp only [pow_one] at hδ
  have hp : (0:ℝ) ≤ C4 ^ 3 / cj := by positivity
  set CC : ℝ := C4 ^ 3 / cj + Cd + Cr + Ck + C4 + C2 + C6 + 1 with hCC
  have hCc4 : C4 ^ 3 / cj ≤ CC := by
    rw [hCC]; linarith [hp, hCd.le, hCr.le, hCk.le, hC4.le, hC2.le, hC6.le]
  have hCd' : Cd ≤ CC := by rw [hCC]; linarith [hp, hCr.le, hCk.le, hC4.le, hC2.le, hC6.le]
  have hCr' : Cr ≤ CC := by rw [hCC]; linarith [hp, hCd.le, hCk.le, hC4.le, hC2.le, hC6.le]
  have hCk' : Ck ≤ CC := by rw [hCC]; linarith [hp, hCd.le, hCr.le, hC4.le, hC2.le, hC6.le]
  have hC4' : C4 ≤ CC := by rw [hCC]; linarith [hp, hCd.le, hCr.le, hCk.le, hC2.le, hC6.le]
  have hC2' : C2 ≤ CC := by rw [hCC]; linarith [hp, hCd.le, hCr.le, hCk.le, hC4.le, hC6.le]
  have hC6' : C6 ≤ CC := by rw [hCC]; linarith [hp, hCd.le, hCr.le, hCk.le, hC4.le, hC2.le]
  refine ⟨CC, by rw [hCC]; positivity, fun z hz => ?_⟩
  have hqz : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hqpos : 0 < ‖Work.Kernels.qParamFun z‖ := norm_pos_iff.mpr (qParamFun_ne_zero' z)
  have hDl : cj * ‖Work.Kernels.qParamFun z‖ ≤ ‖Work.Kernels.DeltaFun z‖ := hj z hz
  have hDpos : 0 < ‖Work.Kernels.DeltaFun z‖ := lt_of_lt_of_le (mul_pos hcj hqpos) hDl
  have hE4z := hE4 z hz
  refine ⟨le_trans (hδ z hz) (mul_le_mul_of_nonneg_right hCd' hqz),
    le_trans (hrr z hz) (mul_le_mul_of_nonneg_right hCr' (pow_nonneg hqz 2)),
    le_trans (h288 z hz) (mul_le_mul_of_nonneg_right hCk' (pow_nonneg hqz 2)),
    le_trans hE4z hC4', ?_, le_trans (hE2 z hz) hC2', le_trans (hE6 z hz) hC6'⟩
  rw [show Work.Kernels.jInvariantFun z
      = Work.Kernels.E4Fun z ^ 3 / Work.Kernels.DeltaFun z from rfl, norm_div, norm_pow,
    div_mul_eq_mul_div, div_le_iff₀ hDpos]
  calc ‖Work.Kernels.E4Fun z‖ ^ 3 * ‖Work.Kernels.qParamFun z‖
      ≤ C4 ^ 3 * ‖Work.Kernels.qParamFun z‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hE4z 3) hqz
    _ = (C4 ^ 3 / cj) * (cj * ‖Work.Kernels.qParamFun z‖) := by field_simp
    _ ≤ (C4 ^ 3 / cj) * ‖Work.Kernels.DeltaFun z‖ := mul_le_mul_of_nonneg_left hDl hp
    _ ≤ CC * ‖Work.Kernels.DeltaFun z‖ := mul_le_mul_of_nonneg_right hCc4 (norm_nonneg _)

/-! ## The `σ`-side bound for the atom `A` -/

/-- On the cusp `{Im σ ≥ 1}`, the atom `σE₁₄(σ) + φ₂(σ)E₁₀(σ) - 2φ₀(σ)E₄(σ)³` vanishes to
first order in `q(σ)`. -/
theorem Xi24_A_sigma_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : UpperHalfPlane, 1 ≤ σ.im →
      ‖(σ : ℂ) * Work.Kernels.E14Fun σ + Work.Kernels.phi2 σ * Work.Kernels.E10Fun σ
          - 2 * (Work.Kernels.phi0 σ * Work.Kernels.E4Fun σ ^ 3)‖
        ≤ C * ‖(σ : ℂ)‖ * ‖Work.Kernels.qParamFun σ‖ := by
  obtain ⟨Cδ, hCδ, hδ⟩ := delta1_isBigOq
  obtain ⟨Cγ, hCγ, hγ⟩ := eps_isBigOq
  obtain ⟨Ce2, hCe2, he2⟩ := E2Fun_bdd
  obtain ⟨Ce4, hCe4, he4⟩ := E4Fun_bdd
  obtain ⟨Ce6, hCe6, he6⟩ := E6Fun_bdd
  simp only [pow_zero, mul_one] at he2 he4 he6
  simp only [pow_one] at hδ hγ
  set CB : ℝ := Ce6 * Cδ + 2 * Ce2 * Cγ with hCB
  refine ⟨Ce4 * (CB + (6 / Real.pi) * Cγ) + 1, by positivity, fun σ hσ => ?_⟩
  have hσ1 : (1:ℝ) ≤ ‖(σ : ℂ)‖ := le_trans hσ (Work.Kernels.im_le_coe_norm σ)
  have hq : (0:ℝ) ≤ ‖Work.Kernels.qParamFun σ‖ := norm_nonneg _
  have hkey : (σ : ℂ) * Work.Kernels.E14Fun σ + Work.Kernels.phi2 σ * Work.Kernels.E10Fun σ
        - 2 * (Work.Kernels.phi0 σ * Work.Kernels.E4Fun σ ^ 3)
      = Work.Kernels.E4Fun σ * ((σ : ℂ) * (Work.Kernels.E6Fun σ
            * (Work.Kernels.E4Fun σ - Work.Kernels.E2Fun σ ^ 2)
          - 2 * Work.Kernels.E2Fun σ
            * (Work.Kernels.E4Fun σ ^ 2 - Work.Kernels.E6Fun σ * Work.Kernels.E2Fun σ))
        + (6 * Complex.I / (Real.pi : ℂ))
          * (Work.Kernels.E4Fun σ ^ 2 - Work.Kernels.E6Fun σ * Work.Kernels.E2Fun σ)) := by
    simp only [Work.Kernels.E14Fun, Work.Kernels.E10Fun, Work.Kernels.phi2, Work.Kernels.phi0]
    ring
  have hβb : ‖Work.Kernels.E6Fun σ * (Work.Kernels.E4Fun σ - Work.Kernels.E2Fun σ ^ 2)
        - 2 * Work.Kernels.E2Fun σ * (Work.Kernels.E4Fun σ ^ 2
            - Work.Kernels.E6Fun σ * Work.Kernels.E2Fun σ)‖
      ≤ CB * ‖Work.Kernels.qParamFun σ‖ := by
    have h1 : ‖Work.Kernels.E6Fun σ * (Work.Kernels.E4Fun σ - Work.Kernels.E2Fun σ ^ 2)‖
        ≤ Ce6 * (Cδ * ‖Work.Kernels.qParamFun σ‖) := by
      rw [norm_mul]
      exact mul_le_mul (he6 σ hσ) (hδ σ hσ) (norm_nonneg _) hCe6.le
    have h2 : ‖2 * Work.Kernels.E2Fun σ * (Work.Kernels.E4Fun σ ^ 2
        - Work.Kernels.E6Fun σ * Work.Kernels.E2Fun σ)‖
        ≤ 2 * Ce2 * (Cγ * ‖Work.Kernels.qParamFun σ‖) := by
      rw [norm_mul]
      have h2c : ‖(2:ℂ) * Work.Kernels.E2Fun σ‖ ≤ 2 * Ce2 := by
        rw [norm_mul]
        have : ‖(2:ℂ)‖ = 2 := by norm_num
        rw [this]
        exact mul_le_mul_of_nonneg_left (he2 σ hσ) (by norm_num)
      exact mul_le_mul h2c (hγ σ hσ) (norm_nonneg _) (by positivity)
    calc ‖Work.Kernels.E6Fun σ * (Work.Kernels.E4Fun σ - Work.Kernels.E2Fun σ ^ 2)
          - 2 * Work.Kernels.E2Fun σ * (Work.Kernels.E4Fun σ ^ 2
              - Work.Kernels.E6Fun σ * Work.Kernels.E2Fun σ)‖
        ≤ ‖Work.Kernels.E6Fun σ * (Work.Kernels.E4Fun σ - Work.Kernels.E2Fun σ ^ 2)‖
          + ‖2 * Work.Kernels.E2Fun σ * (Work.Kernels.E4Fun σ ^ 2
              - Work.Kernels.E6Fun σ * Work.Kernels.E2Fun σ)‖ := norm_sub_le _ _
      _ ≤ Ce6 * (Cδ * ‖Work.Kernels.qParamFun σ‖)
          + 2 * Ce2 * (Cγ * ‖Work.Kernels.qParamFun σ‖) := add_le_add h1 h2
      _ = CB * ‖Work.Kernels.qParamFun σ‖ := by rw [hCB]; ring
  have h6π : ‖(6 * Complex.I / (Real.pi : ℂ))‖ = 6 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hkey, norm_mul]
  have hinner : ‖(σ : ℂ) * (Work.Kernels.E6Fun σ * (Work.Kernels.E4Fun σ - Work.Kernels.E2Fun σ ^ 2)
        - 2 * Work.Kernels.E2Fun σ * (Work.Kernels.E4Fun σ ^ 2
            - Work.Kernels.E6Fun σ * Work.Kernels.E2Fun σ))
      + (6 * Complex.I / (Real.pi : ℂ))
        * (Work.Kernels.E4Fun σ ^ 2 - Work.Kernels.E6Fun σ * Work.Kernels.E2Fun σ)‖
      ≤ ‖(σ : ℂ)‖ * (CB * ‖Work.Kernels.qParamFun σ‖)
        + (6 / Real.pi) * (Cγ * ‖Work.Kernels.qParamFun σ‖) := by
    have h1 : ‖(σ : ℂ) * (Work.Kernels.E6Fun σ * (Work.Kernels.E4Fun σ - Work.Kernels.E2Fun σ ^ 2)
        - 2 * Work.Kernels.E2Fun σ * (Work.Kernels.E4Fun σ ^ 2
            - Work.Kernels.E6Fun σ * Work.Kernels.E2Fun σ))‖
        ≤ ‖(σ : ℂ)‖ * (CB * ‖Work.Kernels.qParamFun σ‖) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hβb (norm_nonneg _)
    have h2 : ‖(6 * Complex.I / (Real.pi : ℂ))
        * (Work.Kernels.E4Fun σ ^ 2 - Work.Kernels.E6Fun σ * Work.Kernels.E2Fun σ)‖
        ≤ (6 / Real.pi) * (Cγ * ‖Work.Kernels.qParamFun σ‖) := by
      rw [norm_mul, h6π]
      exact mul_le_mul_of_nonneg_left (hγ σ hσ) (by positivity)
    calc _ ≤ ‖(σ : ℂ) * (Work.Kernels.E6Fun σ * (Work.Kernels.E4Fun σ - Work.Kernels.E2Fun σ ^ 2)
          - 2 * Work.Kernels.E2Fun σ * (Work.Kernels.E4Fun σ ^ 2
              - Work.Kernels.E6Fun σ * Work.Kernels.E2Fun σ))‖
        + ‖(6 * Complex.I / (Real.pi : ℂ))
          * (Work.Kernels.E4Fun σ ^ 2 - Work.Kernels.E6Fun σ * Work.Kernels.E2Fun σ)‖ :=
          norm_add_le _ _
      _ ≤ _ := add_le_add h1 h2
  calc ‖Work.Kernels.E4Fun σ‖ * ‖(σ : ℂ) * (Work.Kernels.E6Fun σ * (Work.Kernels.E4Fun σ - Work.Kernels.E2Fun σ ^ 2)
        - 2 * Work.Kernels.E2Fun σ * (Work.Kernels.E4Fun σ ^ 2
            - Work.Kernels.E6Fun σ * Work.Kernels.E2Fun σ))
      + (6 * Complex.I / (Real.pi : ℂ))
        * (Work.Kernels.E4Fun σ ^ 2 - Work.Kernels.E6Fun σ * Work.Kernels.E2Fun σ)‖
      ≤ Ce4 * (‖(σ : ℂ)‖ * (CB * ‖Work.Kernels.qParamFun σ‖)
          + (6 / Real.pi) * (Cγ * ‖Work.Kernels.qParamFun σ‖)) :=
        mul_le_mul (he4 σ hσ) hinner (by positivity) hCe4.le
    _ ≤ (Ce4 * (CB + (6 / Real.pi) * Cγ) + 1) * ‖(σ : ℂ)‖ * ‖Work.Kernels.qParamFun σ‖ := by
        have hCγ0 : 0 ≤ Cγ := hCγ.le
        have hCB0 : 0 ≤ CB := by rw [hCB]; positivity
        have h1 : Ce4 * (‖(σ : ℂ)‖ * (CB * ‖Work.Kernels.qParamFun σ‖)
            + (6 / Real.pi) * (Cγ * ‖Work.Kernels.qParamFun σ‖))
            ≤ Ce4 * ((CB + (6 / Real.pi) * Cγ) * (‖(σ : ℂ)‖ * ‖Work.Kernels.qParamFun σ‖)) := by
          apply mul_le_mul_of_nonneg_left _ hCe4.le
          have h2 : (6 / Real.pi) * (Cγ * ‖Work.Kernels.qParamFun σ‖)
              ≤ ‖(σ : ℂ)‖ * ((6 / Real.pi) * (Cγ * ‖Work.Kernels.qParamFun σ‖)) := by
            calc (6 / Real.pi) * (Cγ * ‖Work.Kernels.qParamFun σ‖)
                = 1 * ((6 / Real.pi) * (Cγ * ‖Work.Kernels.qParamFun σ‖)) := by ring
              _ ≤ ‖(σ : ℂ)‖ * ((6 / Real.pi) * (Cγ * ‖Work.Kernels.qParamFun σ‖)) :=
                  mul_le_mul_of_nonneg_right hσ1 (by positivity)
          nlinarith [h2, hσ1, hq, hCγ0, hCB0, norm_nonneg (σ:ℂ)]
        calc Ce4 * (‖(σ : ℂ)‖ * (CB * ‖Work.Kernels.qParamFun σ‖)
              + (6 / Real.pi) * (Cγ * ‖Work.Kernels.qParamFun σ‖))
            ≤ Ce4 * ((CB + (6 / Real.pi) * Cγ) * (‖(σ : ℂ)‖ * ‖Work.Kernels.qParamFun σ‖)) := h1
          _ = Ce4 * (CB + (6 / Real.pi) * Cγ) * (‖(σ : ℂ)‖ * ‖Work.Kernels.qParamFun σ‖) := by ring
          _ ≤ (Ce4 * (CB + (6 / Real.pi) * Cγ) + 1) * ‖(σ : ℂ)‖ * ‖Work.Kernels.qParamFun σ‖ := by
              have h4 : (0:ℝ) ≤ Ce4 * (CB + (6 / Real.pi) * Cγ) := by positivity
              nlinarith [mul_nonneg (le_trans zero_le_one hσ1) hq, h4]

/-! ## Slash relations and elementary norm facts -/

private lemma coe_ne_zero (t : ℍ) : (t : ℂ) ≠ 0 :=
  fun h => t.im_ne_zero (by rw [← UpperHalfPlane.coe_im t, h]; simp)

private lemma norm_coe_inv_le_scale (τ : ℍ) : ‖(τ : ℂ)‖⁻¹ ≤ Work.Kernels.scale τ := by
  have h1 : (0:ℝ) < τ.im := τ.im_pos
  have hnorm : (0:ℝ) < ‖(τ:ℂ)‖ := norm_pos_iff.mpr (coe_ne_zero τ)
  have h2 : ‖(τ:ℂ)‖⁻¹ ≤ (τ.im)⁻¹ := by
    rw [inv_le_inv₀ hnorm h1]
    exact Work.Kernels.im_le_coe_norm τ
  exact le_trans h2 (Work.Kernels.inv_im_le_scale τ)

private lemma scale_pow_nonneg (τ : ℍ) (k : ℕ) : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ k :=
  pow_nonneg (Work.Kernels.scale_pos τ).le k

private lemma coe_norm_pow_inv_le_scale (τ : ℍ) (k : ℕ) :
    ((‖(τ : ℂ)‖ ^ k)⁻¹) ≤ (Work.Kernels.scale τ) ^ k := by
  rw [← inv_pow]
  exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) (norm_coe_inv_le_scale τ) k

private lemma E4Fun_S_smul (τ : ℍ) :
    Work.Kernels.E4Fun (ModularGroup.S • τ) = (τ : ℂ) ^ 4 * Work.Kernels.E4Fun τ := by
  have h := Work.Kernels.KernelFacts.smul_of_slash_inv Work.Kernels.KernelFacts.E4Fun_S_slash τ
  rwa [show (τ : ℂ) ^ (4 : ℤ) = (τ : ℂ) ^ (4 : ℕ) by norm_num] at h

private lemma E6Fun_S_smul (τ : ℍ) :
    Work.Kernels.E6Fun (ModularGroup.S • τ) = (τ : ℂ) ^ 6 * Work.Kernels.E6Fun τ := by
  have h := Work.Kernels.KernelFacts.smul_of_slash_inv Work.Kernels.KernelFacts.E6Fun_S_slash τ
  rwa [show (τ : ℂ) ^ (6 : ℤ) = (τ : ℂ) ^ (6 : ℕ) by norm_num] at h

private lemma E10Fun_S_smul (τ : ℍ) :
    Work.Kernels.E10Fun (ModularGroup.S • τ) = (τ : ℂ) ^ 10 * Work.Kernels.E10Fun τ := by
  have h := Work.Kernels.KernelFacts.smul_of_slash_inv Work.Kernels.KernelFacts.E10Fun_S_slash τ
  rwa [show (τ : ℂ) ^ (10 : ℤ) = (τ : ℂ) ^ (10 : ℕ) by norm_num] at h

private lemma E14Fun_S_smul (τ : ℍ) :
    Work.Kernels.E14Fun (ModularGroup.S • τ) = (τ : ℂ) ^ 14 * Work.Kernels.E14Fun τ := by
  have h := Work.Kernels.KernelFacts.smul_of_slash_inv Work.Kernels.KernelFacts.E14Fun_S_slash τ
  rwa [show (τ : ℂ) ^ (14 : ℤ) = (τ : ℂ) ^ (14 : ℕ) by norm_num] at h

private lemma DeltaFun_S_smul (τ : ℍ) :
    Work.Kernels.DeltaFun (ModularGroup.S • τ) = (τ : ℂ) ^ 12 * Work.Kernels.DeltaFun τ := by
  have h := Work.Kernels.KernelFacts.smul_of_slash_inv Work.Kernels.KernelFacts.DeltaFun_S_slash τ
  rwa [show (τ : ℂ) ^ (12 : ℤ) = (τ : ℂ) ^ (12 : ℕ) by norm_num] at h

private lemma phi0_S_smul (τ : ℍ) :
    Work.Kernels.phi0 (ModularGroup.S • τ) = - Work.Kernels.phi0 τ := by
  have h := Work.Kernels.KernelFacts.phiVec_S_smul τ 1
  simpa [Work.Kernels.phiVec] using h

private lemma phi2_S_smul (τ : ℍ) :
    Work.Kernels.phi2 (ModularGroup.S • τ) = - (τ : ℂ) ^ 2 * Work.Kernels.phi2 τ := by
  have h := Work.Kernels.KernelFacts.phiVec_S_smul τ 2
  have h' : Work.Kernels.phi2 (ModularGroup.S • τ) = - (τ : ℂ) ^ (2:ℤ) * Work.Kernels.phi2 τ := by
    simpa [Work.Kernels.phiVec] using h
  rwa [show (τ : ℂ) ^ (2 : ℤ) = (τ : ℂ) ^ (2 : ℕ) by norm_num] at h'

private lemma jInvariantFun_S_smul (τ : ℍ) :
    Work.Kernels.jInvariantFun (ModularGroup.S • τ) = Work.Kernels.jInvariantFun τ :=
  Work.Kernels.KernelFacts.jInvariantFun_S_smul τ

private lemma S_smul_norm (τ : ℍ) :
    ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ = ‖(τ : ℂ)‖⁻¹ := by
  rw [Work.Kernels.S_smul_coe τ, norm_neg, norm_inv]

private lemma phi0_bound {σ : ℍ} (hσ : 1 ≤ σ.im) :
    ‖Work.Kernels.phi0 σ‖ ≤ (‖Work.Kernels.E2Fun σ‖ + 3 / Real.pi) * ‖(σ : ℂ)‖ := by
  have h0 : Work.Kernels.phi0 σ
      = (σ : ℂ) * Work.Kernels.E2Fun σ - 3 * Complex.I / (Real.pi : ℂ) := rfl
  have hσ1 : (1:ℝ) ≤ ‖(σ : ℂ)‖ := le_trans hσ (Work.Kernels.im_le_coe_norm σ)
  rw [h0]
  calc ‖(σ : ℂ) * Work.Kernels.E2Fun σ - 3 * Complex.I / (Real.pi : ℂ)‖
      ≤ ‖(σ : ℂ) * Work.Kernels.E2Fun σ‖ + ‖3 * Complex.I / (Real.pi : ℂ)‖ := norm_sub_le _ _
    _ ≤ ‖(σ : ℂ)‖ * ‖Work.Kernels.E2Fun σ‖ + 3 / Real.pi := by
        have ha : ‖(σ : ℂ) * Work.Kernels.E2Fun σ‖ ≤ ‖(σ : ℂ)‖ * ‖Work.Kernels.E2Fun σ‖ :=
          le_of_eq (norm_mul _ _)
        have hb : ‖(3 * Complex.I / (Real.pi : ℂ))‖ = 3 / Real.pi := by
          rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        rw [hb]; linarith
    _ ≤ (‖Work.Kernels.E2Fun σ‖ + 3 / Real.pi) * ‖(σ : ℂ)‖ := by
        have h3 : (3 / Real.pi) * 1 ≤ (3 / Real.pi) * ‖(σ : ℂ)‖ :=
          mul_le_mul_of_nonneg_left hσ1 (by positivity)
        rw [mul_one] at h3
        nlinarith [h3]

private lemma phi2_bound {σ : ℍ} (hσ : 1 ≤ σ.im) :
    ‖Work.Kernels.phi2 σ‖
      ≤ (‖Work.Kernels.E2Fun σ‖ ^ 2 + (6 / Real.pi) * ‖Work.Kernels.E2Fun σ‖) * ‖(σ : ℂ)‖ := by
  have hσ1 : (1:ℝ) ≤ ‖(σ : ℂ)‖ := le_trans hσ (Work.Kernels.im_le_coe_norm σ)
  have h2 : Work.Kernels.phi2 σ
      = (σ : ℂ) * Work.Kernels.E2Fun σ ^ 2
        - (6 * Complex.I / (Real.pi : ℂ)) * Work.Kernels.E2Fun σ := rfl
  rw [h2]
  have h6π : ‖(6 * Complex.I / (Real.pi : ℂ))‖ = 6 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc ‖(σ : ℂ) * Work.Kernels.E2Fun σ ^ 2
        - (6 * Complex.I / (Real.pi : ℂ)) * Work.Kernels.E2Fun σ‖
      ≤ ‖(σ : ℂ) * Work.Kernels.E2Fun σ ^ 2‖
        + ‖(6 * Complex.I / (Real.pi : ℂ)) * Work.Kernels.E2Fun σ‖ := norm_sub_le _ _
    _ ≤ ‖(σ : ℂ)‖ * ‖Work.Kernels.E2Fun σ‖ ^ 2
        + (6 / Real.pi) * ‖Work.Kernels.E2Fun σ‖ := by
        have ha : ‖(σ : ℂ) * Work.Kernels.E2Fun σ ^ 2‖
            ≤ ‖(σ : ℂ)‖ * ‖Work.Kernels.E2Fun σ‖ ^ 2 := le_of_eq (by rw [norm_mul, norm_pow])
        have hb : ‖(6 * Complex.I / (Real.pi : ℂ)) * Work.Kernels.E2Fun σ‖
            ≤ (6 / Real.pi) * ‖Work.Kernels.E2Fun σ‖ := le_of_eq (by rw [norm_mul, h6π])
        linarith
    _ ≤ (‖Work.Kernels.E2Fun σ‖ ^ 2 + (6 / Real.pi) * ‖Work.Kernels.E2Fun σ‖) * ‖(σ : ℂ)‖ := by
        have h3 : ((6 / Real.pi) * ‖Work.Kernels.E2Fun σ‖) * 1
            ≤ ((6 / Real.pi) * ‖Work.Kernels.E2Fun σ‖) * ‖(σ : ℂ)‖ :=
          mul_le_mul_of_nonneg_left hσ1 (by positivity)
        rw [mul_one] at h3
        nlinarith [h3]

/-! ## The `τ`-side atom bounds -/

/-- **The `τ`-side atom bounds.**  On the region `Im(S·τ) ≥ 3/2` all the atoms are bounded by
powers of `scale τ`, the `q(S·τ)`-vanishing ones carrying an explicit `‖q(S·τ)‖`. -/
private lemma Xi24_r0_tau_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, (3 / 2 : ℝ) ≤ (ModularGroup.S • τ).im →
      ‖(τ : ℂ) * Work.Kernels.E14Fun τ‖ ≤ C * (Work.Kernels.scale τ) ^ 13 := by
  obtain ⟨Ce4, hCe4, he4⟩ := E4Fun_bdd
  obtain ⟨Ce6, hCe6, he6⟩ := E6Fun_bdd
  simp only [pow_zero, mul_one] at he4 he6
  have hCe4pos : (0:ℝ) < Ce4 := hCe4
  have hCe6pos : (0:ℝ) < Ce6 := hCe6
  refine ⟨Ce4 ^ 2 * Ce6, by positivity, fun τ hτ => ?_⟩
  have hσ1 : (1:ℝ) ≤ (ModularGroup.S • τ).im := by linarith
  have hSreal : (0:ℝ) < ‖(τ : ℂ)‖ := norm_pos_iff.mpr (coe_ne_zero τ)
  have hE14 : ‖Work.Kernels.E14Fun (ModularGroup.S • τ)‖ ≤ Ce4 ^ 2 * Ce6 := by
    have h14 : Work.Kernels.E14Fun (ModularGroup.S • τ)
        = Work.Kernels.E4Fun (ModularGroup.S • τ) ^ 2
          * Work.Kernels.E6Fun (ModularGroup.S • τ) := rfl
    rw [h14, norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (he4 _ hσ1) 2) (he6 _ hσ1)
      (norm_nonneg _) (by positivity)
  have h13inv : (‖(τ : ℂ)‖⁻¹) ^ 13 ≤ (Work.Kernels.scale τ) ^ 13 :=
    pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) (norm_coe_inv_le_scale τ) 13
  have hkey : ‖(τ : ℂ) * Work.Kernels.E14Fun τ‖
      = ‖Work.Kernels.E14Fun (ModularGroup.S • τ)‖ * (‖(τ : ℂ)‖⁻¹) ^ 13 := by
    have hR : ‖(τ : ℂ) ^ 14 * Work.Kernels.E14Fun τ‖
        = ‖(τ : ℂ)‖ ^ 14 * ‖Work.Kernels.E14Fun τ‖ := by rw [norm_mul, norm_pow]
    rw [E14Fun_S_smul τ, hR, norm_mul]
    field_simp
  rw [hkey]
  calc ‖Work.Kernels.E14Fun (ModularGroup.S • τ)‖ * (‖(τ : ℂ)‖⁻¹) ^ 13
      ≤ (Ce4 ^ 2 * Ce6) * (Work.Kernels.scale τ) ^ 13 :=
        mul_le_mul hE14 h13inv (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) 13) (by positivity)
    _ = Ce4 ^ 2 * Ce6 * (Work.Kernels.scale τ) ^ 13 := by ring

private lemma Xi24_r2_tau_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, (3 / 2 : ℝ) ≤ (ModularGroup.S • τ).im →
      ‖Work.Kernels.phi2 τ * Work.Kernels.E10Fun τ‖ ≤ C * (Work.Kernels.scale τ) ^ 13 := by
  obtain ⟨Ce2, hCe2, he2⟩ := E2Fun_bdd
  obtain ⟨Ce4, hCe4, he4⟩ := E4Fun_bdd
  obtain ⟨Ce6, hCe6, he6⟩ := E6Fun_bdd
  simp only [pow_zero, mul_one] at he2 he4 he6
  have hCe2pos : (0:ℝ) < Ce2 := hCe2
  have hCe4pos : (0:ℝ) < Ce4 := hCe4
  have hCe6pos : (0:ℝ) < Ce6 := hCe6
  refine ⟨(Ce2 ^ 2 + (6 / Real.pi) * Ce2) * Ce4 * Ce6, by positivity, fun τ hτ => ?_⟩
  have hσ1 : (1:ℝ) ≤ (ModularGroup.S • τ).im := by linarith
  have hSreal : (0:ℝ) < ‖(τ : ℂ)‖ := norm_pos_iff.mpr (coe_ne_zero τ)
  have hσle : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ≤ Work.Kernels.scale τ :=
    le_trans (le_of_eq (S_smul_norm τ)) (norm_coe_inv_le_scale τ)
  have hφ2 : ‖Work.Kernels.phi2 (ModularGroup.S • τ)‖
      ≤ (Ce2 ^ 2 + (6 / Real.pi) * Ce2) * ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ := by
    refine le_trans (phi2_bound hσ1) ?_
    have hσnn : (0:ℝ) ≤ ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ := norm_nonneg _
    have h19 : ‖Work.Kernels.E2Fun (ModularGroup.S • τ)‖ ^ 2 ≤ Ce2 ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (he2 _ hσ1) 2
    have h20 : (6 / Real.pi) * ‖Work.Kernels.E2Fun (ModularGroup.S • τ)‖ ≤ (6 / Real.pi) * Ce2 :=
      mul_le_mul_of_nonneg_left (he2 _ hσ1) (by positivity)
    nlinarith [hσnn, h19, h20, he2 _ hσ1]
  have hE10 : ‖Work.Kernels.E10Fun (ModularGroup.S • τ)‖ ≤ Ce4 * Ce6 := by
    have h10 : Work.Kernels.E10Fun (ModularGroup.S • τ)
        = Work.Kernels.E4Fun (ModularGroup.S • τ) * Work.Kernels.E6Fun (ModularGroup.S • τ) := rfl
    rw [h10, norm_mul]
    exact mul_le_mul (he4 _ hσ1) (he6 _ hσ1) (norm_nonneg _) hCe4.le
  have hphi2τ : ‖Work.Kernels.phi2 τ‖
      = ‖Work.Kernels.phi2 (ModularGroup.S • τ)‖ * (‖(τ : ℂ)‖⁻¹) ^ 2 := by
    have hR : ‖(τ : ℂ) ^ 2 * Work.Kernels.phi2 τ‖
        = ‖(τ : ℂ)‖ ^ 2 * ‖Work.Kernels.phi2 τ‖ := by rw [norm_mul, norm_pow]
    rw [phi2_S_smul τ, neg_mul, norm_neg, hR]
    field_simp
  have hE10τ : ‖Work.Kernels.E10Fun τ‖
      = ‖Work.Kernels.E10Fun (ModularGroup.S • τ)‖ * (‖(τ : ℂ)‖⁻¹) ^ 10 := by
    have hR : ‖(τ : ℂ) ^ 10 * Work.Kernels.E10Fun τ‖
        = ‖(τ : ℂ)‖ ^ 10 * ‖Work.Kernels.E10Fun τ‖ := by rw [norm_mul, norm_pow]
    rw [E10Fun_S_smul τ, hR]
    field_simp
  have h12inv : (‖(τ : ℂ)‖⁻¹) ^ 12 ≤ (Work.Kernels.scale τ) ^ 12 :=
    pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) (norm_coe_inv_le_scale τ) 12
  rw [norm_mul, hphi2τ, hE10τ]
  have h5 : ‖Work.Kernels.phi2 (ModularGroup.S • τ)‖
        * ‖Work.Kernels.E10Fun (ModularGroup.S • τ)‖
      ≤ ((Ce2 ^ 2 + (6 / Real.pi) * Ce2) * ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖)
        * (Ce4 * Ce6) :=
    mul_le_mul hφ2 hE10 (norm_nonneg _) (by positivity)
  calc ‖Work.Kernels.phi2 (ModularGroup.S • τ)‖ * (‖(τ : ℂ)‖⁻¹) ^ 2
        * (‖Work.Kernels.E10Fun (ModularGroup.S • τ)‖ * (‖(τ : ℂ)‖⁻¹) ^ 10)
      = (‖(τ : ℂ)‖⁻¹) ^ 12
        * (‖Work.Kernels.phi2 (ModularGroup.S • τ)‖
          * ‖Work.Kernels.E10Fun (ModularGroup.S • τ)‖) := by ring
    _ ≤ (Work.Kernels.scale τ) ^ 12
          * (((Ce2 ^ 2 + (6 / Real.pi) * Ce2) * ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖)
            * (Ce4 * Ce6)) :=
        mul_le_mul h12inv h5 (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (scale_pow_nonneg τ 12)
    _ ≤ (Work.Kernels.scale τ) ^ 12
          * (((Ce2 ^ 2 + (6 / Real.pi) * Ce2) * (Ce4 * Ce6)) * Work.Kernels.scale τ) := by
        apply mul_le_mul_of_nonneg_left _ (scale_pow_nonneg τ 12)
        calc ((Ce2 ^ 2 + (6 / Real.pi) * Ce2) * ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖)
              * (Ce4 * Ce6)
            ≤ ((Ce2 ^ 2 + (6 / Real.pi) * Ce2) * Work.Kernels.scale τ) * (Ce4 * Ce6) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hσle (by positivity))
                (mul_nonneg hCe4.le hCe6.le)
          _ = ((Ce2 ^ 2 + (6 / Real.pi) * Ce2) * (Ce4 * Ce6)) * Work.Kernels.scale τ := by ring
    _ = ((Ce2 ^ 2 + (6 / Real.pi) * Ce2) * Ce4 * Ce6) * (Work.Kernels.scale τ) ^ 13 := by
        ring

private lemma Xi24_R0_tau_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, (3 / 2 : ℝ) ≤ (ModularGroup.S • τ).im →
      ‖Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ ^ 3‖ ≤ C * (Work.Kernels.scale τ) ^ 13 := by
  obtain ⟨Ce2, hCe2, he2⟩ := E2Fun_bdd
  obtain ⟨Ce4, hCe4, he4⟩ := E4Fun_bdd
  simp only [pow_zero, mul_one] at he2 he4
  have hCe2pos : (0:ℝ) < Ce2 := hCe2
  have hCe4pos : (0:ℝ) < Ce4 := hCe4
  refine ⟨(Ce2 + 3 / Real.pi) * Ce4 ^ 3, by positivity, fun τ hτ => ?_⟩
  have hσ1 : (1:ℝ) ≤ (ModularGroup.S • τ).im := by linarith
  have hSreal : (0:ℝ) < ‖(τ : ℂ)‖ := norm_pos_iff.mpr (coe_ne_zero τ)
  have hσle : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ≤ Work.Kernels.scale τ :=
    le_trans (le_of_eq (S_smul_norm τ)) (norm_coe_inv_le_scale τ)
  have hφ0 : ‖Work.Kernels.phi0 (ModularGroup.S • τ)‖
      ≤ (Ce2 + 3 / Real.pi) * ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ := by
    refine le_trans (phi0_bound hσ1) ?_
    have hσnn : (0:ℝ) ≤ ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ := norm_nonneg _
    nlinarith [he2 _ hσ1, hσnn]
  have hE4cube : ‖Work.Kernels.E4Fun (ModularGroup.S • τ)‖ ^ 3 ≤ Ce4 ^ 3 :=
    pow_le_pow_left₀ (norm_nonneg _) (he4 _ hσ1) 3
  have hE4τ : ‖Work.Kernels.E4Fun τ‖
      = ‖Work.Kernels.E4Fun (ModularGroup.S • τ)‖ * (‖(τ : ℂ)‖⁻¹) ^ 4 := by
    have hR : ‖(τ : ℂ) ^ 4 * Work.Kernels.E4Fun τ‖
        = ‖(τ : ℂ)‖ ^ 4 * ‖Work.Kernels.E4Fun τ‖ := by rw [norm_mul, norm_pow]
    rw [E4Fun_S_smul τ, hR]
    field_simp
  have hphi0τ : ‖Work.Kernels.phi0 τ‖ = ‖Work.Kernels.phi0 (ModularGroup.S • τ)‖ := by
    rw [phi0_S_smul τ, norm_neg]
  have h12inv : (‖(τ : ℂ)‖⁻¹) ^ 12 ≤ (Work.Kernels.scale τ) ^ 12 :=
    pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) (norm_coe_inv_le_scale τ) 12
  rw [norm_mul, norm_pow, hE4τ, hphi0τ]
  have h5 : ‖Work.Kernels.phi0 (ModularGroup.S • τ)‖
        * ‖Work.Kernels.E4Fun (ModularGroup.S • τ)‖ ^ 3
      ≤ ((Ce2 + 3 / Real.pi) * ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖) * Ce4 ^ 3 :=
    mul_le_mul hφ0 hE4cube (pow_nonneg (norm_nonneg _) 3) (by positivity)
  calc ‖Work.Kernels.phi0 (ModularGroup.S • τ)‖
        * (‖Work.Kernels.E4Fun (ModularGroup.S • τ)‖ * (‖(τ : ℂ)‖⁻¹) ^ 4) ^ 3
      = (‖(τ : ℂ)‖⁻¹) ^ 12
        * (‖Work.Kernels.phi0 (ModularGroup.S • τ)‖
          * ‖Work.Kernels.E4Fun (ModularGroup.S • τ)‖ ^ 3) := by ring
    _ ≤ (Work.Kernels.scale τ) ^ 12
          * (((Ce2 + 3 / Real.pi) * ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖) * Ce4 ^ 3) :=
        mul_le_mul h12inv h5 (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) 3))
          (scale_pow_nonneg τ 12)
    _ ≤ (Work.Kernels.scale τ) ^ 12
          * (((Ce2 + 3 / Real.pi) * Ce4 ^ 3) * Work.Kernels.scale τ) := by
        apply mul_le_mul_of_nonneg_left _ (scale_pow_nonneg τ 12)
        calc ((Ce2 + 3 / Real.pi) * ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖) * Ce4 ^ 3
            ≤ ((Ce2 + 3 / Real.pi) * Work.Kernels.scale τ) * Ce4 ^ 3 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hσle (by positivity))
                (pow_nonneg hCe4.le 3)
          _ = ((Ce2 + 3 / Real.pi) * Ce4 ^ 3) * Work.Kernels.scale τ := by ring
    _ = ((Ce2 + 3 / Real.pi) * Ce4 ^ 3) * (Work.Kernels.scale τ) ^ 13 := by ring

private lemma Xi24_r1_tau_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, (3 / 2 : ℝ) ≤ (ModularGroup.S • τ).im →
      ‖Work.Kernels.phi0 τ * Work.Kernels.DeltaFun τ‖
        ≤ C * (Work.Kernels.scale τ) ^ 13
          * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ := by
  obtain ⟨CΔ, hCΔ, hΔ⟩ := DeltaFun_isBigOq_one
  obtain ⟨Ce2, hCe2, he2⟩ := E2Fun_bdd
  simp only [pow_zero, mul_one] at he2
  simp only [pow_one] at hΔ
  have hCe2pos : (0:ℝ) < Ce2 := hCe2
  refine ⟨(Ce2 + 3 / Real.pi) * CΔ, by positivity, fun τ hτ => ?_⟩
  have hσ1 : (1:ℝ) ≤ (ModularGroup.S • τ).im := by linarith
  have hSreal : (0:ℝ) < ‖(τ : ℂ)‖ := norm_pos_iff.mpr (coe_ne_zero τ)
  have hσle : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ≤ Work.Kernels.scale τ :=
    le_trans (le_of_eq (S_smul_norm τ)) (norm_coe_inv_le_scale τ)
  have hφ0 : ‖Work.Kernels.phi0 (ModularGroup.S • τ)‖
      ≤ (Ce2 + 3 / Real.pi) * ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ := by
    refine le_trans (phi0_bound hσ1) ?_
    have hσnn : (0:ℝ) ≤ ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ := norm_nonneg _
    nlinarith [he2 _ hσ1, hσnn]
  have hΔc : ‖Work.Kernels.DeltaFun (ModularGroup.S • τ)‖
      ≤ CΔ * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ := hΔ _ hσ1
  have hΔτ : ‖Work.Kernels.DeltaFun τ‖
      = ‖Work.Kernels.DeltaFun (ModularGroup.S • τ)‖ * (‖(τ : ℂ)‖⁻¹) ^ 12 := by
    have hR : ‖(τ : ℂ) ^ 12 * Work.Kernels.DeltaFun τ‖
        = ‖(τ : ℂ)‖ ^ 12 * ‖Work.Kernels.DeltaFun τ‖ := by rw [norm_mul, norm_pow]
    rw [DeltaFun_S_smul τ, hR]
    field_simp
  have hphi0τ : ‖Work.Kernels.phi0 τ‖ = ‖Work.Kernels.phi0 (ModularGroup.S • τ)‖ := by
    rw [phi0_S_smul τ, norm_neg]
  have h12inv : (‖(τ : ℂ)‖⁻¹) ^ 12 ≤ (Work.Kernels.scale τ) ^ 12 :=
    pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) (norm_coe_inv_le_scale τ) 12
  rw [norm_mul, hΔτ, hphi0τ]
  have h5 : ‖Work.Kernels.phi0 (ModularGroup.S • τ)‖
        * ‖Work.Kernels.DeltaFun (ModularGroup.S • τ)‖
      ≤ ((Ce2 + 3 / Real.pi) * ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖)
        * (CΔ * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖) :=
    mul_le_mul hφ0 hΔc (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))
  calc ‖Work.Kernels.phi0 (ModularGroup.S • τ)‖
        * (‖Work.Kernels.DeltaFun (ModularGroup.S • τ)‖ * (‖(τ : ℂ)‖⁻¹) ^ 12)
      = (‖(τ : ℂ)‖⁻¹) ^ 12
        * (‖Work.Kernels.phi0 (ModularGroup.S • τ)‖
          * ‖Work.Kernels.DeltaFun (ModularGroup.S • τ)‖) := by ring
    _ ≤ (Work.Kernels.scale τ) ^ 12
          * (((Ce2 + 3 / Real.pi) * ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖)
            * (CΔ * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖)) :=
        mul_le_mul h12inv h5 (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (scale_pow_nonneg τ 12)
    _ ≤ (Work.Kernels.scale τ) ^ 12 * (((Ce2 + 3 / Real.pi) * CΔ) * Work.Kernels.scale τ)
          * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ := by
        rw [show (Work.Kernels.scale τ) ^ 12
              * (((Ce2 + 3 / Real.pi) * CΔ) * Work.Kernels.scale τ)
              * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖
            = (Work.Kernels.scale τ) ^ 12
              * ((((Ce2 + 3 / Real.pi) * CΔ) * Work.Kernels.scale τ)
                * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖) by ring]
        apply mul_le_mul_of_nonneg_left _ (scale_pow_nonneg τ 12)
        calc ((Ce2 + 3 / Real.pi) * ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖)
              * (CΔ * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖)
            = (((Ce2 + 3 / Real.pi) * CΔ) * ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖)
              * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ := by ring
          _ ≤ (((Ce2 + 3 / Real.pi) * CΔ) * Work.Kernels.scale τ)
              * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hσle (by positivity))
                (norm_nonneg _)
    _ = (Ce2 + 3 / Real.pi) * CΔ * (Work.Kernels.scale τ) ^ 13
          * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ := by ring

private lemma Xi24_jTau_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, (3 / 2 : ℝ) ≤ (ModularGroup.S • τ).im →
      ‖Work.Kernels.jInvariantFun τ‖ * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ ≤ C := by
  obtain ⟨Ce4, hCe4, he4⟩ := E4Fun_bdd
  obtain ⟨cj, hcj, hj⟩ := DeltaFun_lower
  simp only [pow_zero, mul_one] at he4
  have hCe4pos : (0:ℝ) < Ce4 := hCe4
  refine ⟨Ce4 ^ 3 / cj, by positivity, fun τ hτ => ?_⟩
  have hσ1 : (1:ℝ) ≤ (ModularGroup.S • τ).im := by linarith
  have hSreal : (0:ℝ) < ‖(τ : ℂ)‖ := norm_pos_iff.mpr (coe_ne_zero τ)
  have hjS : Work.Kernels.jInvariantFun τ
      = Work.Kernels.jInvariantFun (ModularGroup.S • τ) := (jInvariantFun_S_smul τ).symm
  rw [hjS]
  have hqpos : 0 < ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ :=
    norm_pos_iff.mpr (qParamFun_ne_zero' _)
  have hDl : cj * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖
      ≤ ‖Work.Kernels.DeltaFun (ModularGroup.S • τ)‖ := hj _ hσ1
  have hDpos : 0 < ‖Work.Kernels.DeltaFun (ModularGroup.S • τ)‖ :=
    lt_of_lt_of_le (mul_pos hcj hqpos) hDl
  rw [show Work.Kernels.jInvariantFun (ModularGroup.S • τ)
      = Work.Kernels.E4Fun (ModularGroup.S • τ) ^ 3
        / Work.Kernels.DeltaFun (ModularGroup.S • τ) from rfl, norm_div, norm_pow,
    div_mul_eq_mul_div, div_le_iff₀ hDpos]
  calc ‖Work.Kernels.E4Fun (ModularGroup.S • τ)‖ ^ 3
        * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖
      ≤ Ce4 ^ 3 * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (he4 _ hσ1) 3) (norm_nonneg _)
    _ = (Ce4 ^ 3 / cj) * (cj * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖) := by field_simp
    _ ≤ (Ce4 ^ 3 / cj) * ‖Work.Kernels.DeltaFun (ModularGroup.S • τ)‖ :=
        mul_le_mul_of_nonneg_left hDl (by positivity)
    _ = Ce4 ^ 3 / cj * ‖Work.Kernels.DeltaFun (ModularGroup.S • τ)‖ := by ring

/-- **The `τ`-side atom bounds.**  On the region `Im(S·τ) ≥ 3/2` all the atoms are bounded by
powers of `scale τ`, the `q(S·τ)`-vanishing ones carrying an explicit `‖q(S·τ)‖`. -/
theorem Xi24_atoms_tau_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, (3 / 2 : ℝ) ≤ (ModularGroup.S • τ).im →
      ‖(τ : ℂ) * Work.Kernels.E14Fun τ‖ ≤ C * (Work.Kernels.scale τ) ^ (13 : ℕ) ∧
      ‖Work.Kernels.phi2 τ * Work.Kernels.E10Fun τ‖ ≤ C * (Work.Kernels.scale τ) ^ (13 : ℕ) ∧
      ‖Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ ^ 3‖ ≤ C * (Work.Kernels.scale τ) ^ (13 : ℕ) ∧
      ‖Work.Kernels.phi0 τ * Work.Kernels.DeltaFun τ‖
        ≤ C * (Work.Kernels.scale τ) ^ (13 : ℕ)
          * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ ∧
      ‖Work.Kernels.jInvariantFun τ‖ * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ ≤ C := by
  obtain ⟨C0, hC0, h0⟩ := Xi24_r0_tau_bound
  obtain ⟨C2, hC2, h2⟩ := Xi24_r2_tau_bound
  obtain ⟨CR, hCR, hR⟩ := Xi24_R0_tau_bound
  obtain ⟨C1, hC1, h1⟩ := Xi24_r1_tau_bound
  obtain ⟨Cj, hCj, hj⟩ := Xi24_jTau_bound
  refine ⟨C0 + C2 + CR + C1 + Cj + 1, by positivity, fun τ hτ => ?_⟩
  have hspow : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ 13 := scale_pow_nonneg τ 13
  have e0 : C0 ≤ C0 + C2 + CR + C1 + Cj + 1 := by linarith [hC2.le, hCR.le, hC1.le, hCj.le]
  have e2 : C2 ≤ C0 + C2 + CR + C1 + Cj + 1 := by linarith [hC0.le, hCR.le, hC1.le, hCj.le]
  have eR : CR ≤ C0 + C2 + CR + C1 + Cj + 1 := by linarith [hC0.le, hC2.le, hC1.le, hCj.le]
  have e1 : C1 ≤ C0 + C2 + CR + C1 + Cj + 1 := by linarith [hC0.le, hC2.le, hCR.le, hCj.le]
  have ej : Cj ≤ C0 + C2 + CR + C1 + Cj + 1 := by linarith [hC0.le, hC2.le, hCR.le, hC1.le]
  exact ⟨le_trans (h0 τ hτ) (mul_le_mul_of_nonneg_right e0 hspow),
    le_trans (h2 τ hτ) (mul_le_mul_of_nonneg_right e2 hspow),
    le_trans (hR τ hτ) (mul_le_mul_of_nonneg_right eR hspow),
    le_trans (h1 τ hτ)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e1 hspow) (norm_nonneg _)),
    le_trans (hj τ hτ) ej⟩

/-- **The `τ`-side bound for the atom `A = r0 + r2 - 2R0`.** -/
theorem Xi24_A_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, (3 / 2 : ℝ) ≤ (ModularGroup.S • τ).im →
      ‖Xi24r0 τ + Xi24r2 τ - 2 * Xi24R0 τ‖
        ≤ C * (Work.Kernels.scale τ) ^ 13
            * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ := by
  obtain ⟨CA, hCA, hA⟩ := Xi24_A_sigma_bound
  refine ⟨CA, hCA, fun τ hτ => ?_⟩
  have hσ1 : (1:ℝ) ≤ (ModularGroup.S • τ).im := by linarith
  have hσnorm : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ = ‖(τ : ℂ)‖⁻¹ := S_smul_norm τ
  have hσle : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ≤ Work.Kernels.scale τ :=
    le_trans (le_of_eq hσnorm) (norm_coe_inv_le_scale τ)
  have hAeq : Xi24r0 τ + Xi24r2 τ - 2 * Xi24R0 τ
      = - ((τ : ℂ) ^ (12 : ℤ))⁻¹
          * ((((ModularGroup.S • τ : ℍ)) : ℂ) * Work.Kernels.E14Fun (ModularGroup.S • τ)
              + Work.Kernels.phi2 (ModularGroup.S • τ) * Work.Kernels.E10Fun (ModularGroup.S • τ)
              - 2 * (Work.Kernels.phi0 (ModularGroup.S • τ)
                  * Work.Kernels.E4Fun (ModularGroup.S • τ) ^ 3)) := by
    simp only [Xi24r0, Xi24r2, Xi24R0]
    rw [E14Fun_S_smul τ, E10Fun_S_smul τ, E4Fun_S_smul τ, phi0_S_smul τ, phi2_S_smul τ,
      Work.Kernels.S_smul_coe τ]
    have hτ0 : (τ : ℂ) ≠ 0 := coe_ne_zero τ
    field_simp
    ring
  rw [hAeq, norm_mul, norm_neg]
  have h1 : ‖((τ : ℂ) ^ (12 : ℤ))⁻¹‖ ≤ (Work.Kernels.scale τ) ^ 12 := by
    rw [show ((τ : ℂ) ^ (12 : ℤ)) = ((τ : ℂ) ^ (12 : ℕ)) by norm_num, norm_inv, norm_pow,
      ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) (norm_coe_inv_le_scale τ) 12
  have h2 := hA (ModularGroup.S • τ) hσ1
  have h2v : (0:ℝ) ≤ ‖(((ModularGroup.S • τ : ℍ)) : ℂ) * Work.Kernels.E14Fun (ModularGroup.S • τ)
      + Work.Kernels.phi2 (ModularGroup.S • τ) * Work.Kernels.E10Fun (ModularGroup.S • τ)
      - 2 * (Work.Kernels.phi0 (ModularGroup.S • τ)
          * Work.Kernels.E4Fun (ModularGroup.S • τ) ^ 3)‖ := norm_nonneg _
  calc ‖((τ : ℂ) ^ (12 : ℤ))⁻¹‖ * ‖(((ModularGroup.S • τ : ℍ)) : ℂ)
        * Work.Kernels.E14Fun (ModularGroup.S • τ)
        + Work.Kernels.phi2 (ModularGroup.S • τ) * Work.Kernels.E10Fun (ModularGroup.S • τ)
        - 2 * (Work.Kernels.phi0 (ModularGroup.S • τ)
            * Work.Kernels.E4Fun (ModularGroup.S • τ) ^ 3)‖
      ≤ (Work.Kernels.scale τ) ^ 12
          * (CA * ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖
            * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖) :=
        mul_le_mul h1 h2 h2v (by positivity)
    _ = CA * ((Work.Kernels.scale τ) ^ 12 * ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖)
          * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ := by ring
    _ ≤ CA * (Work.Kernels.scale τ) ^ 13 * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ := by
        have h6 : (Work.Kernels.scale τ) ^ 12 * ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖
            ≤ (Work.Kernels.scale τ) ^ 13 := by
          calc (Work.Kernels.scale τ) ^ 12 * ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖
              ≤ (Work.Kernels.scale τ) ^ 12 * Work.Kernels.scale τ :=
                mul_le_mul_of_nonneg_left hσle (scale_pow_nonneg τ 12)
            _ = (Work.Kernels.scale τ) ^ 13 := by ring
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h6 hCA.le) (norm_nonneg _)
/-- `B = 6δ(z)(j(τ)-j(z)) + 1728E₄(z) = 6δ(z)j(τ) + 6E₄(z)(288Δ(z) - δ(z)E₄(z)²)/Δ(z)`. -/
private lemma Xi24_B_eq (τ z : ℍ) :
    6 * Xi24delta z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
        + 1728 * Work.Kernels.E4Fun z
      = 6 * Xi24delta z * Work.Kernels.jInvariantFun τ
        + 6 * Work.Kernels.E4Fun z * (288 * Work.Kernels.DeltaFun z
            - Xi24delta z * Work.Kernels.E4Fun z ^ 2) / Work.Kernels.DeltaFun z := by
  have hDz : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  rw [Xi24delta, Work.Kernels.jInvariantFun]
  field_simp
  ring

/-- The factor `B` of the decomposition is `O(q_z)` up to the harmless factor `(1 + ‖j τ‖)`. -/
theorem Xi24_B_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ z : UpperHalfPlane, (3 / 2 : ℝ) ≤ (ModularGroup.S • τ).im → 1 ≤ z.im →
      ‖6 * Xi24delta z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
          + 1728 * Work.Kernels.E4Fun z‖
        ≤ C * ‖Work.Kernels.qParamFun z‖ * (1 + ‖Work.Kernels.jInvariantFun τ‖) := by
  obtain ⟨Cz, hCz, hzi⟩ := Xi24_z_bounds
  obtain ⟨cj, hcj, hj⟩ := DeltaFun_lower
  refine ⟨6 * Cz + 6 * Cz ^ 2 / cj + 1, by positivity, fun τ z hτ hz => ?_⟩
  obtain ⟨hδz0, hrz0, h288z0, hE4z, hjzi, hE2z, hE6z⟩ := hzi z hz
  have hδz : ‖Xi24delta z‖ ≤ Cz * ‖Work.Kernels.qParamFun z‖ := hδz0
  have h288z : ‖288 * Work.Kernels.DeltaFun z - Xi24delta z * Work.Kernels.E4Fun z ^ 2‖
      ≤ Cz * ‖Work.Kernels.qParamFun z‖ ^ 2 := h288z0
  have hqz : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hqpos : 0 < ‖Work.Kernels.qParamFun z‖ := norm_pos_iff.mpr (qParamFun_ne_zero' z)
  have hDl : cj * ‖Work.Kernels.qParamFun z‖ ≤ ‖Work.Kernels.DeltaFun z‖ := hj z hz
  have hDpos : 0 < ‖Work.Kernels.DeltaFun z‖ := lt_of_lt_of_le (mul_pos hcj hqpos) hDl
  rw [Xi24_B_eq]
  have h1 : ‖6 * Xi24delta z * Work.Kernels.jInvariantFun τ‖
      ≤ 6 * Cz * ‖Work.Kernels.qParamFun z‖ * ‖Work.Kernels.jInvariantFun τ‖ := by
    rw [norm_mul, norm_mul]
    have h6 : ‖(6:ℂ)‖ = 6 := by norm_num
    rw [h6]
    have h := mul_le_mul_of_nonneg_right hδz (norm_nonneg (Work.Kernels.jInvariantFun τ))
    nlinarith [h, hqz, norm_nonneg (Work.Kernels.jInvariantFun τ)]
  have h2 : ‖6 * Work.Kernels.E4Fun z * (288 * Work.Kernels.DeltaFun z
        - Xi24delta z * Work.Kernels.E4Fun z ^ 2) / Work.Kernels.DeltaFun z‖
      ≤ 6 * Cz ^ 2 / cj * ‖Work.Kernels.qParamFun z‖ := by
    rw [norm_div, norm_mul, norm_mul]
    have h6 : ‖(6:ℂ)‖ = 6 := by norm_num
    rw [h6]
    have hnum : 6 * ‖Work.Kernels.E4Fun z‖ * ‖288 * Work.Kernels.DeltaFun z
        - Xi24delta z * Work.Kernels.E4Fun z ^ 2‖
        ≤ 6 * Cz * (Cz * ‖Work.Kernels.qParamFun z‖ ^ 2) := by
      have h := mul_le_mul hE4z h288z (norm_nonneg _) hCz.le
      nlinarith [h, hE4z, h288z, hqz]
    have hdiv : ‖Work.Kernels.qParamFun z‖ / ‖Work.Kernels.DeltaFun z‖ ≤ 1 / cj := by
      rw [div_eq_mul_one_div]
      calc ‖Work.Kernels.qParamFun z‖ * (1 / ‖Work.Kernels.DeltaFun z‖)
          ≤ ‖Work.Kernels.qParamFun z‖ * (1 / (cj * ‖Work.Kernels.qParamFun z‖)) :=
            mul_le_mul_of_nonneg_left
              (one_div_le_one_div_of_le (mul_pos hcj hqpos) hDl) hqz
        _ = 1 / cj := by field_simp
    calc 6 * ‖Work.Kernels.E4Fun z‖ * ‖288 * Work.Kernels.DeltaFun z
          - Xi24delta z * Work.Kernels.E4Fun z ^ 2‖ / ‖Work.Kernels.DeltaFun z‖
        = (6 * ‖Work.Kernels.E4Fun z‖ * ‖288 * Work.Kernels.DeltaFun z
            - Xi24delta z * Work.Kernels.E4Fun z ^ 2‖) / ‖Work.Kernels.DeltaFun z‖ := by ring
      _ ≤ (6 * Cz * (Cz * ‖Work.Kernels.qParamFun z‖ ^ 2)) / ‖Work.Kernels.DeltaFun z‖ :=
          div_le_div_of_nonneg_right hnum hDpos.le
      _ = 6 * Cz * (Cz * ‖Work.Kernels.qParamFun z‖ ^ 2) * (1 / ‖Work.Kernels.DeltaFun z‖) := by
          ring
      _ = 6 * Cz * Cz * ‖Work.Kernels.qParamFun z‖
            * (‖Work.Kernels.qParamFun z‖ / ‖Work.Kernels.DeltaFun z‖) := by ring
      _ ≤ 6 * Cz * Cz * ‖Work.Kernels.qParamFun z‖ * (1 / cj) :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = 6 * Cz ^ 2 / cj * ‖Work.Kernels.qParamFun z‖ := by ring
  calc ‖6 * Xi24delta z * Work.Kernels.jInvariantFun τ
        + 6 * Work.Kernels.E4Fun z * (288 * Work.Kernels.DeltaFun z
            - Xi24delta z * Work.Kernels.E4Fun z ^ 2) / Work.Kernels.DeltaFun z‖
      ≤ ‖6 * Xi24delta z * Work.Kernels.jInvariantFun τ‖
        + ‖6 * Work.Kernels.E4Fun z * (288 * Work.Kernels.DeltaFun z
            - Xi24delta z * Work.Kernels.E4Fun z ^ 2) / Work.Kernels.DeltaFun z‖ :=
        norm_add_le _ _
    _ ≤ (6 * Cz * ‖Work.Kernels.qParamFun z‖ * ‖Work.Kernels.jInvariantFun τ‖)
        + 6 * Cz ^ 2 / cj * ‖Work.Kernels.qParamFun z‖ := add_le_add h1 h2
    _ ≤ (6 * Cz + 6 * Cz ^ 2 / cj + 1) * ‖Work.Kernels.qParamFun z‖
          * (1 + ‖Work.Kernels.jInvariantFun τ‖) := by
        have hjt : (0:ℝ) ≤ ‖Work.Kernels.jInvariantFun τ‖ := norm_nonneg _
        have hX : (0:ℝ) ≤ 6 * Cz ^ 2 / cj := by positivity
        have hA : 6 * Cz * ‖Work.Kernels.qParamFun z‖ * ‖Work.Kernels.jInvariantFun τ‖
            ≤ (6 * Cz + 6 * Cz ^ 2 / cj + 1) * ‖Work.Kernels.qParamFun z‖
              * ‖Work.Kernels.jInvariantFun τ‖ := by
          apply mul_le_mul_of_nonneg_right _ hjt
          apply mul_le_mul_of_nonneg_right _ hqz
          linarith [hX, hCz.le]
        have hB : 6 * Cz ^ 2 / cj * ‖Work.Kernels.qParamFun z‖
            ≤ (6 * Cz + 6 * Cz ^ 2 / cj + 1) * ‖Work.Kernels.qParamFun z‖ := by
          apply mul_le_mul_of_nonneg_right _ hqz
          linarith [hX, hCz.le]
        nlinarith [hA, hB, hqz, hjt]

/-! ## The main theorem -/

theorem Xi24_bound_E :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : UpperHalfPlane),
      (3 / 2 : ℝ) ≤ (ModularGroup.S • τ).im → 1 ≤ z.im →
        ‖Work.Asymptotics.Xi24 τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun z‖ := by
  obtain ⟨CA, hCA, hAb⟩ := Xi24_A_bound
  obtain ⟨Cat, hCat, hat⟩ := Xi24_atoms_tau_bounds
  obtain ⟨CB, hCB, hBb⟩ := Xi24_B_bound
  obtain ⟨Cz, hCz, hzi⟩ := Xi24_z_bounds
  obtain ⟨cj, hcj, hj⟩ := DeltaFun_lower
  refine ⟨CA * CB * (1 + Cat) + 1728 * (7 * Cat + Cat) * Cz + 1728 * Cat * Cz ^ 2 * Cz / cj + 1,
    13, by positivity, by norm_num, fun τ z hτ hz => ?_⟩
  rw [show (Work.Kernels.scale τ) ^ (13 : ℝ) = (Work.Kernels.scale τ) ^ (13 : ℕ) from
    Real.rpow_natCast (Work.Kernels.scale τ) 13]
  obtain ⟨hr00, hr20, hR00, hr10, hjt⟩ := hat τ hτ
  have hr0 : ‖Xi24r0 τ‖ ≤ Cat * (Work.Kernels.scale τ) ^ 13 := hr00
  have hR0 : ‖Xi24R0 τ‖ ≤ Cat * (Work.Kernels.scale τ) ^ 13 := hR00
  have hr1 : ‖Xi24r1 τ‖ ≤ Cat * (Work.Kernels.scale τ) ^ 13
      * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ := hr10
  obtain ⟨hδz0, hrz0, h288z0, hE4z, hjzi, hE2z, hE6z⟩ := hzi z hz
  have hδz : ‖Xi24delta z‖ ≤ Cz * ‖Work.Kernels.qParamFun z‖ := hδz0
  have hrz : ‖Xi24rr z‖ ≤ Cz * ‖Work.Kernels.qParamFun z‖ ^ 2 := hrz0
  have hqznn : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hqzpos : 0 < ‖Work.Kernels.qParamFun z‖ := norm_pos_iff.mpr (qParamFun_ne_zero' z)
  have hDl : cj * ‖Work.Kernels.qParamFun z‖ ≤ ‖Work.Kernels.DeltaFun z‖ := hj z hz
  have hDpos : 0 < ‖Work.Kernels.DeltaFun z‖ := lt_of_lt_of_le (mul_pos hcj hqzpos) hDl
  have hσim : (1:ℝ) ≤ (ModularGroup.S • τ).im := by linarith
  have hqσ1 : ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ ≤ 1 :=
    norm_qParamFun_le_one _ hσim
  have hqσnn : (0:ℝ) ≤ ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ := norm_nonneg _
  have hspos : (0:ℝ) < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
  have hsnn : (0:ℝ) ≤ Work.Kernels.scale τ := hspos.le
  have hspow : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ 13 := scale_pow_nonneg τ 13
  set AA : ℂ := Xi24r0 τ + Xi24r2 τ - 2 * Xi24R0 τ with hAAdef
  set BB : ℂ := 6 * Xi24delta z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
      + 1728 * Work.Kernels.E4Fun z with hBBdef
  set CC : ℂ := 1728 * (7 * Xi24R0 τ - Xi24r0 τ) * Xi24delta z with hCCdef
  set DD : ℂ := 1728 * Xi24r1 τ * Work.Kernels.E4Fun z ^ 2 * Xi24rr z / Work.Kernels.DeltaFun z
    with hDDdef
  have hAB : ‖AA * BB‖
      ≤ CA * CB * (1 + Cat) * (Work.Kernels.scale τ) ^ 13 * ‖Work.Kernels.qParamFun z‖ := by
    rw [norm_mul]
    have hA := hAb τ hτ
    have hB := hBb τ z hτ hz
    rw [← hAAdef] at hA
    rw [← hBBdef] at hB
    have hkey : ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ * (1 + ‖Work.Kernels.jInvariantFun τ‖)
        ≤ 1 + Cat := by
      nlinarith [hqσ1, hqσnn, hjt, norm_nonneg (Work.Kernels.jInvariantFun τ), hCat.le]
    have hn1 : (0:ℝ) ≤ CA * (Work.Kernels.scale τ) ^ 13
        * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ := by positivity
    have hn2 : (0:ℝ) ≤ CA * CB * (Work.Kernels.scale τ) ^ 13 * ‖Work.Kernels.qParamFun z‖ := by
      positivity
    calc ‖AA‖ * ‖BB‖
        ≤ (CA * (Work.Kernels.scale τ) ^ 13 * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖)
          * (CB * ‖Work.Kernels.qParamFun z‖ * (1 + ‖Work.Kernels.jInvariantFun τ‖)) :=
          mul_le_mul hA hB (norm_nonneg _) hn1
      _ = CA * CB * (Work.Kernels.scale τ) ^ 13 * ‖Work.Kernels.qParamFun z‖
            * (‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖
              * (1 + ‖Work.Kernels.jInvariantFun τ‖)) := by ring
      _ ≤ CA * CB * (Work.Kernels.scale τ) ^ 13 * ‖Work.Kernels.qParamFun z‖ * (1 + Cat) :=
          mul_le_mul_of_nonneg_left hkey hn2
      _ = CA * CB * (1 + Cat) * (Work.Kernels.scale τ) ^ 13
            * ‖Work.Kernels.qParamFun z‖ := by ring
  have hCC2 : ‖CC‖
      ≤ 1728 * (7 * Cat + Cat) * Cz * (Work.Kernels.scale τ) ^ 13
        * ‖Work.Kernels.qParamFun z‖ := by
    rw [hCCdef, norm_mul, norm_mul]
    have h7 : ‖(7 : ℂ) * Xi24R0 τ - Xi24r0 τ‖
        ≤ 7 * Cat * (Work.Kernels.scale τ) ^ 13 + Cat * (Work.Kernels.scale τ) ^ 13 := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_mul]
      have h7c : ‖(7:ℂ)‖ = 7 := by norm_num
      rw [h7c]
      have h := mul_le_mul_of_nonneg_left hR0 (by norm_num : (0:ℝ) ≤ 7)
      linarith [h, hr0]
    have h1728 : ‖(1728:ℂ)‖ = 1728 := by norm_num
    rw [h1728]
    have hn : (0:ℝ) ≤ 1728 * (7 * Cat * (Work.Kernels.scale τ) ^ 13
        + Cat * (Work.Kernels.scale τ) ^ 13) := by positivity
    calc 1728 * ‖(7 : ℂ) * Xi24R0 τ - Xi24r0 τ‖ * ‖Xi24delta z‖
        ≤ 1728 * (7 * Cat * (Work.Kernels.scale τ) ^ 13 + Cat * (Work.Kernels.scale τ) ^ 13)
            * (Cz * ‖Work.Kernels.qParamFun z‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h7 (by norm_num)) hδz (norm_nonneg _) hn
      _ = 1728 * (7 * Cat + Cat) * Cz * (Work.Kernels.scale τ) ^ 13
            * ‖Work.Kernels.qParamFun z‖ := by ring
  have hDD2 : ‖DD‖ ≤ 1728 * Cat * Cz ^ 2 * Cz / cj * (Work.Kernels.scale τ) ^ 13
      * ‖Work.Kernels.qParamFun z‖ := by
    rw [hDDdef, norm_div]
    have hnum : ‖1728 * Xi24r1 τ * Work.Kernels.E4Fun z ^ 2 * Xi24rr z‖
        ≤ 1728 * Cat * (Work.Kernels.scale τ) ^ 13
            * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖
            * Cz ^ 2 * (Cz * ‖Work.Kernels.qParamFun z‖ ^ 2) := by
      rw [norm_mul, norm_mul, norm_mul]
      have h1728 : ‖(1728:ℂ)‖ = 1728 := by norm_num
      rw [h1728]
      have hE4sq : ‖Work.Kernels.E4Fun z ^ 2‖ ≤ Cz ^ 2 := by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hE4z 2
      have step1 : 1728 * ‖Xi24r1 τ‖ * ‖Work.Kernels.E4Fun z ^ 2‖
          ≤ 1728 * (Cat * (Work.Kernels.scale τ) ^ 13
              * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖) * Cz ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hr1 (by norm_num)) hE4sq
          (norm_nonneg _) (by positivity)
      calc 1728 * ‖Xi24r1 τ‖ * ‖Work.Kernels.E4Fun z ^ 2‖ * ‖Xi24rr z‖
          ≤ (1728 * (Cat * (Work.Kernels.scale τ) ^ 13
                * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖) * Cz ^ 2)
              * (Cz * ‖Work.Kernels.qParamFun z‖ ^ 2) :=
            mul_le_mul step1 hrz (norm_nonneg _) (by positivity)
        _ = 1728 * Cat * (Work.Kernels.scale τ) ^ 13
              * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖
              * Cz ^ 2 * (Cz * ‖Work.Kernels.qParamFun z‖ ^ 2) := by ring
    rw [div_le_iff₀ hDpos]
    have hmid : 1728 * Cat * (Work.Kernels.scale τ) ^ 13
          * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ * Cz ^ 2
          * (Cz * ‖Work.Kernels.qParamFun z‖ ^ 2)
        ≤ 1728 * Cat * (Work.Kernels.scale τ) ^ 13 * 1 * Cz ^ 2
          * (Cz * ‖Work.Kernels.qParamFun z‖ ^ 2) := by
      have hpos : (0:ℝ) ≤ 1728 * Cat * (Work.Kernels.scale τ) ^ 13
          * (Cz ^ 2 * (Cz * ‖Work.Kernels.qParamFun z‖ ^ 2)) := by positivity
      have h := mul_le_mul_of_nonneg_left hqσ1 hpos
      nlinarith [h]
    calc ‖1728 * Xi24r1 τ * Work.Kernels.E4Fun z ^ 2 * Xi24rr z‖
        ≤ 1728 * Cat * (Work.Kernels.scale τ) ^ 13
            * ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖
            * Cz ^ 2 * (Cz * ‖Work.Kernels.qParamFun z‖ ^ 2) := hnum
      _ ≤ 1728 * Cat * (Work.Kernels.scale τ) ^ 13 * 1 * Cz ^ 2
            * (Cz * ‖Work.Kernels.qParamFun z‖ ^ 2) := hmid
      _ = 1728 * Cat * Cz ^ 2 * Cz * (Work.Kernels.scale τ) ^ 13
            * ‖Work.Kernels.qParamFun z‖ ^ 2 := by ring
      _ = (1728 * Cat * Cz ^ 2 * Cz / cj * (Work.Kernels.scale τ) ^ 13
            * ‖Work.Kernels.qParamFun z‖) * (cj * ‖Work.Kernels.qParamFun z‖) := by
          field_simp
      _ ≤ (1728 * Cat * Cz ^ 2 * Cz / cj * (Work.Kernels.scale τ) ^ 13
            * ‖Work.Kernels.qParamFun z‖) * ‖Work.Kernels.DeltaFun z‖ :=
          mul_le_mul_of_nonneg_left hDl (by positivity)
  have hdec := Xi24_decomp τ z
  rw [← hAAdef, ← hBBdef, ← hCCdef, ← hDDdef] at hdec
  have hsplit : ‖AA * BB + CC - DD‖ ≤ ‖AA * BB‖ + ‖CC‖ + ‖DD‖ := by
    have h1 : ‖AA * BB + CC - DD‖ ≤ ‖AA * BB + CC‖ + ‖DD‖ := norm_sub_le _ _
    have h2 : ‖AA * BB + CC‖ ≤ ‖AA * BB‖ + ‖CC‖ := norm_add_le _ _
    linarith
  have hsum : ‖AA * BB‖ + ‖CC‖ + ‖DD‖
      ≤ (CA * CB * (1 + Cat) + 1728 * (7 * Cat + Cat) * Cz + 1728 * Cat * Cz ^ 2 * Cz / cj)
          * (Work.Kernels.scale τ) ^ 13 * ‖Work.Kernels.qParamFun z‖ := by
    have htot := add_le_add (add_le_add hAB hCC2) hDD2
    have hrearr : CA * CB * (1 + Cat) * (Work.Kernels.scale τ) ^ 13
            * ‖Work.Kernels.qParamFun z‖
          + 1728 * (7 * Cat + Cat) * Cz * (Work.Kernels.scale τ) ^ 13
            * ‖Work.Kernels.qParamFun z‖
          + 1728 * Cat * Cz ^ 2 * Cz / cj * (Work.Kernels.scale τ) ^ 13
            * ‖Work.Kernels.qParamFun z‖
        = (CA * CB * (1 + Cat) + 1728 * (7 * Cat + Cat) * Cz + 1728 * Cat * Cz ^ 2 * Cz / cj)
            * (Work.Kernels.scale τ) ^ 13 * ‖Work.Kernels.qParamFun z‖ := by ring
    linarith [htot, hrearr.le, hrearr.ge]
  have hlast : (CA * CB * (1 + Cat) + 1728 * (7 * Cat + Cat) * Cz
          + 1728 * Cat * Cz ^ 2 * Cz / cj)
        * (Work.Kernels.scale τ) ^ 13 * ‖Work.Kernels.qParamFun z‖
      ≤ (CA * CB * (1 + Cat) + 1728 * (7 * Cat + Cat) * Cz
            + 1728 * Cat * Cz ^ 2 * Cz / cj + 1)
          * (Work.Kernels.scale τ) ^ 13 * ‖Work.Kernels.qParamFun z‖ := by
    have hle : CA * CB * (1 + Cat) + 1728 * (7 * Cat + Cat) * Cz
          + 1728 * Cat * Cz ^ 2 * Cz / cj
        ≤ CA * CB * (1 + Cat) + 1728 * (7 * Cat + Cat) * Cz
          + 1728 * Cat * Cz ^ 2 * Cz / cj + 1 := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hspow) hqznn
  have hn : ‖Xi24 τ z‖ = ‖AA * BB + CC - DD‖ := by rw [hdec]
  exact le_trans (le_trans (le_trans (le_of_eq hn) hsplit) hsum) hlast

end

end Work.Asymptotics
