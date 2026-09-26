import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.BigCalc
import Submission.Work.Asymptotics.KhatE1Core.EisensteinThreeTerm
import Submission.Work.Asymptotics.KhatE1Core.jq_second_order
import Submission.Work.Asymptotics.KhatE1Core.psi_second_order
import Submission.Work.Asymptotics.KPlus8FunnelAux
import Submission.Work.Asymptotics.CuspL_eq
import Submission.Work.Asymptotics.KhatE1Defs

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-!
# The second-order expansion of `E1combo8` at the cusp

`E1combo8 ℓ τ = j(τ)(ψ₄ - ψ₂E₆/E₄) + 576(2E₄ - ψ₄)` is the `E(z)¹`-coefficient of the CKMRV
funnel bracket.  Its `q`-expansion is

  `E1combo8 ℓ τ = (737280·Λ + 122880)·q(τ) + O(‖q(τ)‖²)`,   `Λ = πiτ + cuspC ℓ`,

the `q⁰`- and `q¹`-coefficients cancelling exactly.  The constant term uses the second-order
expansions of `ψ₂`, `ψ₄` (`psi_second_order`) and the third-order expansions of `E₄`, `E₆`
(`EisensteinThreeTerm`); the `O(‖q‖²)` remainder is tracked with the `Big` calculus of
`BigCalc`.  The `j`-invariant is `O(1/‖q‖)`, not `Big 0`, so multiplication by it is done once
and explicitly in `big_jmul`.
-/

/-! ## The algebraic scaffolding -/

private noncomputable def qF (τ : ℍ) : ℂ := Work.Kernels.qParamFun τ
private noncomputable def LamF (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ
private noncomputable def E4F (τ : ℍ) : ℂ := Work.Kernels.E4Fun τ
private noncomputable def E6F (τ : ℍ) : ℂ := Work.Kernels.E6Fun τ
private noncomputable def jF (τ : ℍ) : ℂ := Work.Kernels.jInvariantFun τ
private noncomputable def psi2F (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  Work.Kernels.psi2 ℓ τ
private noncomputable def psi4F (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  Work.Kernels.psi4 ℓ τ

private noncomputable def A1F (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  E4F τ * psi4F ℓ τ - psi2F ℓ τ * E6F τ
private noncomputable def psi4ap (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  2 * LamF ℓ τ - (288 * LamF ℓ τ + 744) * qF τ - (1824 * LamF ℓ τ + 25972) * qF τ ^ 2
private noncomputable def psi2ap (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  2 * LamF ℓ τ + (48 * LamF ℓ τ + 408) * qF τ + (48 * LamF ℓ τ + 2636) * qF τ ^ 2
private noncomputable def a1F (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  1152 * (LamF ℓ τ - 1)
private noncomputable def b2F (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  -46800 * LamF ℓ τ - 1536
private noncomputable def b3F (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  -413568 * LamF ℓ τ - 4904736
private noncomputable def a2F (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  b2F ℓ τ + 37584 * LamF ℓ τ
private noncomputable def A1ap (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  a1F ℓ τ * qF τ + a2F ℓ τ * qF τ ^ 2
private noncomputable def pap (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (2 - 2 * LamF ℓ τ) + (288 * LamF ℓ τ + 1224) * qF τ
private noncomputable def rPF (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (2 * E4F τ - psi4F ℓ τ) - pap ℓ τ
private noncomputable def rEF (τ : ℍ) : ℂ := E4F τ - (1 + 240 * qF τ)
private noncomputable def rE2F (τ : ℍ) : ℂ := E4F τ - (1 + 240 * qF τ + 2160 * qF τ ^ 2)
private noncomputable def rE6F (τ : ℍ) : ℂ := E6F τ - (1 - 504 * qF τ)
private noncomputable def r62F (τ : ℍ) : ℂ := E6F τ - (1 - 504 * qF τ - 16632 * qF τ ^ 2)
private noncomputable def r4F (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  psi4F ℓ τ - psi4ap ℓ τ
private noncomputable def r2F (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  psi2F ℓ τ - psi2ap ℓ τ
private noncomputable def psi4ap2 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  psi4ap ℓ τ - 2 * LamF ℓ τ
private noncomputable def psi2ap2 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  psi2ap ℓ τ - 2 * LamF ℓ τ
private noncomputable def c2resF (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  744 * a2F ℓ τ + 39813120 * LamF ℓ τ + 169205760
private noncomputable def TTF (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (737280 * LamF ℓ τ + 122880) * qF τ
private noncomputable def A1rem (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  b3F ℓ τ * qF τ ^ 3
    + (1 + 240 * qF τ) * r4F ℓ τ
    + rE2F τ * psi4ap ℓ τ
    + 2160 * qF τ ^ 2 * psi4ap2 ℓ τ
    + rEF τ * r4F ℓ τ
    + 16632 * qF τ ^ 2 * psi2ap2 ℓ τ
    - psi2ap ℓ τ * r62F τ
    - r2F ℓ τ * E6F τ
private noncomputable def Gexpr (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (jF τ * A1ap ℓ τ + 576 * (1 + 240 * qF τ) * pap ℓ τ - TTF ℓ τ)
    + jF τ * (A1F ℓ τ - A1ap ℓ τ)
    + 576 * (1 + 240 * qF τ) * rPF ℓ τ
    + 576 * rEF τ * (2 * E4F τ - psi4F ℓ τ)
private noncomputable def Hexpr (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  c2resF ℓ τ * qF τ ^ 2
    + (jF τ * qF τ - (1 + 744 * qF τ)) * (a1F ℓ τ + a2F ℓ τ * qF τ)

/-! ## The pointwise algebraic identities -/

private lemma A1_sub_A1ap (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    A1F ℓ τ - A1ap ℓ τ = A1rem ℓ τ := by
  simp only [A1F, A1ap, A1rem, r4F, r2F, rEF, rE2F, r62F, psi4ap, psi2ap, psi4ap2,
    psi2ap2, a1F, b2F, b3F, a2F, qF, LamF, psi4F, psi2F, E4F, E6F]
  ring

private lemma E4_mul_E1combo8 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ)
    (hτ : Work.Asymptotics.Funnel τ) :
    E4F τ * Work.Asymptotics.E1combo8 ℓ τ
      = jF τ * A1F ℓ τ + 576 * E4F τ * (2 * E4F τ - psi4F ℓ τ) := by
  have hE4 : E4F τ ≠ 0 := by
    simp only [E4F]; exact Work.Asymptotics.funnel_E4_ne_zero τ hτ
  have hE1 : Work.Asymptotics.E1combo8 ℓ τ
      = jF τ * (psi4F ℓ τ - psi2F ℓ τ * E6F τ / E4F τ)
        + 576 * (2 * E4F τ - psi4F ℓ τ) := by
    simp only [Work.Asymptotics.E1combo8, jF, psi4F, psi2F, E4F, E6F]
  rw [hE1]
  simp only [A1F]
  field_simp

private lemma Gexpr_eq (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ)
    (hτ : Work.Asymptotics.Funnel τ) :
    E4F τ * Work.Asymptotics.E1combo8 ℓ τ - TTF ℓ τ = Gexpr ℓ τ := by
  rw [E4_mul_E1combo8 ℓ τ hτ]
  simp only [Gexpr, A1ap, pap, rPF, rEF, TTF, qF, LamF, jF, E4F, psi4F, psi2F, E6F]
  ring

private lemma head_eq (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    jF τ * A1ap ℓ τ + 576 * (1 + 240 * qF τ) * pap ℓ τ - TTF ℓ τ
      = Hexpr ℓ τ := by
  simp only [Hexpr, A1ap, pap, a1F, a2F, b2F, c2resF, TTF, qF, LamF, jF]
  ring

private lemma ET_eq (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    (E4F τ - 1) * TTF ℓ τ
      = 240 * (qF τ * TTF ℓ τ) + rEF τ * TTF ℓ τ := by
  simp only [rEF, E4F, qF]
  ring

/-! ## The `Big` inputs -/

private lemma big_Lam (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ => LamF ℓ τ) := by
  refine Big.of_scale (C := Real.pi + 4) (N := 1) (by positivity) (by norm_num)
    (fun τ _ => ?_)
  have hc : Work.Asymptotics.Compact.cuspC ℓ = 4 * (Real.log 2 : ℂ) :=
    Work.Asymptotics.CuspL_eq ℓ
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog : ‖(4 : ℂ) * (Real.log 2 : ℂ)‖ ≤ 4 := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlog0]
    linarith
  have hπ : ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ)‖ ≤ Real.pi * Work.Kernels.scale τ := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    have h := Work.Kernels.coe_norm_le_scale τ
    nlinarith [Real.pi_pos, Work.Kernels.scale_pos τ]
  have hgoal : LamF ℓ τ = (Real.pi : ℂ) * Complex.I * (τ : ℂ) + 4 * (Real.log 2 : ℂ) := by
    simp only [LamF]; rw [hc]
  rw [hgoal, Real.rpow_one]
  calc ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ) + 4 * (Real.log 2 : ℂ)‖
      ≤ ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ)‖ + ‖(4 : ℂ) * (Real.log 2 : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ Real.pi * Work.Kernels.scale τ + 4 := add_le_add hπ hlog
    _ ≤ (Real.pi + 4) * Work.Kernels.scale τ := by
        have h1 := Work.Kernels.one_le_scale τ
        nlinarith [Real.pi_pos]

private lemma big_q1 : Big 1 (fun τ : ℍ => qF τ) :=
  ⟨1, 0, one_pos, le_rfl, fun τ _ => by simp [qF]⟩

private lemma big_q (k : ℕ) : Big k (fun τ : ℍ => qF τ ^ k) := by
  have h := Big.pow big_q1 k
  rwa [one_mul] at h

/-- `1 + c * q` is bounded on the funnel. -/
private lemma big_one_add (c : ℂ) : Big 0 (fun τ : ℍ => (1 : ℂ) + c * qF τ) := by
  refine Big.of_bdd (C := 1 + ‖c‖ + 1) (by positivity) (fun τ hτ => ?_)
  have hq : ‖qF τ‖ ≤ 1 := by
    have h := Big.qnorm_le_one τ hτ
    simpa only [qF] using h
  have h2 : ‖(1 : ℂ) + c * qF τ‖ ≤ 1 + ‖c‖ * ‖qF τ‖ := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_one, norm_mul]
  have h3 : ‖c‖ * ‖qF τ‖ ≤ ‖c‖ := by
    nlinarith [norm_nonneg c, norm_nonneg (qF τ)]
  linarith [norm_nonneg ((1 : ℂ) + c * qF τ)]

private lemma big_jqdev : Big 2 (fun τ : ℍ => jF τ * qF τ - (1 + 744 * qF τ)) := by
  obtain ⟨Cj, hCj, hj⟩ := jq_second_order
  refine ⟨Cj, 0, hCj, le_rfl, fun τ hτ => ?_⟩
  have h := hj τ (by have := hτ.2; linarith)
  have hL : Work.Kernels.jInvariantFun τ * Work.Kernels.qParamFun τ - 1
      - 744 * Work.Kernels.qParamFun τ = jF τ * qF τ - (1 + 744 * qF τ) := by
    simp only [qF, jF]; ring
  rw [hL] at h
  simpa [qF, Real.rpow_zero] using h

/-- `j·q` is bounded on the funnel. -/
private lemma jq_uniform_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ τ : ℍ, Work.Asymptotics.Funnel τ → ‖jF τ * qF τ‖ ≤ K := by
  obtain ⟨Cj, hCj, hj⟩ := jq_second_order
  refine ⟨1 + 744 + Cj, by positivity, fun τ hτ => ?_⟩
  have hq1 : ‖qF τ‖ ≤ 1 := by
    have h := Big.qnorm_le_one τ hτ
    simpa only [qF] using h
  have hq0 : (0 : ℝ) ≤ ‖qF τ‖ := norm_nonneg _
  have h := hj τ (by have := hτ.2; linarith)
  have hL : Work.Kernels.jInvariantFun τ * Work.Kernels.qParamFun τ - 1
      - 744 * Work.Kernels.qParamFun τ = jF τ * qF τ - (1 + 744 * qF τ) := by
    simp only [qF, jF]; ring
  rw [hL] at h
  have h3 : ‖jF τ * qF τ - (1 + 744 * qF τ)‖ ≤ Cj * ‖qF τ‖ ^ 2 := by
    simpa [qF] using h
  have h4 : ‖(1 : ℂ) + 744 * qF τ‖ ≤ 1 + 744 * ‖qF τ‖ := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_one, norm_mul, Complex.norm_ofNat]
  have hsplit : jF τ * qF τ
      = (jF τ * qF τ - (1 + 744 * qF τ)) + ((1 : ℂ) + 744 * qF τ) := by ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have h5 : ‖qF τ‖ ^ 2 ≤ ‖qF τ‖ := by nlinarith [hq0, hq1]
  nlinarith [h3, h4, h5, hq0, hCj.le]

private lemma big_jqbound : Big 0 (fun τ : ℍ => jF τ * qF τ) := by
  obtain ⟨K, hK0, hKb⟩ := jq_uniform_bound
  exact Big.of_bdd hK0 hKb

/-- Multiplication by `j` costs exactly one power of `‖q‖`. -/
private lemma big_jmul {F : ℍ → ℂ} (hF : Big 3 F) : Big 2 (fun τ => jF τ * F τ) := by
  obtain ⟨K, hK0, hKb⟩ := jq_uniform_bound
  obtain ⟨Cf, Nf, hCf, hNf, hFb⟩ := hF
  refine ⟨K * Cf, Nf, by positivity, hNf, fun τ hτ => ?_⟩
  have hqpos : 0 < ‖qF τ‖ := by
    rw [norm_pos_iff]
    simp only [qF, Work.Kernels.qParamFun]
    exact Complex.exp_ne_zero _
  have h1 : ‖jF τ‖ * ‖qF τ‖ ≤ K := by
    rw [← norm_mul]
    exact hKb τ hτ
  have h2 : ‖jF τ‖ ≤ K / ‖qF τ‖ := (le_div_iff₀ hqpos).mpr h1
  have h3 : ‖F τ‖ ≤ Cf * (Work.Kernels.scale τ) ^ Nf * ‖qF τ‖ ^ 3 := hFb τ hτ
  calc ‖jF τ * F τ‖ = ‖jF τ‖ * ‖F τ‖ := norm_mul _ _
    _ ≤ (K / ‖qF τ‖) * (Cf * (Work.Kernels.scale τ) ^ Nf * ‖qF τ‖ ^ 3) :=
        mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
    _ = K * Cf * (Work.Kernels.scale τ) ^ Nf * ‖qF τ‖ ^ 2 := by
        field_simp

private lemma big_rE2F : Big 3 (fun τ : ℍ => rE2F τ) := by
  obtain ⟨C, hC, h4, _⟩ := EisensteinThreeTerm
  refine ⟨C, 0, hC, le_rfl, fun τ hτ => ?_⟩
  show ‖rE2F τ‖ ≤ C * (Work.Kernels.scale τ) ^ (0 : ℝ) * ‖Work.Kernels.qParamFun τ‖ ^ 3
  have h := h4 τ (by have := hτ.2; linarith)
  rw [show rE2F τ = Work.Kernels.E4Fun τ - 1 - 240 * qF τ - 2160 * qF τ ^ 2 by
    simp only [rE2F, E4F]; ring]
  simpa [qF, Real.rpow_zero] using h

private lemma big_rEF : Big 2 (fun τ : ℍ => rEF τ) := by
  have hsum : Big 2 (fun τ : ℍ => rE2F τ + 2160 * qF τ ^ 2) :=
    Big.add big_rE2F (Big.const_mul (2160 : ℂ) (big_q 2))
  exact hsum.congr_on (fun τ _ => by simp only [rEF, rE2F, E4F, qF]; try ring)

private lemma big_r62F : Big 3 (fun τ : ℍ => r62F τ) := by
  obtain ⟨C, hC, _, h6⟩ := EisensteinThreeTerm
  refine ⟨C, 0, hC, le_rfl, fun τ hτ => ?_⟩
  show ‖r62F τ‖ ≤ C * (Work.Kernels.scale τ) ^ (0 : ℝ) * ‖Work.Kernels.qParamFun τ‖ ^ 3
  have h := h6 τ (by have := hτ.2; linarith)
  rw [show r62F τ = Work.Kernels.E6Fun τ - 1 + 504 * qF τ + 16632 * qF τ ^ 2 by
    simp only [r62F, E6F]; ring]
  simpa [qF, Real.rpow_zero] using h

private lemma big_rE6F : Big 2 (fun τ : ℍ => rE6F τ) := by
  have hsum : Big 2 (fun τ : ℍ => r62F τ - 16632 * qF τ ^ 2) :=
    Big.sub big_r62F (Big.const_mul (16632 : ℂ) (big_q 2))
  exact hsum.congr_on (fun τ _ => by simp only [rE6F, r62F, E6F, qF]; try ring)

private lemma big_r4F (ℓ : Work.Kernels.LogLambdaData) : Big 3 (fun τ : ℍ => r4F ℓ τ) := by
  obtain ⟨Cp, Np, hCp, hNp, hpsi⟩ := psi_second_order ℓ
  refine ⟨Cp, Np, hCp, hNp, fun τ hτ => ?_⟩
  have h := (hpsi τ hτ).2
  convert h using 2
  simp only [r4F, psi4F, psi4ap, qF, LamF]
  ring

private lemma big_r2F (ℓ : Work.Kernels.LogLambdaData) : Big 3 (fun τ : ℍ => r2F ℓ τ) := by
  obtain ⟨Cp, Np, hCp, hNp, hpsi⟩ := psi_second_order ℓ
  refine ⟨Cp, Np, hCp, hNp, fun τ hτ => ?_⟩
  have h := (hpsi τ hτ).1
  convert h using 2
  simp only [r2F, psi2F, psi2ap, qF, LamF]
  ring

private lemma big_psi4ap2 (ℓ : Work.Kernels.LogLambdaData) :
    Big 1 (fun τ : ℍ => psi4ap2 ℓ τ) := by
  have h1 : Big 1 (fun τ : ℍ => -((288 * LamF ℓ τ + 744) * qF τ)) :=
    Big.neg ((Big.add (Big.const_mul (288 : ℂ) (Big.mul (big_Lam ℓ) big_q1))
      (Big.const_mul (744 : ℂ) big_q1)).congr_on (fun τ _ => by try ring))
  have h2 : Big 1 (fun τ : ℍ => (1824 * LamF ℓ τ + 25972) * qF τ ^ 2) :=
    ((Big.add (Big.const_mul (1824 : ℂ) (Big.mul (big_Lam ℓ) (big_q 2)))
      (Big.const_mul (25972 : ℂ) (big_q 2))).congr_on (fun τ _ => by try ring)).mono (by norm_num)
  have h : Big 1 (fun τ : ℍ => -((288 * LamF ℓ τ + 744) * qF τ)
      - (1824 * LamF ℓ τ + 25972) * qF τ ^ 2) := Big.sub h1 h2
  exact h.congr_on (fun τ _ => by simp only [psi4ap2, psi4ap, qF, LamF]; try ring)

private lemma big_psi2ap2 (ℓ : Work.Kernels.LogLambdaData) :
    Big 1 (fun τ : ℍ => psi2ap2 ℓ τ) := by
  have h1 : Big 1 (fun τ : ℍ => (48 * LamF ℓ τ + 408) * qF τ) :=
    (Big.add (Big.const_mul (48 : ℂ) (Big.mul (big_Lam ℓ) big_q1))
      (Big.const_mul (408 : ℂ) big_q1)).congr_on (fun τ _ => by try ring)
  have h2 : Big 1 (fun τ : ℍ => (48 * LamF ℓ τ + 2636) * qF τ ^ 2) :=
    ((Big.add (Big.const_mul (48 : ℂ) (Big.mul (big_Lam ℓ) (big_q 2)))
      (Big.const_mul (2636 : ℂ) (big_q 2))).congr_on (fun τ _ => by try ring)).mono (by norm_num)
  have h : Big 1 (fun τ : ℍ => (48 * LamF ℓ τ + 408) * qF τ
      + (48 * LamF ℓ τ + 2636) * qF τ ^ 2) := Big.add h1 h2
  exact h.congr_on (fun τ _ => by simp only [psi2ap2, psi2ap, qF, LamF]; try ring)

private lemma big_psi4ap (ℓ : Work.Kernels.LogLambdaData) :
    Big 0 (fun τ : ℍ => psi4ap ℓ τ) := by
  have h1 : Big 0 (fun τ : ℍ => (288 * LamF ℓ τ + 744) * qF τ) :=
    ((Big.add (Big.const_mul (288 : ℂ) (Big.mul (big_Lam ℓ) big_q1))
      (Big.const_mul (744 : ℂ) big_q1)).congr_on (fun τ _ => by try ring)).mono (by norm_num)
  have h2 : Big 0 (fun τ : ℍ => (1824 * LamF ℓ τ + 25972) * qF τ ^ 2) :=
    ((Big.add (Big.const_mul (1824 : ℂ) (Big.mul (big_Lam ℓ) (big_q 2)))
      (Big.const_mul (25972 : ℂ) (big_q 2))).congr_on (fun τ _ => by try ring)).mono (by norm_num)
  have h : Big 0 (fun τ : ℍ => 2 * LamF ℓ τ - (288 * LamF ℓ τ + 744) * qF τ
      - (1824 * LamF ℓ τ + 25972) * qF τ ^ 2) :=
    (Big.sub (Big.const_mul (2 : ℂ) (big_Lam ℓ)) (Big.add h1 h2)).congr_on
      (fun τ _ => by try ring)
  exact h.congr_on (fun τ _ => by simp only [psi4ap, qF, LamF]; try ring)

private lemma big_psi2ap (ℓ : Work.Kernels.LogLambdaData) :
    Big 0 (fun τ : ℍ => psi2ap ℓ τ) := by
  have h1 : Big 0 (fun τ : ℍ => (48 * LamF ℓ τ + 408) * qF τ) :=
    ((Big.add (Big.const_mul (48 : ℂ) (Big.mul (big_Lam ℓ) big_q1))
      (Big.const_mul (408 : ℂ) big_q1)).congr_on (fun τ _ => by try ring)).mono (by norm_num)
  have h2 : Big 0 (fun τ : ℍ => (48 * LamF ℓ τ + 2636) * qF τ ^ 2) :=
    ((Big.add (Big.const_mul (48 : ℂ) (Big.mul (big_Lam ℓ) (big_q 2)))
      (Big.const_mul (2636 : ℂ) (big_q 2))).congr_on (fun τ _ => by try ring)).mono (by norm_num)
  have h : Big 0 (fun τ : ℍ => 2 * LamF ℓ τ + (48 * LamF ℓ τ + 408) * qF τ
      + (48 * LamF ℓ τ + 2636) * qF τ ^ 2) :=
    (Big.add (Big.const_mul (2 : ℂ) (big_Lam ℓ)) (Big.add h1 h2)).congr_on
      (fun τ _ => by try ring)
  exact h.congr_on (fun τ _ => by simp only [psi2ap, qF, LamF]; try ring)

private lemma big_E4F : Big 0 (fun τ : ℍ => E4F τ) := by
  refine Big.of_bdd (C := (3 : ℝ) / 2) (by norm_num) (fun τ hτ => ?_)
  have h := Work.Asymptotics.funnel_E4_sub_one_le τ hτ
  have h2 := abs_norm_sub_norm_le (Work.Kernels.E4Fun τ) (1 : ℂ)
  rw [norm_one] at h2
  have h3 : ‖Work.Kernels.E4Fun τ‖ - 1 ≤ (1 : ℝ) / 2 := (abs_le.mp (le_trans h2 h)).2
  simp only [E4F]
  linarith

private lemma big_E6F : Big 0 (fun τ : ℍ => E6F τ) := by
  have h : Big (min 2 (min 0 1)) (fun τ : ℍ => rE6F τ + ((1 : ℂ) + (-504) * qF τ)) :=
    Big.add big_rE6F (Big.add (Big.const (1 : ℂ)) (Big.const_mul (-504 : ℂ) big_q1))
  refine h.congr_on (fun τ _ => ?_)
  simp only [rE6F, E6F]; ring

private lemma big_psi4F (ℓ : Work.Kernels.LogLambdaData) :
    Big 0 (fun τ : ℍ => psi4F ℓ τ) := by
  have h := Big.add (big_psi4ap ℓ) (big_r4F ℓ)
  exact h.congr_on (fun τ _ => by simp only [psi4F, r4F]; try ring)

private lemma big_pap (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => pap ℓ τ) := by
  have h : Big (min 0 1) (fun τ : ℍ => (2 * (1 : ℂ) - 2 * LamF ℓ τ)
      + (288 * LamF ℓ τ + 1224) * qF τ) :=
    Big.add (Big.sub (Big.const_mul (2 : ℂ) (Big.const (1 : ℂ)))
        (Big.const_mul (2 : ℂ) (big_Lam ℓ)))
      (Big.mul (Big.add (Big.const_mul (288 : ℂ) (big_Lam ℓ))
        (Big.const (1224 : ℂ))) big_q1)
  refine h.congr_on (fun τ _ => ?_)
  simp only [pap]; try ring

private lemma big_rPF (ℓ : Work.Kernels.LogLambdaData) : Big 2 (fun τ : ℍ => rPF ℓ τ) := by
  have h1 : Big 2 (fun τ : ℍ => (1824 * LamF ℓ τ + 25972) * qF τ ^ 2) :=
    Big.mul (Big.add (Big.const_mul (1824 : ℂ) (big_Lam ℓ)) (Big.const (25972 : ℂ)))
      (big_q 2)
  have h2 : Big 2 (fun τ : ℍ => 2 * rEF τ) := Big.const_mul (2 : ℂ) big_rEF
  have h3 : Big 2 (fun τ : ℍ => r4F ℓ τ) := (big_r4F ℓ).mono (by norm_num)
  have h : Big 2 (fun τ : ℍ => (1824 * LamF ℓ τ + 25972) * qF τ ^ 2 + 2 * rEF τ
      - r4F ℓ τ) := Big.sub (Big.add h1 h2) h3
  exact h.congr_on (fun τ _ => by
    simp only [rPF, rEF, r4F, psi4ap, pap, qF, LamF, E4F, psi4F]; try ring)

private lemma big_a1F (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => a1F ℓ τ) := by
  have h := Big.const_mul (1152 : ℂ) (Big.sub (big_Lam ℓ) (Big.const (1 : ℂ)))
  exact h.congr_on (fun τ _ => by simp only [a1F, qF, LamF]; try ring)

private lemma big_a2F (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => a2F ℓ τ) := by
  have h := Big.add (Big.const_mul (-46800 : ℂ) (big_Lam ℓ))
    (Big.add (Big.const_mul (-1536 : ℂ) (Big.const (1 : ℂ)))
      (Big.const_mul (37584 : ℂ) (big_Lam ℓ)))
  exact h.congr_on (fun τ _ => by simp only [a2F, b2F, qF, LamF]; try ring)

private lemma big_a12 (ℓ : Work.Kernels.LogLambdaData) :
    Big 0 (fun τ : ℍ => a1F ℓ τ + a2F ℓ τ * qF τ) := by
  have h := Big.add (big_a1F ℓ) (Big.mul (big_a2F ℓ) big_q1)
  exact (h.mono (by norm_num)).congr_on (fun τ _ => by simp only [a1F, a2F, b2F, qF, LamF]; try ring)

private lemma big_b3F (ℓ : Work.Kernels.LogLambdaData) : Big 0 (fun τ : ℍ => b3F ℓ τ) := by
  have h := Big.add (Big.const_mul (-413568 : ℂ) (big_Lam ℓ))
    (Big.const_mul (-4904736 : ℂ) (Big.const (1 : ℂ)))
  exact h.congr_on (fun τ _ => by simp only [b3F, qF, LamF]; try ring)

private lemma big_c2res (ℓ : Work.Kernels.LogLambdaData) :
    Big 0 (fun τ : ℍ => c2resF ℓ τ) := by
  have h := Big.add (Big.const_mul (744 : ℂ) (big_a2F ℓ))
    (Big.add (Big.const_mul (39813120 : ℂ) (big_Lam ℓ)) (Big.const_mul (169205760 : ℂ)
      (Big.const (1 : ℂ))))
  exact h.congr_on (fun τ _ => by simp only [c2resF, a2F, b2F, qF, LamF]; try ring)

private lemma big_A1rem (ℓ : Work.Kernels.LogLambdaData) : Big 3 (fun τ : ℍ => A1rem ℓ τ) := by
  have h1 : Big 3 (fun τ : ℍ => b3F ℓ τ * qF τ ^ 3) := Big.mul (big_b3F ℓ) (big_q 3)
  have h2 : Big 3 (fun τ : ℍ => (1 + 240 * qF τ) * r4F ℓ τ) :=
    Big.mul (big_one_add 240) (big_r4F ℓ)
  have h3 : Big 3 (fun τ : ℍ => rE2F τ * psi4ap ℓ τ) := Big.mul big_rE2F (big_psi4ap ℓ)
  have h4 : Big 3 (fun τ : ℍ => 2160 * qF τ ^ 2 * psi4ap2 ℓ τ) :=
    (Big.const_mul (2160 : ℂ) (Big.mul (big_q 2) (big_psi4ap2 ℓ))).congr_on
      (fun τ _ => by try ring)
  have h5 : Big 3 (fun τ : ℍ => rEF τ * r4F ℓ τ) :=
    (Big.mul big_rEF (big_r4F ℓ)).mono (by norm_num)
  have h6 : Big 3 (fun τ : ℍ => 16632 * qF τ ^ 2 * psi2ap2 ℓ τ) :=
    (Big.const_mul (16632 : ℂ) (Big.mul (big_q 2) (big_psi2ap2 ℓ))).congr_on
      (fun τ _ => by try ring)
  have h7 : Big 3 (fun τ : ℍ => psi2ap ℓ τ * r62F τ) := Big.mul (big_psi2ap ℓ) big_r62F
  have h8 : Big 3 (fun τ : ℍ => r2F ℓ τ * E6F τ) := Big.mul (big_r2F ℓ) big_E6F
  have hsum := Big.sub (Big.sub (Big.add (Big.add (Big.add (Big.add (Big.add h1 h2) h3) h4)
    h5) h6) h7) h8
  exact hsum.congr_on (fun τ _ => by simp only [A1rem]; try ring)

private lemma big_A1r (ℓ : Work.Kernels.LogLambdaData) :
    Big 3 (fun τ : ℍ => A1F ℓ τ - A1ap ℓ τ) :=
  (big_A1rem ℓ).congr_on (fun τ _ => (A1_sub_A1ap ℓ τ).symm)

private lemma big_Head (ℓ : Work.Kernels.LogLambdaData) :
    Big 2 (fun τ : ℍ => jF τ * A1ap ℓ τ + 576 * (1 + 240 * qF τ) * pap ℓ τ - TTF ℓ τ) := by
  have hh : Big 2 (fun τ : ℍ => Hexpr ℓ τ) := by
    have hA0 : Big 2 (fun τ : ℍ => c2resF ℓ τ * qF τ ^ 2) := Big.mul (big_c2res ℓ) (big_q 2)
    have hA1 : Big 2 (fun τ : ℍ => (jF τ * qF τ - (1 + 744 * qF τ))
        * (a1F ℓ τ + a2F ℓ τ * qF τ)) := Big.mul big_jqdev (big_a12 ℓ)
    exact (Big.add hA0 hA1).congr_on (fun τ _ => by simp only [Hexpr]; try ring)
  exact hh.congr_on (fun τ _ => (head_eq ℓ τ).symm)

private lemma big_Gexpr (ℓ : Work.Kernels.LogLambdaData) :
    Big 2 (fun τ : ℍ => Gexpr ℓ τ) := by
  have h1 := big_Head ℓ
  have h2 : Big 2 (fun τ : ℍ => jF τ * (A1F ℓ τ - A1ap ℓ τ)) := big_jmul (big_A1r ℓ)
  have h3 : Big 2 (fun τ : ℍ => 576 * (1 + 240 * qF τ) * rPF ℓ τ) :=
    (Big.const_mul (576 : ℂ) (Big.mul (big_one_add 240) (big_rPF ℓ))).congr_on
      (fun τ _ => by try ring)
  have h4 : Big 2 (fun τ : ℍ => 576 * rEF τ * (2 * E4F τ - psi4F ℓ τ)) := by
    have h0 : Big 0 (fun τ : ℍ => 2 * E4F τ - psi4F ℓ τ) :=
      Big.sub (Big.const_mul (2 : ℂ) big_E4F) (big_psi4F ℓ)
    exact (Big.const_mul (576 : ℂ) (Big.mul big_rEF h0)).congr_on (fun τ _ => by try ring)
  have hsum := ((h1.add h2).add h3).add h4
  exact hsum.congr_on (fun τ _ => by simp only [Gexpr]; try ring)

private lemma big_G (ℓ : Work.Kernels.LogLambdaData) :
    Big 2 (fun τ : ℍ => E4F τ * Work.Asymptotics.E1combo8 ℓ τ - TTF ℓ τ) :=
  (big_Gexpr ℓ).congr_on (fun τ hτ => (Gexpr_eq ℓ τ hτ).symm)

private lemma big_TTF (ℓ : Work.Kernels.LogLambdaData) : Big 1 (fun τ : ℍ => TTF ℓ τ) := by
  have h : Big 1 (fun τ : ℍ => (737280 * LamF ℓ τ + 122880) * qF τ) :=
    (Big.mul (Big.add (Big.const_mul (737280 : ℂ) (big_Lam ℓ))
      (Big.const_mul (122880 : ℂ) (Big.const (1 : ℂ)))) big_q1).congr_on
      (fun τ _ => by try ring)
  exact h.congr_on (fun τ _ => by simp only [TTF, qF, LamF]; try ring)

private lemma big_ET (ℓ : Work.Kernels.LogLambdaData) :
    Big 2 (fun τ : ℍ => (E4F τ - 1) * TTF ℓ τ) := by
  have h1 : Big 2 (fun τ : ℍ => 240 * (qF τ * TTF ℓ τ)) :=
    Big.const_mul (240 : ℂ) (Big.mul big_q1 (big_TTF ℓ))
  have h2 : Big 3 (fun τ : ℍ => rEF τ * TTF ℓ τ) := Big.mul big_rEF (big_TTF ℓ)
  have hsum : Big 2 (fun τ : ℍ => 240 * (qF τ * TTF ℓ τ) + rEF τ * TTF ℓ τ) := Big.add h1 h2
  exact hsum.congr_on (fun τ _ => (ET_eq ℓ τ).symm)

private lemma big_final (ℓ : Work.Kernels.LogLambdaData) :
    Big 2 (fun τ : ℍ => Work.Asymptotics.E1combo8 ℓ τ - TTF ℓ τ) := by
  have hE4inv : Big 0 (fun τ : ℍ => (E4F τ)⁻¹) := by
    refine Big.of_bdd (C := 2) (by norm_num) (fun τ hτ => ?_)
    have h := Work.Asymptotics.funnel_E4_inv_le τ hτ
    simp only [E4F]
    exact h
  have hnum : Big 2 (fun τ : ℍ => (E4F τ * Work.Asymptotics.E1combo8 ℓ τ - TTF ℓ τ)
      - (E4F τ - 1) * TTF ℓ τ) := Big.sub (big_G ℓ) (big_ET ℓ)
  have hprod := Big.mul hE4inv hnum
  refine hprod.congr_on (fun τ hτ => ?_)
  have hE4 : E4F τ ≠ 0 := by
    simp only [E4F]; exact Work.Asymptotics.funnel_E4_ne_zero τ hτ
  field_simp
  ring

/-- **The second-order expansion of `E1combo8` at the cusp.**
`E1combo8 ℓ τ = (737280·Λ + 122880)·q(τ) + O(‖q(τ)‖²)`, `Λ = πiτ + cuspC ℓ`. -/
theorem E1combo8_second_order (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      ‖Work.Asymptotics.E1combo8 ℓ τ
        - (737280 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
            + Work.Asymptotics.Compact.cuspC ℓ) + 122880) * Work.Kernels.qParamFun τ‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
  obtain ⟨C, N, hC, hN, h⟩ := big_final ℓ
  exact ⟨C, N, hC, hN, fun τ hτ => by
    have hh := h τ hτ
    simpa only [qF, LamF, TTF] using hh⟩

end

end Work.Asymptotics.KhatE1Core
