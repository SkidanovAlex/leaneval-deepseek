/-
# The weight-twelve rigidity lemma at eigenvalue `-1`

This file proves `Work.Rigidity.SingleRigidityP 12 (-1 : ℂ) 1`: no nonzero holomorphic
`f : ℍ → ℂ` of moderate growth (`f ∈ 𝒫 = Work.Kernels.InP`) that is annihilated by `(T - I)²`,
is anti-invariant for the weight-`12` slash action of `S`, and decays like `o(e^{-2π Im τ})`
along the strip `-1 ≤ Re τ ≤ 1`.

The proof follows CKMRV, Proposition `prop: HFE plus` (arXiv 1902.05438, Section 3.3), at
`k = 12`, together with the `q`-expansion analysis of `lem:noPsolutions`:

* `A = fstDiff f` and `B = qzero f = f - τ A` are periodic of period `1` and `O(q²)` at the
  cusp (`fstDiff_q2_bound`, `QzeroOrderTwo`), so that the first two `q`-expansion coefficients
  of `A` and `B` vanish (`ExpDecayCoeffZero`);
* `h₂ = A |₁₂ S - τ²A - 2τB` is a level-one modular form of weight `10`, and
  `m = 2B - (πi/3) h₂ E₂`, `F₀ = A - (πi/6) m E₂ + (π²/36) h₂ E₂²` are modular forms of
  weights `12` and `14` (the description of `Ann₁₂(𝓘₊, 𝒫)`);
* writing `c = [h₂]₀`, `c₁ = [h₂]₁`, the vanishing of the first two coefficients of `A` and
  `B` gives `c₁ = 24c` (weight-`14` rank one) and `c₁ = -264c` (`M₁₀ = ℂ E₁₀`), whence `c = 0`,
  and then `F₀ = m = h₂ = A = B = 0`.
-/
import Mathlib
import Submission.Work.Rigidity.TwelvePlusSetup
import Submission.Work.Rigidity.ModerateGrowth
import Submission.Work.Rigidity.boundedAtImInfty_of_periodic_inP
import Submission.Work.Rigidity.QzeroOrderTwo
import Submission.Work.Rigidity.ExpDecayCoeffZero
import Submission.Work.Rigidity.CuspFunctionMul
import Submission.Work.Modular.modularForm_of_slash_invariant
import Submission.Work.Modular.E2_qExpansion_coeff

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix Filter
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Rigidity

/-! ## `q`-expansion coefficient helpers -/

lemma coeff_zero_mul_qExp {F G : ℍ → ℂ}
    (hF : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 F) 0)
    (hG : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 G) 0) :
    (UpperHalfPlane.qExpansion 1 (F * G)).coeff 0
      = (UpperHalfPlane.qExpansion 1 F).coeff 0 * (UpperHalfPlane.qExpansion 1 G).coeff 0 :=
  UpperHalfPlane.qExpansion_mul_coeff_zero hF.continuousAt hG.continuousAt

lemma coeff_one_mul_qExp {F G : ℍ → ℂ}
    (hF : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 F) 0)
    (hG : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 G) 0) :
    (UpperHalfPlane.qExpansion 1 (F * G)).coeff 1
      = (UpperHalfPlane.qExpansion 1 F).coeff 1 * (UpperHalfPlane.qExpansion 1 G).coeff 0
        + (UpperHalfPlane.qExpansion 1 F).coeff 0 * (UpperHalfPlane.qExpansion 1 G).coeff 1 := by
  rw [UpperHalfPlane.qExpansion_mul hF hG, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_empty, zero_add,
    Nat.reduceSubDiff, zero_sub, Prod.mk.eta]
  ring

lemma psCoeff_zero_mul (φ ψ : PowerSeries ℂ) :
    (φ * ψ).coeff 0 = φ.coeff 0 * ψ.coeff 0 := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]

lemma psCoeff_one_mul (φ ψ : PowerSeries ℂ) :
    (φ * ψ).coeff 1 = φ.coeff 1 * ψ.coeff 0 + φ.coeff 0 * ψ.coeff 1 := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_empty, zero_add,
    Nat.reduceSubDiff, zero_sub, Prod.mk.eta]
  ring

/-! ## Coefficients of `E₂`, `E₁₀`, `E₁₄` -/

lemma E2_sq_eq : (Work.Modular.E2 : ℍ → ℂ) ^ 2 = Work.Modular.E2 * Work.Modular.E2 := by
  funext τ
  simp only [Pi.pow_apply, Pi.mul_apply, pow_two]

lemma E2_coeff_zero : (UpperHalfPlane.qExpansion 1 Work.Modular.E2).coeff 0 = 1 := by
  rw [Work.Modular.E2_qExpansion_coeff]
  simp

lemma E2_coeff_one : (UpperHalfPlane.qExpansion 1 Work.Modular.E2).coeff 1 = -24 := by
  rw [Work.Modular.E2_qExpansion_coeff]
  norm_num [ArithmeticFunction.sigma_one]

lemma E10_coeff_zero :
    (UpperHalfPlane.qExpansion 1 (ModularForm.E (by norm_num : 3 ≤ 10) : ℍ → ℂ)).coeff 0 = 1 :=
  EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) (by norm_num)

lemma E14_coeff_zero :
    (UpperHalfPlane.qExpansion 1 (ModularForm.E (by norm_num : 3 ≤ 14) : ℍ → ℂ)).coeff 0 = 1 :=
  EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) (by norm_num)

lemma E10_coeff_one :
    (UpperHalfPlane.qExpansion 1 (ModularForm.E (by norm_num : 3 ≤ 10) : ℍ → ℂ)).coeff 1
      = -264 := by
  rw [EisensteinSeries.E_qExpansion_coeff (by norm_num : (3 : ℕ) ≤ 10) (by norm_num) 1]
  norm_num [ArithmeticFunction.sigma_one,
    show bernoulli 10 = 5 / 66 by decide +kernel]

lemma E14_coeff_one :
    (UpperHalfPlane.qExpansion 1 (ModularForm.E (by norm_num : 3 ≤ 14) : ℍ → ℂ)).coeff 1
      = -24 := by
  rw [EisensteinSeries.E_qExpansion_coeff (by norm_num : (3 : ℕ) ≤ 14) (by norm_num) 1]
  norm_num [ArithmeticFunction.sigma_one,
    show bernoulli 14 = 7 / 6 by decide +kernel]

/-! ## The linear algebra of the six coefficient relations -/

lemma coeff_kill {c c1 f0 f1 : ℂ}
    (hf0 : f0 = -((Real.pi : ℂ) ^ 2 / 36) * c)
    (hf1 : f1 = -((Real.pi : ℂ) ^ 2 / 36) * c1 + 4 * (Real.pi : ℂ) ^ 2 / 3 * c)
    (hrank : f1 = -24 * f0)
    (hc1 : c1 = -264 * c) : c = 0 := by
  have h1 : f1 = 24 * ((Real.pi : ℂ) ^ 2 / 36) * c := by
    rw [hrank, hf0]; ring
  have h2 : f1 = 264 * ((Real.pi : ℂ) ^ 2 / 36) * c + 4 * (Real.pi : ℂ) ^ 2 / 3 * c := by
    rw [hf1, hc1]; ring
  have h3 : (240 * ((Real.pi : ℂ) ^ 2 / 36) + 4 * (Real.pi : ℂ) ^ 2 / 3) * c = 0 := by
    linear_combination h1 - h2
  have h4 : 240 * ((Real.pi : ℂ) ^ 2 / 36) + 4 * (Real.pi : ℂ) ^ 2 / 3
      = 8 * (Real.pi : ℂ) ^ 2 := by ring
  rw [h4] at h3
  have hpi : (8 * (Real.pi : ℂ) ^ 2) ≠ 0 := by
    have h : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 h)
  exact (mul_eq_zero.mp h3).resolve_left hpi



lemma F0_kill0 (c : ℂ) :
    -((Real.pi : ℂ) * Complex.I / 6) * (-((Real.pi : ℂ) * Complex.I / 3) * c)
      + ((Real.pi : ℂ) ^ 2 / 36) * c = -((Real.pi : ℂ) ^ 2 / 36) * c := by
  rw [show -((Real.pi : ℂ) * Complex.I / 6) * (-((Real.pi : ℂ) * Complex.I / 3) * c)
      = (((Real.pi : ℂ) * Complex.I / 6) * ((Real.pi : ℂ) * Complex.I / 3)) * c by ring]
  rw [show ((Real.pi : ℂ) * Complex.I / 6) * ((Real.pi : ℂ) * Complex.I / 3)
      = (Real.pi : ℂ) ^ 2 * (Complex.I * Complex.I) / 18 by ring]
  rw [Complex.I_mul_I]
  ring

lemma F0_kill1 (c c1 : ℂ) :
    -((Real.pi : ℂ) * Complex.I / 6) * (-((Real.pi : ℂ) * Complex.I / 3) * (c1 - 24 * c)
        - 24 * (-((Real.pi : ℂ) * Complex.I / 3) * c))
      + ((Real.pi : ℂ) ^ 2 / 36) * (c1 - 48 * c)
      = -((Real.pi : ℂ) ^ 2 / 36) * c1 + 4 * (Real.pi : ℂ) ^ 2 / 3 * c := by
  ring_nf
  simp only [Complex.I_mul_I, Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four]
  ring

/-! ## The normalized generator of the space of modular forms -/

lemma eq_smul_E {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k)
    (hrank : Module.rank ℂ (ModularForm 𝒮ℒ (k : ℤ)) = 1)
    (F : ModularForm 𝒮ℒ (k : ℤ)) :
    F = ((UpperHalfPlane.qExpansion 1 (⇑F)).coeff 0) • (ModularForm.E hk) := by
  obtain ⟨c0, hc0⟩ := (finrank_eq_one_iff_of_nonzero' (ModularForm.E hk)
      (EisensteinSeries.E_ne_zero hk hk2)).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp hrank) F
  have h0 : (UpperHalfPlane.qExpansion 1 (⇑(ModularForm.E hk))).coeff 0 = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero hk hk2
  have hsm : UpperHalfPlane.qExpansion 1 (⇑(c0 • ModularForm.E hk))
      = c0 • UpperHalfPlane.qExpansion 1 (⇑(ModularForm.E hk)) :=
    ModularForm.qExpansion_smul (h := 1) (Γ := 𝒮ℒ) one_pos one_mem_strictPeriods_SL c0
      (ModularForm.E hk)
  have hval : c0 = (UpperHalfPlane.qExpansion 1 (⇑F)).coeff 0 := by
    have h := congrArg (fun (G : ModularForm 𝒮ℒ (k : ℤ)) =>
      (UpperHalfPlane.qExpansion 1 (⇑G)).coeff 0) hc0
    rw [hsm] at h
    simp only [PowerSeries.coeff_smul, smul_eq_mul, h0, mul_one] at h
    exact h
  exact hc0.symm.trans (congrArg (fun c : ℂ => c • ModularForm.E hk) hval)

lemma coeff_smul_E {k : ℕ} (hk : 3 ≤ k) (c : ℂ) (n : ℕ) :
    (UpperHalfPlane.qExpansion 1 (⇑(c • ModularForm.E hk))).coeff n
      = c * (UpperHalfPlane.qExpansion 1 (⇑(ModularForm.E hk))).coeff n := by
  have hsm : UpperHalfPlane.qExpansion 1 (⇑(c • ModularForm.E hk))
      = c • UpperHalfPlane.qExpansion 1 (⇑(ModularForm.E hk)) :=
    ModularForm.qExpansion_smul (h := 1) (Γ := 𝒮ℒ) one_pos one_mem_strictPeriods_SL c
      (ModularForm.E hk)
  rw [hsm, PowerSeries.coeff_smul, smul_eq_mul]

/-! ## The main theorem -/

theorem AnnPlusWeightTwelveP : Work.Rigidity.SingleRigidityP 12 (-1 : ℂ) 1 := by
  intro f hP hT2 hS hdec
  have hmd : MDiff f := hP.1
  -- periodicity of the auxiliary functions
  have hAv : ∀ τ : ℍ, fstDiff f ((1 : ℝ) +ᵥ τ) = fstDiff f τ :=
    (fstDiff_vadd_one_iff f).mp hT2
  have hBv : ∀ τ : ℍ, qzero f ((1 : ℝ) +ᵥ τ) = qzero f τ := qzero_vadd_one hT2
  have hHv : ∀ τ : ℍ, h2fun f ((1 : ℝ) +ᵥ τ) = h2fun f τ := h2fun_vadd_one hT2 hS
  have hMv : ∀ τ : ℍ, mfun f ((1 : ℝ) +ᵥ τ) = mfun f τ := mfun_vadd_one hT2 hS
  have hFv : ∀ τ : ℍ, F0fun f ((1 : ℝ) +ᵥ τ) = F0fun f τ := F0fun_vadd_one hT2 hS
  have hAper := periodic_comp_ofComplex_of_vadd_one hAv
  have hBper := periodic_comp_ofComplex_of_vadd_one hBv
  -- membership in 𝒫
  have hAinP : Work.Kernels.InP (fstDiff f) := inP_fstDiff hP
  have hBinP : Work.Kernels.InP (qzero f) := inP_qzero hP
  have hHinP : Work.Kernels.InP (h2fun f) := inP_h2fun hP
  have hMinP : Work.Kernels.InP (mfun f) := inP_mfun hP
  have hFinP : Work.Kernels.InP (F0fun f) := inP_F0fun hP
  -- boundedness at the cusp
  have hAbdd : IsBoundedAtImInfty (fstDiff f) := boundedAtImInfty_of_periodic_inP hAinP hAv
  have hBbdd : IsBoundedAtImInfty (qzero f) := boundedAtImInfty_of_periodic_inP hBinP hBv
  have hHbdd : IsBoundedAtImInfty (h2fun f) := boundedAtImInfty_of_periodic_inP hHinP hHv
  have hMbdd : IsBoundedAtImInfty (mfun f) := boundedAtImInfty_of_periodic_inP hMinP hMv
  have hFbdd : IsBoundedAtImInfty (F0fun f) := boundedAtImInfty_of_periodic_inP hFinP hFv
  -- decay at the cusp
  obtain ⟨CA, hCA0, hCA⟩ := fstDiff_q2_bound hmd hT2 hdec
  obtain ⟨CB, hCB0, hCB⟩ := QzeroOrderTwo hP hT2 hdec
  have hAdec : ∀ τ : ℍ, 1 ≤ τ.im →
      ‖fstDiff f τ‖ ≤ CA * Real.exp (-(2 * Real.pi * (2 : ℝ) * τ.im)) := by
    intro τ hτ
    rw [show -(2 * Real.pi * (2 : ℝ) * τ.im) = -(4 * Real.pi * τ.im) by ring]
    exact hCA τ hτ
  have hBdec : ∀ τ : ℍ, 1 ≤ τ.im →
      ‖qzero f τ‖ ≤ CB * Real.exp (-(2 * Real.pi * (2 : ℝ) * τ.im)) := by
    intro τ hτ
    rw [show -(2 * Real.pi * (2 : ℝ) * τ.im) = -(4 * Real.pi * τ.im) by ring]
    exact hCB τ hτ
  -- vanishing of the first two `q`-expansion coefficients of `A` and `B`
  have hqA0 : (qExpansion 1 (fstDiff f)).coeff 0 = 0 :=
    ExpDecayCoeffZero hCA0 (m := 2) hAper hAinP hAbdd hAdec 0 (by norm_num)
  have hqA1 : (qExpansion 1 (fstDiff f)).coeff 1 = 0 :=
    ExpDecayCoeffZero hCA0 (m := 2) hAper hAinP hAbdd hAdec 1 (by norm_num)
  have hqB0 : (qExpansion 1 (qzero f)).coeff 0 = 0 :=
    ExpDecayCoeffZero hCB0 (m := 2) hBper hBinP hBbdd hBdec 0 (by norm_num)
  have hqB1 : (qExpansion 1 (qzero f)).coeff 1 = 0 :=
    ExpDecayCoeffZero hCB0 (m := 2) hBper hBinP hBbdd hBdec 1 (by norm_num)
  -- the modular forms
  have hHγ : ∀ γ : SL(2, ℤ), h2fun f ∣[(10 : ℤ)] γ = h2fun f :=
    SlashInvariantForm.slash_action_generators_SL2Z (h2fun_slash_S hS) (h2fun_slash_T hT2 hS)
  obtain ⟨H, hH⟩ := Work.Modular.modularForm_of_slash_invariant hHγ hHinP.1 hHbdd
  have hMγ : ∀ γ : SL(2, ℤ), mfun f ∣[(12 : ℤ)] γ = mfun f :=
    SlashInvariantForm.slash_action_generators_SL2Z (mfun_slash_S hS) (mfun_slash_T hT2 hS)
  obtain ⟨M, hM⟩ := Work.Modular.modularForm_of_slash_invariant hMγ hMinP.1 hMbdd
  have hFγ : ∀ γ : SL(2, ℤ), F0fun f ∣[(14 : ℤ)] γ = F0fun f :=
    SlashInvariantForm.slash_action_generators_SL2Z (F0fun_slash_S hT2 hS) (F0fun_slash_T hT2 hS)
  obtain ⟨Fm, hFm⟩ := Work.Modular.modularForm_of_slash_invariant hFγ hFinP.1 hFbdd
  -- analyticity at the cusp
  have anH : AnalyticAt ℂ (cuspFunction 1 (h2fun f)) 0 := by
    rw [← hH]; exact analyticAt_cuspFunction_of_modularForm H
  have anM : AnalyticAt ℂ (cuspFunction 1 (mfun f)) 0 := by
    rw [← hM]; exact analyticAt_cuspFunction_of_modularForm M
  have anF : AnalyticAt ℂ (cuspFunction 1 (F0fun f)) 0 := by
    rw [← hFm]; exact analyticAt_cuspFunction_of_modularForm Fm
  have anE : AnalyticAt ℂ (cuspFunction 1 Work.Modular.E2) 0 := analyticAt_cuspFunction_E2
  have anHE : AnalyticAt ℂ (cuspFunction 1 (h2fun f * Work.Modular.E2)) 0 :=
    CuspFunctionMul anH anE
  have anME : AnalyticAt ℂ (cuspFunction 1 (mfun f * Work.Modular.E2)) 0 :=
    CuspFunctionMul anM anE
  have anHE2 : AnalyticAt ℂ (cuspFunction 1 (h2fun f * Work.Modular.E2 ^ 2)) 0 := by
    rw [E2_sq_eq]
    exact CuspFunctionMul anH (CuspFunctionMul anE anE)
  -- `q`-expansion identities
  have hQH : qExpansion 1 (h2fun f * Work.Modular.E2)
      = qExpansion 1 (h2fun f) * qExpansion 1 Work.Modular.E2 :=
    qExpansion_mul anH anE
  have hQM : qExpansion 1 (mfun f * Work.Modular.E2)
      = qExpansion 1 (mfun f) * qExpansion 1 Work.Modular.E2 :=
    qExpansion_mul anM anE
  have hQH2 : qExpansion 1 (h2fun f * Work.Modular.E2 ^ 2)
      = (qExpansion 1 (h2fun f) * qExpansion 1 Work.Modular.E2)
        * qExpansion 1 Work.Modular.E2 := by
    have h1 : (h2fun f * Work.Modular.E2 ^ 2 : ℍ → ℂ)
        = (h2fun f * Work.Modular.E2) * Work.Modular.E2 := by
      funext τ
      simp only [Pi.mul_apply, Pi.pow_apply]
      ring
    rw [h1, qExpansion_mul anHE anE, qExpansion_mul anH anE]
  have hBps : qExpansion 1 (qzero f)
      = ((Real.pi : ℂ) * Complex.I / 6) • (qExpansion 1 (h2fun f) * qExpansion 1 Work.Modular.E2)
        + (1 / 2 : ℂ) • qExpansion 1 (mfun f) := by
    rw [qzero_eq_mfun_smul f]
    rw [qExpansion_add (analyticAt_cuspFunction_smul _ anHE) (analyticAt_cuspFunction_smul _ anM),
      qExpansion_smul anHE, qExpansion_smul anM, hQH]
  have hAps : qExpansion 1 (fstDiff f)
      = qExpansion 1 (F0fun f)
        + ((Real.pi : ℂ) * Complex.I / 6) • (qExpansion 1 (mfun f) * qExpansion 1 Work.Modular.E2)
        - ((Real.pi : ℂ) ^ 2 / 36) • ((qExpansion 1 (h2fun f) * qExpansion 1 Work.Modular.E2)
            * qExpansion 1 Work.Modular.E2) := by
    rw [fstDiff_eq_F0fun_smul f]
    rw [qExpansion_sub (analyticAt_cuspFunction_add anF (analyticAt_cuspFunction_smul _ anME))
        (analyticAt_cuspFunction_smul _ anHE2),
      qExpansion_add anF (analyticAt_cuspFunction_smul _ anME),
      qExpansion_smul anME, qExpansion_smul anHE2, hQM, hQH2]
  -- the two low coefficients of `m`
  have hm0 : (qExpansion 1 (mfun f)).coeff 0
      = -((Real.pi : ℂ) * Complex.I / 3) * (qExpansion 1 (h2fun f)).coeff 0 := by
    have h := congrArg (fun p : PowerSeries ℂ => p.coeff 0) hBps
    simp only [map_add, map_smul, smul_eq_mul] at h
    simp only [psCoeff_zero_mul, E2_coeff_zero, mul_one, hqB0] at h
    linear_combination (-2 : ℂ) * h
  have hm1 : (qExpansion 1 (mfun f)).coeff 1
      = -((Real.pi : ℂ) * Complex.I / 3)
        * ((qExpansion 1 (h2fun f)).coeff 1 - 24 * (qExpansion 1 (h2fun f)).coeff 0) := by
    have h := congrArg (fun p : PowerSeries ℂ => p.coeff 1) hBps
    simp only [map_add, map_smul, smul_eq_mul] at h
    simp only [psCoeff_one_mul, E2_coeff_zero, E2_coeff_one, mul_one, hqB1] at h
    linear_combination (-2 : ℂ) * h
  -- the two low coefficients of `F₀`
  have hf0 : (qExpansion 1 (F0fun f)).coeff 0
      = -((Real.pi : ℂ) ^ 2 / 36) * (qExpansion 1 (h2fun f)).coeff 0 := by
    have h := congrArg (fun p : PowerSeries ℂ => p.coeff 0) hAps
    simp only [map_add, map_sub, map_smul, smul_eq_mul] at h
    simp only [psCoeff_zero_mul, E2_coeff_zero, mul_one, hqA0] at h
    have h' : (qExpansion 1 (F0fun f)).coeff 0
        = -((Real.pi : ℂ) * Complex.I / 6) * (qExpansion 1 (mfun f)).coeff 0
          + ((Real.pi : ℂ) ^ 2 / 36) * (qExpansion 1 (h2fun f)).coeff 0 := by
      linear_combination (-1 : ℂ) * h
    rw [h', hm0]
    exact F0_kill0 _
  have hf1 : (qExpansion 1 (F0fun f)).coeff 1
      = -((Real.pi : ℂ) ^ 2 / 36) * (qExpansion 1 (h2fun f)).coeff 1
        + 4 * (Real.pi : ℂ) ^ 2 / 3 * (qExpansion 1 (h2fun f)).coeff 0 := by
    have h := congrArg (fun p : PowerSeries ℂ => p.coeff 1) hAps
    simp only [map_add, map_sub, map_smul, smul_eq_mul] at h
    simp only [psCoeff_one_mul, psCoeff_zero_mul, E2_coeff_zero, E2_coeff_one, mul_one,
      hqA1] at h
    have h' : (qExpansion 1 (F0fun f)).coeff 1
        = -((Real.pi : ℂ) * Complex.I / 6)
            * ((qExpansion 1 (mfun f)).coeff 1 - 24 * (qExpansion 1 (mfun f)).coeff 0)
          + ((Real.pi : ℂ) ^ 2 / 36)
            * ((qExpansion 1 (h2fun f)).coeff 1 - 48 * (qExpansion 1 (h2fun f)).coeff 0) := by
      linear_combination (-1 : ℂ) * h
    rw [h', hm0, hm1]
    exact F0_kill1 _ _
  -- the ranks of the spaces of modular forms of weights `10` and `14`
  have hrank10 : Module.rank ℂ (ModularForm 𝒮ℒ ((10 : ℕ) : ℤ)) = 1 := by
    rw [ModularForm.dimension_level_one 10 ⟨5, by norm_num⟩]
    rw [if_neg (by decide : ¬ (10 ≡ 2 [MOD 12]))]
    norm_num
  have hrank14 : Module.rank ℂ (ModularForm 𝒮ℒ ((14 : ℕ) : ℤ)) = 1 := by
    rw [ModularForm.dimension_level_one 14 ⟨7, by norm_num⟩]
    rw [if_pos (by decide : 14 ≡ 2 [MOD 12])]
    norm_num
  -- the two coefficient relations
  have hHG := eq_smul_E (k := 10) (by norm_num) (by norm_num) hrank10 H
  have hFG := eq_smul_E (k := 14) (by norm_num) (by norm_num) hrank14 Fm
  have hc1 : (qExpansion 1 (h2fun f)).coeff 1
      = -264 * (qExpansion 1 (h2fun f)).coeff 0 := by
    have h := congrArg (fun (G : ModularForm 𝒮ℒ (10 : ℤ)) =>
      (UpperHalfPlane.qExpansion 1 (⇑G)).coeff 1) hHG
    rw [coeff_smul_E (k := 10) (by norm_num) _ 1, E10_coeff_one, hH] at h
    rw [h]; ring
  have hfr : (qExpansion 1 (F0fun f)).coeff 1
      = -24 * (qExpansion 1 (F0fun f)).coeff 0 := by
    have h := congrArg (fun (G : ModularForm 𝒮ℒ (14 : ℤ)) =>
      (UpperHalfPlane.qExpansion 1 (⇑G)).coeff 1) hFG
    rw [coeff_smul_E (k := 14) (by norm_num) _ 1, E14_coeff_one, hFm] at h
    rw [h]; ring
  -- the linear algebra
  have hc0 : (qExpansion 1 (h2fun f)).coeff 0 = 0 :=
    coeff_kill hf0 hf1 hfr hc1
  -- everything collapses
  have hcH : (qExpansion 1 (⇑H)).coeff 0 = 0 := by rw [hH]; exact hc0
  have hH0 : H = 0 := by rw [hHG, hcH, zero_smul]
  have hh2 : h2fun f = 0 := by rw [← hH, hH0]; rfl
  have hm0' : (qExpansion 1 (mfun f)).coeff 0 = 0 := by rw [hm0, hc0]; ring
  have hm1' : (qExpansion 1 (mfun f)).coeff 1 = 0 := by rw [hm1, hc1, hc0]; ring
  have hM0 : M = 0 := by
    apply ModularForm.sturm_bound_levelOne_nat (k := 12)
    rw [show (12 / 12 : ℕ) = 1 by norm_num]
    simp only [Nat.cast_one]
    refine lt_of_lt_of_le (by norm_num : (1 : ℕ∞) < 2) (PowerSeries.nat_le_order _ 2 ?_)
    intro i hi
    have hq : qExpansion 1 (⇑M) = qExpansion 1 (mfun f) := by rw [hM]
    rw [hq]
    interval_cases i
    · exact hm0'
    · exact hm1'
  have hm0fun : mfun f = 0 := by rw [← hM, hM0]; rfl
  have hFm0v : (qExpansion 1 (⇑Fm)).coeff 0 = 0 := by rw [hFm, hf0, hc0]; ring
  have hFmz : Fm = 0 := by rw [hFG, hFm0v, zero_smul]
  have hF0 : F0fun f = 0 := by rw [← hFm, hFmz]; rfl
  have hA0fun : fstDiff f = 0 := by
    rw [fstDiff_eq_F0fun_smul f, hF0, hm0fun, hh2]
    funext τ; simp
  have hB0fun : qzero f = 0 := by
    rw [qzero_eq_mfun_smul f, hm0fun, hh2]
    funext τ; simp
  rw [f_eq_qzero_add f, hB0fun, hA0fun]
  funext τ; simp

end Work.Rigidity
