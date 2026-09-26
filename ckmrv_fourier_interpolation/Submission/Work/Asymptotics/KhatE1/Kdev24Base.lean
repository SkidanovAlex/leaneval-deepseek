import Mathlib
import Submission.Work.Asymptotics.KhatE1Defs
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Residues.ThetaEpt
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Compact.kminus_tail_main
import Submission.Work.Asymptotics.Compact.kplus24_defs
import Submission.Work.Asymptotics.KhatE1.E1combo24_bound
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.KMinusFunnelJAtoms
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Kernels.LogLambda.ThetaLower.theta_lower_bound

/-!
# The `d = 24` sharp remainder: definitions and the exact splitting

This module holds the *definitions* `Am24`, `KdevLead24` and the proved lemmas

* `Am24_bound`, `KdevLead24_bound` — the magnitude of the leading coefficient;
* `R24_p0_eq_e1combo24'` — `Compact.R24_p0 = E1combo24`;
* `Sh_ne_zero_of_im_ge'` — `Sh τ z ≠ 0` on the funnel strip;
* `Kdev24RemCore_key` — the exact identity expressing the target's left-hand side as twice the
  leading-term-free deviation `Kdev ℓ 24 τ z - KdevLead24 ℓ τ · Ept z`.

They are split out of `KhatE1/Kdev24RemCore.lean` so that the `d = 24` sharp-remainder chain
(`KhatE1/Bracket24Defs.lean`, `KhatE1/Kdev24Lead.lean`, `KhatE1Core/Bracket24TailCore.lean`, …)
can sit *below* the target theorem `KhatE1.Kdev24RemCore` in the import graph.
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-- The `E(z)¹`-coefficient correction of the `K₋`-side deviation sum:
`A(τ) = -73728 Δ(τ) - 384 (ψ₂(τ)E₁₀(τ) - ψ₄(τ)E₈(τ))`. -/
noncomputable def Am24 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  -73728 * Work.Kernels.DeltaFun τ
    - 384 * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ
        - Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ)

/-- The leading `E(z)¹`-coefficient of the `d = 24` funnel deviation `Kdev`:
`(E1combo24 + A)/(6912π)`. -/
noncomputable def KdevLead24 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (Work.Asymptotics.E1combo24 ℓ τ + Am24 ℓ τ) / (6912 * (Real.pi : ℂ))

/-- `A = -73728Δ - 384(ψ₂E₁₀ - ψ₄E₈)` is `O(‖q(τ)‖ (scale τ)^N)` on the funnel. -/
theorem Am24_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      ‖Am24 ℓ τ‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ := by
  obtain ⟨C2, N2, hC2, hN2, h2⟩ := Work.Asymptotics.psi4E8_sub_psi2E10_funnel ℓ
  refine ⟨73728 * 2 + 384 * C2 + 1, N2, by positivity, hN2, fun τ hτ => ?_⟩
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hs0 : (0 : ℝ) ≤ Work.Kernels.scale τ := le_trans zero_le_one hs1
  have hsN : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N2 := Real.rpow_nonneg hs0 N2
  have hΔ : ‖Work.Kernels.DeltaFun τ‖ ≤ 2 * ‖Work.Kernels.qParamFun τ‖ :=
    Work.Asymptotics.DeltaFun_funnel_le τ hτ
  have hψ := h2 τ hτ
  have hψ' : ‖Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ
      - Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ‖ ≤ C2 * (Work.Kernels.scale τ) ^ N2
        * ‖Work.Kernels.qParamFun τ‖ := by
    rw [norm_sub_rev]
    exact hψ
  have hn1 : ‖(-73728 : ℂ)‖ = 73728 := by norm_num
  have e1 : ‖(-73728 : ℂ) * Work.Kernels.DeltaFun τ‖
      ≤ 73728 * 2 * (Work.Kernels.scale τ) ^ N2 * ‖Work.Kernels.qParamFun τ‖ := by
    rw [norm_mul, hn1]
    have h1s : (1 : ℝ) ≤ (Work.Kernels.scale τ) ^ N2 := Real.one_le_rpow hs1 hN2
    calc (73728 : ℝ) * ‖Work.Kernels.DeltaFun τ‖
        ≤ 73728 * (2 * ‖Work.Kernels.qParamFun τ‖) :=
          mul_le_mul_of_nonneg_left hΔ (by norm_num)
      _ = 73728 * 2 * ‖Work.Kernels.qParamFun τ‖ := by ring
      _ ≤ 73728 * 2 * (Work.Kernels.scale τ) ^ N2 * ‖Work.Kernels.qParamFun τ‖ := by
          have := mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) ≤ (Work.Kernels.scale τ) ^ N2) hq0
          nlinarith [this, hq0]
  have hn2 : ‖(384 : ℂ)‖ = 384 := by norm_num
  have e2 : ‖-(384 * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ
        - Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ))‖
      ≤ 384 * (C2 * (Work.Kernels.scale τ) ^ N2 * ‖Work.Kernels.qParamFun τ‖) := by
    rw [norm_neg, norm_mul, hn2]
    exact mul_le_mul_of_nonneg_left hψ' (by norm_num)
  rw [Am24, sub_eq_add_neg]
  refine le_trans (norm_add_le _ _) ?_
  have hsum : 73728 * 2 * (Work.Kernels.scale τ) ^ N2 * ‖Work.Kernels.qParamFun τ‖
      + 384 * (C2 * (Work.Kernels.scale τ) ^ N2 * ‖Work.Kernels.qParamFun τ‖)
      = (73728 * 2 + 384 * C2) * (Work.Kernels.scale τ) ^ N2
          * ‖Work.Kernels.qParamFun τ‖ := by ring
  refine le_trans (add_le_add e1 e2) ?_
  rw [hsum]
  refine mul_le_mul_of_nonneg_right ?_ hq0
  refine mul_le_mul_of_nonneg_right ?_ hsN
  linarith

/-- **The magnitude of the leading coefficient.**  `KdevLead24` is `O(‖q(τ)‖ (scale τ)^N)` on
the funnel. -/
theorem KdevLead24_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      ‖KdevLead24 ℓ τ‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨C1, N1, hC1, hN1, h1⟩ := Work.Asymptotics.KhatE1.E1combo24_bound ℓ
  obtain ⟨C2, N2, hC2, hN2, h2⟩ := Am24_bound ℓ
  refine ⟨(C1 + C2 + 1) / (6912 * Real.pi), max N1 N2, by positivity, le_max_of_le_left hN1,
    fun τ hτ => ?_⟩
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hs0 : (0 : ℝ) ≤ Work.Kernels.scale τ := le_trans zero_le_one hs1
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hsN1 : Work.Kernels.scale τ ^ N1 ≤ Work.Kernels.scale τ ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
  have hsN2 : Work.Kernels.scale τ ^ N2 ≤ Work.Kernels.scale τ ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
  have hE1 : ‖Work.Asymptotics.E1combo24 ℓ τ‖
      ≤ C1 * (Work.Kernels.scale τ) ^ (max N1 N2) * ‖Work.Kernels.qParamFun τ‖ := by
    refine le_trans (h1 τ hτ) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsN1 hC1.le) hq0
  have hAm : ‖Am24 ℓ τ‖
      ≤ C2 * (Work.Kernels.scale τ) ^ (max N1 N2) * ‖Work.Kernels.qParamFun τ‖ := by
    refine le_trans (h2 τ hτ) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsN2 hC2.le) hq0
  have hnum : ‖Work.Asymptotics.E1combo24 ℓ τ + Am24 ℓ τ‖
      ≤ (C1 + C2) * (Work.Kernels.scale τ) ^ (max N1 N2) * ‖Work.Kernels.qParamFun τ‖ := by
    refine le_trans (norm_add_le _ _) ?_
    have h : C1 * (Work.Kernels.scale τ) ^ (max N1 N2) * ‖Work.Kernels.qParamFun τ‖
        + C2 * (Work.Kernels.scale τ) ^ (max N1 N2) * ‖Work.Kernels.qParamFun τ‖
        = (C1 + C2) * (Work.Kernels.scale τ) ^ (max N1 N2) * ‖Work.Kernels.qParamFun τ‖ := by
      ring
    rw [← h]
    exact add_le_add hE1 hAm
  have hden : ‖(6912 : ℂ) * (Real.pi : ℂ)‖ = 6912 * Real.pi := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [KdevLead24, norm_div, hden]
  have hdenpos : (0 : ℝ) < 6912 * Real.pi := by positivity
  have hbase : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ (max N1 N2) * ‖Work.Kernels.qParamFun τ‖ :=
    mul_nonneg (Real.rpow_nonneg hs0 _) hq0
  calc ‖Work.Asymptotics.E1combo24 ℓ τ + Am24 ℓ τ‖ / (6912 * Real.pi)
      ≤ ((C1 + C2) * (Work.Kernels.scale τ) ^ (max N1 N2)
            * ‖Work.Kernels.qParamFun τ‖) / (6912 * Real.pi) :=
        div_le_div_of_nonneg_right hnum hdenpos.le
    _ = ((C1 + C2) / (6912 * Real.pi))
          * ((Work.Kernels.scale τ) ^ (max N1 N2) * ‖Work.Kernels.qParamFun τ‖) := by ring
    _ ≤ ((C1 + C2 + 1) / (6912 * Real.pi))
          * ((Work.Kernels.scale τ) ^ (max N1 N2) * ‖Work.Kernels.qParamFun τ‖) := by
        refine mul_le_mul_of_nonneg_right ?_ hbase
        exact div_le_div_of_nonneg_right (by linarith) hdenpos.le
    _ = (C1 + C2 + 1) / (6912 * Real.pi) * ‖Work.Kernels.qParamFun τ‖
          * (Work.Kernels.scale τ) ^ (max N1 N2) := by ring

/-- `R24_p0 = E1combo24`: the `E(z)¹`-coefficient of the `K₋`-reference bracket. -/
theorem R24_p0_eq_e1combo24' (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Asymptotics.Compact.R24_p0 ℓ τ = Work.Asymptotics.E1combo24 ℓ τ := by
  have hΔ : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  simp only [Work.Asymptotics.Compact.R24_p0, Work.Asymptotics.E1combo24]
  field_simp
  ring

/-- `Sh τ z ≠ 0` whenever `2 ≤ Im τ` and `Im τ + 1 ≤ Im z`: a point `z` with `j(z) = j(τ)` is a
`SL(2,ℤ)`-translate of `τ`, and every translate has imaginary part at most
`max (Im τ) (Im τ)⁻¹ = Im τ`. -/
theorem Sh_ne_zero_of_im_ge' (τ z : ℍ) (hτ : 2 ≤ τ.im) (hz : τ.im + 1 ≤ z.im) :
    Work.Asymptotics.Compact.Sh τ z ≠ 0 := by
  intro h0
  have hΔ : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  have hj : Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun z := by
    have h := Work.Asymptotics.Compact.DeltaFun_mul_sub τ z
    rw [h0, neg_zero] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hΔ)
  obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hj
  have hzγ : z = γ⁻¹ • τ := by
    rw [← hγ]
    exact (inv_smul_smul γ z).symm
  have h1 : z.im ≤ max τ.im (τ.im)⁻¹ := by
    rw [hzγ]
    exact Work.Kernels.LogLambda.ThetaLower.im_smul_le_max γ⁻¹ τ
  have h2 : max τ.im (τ.im)⁻¹ = τ.im :=
    max_eq_left (le_trans (inv_le_one_of_one_le₀ (by linarith)) (by linarith))
  rw [h2] at h1
  linarith

/-- **The exact splitting.**  On the funnel strip, the left-hand side of the target is twice the
leading-term-free deviation `Kdev - KdevLead24 · E(z)`. -/
theorem Kdev24RemCore_key (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0) :
    (Work.Kernels.KPlus 24 τ z - Work.Asymptotics.Compact.Gplus 24 τ z)
        + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
            (Work.Residues.Ept z * (Work.Asymptotics.Compact.R24 ℓ τ z
                - Work.Asymptotics.Compact.R24_p0 ℓ τ)
              + Work.Asymptotics.Compact.Dev24Sum ℓ τ z
              - Am24 ℓ τ * Work.Residues.Ept z)
      = 2 * (Work.Asymptotics.Kdev ℓ 24 τ z - KdevLead24 ℓ τ * Work.Residues.Ept z) := by
  have hpi : ((3456 : ℂ) * (Real.pi : ℂ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    exact_mod_cast Real.pi_ne_zero
  have htail := Work.Asymptotics.Compact.tail_identity ℓ 24 (Or.inr rfl) τ z hSh
  have hdec := Work.Asymptotics.Compact.decomp24_sum ℓ τ z hSh
  have hT := Work.Asymptotics.Compact.Tref24_eq ℓ τ z
  have hp0 := R24_p0_eq_e1combo24' ℓ τ
  have hK : Work.Asymptotics.Kdev ℓ 24 τ z
      = (Work.Kernels.KPlus 24 τ z - Work.Asymptotics.Compact.Gplus 24 τ z) / 2
        - (Work.Kernels.KMinus ℓ 24 τ z - Work.Asymptotics.Compact.Gminus 24 ℓ τ z) / 2 := by
    simp only [Work.Asymptotics.Kdev, Work.Kernels.Khat]
    ring
  have hKm : Work.Kernels.KMinus ℓ 24 τ z - Work.Asymptotics.Compact.Gminus 24 ℓ τ z
      = -(((3456 : ℂ) * (Real.pi : ℂ))⁻¹
            * ((Work.Asymptotics.Compact.Sh τ z)⁻¹
                * (Work.Asymptotics.Compact.brMinus ℓ 24 τ z
                    + Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.br0 24 ℓ τ z))) := by
    apply mul_left_cancel₀ hpi
    rw [htail]
    field_simp
  have hsplit : (Work.Asymptotics.Compact.Sh τ z)⁻¹
        * (Work.Asymptotics.Compact.brMinus ℓ 24 τ z
            + Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.br0 24 ℓ τ z)
      = Work.Residues.Ept z * Work.Asymptotics.Compact.R24 ℓ τ z
        + Work.Asymptotics.Compact.Dev24Sum ℓ τ z := by
    rw [hdec, hT]
  have hmain : 2 * (Work.Asymptotics.Kdev ℓ 24 τ z)
      = (Work.Kernels.KPlus 24 τ z - Work.Asymptotics.Compact.Gplus 24 τ z)
        + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
            (Work.Residues.Ept z * Work.Asymptotics.Compact.R24 ℓ τ z
              + Work.Asymptotics.Compact.Dev24Sum ℓ τ z) := by
    rw [hK, hKm, hsplit]
    field_simp
    ring
  have hlead : ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
        (Work.Residues.Ept z
          * (Work.Asymptotics.Compact.R24_p0 ℓ τ + Am24 ℓ τ))
      = 2 * (KdevLead24 ℓ τ * Work.Residues.Ept z) := by
    rw [KdevLead24, hp0]
    field_simp
    ring
  conv_rhs => rw [mul_sub]
  rw [hmain, ← hlead]
  ring

end

end Work.Asymptotics.KhatE1
