import Mathlib
import Submission.Work.Asymptotics.KMinusCuspBallDefs
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KMinusFunnelSlash
import Submission.Work.Asymptotics.KMinusFunnelZBounds
import Submission.Work.Asymptotics.KMinusFunnelZBoundsLS
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.KPlusFunnel.ZFacts
import Submission.Work.CKFinal.LineDecay.Ncusp24_zA_third
import Submission.Work.CKFinal.LineDecay.Ncusp24_zB_third
import Submission.Work.CKFinal.LineDecay.Ncusp24_V0LS_funnel
import Submission.Work.CKFinal.LineDecay.Ncusp24_V0L_funnel

/-!
# The `Ncusp`-funnel bound with no `z`-factor: `‖Δ(τ)·Ncusp ℓ 24 τ z‖ ≤ C(1+‖τ‖)^A e^{-π(4 Im τ + Im z)}`

This file proves `Work.CKFinal.LineDecay.Ncusp24_delta_funnel_zfree` (CKMRV Lemma 4.11 (4.42)
for `d = 24`, in the `Δ(τ)`-cleared form needed by the `slash_qtau_twentyfour` assembly).

## The decomposition

`Ncusp ℓ 24 τ z = (2·1728·π)⁻¹ T24 ℓ τ z` (`Ncusp_twentyfour_expansion`), and the *cancelled*
form of `T24` (`T24_cancelled`, proved in `KMinusFunnelSlash`) is

`T24 = -3456 Δ(τ)(E₁₄(z)/Δ(z))𝓛_S(z) + [(3456Δ(τ)+2D)(j(τ)-j(z)) + D j(τ) - 1728ψ₄(τ)E₈(τ)] V(z)
      + D (E₁₀(z)/Δ(z))(U(z)²-W(z)²)`,

with `D = ψ₄E₈ - ψ₂E₁₀`.  Multiplying by `Δ(z)Δ(τ)` and clearing the two `z`-denominators by means
of `Δ(z)j(z) = E₄(z)³` and `Δ(τ)j(τ) = E₄(τ)³` gives the exact identity `dk_mul_T24` below:

`Δ(z)Δ(τ)T24 = -3456Δ(τ)²·A(z) + Δ(τ)D(τ)·B(z) + (Δ(τ)𝒱₀(τ))·(Δ(z)V(z))`,

where the *composite* `z`-factors

`A(z) = E₁₄(z)𝓛_S(z) + E₄(z)³V(z)`,  `B(z) = E₁₀(z)(U(z)²-W(z)²) - 2E₄(z)³V(z)`

vanish to third order at the cusp `i∞`, while the `τ`-factor
`𝒱₀(τ) = 3456E₄(τ)³ + 3D(τ)j(τ) - 1728ψ₄(τ)E₈(τ)` is exponentially small on the funnel.  The two
`z`-atoms are the effective form of CKMRV's "the power series in `e^{πiz}` vanishes to the
asserted order" statement of Lemma 4.11: the leading `(Ept z)⁻¹`-pieces of `𝓛_S` and of
`(U²-W²)` cancel against the `E₄(z)³V(z)`-pieces, leaving `O(‖Ept z‖³)`.
-/

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

noncomputable section

/-- The composite `z`-atom `A(z) = E₁₄(z)·𝓛_S(z) + E₄(z)³·V(z)`; it is `O(‖Ept z‖³)`. -/
def NczA (ℓ : Work.Kernels.LogLambdaData) (z : UpperHalfPlane) : ℂ :=
  Work.Kernels.E14Fun z * ℓ.L_S z + Work.Kernels.E4Fun z ^ 3 * Work.Kernels.VFun z

/-- The composite `z`-atom `B(z) = E₁₀(z)(U(z)²-W(z)²) - 2E₄(z)³V(z)`; it is `O(‖Ept z‖³)`. -/
def NczB (z : UpperHalfPlane) : ℂ :=
  Work.Kernels.E10Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)
    - 2 * Work.Kernels.E4Fun z ^ 3 * Work.Kernels.VFun z

/-- `D(τ) = ψ₄(τ)E₈(τ) - ψ₂(τ)E₁₀(τ)`, the coefficient of the `z`-atom `B`. -/
def NcD (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ

/-- `𝒱₀(τ) = 3456E₄(τ)³ + 3D(τ)j(τ) - 1728ψ₄(τ)E₈(τ)`, the exponentially small `τ`-factor. -/
def NcV0 (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  3456 * Work.Kernels.E4Fun τ ^ 3 + 3 * NcD ℓ τ * Work.Kernels.jInvariantFun τ
    - 1728 * Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ

/-- **The clearing identity.**  Multiplying `T24` by `Δ(z)Δ(τ)` produces the fully holomorphic
combination of the composite atoms `A`, `B` and `Δ(z)V(z)`, with `τ`-coefficients
`Δ(τ)²`, `Δ(τ)D(τ)` and `Δ(τ)𝒱₀(τ)`. -/
lemma dk_mul_T24 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) :
    Work.Kernels.DeltaFun z * Work.Kernels.DeltaFun τ * Work.Asymptotics.T24 ℓ τ z
      = -3456 * Work.Kernels.DeltaFun τ ^ 2 * NczA ℓ z
        + Work.Kernels.DeltaFun τ * NcD ℓ τ * NczB z
        + (Work.Kernels.DeltaFun τ * NcV0 ℓ τ) * (Work.Kernels.DeltaFun z * Work.Kernels.VFun z) := by
  have hz : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  have hτ : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  rw [Work.Asymptotics.T24_cancelled]
  simp only [NczA, NczB, NcD, NcV0, Work.Kernels.jInvariantFun]
  field_simp
  ring

/-- **The `z`-atom `Δ(z)V(z)`.**  `‖Δ(z)V(z)‖ ≤ C e^{-3π Im z}` for `Im z ≥ 1/3`. -/
lemma delta_mul_V_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im →
      ‖Work.Kernels.DeltaFun z * Work.Kernels.VFun z‖
        ≤ C * Real.exp (-(Real.pi * z.im)) ^ 3 := by
  obtain ⟨Cd, hCd, hΔu⟩ := Work.Asymptotics.delta_upper_third
  obtain ⟨Cv, hCv, hVb⟩ := Work.Asymptotics.VFun_bound_third
  refine ⟨Cd * Cv + 1, by positivity, fun z hz => ?_⟩
  have h1 := hΔu z hz
  have h2 := hVb z hz
  have hq : ‖Work.Kernels.qParamFun z‖ = Real.exp (-(Real.pi * z.im)) ^ 2 := by
    rw [Work.Asymptotics.norm_qParamFun, sq, ← Real.exp_add]
    congr 1
    ring
  have h1' : ‖Work.Kernels.DeltaFun z‖ ≤ Cd * Real.exp (-(Real.pi * z.im)) ^ 2 :=
    (by simpa only [hq] using h1)
  rw [norm_mul]
  calc ‖Work.Kernels.DeltaFun z‖ * ‖Work.Kernels.VFun z‖
      ≤ (Cd * Real.exp (-(Real.pi * z.im)) ^ 2) * (Cv * Real.exp (-(Real.pi * z.im))) :=
        mul_le_mul h1' h2 (norm_nonneg _) (by positivity)
    _ = (Cd * Cv) * Real.exp (-(Real.pi * z.im)) ^ 3 := by ring
    _ ≤ (Cd * Cv + 1) * Real.exp (-(Real.pi * z.im)) ^ 3 := by
        apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)


/-- **The assembly.**  The two composite `z`-atom bounds (`A`, `B`), the `τ`-atom bound for `𝒱₀`
and the clearing identity `dk_mul_T24` imply the target bound. -/
theorem ncusp_delta_funnel_zfree_of (ℓ : Work.Kernels.LogLambdaData)
    (hA : ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im →
      ‖NczA ℓ z‖ ≤ C * Real.exp (-(Real.pi * z.im)) ^ 3)
    (hB : ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im →
      ‖NczB z‖ ≤ C * Real.exp (-(Real.pi * z.im)) ^ 3)
    (hV : ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖NcV0 ℓ τ‖ ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * τ.im)) ^ 2) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ τ z : UpperHalfPlane,
      τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → (1 : ℝ) / 3 ≤ z.im →
      ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Ncusp ℓ 24 τ z‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * (4 * τ.im + z.im))) := by
  obtain ⟨C1, hC1, hAz⟩ := hA
  obtain ⟨C2, hC2, hBz⟩ := hB
  obtain ⟨C3, A3, hC3, hA3, hVb⟩ := hV
  obtain ⟨cd, hcd, hΔl⟩ := Work.Asymptotics.delta_lower_third
  obtain ⟨CD, ND, hCD, hND, hDb⟩ := Work.Asymptotics.psi4E8_sub_psi2E10_funnel ℓ
  obtain ⟨C4, hC4, hΔV⟩ := delta_mul_V_bound
  have hA0 : 0 ≤ max ND A3 := le_trans hND (le_max_left ND A3)
  have hKpos : 0 < 4 * 3456 * C1 + 2 * CD * C2 * 3 ^ max ND A3 + 2 * C3 * C4 := by positivity
  refine ⟨‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖
      * ((4 * 3456 * C1 + 2 * CD * C2 * 3 ^ max ND A3 + 2 * C3 * C4) / cd) + 1,
    max ND A3, by positivity, hA0, ?_⟩
  intro τ z hτD hτ2 hz
  have hF : Work.Asymptotics.Funnel τ := ⟨hτD, hτ2⟩
  have hτ1 : (1 : ℝ) / 2 ≤ τ.im := by linarith
  have hsc : Work.Kernels.scale τ ≤ 3 * (1 + ‖(τ : ℂ)‖) := Work.Asymptotics.scale_le_three τ hτ1
  have hsc0 : (0 : ℝ) ≤ Work.Kernels.scale τ := (Work.Kernels.scale_pos τ).le
  have hs0 : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by positivity
  have hs1 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by have := norm_nonneg (τ : ℂ); linarith
  have hqτ : ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(Real.pi * τ.im)) ^ 2 := by
    rw [Work.Asymptotics.norm_qParamFun, sq, ← Real.exp_add] <;> ring_nf
  have hqz : ‖Work.Kernels.qParamFun z‖ = Real.exp (-(Real.pi * z.im)) ^ 2 := by
    rw [Work.Asymptotics.norm_qParamFun, sq, ← Real.exp_add] <;> ring_nf
  have hΔτ : ‖Work.Kernels.DeltaFun τ‖ ≤ 2 * Real.exp (-(Real.pi * τ.im)) ^ 2 := by
    have h := Work.Asymptotics.DeltaFun_funnel_le τ hF
    rw [hqτ] at h
    exact h
  have hDτ : ‖Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
        - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ‖
      ≤ CD * Work.Kernels.scale τ ^ ND * Real.exp (-(Real.pi * τ.im)) ^ 2 := by
    have h := hDb τ hF
    rw [hqτ] at h
    exact h
  have hV0τ : ‖NcV0 ℓ τ‖
      ≤ C3 * (1 + ‖(τ : ℂ)‖) ^ A3 * Real.exp (-(Real.pi * τ.im)) ^ 2 := hVb τ hF
  have hpA : (1 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ max ND A3 := Real.one_le_rpow hs1 hA0
  have hAz' := hAz z hz
  have hBz' := hBz z hz
  have hΔVz := hΔV z hz
  have hΔlz : cd * Real.exp (-(Real.pi * z.im)) ^ 2 ≤ ‖Work.Kernels.DeltaFun z‖ :=
    le_trans (le_of_eq (by rw [hqz])) (hΔl z hz)
  have hzt : (0 : ℝ) < Real.exp (-(Real.pi * z.im)) ^ 2 := pow_pos (by positivity) 2
  -- triangle inequality for the cleared identity
  have htri : ‖Work.Kernels.DeltaFun z * Work.Kernels.DeltaFun τ * Work.Asymptotics.T24 ℓ τ z‖
      ≤ 3456 * ‖Work.Kernels.DeltaFun τ‖ ^ 2 * ‖NczA ℓ z‖
        + ‖Work.Kernels.DeltaFun τ‖ * ‖NcD ℓ τ‖ * ‖NczB z‖
        + (‖Work.Kernels.DeltaFun τ‖ * ‖NcV0 ℓ τ‖)
          * ‖Work.Kernels.DeltaFun z * Work.Kernels.VFun z‖ := by
    rw [dk_mul_T24 ℓ τ z]
    have e1 : ‖-3456 * Work.Kernels.DeltaFun τ ^ 2 * NczA ℓ z‖
        = 3456 * ‖Work.Kernels.DeltaFun τ‖ ^ 2 * ‖NczA ℓ z‖ := by
      rw [norm_mul, norm_mul, norm_neg, norm_pow, Complex.norm_ofNat] <;> ring
    have e2 : ‖Work.Kernels.DeltaFun τ * NcD ℓ τ * NczB z‖
        = ‖Work.Kernels.DeltaFun τ‖ * ‖NcD ℓ τ‖ * ‖NczB z‖ := by
      rw [norm_mul, norm_mul] <;> ring
    have e3 : ‖(Work.Kernels.DeltaFun τ * NcV0 ℓ τ)
          * (Work.Kernels.DeltaFun z * Work.Kernels.VFun z)‖
        = (‖Work.Kernels.DeltaFun τ‖ * ‖NcV0 ℓ τ‖)
          * ‖Work.Kernels.DeltaFun z * Work.Kernels.VFun z‖ := by
      rw [norm_mul, norm_mul] <;> ring
    calc ‖-3456 * Work.Kernels.DeltaFun τ ^ 2 * NczA ℓ z
          + Work.Kernels.DeltaFun τ * NcD ℓ τ * NczB z
          + (Work.Kernels.DeltaFun τ * NcV0 ℓ τ) * (Work.Kernels.DeltaFun z * Work.Kernels.VFun z)‖
        ≤ ‖-3456 * Work.Kernels.DeltaFun τ ^ 2 * NczA ℓ z
            + Work.Kernels.DeltaFun τ * NcD ℓ τ * NczB z‖
          + ‖(Work.Kernels.DeltaFun τ * NcV0 ℓ τ)
              * (Work.Kernels.DeltaFun z * Work.Kernels.VFun z)‖ := norm_add_le _ _
      _ ≤ (‖-3456 * Work.Kernels.DeltaFun τ ^ 2 * NczA ℓ z‖
            + ‖Work.Kernels.DeltaFun τ * NcD ℓ τ * NczB z‖)
          + ‖(Work.Kernels.DeltaFun τ * NcV0 ℓ τ)
              * (Work.Kernels.DeltaFun z * Work.Kernels.VFun z)‖ := by
          have h := norm_add_le (-3456 * Work.Kernels.DeltaFun τ ^ 2 * NczA ℓ z)
            (Work.Kernels.DeltaFun τ * NcD ℓ τ * NczB z)
          linarith [h]
      _ = _ := by rw [e1, e2, e3]
  -- the three term bounds
  have hT1 : 3456 * ‖Work.Kernels.DeltaFun τ‖ ^ 2 * ‖NczA ℓ z‖
      ≤ (4 * 3456 * C1) * ((1 + ‖(τ : ℂ)‖) ^ max ND A3
          * (Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3)) := by
    have h1 : ‖Work.Kernels.DeltaFun τ‖ ^ 2 ≤ 4 * Real.exp (-(Real.pi * τ.im)) ^ 4 := by
      refine le_trans (pow_le_pow_left₀ (norm_nonneg _) hΔτ 2) (le_of_eq ?_)
      ring
    have ht4 : (0 : ℝ) ≤ Real.exp (-(Real.pi * τ.im)) ^ 4 := by positivity
    have hz3 : (0 : ℝ) ≤ Real.exp (-(Real.pi * z.im)) ^ 3 := by positivity
    have h5 : Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3
        ≤ (1 + ‖(τ : ℂ)‖) ^ max ND A3
          * (Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3) :=
      le_mul_of_one_le_left (mul_nonneg ht4 hz3) hpA
    calc 3456 * ‖Work.Kernels.DeltaFun τ‖ ^ 2 * ‖NczA ℓ z‖
        ≤ 3456 * (4 * Real.exp (-(Real.pi * τ.im)) ^ 4)
            * (C1 * Real.exp (-(Real.pi * z.im)) ^ 3) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) hAz' (norm_nonneg _)
            (by positivity)
      _ = (4 * 3456 * C1) * (Real.exp (-(Real.pi * τ.im)) ^ 4
            * Real.exp (-(Real.pi * z.im)) ^ 3) := by ring
      _ ≤ (4 * 3456 * C1) * ((1 + ‖(τ : ℂ)‖) ^ max ND A3
            * (Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3)) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
  have hT2 : ‖Work.Kernels.DeltaFun τ‖ * ‖NcD ℓ τ‖ * ‖NczB z‖
      ≤ (2 * CD * C2 * 3 ^ max ND A3) * ((1 + ‖(τ : ℂ)‖) ^ max ND A3
          * (Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3)) := by
    have h3s1 : (1 : ℝ) ≤ 3 * (1 + ‖(τ : ℂ)‖) := by nlinarith [hs1]
    have hscA : Work.Kernels.scale τ ^ ND
        ≤ 3 ^ max ND A3 * (1 + ‖(τ : ℂ)‖) ^ max ND A3 := by
      have h1 : Work.Kernels.scale τ ^ ND ≤ (3 * (1 + ‖(τ : ℂ)‖)) ^ ND :=
        Real.rpow_le_rpow hsc0 hsc hND
      have h2 : (3 * (1 + ‖(τ : ℂ)‖)) ^ ND ≤ (3 * (1 + ‖(τ : ℂ)‖)) ^ max ND A3 :=
        Real.rpow_le_rpow_of_exponent_le h3s1 (le_max_left ND A3)
      have h3 : (3 * (1 + ‖(τ : ℂ)‖)) ^ max ND A3
          = 3 ^ max ND A3 * (1 + ‖(τ : ℂ)‖) ^ max ND A3 :=
        Real.mul_rpow (by norm_num) hs0
      calc Work.Kernels.scale τ ^ ND ≤ (3 * (1 + ‖(τ : ℂ)‖)) ^ ND := h1
        _ ≤ (3 * (1 + ‖(τ : ℂ)‖)) ^ max ND A3 := h2
        _ = 3 ^ max ND A3 * (1 + ‖(τ : ℂ)‖) ^ max ND A3 := h3
    have ht4 : (0 : ℝ) ≤ Real.exp (-(Real.pi * τ.im)) ^ 4 := by positivity
    have hz3 : (0 : ℝ) ≤ Real.exp (-(Real.pi * z.im)) ^ 3 := by positivity
    have hstep : (2 * Real.exp (-(Real.pi * τ.im)) ^ 2)
          * (CD * Work.Kernels.scale τ ^ ND * Real.exp (-(Real.pi * τ.im)) ^ 2)
          * (C2 * Real.exp (-(Real.pi * z.im)) ^ 3)
        ≤ (2 * CD * C2) * (Work.Kernels.scale τ ^ ND)
            * (Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3) := by
      refine le_of_eq ?_
      ring
    have h6 : Work.Kernels.scale τ ^ ND * (Real.exp (-(Real.pi * τ.im)) ^ 4
          * Real.exp (-(Real.pi * z.im)) ^ 3)
        ≤ (3 ^ max ND A3 * (1 + ‖(τ : ℂ)‖) ^ max ND A3)
          * (Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3) :=
      mul_le_mul_of_nonneg_right hscA (mul_nonneg ht4 hz3)
    refine le_trans (mul_le_mul (mul_le_mul hΔτ hDτ (norm_nonneg _) (by positivity)) hBz'
      (norm_nonneg _) (by positivity)) ?_
    refine le_trans hstep ?_
    calc (2 * CD * C2) * Work.Kernels.scale τ ^ ND
          * (Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3)
        = (2 * CD * C2) * (Work.Kernels.scale τ ^ ND
            * (Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3)) := by ring
      _ ≤ (2 * CD * C2) * ((3 ^ max ND A3 * (1 + ‖(τ : ℂ)‖) ^ max ND A3)
            * (Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3)) :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = (2 * CD * C2 * 3 ^ max ND A3) * ((1 + ‖(τ : ℂ)‖) ^ max ND A3
            * (Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3)) := by ring
  have hT3 : (‖Work.Kernels.DeltaFun τ‖ * ‖NcV0 ℓ τ‖)
        * ‖Work.Kernels.DeltaFun z * Work.Kernels.VFun z‖
      ≤ (2 * C3 * C4) * ((1 + ‖(τ : ℂ)‖) ^ max ND A3
          * (Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3)) := by
    have hsA : (1 + ‖(τ : ℂ)‖) ^ A3 ≤ (1 + ‖(τ : ℂ)‖) ^ max ND A3 :=
      Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right ND A3)
    have ht4 : (0 : ℝ) ≤ Real.exp (-(Real.pi * τ.im)) ^ 4 := by positivity
    have hz3 : (0 : ℝ) ≤ Real.exp (-(Real.pi * z.im)) ^ 3 := by positivity
    have h8 : (2 * Real.exp (-(Real.pi * τ.im)) ^ 2)
          * (C3 * (1 + ‖(τ : ℂ)‖) ^ A3 * Real.exp (-(Real.pi * τ.im)) ^ 2)
          * (C4 * Real.exp (-(Real.pi * z.im)) ^ 3)
        = (2 * C3 * C4) * ((1 + ‖(τ : ℂ)‖) ^ A3
          * (Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3)) := by ring
    have hstep : (2 * Real.exp (-(Real.pi * τ.im)) ^ 2)
          * (C3 * (1 + ‖(τ : ℂ)‖) ^ A3 * Real.exp (-(Real.pi * τ.im)) ^ 2)
          * (C4 * Real.exp (-(Real.pi * z.im)) ^ 3)
        ≤ (2 * C3 * C4) * ((1 + ‖(τ : ℂ)‖) ^ max ND A3
          * (Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3)) := by
      rw [h8]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_right hsA (mul_nonneg ht4 hz3)
    refine le_trans (mul_le_mul (mul_le_mul hΔτ hV0τ (norm_nonneg _) (by positivity)) hΔVz
      (norm_nonneg _) (by positivity)) hstep
  have hmain : ‖Work.Kernels.DeltaFun z * Work.Kernels.DeltaFun τ * Work.Asymptotics.T24 ℓ τ z‖
      ≤ (4 * 3456 * C1 + 2 * CD * C2 * 3 ^ max ND A3 + 2 * C3 * C4)
        * ((1 + ‖(τ : ℂ)‖) ^ max ND A3
          * (Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3)) := by
    have hsum := add_le_add (add_le_add hT1 hT2) hT3
    have hfac : (4 * 3456 * C1) * ((1 + ‖(τ : ℂ)‖) ^ max ND A3
            * (Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3))
          + (2 * CD * C2 * 3 ^ max ND A3) * ((1 + ‖(τ : ℂ)‖) ^ max ND A3
            * (Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3))
          + (2 * C3 * C4) * ((1 + ‖(τ : ℂ)‖) ^ max ND A3
            * (Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3))
        = (4 * 3456 * C1 + 2 * CD * C2 * 3 ^ max ND A3 + 2 * C3 * C4)
          * ((1 + ‖(τ : ℂ)‖) ^ max ND A3
            * (Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3)) := by ring
    linarith [le_trans htri hsum, le_of_eq hfac]
  -- the final chain
  have hNc : Work.Kernels.DeltaFun τ * Work.Asymptotics.Ncusp ℓ 24 τ z
      = ((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹
        * (Work.Kernels.DeltaFun τ * Work.Asymptotics.T24 ℓ τ z) := by
    rw [Work.Asymptotics.Ncusp_twentyfour_expansion]; ring
  rw [hNc, norm_mul]
  have hq : ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.T24 ℓ τ z‖
      = ‖Work.Kernels.DeltaFun z * Work.Kernels.DeltaFun τ * Work.Asymptotics.T24 ℓ τ z‖
        / ‖Work.Kernels.DeltaFun z‖ := by
    have h1 : ‖Work.Kernels.DeltaFun z * Work.Kernels.DeltaFun τ * Work.Asymptotics.T24 ℓ τ z‖
        = ‖Work.Kernels.DeltaFun z‖
          * ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.T24 ℓ τ z‖ := by
      rw [mul_assoc, norm_mul]
    rw [h1, mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr
      (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z))]
  rw [hq]
  have hB0 : (0 : ℝ) ≤ 4 * 3456 * C1 + 2 * CD * C2 * 3 ^ max ND A3 + 2 * C3 * C4 := hKpos.le
  have hexp : Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3
      / Real.exp (-(Real.pi * z.im)) ^ 2
      = Real.exp (-(Real.pi * (4 * τ.im + z.im))) := by
    have h4 : Real.exp (-(Real.pi * τ.im)) ^ 4 = Real.exp (-(4 * (Real.pi * τ.im))) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h3 : Real.exp (-(Real.pi * z.im)) ^ 3 = Real.exp (-(3 * (Real.pi * z.im))) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h2 : Real.exp (-(Real.pi * z.im)) ^ 2 = Real.exp (-(2 * (Real.pi * z.im))) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have hsplit : Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3
        = Real.exp (-(Real.pi * (4 * τ.im + z.im))) * Real.exp (-(Real.pi * z.im)) ^ 2 := by
      rw [h4, h3, h2, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [hsplit, mul_div_cancel_right₀ _ (ne_of_gt (pow_pos (by positivity) 2))]
  have hdiv : ‖Work.Kernels.DeltaFun z * Work.Kernels.DeltaFun τ * Work.Asymptotics.T24 ℓ τ z‖
        / ‖Work.Kernels.DeltaFun z‖
      ≤ (4 * 3456 * C1 + 2 * CD * C2 * 3 ^ max ND A3 + 2 * C3 * C4) / cd
        * (1 + ‖(τ : ℂ)‖) ^ max ND A3 * Real.exp (-(Real.pi * (4 * τ.im + z.im))) := by
    refine le_trans (div_le_div_of_nonneg_right hmain (norm_nonneg _)) ?_
    refine le_trans (div_le_div_of_nonneg_left (by positivity) (mul_pos hcd hzt) hΔlz) ?_
    have h10 : (4 * 3456 * C1 + 2 * CD * C2 * 3 ^ max ND A3 + 2 * C3 * C4)
          * ((1 + ‖(τ : ℂ)‖) ^ max ND A3
            * (Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3))
          / (cd * Real.exp (-(Real.pi * z.im)) ^ 2)
        = ((4 * 3456 * C1 + 2 * CD * C2 * 3 ^ max ND A3 + 2 * C3 * C4) / cd)
          * (1 + ‖(τ : ℂ)‖) ^ max ND A3
          * (Real.exp (-(Real.pi * τ.im)) ^ 4 * Real.exp (-(Real.pi * z.im)) ^ 3
              / Real.exp (-(Real.pi * z.im)) ^ 2) := by
      field_simp <;> ring
    rw [h10, hexp]
  refine le_trans (mul_le_mul_of_nonneg_left hdiv (norm_nonneg _)) ?_
  have hconst : ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖
        * ((4 * 3456 * C1 + 2 * CD * C2 * 3 ^ max ND A3 + 2 * C3 * C4) / cd)
      ≤ ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖
        * ((4 * 3456 * C1 + 2 * CD * C2 * 3 ^ max ND A3 + 2 * C3 * C4) / cd) + 1 := by
    linarith
  calc ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖
        * ((4 * 3456 * C1 + 2 * CD * C2 * 3 ^ max ND A3 + 2 * C3 * C4) / cd
          * (1 + ‖(τ : ℂ)‖) ^ max ND A3 * Real.exp (-(Real.pi * (4 * τ.im + z.im))))
      = (‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖
        * ((4 * 3456 * C1 + 2 * CD * C2 * 3 ^ max ND A3 + 2 * C3 * C4) / cd))
        * (1 + ‖(τ : ℂ)‖) ^ max ND A3 * Real.exp (-(Real.pi * (4 * τ.im + z.im))) := by ring
    _ ≤ (‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖
        * ((4 * 3456 * C1 + 2 * CD * C2 * 3 ^ max ND A3 + 2 * C3 * C4) / cd) + 1)
        * (1 + ‖(τ : ℂ)‖) ^ max ND A3 * Real.exp (-(Real.pi * (4 * τ.im + z.im))) := by
        have hx : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ max ND A3
            * Real.exp (-(Real.pi * (4 * τ.im + z.im))) := by positivity
        nlinarith [hconst, hx]

/-- **The splitting of `𝒱₀`.**  `𝒱₀` is the sum of an `𝓛`-piece and the `𝓛_S`-piece `Ncusp24_V0LS`. -/
lemma NcV0_eq (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    NcV0 ℓ τ
      = (3456 * Work.Kernels.E4Fun τ ^ 3
          + (3 * Work.Kernels.jInvariantFun τ * Work.Residues.Yfun τ
              - 1728 * (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
                  - 2 * Work.Kernels.WFun τ ^ 2) * Work.Kernels.E8Fun τ) * ℓ.L_S τ)
        + (3 * Work.Kernels.jInvariantFun τ * Work.Residues.Xfun τ
            - 1728 * Work.Kernels.xi4Fun τ * Work.Kernels.E8Fun τ) * ℓ.L τ := by
  rw [NcV0, NcD, Work.Residues.psi4E8_sub ℓ τ]
  simp only [Work.Kernels.psi4, Work.Residues.Xfun, Work.Residues.Yfun,
    Work.Residues.xi4Fun_slash_S_apply]
  ring

/-- The `τ`-atom bound for `𝒱₀` follows from its two pieces. -/
theorem NcV0_funnel_bound_of (ℓ : Work.Kernels.LogLambdaData)
    (h1 : ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖3456 * Work.Kernels.E4Fun τ ^ 3
        + (3 * Work.Kernels.jInvariantFun τ * Work.Residues.Yfun τ
            - 1728 * (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
                - 2 * Work.Kernels.WFun τ ^ 2) * Work.Kernels.E8Fun τ) * ℓ.L_S τ‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * τ.im)) ^ 2)
    (h2 : ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖(3 * Work.Kernels.jInvariantFun τ * Work.Residues.Xfun τ
          - 1728 * Work.Kernels.xi4Fun τ * Work.Kernels.E8Fun τ) * ℓ.L τ‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * τ.im)) ^ 2) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖NcV0 ℓ τ‖ ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * τ.im)) ^ 2 := by
  obtain ⟨C1, A1, hC1, hA1, hf1⟩ := h1
  obtain ⟨C2, A2, hC2, hA2, hf2⟩ := h2
  refine ⟨C1 + C2 + 1, max A1 A2 + 1, by positivity, by positivity, fun τ hτ => ?_⟩
  have hs1 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by have := norm_nonneg (τ : ℂ); linarith
  have hs0 : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by linarith
  have e0 : (0 : ℝ) ≤ Real.exp (-(Real.pi * τ.im)) ^ 2 := by positivity
  have hp1 : (1 + ‖(τ : ℂ)‖) ^ A1 ≤ (1 + ‖(τ : ℂ)‖) ^ (max A1 A2 + 1) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (by linarith [le_max_left A1 A2])
  have hp2 : (1 + ‖(τ : ℂ)‖) ^ A2 ≤ (1 + ‖(τ : ℂ)‖) ^ (max A1 A2 + 1) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (by linarith [le_max_right A1 A2])
  have hb1 : C1 * (1 + ‖(τ : ℂ)‖) ^ A1 * Real.exp (-(Real.pi * τ.im)) ^ 2
      ≤ C1 * (1 + ‖(τ : ℂ)‖) ^ (max A1 A2 + 1) * Real.exp (-(Real.pi * τ.im)) ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ e0
    exact mul_le_mul_of_nonneg_left hp1 hC1.le
  have hb2 : C2 * (1 + ‖(τ : ℂ)‖) ^ A2 * Real.exp (-(Real.pi * τ.im)) ^ 2
      ≤ C2 * (1 + ‖(τ : ℂ)‖) ^ (max A1 A2 + 1) * Real.exp (-(Real.pi * τ.im)) ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ e0
    exact mul_le_mul_of_nonneg_left hp2 hC2.le
  rw [NcV0_eq ℓ τ]
  refine le_trans (norm_add_le _ _) ?_
  have hsum2 : C1 * (1 + ‖(τ : ℂ)‖) ^ (max A1 A2 + 1) * Real.exp (-(Real.pi * τ.im)) ^ 2
      + C2 * (1 + ‖(τ : ℂ)‖) ^ (max A1 A2 + 1) * Real.exp (-(Real.pi * τ.im)) ^ 2
      = (C1 + C2) * (1 + ‖(τ : ℂ)‖) ^ (max A1 A2 + 1) * Real.exp (-(Real.pi * τ.im)) ^ 2 := by
    ring
  have hle : (C1 + C2) * (1 + ‖(τ : ℂ)‖) ^ (max A1 A2 + 1) * Real.exp (-(Real.pi * τ.im)) ^ 2
      ≤ (C1 + C2 + 1) * (1 + ‖(τ : ℂ)‖) ^ (max A1 A2 + 1) * Real.exp (-(Real.pi * τ.im)) ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ e0
    exact mul_le_mul_of_nonneg_right (show C1 + C2 ≤ C1 + C2 + 1 by linarith)
      (Real.rpow_nonneg hs0 (max A1 A2 + 1))
  have hstep := add_le_add (le_trans (hf1 τ hτ) hb1) (le_trans (hf2 τ hτ) hb2)
  linarith [hstep, le_of_eq hsum2, hle]

/-- `𝒱₀` is exponentially small on the funnel. -/
theorem NcV0_funnel_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖NcV0 ℓ τ‖ ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * τ.im)) ^ 2 :=
  NcV0_funnel_bound_of ℓ (Ncusp24_V0LS_funnel ℓ) (Ncusp24_V0L_funnel ℓ)

/-- **CKMRV Lemma 4.11 (4.42) for `d = 24`, in `Δ(τ)`-cleared `z`-free form.** -/
theorem Ncusp24_delta_funnel_zfree (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ τ z : UpperHalfPlane,
      τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → (1 : ℝ) / 3 ≤ z.im →
      ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Ncusp ℓ 24 τ z‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A *
            Real.exp (-(Real.pi * (4 * τ.im + z.im))) := by
  obtain ⟨C1, hC1, h1⟩ := Ncusp24_zA_third ℓ
  obtain ⟨C2, hC2, h2⟩ := Ncusp24_zB_third
  refine ncusp_delta_funnel_zfree_of ℓ ⟨C1, hC1, fun z hz => ?_⟩ ⟨C2, hC2, fun z hz => ?_⟩
    (NcV0_funnel_bound ℓ)
  · simpa only [NczA] using h1 z hz
  · simpa only [NczB] using h2 z hz

end

end Work.CKFinal.LineDecay
