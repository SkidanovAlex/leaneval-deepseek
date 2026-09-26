import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Bracket24E2PrimeDefs
import Submission.Work.Asymptotics.KhatE1Core.psi_second_order
import Submission.Work.Asymptotics.KhatE1Core.EisensteinThreeTerm
import Submission.Work.Asymptotics.KhatE1.KdevE2fun_funnel
import Submission.Work.Asymptotics.KhatE1Core.Bracket24E2Prime_work2

set_option maxRecDepth 1000000

namespace Work.Asymptotics.KhatE1Core

open Work.Asymptotics.KhatE1

noncomputable section

/-- `Bracket24E2'` and `Bracket24E2` are the same explicit polynomial. -/
theorem Bracket24E2_prime_eq (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) :
    Bracket24E2' ℓ τ z = Work.Asymptotics.KhatE1.Bracket24E2 ℓ τ z := by
  unfold Bracket24E2' Work.Asymptotics.KhatE1.Bracket24E2
  ring

/-- The truncation identity `A₁κ̂ + qρ̂ = q²Δ₂` at `(τ,z)`. -/
theorem khat_rhat_identity (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) :
    A1q (Work.Kernels.qParamFun τ) * khatDef ℓ τ z
        + Work.Kernels.qParamFun τ * rhatDef ℓ τ z
      = (Work.Kernels.qParamFun τ) ^ 2 * delta2Fun ℓ τ z := by
  have hz : (z : ℂ) ≠ 0 := by
    intro h
    have h1 : ((z : ℂ)).im = 0 := by rw [h]; simp
    rw [UpperHalfPlane.coe_im] at h1
    exact (ne_of_gt z.im_pos) h1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hPZ : ((Real.pi : ℂ) * (z : ℂ)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero hpi hz)
  have h0 := kappahat_identity (Work.Kernels.qParamFun τ) (τ : ℂ) (z : ℂ)
      (Work.Asymptotics.Compact.cuspC ℓ) (Real.pi : ℂ)
  rw [KappaHatP_eq _ _ _ _ _ _ hz hpi, RestHatP_eq _ _ _ _ _ _ hz hpi] at h0
  have h1' : ((Real.pi : ℂ) * (z : ℂ)) ^ 2
        * (A1q (Work.Kernels.qParamFun τ) * khatDef ℓ τ z
            + Work.Kernels.qParamFun τ * rhatDef ℓ τ z)
      = (Work.Kernels.qParamFun τ) ^ 2
        * Poly2 (Work.Kernels.qParamFun τ) (τ : ℂ) (z : ℂ)
            (Work.Asymptotics.Compact.cuspC ℓ) (Real.pi : ℂ) := by
    rw [show khatDef ℓ τ z = KappaHat (Work.Kernels.qParamFun τ) (cuspLin ℓ τ) (τ : ℂ) (z : ℂ)
          (Work.Asymptotics.Compact.cuspC ℓ) (Real.pi : ℂ) from rfl,
        show rhatDef ℓ τ z = RestHat (Work.Kernels.qParamFun τ) (cuspLin ℓ τ) (τ : ℂ) (z : ℂ)
          (Work.Asymptotics.Compact.cuspC ℓ) (Real.pi : ℂ) from rfl,
        show cuspLin ℓ τ = (Real.pi : ℂ) * Complex.I * (τ : ℂ)
            + Work.Asymptotics.Compact.cuspC ℓ from rfl]
    rw [← h0]
    ring
  have hQ : (Work.Kernels.qParamFun τ) ^ 2 * delta2Fun ℓ τ z
      = ((Work.Kernels.qParamFun τ) ^ 2
          * Poly2 (Work.Kernels.qParamFun τ) (τ : ℂ) (z : ℂ)
              (Work.Asymptotics.Compact.cuspC ℓ) (Real.pi : ℂ))
        / ((Real.pi : ℂ) * (z : ℂ)) ^ 2 := by
    rw [show delta2Fun ℓ τ z = Poly2 (Work.Kernels.qParamFun τ) (τ : ℂ) (z : ℂ)
          (Work.Asymptotics.Compact.cuspC ℓ) (Real.pi : ℂ) / ((Real.pi : ℂ) * (z : ℂ)) ^ 2 from rfl]
    rw [mul_div_assoc]
  rw [hQ, eq_div_iff hPZ, mul_comm]
  exact h1'

/-- **The exact algebraic reduction.**
`Δ·Bracket24E2 = q²Δ₂ + devA₁·κ̂ + E₄³·(κ-κ̂) + (Δ-q)·ρ̂ + Δ·(ρ-ρ̂)`. -/
theorem delta_mul_bracket (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) :
    Work.Kernels.DeltaFun τ * Work.Asymptotics.KhatE1.Bracket24E2 ℓ τ z =
      (Work.Kernels.qParamFun τ) ^ 2 * delta2Fun ℓ τ z
      + devA1Fun τ * khatDef ℓ τ z
      + (Work.Kernels.E4Fun τ) ^ 3 * (Work.Asymptotics.KhatE1.Kappa ℓ τ z - khatDef ℓ τ z)
      + devD τ * rhatDef ℓ τ z
      + Work.Kernels.DeltaFun τ * (Work.Asymptotics.KhatE1.Rest ℓ τ z - rhatDef ℓ τ z) := by
  have hDj := Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ
  have hkey := khat_rhat_identity ℓ τ z
  rw [Work.Asymptotics.KhatE1.Bracket24E2_eq_Kappa_Rest ℓ τ z]
  simp only [devD, devA1Fun]
  rw [← hDj, ← hkey]
  ring

/-- The `Bound`-form of the reduction: `Δ·B₂` is `O(‖q‖²)`. -/
theorem delta_mul_bracket_bound (ℓ : Work.Kernels.LogLambdaData) :
    Bound (fun τ z => Work.Kernels.DeltaFun τ * Work.Asymptotics.KhatE1.Bracket24E2 ℓ τ z) 2 := by
  have hq2 : Bound (fun τ z => (Work.Kernels.qParamFun τ) ^ 2 * delta2Fun ℓ τ z) 2 :=
    boundQ2Delta2 ℓ
  have hda : Bound (fun τ z => devA1Fun τ * khatDef ℓ τ z) 2 :=
    (boundDevA1).mul (boundKhatDef ℓ)
  have hE4 : Bound (fun τ z => (Work.Kernels.E4Fun τ) ^ 3
      * (Work.Asymptotics.KhatE1.Kappa ℓ τ z - khatDef ℓ τ z)) 2 :=
    ((Bound.E4Fun).pow 3).mul (kappaDevBound ℓ)
  have hDq : Bound (fun τ z => devD τ * rhatDef ℓ τ z) 2 :=
    (Bound.devD).mul (boundRhatDef ℓ)
  have hDR : Bound (fun τ z => Work.Kernels.DeltaFun τ
      * (Work.Asymptotics.KhatE1.Rest ℓ τ z - rhatDef ℓ τ z)) 2 :=
    Bound.mono (by norm_num) ((Bound.DeltaFun).mul (restDevBound ℓ))
  have hsum := (((hq2.add hda).add hE4).add hDq).add hDR
  refine Bound.congr hsum ?_
  intro τ z
  rw [delta_mul_bracket ℓ τ z]

theorem Bracket24E2Prime_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.KhatE1Core.Bracket24E2' ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, hb1⟩ := delta_mul_bracket_bound ℓ
  refine ⟨2 * C1 + 1, max N1 0, max M1 0, by positivity, le_max_right _ _, le_max_right _ _,
    fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hb := hb1 τ z t hF ht hz0 hz1 hzim
  rw [norm_mul] at hb
  have hΔlow : (1 / 2) * ‖Work.Kernels.qParamFun τ‖ ≤ ‖Work.Kernels.DeltaFun τ‖ := by
    simpa only [Work.Asymptotics.norm_qParamFun]
      using Work.Asymptotics.DeltaFun_funnel_lower_sharp hF.2
  have hq0 : 0 < ‖Work.Kernels.qParamFun τ‖ :=
    norm_pos_iff.mpr (Work.Asymptotics.qParamFun_ne_zero' τ)
  have hle : (1 / 2) * ‖Work.Kernels.qParamFun τ‖
        * ‖Work.Asymptotics.KhatE1.Bracket24E2 ℓ τ z‖
      ≤ C1 * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
        * ‖Work.Kernels.qParamFun τ‖ ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_right hΔlow (norm_nonneg _)) hb
  have hstep : ‖Work.Asymptotics.KhatE1.Bracket24E2 ℓ τ z‖
      ≤ (C1 * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1 * ‖Work.Kernels.qParamFun τ‖ ^ 2)
        / ((1 / 2) * ‖Work.Kernels.qParamFun τ‖) := by
    rw [le_div_iff₀ (by positivity)]
    calc ‖Work.Asymptotics.KhatE1.Bracket24E2 ℓ τ z‖ * ((1 / 2) * ‖Work.Kernels.qParamFun τ‖)
        = (1 / 2) * ‖Work.Kernels.qParamFun τ‖
            * ‖Work.Asymptotics.KhatE1.Bracket24E2 ℓ τ z‖ := by ring
      _ ≤ C1 * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
            * ‖Work.Kernels.qParamFun τ‖ ^ 2 := hle
  have hsimp : (C1 * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1 * ‖Work.Kernels.qParamFun τ‖ ^ 2)
        / ((1 / 2) * ‖Work.Kernels.qParamFun τ‖)
      = 2 * C1 * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1 * ‖Work.Kernels.qParamFun τ‖ := by
    rw [div_eq_iff (by positivity : (((1 / 2 : ℝ) * ‖Work.Kernels.qParamFun τ‖)) ≠ 0)]
    ring
  rw [hsimp] at hstep
  have hS1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hS0 : (0 : ℝ) ≤ Work.Kernels.scale τ := le_of_lt (Work.Kernels.scale_pos τ)
  have hU1 : (1 : ℝ) ≤ 1 + t := by have := Work.Asymptotics.Funnel.im_one hF; linarith
  have hU0 : (0 : ℝ) ≤ 1 + t := by linarith
  have hq : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have e1 : 2 * C1 * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1 * ‖Work.Kernels.qParamFun τ‖
      ≤ 2 * C1 * (Work.Kernels.scale τ) ^ (max N1 0) * (1 + t) ^ (max M1 0)
        * ‖Work.Kernels.qParamFun τ‖ :=
    mul4_le le_rfl (Real.rpow_le_rpow_of_exponent_le hS1 (le_max_left _ _))
      (Real.rpow_le_rpow_of_exponent_le hU1 (le_max_left _ _)) le_rfl
      (by linarith) (Real.rpow_nonneg hS0 _) (Real.rpow_nonneg hU0 _) hq
  have e2 : 2 * C1 * (Work.Kernels.scale τ) ^ (max N1 0) * (1 + t) ^ (max M1 0)
        * ‖Work.Kernels.qParamFun τ‖
      ≤ (2 * C1 + 1) * (Work.Kernels.scale τ) ^ (max N1 0) * (1 + t) ^ (max M1 0)
        * ‖Work.Kernels.qParamFun τ‖ :=
    mul4_le (by linarith) le_rfl le_rfl le_rfl (by linarith)
      (Real.rpow_nonneg hS0 _) (Real.rpow_nonneg hU0 _) hq
  rw [Bracket24E2_prime_eq ℓ τ z]
  calc ‖Work.Asymptotics.KhatE1.Bracket24E2 ℓ τ z‖
      ≤ 2 * C1 * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
          * ‖Work.Kernels.qParamFun τ‖ := hstep
    _ ≤ (2 * C1 + 1) * (Work.Kernels.scale τ) ^ (max N1 0) * (1 + t) ^ (max M1 0)
          * ‖Work.Kernels.qParamFun τ‖ := le_trans e1 e2
    _ = (2 * C1 + 1) * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max N1 0)
          * (1 + t) ^ (max M1 0) := by ring

end

end Work.Asymptotics.KhatE1Core
