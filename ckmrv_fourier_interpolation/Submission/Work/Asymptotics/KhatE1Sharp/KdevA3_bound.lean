import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.BigCalc
import Submission.Work.Asymptotics.KhatE1Core.JmulBig
import Submission.Work.Asymptotics.KhatE1Core.E1combo8_second_order
import Submission.Work.Asymptotics.KhatE1Core.EisensteinThreeTerm
import Submission.Work.Asymptotics.KhatE1Core.jq_second_order
import Submission.Work.Asymptotics.KhatE1Core.psi_second_order
import Submission.Work.Asymptotics.KhatE1Sharp.KdevA3Defs
import Submission.Work.Asymptotics.KhatE1.E1combo8_bound

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-!
# The `E(z)³`-coefficient of the funnel bracket is `O(‖q(τ)‖ (scale τ)^N)`

`KdevA3 ℓ τ` (`KhatE1.KdevBracket_cleared`) is the `E(z)³`-coefficient of the residual
`Kdev8Bracket - 2·KdevE2·E(z)²`.  The proved identity `KhatE1.KdevA3_eq` writes it as

  `3456π·KdevA3 = (24 j(τ) - 21024)·E1combo8 ℓ τ - 2949120·E₄(τ) - 8847360·ψ₄(τ)`,

and the right-hand side is `O(‖q(τ)‖ (scale τ)^N)`: the `q⁰`-parts
`24·(737280Λ + 122880)` and `-2949120 - 8847360·2Λ` cancel exactly, the `q¹`-parts are of size
`(scale τ)`, and the remainders are the second-order expansions of `ψ₄`, `E₄`, `j` and of
`E1combo8` itself (`E1combo8_second_order`).
-/

private noncomputable def LamF (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ
private noncomputable def E4F (τ : ℍ) : ℂ := Work.Kernels.E4Fun τ
private noncomputable def psi4F (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  Work.Kernels.psi4 ℓ τ
private noncomputable def E1F (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  Work.Asymptotics.E1combo8 ℓ τ
private noncomputable def Tfun (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (737280 * LamF ℓ τ + 122880) * qAt τ
private noncomputable def Yfun (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (24 * jAt τ - 21024) * E1F ℓ τ - 2949120 * E4F τ - 8847360 * psi4F ℓ τ

/-! ## The decomposition of `Y` -/

private lemma Yfun_eq (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Yfun ℓ τ
      = 24 * (737280 * LamF ℓ τ + 122880) * 744 * qAt τ
        + 24 * (737280 * LamF ℓ τ + 122880) * (jAt τ * qAt τ - (1 + 744 * qAt τ))
        + 24 * jAt τ * (E1F ℓ τ - Tfun ℓ τ)
        - 21024 * E1F ℓ τ
        - 2949120 * (E4F τ - 1)
        - 8847360 * (psi4F ℓ τ - 2 * LamF ℓ τ) := by
  simp only [Yfun, Tfun, qAt, jAt, E1F, E4F, psi4F, LamF]
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

private lemma big_q1 : Big 1 (fun τ : ℍ => qAt τ) :=
  ⟨1, 0, one_pos, le_rfl, fun τ _ => by simp [qAt]⟩

private lemma big_q (k : ℕ) : Big k (fun τ : ℍ => qAt τ ^ k) := by
  have h := Big.pow big_q1 k
  rwa [one_mul] at h

/-- `737280·Λ + 122880` is `Big 0`. -/
private lemma big_Tcoef (ℓ : Work.Kernels.LogLambdaData) :
    Big 0 (fun τ : ℍ => 737280 * LamF ℓ τ + 122880) := by
  have h := Big.add (Big.const_mul (737280 : ℂ) (big_Lam ℓ)) (Big.const (122880 : ℂ))
  exact h.congr_on (fun τ _ => by try ring)

/-- `E1combo8` is `Big 1` (`E1combo8_bound`). -/
private lemma big_E1 (ℓ : Work.Kernels.LogLambdaData) : Big 1 (fun τ : ℍ => E1F ℓ τ) := by
  obtain ⟨C, N, hC, hN, hb⟩ := Work.Asymptotics.KhatE1.E1combo8_bound ℓ
  refine ⟨C, N, hC, hN, fun τ hτ => ?_⟩
  have h := hb τ hτ
  simpa only [E1F, qAt, pow_one] using h

/-- The second-order remainder of `E1combo8` is `Big 2`. -/
private lemma big_R (ℓ : Work.Kernels.LogLambdaData) :
    Big 2 (fun τ : ℍ => E1F ℓ τ - Tfun ℓ τ) := by
  obtain ⟨C, N, hC, hN, hb⟩ := E1combo8_second_order ℓ
  refine ⟨C, N, hC, hN, fun τ hτ => ?_⟩
  have h := hb τ hτ
  show ‖E1F ℓ τ - Tfun ℓ τ‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 2
  have hL : E1F ℓ τ - Tfun ℓ τ
      = Work.Asymptotics.E1combo8 ℓ τ
        - (737280 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
            + Work.Asymptotics.Compact.cuspC ℓ) + 122880) * Work.Kernels.qParamFun τ := by
    simp only [E1F, Tfun, LamF, qAt]; try ring
  rw [hL]
  simpa only [qAt, Work.Kernels.qParamFun] using h

/-- The second-order remainder of `j·q` is `Big 2`. -/
private lemma big_rj : Big 2 (fun τ : ℍ => jAt τ * qAt τ - (1 + 744 * qAt τ)) := by
  obtain ⟨Cj, hCj, hj⟩ := jq_second_order
  refine ⟨Cj, 0, hCj, le_rfl, fun τ hτ => ?_⟩
  have h := hj τ (by have := hτ.2; linarith)
  have hL : Work.Kernels.jInvariantFun τ * Work.Kernels.qParamFun τ - 1
      - 744 * Work.Kernels.qParamFun τ = jAt τ * qAt τ - (1 + 744 * qAt τ) := by
    simp only [qAt, jAt]; ring
  rw [hL] at h
  simpa [qAt, Real.rpow_zero] using h

/-- `E₄ - 1` is `Big 1`. -/
private lemma big_E4m1 : Big 1 (fun τ : ℍ => E4F τ - 1) := by
  obtain ⟨C, hC, h4, _⟩ := EisensteinThreeTerm
  have hE4 : Big 3 (fun τ : ℍ => Work.Kernels.E4Fun τ
      - 1 - 240 * qAt τ - 2160 * qAt τ ^ 2) := by
    refine ⟨C, 0, hC, le_rfl, fun τ hτ => ?_⟩
    show ‖Work.Kernels.E4Fun τ - 1 - 240 * (fun τ : ℍ => qAt τ) τ
        - 2160 * (fun τ : ℍ => qAt τ ^ 2) τ‖
      ≤ C * (Work.Kernels.scale τ) ^ (0 : ℝ) * ‖Work.Kernels.qParamFun τ‖ ^ 3
    have h := h4 τ (by have := hτ.2; linarith)
    simpa [qAt, Real.rpow_zero] using h
  have hq2 : Big 1 (fun τ : ℍ => 2160 * qAt τ ^ 2) :=
    (Big.const_mul (2160 : ℂ) (big_q 2)).mono (by norm_num)
  have hlin : Big 1 (fun τ : ℍ => 240 * qAt τ + 2160 * qAt τ ^ 2) :=
    Big.add (Big.const_mul (240 : ℂ) big_q1) hq2
  have hsum : Big 1 (fun τ : ℍ => (Work.Kernels.E4Fun τ - 1 - 240 * qAt τ - 2160 * qAt τ ^ 2)
      + (240 * qAt τ + 2160 * qAt τ ^ 2)) := Big.add hE4 hlin
  exact hsum.congr_on (fun τ _ => by simp only [E4F]; try ring)

/-- `ψ₄ - 2Λ` is `Big 1`. -/
private lemma big_psi4m (ℓ : Work.Kernels.LogLambdaData) :
    Big 1 (fun τ : ℍ => psi4F ℓ τ - 2 * LamF ℓ τ) := by
  obtain ⟨Cp, Np, hCp, hNp, hpsi⟩ := psi_second_order ℓ
  have hrest : Big 3 (fun τ : ℍ => psi4F ℓ τ - 2 * LamF ℓ τ
      + (288 * LamF ℓ τ + 744) * qAt τ + (1824 * LamF ℓ τ + 25972) * qAt τ ^ 2) := by
    refine ⟨Cp, Np, hCp, hNp, fun τ hτ => ?_⟩
    have h := (hpsi τ hτ).2
    convert h using 2
    simp only [psi4F, LamF, qAt]
    try ring
  have hlin : Big 1 (fun τ : ℍ => -((288 * LamF ℓ τ + 744) * qAt τ)
      - (1824 * LamF ℓ τ + 25972) * qAt τ ^ 2) := by
    have h1 : Big 1 (fun τ : ℍ => (288 * LamF ℓ τ + 744) * qAt τ) :=
      ((Big.add (Big.const_mul (288 : ℂ) (Big.mul (big_Lam ℓ) big_q1))
        (Big.const_mul (744 : ℂ) big_q1)).congr_on (fun τ _ => by try ring))
    have h2 : Big 1 (fun τ : ℍ => (1824 * LamF ℓ τ + 25972) * qAt τ ^ 2) :=
      ((Big.add (Big.const_mul (1824 : ℂ) (Big.mul (big_Lam ℓ) (big_q 2)))
        (Big.const_mul (25972 : ℂ) (big_q 2))).congr_on (fun τ _ => by try ring)).mono
        (by norm_num)
    exact Big.sub (Big.neg h1) h2
  have hsum : Big 1 (fun τ : ℍ => (psi4F ℓ τ - 2 * LamF ℓ τ
      + (288 * LamF ℓ τ + 744) * qAt τ + (1824 * LamF ℓ τ + 25972) * qAt τ ^ 2)
      + (-((288 * LamF ℓ τ + 744) * qAt τ) - (1824 * LamF ℓ τ + 25972) * qAt τ ^ 2)) :=
    Big.add hrest hlin
  exact hsum.congr_on (fun τ _ => by try ring)

/-! ## The bound on `Y` and on `KdevA3` -/

private lemma big_Y (ℓ : Work.Kernels.LogLambdaData) : Big 1 (fun τ : ℍ => Yfun ℓ τ) := by
  have h1 : Big 1 (fun τ : ℍ => 24 * (737280 * LamF ℓ τ + 122880) * 744 * qAt τ) :=
    (Big.mul (Big.const_mul (24 * 744 : ℂ) (big_Tcoef ℓ)) big_q1).congr_on
      (fun τ _ => by try ring)
  have h2 : Big 2 (fun τ : ℍ => 24 * (737280 * LamF ℓ τ + 122880)
      * (jAt τ * qAt τ - (1 + 744 * qAt τ))) :=
    (Big.mul (Big.const_mul (24 : ℂ) (big_Tcoef ℓ)) big_rj).congr_on (fun τ _ => by try ring)
  have h3 : Big 1 (fun τ : ℍ => 24 * jAt τ * (E1F ℓ τ - Tfun ℓ τ)) :=
    (Big.const_mul (24 : ℂ) (Big.mul (jmul2 (big_R ℓ)) (Big.one))).congr_on
      (fun τ _ => by try ring)
  have h4 : Big 1 (fun τ : ℍ => 21024 * E1F ℓ τ) := Big.const_mul (21024 : ℂ) (big_E1 ℓ)
  have h5 : Big 1 (fun τ : ℍ => 2949120 * (E4F τ - 1)) :=
    Big.const_mul (2949120 : ℂ) big_E4m1
  have h6 : Big 1 (fun τ : ℍ => 8847360 * (psi4F ℓ τ - 2 * LamF ℓ τ)) :=
    Big.const_mul (8847360 : ℂ) (big_psi4m ℓ)
  have hsum : Big 1 (fun τ : ℍ => 24 * (737280 * LamF ℓ τ + 122880) * 744 * qAt τ
      + 24 * (737280 * LamF ℓ τ + 122880) * (jAt τ * qAt τ - (1 + 744 * qAt τ))
      + 24 * jAt τ * (E1F ℓ τ - Tfun ℓ τ)
      - 21024 * E1F ℓ τ - 2949120 * (E4F τ - 1) - 8847360 * (psi4F ℓ τ - 2 * LamF ℓ τ)) :=
    Big.sub (Big.sub (Big.sub (Big.add (Big.add h1 h2) h3) h4) h5) h6
  exact hsum.congr_on (fun τ _ => (Yfun_eq ℓ τ).symm)

private lemma big_KdevA3 (ℓ : Work.Kernels.LogLambdaData) :
    Big 1 (fun τ : ℍ => Work.Asymptotics.KhatE1.KdevA3 ℓ τ) := by
  have hpi : ((3456 : ℂ) * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have h : Big 1 (fun τ : ℍ => ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * Yfun ℓ τ) :=
    Big.const_mul (((3456 : ℂ) * (Real.pi : ℂ))⁻¹) (big_Y ℓ)
  refine h.congr_on (fun τ hτ => ?_)
  have hk := Work.Asymptotics.KhatE1.KdevA3_eq ℓ τ hτ
  have hY : Yfun ℓ τ = (24 * Work.Kernels.jInvariantFun τ - 21024)
        * Work.Asymptotics.E1combo8 ℓ τ
      - 2949120 * Work.Kernels.E4Fun τ - 8847360 * Work.Kernels.psi4 ℓ τ := by
    simp only [Yfun, jAt, E1F, E4F, psi4F]; try ring
  rw [hY, ← hk, ← mul_assoc, inv_mul_cancel₀ hpi, one_mul]

/-- **The `E(z)³`-coefficient of the residual bracket is `O(‖q(τ)‖ (scale τ)^N)`.** -/
theorem KdevA3_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      ‖Work.Asymptotics.KhatE1.KdevA3 ℓ τ‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ := by
  obtain ⟨C, N, hC, hN, hb⟩ := big_KdevA3 ℓ
  exact ⟨C, N, hC, hN, fun τ hτ => by
    have h := hb τ hτ
    simpa only [qAt, pow_one] using h⟩

end

end Work.Asymptotics.KhatE1Core
