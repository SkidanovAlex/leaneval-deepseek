/-
# Bounds for the atoms of the cusp-`i∞` expansion of `K_-` on the tail region

This file proves `Work.Asymptotics.Compact.kminus_tail_aux`: on the region `z.im ≥ H`,
uniformly for `τ` in a compact `K ⊆ ℍ`, every atom entering the cusp expansion of `K_-`
(the reference values `Dref`, `Sinvref`, `Wref`, `D2ref`, `Lref`, `E14ref`, `E10ref`, the
deviations `dDelta`, `dSinv`, `dW`, `dD2`, `dL`, `dE14`, `dE10`, and the atoms `A24`, `A24ref`,
`C24`, `B24`, `ψ₂`, `ψ₄`, `E₄`, `E₆`, `E₈`, `E₁₀`, `Δ`, `j`) is bounded by the corresponding
power of `‖Ept z‖ = e^{-π z.im}` (for the quantities vanishing at the cusp) or by a constant
resp. by `C(1+‖z‖)` (for the quantities that stay finite there).

The proofs use the second order cusp expansions of the level one modular forms
(`cusp_invDelta`, `cusp_W_second`, `cusp_D_second`, `cusp_L_second`,
`cusp_inv_divisor_second`) and, for the higher order deviations `dE14`, `dE10`, the
`CuspEst` calculus of `Submission.Work.Asymptotics.KMinusCuspBallLimit` fed with the
two-term `q`-expansions of `E₄` and `E₆` (`E4Fun_two_term`, `E6Fun_two_term`).  Boundedness of
the `τ`-atoms on the compact `K` is supplied by `IsCompact.exists_bound_of_continuousOn` and
the continuity lemmas of `Ncusp_bound_ball`.
-/
import Mathlib
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Compact.kminus_tail_bounds
import Submission.Work.Asymptotics.Ncusp_bound_ball
import Submission.Work.Asymptotics.MiddleRange.Basic
import Submission.Work.Asymptotics.Compact.kaux_A24_est
import Submission.Work.Asymptotics.Compact.kaux_A24ref_est

noncomputable section

open UpperHalfPlane

namespace Work.Asymptotics.Compact

open Work.Kernels
open Work.Residues (Ept Ept_ne_zero)

/-! ## Toolbox -/

/-- A `CuspEst` (`‖f z‖ ≤ C·tpar z ^ k` for large `z.im`) rephrased with a positive threshold
and the `‖Ept z‖ ^ k` shape used throughout this file. -/
lemma kaux_est_of_cuspEst {f : ℍ → ℂ} {k : ℕ} (h : Work.Asymptotics.CuspEst f k) :
    ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ z : ℍ, H ≤ z.im → ‖f z‖ ≤ C * ‖Ept z‖ ^ k := by
  obtain ⟨H, C, hC, hb⟩ := h
  refine ⟨max H 1, C, lt_of_lt_of_le zero_lt_one (le_max_right _ _), hC, fun z hz => ?_⟩
  rw [← Work.Residues.tpar_eq_norm_Ept z]
  exact hb z (le_trans (le_max_left _ _) hz)

/-- A `CuspEst` gives an honest boundedness statement (since `tpar z ≤ 1`). -/
lemma kaux_bdd_of_cuspEst {f : ℍ → ℂ} {k : ℕ} (h : Work.Asymptotics.CuspEst f k) :
    ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ z : ℍ, H ≤ z.im → ‖f z‖ ≤ C := by
  obtain ⟨H, C, hC, hb⟩ := h
  refine ⟨max H 1, C, lt_of_lt_of_le zero_lt_one (le_max_right _ _), hC, fun z hz => ?_⟩
  have ht : Work.Residues.tpar z ^ k ≤ 1 :=
    pow_le_one₀ (Work.Residues.tpar_nonneg z) (Work.Residues.tpar_le_one z)
  calc ‖f z‖ ≤ C * Work.Residues.tpar z ^ k := hb z (le_trans (le_max_left _ _) hz)
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left ht hC.le
    _ = C := mul_one C

/-- A continuous function is bounded on a compact subset of `ℍ`. -/
lemma kaux_bound_compact {F : ℍ → ℂ} {K : Set ℍ} (hK : IsCompact K) (hF : Continuous F) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ K, ‖F τ‖ ≤ C := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  exact ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun τ hτ => le_trans (hB τ hτ) (le_max_left _ _)⟩

/-- `‖Ept z‖ ≤ 1` for `z.im ≥ 1`. -/
lemma kaux_norm_Ept_le_one {z : ℍ} (hz : 1 ≤ z.im) : ‖Ept z‖ ≤ 1 := by
  rw [Work.Residues.norm_Ept]
  exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hz])

/-- `‖Xc ℓ z‖ ≤ (π + ‖cuspC ℓ‖)(1 + ‖z‖)`. -/
lemma kaux_norm_Xc_le (ℓ : LogLambdaData) (z : ℍ) :
    ‖Xc ℓ z‖ ≤ (Real.pi + ‖cuspC ℓ‖) * (1 + ‖(z : ℂ)‖) := by
  have hX : ‖Xc ℓ z‖ ≤ Real.pi * ‖(z : ℂ)‖ + ‖cuspC ℓ‖ := by
    rw [Xc]
    calc ‖(Real.pi : ℂ) * Complex.I * (z : ℂ) + cuspC ℓ‖
        ≤ ‖(Real.pi : ℂ) * Complex.I * (z : ℂ)‖ + ‖cuspC ℓ‖ := norm_add_le _ _
      _ = Real.pi * ‖(z : ℂ)‖ + ‖cuspC ℓ‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
  nlinarith [hX, Real.pi_pos, norm_nonneg (cuspC ℓ), norm_nonneg (z : ℂ)]

/-- If `1 ≤ c` and `0 ≤ t`, then `a·t + b·(c·t) ≤ (a+b)·(c·t)` for `a, b ≥ 0`. -/
lemma kaux_add_mul_le {a b c t : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b) (ht : 0 ≤ t) (hc : 1 ≤ c) :
    a * t + b * c * t ≤ (a + b) * c * t := by
  have h1 : a * t ≤ a * c * t := by
    have h2 : a * 1 ≤ a * c := mul_le_mul_of_nonneg_left hc ha
    rw [mul_one] at h2
    simpa using mul_le_mul_of_nonneg_right h2 ht
  have h3 : b * c * t ≤ (a + b) * c * t :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (le_trans zero_le_one hc)) ht
  linarith

/-! ## Two-term expansions of `E₄`, `E₆` as `CuspEst`s -/

/-- `E₄ = 1 + 240 E² + O(‖E‖⁴)`. -/
lemma kaux_cuspEst_E4_two :
    Work.Asymptotics.CuspEst (fun z : ℍ => E4Fun z - 1 - 240 * (Ept z) ^ 2) 4 := by
  obtain ⟨C, hC, h⟩ := E4_two_term_core
  refine ⟨1, C, hC, fun z hz => ?_⟩
  have h' := h z hz
  rw [qParamFun_eq_Ept_sq z] at h'
  have h2 : ‖(Ept z) ^ 2‖ ^ 2 = Work.Residues.tpar z ^ 4 := by
    rw [norm_pow, ← Work.Residues.tpar_eq_norm_Ept z]; ring
  rwa [h2] at h'

/-- `E₆ = 1 - 504 E² + O(‖E‖⁴)`. -/
lemma kaux_cuspEst_E6_two :
    Work.Asymptotics.CuspEst (fun z : ℍ => E6Fun z - 1 + 504 * (Ept z) ^ 2) 4 := by
  obtain ⟨C, hC, h⟩ := E6_two_term_core
  refine ⟨1, C, hC, fun z hz => ?_⟩
  have h' := h z hz
  rw [qParamFun_eq_Ept_sq z] at h'
  have h2 : ‖(Ept z) ^ 2‖ ^ 2 = Work.Residues.tpar z ^ 4 := by
    rw [norm_pow, ← Work.Residues.tpar_eq_norm_Ept z]; ring
  rwa [h2] at h'

/-! ## The deviations of the `z`-atoms -/

/-- `Δ(z)⁻¹ = E⁻² + 24 + O(‖E‖²)`: the deviation `dDelta` is `O(‖E‖²)`. -/
lemma kaux_dDelta : ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ z : ℍ, H ≤ z.im →
    ‖dDelta z‖ ≤ C * ‖Ept z‖ ^ 2 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.cusp_invDelta
  refine ⟨1, C, one_pos, hC, fun z hz => ?_⟩
  simpa [dDelta, Dref, einv2] using h z hz

/-- `dW = W - Wref = O(‖E‖³)`. -/
lemma kaux_dW : ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ z : ℍ, H ≤ z.im →
    ‖dW z‖ ≤ C * ‖Ept z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.cusp_W_second
  refine ⟨1, C, one_pos, hC, fun z hz => ?_⟩
  simpa [dW, Wref] using h z hz

/-- `dD2 = (U² - V²) - D2ref = O(‖E‖³)`. -/
lemma kaux_dD2 : ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ z : ℍ, H ≤ z.im →
    ‖dD2 z‖ ≤ C * ‖Ept z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.cusp_D_second
  refine ⟨1, C, one_pos, hC, fun z hz => ?_⟩
  simpa [dD2, D2ref] using h z hz

/-- `dL = 𝓛 - Lref = O(‖E‖³)`. -/
lemma kaux_dL (ℓ : LogLambdaData) : ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ z : ℍ, H ≤ z.im →
    ‖dL ℓ z‖ ≤ C * ‖Ept z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := cuspC_spec ℓ
  refine ⟨1, C, one_pos, hC, fun z hz => ?_⟩
  simpa [dL, Lref, Xc] using h z hz

/-- `dSinv = (Sh)⁻¹ - Sinvref = O(‖E‖⁴)`, uniformly for `τ ∈ K`. -/
lemma kaux_dSinv {K : Set ℍ} (hK : IsCompact K) :
    ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ (τ z : ℍ), τ ∈ K → H ≤ z.im →
      ‖dSinv τ z‖ ≤ C * ‖Ept z‖ ^ 4 := by
  obtain ⟨T, hT, C, hC, h⟩ := Work.Asymptotics.cusp_inv_divisor_second (K := K) hK
  refine ⟨max T 1, C, lt_of_lt_of_le zero_lt_one (le_max_right _ _), hC, fun τ z hτ hz => ?_⟩
  have h1 := h τ hτ z (le_trans (le_max_left _ _) hz)
  have hd : dSinv τ z = -((DeltaFun z * (jInvariantFun τ - jInvariantFun z))⁻¹ + 1
      - (720 - jInvariantFun τ) * (Ept z) ^ 2) := by
    simp only [dSinv, Sinvref, Sh_eq, inv_neg]
    ring
  rw [hd, norm_neg]
  exact h1

/-! ## The fourth order deviations `dE14`, `dE10` -/

/-- `E₁₄ = E₄²E₆ = 1 - 24 E² + O(‖E‖⁴)`, i.e. `dE14 = O(‖E‖⁴)`. -/
lemma kaux_dE14 : ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ z : ℍ, H ≤ z.im →
    ‖dE14 z‖ ≤ C * ‖Ept z‖ ^ 4 := by
  have hδ : Work.Asymptotics.CuspEst (fun z : ℍ => E4Fun z - 1 - 240 * (Ept z) ^ 2) 4 :=
    kaux_cuspEst_E4_two
  have hε : Work.Asymptotics.CuspEst (fun z : ℍ => E6Fun z - 1 + 504 * (Ept z) ^ 2) 4 :=
    kaux_cuspEst_E6_two
  have hq : Work.Asymptotics.CuspEst (fun z : ℍ => (Ept z) ^ 2) 2 :=
    Work.Asymptotics.cuspEst_Ept_pow 2
  have hE6 : Work.Asymptotics.CuspEst (fun z : ℍ => E6Fun z) 0 := Work.Asymptotics.cuspEst_E6Fun
  have h4 : Work.Asymptotics.CuspEst (fun z : ℍ => (Ept z) ^ 4) 4 :=
    (hq.mul hq).congr (fun z => by ring)
  have h1 : Work.Asymptotics.CuspEst (fun z : ℍ => 57600 * (Ept z) ^ 4
      + 2 * (E4Fun z - 1 - 240 * (Ept z) ^ 2)
      + 480 * (Ept z) ^ 2 * (E4Fun z - 1 - 240 * (Ept z) ^ 2)
      + (E4Fun z - 1 - 240 * (Ept z) ^ 2) ^ 2) 4 := by
    have hA : Work.Asymptotics.CuspEst (fun z : ℍ => 57600 * (Ept z) ^ 4) 4 :=
      Work.Asymptotics.CuspEst.const_mul (57600 : ℂ) h4
    have hB : Work.Asymptotics.CuspEst
        (fun z : ℍ => 2 * (E4Fun z - 1 - 240 * (Ept z) ^ 2)) 4 :=
      Work.Asymptotics.CuspEst.const_mul (2 : ℂ) hδ
    have hC : Work.Asymptotics.CuspEst
        (fun z : ℍ => 480 * ((Ept z) ^ 2 * (E4Fun z - 1 - 240 * (Ept z) ^ 2))) 4 :=
      (Work.Asymptotics.CuspEst.const_mul (480 : ℂ) (hq.mul hδ)).mono (by norm_num)
    have hD : Work.Asymptotics.CuspEst
        (fun z : ℍ => (E4Fun z - 1 - 240 * (Ept z) ^ 2) ^ 2) 4 :=
      ((hδ.mul hδ).mono (by norm_num : 4 ≤ 8)).congr (fun z => by ring)
    exact (((hA.add hB).add hC).add hD).congr (fun z => by ring)
  have hone : Work.Asymptotics.CuspEst (fun z : ℍ => (1 : ℂ) + 480 * (Ept z) ^ 2) 0 := by
    have hc : Work.Asymptotics.CuspEst (fun _ : ℍ => (1 : ℂ)) 0 :=
      Work.Asymptotics.CuspEst.const 1
    have h480 : Work.Asymptotics.CuspEst (fun z : ℍ => 480 * (Ept z) ^ 2) 0 :=
      (Work.Asymptotics.CuspEst.const_mul (480 : ℂ) hq).mono (by norm_num)
    exact (hc.add h480).congr (fun z => by ring)
  have hconst : Work.Asymptotics.CuspEst (fun z : ℍ => 241920 * (Ept z) ^ 4) 4 :=
    Work.Asymptotics.CuspEst.const_mul (241920 : ℂ) h4
  have h2 : Work.Asymptotics.CuspEst (fun z : ℍ => dE14 z) 4 :=
    (((h1.mul hE6).add (hone.mul hε)).sub hconst).congr (fun z => by
      simp only [dE14, E14ref, E14Fun]; ring)
  exact kaux_est_of_cuspEst h2

/-- `E₁₀ = E₄E₆ = 1 - 264 E² + O(‖E‖⁴)`, i.e. `dE10 = O(‖E‖⁴)`. -/
lemma kaux_dE10 : ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ z : ℍ, H ≤ z.im →
    ‖dE10 z‖ ≤ C * ‖Ept z‖ ^ 4 := by
  have hδ : Work.Asymptotics.CuspEst (fun z : ℍ => E4Fun z - 1 - 240 * (Ept z) ^ 2) 4 :=
    kaux_cuspEst_E4_two
  have hε : Work.Asymptotics.CuspEst (fun z : ℍ => E6Fun z - 1 + 504 * (Ept z) ^ 2) 4 :=
    kaux_cuspEst_E6_two
  have hq : Work.Asymptotics.CuspEst (fun z : ℍ => (Ept z) ^ 2) 2 :=
    Work.Asymptotics.cuspEst_Ept_pow 2
  have h4 : Work.Asymptotics.CuspEst (fun z : ℍ => (Ept z) ^ 4) 4 :=
    (hq.mul hq).congr (fun z => by ring)
  have hA : Work.Asymptotics.CuspEst
      (fun z : ℍ => 240 * ((Ept z) ^ 2 * (E6Fun z - 1 + 504 * (Ept z) ^ 2))) 4 :=
    (Work.Asymptotics.CuspEst.const_mul (240 : ℂ) (hq.mul hε)).mono (by norm_num)
  have hD : Work.Asymptotics.CuspEst
      (fun z : ℍ => 504 * ((Ept z) ^ 2 * (E4Fun z - 1 - 240 * (Ept z) ^ 2))) 4 :=
    (Work.Asymptotics.CuspEst.const_mul (504 : ℂ) (hq.mul hδ)).mono (by norm_num)
  have hE : Work.Asymptotics.CuspEst
      (fun z : ℍ => (E4Fun z - 1 - 240 * (Ept z) ^ 2) * (E6Fun z - 1 + 504 * (Ept z) ^ 2)) 4 :=
    (hδ.mul hε).mono (by norm_num)
  have hF : Work.Asymptotics.CuspEst (fun z : ℍ => 120960 * (Ept z) ^ 4) 4 :=
    Work.Asymptotics.CuspEst.const_mul (120960 : ℂ) h4
  have h2 : Work.Asymptotics.CuspEst (fun z : ℍ => dE10 z) 4 :=
    (((((hA.add hε).add hδ).sub hD).add hE).sub hF).congr (fun z => by
      simp only [dE10, E10ref, E10Fun]; ring)
  exact kaux_est_of_cuspEst h2

/-! ## The bounded `z`-atoms -/

lemma kaux_WFun : ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ z : ℍ, H ≤ z.im → ‖WFun z‖ ≤ C :=
  kaux_bdd_of_cuspEst Work.Asymptotics.cuspEst_WFun

lemma kaux_E14 : ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ z : ℍ, H ≤ z.im → ‖E14Fun z‖ ≤ C :=
  kaux_bdd_of_cuspEst Work.Asymptotics.cuspEst_E14Fun

lemma kaux_E10 : ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ z : ℍ, H ≤ z.im → ‖E10Fun z‖ ≤ C :=
  kaux_bdd_of_cuspEst Work.Asymptotics.cuspEst_E10Fun

/-- `U² - V²` is bounded on the tail. -/
lemma kaux_D2z : ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ z : ℍ, H ≤ z.im →
    ‖UFun z ^ 2 - VFun z ^ 2‖ ≤ C := by
  have hUW : Work.Asymptotics.CuspEst (fun z : ℍ => UFun z ^ 2 - WFun z ^ 2) 0 := by
    have hA : Work.Asymptotics.CuspEst
        (fun z : ℍ => UFun z ^ 2 - WFun z ^ 2 - 32 * Ept z) 0 :=
      (Work.Asymptotics.cuspEst_UFun_sq_sub_WFun_sq_sub_32E).mono (by norm_num)
    have hB : Work.Asymptotics.CuspEst (fun z : ℍ => 32 * Ept z) 0 :=
      (Work.Asymptotics.CuspEst.const_mul (32 : ℂ) Work.Asymptotics.cuspEst_Ept).mono
        (by norm_num)
    exact (hA.add hB).congr (fun z => by ring)
  have hW2 : Work.Asymptotics.CuspEst (fun z : ℍ => WFun z ^ 2) 0 :=
    (Work.Asymptotics.cuspEst_WFun.mul Work.Asymptotics.cuspEst_WFun).congr
      (fun z => by ring)
  have hV2 : Work.Asymptotics.CuspEst (fun z : ℍ => VFun z ^ 2) 0 :=
    ((Work.Asymptotics.cuspEst_VFun.mul Work.Asymptotics.cuspEst_VFun).mono
      (by norm_num : 0 ≤ 2)).congr (fun z => by ring)
  exact kaux_bdd_of_cuspEst
    ((hUW.add (hW2.sub hV2)).congr (fun z => by ring))

/-! ## The reference `z`-atoms and `𝓛` -/

/-- `‖Lref ℓ z‖ ≤ C(1 + ‖z‖)`, since `Lref = Xc + O(1)` and `Xc = πiz + c`. -/
lemma kaux_Lref (ℓ : LogLambdaData) : ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ z : ℍ, H ≤ z.im →
    ‖Lref ℓ z‖ ≤ C * (1 + ‖(z : ℂ)‖) := by
  refine ⟨1, Real.pi + ‖cuspC ℓ‖ + 21, one_pos, by positivity, fun z hz => ?_⟩
  have hX := kaux_norm_Xc_le ℓ z
  have he : ‖Ept z‖ ≤ 1 := kaux_norm_Ept_le_one hz
  have h8 : ‖(8 : ℂ) * Ept z‖ ≤ 8 := by
    rw [norm_mul, show ‖(8 : ℂ)‖ = 8 by norm_num]; linarith
  have h12 : ‖(12 : ℂ) * (Ept z) ^ 2‖ ≤ 12 := by
    have he2 : ‖(Ept z) ^ 2‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg (Ept z)) he
    rw [norm_mul, show ‖(12 : ℂ)‖ = 12 by norm_num]; linarith
  rw [Lref]
  calc ‖Xc ℓ z - 8 * Ept z + 12 * (Ept z) ^ 2‖
      ≤ ‖Xc ℓ z - 8 * Ept z‖ + ‖(12 : ℂ) * (Ept z) ^ 2‖ := norm_add_le _ _
    _ ≤ (‖Xc ℓ z‖ + 8) + 12 := by
        refine add_le_add ?_ h12
        calc ‖Xc ℓ z - 8 * Ept z‖ ≤ ‖Xc ℓ z‖ + ‖(8 : ℂ) * Ept z‖ := norm_sub_le _ _
          _ ≤ ‖Xc ℓ z‖ + 8 := by linarith
    _ ≤ (Real.pi + ‖cuspC ℓ‖ + 21) * (1 + ‖(z : ℂ)‖) := by
        have h1 : (0 : ℝ) ≤ ‖(z : ℂ)‖ := norm_nonneg _
        have h2 : (0 : ℝ) ≤ ‖cuspC ℓ‖ := norm_nonneg _
        nlinarith [hX, Real.pi_pos]

/-- `‖𝓛(z)‖ ≤ C(1 + ‖z‖)`. -/
lemma kaux_L (ℓ : LogLambdaData) : ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ z : ℍ, H ≤ z.im →
    ‖ℓ.L z‖ ≤ C * (1 + ‖(z : ℂ)‖) := by
  obtain ⟨H1, C1, hH1, hC1, b1⟩ := kaux_dL ℓ
  obtain ⟨H2, C2, hH2, hC2, b2⟩ := kaux_Lref ℓ
  refine ⟨1 + H1 + H2, C1 + C2 + 1, by linarith, by linarith, fun z hz => ?_⟩
  have hz1 : H1 ≤ z.im := by linarith
  have hz2 : H2 ≤ z.im := by linarith
  have hz0 : (1 : ℝ) ≤ z.im := by linarith
  have he : ‖Ept z‖ ≤ 1 := kaux_norm_Ept_le_one hz0
  have hE3 : ‖Ept z‖ ^ 3 ≤ 1 := pow_le_one₀ (norm_nonneg (Ept z)) he
  have hsplit : ℓ.L z = dL ℓ z + Lref ℓ z := by rw [dL]; ring
  have hnn : (0 : ℝ) ≤ 1 + ‖(z : ℂ)‖ := by positivity
  have hone : (1 : ℝ) ≤ 1 + ‖(z : ℂ)‖ := by linarith [norm_nonneg (z : ℂ)]
  calc ‖ℓ.L z‖ ≤ ‖dL ℓ z‖ + ‖Lref ℓ z‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ C1 * ‖Ept z‖ ^ 3 + C2 * (1 + ‖(z : ℂ)‖) := add_le_add (b1 z hz1) (b2 z hz2)
    _ ≤ C1 * (1 + ‖(z : ℂ)‖) + C2 * (1 + ‖(z : ℂ)‖) := by
        have hle : C1 * ‖Ept z‖ ^ 3 ≤ C1 * (1 + ‖(z : ℂ)‖) :=
          mul_le_mul_of_nonneg_left (le_trans hE3 hone) hC1.le
        linarith
    _ = (C1 + C2) * (1 + ‖(z : ℂ)‖) := by ring
    _ ≤ (C1 + C2 + 1) * (1 + ‖(z : ℂ)‖) :=
        mul_le_mul_of_nonneg_right (by linarith) hnn

/-- `‖Dref z‖ ≤ C(‖E‖²)⁻¹`, since `Dref = E⁻² + 24`. -/
lemma kaux_Dref : ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ z : ℍ, H ≤ z.im →
    ‖Dref z‖ ≤ C * (‖Ept z‖ ^ 2)⁻¹ := by
  refine ⟨1, 25, one_pos, by norm_num, fun z hz => ?_⟩
  have he : ‖Ept z‖ ≤ 1 := kaux_norm_Ept_le_one hz
  have he0 : 0 < ‖Ept z‖ := norm_pos_iff.mpr (Ept_ne_zero z)
  have ht2 : ‖Ept z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg (Ept z)) he
  have hge : (1 : ℝ) ≤ (‖Ept z‖ ^ 2)⁻¹ := by
    rw [one_le_inv₀ (pow_pos he0 2)]; exact ht2
  have hinv : ‖(Ept z)⁻¹ ^ 2‖ = (‖Ept z‖ ^ 2)⁻¹ := by
    rw [norm_pow, norm_inv, inv_pow]
  rw [Dref]
  calc ‖einv2 z + 24‖ ≤ ‖einv2 z‖ + ‖(24 : ℂ)‖ := norm_add_le _ _
    _ = (‖Ept z‖ ^ 2)⁻¹ + 24 := by rw [einv2, hinv]; norm_num
    _ ≤ 25 * (‖Ept z‖ ^ 2)⁻¹ := by nlinarith [hge]

/-- `‖Δ(z)⁻¹‖ ≤ C(‖E‖²)⁻¹`. -/
lemma kaux_invDelta : ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ z : ℍ, H ≤ z.im →
    ‖(DeltaFun z)⁻¹‖ ≤ C * (‖Ept z‖ ^ 2)⁻¹ := by
  obtain ⟨H1, C1, hH1, hC1, b1⟩ := kaux_dDelta
  refine ⟨H1 + 1, 25 + C1 + 1, by linarith, by linarith, fun z hz => ?_⟩
  have hz1 : H1 ≤ z.im := by linarith
  have hz0 : (1 : ℝ) ≤ z.im := by linarith
  have he : ‖Ept z‖ ≤ 1 := kaux_norm_Ept_le_one hz0
  have he0 : 0 < ‖Ept z‖ := norm_pos_iff.mpr (Ept_ne_zero z)
  have ht2 : ‖Ept z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg (Ept z)) he
  have hge : (1 : ℝ) ≤ (‖Ept z‖ ^ 2)⁻¹ := by
    rw [one_le_inv₀ (pow_pos he0 2)]; exact ht2
  have hinv : ‖(Ept z)⁻¹ ^ 2‖ = (‖Ept z‖ ^ 2)⁻¹ := by
    rw [norm_pow, norm_inv, inv_pow]
  have hD : ‖Dref z‖ ≤ 25 * (‖Ept z‖ ^ 2)⁻¹ := by
    rw [Dref]
    calc ‖einv2 z + 24‖ ≤ ‖einv2 z‖ + ‖(24 : ℂ)‖ := norm_add_le _ _
      _ = (‖Ept z‖ ^ 2)⁻¹ + 24 := by rw [einv2, hinv]; norm_num
      _ ≤ 25 * (‖Ept z‖ ^ 2)⁻¹ := by nlinarith [hge]
  calc ‖(DeltaFun z)⁻¹‖ = ‖Dref z + dDelta z‖ := by
        rw [show (DeltaFun z)⁻¹ = Dref z + dDelta z by rw [dDelta]; ring]
    _ ≤ ‖Dref z‖ + ‖dDelta z‖ := norm_add_le _ _
    _ ≤ 25 * (‖Ept z‖ ^ 2)⁻¹ + C1 * ‖Ept z‖ ^ 2 := add_le_add hD (b1 z hz1)
    _ ≤ (25 + C1 + 1) * (‖Ept z‖ ^ 2)⁻¹ := by
        have hle : C1 * ‖Ept z‖ ^ 2 ≤ C1 * (‖Ept z‖ ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left (le_trans ht2 hge) hC1.le
        have hge0 : (0 : ℝ) ≤ (‖Ept z‖ ^ 2)⁻¹ := le_trans zero_le_one hge
        nlinarith [hle, hge0]

/-- `‖Sinvref τ z‖ ≤ C`, uniformly for `τ ∈ K`. -/
lemma kaux_Sinvref {K : Set ℍ} (hK : IsCompact K) :
    ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ (τ z : ℍ), τ ∈ K → H ≤ z.im → ‖Sinvref τ z‖ ≤ C := by
  obtain ⟨Bj, hBj, bj⟩ := kaux_bound_compact hK continuous_jInvariantFun_ub
  refine ⟨1, 1 + (Bj + 720) + 1, one_pos, by linarith, fun τ z hτ hz => ?_⟩
  have he : ‖Ept z‖ ≤ 1 := kaux_norm_Ept_le_one hz
  have he2 : ‖(Ept z) ^ 2‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg (Ept z)) he
  have hj : ‖jInvariantFun τ - 720‖ ≤ Bj + 720 := by
    calc ‖jInvariantFun τ - (720 : ℂ)‖ ≤ ‖jInvariantFun τ‖ + ‖(720 : ℂ)‖ := norm_sub_le _ _
      _ ≤ Bj + 720 := by rw [show ‖(720 : ℂ)‖ = 720 by norm_num]; linarith [bj τ hτ]
  rw [Sinvref]
  calc ‖1 + (jInvariantFun τ - 720) * (Ept z) ^ 2‖
      ≤ 1 + ‖(jInvariantFun τ - 720) * (Ept z) ^ 2‖ := by
        have h := norm_add_le (1 : ℂ) ((jInvariantFun τ - 720) * (Ept z) ^ 2)
        rwa [norm_one] at h
    _ ≤ 1 + (Bj + 720) := by
        rw [norm_mul]
        have h := mul_le_mul hj he2 (norm_nonneg _) (by linarith [hBj])
        have h' : ‖jInvariantFun τ - 720‖ * ‖(Ept z) ^ 2‖ ≤ Bj + 720 := by simpa using h
        linarith
    _ ≤ 1 + (Bj + 720) + 1 := by linarith

/-! ## The `τ`-atoms, bounded on the compact `K` -/

lemma kaux_continuous_E8Fun : Continuous (fun τ : ℍ => E8Fun τ) := continuous_E4Fun_ub.pow 2

lemma kaux_continuous_E10Fun : Continuous (fun τ : ℍ => E10Fun τ) :=
  continuous_E4Fun_ub.mul continuous_E6Fun_ub

lemma kaux_psi2 (ℓ : LogLambdaData) {K : Set ℍ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ K, ‖psi2 ℓ τ‖ ≤ C :=
  kaux_bound_compact hK (continuous_psi2_ub ℓ)

lemma kaux_psi4 (ℓ : LogLambdaData) {K : Set ℍ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ K, ‖psi4 ℓ τ‖ ≤ C :=
  kaux_bound_compact hK (continuous_psi4_ub ℓ)

lemma kaux_E4tau {K : Set ℍ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ K, ‖E4Fun τ‖ ≤ C :=
  kaux_bound_compact hK continuous_E4Fun_ub

lemma kaux_Deltatau {K : Set ℍ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ K, ‖DeltaFun τ‖ ≤ C :=
  kaux_bound_compact hK continuous_DeltaFun_ub

lemma kaux_jtau {K : Set ℍ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ K, ‖jInvariantFun τ‖ ≤ C :=
  kaux_bound_compact hK continuous_jInvariantFun_ub

lemma kaux_E10tau {K : Set ℍ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ K, ‖E10Fun τ‖ ≤ C :=
  kaux_bound_compact hK kaux_continuous_E10Fun

lemma kaux_E8tau {K : Set ℍ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ K, ‖E8Fun τ‖ ≤ C :=
  kaux_bound_compact hK kaux_continuous_E8Fun

/-- `‖C24 ℓ τ‖ ≤ C` for `τ ∈ K`. -/
lemma kaux_C24 (ℓ : LogLambdaData) {K : Set ℍ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ K, ‖C24 ℓ τ‖ ≤ C := by
  obtain ⟨B2, hB2, b2⟩ := kaux_psi2 ℓ hK
  obtain ⟨B4, hB4, b4⟩ := kaux_psi4 ℓ hK
  obtain ⟨B10, hB10, b10⟩ := kaux_E10tau hK
  obtain ⟨B8, hB8, b8⟩ := kaux_E8tau hK
  obtain ⟨Bj, hBj, bj⟩ := kaux_jtau hK
  refine ⟨B2 * B10 * Bj + B4 * B8 * (1728 + Bj) + 1, by positivity, fun τ hτ => ?_⟩
  have h1 : ‖psi2 ℓ τ * E10Fun τ * jInvariantFun τ‖ ≤ B2 * B10 * Bj := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (b2 τ hτ) (b10 τ hτ) (norm_nonneg _) hB2.le) (bj τ hτ)
      (norm_nonneg _) (by positivity)
  have hsub : ‖(1728 : ℂ) - jInvariantFun τ‖ ≤ 1728 + Bj := by
    calc ‖(1728 : ℂ) - jInvariantFun τ‖ ≤ ‖(1728 : ℂ)‖ + ‖jInvariantFun τ‖ := norm_sub_le _ _
      _ ≤ 1728 + Bj := by rw [show ‖(1728 : ℂ)‖ = 1728 by norm_num]; linarith [bj τ hτ]
  have h3 : ‖psi4 ℓ τ * E8Fun τ * (1728 - jInvariantFun τ)‖ ≤ B4 * B8 * (1728 + Bj) := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (b4 τ hτ) (b8 τ hτ) (norm_nonneg _) hB4.le) hsub
      (norm_nonneg _) (by positivity)
  rw [C24]
  calc ‖psi2 ℓ τ * E10Fun τ * jInvariantFun τ
        + psi4 ℓ τ * E8Fun τ * (1728 - jInvariantFun τ)‖
      ≤ ‖psi2 ℓ τ * E10Fun τ * jInvariantFun τ‖
        + ‖psi4 ℓ τ * E8Fun τ * (1728 - jInvariantFun τ)‖ := norm_add_le _ _
    _ ≤ B2 * B10 * Bj + B4 * B8 * (1728 + Bj) := add_le_add h1 h3
    _ ≤ B2 * B10 * Bj + B4 * B8 * (1728 + Bj) + 1 := by linarith

/-- `‖B24 ℓ τ‖ ≤ C` for `τ ∈ K`. -/
lemma kaux_B24 (ℓ : LogLambdaData) {K : Set ℍ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ K, ‖B24 ℓ τ‖ ≤ C := by
  obtain ⟨Bd, hBd, bd⟩ := kaux_Deltatau hK
  obtain ⟨B2, hB2, b2⟩ := kaux_psi2 ℓ hK
  obtain ⟨B4, hB4, b4⟩ := kaux_psi4 ℓ hK
  obtain ⟨B10, hB10, b10⟩ := kaux_E10tau hK
  obtain ⟨B8, hB8, b8⟩ := kaux_E8tau hK
  refine ⟨3456 * Bd + 2 * B2 * B10 + 2 * B4 * B8 + 1, by positivity, fun τ hτ => ?_⟩
  have h1 : ‖(-3456 : ℂ) * DeltaFun τ‖ ≤ 3456 * Bd := by
    rw [norm_mul, show ‖(-3456 : ℂ)‖ = 3456 by norm_num]
    exact mul_le_mul_of_nonneg_left (bd τ hτ) (by norm_num)
  have h2 : ‖2 * psi2 ℓ τ * E10Fun τ‖ ≤ 2 * B2 * B10 := by
    rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have h := mul_le_mul (b2 τ hτ) (b10 τ hτ) (norm_nonneg _) hB2.le
    nlinarith [h]
  have h3 : ‖2 * psi4 ℓ τ * E8Fun τ‖ ≤ 2 * B4 * B8 := by
    rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have h := mul_le_mul (b4 τ hτ) (b8 τ hτ) (norm_nonneg _) hB4.le
    nlinarith [h]
  rw [B24]
  calc ‖-3456 * DeltaFun τ + 2 * psi2 ℓ τ * E10Fun τ - 2 * psi4 ℓ τ * E8Fun τ‖
      ≤ ‖-3456 * DeltaFun τ + 2 * psi2 ℓ τ * E10Fun τ‖ + ‖2 * psi4 ℓ τ * E8Fun τ‖ :=
        norm_sub_le _ _
    _ ≤ (‖(-3456 : ℂ) * DeltaFun τ‖ + ‖2 * psi2 ℓ τ * E10Fun τ‖)
        + ‖2 * psi4 ℓ τ * E8Fun τ‖ := by
        exact add_le_add (norm_add_le _ _) le_rfl
    _ ≤ 3456 * Bd + 2 * B2 * B10 + 2 * B4 * B8 := by linarith
    _ ≤ 3456 * Bd + 2 * B2 * B10 + 2 * B4 * B8 + 1 := by linarith

/-! ## The deviation `A24 - A24ref` -/

/-- The difference of the true and reference `A24` atoms is `O((1+‖z‖)·‖E‖³)`.

Algebraically, with `ψ = ψ₂E₁₀ - ψ₄E₈`,
`A24 - A24ref = -3456 Δ(τ)(E14·dL + dE14·Lref) - ψ(E10·dD2 + dE10·D2ref)`,
and every term is a bounded (or `O(1+‖z‖)`) factor times a deviation of order `‖E‖³`. -/
lemma kaux_A24diff_bound (ℓ : LogLambdaData) {K : Set ℍ} (hK : IsCompact K) :
    ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ (τ z : ℍ), τ ∈ K → H ≤ z.im →
      ‖A24 ℓ τ z - A24ref ℓ τ z‖ ≤ C * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ ^ 3 := by
  obtain ⟨H1, C1, hH1, hC1, b1⟩ := kaux_E14
  obtain ⟨H2, C2, hH2, hC2, b2⟩ := kaux_L ℓ
  obtain ⟨H3, C3, hH3, hC3, b3⟩ := kaux_Lref ℓ
  obtain ⟨H4, C4, hH4, hC4, b4⟩ := kaux_dL ℓ
  obtain ⟨H5, C5, hH5, hC5, b5⟩ := kaux_dE14
  obtain ⟨H6, C6, hH6, hC6, b6⟩ := kaux_E10
  obtain ⟨H7, C7, hH7, hC7, b7⟩ := kaux_D2z
  obtain ⟨H8, C8, hH8, hC8, b8⟩ := kaux_dD2
  obtain ⟨H9, C9, hH9, hC9, b9⟩ := kaux_dE10
  obtain ⟨Bd, hBd, bd⟩ := kaux_Deltatau hK
  obtain ⟨D2, hD2, bD2⟩ := kaux_psi2 ℓ hK
  obtain ⟨D4, hD4, bD4⟩ := kaux_psi4 ℓ hK
  obtain ⟨D10, hD10, bD10⟩ := kaux_E10tau hK
  obtain ⟨D8, hD8, bD8⟩ := kaux_E8tau hK
  refine ⟨1 + H1 + H2 + H3 + H4 + H5 + H6 + H7 + H8 + H9,
    1 + 3456 * Bd * (C1 * C4 + C5 * C3) + (D2 * D10 + D4 * D8) * (C6 * C8 + 161 * C9),
    by linarith, by positivity, fun τ z hτ hz => ?_⟩
  have hz1 : H1 ≤ z.im := by linarith
  have hz2 : H2 ≤ z.im := by linarith
  have hz3 : H3 ≤ z.im := by linarith
  have hz4 : H4 ≤ z.im := by linarith
  have hz5 : H5 ≤ z.im := by linarith
  have hz6 : H6 ≤ z.im := by linarith
  have hz7 : H7 ≤ z.im := by linarith
  have hz8 : H8 ≤ z.im := by linarith
  have hz9 : H9 ≤ z.im := by linarith
  have hz0 : (1 : ℝ) ≤ z.im := by linarith
  have he : ‖Ept z‖ ≤ 1 := kaux_norm_Ept_le_one hz0
  have h0 : (0 : ℝ) ≤ ‖Ept z‖ := norm_nonneg _
  have ht4 : ‖Ept z‖ ^ 4 ≤ ‖Ept z‖ ^ 3 := pow_le_pow_of_le_one h0 he (by norm_num)
  have hX1 : (1 : ℝ) ≤ 1 + ‖(z : ℂ)‖ := by linarith [norm_nonneg (z : ℂ)]
  have hX0 : (0 : ℝ) ≤ 1 + ‖(z : ℂ)‖ := by linarith [norm_nonneg (z : ℂ)]
  have hE14b := b1 z hz1
  have hLb := b2 z hz2
  have hLrefb := b3 z hz3
  have hdLb := b4 z hz4
  have hdE14b := b5 z hz5
  have hE10b := b6 z hz6
  have hD2b := b7 z hz7
  have hdD2b := b8 z hz8
  have hdE10b := b9 z hz9
  have hΔb := bd τ hτ
  have hD2refb : ‖D2ref z‖ ≤ 161 := norm_D2ref_le hz0
  have hψb : ‖psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ‖ ≤ D2 * D10 + D4 * D8 := by
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖psi2 ℓ τ * E10Fun τ‖ ≤ D2 * D10 := by
      rw [norm_mul]
      exact mul_le_mul (bD2 τ hτ) (bD10 τ hτ) (norm_nonneg _) hD2.le
    have h2 : ‖psi4 ℓ τ * E8Fun τ‖ ≤ D4 * D8 := by
      rw [norm_mul]
      exact mul_le_mul (bD4 τ hτ) (bD8 τ hτ) (norm_nonneg _) hD4.le
    linarith
  have hsplit : A24 ℓ τ z - A24ref ℓ τ z
      = -3456 * DeltaFun τ * (E14Fun z * dL ℓ z + dE14 z * Lref ℓ z)
        - (psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ)
          * (E10Fun z * dD2 z + dE10 z * D2ref z) := by
    simp only [A24, A24ref, dL, dE14, dD2, dE10, Lref, E14ref]
    ring
  have hX : ‖E14Fun z * dL ℓ z + dE14 z * Lref ℓ z‖
      ≤ (C1 * C4 + C5 * C3) * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ ^ 3 := by
    have hA : ‖E14Fun z * dL ℓ z‖ ≤ C1 * C4 * ‖Ept z‖ ^ 3 := by
      rw [norm_mul]
      calc ‖E14Fun z‖ * ‖dL ℓ z‖ ≤ C1 * (C4 * ‖Ept z‖ ^ 3) :=
            mul_le_mul hE14b hdLb (norm_nonneg _) hC1.le
        _ = C1 * C4 * ‖Ept z‖ ^ 3 := by ring
    have hB : ‖dE14 z * Lref ℓ z‖ ≤ C5 * C3 * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ ^ 3 := by
      rw [norm_mul]
      calc ‖dE14 z‖ * ‖Lref ℓ z‖ ≤ (C5 * ‖Ept z‖ ^ 4) * (C3 * (1 + ‖(z : ℂ)‖)) :=
            mul_le_mul hdE14b hLrefb (norm_nonneg _) (by positivity)
        _ ≤ (C5 * ‖Ept z‖ ^ 3) * (C3 * (1 + ‖(z : ℂ)‖)) := by
            have hC3X : (0 : ℝ) ≤ C3 * (1 + ‖(z : ℂ)‖) := by positivity
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht4 hC5.le) hC3X
        _ = C5 * C3 * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ ^ 3 := by ring
    calc ‖E14Fun z * dL ℓ z + dE14 z * Lref ℓ z‖
        ≤ ‖E14Fun z * dL ℓ z‖ + ‖dE14 z * Lref ℓ z‖ := norm_add_le _ _
      _ ≤ C1 * C4 * ‖Ept z‖ ^ 3 + C5 * C3 * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ ^ 3 :=
            add_le_add hA hB
      _ ≤ (C1 * C4 + C5 * C3) * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ ^ 3 :=
            kaux_add_mul_le (by positivity) (by positivity) (by positivity) hX1
  have hY : ‖E10Fun z * dD2 z + dE10 z * D2ref z‖
      ≤ (C6 * C8 + 161 * C9) * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ ^ 3 := by
    have hA : ‖E10Fun z * dD2 z‖ ≤ C6 * C8 * ‖Ept z‖ ^ 3 := by
      rw [norm_mul]
      calc ‖E10Fun z‖ * ‖dD2 z‖ ≤ C6 * (C8 * ‖Ept z‖ ^ 3) :=
            mul_le_mul hE10b hdD2b (norm_nonneg _) hC6.le
        _ = C6 * C8 * ‖Ept z‖ ^ 3 := by ring
    have hB : ‖dE10 z * D2ref z‖ ≤ 161 * C9 * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ ^ 3 := by
      rw [norm_mul]
      have h1 : ‖dE10 z‖ * ‖D2ref z‖ ≤ (C9 * ‖Ept z‖ ^ 4) * 161 :=
        mul_le_mul hdE10b hD2refb (norm_nonneg _) (by positivity)
      have h2 : (C9 * ‖Ept z‖ ^ 4) * 161 ≤ (C9 * ‖Ept z‖ ^ 3) * 161 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht4 hC9.le) (by norm_num)
      have h3 : (C9 * ‖Ept z‖ ^ 3) * 161 = 161 * C9 * ‖Ept z‖ ^ 3 := by ring
      have h4 : 161 * C9 * ‖Ept z‖ ^ 3 ≤ 161 * C9 * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ ^ 3 := by
        have h5 : (161 * C9) * 1 ≤ (161 * C9) * (1 + ‖(z : ℂ)‖) :=
          mul_le_mul_of_nonneg_left hX1 (by positivity)
        rw [mul_one] at h5
        simpa using mul_le_mul_of_nonneg_right h5 (by positivity : (0 : ℝ) ≤ ‖Ept z‖ ^ 3)
      linarith
    calc ‖E10Fun z * dD2 z + dE10 z * D2ref z‖
        ≤ ‖E10Fun z * dD2 z‖ + ‖dE10 z * D2ref z‖ := norm_add_le _ _
      _ ≤ C6 * C8 * ‖Ept z‖ ^ 3 + 161 * C9 * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ ^ 3 :=
            add_le_add hA hB
      _ ≤ (C6 * C8 + 161 * C9) * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ ^ 3 :=
            kaux_add_mul_le (by positivity) (by positivity) (by positivity) hX1
  have hT1 : ‖(-3456 : ℂ) * DeltaFun τ * (E14Fun z * dL ℓ z + dE14 z * Lref ℓ z)‖
      ≤ 3456 * Bd * (C1 * C4 + C5 * C3) * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ ^ 3 := by
    rw [norm_mul, norm_mul, show ‖(-3456 : ℂ)‖ = 3456 by norm_num]
    calc 3456 * ‖DeltaFun τ‖ * ‖E14Fun z * dL ℓ z + dE14 z * Lref ℓ z‖
        ≤ 3456 * Bd * ((C1 * C4 + C5 * C3) * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ ^ 3) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hΔb (by norm_num)) hX (norm_nonneg _)
            (by positivity)
      _ = 3456 * Bd * (C1 * C4 + C5 * C3) * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ ^ 3 := by ring
  have hT2 : ‖(psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ)
      * (E10Fun z * dD2 z + dE10 z * D2ref z)‖
      ≤ (D2 * D10 + D4 * D8) * (C6 * C8 + 161 * C9) * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ ^ 3 := by
    rw [norm_mul]
    calc ‖psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ‖
          * ‖E10Fun z * dD2 z + dE10 z * D2ref z‖
        ≤ (D2 * D10 + D4 * D8) * ((C6 * C8 + 161 * C9) * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ ^ 3) :=
          mul_le_mul hψb hY (norm_nonneg _) (by positivity)
      _ = (D2 * D10 + D4 * D8) * (C6 * C8 + 161 * C9) * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ ^ 3 := by
          ring
  rw [hsplit]
  refine le_trans (norm_sub_le _ _) ?_
  refine le_trans (add_le_add hT1 hT2) ?_
  have hcomb : 3456 * Bd * (C1 * C4 + C5 * C3) * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ ^ 3
      + (D2 * D10 + D4 * D8) * (C6 * C8 + 161 * C9) * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ ^ 3
      = (3456 * Bd * (C1 * C4 + C5 * C3) + (D2 * D10 + D4 * D8) * (C6 * C8 + 161 * C9))
        * (1 + ‖(z : ℂ)‖) * ‖Ept z‖ ^ 3 := by ring
  rw [hcomb]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity)

/-! ## The target -/

theorem kminus_tail_aux (ℓ : Work.Kernels.LogLambdaData) {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ H C : ℝ, 0 < H ∧ 0 < C ∧ ∀ (τ z : UpperHalfPlane), τ ∈ K → H ≤ z.im →
      (‖Work.Asymptotics.Compact.dDelta z‖ ≤ C * ‖Work.Residues.Ept z‖ ^ 2 ∧
       ‖Work.Asymptotics.Compact.dSinv τ z‖ ≤ C * ‖Work.Residues.Ept z‖ ^ 4 ∧
       ‖Work.Asymptotics.Compact.dW z‖ ≤ C * ‖Work.Residues.Ept z‖ ^ 3 ∧
       ‖Work.Asymptotics.Compact.dD2 z‖ ≤ C * ‖Work.Residues.Ept z‖ ^ 3 ∧
       ‖Work.Asymptotics.Compact.dL ℓ z‖ ≤ C * ‖Work.Residues.Ept z‖ ^ 3 ∧
       ‖Work.Asymptotics.Compact.dE14 z‖ ≤ C * ‖Work.Residues.Ept z‖ ^ 4 ∧
       ‖Work.Asymptotics.Compact.dE10 z‖ ≤ C * ‖Work.Residues.Ept z‖ ^ 4 ∧
       ‖Work.Kernels.WFun z‖ ≤ C ∧
       ‖Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2‖ ≤ C ∧
       ‖Work.Kernels.E14Fun z‖ ≤ C ∧ ‖Work.Kernels.E10Fun z‖ ≤ C ∧
       ‖ℓ.L z‖ ≤ C * (1 + ‖(z : ℂ)‖) ∧
       ‖Work.Asymptotics.Compact.Lref ℓ z‖ ≤ C * (1 + ‖(z : ℂ)‖) ∧
       ‖(Work.Kernels.DeltaFun z)⁻¹‖ ≤ C * (‖Work.Residues.Ept z‖ ^ 2)⁻¹ ∧
       ‖Work.Asymptotics.Compact.Dref z‖ ≤ C * (‖Work.Residues.Ept z‖ ^ 2)⁻¹ ∧
       ‖Work.Asymptotics.Compact.Sinvref τ z‖ ≤ C ∧
       ‖Work.Asymptotics.Compact.A24 ℓ τ z‖ ≤ C * (1 + ‖(z : ℂ)‖) ∧
       ‖Work.Asymptotics.Compact.A24ref ℓ τ z‖ ≤ C * (1 + ‖(z : ℂ)‖) ∧
       ‖Work.Asymptotics.Compact.A24 ℓ τ z - Work.Asymptotics.Compact.A24ref ℓ τ z‖
          ≤ C * (1 + ‖(z : ℂ)‖) * ‖Work.Residues.Ept z‖ ^ 3 ∧
       ‖Work.Asymptotics.Compact.C24 ℓ τ‖ ≤ C ∧
       ‖Work.Asymptotics.Compact.B24 ℓ τ‖ ≤ C ∧
       ‖Work.Kernels.psi2 ℓ τ‖ ≤ C ∧ ‖Work.Kernels.psi4 ℓ τ‖ ≤ C ∧
       ‖Work.Kernels.E4Fun τ‖ ≤ C ∧ ‖Work.Kernels.DeltaFun τ‖ ≤ C ∧
       ‖Work.Kernels.jInvariantFun τ‖ ≤ C ∧ ‖Work.Kernels.E10Fun τ‖ ≤ C ∧
       ‖Work.Kernels.E8Fun τ‖ ≤ C) := by
  obtain ⟨H1, C1, hH1, hC1, b1⟩ := kaux_dDelta
  obtain ⟨H2, C2, hH2, hC2, b2⟩ := kaux_dSinv hK
  obtain ⟨H3, C3, hH3, hC3, b3⟩ := kaux_dW
  obtain ⟨H4, C4, hH4, hC4, b4⟩ := kaux_dD2
  obtain ⟨H5, C5, hH5, hC5, b5⟩ := kaux_dL ℓ
  obtain ⟨H6, C6, hH6, hC6, b6⟩ := kaux_dE14
  obtain ⟨H7, C7, hH7, hC7, b7⟩ := kaux_dE10
  obtain ⟨H8, C8, hH8, hC8, b8⟩ := kaux_WFun
  obtain ⟨H9, C9, hH9, hC9, b9⟩ := kaux_D2z
  obtain ⟨H10, C10, hH10, hC10, b10⟩ := kaux_E14
  obtain ⟨H11, C11, hH11, hC11, b11⟩ := kaux_E10
  obtain ⟨H12, C12, hH12, hC12, b12⟩ := kaux_L ℓ
  obtain ⟨H13, C13, hH13, hC13, b13⟩ := kaux_Lref ℓ
  obtain ⟨H14, C14, hH14, hC14, b14⟩ := kaux_invDelta
  obtain ⟨H15, C15, hH15, hC15, b15⟩ := kaux_Dref
  obtain ⟨H16, C16, hH16, hC16, b16⟩ := kaux_Sinvref hK
  obtain ⟨H17, C17, hH17, hC17, b17⟩ := kaux_A24_est ℓ hK
  obtain ⟨H18, C18, hH18, hC18, b18⟩ := kaux_A24ref_est ℓ hK
  obtain ⟨H19, C19, hH19, hC19, b19⟩ := kaux_A24diff_bound ℓ hK
  obtain ⟨p20, hp20, b20⟩ := kaux_C24 ℓ hK
  obtain ⟨p21, hp21, b21⟩ := kaux_B24 ℓ hK
  obtain ⟨p22, hp22, b22⟩ := kaux_psi2 ℓ hK
  obtain ⟨p23, hp23, b23⟩ := kaux_psi4 ℓ hK
  obtain ⟨p24, hp24, b24⟩ := kaux_E4tau hK
  obtain ⟨p25, hp25, b25⟩ := kaux_Deltatau hK
  obtain ⟨p26, hp26, b26⟩ := kaux_jtau hK
  obtain ⟨p27, hp27, b27⟩ := kaux_E10tau hK
  obtain ⟨p28, hp28, b28⟩ := kaux_E8tau hK
  refine ⟨1 + H1 + H2 + H3 + H4 + H5 + H6 + H7 + H8 + H9 + H10 + H11 + H12 + H13 + H14
      + H15 + H16 + H17 + H18 + H19,
    1 + C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8 + C9 + C10 + C11 + C12 + C13 + C14
      + C15 + C16 + C17 + C18 + C19 + p20 + p21 + p22 + p23 + p24 + p25 + p26 + p27 + p28,
    by linarith, by linarith, fun τ z hτ hz => ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (b1 z (by linarith)) (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · exact le_trans (b2 τ z hτ (by linarith))
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · exact le_trans (b3 z (by linarith)) (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · exact le_trans (b4 z (by linarith)) (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · exact le_trans (b5 z (by linarith)) (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · exact le_trans (b6 z (by linarith)) (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · exact le_trans (b7 z (by linarith)) (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · exact le_trans (b8 z (by linarith)) (by linarith)
  · exact le_trans (b9 z (by linarith)) (by linarith)
  · exact le_trans (b10 z (by linarith)) (by linarith)
  · exact le_trans (b11 z (by linarith)) (by linarith)
  · exact le_trans (b12 z (by linarith)) (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · exact le_trans (b13 z (by linarith)) (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · exact le_trans (b14 z (by linarith)) (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · exact le_trans (b15 z (by linarith)) (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · exact le_trans (b16 τ z hτ (by linarith)) (by linarith)
  · exact le_trans (b17 τ z hτ (by linarith))
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · exact le_trans (b18 τ z hτ (by linarith))
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · exact le_trans (b19 τ z hτ (by linarith))
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity))
  · exact le_trans (b20 τ hτ) (by linarith)
  · exact le_trans (b21 τ hτ) (by linarith)
  · exact le_trans (b22 τ hτ) (by linarith)
  · exact le_trans (b23 τ hτ) (by linarith)
  · exact le_trans (b24 τ hτ) (by linarith)
  · exact le_trans (b25 τ hτ) (by linarith)
  · exact le_trans (b26 τ hτ) (by linarith)
  · exact le_trans (b27 τ hτ) (by linarith)
  · exact le_trans (b28 τ hτ) (by linarith)

end Work.Asymptotics.Compact
