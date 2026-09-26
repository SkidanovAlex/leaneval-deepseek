/-
# The spike-circle bound for `K_-^{(24)}` (via the weighted calculus `SBs`)

`K_-^{(24)} = (kpre ζ τ)⁻¹ · bracket24 ℓ ζ τ` and the bracket, regrouped as
`W(ζ)B'(τ,ζ) + ((E₁₀/Δ)(U²-V²))(ζ)·(𝓛X + 𝓛_SY)(τ) - 3456Δ(τ)(E₁₄/Δ)(ζ)𝓛(ζ)`
(`Work.Residues.bracket24_regroup`), is a sum of products of `SBs`-atoms whose exponential
weights cancel: every product has total weight `≤ 0`.  Hence `K_-^{(24)}` is polynomially
bounded on the spike circle, and `KM24_spike_bound` extracts the explicit form.

(This file duplicates, in a self-contained way, the corresponding lemmas of
`Submission/Work/Asymptotics/SpikeCircle/Kfun_sphere_bound.lean`, which is being edited
concurrently.)
-/
import Mathlib
import Submission.Work.Asymptotics.SpikeCircle.SBsAtoms
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Asymptotics.Compact.kminus_bracket

noncomputable section
open UpperHalfPlane
open scoped Topology

namespace Work.Asymptotics.SpikeCircle

set_option maxHeartbeats 2000000

open Work.Kernels

lemma SBs.mul' {H₁ H₂ k l : ℝ} {f g : ℍ → ℍ → ℂ} (hf : SBs H₁ k f) (hg : SBs H₂ l g) :
    SBs (max H₁ H₂) (k + l) (fun τ ζ => f τ ζ * g τ ζ) :=
  SBs.mul (hf.monoH (le_max_left _ _)) (hg.monoH (le_max_right _ _))

lemma SBs.add' {H₁ H₂ k : ℝ} {f g : ℍ → ℍ → ℂ} (hf : SBs H₁ k f) (hg : SBs H₂ k g) :
    SBs (max H₁ H₂) k (fun τ ζ => f τ ζ + g τ ζ) :=
  SBs.add (hf.monoH (le_max_left _ _)) (hg.monoH (le_max_right _ _))

lemma SBs.sub' {H₁ H₂ k : ℝ} {f g : ℍ → ℍ → ℂ} (hf : SBs H₁ k f) (hg : SBs H₂ k g) :
    SBs (max H₁ H₂) k (fun τ ζ => f τ ζ - g τ ζ) :=
  SBs.sub (hf.monoH (le_max_left _ _)) (hg.monoH (le_max_right _ _))

lemma SBs.const_mul' (c : ℂ) {H k : ℝ} {f : ℍ → ℍ → ℂ} (hf : SBs H k f) :
    SBs H k (fun τ ζ => c * f τ ζ) :=
  SBs.const_mul c hf

/-! ## The `d = 24` bracket -/

/-- `j(ζ)` is of exponential weight `tpar τ^{-2}` on the spike circle: `‖j ζ‖ ≤ C e^{2π Im τ}`. -/
lemma SBs.j_zeta {H : ℝ} (hH : 3 ≤ H) : SBs H (-2) (fun _ ζ : ℍ => jInvariantFun ζ) := by
  obtain ⟨C, hC, hb⟩ := jInvariantFun_strip_bound
  refine ⟨C * Real.exp (2 * Real.pi * (29 / 20)) + 1, 0, by positivity, le_refl 0,
    fun τ ζ hτ hζ hH' => ?_⟩
  rw [Real.rpow_zero, mul_one]
  have hzim : (1 / 2 : ℝ) ≤ ζ.im := by
    have h1 : (1 : ℝ) ≤ ζ.im := one_le_zeta_im hζ (le_trans hH hH')
    linarith
  refine le_trans (hb ζ hzim) ?_
  rw [tpar_neg_two τ]
  calc C * Real.exp (2 * Real.pi * ζ.im)
      ≤ C * (Real.exp (2 * Real.pi * (29 / 20)) * Real.exp (2 * Real.pi * τ.im)) :=
        mul_le_mul_of_nonneg_left (exp_im_zeta_le hζ) hC.le
    _ = C * Real.exp (2 * Real.pi * (29 / 20)) * Real.exp (2 * Real.pi * τ.im) := by ring
    _ ≤ (C * Real.exp (2 * Real.pi * (29 / 20)) + 1) * Real.exp (2 * Real.pi * τ.im) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

/-- The bracket of `K_-^{(24)}`, in the regrouped form `bracket24_regroup`, is polynomially
bounded on the spike circle.  Every product of atoms has exponential weight `≤ 0`:

* `W(ζ)·𝓛(τ)·B₀(τ)`: `0 + 0 + 2`,
* `W(ζ)·j(ζ)·𝓛(τ)·X(τ)`: `0 - 2 + 0 + 2`,
* `W(ζ)·C(τ)`: `0 + 2`,
* `W(ζ)·j(ζ)·𝓛_S(τ)·Y(τ)`: `0 - 2 + 1 + 1`,
* `W(ζ)·Δ(τ)·j(ζ)`: `0 + 2 - 2`,
* `(E₁₀(ζ)/Δ(ζ))·(U²-V²)(ζ)·(𝓛 X + 𝓛_S Y)(τ)`: `-2 + 0 + 2`,
* `Δ(τ)·(E₁₄(ζ)/Δ(ζ))·𝓛(ζ)`: `2 - 2 + 0`. -/
lemma SBs_bracket24_regroup (ℓ : LogLambdaData) : ∃ H : ℝ, SBs H 0 (fun τ ζ : ℍ =>
    WFun ζ * Work.Residues.Bprimefun ℓ ζ τ
      + (E10Fun ζ * (DeltaFun ζ)⁻¹) * (UFun ζ ^ 2 - VFun ζ ^ 2)
          * (ℓ.L τ * Work.Residues.Xfun τ + ℓ.L_S τ * Work.Residues.Yfun τ)
      - 3456 * DeltaFun τ * (E14Fun ζ * (DeltaFun ζ)⁻¹) * ℓ.L ζ) := by
  have hW : SBs 3 0 (fun _ ζ : ℍ => WFun ζ) := SBs_W_zeta (H := 3) le_rfl
  have hE10 : SBs 3 0 (fun _ ζ : ℍ => E10Fun ζ) := SBs_E10_zeta (H := 3) le_rfl
  have hE14 : SBs 3 0 (fun _ ζ : ℍ => E14Fun ζ) := SBs_E14_zeta (H := 3) le_rfl
  have hU : SBs 3 0 (fun _ ζ : ℍ => UFun ζ) := SBs_U_zeta (H := 3) le_rfl
  have hV : SBs 3 0 (fun _ ζ : ℍ => VFun ζ) := SBs_V_zeta (H := 3) le_rfl
  have hLz : SBs 3 0 (fun _ ζ : ℍ => ℓ.L ζ) := SBs_L_zeta ℓ (H := 3) le_rfl
  have hJz : SBs 3 (-2) (fun _ ζ : ℍ => jInvariantFun ζ) := SBs.j_zeta (H := 3) le_rfl
  have hInvDz : SBs 3 (-2) (fun _ ζ : ℍ => (DeltaFun ζ)⁻¹) :=
    SBs_inv_Delta_zeta (H := 3) le_rfl
  have hDt : SBs 1 2 (fun τ _ : ℍ => DeltaFun τ) := SBs_Delta_tau (H := 1) le_rfl
  obtain ⟨_HL, hL⟩ := SBs.of_cuspBound (H := 3) (Work.Residues.L_cusp ℓ)
  obtain ⟨_HLS, hLS⟩ := SBs.of_cuspBound (H := 3) (Work.Residues.LS_cusp ℓ)
  obtain ⟨_HX, hX⟩ := SBs.of_cuspBound (H := 3) (Work.Residues.X_cusp)
  obtain ⟨_HY, hY⟩ := SBs.of_cuspBound (H := 3) (Work.Residues.Y_cusp)
  obtain ⟨_HB, hB⟩ := SBs.of_cuspBound (H := 3) (Work.Residues.B0core_cusp)
  obtain ⟨_HC, hC⟩ := SBs.of_cuspBound (H := 3) (Work.Residues.Ccore_cusp ℓ)
  -- the five terms of `B'`
  have hT1 : SBs _ 0 _ :=
    (SBs.mul' hW (SBs.mul' hL hB)).mono0 (by norm_num)
  have hT2 : SBs _ 0 _ :=
    (SBs.mul' hW (SBs.mul' (SBs.const_mul' (2 : ℂ) hJz) (SBs.mul' hL hX))).mono0 (by norm_num)
  have hT3 : SBs _ 0 _ := (SBs.mul' hW hC).mono0 (by norm_num)
  have hT4 : SBs _ 0 _ :=
    (SBs.mul' hW (SBs.mul' (SBs.const_mul' (2 : ℂ) hJz) (SBs.mul' hLS hY))).mono0 (by norm_num)
  have hT5 : SBs _ 0 _ :=
    (SBs.mul' hW (SBs.mul' (SBs.const_mul' (3456 : ℂ) hDt) hJz)).mono0 (by norm_num)
  -- the `(E₁₀/Δ)(U²-V²)` term
  have hE10D : SBs _ (-2 : ℝ) _ := (SBs.mul' hE10 hInvDz).mono (by norm_num)
  have hUV : SBs _ 0 _ := (SBs.sub' (SBs.mul' hU hU) (SBs.mul' hV hV)).mono0 (by norm_num)
  have hXY : SBs _ 2 _ :=
    SBs.add' ((SBs.mul' hL hX).mono (by norm_num)) ((SBs.mul' hLS hY).mono (by norm_num))
  have hT6 : SBs _ 0 _ := (SBs.mul' (SBs.mul' hE10D hUV) hXY).mono0 (by norm_num)
  -- the `Δ (E₁₄/Δ) 𝓛` term
  have hE14D : SBs _ (-2 : ℝ) _ := (SBs.mul' hE14 hInvDz).mono (by norm_num)
  have hT7 : SBs _ 0 _ :=
    (SBs.mul' (SBs.const_mul' (-3456 : ℂ) hDt) (SBs.mul' hE14D hLz)).mono0 (by norm_num)
  refine ⟨_, SBs.congr
    (SBs.add' (SBs.add' (SBs.add' (SBs.add' (SBs.add' (SBs.add' hT1 hT2) hT3) hT4) hT5)
      hT6) hT7) (fun τ ζ => ?_)⟩
  rw [Work.Residues.Bprimefun]
  ring

/-- `K_-^{(24)}` is polynomially bounded on the spike circle: the prefactor `(kpre ζ τ)⁻¹` has
exponential weight `0`, and so does the bracket. -/
theorem SBs_KMinus24 (ℓ : LogLambdaData) :
    ∃ H : ℝ, SBs H 0 (fun τ ζ : ℍ => KMinus ℓ 24 τ ζ) := by
  obtain ⟨H1, hbr⟩ := SBs_bracket24_regroup ℓ
  have hbr' : SBs H1 0 (fun τ ζ : ℍ => Work.Residues.bracket24 ℓ ζ τ) :=
    SBs.congr hbr (fun τ ζ => by
      rw [Work.Residues.bracket24_eq, Work.Residues.bracket24_regroup]
      ring)
  have hk : SBs 3 0 (fun τ ζ : ℍ => (Work.Residues.kpre ζ τ)⁻¹) :=
    SBs_inv_kpre ℓ (le_refl 3)
  have hK : SBs (max 3 H1) 0 (fun τ ζ : ℍ => KMinus ℓ 24 τ ζ) :=
    SBs.congr ((SBs.mul' hk hbr').mono (by norm_num)) (fun τ ζ => by
      rw [Work.Asymptotics.Compact.KMinus24_eq ℓ τ ζ]
      exact congrArg (fun t => (Work.Residues.kpre ζ τ)⁻¹ * t)
        (Work.Residues.bracket24_eq ℓ ζ τ))
  exact ⟨max 3 H1, hK⟩

/-- The polynomial bound for `K_-^{(24)}` on the spike circle, above a threshold `H ≥ 3`. -/
theorem KM24_spike_bound (ℓ : LogLambdaData) :
    ∃ H C N : ℝ, 3 ≤ H ∧ 0 < C ∧ 0 ≤ N ∧ ∀ τ ζ : ℍ, Funnel τ →
      ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20 → H ≤ τ.im →
      ‖KMinus ℓ 24 τ ζ‖ ≤ C * (scale τ) ^ N := by
  obtain ⟨H, h⟩ := SBs_KMinus24 ℓ
  obtain ⟨C, N, hC, hN, hb⟩ := SBs.to_bound h le_rfl
  exact ⟨max 3 H, C, N, le_max_left _ _, hC, hN,
    fun τ ζ hτ hζ hH => hb τ ζ hτ hζ (le_trans (le_max_right _ _) hH)⟩

/-! ## The target

The half-sum `K = (K₊ + K₋)/2` of two `C (S τ)^N` bounds is again of that form; combining this
with the constant bound on the strip `Im τ ≤ H` gives the statement. -/

/-- Combining two polynomial bounds for the half-sum. -/
lemma half_add_bound {C1 C2 N1 N2 : ℝ} (hC1 : 0 < C1) (hC2 : 0 < C2)
    (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2) {τ : ℍ} {a b : ℂ}
    (ha : ‖a‖ ≤ C1 * (scale τ) ^ N1) (hb : ‖b‖ ≤ C2 * (scale τ) ^ N2) :
    ‖(a + b) / 2‖ ≤ ((C1 + C2 + 1) / 2) * (scale τ) ^ (max N1 N2) := by
  have hs : (1 : ℝ) ≤ scale τ := one_le_scale τ
  have hsp : (0 : ℝ) < scale τ := scale_pos τ
  have h0 : (0 : ℝ) ≤ (scale τ) ^ max N1 N2 := Real.rpow_nonneg hsp.le _
  have h1 : (scale τ) ^ N1 ≤ (scale τ) ^ max N1 N2 :=
    Real.rpow_le_rpow_of_exponent_le hs (le_max_left _ _)
  have h2 : (scale τ) ^ N2 ≤ (scale τ) ^ max N1 N2 :=
    Real.rpow_le_rpow_of_exponent_le hs (le_max_right _ _)
  have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
  have h5 : ‖a‖ + ‖b‖ ≤ (C1 + C2 + 1) * (scale τ) ^ max N1 N2 := by
    have e1 : C1 * (scale τ) ^ N1 ≤ C1 * (scale τ) ^ max N1 N2 :=
      mul_le_mul_of_nonneg_left h1 hC1.le
    have e2 : C2 * (scale τ) ^ N2 ≤ C2 * (scale τ) ^ max N1 N2 :=
      mul_le_mul_of_nonneg_left h2 hC2.le
    nlinarith [ha, hb, e1, e2, h0]
  rw [norm_div, h2n]
  calc ‖a + b‖ / 2 ≤ (‖a‖ + ‖b‖) / 2 :=
        div_le_div_of_nonneg_right (norm_add_le a b) (by norm_num)
    _ ≤ ((C1 + C2 + 1) * (scale τ) ^ max N1 N2) / 2 := by linarith
    _ = ((C1 + C2 + 1) / 2) * (scale τ) ^ max N1 N2 := by ring


end Work.Asymptotics.SpikeCircle
