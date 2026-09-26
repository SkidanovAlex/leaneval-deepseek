/-
# The spike-circle bound for the CKMRV kernel `K^{(d)}`

This file proves `Work.Asymptotics.SpikeCircle.Kfun_sphere_bound`: on the *spike circle*
`‖ζ - τ‖ = 29/20` around a point `τ` of the funnel, the CKMRV kernel `K^{(d)}` is bounded by a
power of the scale `S τ = 1 + (Im τ)⁻¹ + |τ|`:

  `‖K^{(d)}(τ,ζ)‖ ≤ C (S τ)^N`   (`d ∈ {8,24}`, `Im τ ≥ 2`, `j τ ≠ j ζ`).

The proof splits the kernel as `K = (K₊ + K₋)/2`, uses the *explicit* decompositions of
`K_±` (`KPlus_eight_decomposition`, `Compact.KMinus8_eq`, `Tail24.KPlus24_cusp`,
`Compact.KMinus24_eq` + `bracket24_regroup`), and estimates each atom on the spike circle.
The two exponential cancellations of the paper are supplied by the *proven* identities
`Residues.bracket8_eq` (`Γ`/`Λ` regrouping), `Residues.bracket24_regroup` and the bound
`psi_sub_funnel` (`ψ₄E₈ - ψ₂E₁₀ = O(q)`), together with the `O(q)` bound on the diagonal
bracket `diagW` (`diagW_spike` below).
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Residues.ThetaDecay
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.KPlus_eight_decomposition
import Submission.Work.Asymptotics.KPlus_tail24
import Submission.Work.Asymptotics.Compact.kminus_bracket
import Submission.Work.Asymptotics.KMinusFunnelAtoms
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.Funnel_Kfun_diag_bound
import Submission.Work.Asymptotics.SpikeCircle.DeltaFunBoundsHalf
import Submission.Work.Asymptotics.SpikeCircle.jInvariantFun_eq_iff_disc
import Submission.Work.Asymptotics.SpikeCircle.divisorLowerDisc
import Submission.Work.Asymptotics.SpikeCircle.jInvariantFunUpperDisc
import Submission.Work.Asymptotics.continuousOn_Kfun_clean

noncomputable section

open UpperHalfPlane
open scoped Topology

namespace Work.Asymptotics.SpikeCircle

open Work.Kernels

/-! ## Region facts -/

/-- Unfolding of the scale `S τ = 1 + (Im τ)⁻¹ + |τ|`. -/
lemma scale_eq (τ : ℍ) : scale τ = 1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖ := rfl

/-- On the spike circle, `Im ζ ≥ Im τ - 29/20`. -/
lemma im_zeta_ge {τ ζ : ℍ} (hζ : ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20) :
    ζ.im ≥ τ.im - 29 / 20 := by
  have h1 : |ζ.im - τ.im| ≤ ‖(ζ : ℂ) - (τ : ℂ)‖ := by
    have h := Complex.abs_im_le_norm ((ζ : ℂ) - (τ : ℂ))
    rwa [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im] at h
  rw [hζ] at h1
  have := (abs_le.mp h1).1
  linarith

/-- `‖ζ‖ ≤ ‖τ‖ + 29/20` on the spike circle. -/
lemma norm_zeta_le {τ ζ : ℍ} (hζ : ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20) :
    ‖(ζ : ℂ)‖ ≤ ‖(τ : ℂ)‖ + 29 / 20 := by
  have h := norm_add_le ((ζ : ℂ) - (τ : ℂ)) (τ : ℂ)
  rw [sub_add_cancel, hζ] at h
  linarith

/-- `|(ζ : ℂ)|² ≤ (2 S τ)²` for `Im τ ≥ 2`. -/
lemma norm_zeta_sq_le {τ ζ : ℍ} (hζ : ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20) (hH : 2 ≤ τ.im) :
    ‖(ζ : ℂ)‖ ^ 2 ≤ (2 * scale τ) ^ 2 := by
  have h1 := norm_zeta_le hζ
  have h2 : ‖(τ : ℂ)‖ ≤ scale τ := coe_norm_le_scale τ
  have h3 : (29 / 20 : ℝ) ≤ scale τ := by
    rw [scale_eq]
    have h := inv_nonneg.mpr τ.im_pos.le
    have h' : τ.im ≤ ‖(τ : ℂ)‖ := im_le_coe_norm τ
    linarith
  have h4 : ‖(ζ : ℂ)‖ ≤ 2 * scale τ := by linarith
  exact pow_le_pow_left₀ (norm_nonneg _) h4 2

/-- `S ζ ≤ 6 S τ` on the spike circle when `Im τ ≥ 10`. -/
lemma scale_zeta_le {τ ζ : ℍ} (hζ : ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20) (hH : 2 ≤ τ.im) :
    scale ζ ≤ 6 * scale τ := by
  rw [scale_eq, scale_eq]
  have hτ10 : (1 : ℝ) ≤ 1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖ := by
    have h := inv_nonneg.mpr τ.im_pos.le
    have h' := norm_nonneg (τ : ℂ)
    linarith
  have hζim : 11 / 20 ≤ ζ.im := by
    have := im_zeta_ge hζ; linarith
  have hinv : (ζ.im)⁻¹ ≤ 2 * (1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖) := by
    have h1 : (ζ.im)⁻¹ ≤ (11 / 20 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hζim
    have h2 : ((11 / 20 : ℝ))⁻¹ = 20 / 11 := by norm_num
    rw [h2] at h1
    linarith
  have hnorm : ‖(ζ : ℂ)‖ ≤ 3 * (1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖) := by
    have h1 := norm_zeta_le hζ
    have h2 : ‖(τ : ℂ)‖ ≤ 1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖ := by
      have h := inv_nonneg.mpr τ.im_pos.le; linarith
    linarith
  linarith

/-- `e^{2π Im ζ} ≤ e^{2π·29/20} e^{2π Im τ}` on the spike circle. -/
lemma exp_im_zeta_le {τ ζ : ℍ} (hζ : ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20) :
    Real.exp (2 * Real.pi * ζ.im)
      ≤ Real.exp (2 * Real.pi * (29 / 20)) * Real.exp (2 * Real.pi * τ.im) := by
  have h1 : |ζ.im - τ.im| ≤ 29 / 20 := by
    have h := Complex.abs_im_le_norm ((ζ : ℂ) - (τ : ℂ))
    rw [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im, hζ] at h
    exact h
  have h2 : ζ.im ≤ τ.im + 29 / 20 := by
    have := (abs_le.mp h1).2; linarith
  calc Real.exp (2 * Real.pi * ζ.im) ≤ Real.exp (2 * Real.pi * (τ.im + 29 / 20)) := by
        apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
    _ = Real.exp (2 * Real.pi * (29 / 20)) * Real.exp (2 * Real.pi * τ.im) := by
        rw [← Real.exp_add]; ring_nf

/-- `|ζ - (τ ± 1)| ≥ 9/20` on the spike circle. -/
lemma norm_sub_vadd_one_ge {τ ζ : ℍ} (hζ : ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20) :
    (9 / 20 : ℝ) ≤ ‖(ζ : ℂ) - ((τ : ℂ) + 1)‖ ∧
      (9 / 20 : ℝ) ≤ ‖(ζ : ℂ) - ((τ : ℂ) - 1)‖ := by
  constructor
  · have h1 : ((ζ : ℂ) - ((τ : ℂ) + 1)) + 1 = (ζ : ℂ) - (τ : ℂ) := by ring
    have h := norm_add_le ((ζ : ℂ) - ((τ : ℂ) + 1)) (1 : ℂ)
    rw [h1, hζ, norm_one] at h
    linarith
  · have h1 : ((ζ : ℂ) - ((τ : ℂ) - 1)) - 1 = (ζ : ℂ) - (τ : ℂ) := by ring
    have h := norm_sub_le ((ζ : ℂ) - ((τ : ℂ) - 1)) (1 : ℂ)
    rw [h1, hζ, norm_one] at h
    linarith


/-! ## A calculus of bounds on the spike circle

`SB f` means `‖f τ ζ‖ ≤ C (S τ)^N` on the spike circle with `Im τ ≥ 10`. -/

def SB (f : ℍ → ℍ → ℂ) : Prop :=
  ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ ζ : ℍ, Funnel τ → ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20 → 3 ≤ τ.im →
    ‖f τ ζ‖ ≤ C * (scale τ) ^ N

lemma SB.mono {C N : ℝ} {f : ℍ → ℍ → ℂ} (hC : 0 < C) (hN : 0 ≤ N)
    (h : ∀ τ ζ : ℍ, Funnel τ → ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20 → 3 ≤ τ.im →
      ‖f τ ζ‖ ≤ C * (scale τ) ^ N) : SB f := ⟨C, N, hC, hN, h⟩

lemma SB.congr {f g : ℍ → ℍ → ℂ} (hf : SB f) (h : ∀ τ ζ, f τ ζ = g τ ζ) : SB g := by
  obtain ⟨C, N, hC, hN, hb⟩ := hf
  exact ⟨C, N, hC, hN, fun τ ζ hτ hζ hH => by rw [← h τ ζ]; exact hb τ ζ hτ hζ hH⟩

lemma SB.add {f g : ℍ → ℍ → ℂ} (hf : SB f) (hg : SB g) :
    SB (fun τ ζ => f τ ζ + g τ ζ) := by
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := hf
  obtain ⟨C2, N2, hC2, hN2, hb2⟩ := hg
  refine SB.mono (C := C1 + C2) (N := max N1 N2) (by positivity) (le_max_of_le_left hN1)
    (fun τ ζ hτ hζ hH => ?_)
  have hs : (1 : ℝ) ≤ scale τ := one_le_scale τ
  have h1 : (scale τ) ^ N1 ≤ (scale τ) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs (le_max_left _ _)
  have h2 : (scale τ) ^ N2 ≤ (scale τ) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs (le_max_right _ _)
  calc ‖f τ ζ + g τ ζ‖ ≤ ‖f τ ζ‖ + ‖g τ ζ‖ := norm_add_le _ _
    _ ≤ C1 * (scale τ) ^ N1 + C2 * (scale τ) ^ N2 :=
        add_le_add (hb1 τ ζ hτ hζ hH) (hb2 τ ζ hτ hζ hH)
    _ ≤ C1 * (scale τ) ^ (max N1 N2) + C2 * (scale τ) ^ (max N1 N2) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hC1.le) (mul_le_mul_of_nonneg_left h2 hC2.le)
    _ = (C1 + C2) * (scale τ) ^ (max N1 N2) := by ring

lemma SB.neg {f : ℍ → ℍ → ℂ} (hf : SB f) : SB (fun τ ζ => - f τ ζ) := by
  obtain ⟨C, N, hC, hN, hb⟩ := hf
  exact SB.mono hC hN (fun τ ζ hτ hζ hH => by simpa using hb τ ζ hτ hζ hH)

lemma SB.sub {f g : ℍ → ℍ → ℂ} (hf : SB f) (hg : SB g) :
    SB (fun τ ζ => f τ ζ - g τ ζ) := by
  have h := SB.add hf (SB.neg hg)
  simpa [sub_eq_add_neg] using h

lemma SB.const_mul (c : ℂ) {f : ℍ → ℍ → ℂ} (hf : SB f) :
    SB (fun τ ζ => c * f τ ζ) := by
  obtain ⟨C, N, hC, hN, hb⟩ := hf
  refine SB.mono (C := ‖c‖ * C + 1) (N := N) (by positivity) hN (fun τ ζ hτ hζ hH => ?_)
  rw [norm_mul]
  have h1 : (1 : ℝ) ≤ (scale τ) ^ N := Real.one_le_rpow (one_le_scale τ) hN
  have h3 : (0 : ℝ) ≤ (scale τ) ^ N := Real.rpow_nonneg (le_of_lt (scale_pos τ)) N
  calc ‖c‖ * ‖f τ ζ‖ ≤ ‖c‖ * (C * (scale τ) ^ N) :=
        mul_le_mul_of_nonneg_left (hb τ ζ hτ hζ hH) (norm_nonneg c)
    _ = ‖c‖ * C * (scale τ) ^ N := by ring
    _ ≤ (‖c‖ * C + 1) * (scale τ) ^ N := by
        nlinarith [h1, h3, mul_nonneg (norm_nonneg c) hC.le]

lemma SB.mul {f g : ℍ → ℍ → ℂ} (hf : SB f) (hg : SB g) :
    SB (fun τ ζ => f τ ζ * g τ ζ) := by
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := hf
  obtain ⟨C2, N2, hC2, hN2, hb2⟩ := hg
  refine SB.mono (C := C1 * C2) (N := N1 + N2) (by positivity) (by positivity)
    (fun τ ζ hτ hζ hH => ?_)
  have hsp : (0 : ℝ) < scale τ := scale_pos τ
  calc ‖f τ ζ * g τ ζ‖ = ‖f τ ζ‖ * ‖g τ ζ‖ := norm_mul _ _
    _ ≤ (C1 * (scale τ) ^ N1) * (C2 * (scale τ) ^ N2) :=
        mul_le_mul (hb1 τ ζ hτ hζ hH) (hb2 τ ζ hτ hζ hH) (norm_nonneg _) (by positivity)
    _ = C1 * C2 * (scale τ) ^ (N1 + N2) := by rw [Real.rpow_add hsp]; ring

lemma SB.const (c : ℂ) : SB (fun _ _ : ℍ => c) :=
  SB.mono (C := ‖c‖ + 1) (N := 0) (by positivity) (le_refl 0) (fun τ ζ _ _ _ => by
    rw [Real.rpow_zero, mul_one]
    linarith [norm_nonneg c])


/-! ## Atoms of the estimates -/

lemma one_le_zeta_im {τ ζ : ℍ} (hζ : ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20) (hH : 3 ≤ τ.im) :
    1 ≤ ζ.im := by
  have h := im_zeta_ge hζ
  linarith

/-- `‖(ζ - τ - 1)(ζ - τ + 1)‖ ≥ (9/20)²` on the spike circle. -/
lemma prod_sub_vadd_one_ge {τ ζ : ℍ} (hζ : ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20) :
    ((9 / 20 : ℝ) * (9 / 20)) ≤ ‖((ζ : ℂ) - ((τ : ℂ) + 1)) * ((ζ : ℂ) - ((τ : ℂ) - 1))‖ := by
  obtain ⟨h1, h2⟩ := norm_sub_vadd_one_ge hζ
  rw [norm_mul]
  nlinarith [norm_nonneg ((ζ : ℂ) - ((τ : ℂ) + 1)), norm_nonneg ((ζ : ℂ) - ((τ : ℂ) - 1))]

lemma SB_tau : SB (fun τ _ => (τ : ℂ)) :=
  SB.mono (C := 1) (N := 1) one_pos (by norm_num) (fun τ ζ hτ hζ hH => by
    rw [Real.rpow_one, one_mul]
    exact coe_norm_le_scale τ)

lemma SB_zeta_sq : SB (fun _ ζ => (ζ : ℂ) ^ 2) := by
  refine SB.mono (C := 4) (N := 2) (by norm_num) (by norm_num) (fun τ ζ hτ hζ hH => ?_)
  rw [norm_pow, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h := norm_zeta_sq_le hζ (Funnel.im_two hτ)
  calc ‖(ζ : ℂ)‖ ^ 2 ≤ (2 * scale τ) ^ 2 := h
    _ = 4 * (scale τ) ^ 2 := by ring

lemma SB_E4_tau : SB (fun τ _ => E4Fun τ) := by
  obtain ⟨C, hC, h⟩ := exists_E4_Funnel_bound
  exact SB.mono (C := C) (N := 0) hC (le_refl 0) (fun τ ζ hτ hζ hH => by
    rw [Real.rpow_zero, mul_one]; exact h τ hτ)

lemma SB_E6_tau : SB (fun τ _ => E6Fun τ) := by
  obtain ⟨C, hC, h⟩ := exists_E6_Funnel_bound
  exact SB.mono (C := C) (N := 0) hC (le_refl 0) (fun τ ζ hτ hζ hH => by
    rw [Real.rpow_zero, mul_one]; exact h τ hτ)

lemma SB_E2_tau : SB (fun τ _ => E2Fun τ) := by
  obtain ⟨C, hC, h⟩ := exists_E2_Funnel_bound
  exact SB.mono (C := C) (N := 0) hC (le_refl 0) (fun τ ζ hτ hζ hH => by
    rw [Real.rpow_zero, mul_one]; exact h τ hτ)

lemma SB_E8_tau : SB (fun τ _ => E8Fun τ) := by
  obtain ⟨C, hC, h⟩ := exists_E4_Funnel_bound
  refine SB.mono (C := C ^ 2 + 1) (N := 0) (by positivity) (le_refl 0) (fun τ ζ hτ hζ hH => ?_)
  rw [Real.rpow_zero, mul_one]
  have h1 : E8Fun τ = E4Fun τ ^ 2 := rfl
  rw [h1, norm_pow]
  have h2 := h τ hτ
  have h3 : ‖E4Fun τ‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  linarith

lemma SB_E10_tau : SB (fun τ _ => E10Fun τ) := by
  obtain ⟨C4, hC4, h4⟩ := exists_E4_Funnel_bound
  obtain ⟨C6, hC6, h6⟩ := exists_E6_Funnel_bound
  refine SB.mono (C := C4 * C6 + 1) (N := 0) (by positivity) (le_refl 0) (fun τ ζ hτ hζ hH => ?_)
  rw [Real.rpow_zero, mul_one]
  have h1 : E10Fun τ = E4Fun τ * E6Fun τ := rfl
  rw [h1, norm_mul]
  exact le_trans (mul_le_mul (h4 τ hτ) (h6 τ hτ) (norm_nonneg _) hC4.le) (by linarith)

lemma SB_E14_tau : SB (fun τ _ => E14Fun τ) := by
  obtain ⟨C4, hC4, h4⟩ := exists_E4_Funnel_bound
  obtain ⟨C6, hC6, h6⟩ := exists_E6_Funnel_bound
  refine SB.mono (C := C4 ^ 2 * C6 + 1) (N := 0) (by positivity) (le_refl 0) (fun τ ζ hτ hζ hH => ?_)
  rw [Real.rpow_zero, mul_one]
  have h1 : E14Fun τ = E4Fun τ ^ 2 * E6Fun τ := rfl
  rw [h1, norm_mul, norm_pow]
  have h2 := h4 τ hτ
  have h3 := h6 τ hτ
  have h5 : ‖E4Fun τ‖ ^ 2 ≤ C4 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  exact le_trans (mul_le_mul h5 h3 (norm_nonneg _) (by positivity)) (by nlinarith [hC4, hC6])

lemma SB_phi0_tau : SB (fun τ _ => phi0 τ) := by
  obtain ⟨C, hC, h⟩ := E2Fun_bound
  refine SB.mono (C := C + 3 / Real.pi + 1) (N := 1) (by positivity) (by norm_num)
    (fun τ ζ hτ hζ hH => ?_)
  rw [Real.rpow_one]
  have h2 := h τ (Funnel.im_one hτ)
  have h3 : ‖(τ : ℂ)‖ ≤ scale τ := coe_norm_le_scale τ
  have h4 : (1 : ℝ) ≤ scale τ := one_le_scale τ
  have h5 : ‖phi0 τ‖ ≤ ‖(τ : ℂ)‖ * ‖E2Fun τ‖ + 3 / Real.pi := by
    rw [show phi0 τ = (τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ) from rfl]
    calc ‖(τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)‖
        ≤ ‖(τ : ℂ) * E2Fun τ‖ + ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ := norm_sub_le _ _
      _ = ‖(τ : ℂ)‖ * ‖E2Fun τ‖ + 3 / Real.pi := by
          rw [norm_mul, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
            Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have h6 : ‖(τ : ℂ)‖ * ‖E2Fun τ‖ ≤ C * scale τ :=
    le_trans (mul_le_mul h3 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h3)) (le_of_eq (by ring))
  have h7 : (3 : ℝ) / Real.pi ≤ (3 / Real.pi) * scale τ := by
    have := mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ 3 / Real.pi)
    simpa using this
  have h8 : ‖phi0 τ‖ ≤ (C + 3 / Real.pi) * scale τ := by
    calc ‖phi0 τ‖ ≤ ‖(τ : ℂ)‖ * ‖E2Fun τ‖ + 3 / Real.pi := h5
      _ ≤ C * scale τ + (3 / Real.pi) * scale τ := add_le_add h6 h7
      _ = (C + 3 / Real.pi) * scale τ := by ring
  calc ‖phi0 τ‖ ≤ (C + 3 / Real.pi) * scale τ := h8
    _ ≤ (C + 3 / Real.pi + 1) * scale τ := by
        nlinarith [h4, hC.le, Real.pi_pos, one_le_scale τ]

lemma SB_phi2_tau : SB (fun τ _ => phi2 τ) := by
  obtain ⟨C, hC, h⟩ := E2Fun_bound
  refine SB.mono (C := C ^ 2 + 6 * C / Real.pi + 1) (N := 2) (by positivity) (by norm_num)
    (fun τ ζ hτ hζ hH => ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h2 := h τ (Funnel.im_one hτ)
  have h3 : ‖(τ : ℂ)‖ ≤ scale τ := coe_norm_le_scale τ
  have h4 : (1 : ℝ) ≤ scale τ := one_le_scale τ
  have h5 : ‖phi2 τ‖ ≤ ‖(τ : ℂ)‖ * C ^ 2 + (6 / Real.pi) * C := by
    rw [show phi2 τ = (τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ from rfl]
    have h6 : ‖(τ : ℂ) * E2Fun τ ^ 2‖ = ‖(τ : ℂ)‖ * ‖E2Fun τ‖ ^ 2 := by
      rw [norm_mul, norm_pow]
    have h7 : ‖(6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ‖ = (6 / Real.pi) * ‖E2Fun τ‖ := by
      rw [norm_mul, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    calc ‖(τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ‖
        ≤ ‖(τ : ℂ) * E2Fun τ ^ 2‖ + ‖(6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ‖ := norm_sub_le _ _
      _ = ‖(τ : ℂ)‖ * ‖E2Fun τ‖ ^ 2 + (6 / Real.pi) * ‖E2Fun τ‖ := by rw [h6, h7]
      _ ≤ ‖(τ : ℂ)‖ * C ^ 2 + (6 / Real.pi) * C := by
          have h8 : ‖E2Fun τ‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
          have h9 : (6 / Real.pi) * ‖E2Fun τ‖ ≤ (6 / Real.pi) * C :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left h8 (norm_nonneg (τ : ℂ)), h9]
  have hsp : (1 : ℝ) ≤ (scale τ) ^ 2 := one_le_pow₀ h4
  have h6 : ‖(τ : ℂ)‖ * C ^ 2 ≤ scale τ * C ^ 2 := mul_le_mul_of_nonneg_right h3 (by positivity)
  have h7 : (6 / Real.pi) * C ≤ (6 / Real.pi) * C * scale τ := by
    have := mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ (6 / Real.pi) * C)
    simpa [mul_assoc] using this
  have h9 : (0 : ℝ) ≤ C ^ 2 + 6 * C / Real.pi := by positivity
  calc ‖phi2 τ‖ ≤ ‖(τ : ℂ)‖ * C ^ 2 + (6 / Real.pi) * C := h5
    _ ≤ scale τ * C ^ 2 + (6 / Real.pi) * C * scale τ := add_le_add h6 h7
    _ = (C ^ 2 + 6 * C / Real.pi) * scale τ := by ring
    _ ≤ (C ^ 2 + 6 * C / Real.pi) * scale τ * scale τ := by
        have hX : (0 : ℝ) ≤ (C ^ 2 + 6 * C / Real.pi) * scale τ := by positivity
        have := mul_le_mul_of_nonneg_left h4 hX
        simpa using this
    _ ≤ (C ^ 2 + 6 * C / Real.pi + 1) * scale τ * scale τ := by
        have hX : (0 : ℝ) ≤ scale τ * scale τ := by positivity
        nlinarith [hX]
    _ = (C ^ 2 + 6 * C / Real.pi + 1) * (scale τ) ^ 2 := by ring

lemma SB_psi2_tau (ℓ : LogLambdaData) : SB (fun τ _ => psi2 ℓ τ) := by
  obtain ⟨C, N, hC, hN, h⟩ := psi_scale_funnel ℓ
  exact SB.mono hC hN (fun τ ζ hτ hζ hH => (h τ hτ).1)

lemma SB_psi4_tau (ℓ : LogLambdaData) : SB (fun τ _ => psi4 ℓ τ) := by
  obtain ⟨C, N, hC, hN, h⟩ := psi_scale_funnel ℓ
  exact SB.mono hC hN (fun τ ζ hτ hζ hH => (h τ hτ).2)

lemma SB_Lamb_tau (ℓ : LogLambdaData) : SB (fun τ _ => Work.Residues.Lamb ℓ τ) := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.FunnelNumerics.Lamb_funnel_bound ℓ
  refine SB.mono (C := 2 * C + 1) (N := N) (by positivity) hN (fun τ ζ hτ hζ hH => ?_)
  have hD := (Work.FunnelNumerics.Delta_funnel_bounds).1 τ (Funnel.im_two hτ)
  have hq : 0 < ‖qParamFun τ‖ := norm_pos_iff.mpr (qParamFun_ne_zero' τ)
  have hL : ‖DeltaFun τ‖ * ‖Work.Residues.Lamb ℓ τ‖ ≤ C * (scale τ) ^ N * ‖qParamFun τ‖ := by
    rw [← norm_mul]; exact h τ hτ
  have h3 : (1 / 2 : ℝ) * ‖qParamFun τ‖ * ‖Work.Residues.Lamb ℓ τ‖ ≤
      C * (scale τ) ^ N * ‖qParamFun τ‖ :=
    le_trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _)) hL
  have h3' : ‖qParamFun τ‖ * ((1 / 2) * ‖Work.Residues.Lamb ℓ τ‖) ≤
      ‖qParamFun τ‖ * (C * (scale τ) ^ N) := by
    calc ‖qParamFun τ‖ * ((1 / 2) * ‖Work.Residues.Lamb ℓ τ‖)
        = (1 / 2) * ‖qParamFun τ‖ * ‖Work.Residues.Lamb ℓ τ‖ := by ring
      _ ≤ C * (scale τ) ^ N * ‖qParamFun τ‖ := h3
      _ = ‖qParamFun τ‖ * (C * (scale τ) ^ N) := by ring
  have h4 : (1 / 2) * ‖Work.Residues.Lamb ℓ τ‖ ≤ C * (scale τ) ^ N :=
    (mul_le_mul_iff_of_pos_left hq).mp h3'
  have hsp : (1 : ℝ) ≤ (scale τ) ^ N := Real.one_le_rpow (one_le_scale τ) hN
  have h5 : ‖Work.Residues.Lamb ℓ τ‖ ≤ 2 * C * (scale τ) ^ N := by
    nlinarith [h4]
  calc ‖Work.Residues.Lamb ℓ τ‖ ≤ 2 * C * (scale τ) ^ N := h5
    _ ≤ (2 * C + 1) * (scale τ) ^ N := by nlinarith [hsp]

lemma SB_Gamm_tau (ℓ : LogLambdaData) : SB (fun τ _ => Work.Residues.Gamm ℓ τ) := by
  have h := SB.sub (SB.const_mul (1728 : ℂ) (SB_psi4_tau ℓ)) (SB_Lamb_tau ℓ)
  refine SB.congr h (fun τ ζ => ?_)
  show 1728 * psi4 ℓ τ - Work.Residues.Lamb ℓ τ = Work.Residues.Gamm ℓ τ
  rw [Work.Residues.Gamm, Work.Residues.Lamb]
  simp only [c1728]
  ring

lemma SB_inv_DeltaTauJ :
    SB (fun τ ζ => (DeltaFun τ * (jInvariantFun τ - jInvariantFun ζ))⁻¹) := by
  obtain ⟨cJ, hcJ, hJ⟩ := divisorLowerDisc
  set δ : ℝ := (29 / 20) * (9 / 20) * (9 / 20) with hδ
  have hδpos : 0 < δ := by rw [hδ]; norm_num
  refine SB.mono (C := 2 / (cJ * δ) + 1) (N := 0) (by positivity) (le_refl 0)
    (fun τ ζ hτ hζ hH => ?_)
  rw [Real.rpow_zero, mul_one]
  have hD : (1 / 2 : ℝ) * ‖qParamFun τ‖ ≤ ‖DeltaFun τ‖ :=
    (Work.FunnelNumerics.Delta_funnel_bounds).1 τ (Funnel.im_two hτ)
  have hqe : ‖qParamFun τ‖ * Real.exp (2 * Real.pi * τ.im) = 1 := by
    rw [norm_qParamFun, ← Real.exp_add]; simp
  have hP : δ ≤ ‖((ζ : ℂ) - (τ : ℂ)) * ((ζ : ℂ) - ((τ : ℂ) - 1)) * ((ζ : ℂ) - ((τ : ℂ) + 1))‖ := by
    have h1 : ‖((ζ : ℂ) - (τ : ℂ)) * ((ζ : ℂ) - ((τ : ℂ) - 1)) * ((ζ : ℂ) - ((τ : ℂ) + 1))‖
        = (29 / 20) * (‖(ζ : ℂ) - ((τ : ℂ) - 1)‖ * ‖(ζ : ℂ) - ((τ : ℂ) + 1)‖) := by
      rw [norm_mul, norm_mul, hζ]; ring
    rw [h1, hδ]
    have hq := prod_sub_vadd_one_ge hζ
    rw [norm_mul, mul_comm ‖((ζ : ℂ) - ((τ : ℂ) + 1))‖ ‖((ζ : ℂ) - ((τ : ℂ) - 1))‖] at hq
    calc (29 / 20 : ℝ) * (9 / 20) * (9 / 20)
        = (29 / 20) * ((9 / 20) * (9 / 20)) := by ring
      _ ≤ (29 / 20) * (‖(ζ : ℂ) - ((τ : ℂ) - 1)‖ * ‖(ζ : ℂ) - ((τ : ℂ) + 1)‖) :=
          mul_le_mul_of_nonneg_left hq (by norm_num)
  have h3 : cJ * Real.exp (2 * Real.pi * τ.im) * δ ≤ ‖jInvariantFun τ - jInvariantFun ζ‖ := by
    have hc : 0 < cJ * Real.exp (2 * Real.pi * τ.im) := by positivity
    exact le_trans (mul_le_mul_of_nonneg_left hP hc.le) (hJ τ ζ hτ (le_of_eq hζ))
  have h4 : (cJ * δ / 2) * (‖qParamFun τ‖ * Real.exp (2 * Real.pi * τ.im)) ≤
      ‖DeltaFun τ‖ * ‖jInvariantFun τ - jInvariantFun ζ‖ := by
    have h5 : (1 / 2 : ℝ) * ‖qParamFun τ‖ * (cJ * Real.exp (2 * Real.pi * τ.im) * δ) =
        (cJ * δ / 2) * (‖qParamFun τ‖ * Real.exp (2 * Real.pi * τ.im)) := by ring
    rw [← h5]
    exact mul_le_mul hD h3 (by positivity) (by positivity)
  have hprod : cJ * δ / 2 ≤ ‖DeltaFun τ * (jInvariantFun τ - jInvariantFun ζ)‖ := by
    rw [norm_mul]
    calc cJ * δ / 2 = (cJ * δ / 2) * (‖qParamFun τ‖ * Real.exp (2 * Real.pi * τ.im)) := by
          rw [hqe, mul_one]
      _ ≤ ‖DeltaFun τ‖ * ‖jInvariantFun τ - jInvariantFun ζ‖ := h4
  have hpos : 0 < cJ * δ / 2 := by positivity
  have hxpos : 0 < ‖DeltaFun τ * (jInvariantFun τ - jInvariantFun ζ)‖ :=
    lt_of_lt_of_le hpos hprod
  calc ‖(DeltaFun τ * (jInvariantFun τ - jInvariantFun ζ))⁻¹‖
      = (‖DeltaFun τ * (jInvariantFun τ - jInvariantFun ζ)‖)⁻¹ := norm_inv _
    _ ≤ (cJ * δ / 2)⁻¹ := (inv_le_inv₀ hxpos hpos).mpr hprod
    _ = 2 / (cJ * δ) := by rw [inv_div]
    _ ≤ 2 / (cJ * δ) + 1 := by linarith

lemma SB_inv_DeltaZetaJ :
    SB (fun τ ζ => (DeltaFun ζ * (jInvariantFun τ - jInvariantFun ζ))⁻¹) := by
  obtain ⟨cΔ, CΔ, hcΔ, hCΔ, hΔ⟩ := DeltaFunBoundsHalf
  obtain ⟨cJ, hcJ, hJ⟩ := divisorLowerDisc
  set δ : ℝ := (29 / 20) * (9 / 20) * (9 / 20) with hδ
  have hδpos : 0 < δ := by rw [hδ]; norm_num
  refine SB.mono (C := (1 / (cΔ * cJ * δ)) * Real.exp (2 * Real.pi * (29 / 20)) + 1) (N := 0)
    (by positivity) (le_refl 0) (fun τ ζ hτ hζ hH => ?_)
  rw [Real.rpow_zero, mul_one]
  have h1 : cΔ * Real.exp (-(2 * Real.pi * ζ.im)) ≤ ‖DeltaFun ζ‖ :=
    (hΔ ζ (by have := one_le_zeta_im hζ hH; linarith)).1
  have hP : δ ≤ ‖((ζ : ℂ) - (τ : ℂ)) * ((ζ : ℂ) - ((τ : ℂ) - 1)) * ((ζ : ℂ) - ((τ : ℂ) + 1))‖ := by
    have h1' : ‖((ζ : ℂ) - (τ : ℂ)) * ((ζ : ℂ) - ((τ : ℂ) - 1)) * ((ζ : ℂ) - ((τ : ℂ) + 1))‖
        = (29 / 20) * (‖(ζ : ℂ) - ((τ : ℂ) - 1)‖ * ‖(ζ : ℂ) - ((τ : ℂ) + 1)‖) := by
      rw [norm_mul, norm_mul, hζ]; ring
    rw [h1', hδ]
    have hq := prod_sub_vadd_one_ge hζ
    rw [norm_mul, mul_comm ‖((ζ : ℂ) - ((τ : ℂ) + 1))‖ ‖((ζ : ℂ) - ((τ : ℂ) - 1))‖] at hq
    calc (29 / 20 : ℝ) * (9 / 20) * (9 / 20)
        = (29 / 20) * ((9 / 20) * (9 / 20)) := by ring
      _ ≤ (29 / 20) * (‖(ζ : ℂ) - ((τ : ℂ) - 1)‖ * ‖(ζ : ℂ) - ((τ : ℂ) + 1)‖) :=
          mul_le_mul_of_nonneg_left hq (by norm_num)
  have h3 : cJ * Real.exp (2 * Real.pi * τ.im) * δ ≤ ‖jInvariantFun τ - jInvariantFun ζ‖ := by
    have hc : 0 < cJ * Real.exp (2 * Real.pi * τ.im) := by positivity
    exact le_trans (mul_le_mul_of_nonneg_left hP hc.le) (hJ τ ζ hτ (le_of_eq hζ))
  have hE : Real.exp (-(2 * Real.pi * (29 / 20))) ≤
      Real.exp (2 * Real.pi * τ.im) * Real.exp (-(2 * Real.pi * ζ.im)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : |ζ.im - τ.im| ≤ 29 / 20 := by
      have h := Complex.abs_im_le_norm ((ζ : ℂ) - (τ : ℂ))
      rw [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im, hζ] at h
      exact h
    have h2 : ζ.im ≤ τ.im + 29 / 20 := by have := (abs_le.mp h1).2; linarith
    have h3 : 2 * Real.pi * τ.im + -(2 * Real.pi * ζ.im) = 2 * Real.pi * (τ.im - ζ.im) := by ring
    rw [h3]
    have h4 : -(29 / 20) ≤ τ.im - ζ.im := by linarith
    nlinarith [Real.pi_pos, h4]
  have h4 : cΔ * cJ * δ * Real.exp (-(2 * Real.pi * (29 / 20))) ≤
      ‖DeltaFun ζ‖ * ‖jInvariantFun τ - jInvariantFun ζ‖ := by
    calc cΔ * cJ * δ * Real.exp (-(2 * Real.pi * (29 / 20)))
        ≤ cΔ * cJ * δ * (Real.exp (2 * Real.pi * τ.im) * Real.exp (-(2 * Real.pi * ζ.im))) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ = (cΔ * Real.exp (-(2 * Real.pi * ζ.im))) *
            (cJ * Real.exp (2 * Real.pi * τ.im) * δ) := by ring
      _ ≤ ‖DeltaFun ζ‖ * ‖jInvariantFun τ - jInvariantFun ζ‖ :=
          mul_le_mul h1 h3 (by positivity) (by positivity)
  have hprod : cΔ * cJ * δ * Real.exp (-(2 * Real.pi * (29 / 20))) ≤
      ‖DeltaFun ζ * (jInvariantFun τ - jInvariantFun ζ)‖ := by
    rw [norm_mul]; exact h4
  have hpos : 0 < cΔ * cJ * δ * Real.exp (-(2 * Real.pi * (29 / 20))) := by positivity
  have hxpos : 0 < ‖DeltaFun ζ * (jInvariantFun τ - jInvariantFun ζ)‖ :=
    lt_of_lt_of_le hpos hprod
  calc ‖(DeltaFun ζ * (jInvariantFun τ - jInvariantFun ζ))⁻¹‖
      = (‖DeltaFun ζ * (jInvariantFun τ - jInvariantFun ζ)‖)⁻¹ := norm_inv _
    _ ≤ (cΔ * cJ * δ * Real.exp (-(2 * Real.pi * (29 / 20))))⁻¹ :=
        (inv_le_inv₀ hxpos hpos).mpr hprod
    _ = (1 / (cΔ * cJ * δ)) * Real.exp (2 * Real.pi * (29 / 20)) := by
        rw [mul_inv, Real.exp_neg, inv_inv, one_div]
    _ ≤ (1 / (cΔ * cJ * δ)) * Real.exp (2 * Real.pi * (29 / 20)) + 1 := by linarith


/-- Transfer of an `SB` bound along a pointwise equality valid on the spike circle. -/
lemma SB.of_pointwise {f g : ℍ → ℍ → ℂ} (hf : SB f)
    (h : ∀ τ ζ : ℍ, Funnel τ → ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20 → 3 ≤ τ.im → f τ ζ = g τ ζ) :
    SB g := by
  obtain ⟨C, N, hC, hN, hb⟩ := hf
  exact ⟨C, N, hC, hN, fun τ ζ hτ hζ hH => by rw [← h τ ζ hτ hζ hH]; exact hb τ ζ hτ hζ hH⟩

/-- On the spike circle the coincidence `j τ = j ζ` is impossible. -/
lemma jne_of_spike {τ ζ : ℍ} (hτ : Funnel τ) (hζ : ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20) :
    jInvariantFun τ ≠ jInvariantFun ζ := by
  intro h
  have h' := (jInvariantFun_eq_iff_disc hτ (le_of_eq hζ)).mp h
  rcases h' with h1 | h1 | h1
  · rw [h1, sub_self, norm_zero] at hζ; norm_num at hζ
  · have h2 : ‖(((1 : ℝ) +ᵥ τ : ℍ) : ℂ) - (τ : ℂ)‖ = 1 := by
      rw [UpperHalfPlane.coe_vadd]; push_cast; simp
    rw [h1, h2] at hζ; norm_num at hζ
  · have h2 : ‖(((-1 : ℝ) +ᵥ τ : ℍ) : ℂ) - (τ : ℂ)‖ = 1 := by
      rw [UpperHalfPlane.coe_vadd]; push_cast; simp
    rw [h1, h2] at hζ; norm_num at hζ

lemma SB_L_zeta (ℓ : LogLambdaData) : SB (fun _ ζ => ℓ.L ζ) := by
  obtain ⟨α, N, hα, hN, hb⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale Set.univ (ℓ.L)).mp ℓ.memP
  refine SB.mono (C := α * 6 ^ N + 1) (N := N) (by positivity) hN (fun τ ζ hτ hζ hH => ?_)
  have h1 := hb ζ (Set.mem_univ ζ)
  have h2 : scale ζ ≤ 6 * scale τ := scale_zeta_le hζ (Funnel.im_two hτ)
  have h3 : (scale ζ) ^ N ≤ (6 * scale τ) ^ N := Real.rpow_le_rpow (scale_pos ζ).le h2 hN
  have h4 : (6 * scale τ) ^ N = 6 ^ N * (scale τ) ^ N := Real.mul_rpow (by norm_num) (scale_pos τ).le
  have h5 : (0 : ℝ) ≤ (scale τ) ^ N := Real.rpow_nonneg (scale_pos τ).le N
  rw [h4] at h3
  calc ‖ℓ.L ζ‖ ≤ α * (scale ζ) ^ N := h1
    _ ≤ α * (6 ^ N * (scale τ) ^ N) := mul_le_mul_of_nonneg_left h3 hα
    _ = α * 6 ^ N * (scale τ) ^ N := by ring
    _ ≤ (α * 6 ^ N + 1) * (scale τ) ^ N := by
        have h6 : (0 : ℝ) ≤ 6 ^ N := Real.rpow_nonneg (by norm_num) N
        nlinarith [mul_nonneg hα h6, h5]

/-- `‖(Real.pi : ℂ)‖ = Real.pi`. -/
lemma norm_pi : ‖(Real.pi : ℂ)‖ = Real.pi := by
  rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self Real.pi_pos.le]

/-- `diagW` is `O(q)` at the cusp. -/
lemma diagW_exp_bound : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
    ‖diagW τ‖ ≤ C * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) := by
  obtain ⟨C1, hC1, h1⟩ := delta1_isBigOq
  obtain ⟨C2, hC2, h2⟩ := eps_isBigOq
  obtain ⟨C3, hC3, h3⟩ := E2Fun_bdd
  obtain ⟨C4, hC4, h4⟩ := E6Fun_bdd
  have hG : ∀ τ : ℍ, 1 ≤ τ.im →
      ‖E6Fun τ * (E4Fun τ + E2Fun τ ^ 2) - 2 * E4Fun τ ^ 2 * E2Fun τ‖
        ≤ (C4 * C1 + 2 * C3 * C2) * ‖qParamFun τ‖ := by
    intro τ hτ
    have hA : ‖E2Fun τ ^ 2 - E4Fun τ‖ ≤ C1 * ‖qParamFun τ‖ := by
      have := h1 τ hτ
      rwa [pow_one, norm_sub_rev] at this
    have hB : ‖E4Fun τ ^ 2 - E6Fun τ * E2Fun τ‖ ≤ C2 * ‖qParamFun τ‖ := by
      have := h2 τ hτ
      rwa [pow_one] at this
    have hE2 : ‖E2Fun τ‖ ≤ C3 := by
      have := h3 τ hτ; simpa [Real.rpow_zero] using this
    have hE6 : ‖E6Fun τ‖ ≤ C4 := by
      have := h4 τ hτ; simpa [Real.rpow_zero] using this
    have hfac : E6Fun τ * (E4Fun τ + E2Fun τ ^ 2) - 2 * E4Fun τ ^ 2 * E2Fun τ
        = -(E6Fun τ * (E2Fun τ ^ 2 - E4Fun τ))
          - 2 * E2Fun τ * (E4Fun τ ^ 2 - E6Fun τ * E2Fun τ) := by ring
    rw [hfac]
    calc ‖-(E6Fun τ * (E2Fun τ ^ 2 - E4Fun τ))
            - 2 * E2Fun τ * (E4Fun τ ^ 2 - E6Fun τ * E2Fun τ)‖
        ≤ ‖-(E6Fun τ * (E2Fun τ ^ 2 - E4Fun τ))‖
            + ‖2 * E2Fun τ * (E4Fun τ ^ 2 - E6Fun τ * E2Fun τ)‖ := norm_sub_le _ _
      _ = ‖E6Fun τ‖ * ‖E2Fun τ ^ 2 - E4Fun τ‖
            + 2 * ‖E2Fun τ‖ * ‖E4Fun τ ^ 2 - E6Fun τ * E2Fun τ‖ := by
          simp only [norm_neg, norm_mul, Complex.norm_ofNat]
      _ ≤ C4 * (C1 * ‖qParamFun τ‖) + 2 * C3 * (C2 * ‖qParamFun τ‖) := by
          refine add_le_add (mul_le_mul hE6 hA (norm_nonneg _) hC4.le) ?_
          refine mul_le_mul ?_ hB (norm_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hE2 (by norm_num)
      _ = (C4 * C1 + 2 * C3 * C2) * ‖qParamFun τ‖ := by ring
  refine ⟨(C4 * C1 + 2 * C3 * C2) + (6 / Real.pi) * C2, 1, by positivity, by norm_num,
    fun τ hτ => ?_⟩
  have hτ1 : 1 ≤ τ.im := Funnel.im_one hτ
  have hH := hG τ hτ1
  have hH2 : ‖E4Fun τ ^ 2 - E6Fun τ * E2Fun τ‖ ≤ C2 * ‖qParamFun τ‖ := by
    have := h2 τ hτ1; rwa [pow_one] at this
  rw [show diagW τ = (τ : ℂ) * (E6Fun τ * (E4Fun τ + E2Fun τ ^ 2) - 2 * E4Fun τ ^ 2 * E2Fun τ)
      + (6 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 2 - E6Fun τ * E2Fun τ) from by
    simp only [diagW, phiNeg2, phi0, phi2]; ring]
  have h6 : ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 6 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, norm_pi]
  have hq : ‖qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) := norm_qParamFun τ
  have htn : ‖(τ : ℂ)‖ ≤ scale τ := coe_norm_le_scale τ
  have hsp : (1 : ℝ) ≤ scale τ := one_le_scale τ
  calc ‖(τ : ℂ) * (E6Fun τ * (E4Fun τ + E2Fun τ ^ 2) - 2 * E4Fun τ ^ 2 * E2Fun τ)
          + (6 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 2 - E6Fun τ * E2Fun τ)‖
      ≤ ‖(τ : ℂ) * (E6Fun τ * (E4Fun τ + E2Fun τ ^ 2) - 2 * E4Fun τ ^ 2 * E2Fun τ)‖
          + ‖(6 * Complex.I / (Real.pi : ℂ)) * (E4Fun τ ^ 2 - E6Fun τ * E2Fun τ)‖ := norm_add_le _ _
    _ = ‖(τ : ℂ)‖ * ‖E6Fun τ * (E4Fun τ + E2Fun τ ^ 2) - 2 * E4Fun τ ^ 2 * E2Fun τ‖
          + (6 / Real.pi) * ‖E4Fun τ ^ 2 - E6Fun τ * E2Fun τ‖ := by rw [norm_mul, norm_mul, h6]
    _ ≤ scale τ * ((C4 * C1 + 2 * C3 * C2) * ‖qParamFun τ‖)
          + (6 / Real.pi) * (C2 * ‖qParamFun τ‖) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul htn hH (norm_nonneg _) (le_trans (norm_nonneg _) htn)
        · exact mul_le_mul_of_nonneg_left hH2 (by positivity)
    _ ≤ ((C4 * C1 + 2 * C3 * C2) + (6 / Real.pi) * C2) * (scale τ) ^ (1 : ℝ)
          * Real.exp (-(2 * Real.pi * τ.im)) := by
        rw [Real.rpow_one, hq]
        have hX : (0 : ℝ) ≤ C4 * C1 + 2 * C3 * C2 := by positivity
        have hY : (0 : ℝ) ≤ (6 / Real.pi) * C2 := by positivity
        have hsp : (1 : ℝ) ≤ scale τ := one_le_scale τ
        have he : (0 : ℝ) < Real.exp (-(2 * Real.pi * τ.im)) := Real.exp_pos _
        have he0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * τ.im)) := he.le
        have ht0 : (0 : ℝ) ≤ scale τ := le_trans (by norm_num) hsp
        nlinarith [mul_nonneg hX (mul_nonneg ht0 he0), mul_nonneg hY he0,
          mul_nonneg hX he0, mul_nonneg (mul_nonneg hX he0) ht0,
          mul_nonneg (mul_nonneg hY he0) ht0]


/-- `‖E2S w‖` is bounded for `Im w ≥ 1`. -/
lemma exists_norm_E2S_le' : ∃ C : ℝ, 0 < C ∧ ∀ w : ℍ, 1 ≤ w.im → ‖E2S w‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := E2Fun_bound
  refine ⟨C + 6 / Real.pi + 1, by positivity, fun w hw => ?_⟩
  rw [TildeFacts.E2S_eq]
  have h1 := h w hw
  have hw1 : (1 : ℝ) ≤ ‖(w : ℂ)‖ := le_trans hw (im_le_coe_norm w)
  have h2 : ‖(6 : ℂ) * Complex.I / ((Real.pi : ℂ) * (w : ℂ))‖ ≤ 6 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_ofNat, norm_pi]
    rw [div_le_iff₀ (by positivity)]
    have h3 : (6 / Real.pi) * (Real.pi * ‖(w : ℂ)‖) = 6 * ‖(w : ℂ)‖ := by field_simp
    rw [h3]; linarith
  calc ‖E2Fun w - 6 * Complex.I / ((Real.pi : ℂ) * (w : ℂ))‖
      ≤ ‖E2Fun w‖ + ‖6 * Complex.I / ((Real.pi : ℂ) * (w : ℂ))‖ := norm_sub_le _ _
    _ ≤ C + 6 / Real.pi := add_le_add h1 h2
    _ ≤ C + 6 / Real.pi + 1 := by linarith

/-- `‖φ₂(τ)‖ ≤ C S τ` on the funnel. -/
lemma phi2t_bound : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ →
    ‖Compact.phi2t τ‖ ≤ C * scale τ := by
  obtain ⟨C, hC, h⟩ := exists_E2_Funnel_bound
  refine ⟨C ^ 2 + (6 / Real.pi) * C + 1, by positivity, fun τ hτ => ?_⟩
  have h2 := h τ hτ
  have h3 : ‖(τ : ℂ)‖ ≤ scale τ := coe_norm_le_scale τ
  have h4 : (1 : ℝ) ≤ scale τ := one_le_scale τ
  have h5 : Compact.phi2t τ
      = (τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ := rfl
  rw [h5]
  have h6 : ‖(τ : ℂ) * E2Fun τ ^ 2‖ ≤ scale τ * C ^ 2 := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul h3 (pow_le_pow_left₀ (norm_nonneg _) h2 2) (by positivity)
      (le_trans (norm_nonneg _) h3)
  have h7 : ‖(6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ‖ ≤ (6 / Real.pi) * C := by
    rw [norm_mul, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, norm_pi]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have h8 : ‖(τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ‖
      ≤ scale τ * C ^ 2 + (6 / Real.pi) * C := le_trans (norm_sub_le _ _) (add_le_add h6 h7)
  calc ‖(τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ‖
      ≤ scale τ * C ^ 2 + (6 / Real.pi) * C := h8
    _ ≤ (C ^ 2 + (6 / Real.pi) * C + 1) * scale τ := by
        have h12 : (6 / Real.pi) * C ≤ (6 / Real.pi) * C * scale τ := by
          have := mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ (6 / Real.pi) * C)
          simpa using this
        calc scale τ * C ^ 2 + (6 / Real.pi) * C
            ≤ scale τ * C ^ 2 + (6 / Real.pi) * C * scale τ := by linarith
          _ = (C ^ 2 + (6 / Real.pi) * C) * scale τ := by ring
          _ ≤ (C ^ 2 + (6 / Real.pi) * C + 1) * scale τ := by
              have h13 : (0 : ℝ) ≤ scale τ := le_trans (norm_nonneg _) h3
              nlinarith [h13]



lemma SBz_E4 : SB (fun _ ζ => E4Fun ζ) := by
  obtain ⟨C, hC, h⟩ := E4Fun_bound
  exact SB.mono hC (le_refl 0) (fun τ ζ hτ hζ hH => by
    rw [Real.rpow_zero, mul_one]; exact h ζ (one_le_zeta_im hζ hH))

lemma SBz_E6 : SB (fun _ ζ => E6Fun ζ) := by
  obtain ⟨C, hC, h⟩ := E6Fun_bound
  exact SB.mono hC (le_refl 0) (fun τ ζ hτ hζ hH => by
    rw [Real.rpow_zero, mul_one]; exact h ζ (one_le_zeta_im hζ hH))

lemma SBz_E2 : SB (fun _ ζ => E2Fun ζ) := by
  obtain ⟨C, hC, h⟩ := E2Fun_bound
  exact SB.mono hC (le_refl 0) (fun τ ζ hτ hζ hH => by
    rw [Real.rpow_zero, mul_one]; exact h ζ (one_le_zeta_im hζ hH))

lemma SBz_E8 : SB (fun _ ζ => E8Fun ζ) := by
  obtain ⟨C, hC, h⟩ := E4Fun_bound
  refine SB.mono (C := C ^ 2 + 1) (N := 0) (by positivity) (le_refl 0) (fun τ ζ hτ hζ hH => ?_)
  rw [Real.rpow_zero, mul_one]
  have h1 : E8Fun ζ = E4Fun ζ ^ 2 := rfl
  rw [h1, norm_pow]
  have h2 := h ζ (one_le_zeta_im hζ hH)
  have h3 : ‖E4Fun ζ‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  linarith

lemma SBz_E10 : SB (fun _ ζ => E10Fun ζ) := by
  obtain ⟨C4, hC4, h4⟩ := E4Fun_bound
  obtain ⟨C6, hC6, h6⟩ := E6Fun_bound
  refine SB.mono (C := C4 * C6 + 1) (N := 0) (by positivity) (le_refl 0) (fun τ ζ hτ hζ hH => ?_)
  rw [Real.rpow_zero, mul_one]
  have h1 : E10Fun ζ = E4Fun ζ * E6Fun ζ := rfl
  rw [h1, norm_mul]
  exact le_trans (mul_le_mul (h4 ζ (one_le_zeta_im hζ hH)) (h6 ζ (one_le_zeta_im hζ hH))
    (norm_nonneg _) hC4.le) (by linarith)

lemma SBz_E14 : SB (fun _ ζ => E14Fun ζ) := by
  obtain ⟨C4, hC4, h4⟩ := E4Fun_bound
  obtain ⟨C6, hC6, h6⟩ := E6Fun_bound
  refine SB.mono (C := C4 ^ 2 * C6 + 1) (N := 0) (by positivity) (le_refl 0) (fun τ ζ hτ hζ hH => ?_)
  rw [Real.rpow_zero, mul_one]
  have h1 : E14Fun ζ = E4Fun ζ ^ 2 * E6Fun ζ := rfl
  rw [h1, norm_mul, norm_pow]
  have h2 := h4 ζ (one_le_zeta_im hζ hH)
  have h3 := h6 ζ (one_le_zeta_im hζ hH)
  have h5 : ‖E4Fun ζ‖ ^ 2 ≤ C4 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  exact le_trans (mul_le_mul h5 h3 (norm_nonneg _) (by positivity)) (by nlinarith [hC4, hC6])

lemma SBz_E2S : SB (fun _ ζ => E2S ζ) := by
  obtain ⟨C, hC, h⟩ := exists_norm_E2S_le'
  exact SB.mono hC (le_refl 0) (fun τ ζ hτ hζ hH => by
    rw [Real.rpow_zero, mul_one]; exact h ζ (one_le_zeta_im hζ hH))

lemma SBz_U : SB (fun _ ζ => UFun ζ) := by
  obtain ⟨C, hC, h⟩ := Work.Residues.UFun_decay
  refine SB.mono (C := C + 1) (N := 0) (by positivity) (le_refl 0) (fun τ ζ hτ hζ hH => ?_)
  rw [Real.rpow_zero, mul_one]
  have h1 := h ζ (one_le_zeta_im hζ hH)
  have h2 : Real.exp (-(Real.pi * ζ.im)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, ζ.im_pos])
  have h3 : ‖UFun ζ‖ ≤ ‖UFun ζ - 1‖ + 1 := by
    have h4 := norm_add_le (UFun ζ - 1) 1
    rw [sub_add_cancel, norm_one] at h4; exact h4
  nlinarith [h1, h2, hC.le]

lemma SBz_W : SB (fun _ ζ => WFun ζ) := by
  obtain ⟨C, hC, h⟩ := Work.Residues.WFun_decay
  refine SB.mono (C := C + 1) (N := 0) (by positivity) (le_refl 0) (fun τ ζ hτ hζ hH => ?_)
  rw [Real.rpow_zero, mul_one]
  have h1 := h ζ (one_le_zeta_im hζ hH)
  have h2 : Real.exp (-(Real.pi * ζ.im)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, ζ.im_pos])
  have h3 : ‖WFun ζ‖ ≤ ‖WFun ζ - 1‖ + 1 := by
    have h4 := norm_add_le (WFun ζ - 1) 1
    rw [sub_add_cancel, norm_one] at h4; exact h4
  nlinarith [h1, h2, hC.le]

lemma SBz_V : SB (fun _ ζ => VFun ζ) := by
  obtain ⟨C, hC, h⟩ := Work.Residues.VFun_decay
  refine SB.mono (C := C + 1) (N := 0) (by positivity) (le_refl 0) (fun τ ζ hτ hζ hH => ?_)
  rw [Real.rpow_zero, mul_one]
  have h1 := h ζ (one_le_zeta_im hζ hH)
  have h2 : Real.exp (-(Real.pi * ζ.im)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, ζ.im_pos])
  nlinarith [h1, h2, hC.le]

end Work.Asymptotics.SpikeCircle
