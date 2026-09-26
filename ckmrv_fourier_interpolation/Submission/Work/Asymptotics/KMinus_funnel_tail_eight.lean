/-
# Funnel tail expansion of `K₋^{(8)}`

The kernel `K₋^{(8)}` of CKMRV §4.5, restricted to the contour `z = i t` with `τ` in the
funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}` and `t ≥ Im τ + 1`, differs from the cusp model
`Work.Asymptotics.Compact.Gminus 8` by `O((scale τ)^N (1+t)^M exp (-π (t - Im τ)))`.

The proof goes through the identity `Work.Asymptotics.Compact.tail_identity`

  `3456π (K₋ - 𝒢₋) = -(Sh)⁻¹ (br + Sh · br0)`,

with `Sh τ z = E₄(z)³ - Δ(z)j(τ)`, `br` the bracket of `KMinus8_eq` and `br0 = 3456π·𝒢₋`.
Writing `br + br0 = A`, the two remainders are `(Sh)⁻¹·A` and `(1 - (Sh)⁻¹)·br0`; `A` is a sum
of three terms of size `O((1+t)‖E(z)‖)`, `O(‖Lamb τ‖‖E(z)‖)` and `O(‖ψ₄ τ‖‖E(z)‖)` with
`E(z) = e^{πiz}`, and `Sh - 1` is `O(‖q(z)‖ + ‖Δ(z)j(τ)‖)`.  The uniform lower bound
`‖Sh‖ ≥ 1/16` and the bound `‖Δ(z)j(τ)‖ ≤ (27/4)e^{-2π(t-Im τ)}` come from the sharp cusp
bounds on `E₄` and `Δ` (`E4_funnel_upper`, `E4_imagAxis_lower`, `DeltaFun_funnel_lower_sharp`,
`DeltaFun_imagAxis_upper_sharp`), and the cancellation of the `E(z)`-order terms of the
`ψ₂`- and `ψ₄`-parts is the identity `ψ₂E₁₄/Δ - j(τ)ψ₄ = -Lamb`, bounded by
`Lamb_funnel_bound`.
-/
import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.funnelTailQuant
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.cusp_L_second
import Submission.Work.Asymptotics.cusp_W_second
import Submission.Work.Asymptotics.cusp_D_second
import Submission.Work.Asymptotics.cusp_U_second
import Submission.Work.Asymptotics.cusp_invDelta
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.jInvariantFun_imagAxis_atTop
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atTop
import Submission.Work.Asymptotics.psi_InP
import Submission.Work.Residues.ThetaExpansion
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.FunnelNumerics.E4_funnel_bounds
import Submission.Work.FunnelNumerics.Delta_funnel_bounds
import Submission.Work.FunnelNumerics.Lamb_funnel_bound

set_option maxHeartbeats 1000000

namespace Work.Asymptotics

open UpperHalfPlane

noncomputable section

/-! ## Interface lemmas proved in sibling modules -/

/-- On the funnel, `‖E₄‖ ≤ 3/2`. -/
private theorem E4_funnel_upper (τ : ℍ) (hτ : Funnel τ) :
    ‖Work.Kernels.E4Fun τ‖ ≤ 3 / 2 :=
  (Work.FunnelNumerics.E4_funnel_bounds).1 τ hτ

/-- For `Im z ≥ 3`, `‖E₄ z‖ ≥ 1/2`. -/
private theorem E4_imagAxis_lower (z : ℍ) (hz : 3 ≤ z.im) :
    (1 / 2 : ℝ) ≤ ‖Work.Kernels.E4Fun z‖ :=
  (Work.FunnelNumerics.E4_funnel_bounds).2 z hz

/-- Sharp lower bound for `Δ` on the funnel: `‖Δ(τ)‖ ≥ (1/2)‖q(τ)‖` for `Im τ ≥ 2`. -/
private theorem ft_Delta_lower (τ : ℍ) (hτ : 2 ≤ τ.im) :
    (1 / 2 : ℝ) * ‖Work.Kernels.qParamFun τ‖ ≤ ‖Work.Kernels.DeltaFun τ‖ := by
  exact (Work.FunnelNumerics.Delta_funnel_bounds).1 τ hτ

/-- Sharp upper bound for `Δ` on the imaginary axis: `‖Δ(it)‖ ≤ e^{-2πt}` for `t ≥ 1`. -/
private theorem ft_Delta_imUpper (t : ℝ) (ht : 0 < t) (ht1 : 1 ≤ t) :
    ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ≤
      Real.exp (-(2 * Real.pi * t)) :=
  (Work.FunnelNumerics.Delta_funnel_bounds).2 t ht ht1

/-- `Δ(τ)Λ(τ) = O((scale τ)^N q_τ)` on the funnel. -/
private theorem ft_Lamb_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ‖ ≤
        C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ :=
  Work.FunnelNumerics.Lamb_funnel_bound ℓ

/-! ## Elementary facts on the contour `z = i t` -/

private lemma ft_im_of_coe {z : ℍ} {t : ℝ} (hz : (z : ℂ) = (t : ℂ) * Complex.I) :
    z.im = t := by
  have h := congrArg Complex.im hz
  simp [UpperHalfPlane.coe_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im] at h
  linarith [h]

private lemma ft_norm_Ept {z : ℍ} {t : ℝ} (hz : z.im = t) :
    ‖Work.Residues.Ept z‖ = Real.exp (-(Real.pi * t)) := by
  rw [Work.Residues.norm_Ept, hz]

private lemma ft_norm_qParam {z : ℍ} {t : ℝ} (hz : z.im = t) :
    ‖Work.Kernels.qParamFun z‖ = Real.exp (-(2 * Real.pi * t)) := by
  rw [norm_qParamFun, hz]

private lemma ft_Ept_le_one {z : ℍ} (hz : 1 ≤ z.im) : ‖Work.Residues.Ept z‖ ≤ 1 := by
  rw [Work.Residues.norm_Ept]
  exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hz])

private lemma ft_q_eq_Ept_sq (z : ℍ) :
    Work.Kernels.qParamFun z = (Work.Residues.Ept z) ^ 2 := by
  rw [Work.Residues.Ept, Work.Kernels.qParamFun, sq, ← Complex.exp_add]
  ring_nf

private lemma ft_norm_Xc (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) :
    ‖Compact.Xc ℓ z‖ ≤ (Real.pi + ‖Compact.cuspC ℓ‖) * (1 + ‖(z : ℂ)‖) := by
  have hX : ‖Compact.Xc ℓ z‖ ≤ Real.pi * ‖(z : ℂ)‖ + ‖Compact.cuspC ℓ‖ := by
    rw [Compact.Xc]
    calc ‖(Real.pi : ℂ) * Complex.I * (z : ℂ) + Compact.cuspC ℓ‖
        ≤ ‖(Real.pi : ℂ) * Complex.I * (z : ℂ)‖ + ‖Compact.cuspC ℓ‖ := norm_add_le _ _
      _ = Real.pi * ‖(z : ℂ)‖ + ‖Compact.cuspC ℓ‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
  nlinarith [hX, Real.pi_pos, norm_nonneg (Compact.cuspC ℓ), norm_nonneg (z : ℂ)]

/-- `exp (2π) ≥ 108`. -/
private lemma ft_exp_two_pi_ge : (108 : ℝ) ≤ Real.exp (2 * Real.pi) := by
  have h6 : (6 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h1 : (2.7 : ℝ) ≤ Real.exp 1 := le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)
  have h2 : (2.7 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 := pow_le_pow_left₀ (by norm_num) h1 6
  have h3 : Real.exp 6 = (Real.exp 1) ^ 6 := by
    rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
  have h4 : (108 : ℝ) ≤ Real.exp 6 := by
    rw [h3]; linarith [h2]
  exact le_trans h4 (Real.exp_le_exp.mpr h6)

private lemma ft_scale_rpow_nonneg (τ : ℍ) (N : ℝ) :
    (0:ℝ) ≤ Work.Kernels.scale τ ^ N :=
  Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N

/-! ## `O`-bounds of the shape `(1+‖z‖)^m ‖Ept z‖^n` -/

/-- `IsBigOe f m n`: `‖f z‖ ≤ C (1+‖z‖)^m ‖Ept z‖^n` for `z.im ≥ 1`. -/
private def IsBigOe (f : ℍ → ℂ) (m n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖f z‖ ≤ C * (1 + ‖(z : ℂ)‖) ^ m * ‖Work.Residues.Ept z‖ ^ n

private lemma IsBigOe.mono {f : ℍ → ℂ} {m n m' n' : ℕ} (h : IsBigOe f m n)
    (hm : m ≤ m') (hn : n' ≤ n) : IsBigOe f m' n' := by
  obtain ⟨C, hC, hf⟩ := h
  refine ⟨C, hC, fun z hz => ?_⟩
  have h1 : (1 : ℝ) ≤ 1 + ‖(z : ℂ)‖ := by linarith [norm_nonneg (z : ℂ)]
  have h3 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
  have h4 : ‖Work.Residues.Ept z‖ ≤ 1 := ft_Ept_le_one hz
  have hp1 : (1 + ‖(z : ℂ)‖) ^ m ≤ (1 + ‖(z : ℂ)‖) ^ m' := pow_le_pow_right₀ h1 hm
  have hp2 : ‖Work.Residues.Ept z‖ ^ n ≤ ‖Work.Residues.Ept z‖ ^ n' :=
    pow_le_pow_of_le_one h3 h4 hn
  calc ‖f z‖ ≤ C * (1 + ‖(z : ℂ)‖) ^ m * ‖Work.Residues.Ept z‖ ^ n := hf z hz
    _ ≤ C * (1 + ‖(z : ℂ)‖) ^ m' * ‖Work.Residues.Ept z‖ ^ n' :=
        mul_le_mul (mul_le_mul_of_nonneg_left hp1 hC.le) hp2 (by positivity) (by positivity)

private lemma IsBigOe.mul {f g : ℍ → ℂ} {m₁ n₁ m₂ n₂ : ℕ}
    (hf : IsBigOe f m₁ n₁) (hg : IsBigOe g m₂ n₂) :
    IsBigOe (fun z => f z * g z) (m₁ + m₂) (n₁ + n₂) := by
  obtain ⟨C1, hC1, hf⟩ := hf
  obtain ⟨C2, hC2, hg⟩ := hg
  refine ⟨C1 * C2, by positivity, fun z hz => ?_⟩
  have h1 := hf z hz
  have h2 := hg z hz
  rw [norm_mul, pow_add, pow_add]
  calc ‖f z‖ * ‖g z‖
      ≤ (C1 * (1 + ‖(z : ℂ)‖) ^ m₁ * ‖Work.Residues.Ept z‖ ^ n₁)
        * (C2 * (1 + ‖(z : ℂ)‖) ^ m₂ * ‖Work.Residues.Ept z‖ ^ n₂) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = C1 * C2 * ((1 + ‖(z : ℂ)‖) ^ m₁ * (1 + ‖(z : ℂ)‖) ^ m₂)
          * (‖Work.Residues.Ept z‖ ^ n₁ * ‖Work.Residues.Ept z‖ ^ n₂) := by ring

private lemma IsBigOe.neg {f : ℍ → ℂ} {m n : ℕ} (hf : IsBigOe f m n) :
    IsBigOe (fun z => -f z) m n := by
  obtain ⟨C, hC, hf⟩ := hf
  refine ⟨C, hC, fun z hz => ?_⟩
  have h1 := hf z hz
  rw [norm_neg]
  exact h1

private lemma IsBigOe.add {f g : ℍ → ℂ} {m₁ n₁ m₂ n₂ : ℕ}
    (hf : IsBigOe f m₁ n₁) (hg : IsBigOe g m₂ n₂) :
    IsBigOe (fun z => f z + g z) (m₁ + m₂) (min n₁ n₂) := by
  have hf' : IsBigOe f (m₁ + m₂) (min n₁ n₂) :=
    IsBigOe.mono hf (Nat.le_add_right m₁ m₂) (min_le_left n₁ n₂)
  have hg' : IsBigOe g (m₁ + m₂) (min n₁ n₂) :=
    IsBigOe.mono hg (Nat.le_add_left m₂ m₁) (min_le_right n₁ n₂)
  obtain ⟨C1, hC1, hf'⟩ := hf'
  obtain ⟨C2, hC2, hg'⟩ := hg'
  refine ⟨C1 + C2, by positivity, fun z hz => ?_⟩
  have h1 := hf' z hz
  have h2 := hg' z hz
  have h3 : ‖f z + g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
  have h4 : ‖f z‖ + ‖g z‖
      ≤ (C1 + C2) * (1 + ‖(z : ℂ)‖) ^ (m₁ + m₂) * ‖Work.Residues.Ept z‖ ^ (min n₁ n₂) := by
    linarith [h1, h2]
  linarith [h3, h4]

private lemma IsBigOe.sub {f g : ℍ → ℂ} {m₁ n₁ m₂ n₂ : ℕ}
    (hf : IsBigOe f m₁ n₁) (hg : IsBigOe g m₂ n₂) :
    IsBigOe (fun z => f z - g z) (m₁ + m₂) (min n₁ n₂) := by
  obtain ⟨C, hC, h⟩ := IsBigOe.add hf (IsBigOe.neg hg)
  refine ⟨C, hC, fun z hz => ?_⟩
  have h1 : ‖f z - g z‖ ≤ C * (1 + ‖(z : ℂ)‖) ^ (m₁ + m₂)
      * ‖Work.Residues.Ept z‖ ^ (min n₁ n₂) := by
    simpa [sub_eq_add_neg] using h z hz
  simpa using h1

private lemma IsBigOe.congr {f g : ℍ → ℂ} {m n : ℕ} (h : IsBigOe f m n)
    (hfg : ∀ z, f z = g z) : IsBigOe g m n := by
  obtain ⟨C, hC, hf⟩ := h
  exact ⟨C, hC, fun z hz => by rw [← hfg z]; exact hf z hz⟩

private lemma IsBigOe.of_isBigOq {f : ℍ → ℂ} {n : ℕ} (h : IsBigOq f n) :
    IsBigOe f 0 (2 * n) := by
  obtain ⟨C, hC, hf⟩ := h
  refine ⟨C, hC, fun z hz => ?_⟩
  have h1 := hf z hz
  have h2 : ‖Work.Kernels.qParamFun z‖ ^ n = ‖Work.Residues.Ept z‖ ^ (2 * n) := by
    rw [ft_q_eq_Ept_sq z, norm_pow, ← pow_mul]
  rw [h2] at h1
  simpa using h1

/-- `E₈ - 1 = O(q)`. -/
private lemma E8_sub_one_isBigOq : IsBigOq (fun z : ℍ => Work.Kernels.E8Fun z - 1) 1 := by
  have h1 : IsBigOq (fun z : ℍ => Work.Kernels.E4Fun z - 1) 1 := E4_minus_one
  have h2 : IsBigOq (fun z : ℍ => Work.Kernels.E4Fun z + 1) 0 :=
    E4Fun_bdd.add (IsBigOq.bounded (f := fun _ : ℍ => (1 : ℂ)) 1 one_pos (fun _ _ => by simp))
  refine (h1.mul h2).congr (fun z => ?_)
  simp only [Work.Kernels.E8Fun]
  ring

/-- `E₁₀ - 1 = O(q)`. -/
private lemma E10_sub_one_isBigOq : IsBigOq (fun z : ℍ => Work.Kernels.E10Fun z - 1) 1 := by
  have h1 : IsBigOq (fun z : ℍ => Work.Kernels.E4Fun z - 1) 1 := E4_minus_one
  have h2 : IsBigOq (fun z : ℍ => Work.Kernels.E6Fun z) 0 := E6Fun_bdd
  have h3 : IsBigOq (fun z : ℍ => Work.Kernels.E6Fun z - 1) 1 := E6_minus_one
  refine ((h1.mul h2).add h3).congr (fun z => ?_)
  simp only [Work.Kernels.E10Fun]
  ring

/-- `E₄³ - 1 = O(q)`. -/
private lemma E4cube_sub_one_isBigOq : IsBigOq (fun z : ℍ => Work.Kernels.E4Fun z ^ 3 - 1) 1 := by
  have h1 : IsBigOq (fun z : ℍ => Work.Kernels.E4Fun z - 1) 1 := E4_minus_one
  have h2 : IsBigOq (fun z : ℍ => Work.Kernels.E4Fun z ^ 2 + Work.Kernels.E4Fun z + 1) 0 :=
    (E4sq_bdd.add E4Fun_bdd).add
      (IsBigOq.bounded (f := fun _ : ℍ => (1 : ℂ)) 1 one_pos (fun _ _ => by simp))
  refine (h1.mul h2).congr (fun z => ?_)
  ring

/-- If `f - 1` is small then `f` is `O(1)`. -/
private lemma IsBigOe.bdd_of_sub_one {f : ℍ → ℂ} {n : ℕ}
    (h : IsBigOe (fun z => f z - 1) 0 n) : IsBigOe f 0 0 := by
  obtain ⟨C, hC, hf⟩ := h
  refine ⟨C + 1, by positivity, fun z hz => ?_⟩
  have h1 := hf z hz
  have h0 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
  have hE1 : ‖Work.Residues.Ept z‖ ≤ 1 := ft_Ept_le_one hz
  have h2 : ‖Work.Residues.Ept z‖ ^ n ≤ 1 := pow_le_one₀ h0 hE1
  have h3 : ‖f z‖ ≤ ‖f z - 1‖ + 1 := by
    have := norm_add_le (f z - 1) (1 : ℂ)
    simpa using this
  simp only [pow_zero, mul_one] at h1
  simp only [pow_zero, mul_one]
  nlinarith [h1, h2, h3, hC.le]

/-- `W - 1 = O(‖E‖)`. -/
private lemma W_sub_one_isBigOe :
    IsBigOe (fun z : ℍ => Work.Kernels.WFun z - 1) 0 1 := by
  obtain ⟨C, hC, h⟩ := cusp_W_second
  refine ⟨C + 32, by positivity, fun z hz => ?_⟩
  change ‖Work.Kernels.WFun z - 1‖
    ≤ (C + 32) * (1 + ‖(z : ℂ)‖) ^ 0 * ‖Work.Residues.Ept z‖ ^ 1
  have h0 : (0:ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
  have h1 : ‖Work.Residues.Ept z‖ ≤ 1 := ft_Ept_le_one hz
  have h3 : ‖Work.Residues.Ept z‖ ^ 3 ≤ ‖Work.Residues.Ept z‖ :=
    pow_le_of_le_one h0 h1 (by norm_num)
  have hW := h z hz
  have hdec : Work.Kernels.WFun z - 1
      = (Work.Kernels.WFun z - (1 - 8 * Work.Residues.Ept z + 24 * Work.Residues.Ept z ^ 2))
        - (8 * Work.Residues.Ept z - 24 * Work.Residues.Ept z ^ 2) := by ring
  have hb : ‖8 * Work.Residues.Ept z - 24 * Work.Residues.Ept z ^ 2‖
      ≤ 32 * ‖Work.Residues.Ept z‖ := by
    have hs := norm_sub_le ((8 : ℂ) * Work.Residues.Ept z)
      ((24 : ℂ) * Work.Residues.Ept z ^ 2)
    have h8 : ‖(8 : ℂ) * Work.Residues.Ept z‖ = 8 * ‖Work.Residues.Ept z‖ := by
      rw [norm_mul]; norm_num
    have h24 : ‖(24 : ℂ) * Work.Residues.Ept z ^ 2‖ = 24 * ‖Work.Residues.Ept z‖ ^ 2 := by
      rw [norm_mul, norm_pow]; norm_num
    rw [h8, h24] at hs
    have h2 : ‖Work.Residues.Ept z‖ ^ 2 ≤ ‖Work.Residues.Ept z‖ :=
      pow_le_of_le_one h0 h1 (by norm_num)
    linarith
  rw [hdec]
  have hA : ‖Work.Kernels.WFun z - (1 - 8 * Work.Residues.Ept z + 24 * Work.Residues.Ept z ^ 2)‖
      ≤ C * ‖Work.Residues.Ept z‖ := by nlinarith [hW, h3, hC.le]
  simp only [pow_zero, pow_one, mul_one]
  linarith [le_trans (norm_sub_le _ _) (add_le_add hA hb)]

/-- `U² - V² - 1 = O(‖E‖)`. -/
private lemma D2_sub_one_isBigOe :
    IsBigOe (fun z : ℍ => Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2 - 1) 0 1 := by
  obtain ⟨C, hC, h⟩ := cusp_D_second
  refine ⟨C + 160, by positivity, fun z hz => ?_⟩
  change ‖Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2 - 1‖
    ≤ (C + 160) * (1 + ‖(z : ℂ)‖) ^ 0 * ‖Work.Residues.Ept z‖ ^ 1
  have h0 : (0:ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
  have h1 : ‖Work.Residues.Ept z‖ ≤ 1 := ft_Ept_le_one hz
  have h3 : ‖Work.Residues.Ept z‖ ^ 3 ≤ ‖Work.Residues.Ept z‖ :=
    pow_le_of_le_one h0 h1 (by norm_num)
  have hD := h z hz
  have hdec : Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2 - 1
      = (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2
          - (1 + 16 * Work.Residues.Ept z - 144 * Work.Residues.Ept z ^ 2))
        + (16 * Work.Residues.Ept z - 144 * Work.Residues.Ept z ^ 2) := by ring
  have hb : ‖16 * Work.Residues.Ept z - 144 * Work.Residues.Ept z ^ 2‖
      ≤ 160 * ‖Work.Residues.Ept z‖ := by
    have hs := norm_sub_le ((16 : ℂ) * Work.Residues.Ept z)
      ((144 : ℂ) * Work.Residues.Ept z ^ 2)
    have h16 : ‖(16 : ℂ) * Work.Residues.Ept z‖ = 16 * ‖Work.Residues.Ept z‖ := by
      rw [norm_mul]; norm_num
    have h144 : ‖(144 : ℂ) * Work.Residues.Ept z ^ 2‖ = 144 * ‖Work.Residues.Ept z‖ ^ 2 := by
      rw [norm_mul, norm_pow]; norm_num
    rw [h16, h144] at hs
    have h2 : ‖Work.Residues.Ept z‖ ^ 2 ≤ ‖Work.Residues.Ept z‖ :=
      pow_le_of_le_one h0 h1 (by norm_num)
    linarith
  rw [hdec]
  have hA : ‖Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2
      - (1 + 16 * Work.Residues.Ept z - 144 * Work.Residues.Ept z ^ 2)‖
      ≤ C * ‖Work.Residues.Ept z‖ := by nlinarith [hD, h3, hC.le]
  simp only [pow_zero, pow_one, mul_one]
  linarith [le_trans (norm_add_le _ _) (add_le_add hA hb)]

private lemma W_bdd_isBigOe : IsBigOe (fun z : ℍ => Work.Kernels.WFun z) 0 0 :=
  IsBigOe.bdd_of_sub_one W_sub_one_isBigOe

private lemma D2_bdd_isBigOe :
    IsBigOe (fun z : ℍ => Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2) 0 0 :=
  IsBigOe.bdd_of_sub_one D2_sub_one_isBigOe

private lemma E10_bdd_isBigOe : IsBigOe (fun z : ℍ => Work.Kernels.E10Fun z) 0 0 :=
  IsBigOe.bdd_of_sub_one (IsBigOe.of_isBigOq E10_sub_one_isBigOq)

private lemma E8_sub_one_isBigOe :
    IsBigOe (fun z : ℍ => Work.Kernels.E8Fun z - 1) 0 2 :=
  IsBigOe.of_isBigOq E8_sub_one_isBigOq

private lemma E6_sub_one_isBigOe :
    IsBigOe (fun z : ℍ => Work.Kernels.E6Fun z - 1) 0 2 :=
  IsBigOe.of_isBigOq E6_minus_one

private lemma E4cube_sub_one_isBigOe :
    IsBigOe (fun z : ℍ => Work.Kernels.E4Fun z ^ 3 - 1) 0 2 :=
  IsBigOe.of_isBigOq E4cube_sub_one_isBigOq

/-! ## The `z`-atom bounds used in the main estimate -/

/-- `E₁₀(z)𝓛(z) - (πiz + c_L) = O((1+‖z‖)‖E(z)‖)`. -/
private lemma E10L_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
      ‖Work.Kernels.E10Fun z * ℓ.L z - Compact.Xc ℓ z‖
        ≤ C * (1 + ‖(z : ℂ)‖) * ‖Work.Residues.Ept z‖ := by
  obtain ⟨C1, hC1, h1⟩ := Compact.cuspC_spec ℓ
  have h1X : ∀ z : ℍ, 1 ≤ z.im →
      ‖ℓ.L z - (Compact.Xc ℓ z - 8 * Work.Residues.Ept z + 12 * Work.Residues.Ept z ^ 2)‖
        ≤ C1 * ‖Work.Residues.Ept z‖ ^ 3 := by
    intro z hz
    simpa only [Compact.Xc] using h1 z hz
  have hLsub : ∀ z : ℍ, 1 ≤ z.im →
      ‖ℓ.L z - Compact.Xc ℓ z‖ ≤ (20 + C1) * ‖Work.Residues.Ept z‖ := by
    intro z hz
    have hE0 : (0:ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
    have hE1 : ‖Work.Residues.Ept z‖ ≤ 1 := ft_Ept_le_one hz
    have h3 : ‖Work.Residues.Ept z‖ ^ 3 ≤ ‖Work.Residues.Ept z‖ :=
      pow_le_of_le_one hE0 hE1 (by norm_num)
    have hLz := h1X z hz
    have hdec : ℓ.L z - Compact.Xc ℓ z
        = (ℓ.L z - (Compact.Xc ℓ z - 8 * Work.Residues.Ept z
            + 12 * Work.Residues.Ept z ^ 2))
          - (8 * Work.Residues.Ept z - 12 * Work.Residues.Ept z ^ 2) := by ring
    have hb : ‖8 * Work.Residues.Ept z - 12 * Work.Residues.Ept z ^ 2‖
        ≤ 20 * ‖Work.Residues.Ept z‖ := by
      have hs := norm_sub_le ((8 : ℂ) * Work.Residues.Ept z)
        ((12 : ℂ) * Work.Residues.Ept z ^ 2)
      have h8 : ‖(8 : ℂ) * Work.Residues.Ept z‖ = 8 * ‖Work.Residues.Ept z‖ := by
        rw [norm_mul]; norm_num
      have h12 : ‖(12 : ℂ) * Work.Residues.Ept z ^ 2‖ = 12 * ‖Work.Residues.Ept z‖ ^ 2 := by
        rw [norm_mul, norm_pow]; norm_num
      rw [h8, h12] at hs
      have h2 : ‖Work.Residues.Ept z‖ ^ 2 ≤ ‖Work.Residues.Ept z‖ :=
        pow_le_of_le_one hE0 hE1 (by norm_num)
      linarith
    have hA : ‖ℓ.L z - (Compact.Xc ℓ z - 8 * Work.Residues.Ept z
        + 12 * Work.Residues.Ept z ^ 2)‖ ≤ C1 * ‖Work.Residues.Ept z‖ := by
      nlinarith [hLz, h3, hC1.le]
    rw [hdec]
    linarith [le_trans (norm_sub_le _ _) (add_le_add hA hb)]
  have hLsubE : IsBigOe (fun z : ℍ => ℓ.L z - Compact.Xc ℓ z) 0 1 := by
    refine ⟨20 + C1, by positivity, fun z hz => ?_⟩
    change ‖ℓ.L z - Compact.Xc ℓ z‖
      ≤ (20 + C1) * (1 + ‖(z : ℂ)‖) ^ 0 * ‖Work.Residues.Ept z‖ ^ 1
    have h := hLsub z hz
    simpa using h
  have hL : IsBigOe (fun z : ℍ => ℓ.L z) 1 0 := by
    refine ⟨20 + C1 + (Real.pi + ‖Compact.cuspC ℓ‖), by positivity, fun z hz => ?_⟩
    change ‖ℓ.L z‖ ≤ (20 + C1 + (Real.pi + ‖Compact.cuspC ℓ‖)) * (1 + ‖(z : ℂ)‖) ^ 1
      * ‖Work.Residues.Ept z‖ ^ 0
    have hLz := hLsub z hz
    have hE1 : ‖Work.Residues.Ept z‖ ≤ 1 := ft_Ept_le_one hz
    have hX := ft_norm_Xc ℓ z
    have hsplit : ℓ.L z = Compact.Xc ℓ z + (ℓ.L z - Compact.Xc ℓ z) := by ring
    have h1z : (1:ℝ) ≤ 1 + ‖(z : ℂ)‖ := by linarith [norm_nonneg (z : ℂ)]
    simp only [pow_zero, pow_one, mul_one]
    rw [hsplit]
    have hna := norm_add_le (Compact.Xc ℓ z) (ℓ.L z - Compact.Xc ℓ z)
    have hπ : (0:ℝ) ≤ Real.pi + ‖Compact.cuspC ℓ‖ := by positivity
    have hC1r : (20 + C1) * ‖Work.Residues.Ept z‖ ≤ (20 + C1) * 1 :=
      mul_le_mul_of_nonneg_left hE1 (by linarith)
    nlinarith [hna, hX, hLz, hC1r, h1z, hπ, hC1.le]
  have hE10m1 : IsBigOe (fun z : ℍ => Work.Kernels.E10Fun z - 1) 0 2 :=
    IsBigOe.of_isBigOq E10_sub_one_isBigOq
  have hmain : IsBigOe (fun z : ℍ => Work.Kernels.E10Fun z * ℓ.L z - Compact.Xc ℓ z) 1 1 :=
    ((hE10m1.mul hL).add hLsubE).congr (fun z => by ring)
  obtain ⟨C, hC, hf⟩ := hmain
  refine ⟨C, hC, fun z hz => ?_⟩
  have := hf z hz
  simpa using this

/-- `E₈(z)W(z) - E₆(z)(U²-V²)(z) = O(‖E(z)‖)`. -/
private lemma Az_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
      ‖Work.Kernels.E8Fun z * Work.Kernels.WFun z
        - Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)‖
        ≤ C * ‖Work.Residues.Ept z‖ := by
  have hmain : IsBigOe (fun z : ℍ => Work.Kernels.E8Fun z * Work.Kernels.WFun z
      - Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)) 0 1 :=
    (((E8_sub_one_isBigOe.mul W_bdd_isBigOe).add W_sub_one_isBigOe).sub
      (E6_sub_one_isBigOe.mul D2_bdd_isBigOe)).sub D2_sub_one_isBigOe |>.mono
        (by norm_num) (by norm_num) |>.congr (fun z => by ring)
  obtain ⟨C, hC, hf⟩ := hmain
  refine ⟨C, hC, fun z hz => ?_⟩
  have := hf z hz
  simp only [pow_zero, pow_one, mul_one] at this
  exact this

/-- `E₈(z)W(z) - 1 = O(‖E(z)‖)`. -/
private lemma E8W1_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
      ‖Work.Kernels.E8Fun z * Work.Kernels.WFun z - 1‖ ≤ C * ‖Work.Residues.Ept z‖ := by
  have hmain : IsBigOe (fun z : ℍ => Work.Kernels.E8Fun z * Work.Kernels.WFun z - 1) 0 1 :=
    ((E8_sub_one_isBigOe.mul W_bdd_isBigOe).add W_sub_one_isBigOe).mono
      (by norm_num) (by norm_num) |>.congr (fun z => by ring)
  obtain ⟨C, hC, hf⟩ := hmain
  refine ⟨C, hC, fun z hz => ?_⟩
  have := hf z hz
  simp only [pow_zero, pow_one, mul_one] at this
  exact this

/-- `E₄(z)³ - 1 = O(q(z))`. -/
private lemma E4c1_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
      ‖Work.Kernels.E4Fun z ^ 3 - 1‖ ≤ C * ‖Work.Kernels.qParamFun z‖ := by
  obtain ⟨C, hC, h⟩ := E4cube_sub_one_isBigOq
  exact ⟨C, hC, fun z hz => by simpa using h z hz⟩

/-! ## Growth of `ψ₄` on the funnel -/

private lemma psi4_funnel_growth (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖Work.Kernels.psi4 ℓ τ‖ ≤ C * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨_, hmg⟩ := (psi_InP ℓ).2
  obtain ⟨α, N, hα, hN, h⟩ := (Work.Kernels.moderateGrowthOn_iff_scale Set.univ
    (Work.Kernels.psi4 ℓ)).mp hmg
  refine ⟨α + 1, N, by positivity, hN, fun τ hτ => ?_⟩
  have h1 := h τ (Set.mem_univ τ)
  have h2 : (0:ℝ) ≤ Work.Kernels.scale τ ^ N :=
    Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N
  nlinarith [h1, h2, hα]

/-! ## The uniform divisor bound on the funnel -/

/-- `‖Δ(z) j(τ)‖ ≤ (27/4)e^{-2π(t - Im τ)}` for `τ` in the funnel and `z = it`. -/
private lemma funnel_rho_exp (τ z : ℍ) (t : ℝ) (hτ : Funnel τ) (ht : τ.im + 1 ≤ t)
    (hz : (z : ℂ) = (t : ℂ) * Complex.I) :
    ‖Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ‖
      ≤ (27 / 4) * Real.exp (-(Real.pi * (t - τ.im))) ^ 2 := by
  have hτ2 : 2 ≤ τ.im := hτ.2
  have ht0 : 0 < t := by linarith
  have hzim : z.im = t := ft_im_of_coe hz
  have hz3 : 3 ≤ z.im := by rw [hzim]; linarith
  -- `‖Δ(z)‖ ≤ e^{-2πt}`
  have hΔz : ‖Work.Kernels.DeltaFun z‖ ≤ Real.exp (-(2 * Real.pi * t)) := by
    have hzeq : z = Work.Kernels.imagAxis t ht0 :=
      UpperHalfPlane.coe_injective (show (z : ℂ) = ((Work.Kernels.imagAxis t ht0 : ℍ) : ℂ) from hz)
    rw [hzeq]
    exact ft_Delta_imUpper t ht0 (by linarith)
  -- `‖j τ‖ ≤ (27/4) e^{2π Im τ}`
  have hjτ : ‖Work.Kernels.jInvariantFun τ‖ ≤ (27 / 4) * Real.exp (2 * Real.pi * τ.im) := by
    have hDlow := ft_Delta_lower τ hτ2
    have hqpos : 0 < ‖Work.Kernels.qParamFun τ‖ := by rw [norm_qParamFun]; positivity
    have hqpos' : 0 < (1 / 2 : ℝ) * ‖Work.Kernels.qParamFun τ‖ := by linarith
    have hinv : (‖Work.Kernels.DeltaFun τ‖)⁻¹ ≤ 2 * Real.exp (2 * Real.pi * τ.im) := by
      have h2 := inv_anti₀ hqpos' hDlow
      have h3 : ((1 / 2 : ℝ) * ‖Work.Kernels.qParamFun τ‖)⁻¹
          = 2 * Real.exp (2 * Real.pi * τ.im) := by
        rw [norm_qParamFun, mul_inv, inv_div, Real.exp_neg, inv_inv]
        ring
      linarith [h2, h3.le]
    have hE4b : ‖Work.Kernels.E4Fun τ‖ ≤ 3 / 2 := E4_funnel_upper τ hτ
    have hnum : ‖Work.Kernels.E4Fun τ‖ ^ 3 ≤ (3 / 2) ^ 3 :=
      pow_le_pow_left₀ (norm_nonneg _) hE4b 3
    have hmain : ‖Work.Kernels.E4Fun τ ^ 3 / Work.Kernels.DeltaFun τ‖
        ≤ (27 / 4) * Real.exp (2 * Real.pi * τ.im) := by
      rw [norm_div, norm_pow, div_eq_mul_inv]
      calc ‖Work.Kernels.E4Fun τ‖ ^ 3 * (‖Work.Kernels.DeltaFun τ‖)⁻¹
          ≤ (3 / 2) ^ 3 * (2 * Real.exp (2 * Real.pi * τ.im)) :=
            mul_le_mul hnum hinv (by positivity) (by positivity)
        _ = (27 / 4) * Real.exp (2 * Real.pi * τ.im) := by norm_num; ring
    simpa [Work.Kernels.jInvariantFun] using hmain
  rw [norm_mul]
  have hcombi : Real.exp (-(2 * Real.pi * t)) * ((27 / 4) * Real.exp (2 * Real.pi * τ.im))
      = (27 / 4) * Real.exp (-(Real.pi * (t - τ.im))) ^ 2 := by
    rw [show Real.exp (-(2 * Real.pi * t)) * ((27 / 4) * Real.exp (2 * Real.pi * τ.im))
        = (27 / 4) * (Real.exp (-(2 * Real.pi * t)) * Real.exp (2 * Real.pi * τ.im)) by ring]
    rw [← Real.exp_add, show -(2 * Real.pi * t) + 2 * Real.pi * τ.im
      = -(Real.pi * (t - τ.im)) + -(Real.pi * (t - τ.im)) by ring, Real.exp_add]
    ring
  calc ‖Work.Kernels.DeltaFun z‖ * ‖Work.Kernels.jInvariantFun τ‖
      ≤ Real.exp (-(2 * Real.pi * t)) * ((27 / 4) * Real.exp (2 * Real.pi * τ.im)) :=
        mul_le_mul hΔz hjτ (norm_nonneg _) (by positivity)
    _ = (27 / 4) * Real.exp (-(Real.pi * (t - τ.im))) ^ 2 := hcombi

/-- `‖Δ(z) j(τ)‖ ≤ 1/16` for `τ` in the funnel and `z = it`. -/
private lemma funnel_rho_le (τ z : ℍ) (t : ℝ) (hτ : Funnel τ) (ht : τ.im + 1 ≤ t)
    (hz : (z : ℂ) = (t : ℂ) * Complex.I) :
    ‖Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ‖ ≤ (1 / 16 : ℝ) := by
  refine le_trans (funnel_rho_exp τ z t hτ ht hz) ?_
  have hsq : Real.exp (-(Real.pi * (t - τ.im))) ^ 2
      = Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [hsq]
  have h1 : (1 : ℝ) ≤ t - τ.im := by linarith
  have h2 : Real.exp (-(2 * Real.pi * (t - τ.im))) ≤ Real.exp (-(2 * Real.pi)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, h1])
  have h3 : (27 / 4 : ℝ) * Real.exp (-(2 * Real.pi)) ≤ 1 / 16 := by
    rw [Real.exp_neg,
      show (27 / 4 : ℝ) * (Real.exp (2 * Real.pi))⁻¹
        = 27 / (4 * Real.exp (2 * Real.pi)) by ring,
      div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Real.exp (2 * Real.pi))]
    nlinarith [ft_exp_two_pi_ge]
  linarith [h2, h3]

/-- `‖Sh τ z‖ ≥ 1/16` on the funnel. -/
private lemma funnel_Sh_ge (τ z : ℍ) (t : ℝ) (hτ : Funnel τ) (ht : τ.im + 1 ≤ t)
    (hz : (z : ℂ) = (t : ℂ) * Complex.I) :
    (1 / 16 : ℝ) ≤ ‖Compact.Sh τ z‖ := by
  have ht3 : 3 ≤ t := by linarith [hτ.2]
  have hzim : z.im = t := ft_im_of_coe hz
  have hz3 : 3 ≤ z.im := by rw [hzim]; linarith
  have hρ := funnel_rho_le τ z t hτ ht hz
  have hE4z : (1 / 2 : ℝ) ≤ ‖Work.Kernels.E4Fun z‖ := E4_imagAxis_lower z hz3
  have hE4z3 : (1 / 8 : ℝ) ≤ ‖Work.Kernels.E4Fun z ^ 3‖ := by
    rw [norm_pow]
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1 / 2) hE4z 3
    norm_num at h
    linarith
  rw [show Compact.Sh τ z
      = Work.Kernels.E4Fun z ^ 3 - Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ
    from rfl]
  have h := abs_norm_sub_norm_le (Work.Kernels.E4Fun z ^ 3)
    (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ)
  have h2 : ‖Work.Kernels.E4Fun z ^ 3‖
      - ‖Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ‖
      ≤ ‖Work.Kernels.E4Fun z ^ 3
          - Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ‖ :=
    le_trans (le_abs_self _) h
  linarith [h2, hE4z3, hρ]

/-- `Sh τ z - 1 = O(e^{-π(t - Im τ)})` on the funnel. -/
private lemma Sh_sub_one_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.Sh τ z - 1‖ ≤ C * Real.exp (-(Real.pi * (t - τ.im))) := by
  obtain ⟨C4, hC4, hE4c1⟩ := E4c1_bound
  refine ⟨C4 * Real.exp (-Real.pi) + 27 / 4, by positivity, fun τ z t hτ ht hz => ?_⟩
  have hτ2 : 2 ≤ τ.im := hτ.2
  have hzim : z.im = t := ft_im_of_coe hz
  have hz1 : 1 ≤ z.im := by rw [hzim]; linarith
  have hEpos : 0 < Real.exp (-(Real.pi * (t - τ.im))) := Real.exp_pos _
  have hE1 : Real.exp (-(Real.pi * (t - τ.im))) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, ht, τ.im_pos]
  have hρe := funnel_rho_exp τ z t hτ ht hz
  have hρ : ‖Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ‖
      ≤ (27 / 4) * Real.exp (-(Real.pi * (t - τ.im))) := by
    refine le_trans hρe ?_
    have h2 : Real.exp (-(Real.pi * (t - τ.im))) ^ 2
        ≤ Real.exp (-(Real.pi * (t - τ.im))) :=
      pow_le_of_le_one hEpos.le hE1 (by norm_num)
    nlinarith [h2, hEpos.le]
  have hsh : Compact.Sh τ z - 1
      = (Work.Kernels.E4Fun z ^ 3 - 1)
        - Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ := by
    have h1 : Compact.Sh τ z
        = Work.Kernels.E4Fun z ^ 3 - Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ :=
      rfl
    rw [h1]; ring
  have hq1 : ‖Work.Kernels.qParamFun z‖
      ≤ Real.exp (-Real.pi) * Real.exp (-(Real.pi * (t - τ.im))) := by
    rw [ft_norm_qParam hzim, ← Real.exp_add, Real.exp_le_exp]
    nlinarith [Real.pi_pos, τ.im_pos]
  have h1 : ‖Work.Kernels.E4Fun z ^ 3 - 1‖
      ≤ C4 * (Real.exp (-Real.pi) * Real.exp (-(Real.pi * (t - τ.im)))) :=
    le_trans (hE4c1 z hz1) (mul_le_mul_of_nonneg_left hq1 hC4.le)
  have h2 : ‖Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ‖
      ≤ (27 / 4) * Real.exp (-(Real.pi * (t - τ.im))) := hρ
  rw [hsh]
  calc ‖(Work.Kernels.E4Fun z ^ 3 - 1)
        - Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ‖
      ≤ ‖Work.Kernels.E4Fun z ^ 3 - 1‖
        + ‖Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ‖ :=
        norm_sub_le _ _
    _ ≤ C4 * (Real.exp (-Real.pi) * Real.exp (-(Real.pi * (t - τ.im))))
        + (27 / 4) * Real.exp (-(Real.pi * (t - τ.im))) := add_le_add h1 h2
    _ = (C4 * Real.exp (-Real.pi) + 27 / 4)
        * Real.exp (-(Real.pi * (t - τ.im))) := by ring

/-- `‖Lamb τ‖ = O((scale τ)^N)` on the funnel. -/
private lemma Lamb_growth (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖Work.Residues.Lamb ℓ τ‖ ≤ C * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨CLΔ, NLΔ, hCLΔ, hNLΔ, hLambΔ⟩ := ft_Lamb_bound ℓ
  obtain ⟨cΔ, hcΔ, hΔlow⟩ := exists_Delta_Funnel_lower
  refine ⟨CLΔ / cΔ, NLΔ, by positivity, hNLΔ, fun τ hτ => ?_⟩
  have hDne : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hqpos : 0 < ‖Work.Kernels.qParamFun τ‖ := by rw [norm_qParamFun]; positivity
  have hDpos : 0 < ‖Work.Kernels.DeltaFun τ‖ := norm_pos_iff.mpr hDne
  have h1 : ‖Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ‖
      ≤ CLΔ * (Work.Kernels.scale τ) ^ NLΔ * ‖Work.Kernels.qParamFun τ‖ := hLambΔ τ hτ
  have hlow : cΔ * ‖Work.Kernels.qParamFun τ‖ ≤ ‖Work.Kernels.DeltaFun τ‖ := by
    have h := hΔlow τ hτ
    rwa [← norm_qParamFun τ] at h
  have h2 : ‖Work.Residues.Lamb ℓ τ‖
      = ‖Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ‖ / ‖Work.Kernels.DeltaFun τ‖ := by
    rw [norm_mul]
    field_simp
  rw [h2]
  have hnum0 : (0:ℝ) ≤ ‖Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ‖ := norm_nonneg _
  have h3 : ‖Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ‖ / ‖Work.Kernels.DeltaFun τ‖
      ≤ (CLΔ * (Work.Kernels.scale τ) ^ NLΔ * ‖Work.Kernels.qParamFun τ‖)
        / (cΔ * ‖Work.Kernels.qParamFun τ‖) := by
    rw [div_le_div_iff₀ hDpos (mul_pos hcΔ hqpos)]
    calc ‖Work.Kernels.DeltaFun τ * Work.Residues.Lamb ℓ τ‖ * (cΔ * ‖Work.Kernels.qParamFun τ‖)
        ≤ (CLΔ * (Work.Kernels.scale τ) ^ NLΔ * ‖Work.Kernels.qParamFun τ‖)
            * (cΔ * ‖Work.Kernels.qParamFun τ‖) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (CLΔ * (Work.Kernels.scale τ) ^ NLΔ * ‖Work.Kernels.qParamFun τ‖)
            * ‖Work.Kernels.DeltaFun τ‖ :=
          mul_le_mul_of_nonneg_left hlow
            (mul_nonneg (mul_nonneg hCLΔ.le (ft_scale_rpow_nonneg τ NLΔ)) (norm_nonneg _))
  refine le_trans h3 ?_
  have h4 : (CLΔ * (Work.Kernels.scale τ) ^ NLΔ * ‖Work.Kernels.qParamFun τ‖)
        / (cΔ * ‖Work.Kernels.qParamFun τ‖)
      = CLΔ / cΔ * (Work.Kernels.scale τ) ^ NLΔ := by
    field_simp
  rw [h4]

/-! ## The bracket bounds -/

/-- The algebraic decomposition of `br + br0`. -/
private lemma br_add_br0_decomp (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Compact.brMinus ℓ 8 τ z + Compact.br0 8 ℓ τ z
      = -3456 * Work.Kernels.E4Fun τ
          * (Work.Kernels.E10Fun z * ℓ.L z - Compact.Xc ℓ z)
        + (-(Work.Residues.Lamb ℓ τ))
          * (Work.Kernels.E8Fun z * Work.Kernels.WFun z
              - Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2))
        + 1728 * Work.Kernels.psi4 ℓ τ
          * (Work.Kernels.E8Fun z * Work.Kernels.WFun z - 1) := by
  rw [Compact.brMinus_eight, Compact.br0_8]
  simp only [Work.Residues.bracket8e, Work.Residues.Lamb, Compact.Xc, Work.Kernels.c1728]
  ring

/-- `‖br0‖ = O((scale τ)^N (1+t))` on the funnel. -/
private lemma br0_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.br0 8 ℓ τ z‖ ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) := by
  obtain ⟨Cψ, Nψ, hCψ, hNψ, hψ4⟩ := psi4_funnel_growth ℓ
  refine ⟨3456 * (3 / 2) * (Real.pi + ‖Compact.cuspC ℓ‖) + 1728 * Cψ, Nψ,
    by positivity, hNψ, fun τ z t hτ ht hz => ?_⟩
  have ht0 : 0 < t := by linarith [hτ.2]
  have hzn : ‖(z : ℂ)‖ = t := by
    rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ t)]
  have hXc : ‖Compact.Xc ℓ z‖ ≤ (Real.pi + ‖Compact.cuspC ℓ‖) * (1 + t) := by
    have h := ft_norm_Xc ℓ z
    rwa [hzn] at h
  rw [Compact.br0_8]
  have hE4b : ‖Work.Kernels.E4Fun τ‖ ≤ 3 / 2 := E4_funnel_upper τ hτ
  have h1 : ‖(3456 : ℂ) * Work.Kernels.E4Fun τ * Compact.Xc ℓ z‖
      ≤ 3456 * (3 / 2) * ((Real.pi + ‖Compact.cuspC ℓ‖) * (1 + t)) := by
    rw [norm_mul, norm_mul, show ‖(3456 : ℂ)‖ = 3456 by norm_num]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hE4b (by norm_num)) hXc (norm_nonneg _)
      (by positivity)
  have h2 : ‖(1728 : ℂ) * Work.Kernels.psi4 ℓ τ‖
      ≤ 1728 * (Cψ * (Work.Kernels.scale τ) ^ Nψ) := by
    rw [norm_mul, show ‖(1728 : ℂ)‖ = 1728 by norm_num]
    exact mul_le_mul_of_nonneg_left (hψ4 τ hτ) (by norm_num)
  have hsum := norm_sub_le ((3456 : ℂ) * Work.Kernels.E4Fun τ * Compact.Xc ℓ z)
    ((1728 : ℂ) * Work.Kernels.psi4 ℓ τ)
  have hs3 : (1 : ℝ) ≤ Work.Kernels.scale τ ^ Nψ := Real.one_le_rpow (Work.Kernels.one_le_scale τ) hNψ
  have ht1 : (1 : ℝ) ≤ 1 + t := by linarith
  have h3 : 3456 * (3 / 2) * ((Real.pi + ‖Compact.cuspC ℓ‖) * (1 + t))
      ≤ 3456 * (3 / 2) * (Real.pi + ‖Compact.cuspC ℓ‖)
        * (Work.Kernels.scale τ) ^ Nψ * (1 + t) := by
    have hK : (0:ℝ) ≤ 3456 * (3 / 2) * ((Real.pi + ‖Compact.cuspC ℓ‖) * (1 + t)) := by
      have hpi : (0:ℝ) ≤ Real.pi + ‖Compact.cuspC ℓ‖ := by positivity
      positivity
    calc 3456 * (3 / 2) * ((Real.pi + ‖Compact.cuspC ℓ‖) * (1 + t))
        = (3456 * (3 / 2) * ((Real.pi + ‖Compact.cuspC ℓ‖) * (1 + t))) * 1 := by ring
      _ ≤ (3456 * (3 / 2) * ((Real.pi + ‖Compact.cuspC ℓ‖) * (1 + t)))
            * (Work.Kernels.scale τ) ^ Nψ := mul_le_mul_of_nonneg_left hs3 hK
      _ = 3456 * (3 / 2) * (Real.pi + ‖Compact.cuspC ℓ‖)
            * (Work.Kernels.scale τ) ^ Nψ * (1 + t) := by ring
  have h4 : 1728 * (Cψ * Work.Kernels.scale τ ^ Nψ)
      ≤ 1728 * Cψ * (Work.Kernels.scale τ) ^ Nψ * (1 + t) := by
    have hK : (0:ℝ) ≤ 1728 * (Cψ * Work.Kernels.scale τ ^ Nψ) := by
      positivity
    calc 1728 * (Cψ * Work.Kernels.scale τ ^ Nψ)
        = (1728 * (Cψ * Work.Kernels.scale τ ^ Nψ)) * 1 := by ring
      _ ≤ (1728 * (Cψ * Work.Kernels.scale τ ^ Nψ)) * (1 + t) :=
          mul_le_mul_of_nonneg_left ht1 hK
      _ = 1728 * Cψ * (Work.Kernels.scale τ) ^ Nψ * (1 + t) := by ring
  have h5 : 3456 * (3 / 2) * (Real.pi + ‖Compact.cuspC ℓ‖)
        * (Work.Kernels.scale τ) ^ Nψ * (1 + t)
      + 1728 * Cψ * (Work.Kernels.scale τ) ^ Nψ * (1 + t)
      = (3456 * (3 / 2) * (Real.pi + ‖Compact.cuspC ℓ‖) + 1728 * Cψ)
        * (Work.Kernels.scale τ) ^ Nψ * (1 + t) := by ring
  linarith [hsum, h1, h2, h3, h4]

/-- `‖br + br0‖ = O((scale τ)^N (1+t) e^{-π(t-Im τ)})` on the funnel. -/
private lemma A_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.brMinus ℓ 8 τ z + Compact.br0 8 ℓ τ z‖
        ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t)
          * Real.exp (-(Real.pi * (t - τ.im))) := by
  obtain ⟨Ce, hCe, hE10L⟩ := E10L_bound ℓ
  obtain ⟨C2, hC2, hAz⟩ := Az_bound
  obtain ⟨C3, hC3, hE8W1⟩ := E8W1_bound
  obtain ⟨Cψ, Nψ, hCψ, hNψ, hψ4⟩ := psi4_funnel_growth ℓ
  obtain ⟨CL, NL, hCL, hNL, hLamb⟩ := Lamb_growth ℓ
  refine ⟨3456 * (3 / 2) * Ce + CL * C2 + 1728 * Cψ * C3, Nψ + NL, by positivity,
    by positivity, fun τ z t hτ ht hz => ?_⟩
  have hτ2 : 2 ≤ τ.im := hτ.2
  have ht3 : 3 ≤ t := by linarith
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hzim : z.im = t := ft_im_of_coe hz
  have hz1 : 1 ≤ z.im := by rw [hzim]; linarith
  have hzn : ‖(z : ℂ)‖ = t := by
    rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ t)]
  have hE1 : ‖Work.Residues.Ept z‖ ≤ 1 := ft_Ept_le_one hz1
  have heE : ‖Work.Residues.Ept z‖ ≤ Real.exp (-(Real.pi * (t - τ.im))) := by
    rw [ft_norm_Ept hzim, Real.exp_le_exp]
    nlinarith [Real.pi_pos, τ.im_pos]
  have hE4b : ‖Work.Kernels.E4Fun τ‖ ≤ 3 / 2 := E4_funnel_upper τ hτ
  have hE10L' : ‖Work.Kernels.E10Fun z * ℓ.L z - Compact.Xc ℓ z‖
      ≤ Ce * (1 + t) * ‖Work.Residues.Ept z‖ := by
    have h := hE10L z hz1
    rwa [hzn] at h
  rw [br_add_br0_decomp ℓ τ z]
  have hA1 : ‖(-3456 : ℂ) * Work.Kernels.E4Fun τ
      * (Work.Kernels.E10Fun z * ℓ.L z - Compact.Xc ℓ z)‖
      ≤ 3456 * (3 / 2) * (Ce * (1 + t) * ‖Work.Residues.Ept z‖) := by
    rw [norm_mul, norm_mul, show ‖(-3456 : ℂ)‖ = 3456 by norm_num]
    refine mul_le_mul ?_ hE10L' (norm_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left hE4b (by norm_num)
  have hA2 : ‖(-(Work.Residues.Lamb ℓ τ))
      * (Work.Kernels.E8Fun z * Work.Kernels.WFun z
          - Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2))‖
      ≤ CL * (Work.Kernels.scale τ) ^ NL * (C2 * ‖Work.Residues.Ept z‖) := by
    rw [norm_mul, norm_neg]
    have hsNL0 : (0:ℝ) ≤ Work.Kernels.scale τ ^ NL := ft_scale_rpow_nonneg τ NL
    refine mul_le_mul (hLamb τ hτ) (hAz z hz1) (norm_nonneg _) ?_
    positivity
  have hA3 : ‖(1728 : ℂ) * Work.Kernels.psi4 ℓ τ
      * (Work.Kernels.E8Fun z * Work.Kernels.WFun z - 1)‖
      ≤ 1728 * (Cψ * (Work.Kernels.scale τ) ^ Nψ) * (C3 * ‖Work.Residues.Ept z‖) := by
    rw [norm_mul, norm_mul, show ‖(1728 : ℂ)‖ = 1728 by norm_num]
    have hsNψ0 : (0:ℝ) ≤ Work.Kernels.scale τ ^ Nψ := ft_scale_rpow_nonneg τ Nψ
    refine mul_le_mul ?_ (hE8W1 z hz1) (norm_nonneg _) ?_
    · exact mul_le_mul_of_nonneg_left (hψ4 τ hτ) (by norm_num)
    · positivity
  -- common shape
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hsNψ : Work.Kernels.scale τ ^ Nψ ≤ Work.Kernels.scale τ ^ (Nψ + NL) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
  have hsNL : Work.Kernels.scale τ ^ NL ≤ Work.Kernels.scale τ ^ (Nψ + NL) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
  have hsN1 : (1 : ℝ) ≤ Work.Kernels.scale τ ^ (Nψ + NL) :=
    Real.one_le_rpow hs1 (by linarith)
  have ht1 : (1 : ℝ) ≤ 1 + t := by linarith
  have hEpos : 0 < Real.exp (-(Real.pi * (t - τ.im))) := Real.exp_pos _
  have hbase0 : (0:ℝ) ≤ (1 + t) * Real.exp (-(Real.pi * (t - τ.im))) := by
    have h4 : (0:ℝ) ≤ 1 + t := by linarith
    positivity
  have hbaseN : (1 + t) * Real.exp (-(Real.pi * (t - τ.im)))
      ≤ (Work.Kernels.scale τ) ^ (Nψ + NL)
        * ((1 + t) * Real.exp (-(Real.pi * (t - τ.im)))) := by
    calc (1 + t) * Real.exp (-(Real.pi * (t - τ.im)))
        = ((1 + t) * Real.exp (-(Real.pi * (t - τ.im)))) * 1 := by ring
      _ ≤ ((1 + t) * Real.exp (-(Real.pi * (t - τ.im))))
            * (Work.Kernels.scale τ) ^ (Nψ + NL) := mul_le_mul_of_nonneg_left hsN1 hbase0
      _ = (Work.Kernels.scale τ) ^ (Nψ + NL)
            * ((1 + t) * Real.exp (-(Real.pi * (t - τ.im)))) := by ring
  have heS1 : ‖Work.Residues.Ept z‖ ≤ (1 + t) * Real.exp (-(Real.pi * (t - τ.im))) :=
    by nlinarith [heE, ht1, hE1]
  have heU : (1 + t) * ‖Work.Residues.Ept z‖
      ≤ (Work.Kernels.scale τ) ^ (Nψ + NL) * ((1 + t) * Real.exp (-(Real.pi * (t - τ.im)))) := by
    have h1 : (1 + t) * ‖Work.Residues.Ept z‖
        ≤ (1 + t) * Real.exp (-(Real.pi * (t - τ.im))) :=
      mul_le_mul_of_nonneg_left heE (by linarith)
    linarith [h1, hbaseN]
  have heS : ‖Work.Residues.Ept z‖
      ≤ (Work.Kernels.scale τ) ^ (Nψ + NL) * ((1 + t) * Real.exp (-(Real.pi * (t - τ.im)))) :=
    le_trans heS1 hbaseN
  have hA1U : 3456 * (3 / 2) * (Ce * (1 + t) * ‖Work.Residues.Ept z‖)
      ≤ 3456 * (3 / 2) * Ce
        * ((Work.Kernels.scale τ) ^ (Nψ + NL)
          * ((1 + t) * Real.exp (-(Real.pi * (t - τ.im))))) := by
    have h5 : (0:ℝ) ≤ 3456 * (3 / 2) * Ce := by positivity
    calc 3456 * (3 / 2) * (Ce * (1 + t) * ‖Work.Residues.Ept z‖)
        = 3456 * (3 / 2) * Ce * ((1 + t) * ‖Work.Residues.Ept z‖) := by ring
      _ ≤ 3456 * (3 / 2) * Ce
            * ((Work.Kernels.scale τ) ^ (Nψ + NL)
              * ((1 + t) * Real.exp (-(Real.pi * (t - τ.im))))) :=
          mul_le_mul_of_nonneg_left heU h5
  have hA2U : CL * (Work.Kernels.scale τ) ^ NL * (C2 * ‖Work.Residues.Ept z‖)
      ≤ CL * C2 * ((Work.Kernels.scale τ) ^ (Nψ + NL)
          * ((1 + t) * Real.exp (-(Real.pi * (t - τ.im))))) := by
    have h5 : (0:ℝ) ≤ CL * C2 := by positivity
    have h1 : (Work.Kernels.scale τ) ^ NL * ‖Work.Residues.Ept z‖
        ≤ (Work.Kernels.scale τ) ^ (Nψ + NL)
          * ((1 + t) * Real.exp (-(Real.pi * (t - τ.im)))) := by
      have h2 : (Work.Kernels.scale τ) ^ NL * ‖Work.Residues.Ept z‖
          ≤ (Work.Kernels.scale τ) ^ (Nψ + NL) * ‖Work.Residues.Ept z‖ :=
        mul_le_mul_of_nonneg_right hsNL (norm_nonneg _)
      have h3 : (Work.Kernels.scale τ) ^ (Nψ + NL) * ‖Work.Residues.Ept z‖
          ≤ (Work.Kernels.scale τ) ^ (Nψ + NL)
            * ((1 + t) * Real.exp (-(Real.pi * (t - τ.im)))) :=
        mul_le_mul_of_nonneg_left heS1 (ft_scale_rpow_nonneg τ (Nψ + NL))
      linarith [h2, h3]
    calc CL * (Work.Kernels.scale τ) ^ NL * (C2 * ‖Work.Residues.Ept z‖)
        = CL * C2 * ((Work.Kernels.scale τ) ^ NL * ‖Work.Residues.Ept z‖) := by ring
      _ ≤ CL * C2 * ((Work.Kernels.scale τ) ^ (Nψ + NL)
            * ((1 + t) * Real.exp (-(Real.pi * (t - τ.im))))) :=
          mul_le_mul_of_nonneg_left h1 h5
  have hA3U : 1728 * (Cψ * (Work.Kernels.scale τ) ^ Nψ) * (C3 * ‖Work.Residues.Ept z‖)
      ≤ 1728 * Cψ * C3 * ((Work.Kernels.scale τ) ^ (Nψ + NL)
          * ((1 + t) * Real.exp (-(Real.pi * (t - τ.im))))) := by
    have h5 : (0:ℝ) ≤ 1728 * Cψ * C3 := by positivity
    have h1 : (Work.Kernels.scale τ) ^ Nψ * ‖Work.Residues.Ept z‖
        ≤ (Work.Kernels.scale τ) ^ (Nψ + NL)
          * ((1 + t) * Real.exp (-(Real.pi * (t - τ.im)))) := by
      have h2 : (Work.Kernels.scale τ) ^ Nψ * ‖Work.Residues.Ept z‖
          ≤ (Work.Kernels.scale τ) ^ (Nψ + NL) * ‖Work.Residues.Ept z‖ :=
        mul_le_mul_of_nonneg_right hsNψ (norm_nonneg _)
      have h3 : (Work.Kernels.scale τ) ^ (Nψ + NL) * ‖Work.Residues.Ept z‖
          ≤ (Work.Kernels.scale τ) ^ (Nψ + NL)
            * ((1 + t) * Real.exp (-(Real.pi * (t - τ.im)))) :=
        mul_le_mul_of_nonneg_left heS1 (ft_scale_rpow_nonneg τ (Nψ + NL))
      linarith [h2, h3]
    calc 1728 * (Cψ * (Work.Kernels.scale τ) ^ Nψ) * (C3 * ‖Work.Residues.Ept z‖)
        = 1728 * Cψ * C3 * ((Work.Kernels.scale τ) ^ Nψ * ‖Work.Residues.Ept z‖) := by ring
      _ ≤ 1728 * Cψ * C3 * ((Work.Kernels.scale τ) ^ (Nψ + NL)
            * ((1 + t) * Real.exp (-(Real.pi * (t - τ.im))))) :=
          mul_le_mul_of_nonneg_left h1 h5
  have hsum1 := norm_add_le ((-3456 : ℂ) * Work.Kernels.E4Fun τ
      * (Work.Kernels.E10Fun z * ℓ.L z - Compact.Xc ℓ z)
      + (-(Work.Residues.Lamb ℓ τ))
        * (Work.Kernels.E8Fun z * Work.Kernels.WFun z
            - Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)))
    ((1728 : ℂ) * Work.Kernels.psi4 ℓ τ
      * (Work.Kernels.E8Fun z * Work.Kernels.WFun z - 1))
  have hsum2 := norm_add_le ((-3456 : ℂ) * Work.Kernels.E4Fun τ
      * (Work.Kernels.E10Fun z * ℓ.L z - Compact.Xc ℓ z))
    ((-(Work.Residues.Lamb ℓ τ))
      * (Work.Kernels.E8Fun z * Work.Kernels.WFun z
          - Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)))
  have hcomb : 3456 * (3 / 2) * Ce * ((Work.Kernels.scale τ) ^ (Nψ + NL)
        * ((1 + t) * Real.exp (-(Real.pi * (t - τ.im)))))
      + CL * C2 * ((Work.Kernels.scale τ) ^ (Nψ + NL)
        * ((1 + t) * Real.exp (-(Real.pi * (t - τ.im)))))
      + 1728 * Cψ * C3 * ((Work.Kernels.scale τ) ^ (Nψ + NL)
        * ((1 + t) * Real.exp (-(Real.pi * (t - τ.im)))))
      = (3456 * (3 / 2) * Ce + CL * C2 + 1728 * Cψ * C3)
        * (Work.Kernels.scale τ) ^ (Nψ + NL) * (1 + t)
        * Real.exp (-(Real.pi * (t - τ.im))) := by ring
  linarith [hsum1, hsum2, hA1, hA2, hA3, hA1U, hA2U, hA3U, hcomb]

/-! ## The main theorem -/

theorem KMinus_funnel_tail_eight (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        (z : ℂ) = (t : ℂ) * Complex.I →
        ‖Work.Kernels.KMinus ℓ 8 τ z - Work.Asymptotics.Compact.Gminus 8 ℓ τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * (t - τ.im))) := by
  obtain ⟨CA, NA, hCA, hNA, hA⟩ := A_bound ℓ
  obtain ⟨CB, NB, hCB, hNB, hbr0⟩ := br0_bound ℓ
  obtain ⟨CS, hCS, hShm1⟩ := Sh_sub_one_bound
  refine ⟨(3456 * Real.pi)⁻¹ * 16 * (CA + CS * CB), NA + NB, 1, by positivity, by positivity,
    by norm_num, ?_⟩
  intro τ z t hτ ht hz
  have ht0 : (0 : ℝ) ≤ t := by linarith [τ.im_pos, ht]
  have ht3 : (3 : ℝ) ≤ t := by linarith [hτ.2]
  have hSh16 : (1 / 16 : ℝ) ≤ ‖Compact.Sh τ z‖ := funnel_Sh_ge τ z t hτ ht hz
  have hShne : Compact.Sh τ z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hSh16
    norm_num at hSh16
  have hinvSh : ‖(Compact.Sh τ z)⁻¹‖ ≤ 16 := by
    rw [norm_inv, inv_le_iff_one_le_mul₀ (lt_of_lt_of_le (by norm_num) hSh16)]
    linarith [hSh16]
  have htail := Compact.tail_identity ℓ 8 (Or.inl rfl) τ z hShne
  have hAeq : Compact.brMinus ℓ 8 τ z + Compact.Sh τ z * Compact.br0 8 ℓ τ z
      = (Compact.brMinus ℓ 8 τ z + Compact.br0 8 ℓ τ z)
        + (Compact.Sh τ z - 1) * Compact.br0 8 ℓ τ z := by ring
  have hAb := hA τ z t hτ ht hz
  have hSb := hShm1 τ z t hτ ht hz
  have hBb := hbr0 τ z t hτ ht hz
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hsNA : Work.Kernels.scale τ ^ NA ≤ Work.Kernels.scale τ ^ (NA + NB) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
  have hsNB : Work.Kernels.scale τ ^ NB ≤ Work.Kernels.scale τ ^ (NA + NB) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
  have hsN1 : (1 : ℝ) ≤ Work.Kernels.scale τ ^ (NA + NB) := Real.one_le_rpow hs1 (by linarith)
  have ht1 : (1 : ℝ) ≤ 1 + t := by linarith
  have hEpos : 0 < Real.exp (-(Real.pi * (t - τ.im))) := Real.exp_pos _
  have hE1 : Real.exp (-(Real.pi * (t - τ.im))) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, ht, τ.im_pos]
  have hAb' : ‖Compact.brMinus ℓ 8 τ z + Compact.br0 8 ℓ τ z‖
      ≤ CA * (Work.Kernels.scale τ) ^ (NA + NB) * (1 + t)
        * Real.exp (-(Real.pi * (t - τ.im))) := by
    refine le_trans hAb ?_
    have h5 : (0:ℝ) ≤ CA := hCA.le
    have h6 : (Work.Kernels.scale τ) ^ NA * (1 + t) * Real.exp (-(Real.pi * (t - τ.im)))
        ≤ (Work.Kernels.scale τ) ^ (NA + NB) * (1 + t)
          * Real.exp (-(Real.pi * (t - τ.im))) := by
      have h7 : (0:ℝ) ≤ (1 + t) * Real.exp (-(Real.pi * (t - τ.im))) := by positivity
      calc (Work.Kernels.scale τ) ^ NA * (1 + t) * Real.exp (-(Real.pi * (t - τ.im)))
          = (Work.Kernels.scale τ) ^ NA * ((1 + t)
              * Real.exp (-(Real.pi * (t - τ.im)))) := by ring
        _ ≤ (Work.Kernels.scale τ) ^ (NA + NB) * ((1 + t)
              * Real.exp (-(Real.pi * (t - τ.im)))) :=
            mul_le_mul_of_nonneg_right hsNA h7
        _ = (Work.Kernels.scale τ) ^ (NA + NB) * (1 + t)
              * Real.exp (-(Real.pi * (t - τ.im))) := by ring
    calc CA * (Work.Kernels.scale τ) ^ NA * (1 + t) * Real.exp (-(Real.pi * (t - τ.im)))
        = CA * ((Work.Kernels.scale τ) ^ NA * (1 + t)
            * Real.exp (-(Real.pi * (t - τ.im)))) := by ring
      _ ≤ CA * ((Work.Kernels.scale τ) ^ (NA + NB) * (1 + t)
            * Real.exp (-(Real.pi * (t - τ.im)))) := mul_le_mul_of_nonneg_left h6 h5
      _ = CA * (Work.Kernels.scale τ) ^ (NA + NB) * (1 + t)
            * Real.exp (-(Real.pi * (t - τ.im))) := by ring
  have hBb' : ‖Compact.br0 8 ℓ τ z‖
      ≤ CB * (Work.Kernels.scale τ) ^ (NA + NB) * (1 + t) := by
    refine le_trans hBb ?_
    have h5 : (0:ℝ) ≤ CB := hCB.le
    have h6 : (Work.Kernels.scale τ) ^ NB * (1 + t)
        ≤ (Work.Kernels.scale τ) ^ (NA + NB) * (1 + t) :=
      mul_le_mul_of_nonneg_right hsNB (by linarith)
    calc CB * (Work.Kernels.scale τ) ^ NB * (1 + t)
        = CB * ((Work.Kernels.scale τ) ^ NB * (1 + t)) := by ring
      _ ≤ CB * ((Work.Kernels.scale τ) ^ (NA + NB) * (1 + t)) :=
          mul_le_mul_of_nonneg_left h6 h5
      _ = CB * (Work.Kernels.scale τ) ^ (NA + NB) * (1 + t) := by ring
  have hkey : ‖(Compact.Sh τ z)⁻¹
      * (Compact.brMinus ℓ 8 τ z + Compact.Sh τ z * Compact.br0 8 ℓ τ z)‖
      ≤ 16 * (CA + CS * CB) * ((Work.Kernels.scale τ) ^ (NA + NB) * (1 + t)
          * Real.exp (-(Real.pi * (t - τ.im)))) := by
    rw [hAeq]
    have h1 : ‖(Compact.Sh τ z)⁻¹
        * ((Compact.brMinus ℓ 8 τ z + Compact.br0 8 ℓ τ z)
          + (Compact.Sh τ z - 1) * Compact.br0 8 ℓ τ z)‖
        ≤ 16 * (‖Compact.brMinus ℓ 8 τ z + Compact.br0 8 ℓ τ z‖
          + ‖(Compact.Sh τ z - 1) * Compact.br0 8 ℓ τ z‖) := by
      refine le_trans (norm_mul_le _ _) ?_
      refine le_trans (mul_le_mul_of_nonneg_right hinvSh (norm_nonneg _)) ?_
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    refine le_trans h1 ?_
    have h2 : ‖(Compact.Sh τ z - 1) * Compact.br0 8 ℓ τ z‖
        ≤ (CS * Real.exp (-(Real.pi * (t - τ.im))))
          * (CB * (Work.Kernels.scale τ) ^ (NA + NB) * (1 + t)) := by
      rw [norm_mul]
      exact mul_le_mul hSb hBb' (norm_nonneg _) (by positivity)
    have h3 : (0:ℝ) ≤ 16 := by norm_num
    have h4 : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ (NA + NB) * (1 + t)
        * Real.exp (-(Real.pi * (t - τ.im))) := by positivity
    have h5 : 16 * (CA * (Work.Kernels.scale τ) ^ (NA + NB) * (1 + t)
          * Real.exp (-(Real.pi * (t - τ.im)))
        + (CS * Real.exp (-(Real.pi * (t - τ.im))))
          * (CB * (Work.Kernels.scale τ) ^ (NA + NB) * (1 + t)))
        = 16 * (CA + CS * CB) * ((Work.Kernels.scale τ) ^ (NA + NB) * (1 + t)
          * Real.exp (-(Real.pi * (t - τ.im)))) := by ring
    have h6 : (0:ℝ) ≤ CS * Real.exp (-(Real.pi * (t - τ.im))) := by positivity
    have h7 : (0:ℝ) ≤ CB * (Work.Kernels.scale τ) ^ (NA + NB) * (1 + t) := by
      have := ft_scale_rpow_nonneg τ (NA + NB)
      positivity
    linarith [hAb', h2, h3, h5]
  have hnorm : (3456 * Real.pi) * ‖Work.Kernels.KMinus ℓ 8 τ z
      - Compact.Gminus 8 ℓ τ z‖
      = ‖(Compact.Sh τ z)⁻¹
          * (Compact.brMinus ℓ 8 τ z + Compact.Sh τ z * Compact.br0 8 ℓ τ z)‖ := by
    have h2 : ‖(3456 : ℂ) * (Real.pi : ℂ)
        * (Work.Kernels.KMinus ℓ 8 τ z - Compact.Gminus 8 ℓ τ z)‖
        = (3456 * Real.pi) * ‖Work.Kernels.KMinus ℓ 8 τ z
            - Compact.Gminus 8 ℓ τ z‖ := by
      rw [norm_mul, norm_mul, show ‖(3456 : ℂ)‖ = 3456 by norm_num, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [← h2, htail, norm_neg]
  have hstep : ‖Work.Kernels.KMinus ℓ 8 τ z - Compact.Gminus 8 ℓ τ z‖
      ≤ (3456 * Real.pi)⁻¹ * (16 * (CA + CS * CB)
        * ((Work.Kernels.scale τ) ^ (NA + NB) * (1 + t)
          * Real.exp (-(Real.pi * (t - τ.im))))) := by
    have hmult : (3456 * Real.pi) * ‖Work.Kernels.KMinus ℓ 8 τ z
        - Compact.Gminus 8 ℓ τ z‖
        ≤ 16 * (CA + CS * CB) * ((Work.Kernels.scale τ) ^ (NA + NB) * (1 + t)
          * Real.exp (-(Real.pi * (t - τ.im)))) := by
      rw [hnorm]; exact hkey
    calc ‖Work.Kernels.KMinus ℓ 8 τ z - Compact.Gminus 8 ℓ τ z‖
        = (3456 * Real.pi)⁻¹ * ((3456 * Real.pi)
            * ‖Work.Kernels.KMinus ℓ 8 τ z - Compact.Gminus 8 ℓ τ z‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (3456 * Real.pi) ≠ 0), one_mul]
      _ ≤ (3456 * Real.pi)⁻¹ * (16 * (CA + CS * CB)
            * ((Work.Kernels.scale τ) ^ (NA + NB) * (1 + t)
              * Real.exp (-(Real.pi * (t - τ.im))))) :=
          mul_le_mul_of_nonneg_left hmult (by positivity)
  refine le_trans hstep ?_
  rw [Real.rpow_one]
  have hX0 : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ (NA + NB) * (1 + t)
      * Real.exp (-(Real.pi * (t - τ.im))) := by positivity
  have hM0 : (0:ℝ) ≤ 16 * (CA + CS * CB) := by positivity
  have hgoal : (3456 * Real.pi)⁻¹ * (16 * (CA + CS * CB)
        * ((Work.Kernels.scale τ) ^ (NA + NB) * (1 + t)
          * Real.exp (-(Real.pi * (t - τ.im)))))
      = (3456 * Real.pi)⁻¹ * 16 * (CA + CS * CB)
        * ((Work.Kernels.scale τ) ^ (NA + NB) * (1 + t)
          * Real.exp (-(Real.pi * (t - τ.im)))) := by ring
  rw [hgoal]
  nlinarith [hX0, hM0]

end

end Work.Asymptotics
