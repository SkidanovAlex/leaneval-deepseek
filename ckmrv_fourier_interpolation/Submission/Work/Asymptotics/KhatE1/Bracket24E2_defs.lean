/-
# The `E²`-coefficient of the `Sh`-cleared `d = 24` bracket: `O(‖q‖)` calculus

This file sets up the `Bound` calculus (bounds of the shape `C (scale τ)^N (1+t)^M ‖q τ‖^n`
on the funnel strip), records the atom bounds, and defines the explicit expressions
`Kappa`/`Rest` (the `J`-part and `J`-free part of `Bracket24E2 ℓ τ z = J·κ + ρ`), their
truncations `KappaHat`/`RestHat` (with `A`, `B`, `E₂`, `Δ`, `ψ₂`, `ψ₄` replaced by their
first-order truncations `A₀ = 1+240q`, …), the `(πz)²`-cleared forms, and the divisibility
identity `A₁κ̂ + qρ̂ = q²Δ₂` (`kappahat_identity`).
-/
import Mathlib
import Submission.Work.Asymptotics.KhatE1.Bracket24ClearedDefs
import Submission.Work.Asymptotics.KhatE1Core.psi_second_order
import Submission.Work.Asymptotics.KhatE1Core.psi_individual_first_order
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KPlusXiDefs

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-- `BoundW f n C N M` : on the funnel strip, `‖f τ z‖ ≤ C (scale τ)^N (1+t)^M ‖q τ‖^n`. -/
def BoundW (f : UpperHalfPlane → UpperHalfPlane → ℂ) (n : ℕ) (C N M : ℝ) : Prop :=
  0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
      0 ≤ z.re → z.re ≤ 1 → z.im = t →
      ‖f τ z‖ ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * ‖Work.Kernels.qParamFun τ‖ ^ n

/-- `Bound f n` : a bound of the shape `C (scale τ)^N (1+t)^M ‖q τ‖^n` on the funnel strip. -/
def Bound (f : UpperHalfPlane → UpperHalfPlane → ℂ) (n : ℕ) : Prop :=
  ∃ C N M : ℝ, BoundW f n C N M

section Basic

variable {τ z : UpperHalfPlane} {t : ℝ}

lemma funnel_three_le_t (hτ : Work.Asymptotics.Funnel τ) (ht : τ.im + 1 ≤ t) : (3:ℝ) ≤ t := by
  have := hτ.2; linarith

lemma norm_qParamFun_le_one' (hτ : Work.Asymptotics.Funnel τ) :
    ‖Work.Kernels.qParamFun τ‖ ≤ 1 := by
  rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
  nlinarith [Real.pi_pos, hτ.2]

lemma norm_qParamFun_pos' (τ : UpperHalfPlane) : 0 < ‖Work.Kernels.qParamFun τ‖ := by
  rw [Work.Asymptotics.norm_qParamFun]; exact Real.exp_pos _

lemma one_le_one_add_t (hτ : Work.Asymptotics.Funnel τ) (ht : τ.im + 1 ≤ t) :
    (1:ℝ) ≤ 1 + t := by
  have := funnel_three_le_t hτ ht; linarith

lemma norm_coe_tau_le_scale (τ : UpperHalfPlane) : ‖(τ : ℂ)‖ ≤ Work.Kernels.scale τ :=
  Work.Kernels.coe_norm_le_scale τ

lemma norm_coe_z_le (hτ : Work.Asymptotics.Funnel τ) (ht : τ.im + 1 ≤ t)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) (hzim : z.im = t) : ‖(z : ℂ)‖ ≤ 1 + t := by
  have ht3 : (0:ℝ) ≤ t := by have := funnel_three_le_t hτ ht; linarith
  have h1 : ‖(z : ℂ)‖ ≤ |(z : ℂ).re| + |(z : ℂ).im| := Complex.norm_le_abs_re_add_abs_im _
  rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, abs_of_nonneg hz0, hzim,
    abs_of_nonneg ht3] at h1
  linarith

lemma three_le_norm_coe_z (hτ : Work.Asymptotics.Funnel τ) (ht : τ.im + 1 ≤ t)
    (hzim : z.im = t) : (3:ℝ) ≤ ‖(z : ℂ)‖ := by
  have ht3 : (3:ℝ) ≤ t := funnel_three_le_t hτ ht
  have h1 : |(z : ℂ).im| ≤ ‖(z : ℂ)‖ := Complex.abs_im_le_norm _
  rw [UpperHalfPlane.coe_im, hzim, abs_of_nonneg (by linarith)] at h1
  linarith

lemma norm_S0z_le (hτ : Work.Asymptotics.Funnel τ) (ht : τ.im + 1 ≤ t)
    (hzim : z.im = t) : ‖S0z z‖ ≤ 2 := by
  have hzn : (3:ℝ) ≤ ‖(z : ℂ)‖ := three_le_norm_coe_z hτ ht hzim
  have hz0 : (z : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hzn; norm_num at hzn
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hkey : ‖(6 : ℂ) * Complex.I / ((Real.pi : ℂ) * (z : ℂ))‖ ≤ 2 / 3 := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hzn, Real.pi_gt_three]
  have h2 : ‖(1 : ℂ) - (6 : ℂ) * Complex.I / ((Real.pi : ℂ) * (z : ℂ))‖
      ≤ 1 + ‖(6 : ℂ) * Complex.I / ((Real.pi : ℂ) * (z : ℂ))‖ := by
    have h := norm_sub_le (1 : ℂ) ((6 : ℂ) * Complex.I / ((Real.pi : ℂ) * (z : ℂ)))
    rwa [norm_one] at h
  rw [S0z]
  linarith

lemma rpow_scale_mono {N N' : ℝ} (h : N ≤ N') (τ : UpperHalfPlane) :
    Work.Kernels.scale τ ^ N ≤ Work.Kernels.scale τ ^ N' :=
  Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale τ) h

lemma rpow_one_add_mono {M M' : ℝ} (h : M ≤ M') (hτ : Work.Asymptotics.Funnel τ)
    (ht : τ.im + 1 ≤ t) : (1 + t) ^ M ≤ (1 + t) ^ M' :=
  Real.rpow_le_rpow_of_exponent_le (one_le_one_add_t hτ ht) h

lemma pow_q_mono {m n : ℕ} (h : m ≤ n) (hτ : Work.Asymptotics.Funnel τ) :
    ‖Work.Kernels.qParamFun τ‖ ^ n ≤ ‖Work.Kernels.qParamFun τ‖ ^ m :=
  pow_le_pow_of_le_one (norm_nonneg _) (norm_qParamFun_le_one' hτ) h

/-- Product monotonicity for four nonnegative factors. -/
lemma mul4_le {a b c d a' b' c' d' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (hd : d ≤ d')
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d) :
    a * b * c * d ≤ a' * b' * c' * d' := by
  have hb' : 0 ≤ b' := le_trans hb0 hb
  have hc' : 0 ≤ c' := le_trans hc0 hc
  have hd' : 0 ≤ d' := le_trans hd0 hd
  have h1' : a * b ≤ a' * b' := mul_le_mul ha hb hb0 (le_trans ha0 ha)
  have h2' : c * d ≤ c' * d' := mul_le_mul hc hd hd0 (le_trans hc0 hc)
  calc a * b * c * d = (a * b) * (c * d) := by ring
    _ ≤ (a' * b') * (c' * d') := mul_le_mul h1' h2' (mul_nonneg hc0 hd0)
        (mul_nonneg (le_trans ha0 ha) hb')
    _ = a' * b' * c' * d' := by ring

end Basic

/-! ## The `Bound` calculus -/

section Calculus

theorem BoundW.mono {f : UpperHalfPlane → UpperHalfPlane → ℂ} {n m : ℕ}
    {C N M C' N' M' : ℝ} (hnm : n ≤ m) (hC : C ≤ C') (hN : N ≤ N') (hM : M ≤ M')
    (h : BoundW f m C N M) : BoundW f n C' N' M' := by
  obtain ⟨hC0, hN0, hM0, hb⟩ := h
  refine ⟨lt_of_lt_of_le hC0 hC, le_trans hN0 hN, le_trans hM0 hM, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hs0 : (0:ℝ) ≤ Work.Kernels.scale τ := (Work.Kernels.scale_pos τ).le
  have ht0 : (0:ℝ) ≤ 1 + t := le_trans zero_le_one (one_le_one_add_t hF ht)
  have hq0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  refine le_trans (hb τ z t hF ht hz0 hz1 hzim) ?_
  refine mul4_le hC (rpow_scale_mono hN τ) (rpow_one_add_mono hM hF ht)
    (pow_q_mono hnm hF) hC0.le ?_ ?_ ?_
  · exact Real.rpow_nonneg hs0 _
  · exact Real.rpow_nonneg ht0 _
  · exact pow_nonneg hq0 _

theorem Bound.mono {f : UpperHalfPlane → UpperHalfPlane → ℂ} {n m : ℕ} (hnm : n ≤ m)
    (h : Bound f m) : Bound f n := by
  obtain ⟨C, N, M, h⟩ := h
  exact ⟨C, N, M, BoundW.mono hnm le_rfl le_rfl le_rfl h⟩

theorem BoundW.add {f g : UpperHalfPlane → UpperHalfPlane → ℂ} {m n : ℕ} {C1 N1 M1 C2 N2 M2 : ℝ}
    (hf : BoundW f m C1 N1 M1) (hg : BoundW g n C2 N2 M2) :
    BoundW (fun τ z => f τ z + g τ z) (min m n) (C1 + C2 + 1) (max N1 N2) (max M1 M2) := by
  obtain ⟨hC1, hN1, hM1, hb1⟩ := hf
  obtain ⟨hC2, hN2, hM2, hb2⟩ := hg
  refine ⟨by linarith, le_trans hN1 (le_max_left _ _), le_trans hM1 (le_max_left _ _),
    fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hs0 : (0:ℝ) ≤ Work.Kernels.scale τ := (Work.Kernels.scale_pos τ).le
  have ht0 : (0:ℝ) ≤ 1 + t := le_trans zero_le_one (one_le_one_add_t hF ht)
  have hq0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hN1' : Work.Kernels.scale τ ^ N1 ≤ Work.Kernels.scale τ ^ max N1 N2 :=
    rpow_scale_mono (le_max_left _ _) τ
  have hN2' : Work.Kernels.scale τ ^ N2 ≤ Work.Kernels.scale τ ^ max N1 N2 :=
    rpow_scale_mono (le_max_right _ _) τ
  have hM1' : (1 + t) ^ M1 ≤ (1 + t) ^ max M1 M2 := rpow_one_add_mono (le_max_left _ _) hF ht
  have hM2' : (1 + t) ^ M2 ≤ (1 + t) ^ max M1 M2 := rpow_one_add_mono (le_max_right _ _) hF ht
  have hm' : ‖Work.Kernels.qParamFun τ‖ ^ m ≤ ‖Work.Kernels.qParamFun τ‖ ^ min m n :=
    pow_q_mono (min_le_left _ _) hF
  have hn' : ‖Work.Kernels.qParamFun τ‖ ^ n ≤ ‖Work.Kernels.qParamFun τ‖ ^ min m n :=
    pow_q_mono (min_le_right _ _) hF
  have hS0 : (0:ℝ) ≤ Work.Kernels.scale τ ^ max N1 N2 := Real.rpow_nonneg hs0 _
  have hT0 : (0:ℝ) ≤ (1 + t) ^ max M1 M2 := Real.rpow_nonneg ht0 _
  have hQ0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ min m n := pow_nonneg hq0 _
  have e1 : ‖f τ z‖ ≤ C1 * Work.Kernels.scale τ ^ max N1 N2 * (1 + t) ^ max M1 M2
      * ‖Work.Kernels.qParamFun τ‖ ^ min m n :=
    le_trans (hb1 τ z t hF ht hz0 hz1 hzim)
      (mul4_le (le_refl C1) hN1' hM1' hm' hC1.le (Real.rpow_nonneg hs0 _)
        (Real.rpow_nonneg ht0 _) (pow_nonneg hq0 _))
  have e2 : ‖g τ z‖ ≤ C2 * Work.Kernels.scale τ ^ max N1 N2 * (1 + t) ^ max M1 M2
      * ‖Work.Kernels.qParamFun τ‖ ^ min m n :=
    le_trans (hb2 τ z t hF ht hz0 hz1 hzim)
      (mul4_le (le_refl C2) hN2' hM2' hn' hC2.le (Real.rpow_nonneg hs0 _)
        (Real.rpow_nonneg ht0 _) (pow_nonneg hq0 _))
  have h12 : C1 * Work.Kernels.scale τ ^ max N1 N2 * (1 + t) ^ max M1 M2
        * ‖Work.Kernels.qParamFun τ‖ ^ min m n
      + C2 * Work.Kernels.scale τ ^ max N1 N2 * (1 + t) ^ max M1 M2
        * ‖Work.Kernels.qParamFun τ‖ ^ min m n
      ≤ (C1 + C2 + 1) * Work.Kernels.scale τ ^ max N1 N2 * (1 + t) ^ max M1 M2
        * ‖Work.Kernels.qParamFun τ‖ ^ min m n := by
    have hfac : (0:ℝ) ≤ Work.Kernels.scale τ ^ max N1 N2 * (1 + t) ^ max M1 M2
        * ‖Work.Kernels.qParamFun τ‖ ^ min m n := mul_nonneg (mul_nonneg hS0 hT0) hQ0
    nlinarith [hfac]
  calc ‖f τ z + g τ z‖ ≤ ‖f τ z‖ + ‖g τ z‖ := norm_add_le _ _
    _ ≤ (C1 + C2 + 1) * Work.Kernels.scale τ ^ max N1 N2 * (1 + t) ^ max M1 M2
          * ‖Work.Kernels.qParamFun τ‖ ^ min m n := le_trans (add_le_add e1 e2) h12

theorem Bound.add {f g : UpperHalfPlane → UpperHalfPlane → ℂ} {m n : ℕ} (hf : Bound f m)
    (hg : Bound g n) : Bound (fun τ z => f τ z + g τ z) (min m n) := by
  obtain ⟨C1, N1, M1, hf⟩ := hf
  obtain ⟨C2, N2, M2, hg⟩ := hg
  exact ⟨_, _, _, hf.add hg⟩

theorem BoundW.mul {f g : UpperHalfPlane → UpperHalfPlane → ℂ} {m n : ℕ} {C1 N1 M1 C2 N2 M2 : ℝ}
    (hf : BoundW f m C1 N1 M1) (hg : BoundW g n C2 N2 M2) :
    BoundW (fun τ z => f τ z * g τ z) (m + n) (C1 * C2) (N1 + N2) (M1 + M2) := by
  obtain ⟨hC1, hN1, hM1, hb1⟩ := hf
  obtain ⟨hC2, hN2, hM2, hb2⟩ := hg
  refine ⟨mul_pos hC1 hC2, add_nonneg hN1 hN2, add_nonneg hM1 hM2, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hs0 : (0:ℝ) < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
  have ht0 : (0:ℝ) < 1 + t := lt_of_lt_of_le one_pos (one_le_one_add_t hF ht)
  have hq0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hA : (0:ℝ) ≤ C1 * Work.Kernels.scale τ ^ N1 * (1 + t) ^ M1
      * ‖Work.Kernels.qParamFun τ‖ ^ m :=
    mul_nonneg (mul_nonneg (mul_nonneg hC1.le (Real.rpow_nonneg hs0.le _))
      (Real.rpow_nonneg ht0.le _)) (pow_nonneg hq0 _)
  have hkey : (C1 * Work.Kernels.scale τ ^ N1 * (1 + t) ^ M1 * ‖Work.Kernels.qParamFun τ‖ ^ m)
      * (C2 * Work.Kernels.scale τ ^ N2 * (1 + t) ^ M2 * ‖Work.Kernels.qParamFun τ‖ ^ n)
      = C1 * C2 * Work.Kernels.scale τ ^ (N1 + N2) * (1 + t) ^ (M1 + M2)
        * ‖Work.Kernels.qParamFun τ‖ ^ (m + n) := by
    rw [Real.rpow_add hs0, Real.rpow_add ht0, pow_add]; ring
  rw [norm_mul, ← hkey]
  exact mul_le_mul (hb1 τ z t hF ht hz0 hz1 hzim) (hb2 τ z t hF ht hz0 hz1 hzim)
    (norm_nonneg _) hA

theorem Bound.mul {f g : UpperHalfPlane → UpperHalfPlane → ℂ} {m n : ℕ} (hf : Bound f m)
    (hg : Bound g n) : Bound (fun τ z => f τ z * g τ z) (m + n) := by
  obtain ⟨C1, N1, M1, hf⟩ := hf
  obtain ⟨C2, N2, M2, hg⟩ := hg
  exact ⟨_, _, _, hf.mul hg⟩

theorem BoundW.const_mul (c : ℂ) {f : UpperHalfPlane → UpperHalfPlane → ℂ} {n : ℕ}
    {C N M : ℝ} (hf : BoundW f n C N M) :
    BoundW (fun τ z => c * f τ z) n (‖c‖ * C + 1) N M := by
  obtain ⟨hC, hN, hM, hb⟩ := hf
  refine ⟨by positivity, hN, hM, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hs0 : (0:ℝ) ≤ Work.Kernels.scale τ := (Work.Kernels.scale_pos τ).le
  have ht0 : (0:ℝ) ≤ 1 + t := le_trans zero_le_one (one_le_one_add_t hF ht)
  have hq0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have h0 : (0:ℝ) ≤ Work.Kernels.scale τ ^ N * (1 + t) ^ M
      * ‖Work.Kernels.qParamFun τ‖ ^ n :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0 _) (Real.rpow_nonneg ht0 _)) (pow_nonneg hq0 _)
  rw [norm_mul]
  calc ‖c‖ * ‖f τ z‖
      ≤ ‖c‖ * (C * Work.Kernels.scale τ ^ N * (1 + t) ^ M * ‖Work.Kernels.qParamFun τ‖ ^ n) :=
        mul_le_mul_of_nonneg_left (hb τ z t hF ht hz0 hz1 hzim) (norm_nonneg _)
    _ ≤ (‖c‖ * C + 1) * Work.Kernels.scale τ ^ N * (1 + t) ^ M
        * ‖Work.Kernels.qParamFun τ‖ ^ n := by
        nlinarith [h0, norm_nonneg c, hC.le]

theorem Bound.const_mul (c : ℂ) {f : UpperHalfPlane → UpperHalfPlane → ℂ} {n : ℕ}
    (hf : Bound f n) : Bound (fun τ z => c * f τ z) n := by
  obtain ⟨C, N, M, hf⟩ := hf
  exact ⟨_, _, _, hf.const_mul c⟩

theorem BoundW.neg {f : UpperHalfPlane → UpperHalfPlane → ℂ} {n : ℕ} {C N M : ℝ}
    (hf : BoundW f n C N M) : BoundW (fun τ z => -f τ z) n C N M := by
  obtain ⟨hC, hN, hM, hb⟩ := hf
  exact ⟨hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => by
    rw [norm_neg]; exact hb τ z t hF ht hz0 hz1 hzim⟩

theorem Bound.neg {f : UpperHalfPlane → UpperHalfPlane → ℂ} {n : ℕ} (hf : Bound f n) :
    Bound (fun τ z => -f τ z) n := by
  obtain ⟨C, N, M, hf⟩ := hf
  exact ⟨_, _, _, hf.neg⟩

theorem Bound.congr {f g : UpperHalfPlane → UpperHalfPlane → ℂ} {n : ℕ} (h : Bound f n)
    (hfg : ∀ τ z, f τ z = g τ z) : Bound g n := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  exact ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => by
    rw [← hfg τ z]; exact hb τ z t hF ht hz0 hz1 hzim⟩

theorem Bound.sub {f g : UpperHalfPlane → UpperHalfPlane → ℂ} {m n : ℕ} (hf : Bound f m)
    (hg : Bound g n) : Bound (fun τ z => f τ z - g τ z) (min m n) :=
  Bound.congr (hf.add hg.neg) (fun τ z => by ring)

theorem BoundW.const (c : ℂ) : BoundW (fun _ _ => c) 0 (‖c‖ + 1) 0 0 := by
  refine ⟨by positivity, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  rw [Real.rpow_zero, Real.rpow_zero, pow_zero, mul_one, mul_one, mul_one]
  linarith [norm_nonneg c]

theorem Bound.const (c : ℂ) : Bound (fun _ _ => c) 0 := ⟨_, _, _, BoundW.const c⟩

theorem Bound.one : Bound (fun _ _ => (1:ℂ)) 0 :=
  Bound.congr (Bound.const 1) (fun _ _ => by simp)

theorem Bound.of_le {f g : UpperHalfPlane → UpperHalfPlane → ℂ} {n : ℕ} (hg : Bound g n)
    (h : ∀ τ z, ‖f τ z‖ ≤ ‖g τ z‖) : Bound f n := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := hg
  exact ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim =>
    le_trans (h τ z) (hb τ z t hF ht hz0 hz1 hzim)⟩

end Calculus

/-! ## Atom bounds -/

section Atoms

theorem Bound.of_isBigOq {f : UpperHalfPlane → ℂ} {n : ℕ} (h : Work.Asymptotics.IsBigOq f n) :
    Bound (fun τ _ => f τ) n := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, 1, 0, hC, zero_le_one, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h0 := hb τ (Work.Asymptotics.Funnel.im_one hF)
  have hs1 : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hq0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ n := pow_nonneg (norm_nonneg _) _
  have h2 := mul_le_mul_of_nonneg_left hs1 (mul_nonneg hC.le hq0)
  have h1 : C * ‖Work.Kernels.qParamFun τ‖ ^ n
      ≤ C * Work.Kernels.scale τ * ‖Work.Kernels.qParamFun τ‖ ^ n := by linarith [h2]
  refine le_trans h0 ?_
  simpa [Real.rpow_zero, Real.rpow_one, pow_zero, mul_one, one_mul] using h1

theorem Bound.coe_tau : Bound (fun τ _ => (τ : ℂ)) 0 := by
  refine ⟨1, 1, 0, one_pos, zero_le_one, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  simpa [Real.rpow_zero, Real.rpow_one, pow_zero, mul_one, one_mul]
    using Work.Kernels.coe_norm_le_scale τ

theorem Bound.coe_z : Bound (fun _ z => (z : ℂ)) 0 := by
  refine ⟨1, 0, 1, one_pos, le_rfl, zero_le_one, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  simpa [Real.rpow_zero, Real.rpow_one, pow_zero, mul_one, one_mul]
    using norm_coe_z_le hF ht hz0 hz1 hzim

theorem Bound.S0z : Bound (fun _ z => S0z z) 0 := by
  refine ⟨2, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  simpa [Real.rpow_zero, Real.rpow_one, pow_zero, mul_one, one_mul]
    using norm_S0z_le hF ht hzim

theorem Bound.qParamFun : Bound (fun τ _ => Work.Kernels.qParamFun τ) 1 := by
  refine ⟨1, 0, 0, one_pos, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  simp [Real.rpow_zero, Real.rpow_one, pow_zero, mul_one, one_mul]

theorem Bound.qParamFun_sq : Bound (fun τ _ => Work.Kernels.qParamFun τ ^ 2) 2 :=
  Bound.congr (Bound.mul Bound.qParamFun Bound.qParamFun) (fun τ z => by ring)

theorem Bound.E4Fun : Bound (fun τ _ => Work.Kernels.E4Fun τ) 0 :=
  Bound.of_isBigOq Work.Asymptotics.E4Fun_bdd

theorem Bound.E6Fun : Bound (fun τ _ => Work.Kernels.E6Fun τ) 0 :=
  Bound.of_isBigOq Work.Asymptotics.E6Fun_bdd

theorem Bound.E2Fun : Bound (fun τ _ => Work.Kernels.E2Fun τ) 0 :=
  Bound.of_isBigOq Work.Asymptotics.E2Fun_bdd

theorem Bound.DeltaFun : Bound (fun τ _ => Work.Kernels.DeltaFun τ) 1 :=
  Bound.of_isBigOq Work.Asymptotics.DeltaFun_isBigOq_one

theorem Bound.devE4 : Bound (fun τ _ => Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ) 2 :=
  Bound.of_isBigOq Work.Asymptotics.E4Fun_isBigOq

theorem Bound.devE6 : Bound (fun τ _ => Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ) 2 :=
  Bound.of_isBigOq Work.Asymptotics.E6Fun_isBigOq

theorem Bound.devE2 : Bound (fun τ _ => Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ) 2 :=
  Bound.of_isBigOq Work.Asymptotics.E2Fun_isBigOq

theorem Bound.devDelta : Bound (fun τ _ => Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ) 2 :=
  Bound.of_isBigOq Work.Asymptotics.DeltaFun_isBigOq

theorem Bound.cuspC (ℓ : Work.Kernels.LogLambdaData) :
    Bound (fun _ _ => Work.Asymptotics.Compact.cuspC ℓ) 0 := Bound.const _

theorem Bound.piC : Bound (fun _ _ => (Real.pi : ℂ)) 0 := Bound.const _

theorem Bound.piInvC : Bound (fun _ _ => ((Real.pi : ℂ))⁻¹) 0 := Bound.const _

theorem Bound.cuspLin (ℓ : Work.Kernels.LogLambdaData) :
    Bound (fun τ _ => Work.Asymptotics.KhatE1Core.cuspLin ℓ τ) 0 := by
  have hc : Work.Asymptotics.Compact.cuspC ℓ = 4 * (Real.log 2 : ℂ) := Work.Asymptotics.CuspL_eq ℓ
  refine ⟨Real.pi + 4, 1, 0, by positivity, zero_le_one, le_rfl,
    fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hlog : ‖(4 : ℂ) * (Real.log 2 : ℂ)‖ ≤ 4 := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
    linarith
  have hπ : ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ)‖ ≤ Real.pi * Work.Kernels.scale τ := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    have h := Work.Kernels.coe_norm_le_scale τ
    nlinarith [Real.pi_pos]
  have hgoal : ‖Work.Asymptotics.KhatE1Core.cuspLin ℓ τ‖
      ≤ (Real.pi + 4) * Work.Kernels.scale τ := by
    rw [Work.Asymptotics.KhatE1Core.cuspLin, hc]
    calc ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ) + 4 * (Real.log 2 : ℂ)‖
        ≤ ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ)‖ + ‖(4 : ℂ) * (Real.log 2 : ℂ)‖ := norm_add_le _ _
      _ ≤ Real.pi * Work.Kernels.scale τ + 4 := add_le_add hπ hlog
      _ ≤ (Real.pi + 4) * Work.Kernels.scale τ := by
          have := Work.Kernels.one_le_scale τ
          nlinarith
  simpa [Real.rpow_zero, Real.rpow_one, pow_zero, mul_one, one_mul] using hgoal

/-! ## The truncation deviations -/

/-- `A - A₀` with `A₀ = 1 + 240q`. -/
def devA (τ : UpperHalfPlane) : ℂ := Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ

/-- `B - B₀` with `B₀ = 1 - 504q`. -/
def devB (τ : UpperHalfPlane) : ℂ := Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ

/-- `E₂ - E₂₀` with `E₂₀ = 1 - 24q`. -/
def devE (τ : UpperHalfPlane) : ℂ := Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ

/-- `Δ - q`. -/
def devD (τ : UpperHalfPlane) : ℂ := Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ

/-- `ψ₂ - (2Λ + (48Λ+408)q)`. -/
def devPsi2 (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  Work.Kernels.psi2 ℓ τ - (2 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ
    + (48 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ + 408) * Work.Kernels.qParamFun τ)

/-- `ψ₄ - (2Λ - (288Λ+744)q)`. -/
def devPsi4 (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  Work.Kernels.psi4 ℓ τ - (2 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ
    - (288 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ + 744) * Work.Kernels.qParamFun τ)

theorem Bound.devA : Bound (fun τ _ => devA τ) 2 := Bound.devE4

theorem Bound.devB : Bound (fun τ _ => devB τ) 2 := Bound.devE6

theorem Bound.devE : Bound (fun τ _ => devE τ) 2 := Bound.devE2

theorem Bound.devD : Bound (fun τ _ => devD τ) 2 := Bound.devDelta

theorem Bound.devPsi2 (ℓ : Work.Kernels.LogLambdaData) : Bound (fun τ _ => devPsi2 ℓ τ) 2 := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.KhatE1Core.psi_second_order ℓ
  have hrem : Bound (fun τ _ => Work.Kernels.psi2 ℓ τ
      - 2 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ
      - (48 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ + 408) * Work.Kernels.qParamFun τ
      - (48 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ + 2636)
        * Work.Kernels.qParamFun τ ^ 2) 2 := by
    refine ⟨C, N, 0, hC, hN, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
    have h1 := (h τ hF).1
    have hq := norm_qParamFun_le_one' hF
    have h3 : ‖Work.Kernels.qParamFun τ‖ ^ 3 ≤ ‖Work.Kernels.qParamFun τ‖ ^ 2 :=
      pow_le_pow_of_le_one (norm_nonneg _) hq (by norm_num)
    have hsc : (0:ℝ) ≤ C * Work.Kernels.scale τ ^ N :=
      mul_nonneg hC.le (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le _)
    have h4 : C * Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 3
        ≤ C * Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h3 hsc
    refine le_trans h1 ?_
    simpa [Real.rpow_zero, pow_zero, mul_one, one_mul] using h4
  have htail : Bound (fun τ _ => (48 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ + 2636)
      * Work.Kernels.qParamFun τ ^ 2) 2 := by
    have h1 : Bound (fun τ _ => 48 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ
        * Work.Kernels.qParamFun τ ^ 2) 2 :=
      Bound.congr (Bound.mul ((Bound.cuspLin ℓ).const_mul 48) Bound.qParamFun_sq)
        (fun τ z => by ring)
    have h2 : Bound (fun τ _ => (2636:ℂ) * Work.Kernels.qParamFun τ ^ 2) 2 :=
      Bound.congr (Bound.qParamFun_sq.const_mul 2636) (fun τ z => by ring)
    refine Bound.congr (h1.add h2) (fun τ z => ?_)
    ring
  refine Bound.congr (hrem.add htail) (fun τ z => ?_)
  show Work.Kernels.psi2 ℓ τ - 2 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ
      - (48 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ + 408) * Work.Kernels.qParamFun τ
      - (48 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2
      + (48 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2
    = Work.Asymptotics.KhatE1.devPsi2 ℓ τ
  simp only [Work.Asymptotics.KhatE1.devPsi2]; ring

theorem Bound.devPsi4 (ℓ : Work.Kernels.LogLambdaData) : Bound (fun τ _ => devPsi4 ℓ τ) 2 := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.KhatE1Core.psi_second_order ℓ
  have hrem : Bound (fun τ _ => Work.Kernels.psi4 ℓ τ
      - 2 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ
      + (288 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ + 744) * Work.Kernels.qParamFun τ
      + (1824 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ + 25972)
        * Work.Kernels.qParamFun τ ^ 2) 2 := by
    refine ⟨C, N, 0, hC, hN, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
    have h1 := (h τ hF).2
    have hq := norm_qParamFun_le_one' hF
    have h3 : ‖Work.Kernels.qParamFun τ‖ ^ 3 ≤ ‖Work.Kernels.qParamFun τ‖ ^ 2 :=
      pow_le_pow_of_le_one (norm_nonneg _) hq (by norm_num)
    have hsc : (0:ℝ) ≤ C * Work.Kernels.scale τ ^ N :=
      mul_nonneg hC.le (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le _)
    have h4 : C * Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 3
        ≤ C * Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h3 hsc
    refine le_trans h1 ?_
    simpa [Real.rpow_zero, pow_zero, mul_one, one_mul] using h4
  have htail : Bound (fun τ _ => -(1824 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ + 25972)
      * Work.Kernels.qParamFun τ ^ 2) 2 := by
    have h1 : Bound (fun τ _ => -(1824 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ)
        * Work.Kernels.qParamFun τ ^ 2) 2 :=
      Bound.congr (Bound.mul ((Bound.cuspLin ℓ).const_mul (-1824)) Bound.qParamFun_sq)
        (fun τ z => by ring)
    have h2 : Bound (fun τ _ => -(25972:ℂ) * Work.Kernels.qParamFun τ ^ 2) 2 :=
      Bound.congr (Bound.qParamFun_sq.const_mul (-25972)) (fun τ z => by ring)
    refine Bound.congr (h1.add h2) (fun τ z => ?_)
    ring
  refine Bound.congr (hrem.add htail) (fun τ z => ?_)
  show Work.Kernels.psi4 ℓ τ - 2 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ
      + (288 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ + 744) * Work.Kernels.qParamFun τ
      + (1824 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2
      + -(1824 * Work.Asymptotics.KhatE1Core.cuspLin ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2
    = Work.Asymptotics.KhatE1.devPsi4 ℓ τ
  simp only [Work.Asymptotics.KhatE1.devPsi4]; ring

theorem BoundW.pow {f : UpperHalfPlane → UpperHalfPlane → ℂ} {n : ℕ} {C N M : ℝ}
    (hf : BoundW f n C N M) (k : ℕ) :
    BoundW (fun τ z => f τ z ^ k) (n * k) ((C + 1) ^ k) (N * k) (M * k) := by
  induction k with
  | zero =>
      refine ⟨one_pos, by simp, by simp, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
      have hs : Work.Kernels.scale τ ^ (N * ((0:ℕ):ℝ)) = 1 := by
        rw [Nat.cast_zero, mul_zero, Real.rpow_zero]
      have ht : (1 + t) ^ (M * ((0:ℕ):ℝ)) = 1 := by
        rw [Nat.cast_zero, mul_zero, Real.rpow_zero]
      have hq : ‖Work.Kernels.qParamFun τ‖ ^ (n * 0) = 1 := by rw [Nat.mul_zero, pow_zero]
      rw [pow_zero, hs, ht, hq]
      simp
  | succ k ih =>
      have hmul := ih.mul hf
      have he : n * k + n = n * (k + 1) := by ring
      have hN : (N * (k:ℝ) + N) = N * ((k + 1 : ℕ) : ℝ) := by push_cast; ring
      have hM : (M * (k:ℝ) + M) = M * ((k + 1 : ℕ) : ℝ) := by push_cast; ring
      refine BoundW.mono (le_of_eq he) ?_ (le_of_eq hN) (le_of_eq hM) hmul
      have h0 : (0:ℝ) < C + 1 := by linarith [hf.1]
      have h1 : (0:ℝ) ≤ (C + 1) ^ k := by positivity
      have h2 : (C + 1) ^ k * (C + 1) = (C + 1) ^ (k+1) := by rw [pow_succ]
      have h3 : (C + 1) ^ k * C ≤ (C + 1) ^ k * (C + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) h1
      nlinarith [h3, h2, h1]

theorem Bound.pow {f : UpperHalfPlane → UpperHalfPlane → ℂ} {n : ℕ} (hf : Bound f n) (k : ℕ) :
    Bound (fun τ z => f τ z ^ k) (n * k) := by
  obtain ⟨C, N, M, hf⟩ := hf
  exact ⟨_, _, _, hf.pow k⟩

theorem Bound.qParamFun_pow (k : ℕ) :
    Bound (fun τ _ => Work.Kernels.qParamFun τ ^ k) k := by
  have h := (Bound.qParamFun).pow k
  rw [Nat.one_mul] at h
  exact h

theorem Bound.cuspLin_pow (ℓ : Work.Kernels.LogLambdaData) (k : ℕ) :
    Bound (fun τ _ => (Work.Asymptotics.KhatE1Core.cuspLin ℓ τ) ^ k) 0 := by
  have h := (Bound.cuspLin ℓ).pow k
  rw [Nat.zero_mul] at h
  exact h

theorem Bound.coe_z_pow (k : ℕ) : Bound (fun _ z => (z : ℂ) ^ k) 0 := by
  have h := (Bound.coe_z).pow k
  rw [Nat.zero_mul] at h
  exact h

theorem Bound.coe_tau_pow (k : ℕ) : Bound (fun τ _ => (τ : ℂ) ^ k) 0 := by
  have h := (Bound.coe_tau).pow k
  rw [Nat.zero_mul] at h
  exact h

theorem Bound.cuspC_pow (ℓ : Work.Kernels.LogLambdaData) (k : ℕ) :
    Bound (fun _ _ => (Work.Asymptotics.Compact.cuspC ℓ) ^ k) 0 := by
  have h := (Bound.cuspC ℓ).pow k
  rw [Nat.zero_mul] at h
  exact h

theorem Bound.piC_pow (k : ℕ) : Bound (fun _ _ => (Real.pi : ℂ) ^ k) 0 := by
  have h := (Bound.piC).pow k
  rw [Nat.zero_mul] at h
  exact h

theorem Bound.piInvC_pow (k : ℕ) : Bound (fun _ _ => ((Real.pi : ℂ))⁻¹ ^ k) 0 := by
  have h := (Bound.piInvC).pow k
  rw [Nat.zero_mul] at h
  exact h


/-- **Generic monomial bound.**  Any product of a constant, powers of `q`, `cuspLin ℓ`, `τ`,
`z`, `π` and `cuspC ℓ` is `O(1)` on the funnel strip. -/
theorem Bound.monomial (ℓ : Work.Kernels.LogLambdaData) (c : ℂ) (a b d e f g : ℕ) :
    Bound (fun τ z => c * (Work.Kernels.qParamFun τ) ^ a
      * (Work.Asymptotics.KhatE1Core.cuspLin ℓ τ) ^ b * ((τ : ℂ) ^ d) * ((z : ℂ) ^ e)
      * ((Real.pi : ℂ) ^ f) * (Work.Asymptotics.Compact.cuspC ℓ) ^ g) 0 := by
  have h : Bound (fun τ z => c * (Work.Kernels.qParamFun τ) ^ a
      * (Work.Asymptotics.KhatE1Core.cuspLin ℓ τ) ^ b * ((τ : ℂ) ^ d) * ((z : ℂ) ^ e)
      * ((Real.pi : ℂ) ^ f) * (Work.Asymptotics.Compact.cuspC ℓ) ^ g)
      (0 + a + 0 + 0 + 0 + 0) :=
    ((((((Bound.const c).mul (Bound.qParamFun_pow a)).mul (Bound.cuspLin_pow ℓ b)).mul
      (Bound.coe_tau_pow d)).mul (Bound.coe_z_pow e)).mul (Bound.piC_pow f)).mul
      (Bound.cuspC_pow ℓ g)
  refine Bound.congr (Bound.mono (Nat.zero_le _) h) (fun τ z => by ring)

end Atoms


/-! ## The `J`-part and the `J`-free part of `Bracket24E2` -/

/-- `Sh Z π = 1 - 6i/(πZ)` (the value of `S0z` at `Z`). -/
def ShZ (Z pi : ℂ) : ℂ := 1 - 6 * Complex.I / (pi * Z)

theorem Bound.ShZ (k : ℕ) : Bound (fun _ z => (ShZ (z : ℂ) (Real.pi : ℂ)) ^ k) 0 := by
  have h := Bound.congr (Bound.S0z.pow k) (fun τ z => by first | rfl | simp only [ShZ, S0z])
  rw [Nat.zero_mul] at h
  exact h


/-- `A₀ = 1 + 240q`. -/
def A0q (q : ℂ) : ℂ := 1 + 240 * q

/-- `B₀ = 1 - 504q`. -/
def B0q (q : ℂ) : ℂ := 1 - 504 * q

/-- `E₂₀ = 1 - 24q`. -/
def E20q (q : ℂ) : ℂ := 1 - 24 * q

/-- `ψ₂`-truncation `2Λ + (48Λ+408)q`. -/
def P20q (q L : ℂ) : ℂ := 2 * L + (48 * L + 408) * q

/-- `ψ₄`-truncation `2Λ - (288Λ+744)q`. -/
def P40q (q L : ℂ) : ℂ := 2 * L - (288 * L + 744) * q

/-- The coefficient `κ` of `J` in `Bracket24E2 = J·κ + ρ`. -/
def Kappa (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
    (1/3 : ℂ) * ((Real.pi : ℂ))⁻¹ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.psi2 ℓ τ
    + (1/6 : ℂ) * ((Real.pi : ℂ))⁻¹ * (Work.Kernels.E4Fun τ)^2 * Work.Kernels.psi4 ℓ τ
    + (1/36 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * Complex.I * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * (Work.Kernels.E2Fun τ)^2 * (τ : ℂ)
    + (1/6 : ℂ) * ((Real.pi : ℂ)) * (z : ℂ)^2 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ
    - (1/18 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * S0z z * Complex.I * (Work.Kernels.E4Fun τ)^3 * Work.Kernels.E2Fun τ * (τ : ℂ)
    - (1/6 : ℂ) * ((Real.pi : ℂ)) * (z : ℂ)^2 * S0z z * (Work.Kernels.E4Fun τ)^3
    + (1/36 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * (S0z z)^2 * Complex.I * (Work.Kernels.E4Fun τ)^2 * Work.Kernels.E6Fun τ * (τ : ℂ)
    - ((Real.pi : ℂ))⁻¹ * Work.Asymptotics.Compact.cuspC ℓ * (Work.Kernels.E4Fun τ)^3
    - (z : ℂ) * Complex.I * (Work.Kernels.E4Fun τ)^3

/-- The `J`-free part `ρ` of `Bracket24E2 = J·κ + ρ`. -/
def Rest (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
    9558 * ((Real.pi : ℂ))⁻¹ * Work.Kernels.DeltaFun τ
    - 142236 * ((Real.pi : ℂ))⁻¹ * Work.Asymptotics.Compact.cuspC ℓ * Work.Kernels.DeltaFun τ
    - (4719/32 : ℂ) * ((Real.pi : ℂ))⁻¹ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.psi2 ℓ τ
    - (6417/32 : ℂ) * ((Real.pi : ℂ))⁻¹ * (Work.Kernels.E4Fun τ)^2 * Work.Kernels.psi4 ℓ τ
    - 12 * ((Real.pi : ℂ))⁻¹ * (Work.Kernels.E4Fun τ)^3
    + 1464 * ((Real.pi : ℂ))⁻¹ * Work.Asymptotics.Compact.cuspC ℓ * (Work.Kernels.E4Fun τ)^3
    - 142236 * (z : ℂ) * Complex.I * Work.Kernels.DeltaFun τ
    + 1464 * (z : ℂ) * Complex.I * (Work.Kernels.E4Fun τ)^3
    + (71/48 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * Complex.I * Work.Kernels.E2Fun τ * (Work.Kernels.E4Fun τ)^3 * (τ : ℂ)
    + (71/16 : ℂ) * ((Real.pi : ℂ)) * (z : ℂ)^2 * (Work.Kernels.E4Fun τ)^3
    - (71/96 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * Complex.I * (Work.Kernels.E4Fun τ)^2 * Work.Kernels.E6Fun τ * (τ : ℂ)
    - (1351/96 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * Complex.I * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * (Work.Kernels.E2Fun τ)^2 * (τ : ℂ)
    - (1351/16 : ℂ) * ((Real.pi : ℂ)) * (z : ℂ)^2 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ
    - 1989 * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * Complex.I * Work.Kernels.E2Fun τ * Work.Kernels.DeltaFun τ * (τ : ℂ)
    - 5967 * ((Real.pi : ℂ)) * (z : ℂ)^2 * Work.Kernels.DeltaFun τ
    + (4/3 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * Complex.I * (Work.Kernels.E4Fun τ)^3 * Work.Kernels.E2Fun τ * (τ : ℂ)
    + 4 * ((Real.pi : ℂ)) * (z : ℂ)^2 * (Work.Kernels.E4Fun τ)^3
    + (1/4 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * S0z z * Complex.I * Work.Kernels.E2Fun τ * (Work.Kernels.E4Fun τ)^3 * (τ : ℂ)
    + (3/4 : ℂ) * ((Real.pi : ℂ)) * (z : ℂ)^2 * S0z z * (Work.Kernels.E4Fun τ)^3
    - (35/24 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * S0z z * Complex.I * (Work.Kernels.E4Fun τ)^2 * Work.Kernels.E6Fun τ * (τ : ℂ)
    - (1/8 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * S0z z * Complex.I * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * (Work.Kernels.E2Fun τ)^2 * (τ : ℂ)
    - (3/4 : ℂ) * ((Real.pi : ℂ)) * (z : ℂ)^2 * S0z z * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ
    - 8154 * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * S0z z * Complex.I * Work.Kernels.E2Fun τ * Work.Kernels.DeltaFun τ * (τ : ℂ)
    - 24462 * ((Real.pi : ℂ)) * (z : ℂ)^2 * S0z z * Work.Kernels.DeltaFun τ
    + (244/3 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * S0z z * Complex.I * (Work.Kernels.E4Fun τ)^3 * Work.Kernels.E2Fun τ * (τ : ℂ)
    + 244 * ((Real.pi : ℂ)) * (z : ℂ)^2 * S0z z * (Work.Kernels.E4Fun τ)^3
    - (1/16 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * (S0z z)^2 * Complex.I * Work.Kernels.E2Fun τ * (Work.Kernels.E4Fun τ)^3 * (τ : ℂ)
    - (3/16 : ℂ) * ((Real.pi : ℂ)) * (z : ℂ)^2 * (S0z z)^2 * (Work.Kernels.E4Fun τ)^3
    - (639/32 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * (S0z z)^2 * Complex.I * (Work.Kernels.E4Fun τ)^2 * Work.Kernels.E6Fun τ * (τ : ℂ)
    + (1/32 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * (S0z z)^2 * Complex.I * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * (Work.Kernels.E2Fun τ)^2 * (τ : ℂ)
    + (3/16 : ℂ) * ((Real.pi : ℂ)) * (z : ℂ)^2 * (S0z z)^2 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ
    + 63 * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * (S0z z)^2 * Complex.I * Work.Kernels.E2Fun τ * Work.Kernels.DeltaFun τ * (τ : ℂ)
    + 189 * ((Real.pi : ℂ)) * (z : ℂ)^2 * (S0z z)^2 * Work.Kernels.DeltaFun τ

/-- **The split of `Bracket24E2` into its `J`-part and its `J`-free part.** -/
theorem Bracket24E2_eq_Kappa_Rest (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) :
    Bracket24E2 ℓ τ z = Work.Kernels.jInvariantFun τ * Kappa ℓ τ z + Rest ℓ τ z := by
  have hD : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have h : Work.Kernels.DeltaFun τ ^ 2 * Bracket24E2 ℓ τ z
      = Work.Kernels.DeltaFun τ ^ 2
          * (Work.Kernels.jInvariantFun τ * Kappa ℓ τ z + Rest ℓ τ z) := by
    simp only [Bracket24E2, Kappa, Rest, Work.Kernels.jInvariantFun]
    field_simp
    ring
  exact mul_left_cancel₀ (pow_ne_zero 2 hD) h

/-- `(πz)²·κ`, cleared of divisions. -/
def KappaP (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
    (1/3 : ℂ) * ((Real.pi : ℂ)) * (z : ℂ)^2 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.psi2 ℓ τ
    + (1/6 : ℂ) * ((Real.pi : ℂ)) * (z : ℂ)^2 * (Work.Kernels.E4Fun τ)^2 * Work.Kernels.psi4 ℓ τ
    + (1/36 : ℂ) * ((Real.pi : ℂ))^4 * (z : ℂ)^4 * Complex.I * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * (Work.Kernels.E2Fun τ)^2 * (τ : ℂ)
    + (1/6 : ℂ) * ((Real.pi : ℂ))^3 * (z : ℂ)^4 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ
    - (1/18 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * (((Real.pi : ℂ))^2 * (z : ℂ)^2 - 6 * Complex.I * ((Real.pi : ℂ)) * (z : ℂ)) * Complex.I * (Work.Kernels.E4Fun τ)^3 * Work.Kernels.E2Fun τ * (τ : ℂ)
    - (1/6 : ℂ) * ((Real.pi : ℂ))^1 * (z : ℂ)^2 * (((Real.pi : ℂ))^2 * (z : ℂ)^2 - 6 * Complex.I * ((Real.pi : ℂ)) * (z : ℂ)) * (Work.Kernels.E4Fun τ)^3
    + (1/36 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * (((Real.pi : ℂ)) * (z : ℂ) - 6 * Complex.I)^2 * Complex.I * (Work.Kernels.E4Fun τ)^2 * Work.Kernels.E6Fun τ * (τ : ℂ)
    - ((Real.pi : ℂ)) * (z : ℂ)^2 * Work.Asymptotics.Compact.cuspC ℓ * (Work.Kernels.E4Fun τ)^3
    - ((Real.pi : ℂ))^2 * (z : ℂ)^3 * Complex.I * (Work.Kernels.E4Fun τ)^3

/-- `(πz)²·ρ`, cleared of divisions. -/
def RestP (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
    9558 * ((Real.pi : ℂ)) * (z : ℂ)^2 * Work.Kernels.DeltaFun τ
    - 142236 * ((Real.pi : ℂ)) * (z : ℂ)^2 * Work.Asymptotics.Compact.cuspC ℓ * Work.Kernels.DeltaFun τ
    - (4719/32 : ℂ) * ((Real.pi : ℂ)) * (z : ℂ)^2 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.psi2 ℓ τ
    - (6417/32 : ℂ) * ((Real.pi : ℂ)) * (z : ℂ)^2 * (Work.Kernels.E4Fun τ)^2 * Work.Kernels.psi4 ℓ τ
    - 12 * ((Real.pi : ℂ)) * (z : ℂ)^2 * (Work.Kernels.E4Fun τ)^3
    + 1464 * ((Real.pi : ℂ)) * (z : ℂ)^2 * Work.Asymptotics.Compact.cuspC ℓ * (Work.Kernels.E4Fun τ)^3
    - 142236 * ((Real.pi : ℂ))^2 * (z : ℂ)^3 * Complex.I * Work.Kernels.DeltaFun τ
    + 1464 * ((Real.pi : ℂ))^2 * (z : ℂ)^3 * Complex.I * (Work.Kernels.E4Fun τ)^3
    + (71/48 : ℂ) * ((Real.pi : ℂ))^4 * (z : ℂ)^4 * Complex.I * Work.Kernels.E2Fun τ * (Work.Kernels.E4Fun τ)^3 * (τ : ℂ)
    + (71/16 : ℂ) * ((Real.pi : ℂ))^3 * (z : ℂ)^4 * (Work.Kernels.E4Fun τ)^3
    - (71/96 : ℂ) * ((Real.pi : ℂ))^4 * (z : ℂ)^4 * Complex.I * (Work.Kernels.E4Fun τ)^2 * Work.Kernels.E6Fun τ * (τ : ℂ)
    - (1351/96 : ℂ) * ((Real.pi : ℂ))^4 * (z : ℂ)^4 * Complex.I * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * (Work.Kernels.E2Fun τ)^2 * (τ : ℂ)
    - (1351/16 : ℂ) * ((Real.pi : ℂ))^3 * (z : ℂ)^4 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ
    - 1989 * ((Real.pi : ℂ))^4 * (z : ℂ)^4 * Complex.I * Work.Kernels.E2Fun τ * Work.Kernels.DeltaFun τ * (τ : ℂ)
    - 5967 * ((Real.pi : ℂ))^3 * (z : ℂ)^4 * Work.Kernels.DeltaFun τ
    + (4/3 : ℂ) * ((Real.pi : ℂ))^4 * (z : ℂ)^4 * Complex.I * (Work.Kernels.E4Fun τ)^3 * Work.Kernels.E2Fun τ * (τ : ℂ)
    + 4 * ((Real.pi : ℂ))^3 * (z : ℂ)^4 * (Work.Kernels.E4Fun τ)^3
    + (1/4 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * (((Real.pi : ℂ))^2 * (z : ℂ)^2 - 6 * Complex.I * ((Real.pi : ℂ)) * (z : ℂ)) * Complex.I * Work.Kernels.E2Fun τ * (Work.Kernels.E4Fun τ)^3 * (τ : ℂ)
    + (3/4 : ℂ) * ((Real.pi : ℂ))^1 * (z : ℂ)^2 * (((Real.pi : ℂ))^2 * (z : ℂ)^2 - 6 * Complex.I * ((Real.pi : ℂ)) * (z : ℂ)) * (Work.Kernels.E4Fun τ)^3
    - (35/24 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * (((Real.pi : ℂ))^2 * (z : ℂ)^2 - 6 * Complex.I * ((Real.pi : ℂ)) * (z : ℂ)) * Complex.I * (Work.Kernels.E4Fun τ)^2 * Work.Kernels.E6Fun τ * (τ : ℂ)
    - (1/8 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * (((Real.pi : ℂ))^2 * (z : ℂ)^2 - 6 * Complex.I * ((Real.pi : ℂ)) * (z : ℂ)) * Complex.I * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * (Work.Kernels.E2Fun τ)^2 * (τ : ℂ)
    - (3/4 : ℂ) * ((Real.pi : ℂ))^1 * (z : ℂ)^2 * (((Real.pi : ℂ))^2 * (z : ℂ)^2 - 6 * Complex.I * ((Real.pi : ℂ)) * (z : ℂ)) * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ
    - 8154 * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * (((Real.pi : ℂ))^2 * (z : ℂ)^2 - 6 * Complex.I * ((Real.pi : ℂ)) * (z : ℂ)) * Complex.I * Work.Kernels.E2Fun τ * Work.Kernels.DeltaFun τ * (τ : ℂ)
    - 24462 * ((Real.pi : ℂ))^1 * (z : ℂ)^2 * (((Real.pi : ℂ))^2 * (z : ℂ)^2 - 6 * Complex.I * ((Real.pi : ℂ)) * (z : ℂ)) * Work.Kernels.DeltaFun τ
    + (244/3 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * (((Real.pi : ℂ))^2 * (z : ℂ)^2 - 6 * Complex.I * ((Real.pi : ℂ)) * (z : ℂ)) * Complex.I * (Work.Kernels.E4Fun τ)^3 * Work.Kernels.E2Fun τ * (τ : ℂ)
    + 244 * ((Real.pi : ℂ))^1 * (z : ℂ)^2 * (((Real.pi : ℂ))^2 * (z : ℂ)^2 - 6 * Complex.I * ((Real.pi : ℂ)) * (z : ℂ)) * (Work.Kernels.E4Fun τ)^3
    - (1/16 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * (((Real.pi : ℂ)) * (z : ℂ) - 6 * Complex.I)^2 * Complex.I * Work.Kernels.E2Fun τ * (Work.Kernels.E4Fun τ)^3 * (τ : ℂ)
    - (3/16 : ℂ) * ((Real.pi : ℂ))^1 * (z : ℂ)^2 * (((Real.pi : ℂ)) * (z : ℂ) - 6 * Complex.I)^2 * (Work.Kernels.E4Fun τ)^3
    - (639/32 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * (((Real.pi : ℂ)) * (z : ℂ) - 6 * Complex.I)^2 * Complex.I * (Work.Kernels.E4Fun τ)^2 * Work.Kernels.E6Fun τ * (τ : ℂ)
    + (1/32 : ℂ) * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * (((Real.pi : ℂ)) * (z : ℂ) - 6 * Complex.I)^2 * Complex.I * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * (Work.Kernels.E2Fun τ)^2 * (τ : ℂ)
    + (3/16 : ℂ) * ((Real.pi : ℂ))^1 * (z : ℂ)^2 * (((Real.pi : ℂ)) * (z : ℂ) - 6 * Complex.I)^2 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ
    + 63 * ((Real.pi : ℂ))^2 * (z : ℂ)^2 * (((Real.pi : ℂ)) * (z : ℂ) - 6 * Complex.I)^2 * Complex.I * Work.Kernels.E2Fun τ * Work.Kernels.DeltaFun τ * (τ : ℂ)
    + 189 * ((Real.pi : ℂ))^1 * (z : ℂ)^2 * (((Real.pi : ℂ)) * (z : ℂ) - 6 * Complex.I)^2 * Work.Kernels.DeltaFun τ

/-- The truncated coefficient `κ̂` of `J`. -/
def KappaHat (q L tau Z C pi : ℂ) : ℂ :=
    (1/3 : ℂ) * pi⁻¹ * A0q q * B0q q * P20q q L
    + (1/6 : ℂ) * pi⁻¹ * (A0q q)^2 * P40q q L
    + (1/36 : ℂ) * pi^2 * Z^2 * Complex.I * A0q q * B0q q * (E20q q)^2 * tau
    + (1/6 : ℂ) * pi * Z^2 * A0q q * B0q q * E20q q
    - (1/18 : ℂ) * pi^2 * Z^2 * ShZ Z pi * Complex.I * (A0q q)^3 * E20q q * tau
    - (1/6 : ℂ) * pi * Z^2 * ShZ Z pi * (A0q q)^3
    + (1/36 : ℂ) * pi^2 * Z^2 * (ShZ Z pi)^2 * Complex.I * (A0q q)^2 * B0q q * tau
    - pi⁻¹ * C * (A0q q)^3
    - Z * Complex.I * (A0q q)^3

/-- The truncated `J`-free part `ρ̂`. -/
def RestHat (q L tau Z C pi : ℂ) : ℂ :=
    9558 * pi⁻¹ * q
    - 142236 * pi⁻¹ * C * q
    - (4719/32 : ℂ) * pi⁻¹ * A0q q * B0q q * P20q q L
    - (6417/32 : ℂ) * pi⁻¹ * (A0q q)^2 * P40q q L
    - 12 * pi⁻¹ * (A0q q)^3
    + 1464 * pi⁻¹ * C * (A0q q)^3
    - 142236 * Z * Complex.I * q
    + 1464 * Z * Complex.I * (A0q q)^3
    + (71/48 : ℂ) * pi^2 * Z^2 * Complex.I * E20q q * (A0q q)^3 * tau
    + (71/16 : ℂ) * pi * Z^2 * (A0q q)^3
    - (71/96 : ℂ) * pi^2 * Z^2 * Complex.I * (A0q q)^2 * B0q q * tau
    - (1351/96 : ℂ) * pi^2 * Z^2 * Complex.I * A0q q * B0q q * (E20q q)^2 * tau
    - (1351/16 : ℂ) * pi * Z^2 * A0q q * B0q q * E20q q
    - 1989 * pi^2 * Z^2 * Complex.I * E20q q * q * tau
    - 5967 * pi * Z^2 * q
    + (4/3 : ℂ) * pi^2 * Z^2 * Complex.I * (A0q q)^3 * E20q q * tau
    + 4 * pi * Z^2 * (A0q q)^3
    + (1/4 : ℂ) * pi^2 * Z^2 * ShZ Z pi * Complex.I * E20q q * (A0q q)^3 * tau
    + (3/4 : ℂ) * pi * Z^2 * ShZ Z pi * (A0q q)^3
    - (35/24 : ℂ) * pi^2 * Z^2 * ShZ Z pi * Complex.I * (A0q q)^2 * B0q q * tau
    - (1/8 : ℂ) * pi^2 * Z^2 * ShZ Z pi * Complex.I * A0q q * B0q q * (E20q q)^2 * tau
    - (3/4 : ℂ) * pi * Z^2 * ShZ Z pi * A0q q * B0q q * E20q q
    - 8154 * pi^2 * Z^2 * ShZ Z pi * Complex.I * E20q q * q * tau
    - 24462 * pi * Z^2 * ShZ Z pi * q
    + (244/3 : ℂ) * pi^2 * Z^2 * ShZ Z pi * Complex.I * (A0q q)^3 * E20q q * tau
    + 244 * pi * Z^2 * ShZ Z pi * (A0q q)^3
    - (1/16 : ℂ) * pi^2 * Z^2 * (ShZ Z pi)^2 * Complex.I * E20q q * (A0q q)^3 * tau
    - (3/16 : ℂ) * pi * Z^2 * (ShZ Z pi)^2 * (A0q q)^3
    - (639/32 : ℂ) * pi^2 * Z^2 * (ShZ Z pi)^2 * Complex.I * (A0q q)^2 * B0q q * tau
    + (1/32 : ℂ) * pi^2 * Z^2 * (ShZ Z pi)^2 * Complex.I * A0q q * B0q q * (E20q q)^2 * tau
    + (3/16 : ℂ) * pi * Z^2 * (ShZ Z pi)^2 * A0q q * B0q q * E20q q
    + 63 * pi^2 * Z^2 * (ShZ Z pi)^2 * Complex.I * E20q q * q * tau
    + 189 * pi * Z^2 * (ShZ Z pi)^2 * q

/-- `(πZ)²·κ̂`, cleared of divisions. -/
def KappaHatP (q L tau Z C pi : ℂ) : ℂ :=
    (1/3 : ℂ) * pi * Z^2 * A0q q * B0q q * P20q q L
    + (1/6 : ℂ) * pi * Z^2 * (A0q q)^2 * P40q q L
    + (1/36 : ℂ) * pi^4 * Z^4 * Complex.I * A0q q * B0q q * (E20q q)^2 * tau
    + (1/6 : ℂ) * pi^3 * Z^4 * A0q q * B0q q * E20q q
    - (1/18 : ℂ) * pi^2 * Z^2 * (pi^2 * Z^2 - 6 * Complex.I * pi * Z) * Complex.I * (A0q q)^3 * E20q q * tau
    - (1/6 : ℂ) * pi^1 * Z^2 * (pi^2 * Z^2 - 6 * Complex.I * pi * Z) * (A0q q)^3
    + (1/36 : ℂ) * pi^2 * Z^2 * (pi * Z - 6 * Complex.I)^2 * Complex.I * (A0q q)^2 * B0q q * tau
    - pi * Z^2 * C * (A0q q)^3
    - pi^2 * Z^3 * Complex.I * (A0q q)^3

/-- `(πZ)²·ρ̂`, cleared of divisions. -/
def RestHatP (q L tau Z C pi : ℂ) : ℂ :=
    9558 * pi * Z^2 * q
    - 142236 * pi * Z^2 * C * q
    - (4719/32 : ℂ) * pi * Z^2 * A0q q * B0q q * P20q q L
    - (6417/32 : ℂ) * pi * Z^2 * (A0q q)^2 * P40q q L
    - 12 * pi * Z^2 * (A0q q)^3
    + 1464 * pi * Z^2 * C * (A0q q)^3
    - 142236 * pi^2 * Z^3 * Complex.I * q
    + 1464 * pi^2 * Z^3 * Complex.I * (A0q q)^3
    + (71/48 : ℂ) * pi^4 * Z^4 * Complex.I * E20q q * (A0q q)^3 * tau
    + (71/16 : ℂ) * pi^3 * Z^4 * (A0q q)^3
    - (71/96 : ℂ) * pi^4 * Z^4 * Complex.I * (A0q q)^2 * B0q q * tau
    - (1351/96 : ℂ) * pi^4 * Z^4 * Complex.I * A0q q * B0q q * (E20q q)^2 * tau
    - (1351/16 : ℂ) * pi^3 * Z^4 * A0q q * B0q q * E20q q
    - 1989 * pi^4 * Z^4 * Complex.I * E20q q * q * tau
    - 5967 * pi^3 * Z^4 * q
    + (4/3 : ℂ) * pi^4 * Z^4 * Complex.I * (A0q q)^3 * E20q q * tau
    + 4 * pi^3 * Z^4 * (A0q q)^3
    + (1/4 : ℂ) * pi^2 * Z^2 * (pi^2 * Z^2 - 6 * Complex.I * pi * Z) * Complex.I * E20q q * (A0q q)^3 * tau
    + (3/4 : ℂ) * pi^1 * Z^2 * (pi^2 * Z^2 - 6 * Complex.I * pi * Z) * (A0q q)^3
    - (35/24 : ℂ) * pi^2 * Z^2 * (pi^2 * Z^2 - 6 * Complex.I * pi * Z) * Complex.I * (A0q q)^2 * B0q q * tau
    - (1/8 : ℂ) * pi^2 * Z^2 * (pi^2 * Z^2 - 6 * Complex.I * pi * Z) * Complex.I * A0q q * B0q q * (E20q q)^2 * tau
    - (3/4 : ℂ) * pi^1 * Z^2 * (pi^2 * Z^2 - 6 * Complex.I * pi * Z) * A0q q * B0q q * E20q q
    - 8154 * pi^2 * Z^2 * (pi^2 * Z^2 - 6 * Complex.I * pi * Z) * Complex.I * E20q q * q * tau
    - 24462 * pi^1 * Z^2 * (pi^2 * Z^2 - 6 * Complex.I * pi * Z) * q
    + (244/3 : ℂ) * pi^2 * Z^2 * (pi^2 * Z^2 - 6 * Complex.I * pi * Z) * Complex.I * (A0q q)^3 * E20q q * tau
    + 244 * pi^1 * Z^2 * (pi^2 * Z^2 - 6 * Complex.I * pi * Z) * (A0q q)^3
    - (1/16 : ℂ) * pi^2 * Z^2 * (pi * Z - 6 * Complex.I)^2 * Complex.I * E20q q * (A0q q)^3 * tau
    - (3/16 : ℂ) * pi^1 * Z^2 * (pi * Z - 6 * Complex.I)^2 * (A0q q)^3
    - (639/32 : ℂ) * pi^2 * Z^2 * (pi * Z - 6 * Complex.I)^2 * Complex.I * (A0q q)^2 * B0q q * tau
    + (1/32 : ℂ) * pi^2 * Z^2 * (pi * Z - 6 * Complex.I)^2 * Complex.I * A0q q * B0q q * (E20q q)^2 * tau
    + (3/16 : ℂ) * pi^1 * Z^2 * (pi * Z - 6 * Complex.I)^2 * A0q q * B0q q * E20q q
    + 63 * pi^2 * Z^2 * (pi * Z - 6 * Complex.I)^2 * Complex.I * E20q q * q * tau
    + 189 * pi^1 * Z^2 * (pi * Z - 6 * Complex.I)^2 * q


/-- `(πz)²·κ` really is the `(πz)²`-multiple of `κ`. -/
theorem KappaP_eq (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) (hZ : (z : ℂ) ≠ 0) :
    KappaP ℓ τ z = ((Real.pi : ℂ) * (z : ℂ))^2 * Kappa ℓ τ z := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [KappaP, Kappa, S0z]
  field_simp
  try ring

/-- `(πz)²·ρ` really is the `(πz)²`-multiple of `ρ`. -/
theorem RestP_eq (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) (hZ : (z : ℂ) ≠ 0) :
    RestP ℓ τ z = ((Real.pi : ℂ) * (z : ℂ))^2 * Rest ℓ τ z := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [RestP, Rest, S0z]
  field_simp
  try ring

/-- `(πZ)²·κ̂` really is the `(πZ)²`-multiple of `κ̂`. -/
theorem KappaHatP_eq (q L tau Z C pi : ℂ) (hZ : Z ≠ 0) (hpi : pi ≠ 0) :
    KappaHatP q L tau Z C pi = (pi * Z)^2 * KappaHat q L tau Z C pi := by
  simp only [KappaHatP, KappaHat, ShZ]
  field_simp
  try ring

/-- `(πZ)²·ρ̂` really is the `(πZ)²`-multiple of `ρ̂`. -/
theorem RestHatP_eq (q L tau Z C pi : ℂ) (hZ : Z ≠ 0) (hpi : pi ≠ 0) :
    RestHatP q L tau Z C pi = (pi * Z)^2 * RestHat q L tau Z C pi := by
  simp only [RestHatP, RestHat, ShZ]
  field_simp
  try ring

/-- `A₁ = (1 + 240q)³`. -/
def A1q (q : ℂ) : ℂ := (A0q q)^3

/-- The explicit polynomial `Π₂` with `A₁κ̂ + qρ̂ = q²Π₂/(πZ)²`. -/
def Poly2 (q tau Z C pi : ℂ) : ℂ :=
    6*Z^2*pi*(5568*C + 376*Complex.I*Z^2*pi^3*tau + 1256*Z^2*pi^2 + 2000*Z*pi^2*tau
        - 540*Complex.I*pi*tau + 527)
  + q * (6*Z^2*pi*(-7395606*C - 428944*Complex.I*Z^2*pi^3*tau - 1980000*Z^2*pi^2
        - 2158116*Z*pi^2*tau - 107784*Complex.I*Z*pi - 131058*Complex.I*pi*tau - 476709))
  + q^2 * (864*Z^2*pi*(-51760410*C - 3491800*Complex.I*Z^2*pi^3*tau - 10023200*Z^2*pi^2
        - 23303054*Z*pi^2*tau - 28440*Complex.I*Z*pi + 19719228*Complex.I*pi*tau - 20290515))
  + q^3 * (138240*Z^2*pi*(-49305600*C - 3268220*Complex.I*Z^2*pi^3*tau - 7065600*Z^2*pi^2
        - 28052811*Z*pi^2*tau + 39969567*Complex.I*pi*tau - 39033600))
  + q^4 * (10616832000*Z^2*pi*(-24120*C - 1277*Complex.I*Z^2*pi^3*tau - 2370*Z^2*pi^2
        - 15000*Z*pi^2*tau + 31680*Complex.I*pi*tau - 30720))
  + q^5 * (1274019840000*Z^3*pi^3*tau*(179*Complex.I*Z*pi + 1200))

/-- `Δ₂ = Π₂/(πZ)²`. -/
def Delta2 (q tau Z C pi : ℂ) : ℂ := Poly2 q tau Z C pi / (pi * Z)^2

/-- **The divisibility identity.**  `A₁κ̂ + qρ̂ = q²Δ₂`. -/
theorem kappahat_identity (q tau Z C pi : ℂ) :
    A1q q * KappaHatP q (pi * Complex.I * tau + C) tau Z C pi
        + q * RestHatP q (pi * Complex.I * tau + C) tau Z C pi
      = q^2 * Poly2 q tau Z C pi := by
  simp only [A1q, KappaHatP, RestHatP, Poly2, A0q, B0q, E20q, P20q, P40q, ShZ]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

end

end Work.Asymptotics.KhatE1
