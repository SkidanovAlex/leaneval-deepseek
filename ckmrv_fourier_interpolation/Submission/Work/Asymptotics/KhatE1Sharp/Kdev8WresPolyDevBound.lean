import Mathlib
import Submission.Work.Asymptotics.KhatE1Sharp.Kdev8WresTailGlue
import Submission.Work.Asymptotics.KhatE1Sharp.Kdev8WresHighTrunc
import Submission.Work.Asymptotics.KhatE1Sharp.Kdev8WresDeviationBounds
import Submission.Work.Asymptotics.KhatE1.cusp_L_fourth
import Submission.Work.Asymptotics.CuspL_eq
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.KhatE1.KdevA4Book

/-!
# The deviation bound for `WresPolyDevRem`

`WresPolyDevRem ℓ τ z = ((3456π)⁻¹ Δ(τ) Dev8Rem ℓ τ z)
  - tailC⁻¹ Δ(τ)² kdevNum0Rem τ z`

is the remainder of the polynomial/deviations split of the cleared `d = 8` residual
(`KhatE1.Kdev8WresTailGlue`).  This file proves that it satisfies the target funnel bound

`‖WresPolyDevRem ℓ τ z‖ ≤ C ‖q(τ)‖³ ‖Ept z‖² (scale τ)^N (1+t)^M`.

The proof is an explicit `O(·)` calculus on the funnel: every `z`-atom is bounded on
`{1 ≤ Im z}` (the remainders `rW, rD2, rE8, rE10, rE6, rL` by `O(‖Ept z‖⁶)` resp.
`O(‖Ept z‖⁵)`, the reference atoms and their polynomial corrections by constants), and every
`τ`-atom by `(scale τ)^N`.  The `q`/`Ept` exponent bookkeeping is the trade
`‖q(τ)‖^e‖Ept z‖^k ≤ ‖q(τ)‖³‖Ept z‖²` valid as soon as `k ≥ 2` and `2e + k ≥ 8`.
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-! ## The bound calculus `FunnelBnd` -/

/-- `FunnelBnd e k F` means: on the funnel strip (`Funnel τ`, `τ.im + 1 ≤ t`, `-1 ≤ z.re ≤ 2`,
`z.im = t`),

  `‖F τ z‖ ≤ C · ‖q(τ)‖^e · ‖Ept z‖^k · (scale τ)^N · (1+t)^M`.

Since `‖q(τ)‖ ≤ 1` and `‖Ept z‖ ≤ 1` on the strip, larger exponents are stronger. -/
def FunnelBnd (e k : ℕ) (F : ℍ → ℍ → ℂ) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t → -1 ≤ z.re → z.re ≤ 2 →
      z.im = t → ‖F τ z‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ e
        * ‖Work.Residues.Ept z‖ ^ k * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M

private lemma scale_nonneg (τ : ℍ) (N : ℝ) : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N :=
  Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N

private lemma one_le_one_add {τ : ℍ} {t : ℝ} (hτ : Work.Asymptotics.Funnel τ)
    (ht : τ.im + 1 ≤ t) : (1 : ℝ) ≤ 1 + t := by
  have := hτ.2; linarith

private lemma qnorm_le_one {τ : ℍ} (hτ : Work.Asymptotics.Funnel τ) :
    ‖Work.Kernels.qParamFun τ‖ ≤ 1 := by
  rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
  nlinarith [Real.pi_pos, hτ.2]

/-- `‖Ept z‖ ≤ 1`. -/
private lemma Ept_le_one (z : ℍ) : ‖Work.Residues.Ept z‖ ≤ 1 :=
  le_of_lt (Work.Residues.norm_Ept_lt_one z)

private lemma bnd_ept_pow_nonneg (z : ℍ) (k : ℕ) : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ ^ k :=
  pow_nonneg (norm_nonneg _) k

private lemma bnd_qpow_nonneg (τ : ℍ) (e : ℕ) : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ e :=
  pow_nonneg (norm_nonneg _) e

private lemma bnd_tpow_nonneg {t : ℝ} (ht : (1 : ℝ) ≤ 1 + t) (M : ℝ) : (0 : ℝ) ≤ (1 + t) ^ M :=
  Real.rpow_nonneg (le_trans zero_le_one ht) M

/-- Product monotonicity for four factors. -/
private lemma prod4_le {a a' b b' c c' d d' : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hc' : 0 ≤ c') (hd' : 0 ≤ d')
    (h1 : a ≤ a') (h2 : b ≤ b') (h3 : c ≤ c') (h4 : d ≤ d') :
    a * b * c * d ≤ a' * b' * c' * d' := by
  have h12 : a * b ≤ a' * b' := mul_le_mul h1 h2 hb ha'
  have h34 : c * d ≤ c' * d' := mul_le_mul h3 h4 hd hc'
  calc a * b * c * d = (a * b) * (c * d) := by ring
    _ ≤ (a' * b') * (c' * d') := mul_le_mul h12 h34 (mul_nonneg hc hd) (mul_nonneg ha' hb')
    _ = a' * b' * c' * d' := by ring

namespace FunnelBnd

lemma const (c : ℂ) : FunnelBnd 0 0 (fun _ _ => c) :=
  ⟨‖c‖ + 1, 0, 0, by positivity, le_rfl, le_rfl, fun τ z t hτ ht _ _ _ => by
    simp only [pow_zero, Real.rpow_zero, mul_one]
    linarith [norm_nonneg c]⟩

lemma one : FunnelBnd 0 0 (fun _ _ => (1 : ℂ)) := by simpa using const (1 : ℂ)

lemma neg {e k : ℕ} {F : ℍ → ℍ → ℂ} (h : FunnelBnd e k F) : FunnelBnd e k (fun τ z => -F τ z) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  exact ⟨C, N, M, hC, hN, hM, fun τ z t hτ ht ha hb' hzt => by
    rw [norm_neg]; exact hb τ z t hτ ht ha hb' hzt⟩

lemma cmul (c : ℂ) {e k : ℕ} {F : ℍ → ℍ → ℂ} (h : FunnelBnd e k F) :
    FunnelBnd e k (fun τ z => c * F τ z) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨(‖c‖ + 1) * (C + 1), N, M, by positivity, hN, hM, fun τ z t hτ ht ha hb' hzt => ?_⟩
  have hcoef : ‖c‖ * C ≤ (‖c‖ + 1) * (C + 1) := by nlinarith [norm_nonneg c, hC]
  rw [norm_mul]
  refine le_trans (mul_le_mul_of_nonneg_left (hb τ z t hτ ht ha hb' hzt) (norm_nonneg c)) ?_
  calc ‖c‖ * (C * ‖Work.Kernels.qParamFun τ‖ ^ e * ‖Work.Residues.Ept z‖ ^ k
          * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
      = (‖c‖ * C) * (‖Work.Kernels.qParamFun τ‖ ^ e * ‖Work.Residues.Ept z‖ ^ k
          * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M) := by ring
    _ ≤ ((‖c‖ + 1) * (C + 1)) * (‖Work.Kernels.qParamFun τ‖ ^ e * ‖Work.Residues.Ept z‖ ^ k
          * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M) :=
        mul_le_mul_of_nonneg_right hcoef
          (mul_nonneg (mul_nonneg (mul_nonneg (bnd_qpow_nonneg τ e) (bnd_ept_pow_nonneg z k))
            (scale_nonneg τ N)) (bnd_tpow_nonneg (one_le_one_add hτ ht) M))
    _ = (‖c‖ + 1) * (C + 1) * ‖Work.Kernels.qParamFun τ‖ ^ e * ‖Work.Residues.Ept z‖ ^ k
          * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by ring

/-- Addition lowers both exponents to the minimum. -/
lemma add {p q k l : ℕ} {F G : ℍ → ℍ → ℂ} (hF : FunnelBnd p k F) (hG : FunnelBnd q l G) :
    FunnelBnd (min p q) (min k l) (fun τ z => F τ z + G τ z) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, h1⟩ := hF
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, h2⟩ := hG
  refine ⟨C1 + C2, max N1 N2, max M1 M2, by positivity, le_max_of_le_left hN1,
    le_max_of_le_left hM1, fun τ z t hτ ht ha hb hzt => ?_⟩
  have hS : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hT : (1 : ℝ) ≤ 1 + t := one_le_one_add hτ ht
  have hQ : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := qnorm_le_one hτ
  have hU : ‖Work.Residues.Ept z‖ ≤ 1 := Ept_le_one z
  have hQ0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hU0 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
  have hp : ‖Work.Kernels.qParamFun τ‖ ^ p ≤ ‖Work.Kernels.qParamFun τ‖ ^ (min p q) :=
    pow_le_pow_of_le_one hQ0 hQ (min_le_left _ _)
  have hq : ‖Work.Kernels.qParamFun τ‖ ^ q ≤ ‖Work.Kernels.qParamFun τ‖ ^ (min p q) :=
    pow_le_pow_of_le_one hQ0 hQ (min_le_right _ _)
  have hk : ‖Work.Residues.Ept z‖ ^ k ≤ ‖Work.Residues.Ept z‖ ^ (min k l) :=
    pow_le_pow_of_le_one hU0 hU (min_le_left _ _)
  have hl : ‖Work.Residues.Ept z‖ ^ l ≤ ‖Work.Residues.Ept z‖ ^ (min k l) :=
    pow_le_pow_of_le_one hU0 hU (min_le_right _ _)
  have hSN1 : (Work.Kernels.scale τ) ^ N1 ≤ (Work.Kernels.scale τ) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hS (le_max_left _ _)
  have hSN2 : (Work.Kernels.scale τ) ^ N2 ≤ (Work.Kernels.scale τ) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hS (le_max_right _ _)
  have hTM1 : (1 + t) ^ M1 ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le hT (le_max_left _ _)
  have hTM2 : (1 + t) ^ M2 ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le hT (le_max_right _ _)
  have A1 : ‖F τ z‖ ≤ C1 * ‖Work.Kernels.qParamFun τ‖ ^ (min p q)
      * ‖Work.Residues.Ept z‖ ^ (min k l) * (Work.Kernels.scale τ) ^ (max N1 N2)
      * (1 + t) ^ (max M1 M2) := by
    refine le_trans (h1 τ z t hτ ht ha hb hzt) ?_
    calc C1 * ‖Work.Kernels.qParamFun τ‖ ^ p * ‖Work.Residues.Ept z‖ ^ k
          * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
        = C1 * (‖Work.Kernels.qParamFun τ‖ ^ p * ‖Work.Residues.Ept z‖ ^ k
          * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1) := by ring
      _ ≤ C1 * (‖Work.Kernels.qParamFun τ‖ ^ (min p q) * ‖Work.Residues.Ept z‖ ^ (min k l)
          * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)) :=
          mul_le_mul_of_nonneg_left
            (prod4_le (bnd_qpow_nonneg τ p) (bnd_ept_pow_nonneg z k) (scale_nonneg τ N1)
              (bnd_tpow_nonneg hT M1) (bnd_qpow_nonneg τ (min p q))
              (bnd_ept_pow_nonneg z (min k l)) (scale_nonneg τ (max N1 N2))
              (bnd_tpow_nonneg hT (max M1 M2)) hp hk hSN1 hTM1) hC1.le
      _ = C1 * ‖Work.Kernels.qParamFun τ‖ ^ (min p q) * ‖Work.Residues.Ept z‖ ^ (min k l)
          * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) := by ring
  have A2 : ‖G τ z‖ ≤ C2 * ‖Work.Kernels.qParamFun τ‖ ^ (min p q)
      * ‖Work.Residues.Ept z‖ ^ (min k l) * (Work.Kernels.scale τ) ^ (max N1 N2)
      * (1 + t) ^ (max M1 M2) := by
    refine le_trans (h2 τ z t hτ ht ha hb hzt) ?_
    calc C2 * ‖Work.Kernels.qParamFun τ‖ ^ q * ‖Work.Residues.Ept z‖ ^ l
          * (Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2
        = C2 * (‖Work.Kernels.qParamFun τ‖ ^ q * ‖Work.Residues.Ept z‖ ^ l
          * (Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2) := by ring
      _ ≤ C2 * (‖Work.Kernels.qParamFun τ‖ ^ (min p q) * ‖Work.Residues.Ept z‖ ^ (min k l)
          * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)) :=
          mul_le_mul_of_nonneg_left
            (prod4_le (bnd_qpow_nonneg τ q) (bnd_ept_pow_nonneg z l) (scale_nonneg τ N2)
              (bnd_tpow_nonneg hT M2) (bnd_qpow_nonneg τ (min p q))
              (bnd_ept_pow_nonneg z (min k l)) (scale_nonneg τ (max N1 N2))
              (bnd_tpow_nonneg hT (max M1 M2)) hq hl hSN2 hTM2) hC2.le
      _ = C2 * ‖Work.Kernels.qParamFun τ‖ ^ (min p q) * ‖Work.Residues.Ept z‖ ^ (min k l)
          * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) := by ring
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add A1 A2) (le_of_eq ?_)
  ring

lemma sub {p k : ℕ} {F G : ℍ → ℍ → ℂ} (hF : FunnelBnd p k F) (hG : FunnelBnd p k G) :
    FunnelBnd p k (fun τ z => F τ z - G τ z) := by
  have h := add hF (neg hG)
  rw [min_self, min_self] at h
  simpa only [sub_eq_add_neg] using h

/-- Multiplication adds the exponents. -/
lemma mul {p q k l : ℕ} {F G : ℍ → ℍ → ℂ} (hF : FunnelBnd p k F) (hG : FunnelBnd q l G) :
    FunnelBnd (p + q) (k + l) (fun τ z => F τ z * G τ z) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, h1⟩ := hF
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, h2⟩ := hG
  refine ⟨C1 * C2, N1 + N2, M1 + M2, by positivity, by positivity, by positivity,
    fun τ z t hτ ht ha hb hzt => ?_⟩
  have hT : (1 : ℝ) ≤ 1 + t := one_le_one_add hτ ht
  have hA : (0 : ℝ) ≤ C1 * ‖Work.Kernels.qParamFun τ‖ ^ p * ‖Work.Residues.Ept z‖ ^ k
      * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC1.le (bnd_qpow_nonneg τ p))
      (bnd_ept_pow_nonneg z k)) (scale_nonneg τ N1)) (bnd_tpow_nonneg hT M1)
  rw [norm_mul]
  refine le_trans (mul_le_mul (h1 τ z t hτ ht ha hb hzt) (h2 τ z t hτ ht ha hb hzt)
    (norm_nonneg _) hA) ?_
  refine le_of_eq ?_
  rw [Real.rpow_add (Work.Kernels.scale_pos τ), Real.rpow_add (by linarith : (0 : ℝ) < 1 + t),
    pow_add, pow_add]
  ring

lemma pow {p k : ℕ} {F : ℍ → ℍ → ℂ} (hF : FunnelBnd p k F) (n : ℕ) :
    FunnelBnd (p * n) (k * n) (fun τ z => F τ z ^ n) := by
  induction n with
  | zero => simpa only [mul_zero, pow_zero] using (one : FunnelBnd 0 0 (fun _ _ => (1 : ℂ)))
  | succ n ih =>
      have h : FunnelBnd (p * n + p) (k * n + k) (fun τ z => F τ z ^ n * F τ z) := mul ih hF
      rw [show p * n + p = p * (n + 1) by ring, show k * n + k = k * (n + 1) by ring] at h
      simpa only [pow_succ] using h

/-- Lowering the `q`-exponent (weaker statement). -/
lemma mono_e {p p' k : ℕ} {F : ℍ → ℍ → ℂ} (h : FunnelBnd p k F) (hpp' : p' ≤ p) : FunnelBnd p' k F := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hτ ht ha hb' hzt => ?_⟩
  refine le_trans (hb τ z t hτ ht ha hb' hzt) ?_
  have hQ0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hQ : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := qnorm_le_one hτ
  have hle : ‖Work.Kernels.qParamFun τ‖ ^ p ≤ ‖Work.Kernels.qParamFun τ‖ ^ p' :=
    pow_le_pow_of_le_one hQ0 hQ hpp'
  have hT : (1 : ℝ) ≤ 1 + t := one_le_one_add hτ ht
  calc C * ‖Work.Kernels.qParamFun τ‖ ^ p * ‖Work.Residues.Ept z‖ ^ k
        * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
      = (C * ‖Work.Residues.Ept z‖ ^ k * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
        * ‖Work.Kernels.qParamFun τ‖ ^ p := by ring
    _ ≤ (C * ‖Work.Residues.Ept z‖ ^ k * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
        * ‖Work.Kernels.qParamFun τ‖ ^ p' :=
        mul_le_mul_of_nonneg_left hle
          (mul_nonneg (mul_nonneg (mul_nonneg hC.le (bnd_ept_pow_nonneg z k))
            (scale_nonneg τ N)) (bnd_tpow_nonneg hT M))
    _ = C * ‖Work.Kernels.qParamFun τ‖ ^ p' * ‖Work.Residues.Ept z‖ ^ k
        * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by ring

/-- Lowering the `Ept`-exponent (weaker statement). -/
lemma mono_k {p k k' : ℕ} {F : ℍ → ℍ → ℂ} (h : FunnelBnd p k F) (hkk' : k' ≤ k) : FunnelBnd p k' F := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hτ ht ha hb' hzt => ?_⟩
  refine le_trans (hb τ z t hτ ht ha hb' hzt) ?_
  have hU0 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
  have hU : ‖Work.Residues.Ept z‖ ≤ 1 := Ept_le_one z
  have hle : ‖Work.Residues.Ept z‖ ^ k ≤ ‖Work.Residues.Ept z‖ ^ k' :=
    pow_le_pow_of_le_one hU0 hU hkk'
  have hT : (1 : ℝ) ≤ 1 + t := one_le_one_add hτ ht
  calc C * ‖Work.Kernels.qParamFun τ‖ ^ p * ‖Work.Residues.Ept z‖ ^ k
        * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
      = (C * ‖Work.Kernels.qParamFun τ‖ ^ p * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
        * ‖Work.Residues.Ept z‖ ^ k := by ring
    _ ≤ (C * ‖Work.Kernels.qParamFun τ‖ ^ p * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
        * ‖Work.Residues.Ept z‖ ^ k' :=
        mul_le_mul_of_nonneg_left hle
          (mul_nonneg (mul_nonneg (mul_nonneg hC.le (bnd_qpow_nonneg τ p))
            (scale_nonneg τ N)) (bnd_tpow_nonneg hT M))
    _ = C * ‖Work.Kernels.qParamFun τ‖ ^ p * ‖Work.Residues.Ept z‖ ^ k'
        * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by ring

/-- Invariance under pointwise equality on the strip. -/
lemma congr_on {p k : ℕ} {F G : ℍ → ℍ → ℂ} (h : FunnelBnd p k F)
    (hFG : ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t → -1 ≤ z.re →
      z.re ≤ 2 → z.im = t → F τ z = G τ z) : FunnelBnd p k G := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  exact ⟨C, N, M, hC, hN, hM, fun τ z t hτ ht ha hb' hzt => by
    rw [← hFG τ z t hτ ht ha hb' hzt]; exact hb τ z t hτ ht ha hb' hzt⟩

/-- A `z`-only estimate `‖f z‖ ≤ C‖Ept z‖ᵏ` for `1 ≤ Im z` gives `FunnelBnd 0 k`. -/
lemma ofZ_u {k : ℕ} {f : ℍ → ℂ} {C : ℝ} (hC : 0 < C)
    (h : ∀ z : ℍ, 1 ≤ z.im → ‖f z‖ ≤ C * ‖Work.Residues.Ept z‖ ^ k) :
    FunnelBnd 0 k (fun _ z => f z) :=
  ⟨C, 0, 0, hC, le_rfl, le_rfl, fun τ z t hτ ht _ _ hzt => by
    have hz : (1 : ℝ) ≤ z.im := by rw [hzt]; linarith [hτ.2, ht]
    have h' := h z hz
    simpa only [pow_zero, Real.rpow_zero, mul_one] using h'⟩

/-- A `z`-only estimate `‖f z‖ ≤ C‖q(z)‖ⁿ` for `1 ≤ Im z` gives `FunnelBnd 0 (2n)`. -/
lemma ofZ_q {n : ℕ} {f : ℍ → ℂ} {C : ℝ} (hC : 0 < C)
    (h : ∀ z : ℍ, 1 ≤ z.im → ‖f z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ n) :
    FunnelBnd 0 (2 * n) (fun _ z => f z) := by
  refine ofZ_u hC (fun z hz => ?_)
  refine le_trans (h z hz) (mul_le_mul_of_nonneg_left ?_ hC.le)
  rw [Work.Asymptotics.Small.qParamFun_eq_Ept_sq, norm_pow, ← pow_mul]

/-- A `z`-only estimate `‖f z‖ ≤ C(1+Im z)²‖Ept z‖ᵏ` for `3 ≤ Im z` gives `FunnelBnd 0 k`. -/
lemma ofZ_u2 {k : ℕ} {f : ℍ → ℂ} {C : ℝ} (hC : 0 < C)
    (h : ∀ z : ℍ, 3 ≤ z.im → -1 ≤ z.re → z.re ≤ 2 →
      ‖f z‖ ≤ C * (1 + z.im) ^ 2 * ‖Work.Residues.Ept z‖ ^ k) :
    FunnelBnd 0 k (fun _ z => f z) :=
  ⟨C, 0, 2, hC, le_rfl, by norm_num, fun τ z t hτ ht ha hb hzt => by
    have hz : (3 : ℝ) ≤ z.im := by rw [hzt]; linarith [hτ.2, ht]
    have h' := h z hz ha hb
    rw [hzt] at h'
    have h2 : (1 + t) ^ (2 : ℝ) = (1 + t) ^ 2 := Real.rpow_natCast _ 2
    rw [h2]
    have hgoal : ‖f z‖ ≤ C * ‖Work.Residues.Ept z‖ ^ k * (1 + t) ^ 2 := by
      calc ‖f z‖ ≤ C * (1 + t) ^ 2 * ‖Work.Residues.Ept z‖ ^ k := h'
        _ = C * ‖Work.Residues.Ept z‖ ^ k * (1 + t) ^ 2 := by ring
    simpa only [pow_zero, Real.rpow_zero, mul_one] using hgoal⟩

/-- A `τ`-only estimate `‖f τ‖ ≤ C‖q τ‖^p (scale τ)^N` gives `FunnelBnd p 0`. -/
lemma ofTau {p : ℕ} {f : ℍ → ℂ} {C N : ℝ} (hC : 0 < C) (hN : 0 ≤ N)
    (h : ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      ‖f τ‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ p * (Work.Kernels.scale τ) ^ N) :
    FunnelBnd p 0 (fun τ _ => f τ) :=
  ⟨C, N, 0, hC, hN, le_rfl, fun τ z t hτ ht _ _ _ => by
    have h' := h τ hτ
    simpa only [pow_zero, Real.rpow_zero, mul_one] using h'⟩

end FunnelBnd

/-! ## The `q`-power / `Ept`-power trade -/

/-- On the funnel strip (`t ≥ τ.im + 1`), `‖q(τ)‖^e‖Ept z‖^k ≤ ‖q(τ)‖³‖Ept z‖²` as soon as
`k ≥ 2` and `2e + k ≥ 8`. -/
private lemma qpow_Ept_trade {τ z : ℍ} {t : ℝ} (hτ : Work.Asymptotics.Funnel τ)
    (ht : τ.im + 1 ≤ t) (hzt : z.im = t) {e k : ℕ} (hk : 2 ≤ k) (he : 8 ≤ 2 * e + k) :
    ‖Work.Kernels.qParamFun τ‖ ^ e * ‖Work.Residues.Ept z‖ ^ k
      ≤ ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 := by
  have hL : ‖Work.Kernels.qParamFun τ‖ ^ e * ‖Work.Residues.Ept z‖ ^ k
      = Real.exp (-(2 * Real.pi * (e : ℝ) * τ.im) - Real.pi * (k : ℝ) * t) := by
    simp only [Work.Asymptotics.norm_qParamFun, Work.Residues.norm_Ept, hzt,
      ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hR : ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
      = Real.exp (-(2 * Real.pi * 3 * τ.im) - Real.pi * 2 * t) := by
    simp only [Work.Asymptotics.norm_qParamFun, Work.Residues.norm_Ept, hzt,
      ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hL, hR]
  apply Real.exp_le_exp.mpr
  have hIm : (0 : ℝ) ≤ τ.im := le_of_lt τ.im_pos
  have he' : (8 : ℝ) ≤ 2 * (e : ℝ) + (k : ℝ) := by exact_mod_cast he
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hA : 0 ≤ (2 * (e : ℝ) + (k : ℝ) - 8) * τ.im := mul_nonneg (by linarith) hIm
  have hB : 0 ≤ ((k : ℝ) - 2) * (t - τ.im - 1) := mul_nonneg (by linarith) (by linarith)
  have hC : 0 ≤ (k : ℝ) - 2 := by linarith
  have hsum : 0 ≤ (2 * (e : ℝ) + (k : ℝ) - 8) * τ.im
      + ((k : ℝ) - 2) * (t - τ.im - 1) + ((k : ℝ) - 2) := by linarith
  have hgoal0 : 0 ≤ (2 * (e : ℝ) - 6) * τ.im + ((k : ℝ) - 2) * t := by
    convert hsum using 1
    ring
  have hmain : 0 ≤ Real.pi * ((2 * (e : ℝ) - 6) * τ.im + ((k : ℝ) - 2) * t) :=
    mul_nonneg Real.pi_pos.le hgoal0
  rw [show -(2 * Real.pi * (e : ℝ) * τ.im) - Real.pi * (k : ℝ) * t
      = -(2 * Real.pi * 3 * τ.im) - Real.pi * 2 * t
        - Real.pi * ((2 * (e : ℝ) - 6) * τ.im + ((k : ℝ) - 2) * t) from by ring]
  linarith

/-- **Exponent bookkeeping.**  `FunnelBnd e k` with `k ≥ 2` and `2e + k ≥ 8` upgrades to the target
shape `FunnelBnd 3 2`. -/
private lemma Bnd_up {e k : ℕ} {F : ℍ → ℍ → ℂ} (h : FunnelBnd e k F) (hk : 2 ≤ k) (he : 8 ≤ 2 * e + k) :
    FunnelBnd 3 2 F := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hτ ht ha hb' hzt => ?_⟩
  refine le_trans (hb τ z t hτ ht ha hb' hzt) ?_
  have hkey := qpow_Ept_trade hτ ht hzt hk he
  have hT : (1 : ℝ) ≤ 1 + t := one_le_one_add hτ ht
  calc C * ‖Work.Kernels.qParamFun τ‖ ^ e * ‖Work.Residues.Ept z‖ ^ k
        * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
      = C * (‖Work.Kernels.qParamFun τ‖ ^ e * ‖Work.Residues.Ept z‖ ^ k)
        * ((Work.Kernels.scale τ) ^ N * (1 + t) ^ M) := by ring
    _ ≤ C * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2)
        * ((Work.Kernels.scale τ) ^ N * (1 + t) ^ M) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey hC.le)
          (mul_nonneg (scale_nonneg τ N) (bnd_tpow_nonneg hT M))
    _ = C * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
        * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by ring


/-! ## Bounds for the `τ`-atoms -/

private lemma bnd_Delta : FunnelBnd 1 0 (fun τ _ => Work.Kernels.DeltaFun τ) :=
  ⟨2, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hτ ht _ _ _ => by
    have h := Work.Asymptotics.DeltaFun_funnel_le τ hτ
    simpa only [pow_one, pow_zero, Real.rpow_zero, mul_one, one_mul] using h⟩

private lemma bnd_E4 : FunnelBnd 0 0 (fun τ _ => Work.Kernels.E4Fun τ) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.E4Fun_bound
  refine FunnelBnd.ofTau hC le_rfl (fun τ hτ => ?_)
  have h' := h τ (by linarith [hτ.2])
  simpa only [pow_zero, Real.rpow_zero, mul_one, one_mul] using h'

private lemma bnd_E6 : FunnelBnd 0 0 (fun τ _ => Work.Kernels.E6Fun τ) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.E6Fun_bound
  refine FunnelBnd.ofTau hC le_rfl (fun τ hτ => ?_)
  have h' := h τ (by linarith [hτ.2])
  simpa only [pow_zero, Real.rpow_zero, mul_one, one_mul] using h'

private lemma bnd_tau : FunnelBnd 0 0 (fun τ _ => ((τ : ℍ) : ℂ)) :=
  FunnelBnd.ofTau (C := 1) (N := 1) (by norm_num) (by norm_num) (fun τ _ => by
    have h := Work.Kernels.coe_norm_le_scale τ
    simpa only [pow_zero, Real.rpow_one, mul_one, one_mul] using h)

private lemma bnd_phi0 : FunnelBnd 0 0 (fun τ _ => Work.Kernels.phi0 τ) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.E2Fun_bound
  refine FunnelBnd.ofTau (C := C + 3 / Real.pi + 1) (N := 1) (by positivity) (by norm_num)
    (fun τ hτ => ?_)
  have h2 := h τ (by linarith [hτ.2])
  have hS : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hS' : ‖(τ : ℂ)‖ ≤ Work.Kernels.scale τ := Work.Kernels.coe_norm_le_scale τ
  have hp3 : (0 : ℝ) < 3 / Real.pi := by positivity
  have h3 : ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 3 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hmain : ‖Work.Kernels.phi0 τ‖ ≤ (C + 3 / Real.pi + 1) * Work.Kernels.scale τ := by
    rw [Work.Kernels.phi0]
    calc ‖(τ : ℂ) * Work.Kernels.E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)‖
        ≤ ‖(τ : ℂ) * Work.Kernels.E2Fun τ‖ + ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ :=
          norm_sub_le _ _
      _ = ‖(τ : ℂ)‖ * ‖Work.Kernels.E2Fun τ‖ + 3 / Real.pi := by rw [norm_mul, h3]
      _ ≤ Work.Kernels.scale τ * ‖Work.Kernels.E2Fun τ‖ + 3 / Real.pi := by
          have := mul_le_mul_of_nonneg_right hS' (norm_nonneg (Work.Kernels.E2Fun τ))
          linarith
      _ ≤ Work.Kernels.scale τ * C + 3 / Real.pi := by
          have := mul_le_mul_of_nonneg_left h2 (Work.Kernels.scale_pos τ).le
          linarith
      _ ≤ (C + 3 / Real.pi + 1) * Work.Kernels.scale τ := by
          have h3s : 3 / Real.pi ≤ (3 / Real.pi) * Work.Kernels.scale τ := by
            nlinarith [hS, hp3]
          nlinarith [h3s, hS, hp3, hC]
  simpa only [pow_zero, Real.rpow_one, mul_one] using hmain

private lemma bnd_psi2 (ℓ : Work.Kernels.LogLambdaData) :
    FunnelBnd 0 0 (fun τ _ => Work.Kernels.psi2 ℓ τ) := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.psi_scale_funnel ℓ
  exact FunnelBnd.ofTau hC hN (fun τ hτ => by
    simpa only [pow_zero, mul_one] using (h τ hτ).1)

private lemma bnd_psi4 (ℓ : Work.Kernels.LogLambdaData) :
    FunnelBnd 0 0 (fun τ _ => Work.Kernels.psi4 ℓ τ) := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.psi_scale_funnel ℓ
  exact FunnelBnd.ofTau hC hN (fun τ hτ => by
    simpa only [pow_zero, mul_one] using (h τ hτ).2)

private lemma bnd_E14 : FunnelBnd 0 0 (fun τ _ => Work.Kernels.E14Fun τ) := by
  obtain ⟨C4, hC4, h4⟩ := Work.Asymptotics.E4Fun_bound
  obtain ⟨C6, hC6, h6⟩ := Work.Asymptotics.E6Fun_bound
  refine FunnelBnd.ofTau (C := C4 ^ 2 * C6) (N := 0) (by positivity) le_rfl (fun τ hτ => ?_)
  have h4' := h4 τ (by linarith [hτ.2])
  have h6' := h6 τ (by linarith [hτ.2])
  have h : ‖Work.Kernels.E14Fun τ‖ ≤ C4 ^ 2 * C6 := by
    have h4sq : ‖Work.Kernels.E4Fun τ‖ ^ 2 ≤ C4 ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h4' 2
    calc ‖Work.Kernels.E14Fun τ‖
        = ‖Work.Kernels.E4Fun τ ^ 2‖ * ‖Work.Kernels.E6Fun τ‖ := by
          rw [show Work.Kernels.E14Fun τ
            = Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ from rfl, norm_mul]
      _ = ‖Work.Kernels.E4Fun τ‖ ^ 2 * ‖Work.Kernels.E6Fun τ‖ := by rw [norm_pow]
      _ ≤ C4 ^ 2 * C6 := mul_le_mul h4sq h6' (norm_nonneg _) (by positivity)
  simpa only [pow_zero, Real.rpow_zero, mul_one] using h

/-! ## Bounds for the `z`-atoms -/

private lemma Ept_q_le_one {z : ℍ} (hz : 1 ≤ z.im) : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
  rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
  nlinarith [Real.pi_pos, hz]

private lemma E2Ztr_bound (z : ℍ) (hz : 1 ≤ z.im) : ‖E2Ztr z‖ ≤ 97 := by
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := Ept_q_le_one hz
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have h2 : ‖Work.Kernels.qParamFun z‖ ^ 2 ≤ 1 := by nlinarith [hq1, hq0]
  rw [E2Ztr]
  calc ‖(1 : ℂ) - (24 : ℂ) * Work.Kernels.qParamFun z
        - (72 : ℂ) * Work.Kernels.qParamFun z ^ 2‖
      ≤ ‖(1 : ℂ) - (24 : ℂ) * Work.Kernels.qParamFun z‖
        + ‖(72 : ℂ) * Work.Kernels.qParamFun z ^ 2‖ := norm_sub_le _ _
    _ ≤ (1 + 24 * 1) + 72 * 1 := by
        refine add_le_add ?_ ?_
        · calc ‖(1 : ℂ) - (24 : ℂ) * Work.Kernels.qParamFun z‖
              ≤ ‖(1 : ℂ)‖ + ‖(24 : ℂ) * Work.Kernels.qParamFun z‖ := norm_sub_le _ _
            _ = 1 + 24 * ‖Work.Kernels.qParamFun z‖ := by rw [norm_one, norm_mul]; norm_num
            _ ≤ 1 + 24 * 1 := by nlinarith [hq1]
        · rw [norm_mul, norm_pow]; norm_num
          nlinarith [h2]
    _ = 97 := by norm_num

private lemma E4Ztr_bound (z : ℍ) (hz : 1 ≤ z.im) : ‖E4Ztr z‖ ≤ 2401 := by
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := Ept_q_le_one hz
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have h2 : ‖Work.Kernels.qParamFun z‖ ^ 2 ≤ 1 := by nlinarith [hq1, hq0]
  rw [E4Ztr]
  calc ‖(1 : ℂ) + (240 : ℂ) * Work.Kernels.qParamFun z
        + (2160 : ℂ) * Work.Kernels.qParamFun z ^ 2‖
      ≤ ‖(1 : ℂ) + (240 : ℂ) * Work.Kernels.qParamFun z‖
        + ‖(2160 : ℂ) * Work.Kernels.qParamFun z ^ 2‖ := norm_add_le _ _
    _ ≤ (1 + 240 * 1) + 2160 * 1 := by
        refine add_le_add ?_ ?_
        · calc ‖(1 : ℂ) + (240 : ℂ) * Work.Kernels.qParamFun z‖
              ≤ ‖(1 : ℂ)‖ + ‖(240 : ℂ) * Work.Kernels.qParamFun z‖ := norm_add_le _ _
            _ = 1 + 240 * ‖Work.Kernels.qParamFun z‖ := by rw [norm_one, norm_mul]; norm_num
            _ ≤ 1 + 240 * 1 := by nlinarith [hq1]
        · rw [norm_mul, norm_pow]; norm_num
          nlinarith [h2]
    _ = 2401 := by norm_num

private lemma E6Ztr_bound (z : ℍ) (hz : 1 ≤ z.im) : ‖E6Ztr z‖ ≤ 17137 := by
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := Ept_q_le_one hz
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have h2 : ‖Work.Kernels.qParamFun z‖ ^ 2 ≤ 1 := by nlinarith [hq1, hq0]
  rw [E6Ztr]
  calc ‖(1 : ℂ) - (504 : ℂ) * Work.Kernels.qParamFun z
        - (16632 : ℂ) * Work.Kernels.qParamFun z ^ 2‖
      ≤ ‖(1 : ℂ) - (504 : ℂ) * Work.Kernels.qParamFun z‖
        + ‖(16632 : ℂ) * Work.Kernels.qParamFun z ^ 2‖ := norm_sub_le _ _
    _ ≤ (1 + 504 * 1) + 16632 * 1 := by
        refine add_le_add ?_ ?_
        · calc ‖(1 : ℂ) - (504 : ℂ) * Work.Kernels.qParamFun z‖
              ≤ ‖(1 : ℂ)‖ + ‖(504 : ℂ) * Work.Kernels.qParamFun z‖ := norm_sub_le _ _
            _ = 1 + 504 * ‖Work.Kernels.qParamFun z‖ := by rw [norm_one, norm_mul]; norm_num
            _ ≤ 1 + 504 * 1 := by nlinarith [hq1]
        · rw [norm_mul, norm_pow]; norm_num
          nlinarith [h2]
    _ = 17137 := by norm_num

private lemma GtTr_bound (z : ℍ) (hz : 1 ≤ z.im) :
    ‖GtTr z‖ ≤ 97 * ‖(z : ℂ)‖ + 6 / Real.pi := by
  have hEz := E2Ztr_bound z hz
  have h6 : ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 6 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [GtTr]
  calc ‖(z : ℂ) * E2Ztr z - (6 : ℂ) * Complex.I / (Real.pi : ℂ)‖
      ≤ ‖(z : ℂ) * E2Ztr z‖ + ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ := norm_sub_le _ _
    _ = ‖(z : ℂ)‖ * ‖E2Ztr z‖ + 6 / Real.pi := by rw [norm_mul, h6]
    _ ≤ ‖(z : ℂ)‖ * 97 + 6 / Real.pi := by
        have := mul_le_mul_of_nonneg_left hEz (norm_nonneg (z : ℂ)); linarith
    _ = 97 * ‖(z : ℂ)‖ + 6 / Real.pi := by ring

private lemma phit2Ztr_bound (z : ℍ) (hz : 1 ≤ z.im) :
    ‖phit2Ztr z‖ ≤ (97 * ‖(z : ℂ)‖ + 6 / Real.pi) ^ 2 := by
  rw [phit2Ztr, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (GtTr_bound z hz) 2

private lemma phit1Ztr_bound (z : ℍ) (hz : 1 ≤ z.im) :
    ‖phit1Ztr z‖ ≤ ‖(z : ℂ)‖ * (97 * ‖(z : ℂ)‖ + 6 / Real.pi) := by
  rw [phit1Ztr, norm_mul]
  exact mul_le_mul_of_nonneg_left (GtTr_bound z hz) (norm_nonneg _)

private lemma bnd_Ept : FunnelBnd 0 1 (fun _ z => Work.Residues.Ept z) :=
  ⟨1, 0, 0, one_pos, le_rfl, le_rfl, fun τ z t _ _ _ _ _ => by
    simpa only [pow_zero, Real.rpow_zero, pow_one, mul_one, one_mul] using
      (le_refl ‖Work.Residues.Ept z‖ : ‖Work.Residues.Ept z‖ ≤ ‖Work.Residues.Ept z‖)⟩

private lemma norm_Xc_le (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) (t : ℝ)
    (ha : -1 ≤ z.re) (hb : z.re ≤ 2) (hzt : z.im = t) :
    ‖Work.Asymptotics.Compact.Xc ℓ z‖ ≤ (2 * Real.pi + 4 * Real.log 2) * (1 + t) := by
  have hc : Work.Asymptotics.Compact.cuspC ℓ = 4 * (Real.log 2 : ℂ) :=
    Work.Asymptotics.CuspL_eq ℓ
  have hz := Work.Asymptotics.KhatE1.kdevA4_norm_z_le z t ha hb hzt
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlog : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have ht1 : (1 : ℝ) ≤ 1 + t := by rw [← hzt]; linarith [z.im_pos]
  rw [Work.Asymptotics.Compact.Xc, hc]
  calc ‖(Real.pi : ℂ) * Complex.I * (z : ℂ) + (4 : ℂ) * (Real.log 2 : ℂ)‖
      ≤ ‖(Real.pi : ℂ) * Complex.I * (z : ℂ)‖ + ‖(4 : ℂ) * (Real.log 2 : ℂ)‖ :=
        norm_add_le _ _
    _ = Real.pi * ‖(z : ℂ)‖ + 4 * Real.log 2 := by
        have hA : ‖(Real.pi : ℂ) * Complex.I * (z : ℂ)‖ = Real.pi * ‖(z : ℂ)‖ := by
          rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hπ]
        have hB : ‖(4 : ℂ) * (Real.log 2 : ℂ)‖ = 4 * Real.log 2 := by
          rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hlog]
        rw [hA, hB]
    _ ≤ Real.pi * (2 * (1 + t)) + 4 * Real.log 2 := by
        have := mul_le_mul_of_nonneg_left hz hπ.le; linarith
    _ ≤ (2 * Real.pi + 4 * Real.log 2) * (1 + t) := by
        nlinarith [hlog, hπ, ht1]

private lemma bnd_E10ref : FunnelBnd 0 0 (fun _ z => Work.Asymptotics.Compact.E10ref z) := by
  refine FunnelBnd.ofZ_u (C := 265) (by norm_num) (fun z _ => ?_)
  have hu := Ept_le_one z
  have hu0 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
  rw [Work.Asymptotics.Compact.E10ref]
  calc ‖(1 : ℂ) - (264 : ℂ) * Work.Residues.Ept z ^ 2‖
      ≤ ‖(1 : ℂ)‖ + ‖(264 : ℂ) * Work.Residues.Ept z ^ 2‖ := norm_sub_le _ _
    _ = 1 + 264 * ‖Work.Residues.Ept z‖ ^ 2 := by rw [norm_one, norm_mul, norm_pow]; norm_num
    _ ≤ 265 := by nlinarith [hu, hu0]
    _ = 265 * ‖Work.Residues.Ept z‖ ^ 0 := by rw [pow_zero, mul_one]

private lemma bnd_E8ref : FunnelBnd 0 0 (fun _ z => Work.Asymptotics.Compact.E8ref z) := by
  refine FunnelBnd.ofZ_u (C := 481) (by norm_num) (fun z _ => ?_)
  have hu := Ept_le_one z
  have hu0 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
  rw [Work.Asymptotics.Compact.E8ref]
  calc ‖(1 : ℂ) + (480 : ℂ) * Work.Residues.Ept z ^ 2‖
      ≤ ‖(1 : ℂ)‖ + ‖(480 : ℂ) * Work.Residues.Ept z ^ 2‖ := norm_add_le _ _
    _ = 1 + 480 * ‖Work.Residues.Ept z‖ ^ 2 := by rw [norm_one, norm_mul, norm_pow]; norm_num
    _ ≤ 481 := by nlinarith [hu, hu0]
    _ = 481 * ‖Work.Residues.Ept z‖ ^ 0 := by rw [pow_zero, mul_one]

private lemma bnd_E6ref : FunnelBnd 0 0 (fun _ z => Work.Asymptotics.Compact.E6ref z) := by
  refine FunnelBnd.ofZ_u (C := 505) (by norm_num) (fun z _ => ?_)
  have hu := Ept_le_one z
  have hu0 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
  rw [Work.Asymptotics.Compact.E6ref]
  calc ‖(1 : ℂ) - (504 : ℂ) * Work.Residues.Ept z ^ 2‖
      ≤ ‖(1 : ℂ)‖ + ‖(504 : ℂ) * Work.Residues.Ept z ^ 2‖ := norm_sub_le _ _
    _ = 1 + 504 * ‖Work.Residues.Ept z‖ ^ 2 := by rw [norm_one, norm_mul, norm_pow]; norm_num
    _ ≤ 505 := by nlinarith [hu, hu0]
    _ = 505 * ‖Work.Residues.Ept z‖ ^ 0 := by rw [pow_zero, mul_one]

private lemma bnd_Wref : FunnelBnd 0 0 (fun _ z => Work.Asymptotics.Compact.Wref z) := by
  refine FunnelBnd.ofZ_u (C := 33) (by norm_num) (fun z _ => ?_)
  have hu := Ept_le_one z
  have hu0 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
  have h2 : ‖Work.Residues.Ept z ^ 2‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ hu0 hu
  rw [Work.Asymptotics.Compact.Wref]
  calc ‖(1 : ℂ) - (8 : ℂ) * Work.Residues.Ept z + (24 : ℂ) * Work.Residues.Ept z ^ 2‖
      ≤ ‖(1 : ℂ) - (8 : ℂ) * Work.Residues.Ept z‖
        + ‖(24 : ℂ) * Work.Residues.Ept z ^ 2‖ := norm_add_le _ _
    _ ≤ (1 + 8) + 24 := by
        refine add_le_add ?_ ?_
        · calc ‖(1 : ℂ) - (8 : ℂ) * Work.Residues.Ept z‖
              ≤ ‖(1 : ℂ)‖ + ‖(8 : ℂ) * Work.Residues.Ept z‖ := norm_sub_le _ _
            _ = 1 + 8 * ‖Work.Residues.Ept z‖ := by rw [norm_one, norm_mul]; norm_num
            _ ≤ 1 + 8 := by nlinarith [hu]
        · rw [norm_mul, show ‖(24 : ℂ)‖ = 24 by norm_num]
          simpa using mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 24)
    _ ≤ 33 := by norm_num
    _ = 33 * ‖Work.Residues.Ept z‖ ^ 0 := by rw [pow_zero, mul_one]

private lemma bnd_D2ref : FunnelBnd 0 0 (fun _ z => Work.Asymptotics.Compact.D2ref z) := by
  refine FunnelBnd.ofZ_u (C := 161) (by norm_num) (fun z _ => ?_)
  have hu := Ept_le_one z
  have hu0 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
  have h2 : ‖Work.Residues.Ept z ^ 2‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ hu0 hu
  rw [Work.Asymptotics.Compact.D2ref]
  calc ‖(1 : ℂ) + (16 : ℂ) * Work.Residues.Ept z - (144 : ℂ) * Work.Residues.Ept z ^ 2‖
      ≤ ‖(1 : ℂ) + (16 : ℂ) * Work.Residues.Ept z‖
        + ‖(144 : ℂ) * Work.Residues.Ept z ^ 2‖ := norm_sub_le _ _
    _ ≤ (1 + 16) + 144 := by
        refine add_le_add ?_ ?_
        · calc ‖(1 : ℂ) + (16 : ℂ) * Work.Residues.Ept z‖
              ≤ ‖(1 : ℂ)‖ + ‖(16 : ℂ) * Work.Residues.Ept z‖ := norm_add_le _ _
            _ = 1 + 16 * ‖Work.Residues.Ept z‖ := by rw [norm_one, norm_mul]; norm_num
            _ ≤ 1 + 16 := by nlinarith [hu]
        · rw [norm_mul, show ‖(144 : ℂ)‖ = 144 by norm_num]
          simpa using mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 144)
    _ ≤ 161 := by norm_num
    _ = 161 * ‖Work.Residues.Ept z‖ ^ 0 := by rw [pow_zero, mul_one]

private lemma bnd_Lref (ℓ : Work.Kernels.LogLambdaData) :
    FunnelBnd 0 0 (fun _ z => Work.Asymptotics.Compact.Lref ℓ z) := by
  have hlog : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨2 * Real.pi + 4 * Real.log 2 + 21, 0, 1, by positivity, le_rfl, by norm_num,
    fun τ z t hτ ht ha hb hzt => ?_⟩
  have hT : (1 : ℝ) ≤ 1 + t := one_le_one_add hτ ht
  have hu := Ept_le_one z
  have hu0 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
  have h2 : ‖Work.Residues.Ept z ^ 2‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ hu0 hu
  have hXc := norm_Xc_le ℓ z t ha hb hzt
  have hL : Work.Asymptotics.Compact.Lref ℓ z
      = Work.Asymptotics.Compact.Xc ℓ z - (8 : ℂ) * Work.Residues.Ept z
        + (12 : ℂ) * Work.Residues.Ept z ^ 2 := rfl
  dsimp only
  rw [hL]
  calc ‖Work.Asymptotics.Compact.Xc ℓ z - (8 : ℂ) * Work.Residues.Ept z
        + (12 : ℂ) * Work.Residues.Ept z ^ 2‖
      ≤ ‖Work.Asymptotics.Compact.Xc ℓ z‖ + ‖(8 : ℂ) * Work.Residues.Ept z‖
        + ‖(12 : ℂ) * Work.Residues.Ept z ^ 2‖ := by
        have h1 := norm_add_le (Work.Asymptotics.Compact.Xc ℓ z - (8 : ℂ) * Work.Residues.Ept z)
          ((12 : ℂ) * Work.Residues.Ept z ^ 2)
        have h2' := norm_sub_le (Work.Asymptotics.Compact.Xc ℓ z)
          ((8 : ℂ) * Work.Residues.Ept z)
        linarith
    _ ≤ (2 * Real.pi + 4 * Real.log 2) * (1 + t) + 8 + 12 := by
        refine add_le_add (add_le_add hXc ?_) ?_
        · rw [norm_mul, show ‖(8 : ℂ)‖ = 8 by norm_num]; nlinarith [hu]
        · rw [norm_mul, show ‖(12 : ℂ)‖ = 12 by norm_num]; nlinarith [h2]
    _ ≤ (2 * Real.pi + 4 * Real.log 2 + 21) * (1 + t) := by
        nlinarith [hT, hlog, Real.pi_pos]
    _ = (2 * Real.pi + 4 * Real.log 2 + 21) * ‖Work.Kernels.qParamFun τ‖ ^ 0
          * ‖Work.Residues.Ept z‖ ^ 0 * (Work.Kernels.scale τ) ^ (0 : ℝ)
          * (1 + t) ^ (1 : ℝ) := by
        simp only [pow_zero, Real.rpow_zero, Real.rpow_one, mul_one, one_mul]

private lemma dE2z_bound1 : ∃ C : ℝ, 0 < C ∧ (∀ z : ℍ, 1 ≤ z.im →
    ‖dE2z z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.E2Fun_second_order
  refine ⟨C, hC, fun z hz => ?_⟩
  have he : dE2z z = Work.Kernels.E2Fun z - 1 + 24 * Work.Kernels.qParamFun z
      + 72 * (Work.Kernels.qParamFun z) ^ 2 := by
    change Work.Kernels.E2Fun z - (1 - 24 * Work.Kernels.qParamFun z
      - 72 * (Work.Kernels.qParamFun z) ^ 2) = _
    ring
  rw [he]; exact h z hz

private lemma dE4z_bound1 : ∃ C : ℝ, 0 < C ∧ (∀ z : ℍ, 1 ≤ z.im →
    ‖dE4z z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.E4Fun_second_order
  refine ⟨C, hC, fun z hz => ?_⟩
  have he : dE4z z = Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
      - 2160 * (Work.Kernels.qParamFun z) ^ 2 := by
    change Work.Kernels.E4Fun z - (1 + 240 * Work.Kernels.qParamFun z
      + 2160 * (Work.Kernels.qParamFun z) ^ 2) = _
    ring
  rw [he]; exact h z hz

private lemma dE6z_bound1 : ∃ C : ℝ, 0 < C ∧ (∀ z : ℍ, 1 ≤ z.im →
    ‖dE6z z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.E6Fun_second_order
  refine ⟨C, hC, fun z hz => ?_⟩
  have he : dE6z z = Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
      + 16632 * (Work.Kernels.qParamFun z) ^ 2 := by
    change Work.Kernels.E6Fun z - (1 - 504 * Work.Kernels.qParamFun z
      - 16632 * (Work.Kernels.qParamFun z) ^ 2) = _
    ring
  rw [he]; exact h z hz

private lemma bnd_rW : FunnelBnd 0 6 (fun _ z => rW z) := by
  obtain ⟨C, hC, h⟩ := WfunSixthH
  refine FunnelBnd.ofZ_u hC (fun z hz => ?_)
  have htr : (1 - 8 * Work.Residues.Ept z + 24 * (Work.Residues.Ept z) ^ 2
      - 32 * (Work.Residues.Ept z) ^ 3 + 24 * (Work.Residues.Ept z) ^ 4
      - 48 * (Work.Residues.Ept z) ^ 5) = WrefHi z := by
    rw [WrefHi, Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
    ring
  rw [rW, ← htr]
  exact h z hz

private lemma bnd_rD2 : FunnelBnd 0 6 (fun _ z => rD2 z) := by
  obtain ⟨C, hC, h⟩ := UVSqSixthH
  refine FunnelBnd.ofZ_u hC (fun z hz => ?_)
  have htr : (1 + 16 * Work.Residues.Ept z - 144 * (Work.Residues.Ept z) ^ 2
      + 448 * (Work.Residues.Ept z) ^ 3 - 912 * (Work.Residues.Ept z) ^ 4
      + 2016 * (Work.Residues.Ept z) ^ 5) = D2refHi z := by
    rw [D2refHi, Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
    ring
  have he : rD2 z = (Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2)
      - (1 + 16 * Work.Residues.Ept z - 144 * (Work.Residues.Ept z) ^ 2
        + 448 * (Work.Residues.Ept z) ^ 3 - 912 * (Work.Residues.Ept z) ^ 4
        + 2016 * (Work.Residues.Ept z) ^ 5) := by
    rw [rD2, htr]
  rw [he]; exact h z hz

private lemma bnd_rE8 : FunnelBnd 0 6 (fun _ z => rE8 z) := by
  obtain ⟨C, hC, h⟩ := E4sqThirdOrder
  refine FunnelBnd.ofZ_q (n := 3) hC (fun z hz => ?_)
  have hz' := h z hz
  have he : rE8 z = Work.Kernels.E4Fun z ^ 2 - 1 - 480 * Work.Kernels.qParamFun z
      - 61920 * (Work.Kernels.qParamFun z) ^ 2 := by
    show Work.Kernels.E8Fun z - E8refHi z = _
    rw [E8refHi]
    dsimp only [Work.Kernels.E8Fun]
    ring
  rw [he]; exact hz'

private lemma bnd_rE10 : FunnelBnd 0 6 (fun _ z => rE10 z) := by
  obtain ⟨C, hC, h⟩ := E4E6ThirdOrder
  refine FunnelBnd.ofZ_q (n := 3) hC (fun z hz => ?_)
  have hz' := h z hz
  have he : rE10 z = Work.Kernels.E4Fun z * Work.Kernels.E6Fun z - 1
      + 264 * Work.Kernels.qParamFun z + 135432 * (Work.Kernels.qParamFun z) ^ 2 := by
    show Work.Kernels.E10Fun z - E10refHi z = _
    rw [E10refHi]
    dsimp only [Work.Kernels.E10Fun]
    ring
  rw [he]; exact hz'

private lemma bnd_rE6 : FunnelBnd 0 6 (fun _ z => rE6 z) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.E6Fun_second_order
  refine FunnelBnd.ofZ_q (n := 3) hC (fun z hz => ?_)
  have hz' := h z hz
  have he : rE6 z = Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
      + 16632 * (Work.Kernels.qParamFun z) ^ 2 := by
    show Work.Kernels.E6Fun z - E6refHi z = _
    rw [E6refHi]
    ring
  rw [he]; exact hz'

private lemma bnd_rL (ℓ : Work.Kernels.LogLambdaData) : FunnelBnd 0 5 (fun _ z => rL ℓ z) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.KhatE1.cusp_L_fourth ℓ
  refine FunnelBnd.ofZ_u hC (fun z hz => ?_)
  have hz' := h z hz
  have hc : Work.Asymptotics.Compact.cuspC ℓ = 4 * (Real.log 2 : ℂ) :=
    Work.Asymptotics.CuspL_eq ℓ
  have htr : ((Real.pi : ℂ) * Complex.I * (z : ℂ) + 4 * (Real.log 2 : ℂ)
      - 8 * Work.Residues.Ept z + 12 * (Work.Residues.Ept z) ^ 2
      - ((32 : ℂ) / 3) * (Work.Residues.Ept z) ^ 3 + 6 * (Work.Residues.Ept z) ^ 4)
      = LrefHi ℓ z := by
    change ((Real.pi : ℂ) * Complex.I * (z : ℂ) + 4 * (Real.log 2 : ℂ)
        - 8 * Work.Residues.Ept z + 12 * (Work.Residues.Ept z) ^ 2
        - ((32 : ℂ) / 3) * (Work.Residues.Ept z) ^ 3 + 6 * (Work.Residues.Ept z) ^ 4)
      = (Real.pi : ℂ) * Complex.I * (z : ℂ) + Work.Asymptotics.Compact.cuspC ℓ
        - 8 * Work.Residues.Ept z + 12 * Work.Kernels.qParamFun z
        - ((32 : ℂ) / 3) * (Work.Residues.Ept z) ^ 3
        + 6 * (Work.Kernels.qParamFun z) ^ 2
    rw [hc, Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
    ring
  have he : rL ℓ z = ℓ.L z - ((Real.pi : ℂ) * Complex.I * (z : ℂ) + 4 * (Real.log 2 : ℂ)
      - 8 * Work.Residues.Ept z + 12 * (Work.Residues.Ept z) ^ 2
      - ((32 : ℂ) / 3) * (Work.Residues.Ept z) ^ 3 + 6 * (Work.Residues.Ept z) ^ 4) := by
    rw [rL, htr]
  rw [he]; exact hz'

private lemma bnd_dE8pol : FunnelBnd 0 4 (fun _ z => dE8pol z) := by
  refine (FunnelBnd.cmul (61920 : ℂ) (FunnelBnd.pow bnd_Ept 4)).congr_on (fun τ z t _ _ _ _ _ => ?_)
  show (61920 : ℂ) * Work.Residues.Ept z ^ 4 = dE8pol z
  rw [dE8pol, E8refHi_sub_E8ref z, Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
  ring

private lemma bnd_dE10pol : FunnelBnd 0 4 (fun _ z => dE10pol z) := by
  refine (FunnelBnd.cmul (-135432 : ℂ) (FunnelBnd.pow bnd_Ept 4)).congr_on (fun τ z t _ _ _ _ _ => ?_)
  show (-135432 : ℂ) * Work.Residues.Ept z ^ 4 = dE10pol z
  rw [dE10pol, E10refHi_sub_E10ref z, Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
  ring

private lemma bnd_dE6pol : FunnelBnd 0 4 (fun _ z => dE6pol z) := by
  refine (FunnelBnd.cmul (-16632 : ℂ) (FunnelBnd.pow bnd_Ept 4)).congr_on (fun τ z t _ _ _ _ _ => ?_)
  show (-16632 : ℂ) * Work.Residues.Ept z ^ 4 = dE6pol z
  rw [dE6pol, E6refHi_sub_E6ref z, Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
  ring

private lemma bnd_dWpol : FunnelBnd 0 3 (fun _ z => dWpol z) := by
  refine (FunnelBnd.sub (FunnelBnd.add (FunnelBnd.cmul (-32 : ℂ) (FunnelBnd.pow bnd_Ept 3))
      (FunnelBnd.cmul (24 : ℂ) (FunnelBnd.pow bnd_Ept 4)))
    (FunnelBnd.mono_k (FunnelBnd.cmul (48 : ℂ) (FunnelBnd.pow bnd_Ept 5)) (by norm_num : 3 ≤ 5))).congr_on
    (fun τ z t _ _ _ _ _ => ?_)
  show (-32 : ℂ) * Work.Residues.Ept z ^ 3 + (24 : ℂ) * Work.Residues.Ept z ^ 4
    - (48 : ℂ) * Work.Residues.Ept z ^ 5 = dWpol z
  rw [dWpol, WrefHi_sub_Wref z, Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
  ring

private lemma bnd_dD2pol : FunnelBnd 0 3 (fun _ z => dD2pol z) := by
  refine (FunnelBnd.add (FunnelBnd.sub (FunnelBnd.cmul (448 : ℂ) (FunnelBnd.pow bnd_Ept 3))
      (FunnelBnd.mono_k (FunnelBnd.cmul (912 : ℂ) (FunnelBnd.pow bnd_Ept 4)) (by norm_num : 3 ≤ 4)))
    (FunnelBnd.mono_k (FunnelBnd.cmul (2016 : ℂ) (FunnelBnd.pow bnd_Ept 5)) (by norm_num : 3 ≤ 5))).congr_on
    (fun τ z t _ _ _ _ _ => ?_)
  show (448 : ℂ) * Work.Residues.Ept z ^ 3 - (912 : ℂ) * Work.Residues.Ept z ^ 4
    + (2016 : ℂ) * Work.Residues.Ept z ^ 5 = dD2pol z
  rw [dD2pol, D2refHi_sub_D2ref z, Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
  ring

private lemma bnd_dLpol (ℓ : Work.Kernels.LogLambdaData) : FunnelBnd 0 3 (fun _ z => dLpol ℓ z) := by
  refine (FunnelBnd.add (FunnelBnd.cmul (-(32 / 3) : ℂ) (FunnelBnd.pow bnd_Ept 3))
    (FunnelBnd.cmul (6 : ℂ) (FunnelBnd.pow bnd_Ept 4))).congr_on (fun τ z t _ _ _ _ _ => ?_)
  show (-(32 / 3) : ℂ) * Work.Residues.Ept z ^ 3 + (6 : ℂ) * Work.Residues.Ept z ^ 4
    = dLpol ℓ z
  rw [dLpol, LrefHi_sub_Lref ℓ z, Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
  ring

private lemma bnd_dW : FunnelBnd 0 3 (fun _ z => Work.Asymptotics.Compact.dW z) := by
  have h : FunnelBnd 0 3 (fun _ z => rW z + dWpol z) := FunnelBnd.add bnd_rW bnd_dWpol
  refine h.congr_on (fun τ z t _ _ _ _ _ => ?_)
  show rW z + dWpol z = Work.Asymptotics.Compact.dW z
  unfold rW dWpol Work.Asymptotics.Compact.dW Work.Asymptotics.Compact.Wref
  ring

private lemma bnd_dD2 : FunnelBnd 0 3 (fun _ z => Work.Asymptotics.Compact.dD2 z) := by
  have h : FunnelBnd 0 3 (fun _ z => rD2 z + dD2pol z) := FunnelBnd.add bnd_rD2 bnd_dD2pol
  refine h.congr_on (fun τ z t _ _ _ _ _ => ?_)
  show rD2 z + dD2pol z = Work.Asymptotics.Compact.dD2 z
  unfold rD2 dD2pol Work.Asymptotics.Compact.dD2 Work.Asymptotics.Compact.D2ref
  ring

private lemma bnd_dL (ℓ : Work.Kernels.LogLambdaData) :
    FunnelBnd 0 3 (fun _ z => Work.Asymptotics.Compact.dL ℓ z) := by
  have h : FunnelBnd 0 3 (fun _ z => rL ℓ z + dLpol ℓ z) := FunnelBnd.add (bnd_rL ℓ) (bnd_dLpol ℓ)
  refine h.congr_on (fun τ z t _ _ _ _ _ => ?_)
  show rL ℓ z + dLpol ℓ z = Work.Asymptotics.Compact.dL ℓ z
  unfold rL dLpol Work.Asymptotics.Compact.dL Work.Asymptotics.Compact.Lref
  ring

/-! ## The two deviation factors of `kdevNum0Rem` -/

private def KD1 (z : ℍ) : ℂ :=
  Work.Kernels.phitVec z 2 * (Work.Kernels.E4Fun z) ^ 2 - phit2Ztr z * (E4Ztr z) ^ 2

private def KD2 (z : ℍ) : ℂ :=
  Work.Kernels.phitVec z 1 * Work.Kernels.E4Fun z * Work.Kernels.E6Fun z
    - phit1Ztr z * E4Ztr z * E6Ztr z

private lemma KD1_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 3 ≤ z.im → -1 ≤ z.re → z.re ≤ 2 →
    ‖KD1 z‖ ≤ C * (1 + z.im) ^ 2 * ‖Work.Residues.Ept z‖ ^ 6 := by
  obtain ⟨C2, hC2, h2⟩ := dE2z_bound1
  obtain ⟨C4, hC4, h4⟩ := dE4z_bound1
  obtain ⟨CE4, hCE4, hE4⟩ := Work.Asymptotics.E4Fun_bound
  refine ⟨(4 * (194 + 6 / Real.pi) * C2 + 4 * C2 ^ 2) * CE4 ^ 2
      + (194 + 6 / Real.pi) ^ 2 * (C4 * (CE4 + 2401)), by positivity,
    fun z hz3 hre1 hre2 => ?_⟩
  have hz1 : (1 : ℝ) ≤ z.im := by linarith
  have him : (1 : ℝ) ≤ 1 + z.im := by linarith
  have hp6 : (0 : ℝ) ≤ 6 / Real.pi := by positivity
  have hzr : ‖(z : ℂ)‖ ≤ 2 * (1 + z.im) :=
    Work.Asymptotics.KhatE1.kdevA4_norm_z_le z z.im hre1 hre2 rfl
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := Ept_q_le_one hz1
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have Q3 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 := pow_nonneg hq0 _
  have hq3le : ‖Work.Kernels.qParamFun z‖ ^ 3 ≤ 1 := pow_le_one₀ hq0 hq1
  have hq32 : (‖Work.Kernels.qParamFun z‖ ^ 3) ^ 2 ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    nlinarith [Q3, hq3le]
  have hE4b : ‖Work.Kernels.E4Fun z‖ ≤ CE4 := hE4 z hz1
  have hE4sq : ‖(Work.Kernels.E4Fun z) ^ 2‖ ≤ CE4 ^ 2 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hE4b 2
  have hd2 := h2 z hz1
  have hd4 := h4 z hz1
  have hGt := GtTr_bound z hz1
  have hb2 : 97 * (2 * (1 + z.im)) + 6 / Real.pi ≤ (194 + 6 / Real.pi) * (1 + z.im) := by
    have hb1 : 6 / Real.pi ≤ 6 / Real.pi * (1 + z.im) := by nlinarith [hp6, him]
    nlinarith [hb1, hp6, him]
  have hDelta : ‖Work.Kernels.phitVec z 2 - phit2Ztr z‖
      ≤ (4 * (194 + 6 / Real.pi) * C2 + 4 * C2 ^ 2) * (1 + z.im) ^ 2
        * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    have hs : Work.Kernels.phitVec z 2 - phit2Ztr z
        = 2 * GtTr z * ((z : ℂ) * dE2z z) + ((z : ℂ) * dE2z z) ^ 2 := by
      rw [phitVec_two_split]; ring
    rw [hs]
    have hDz : ‖(z : ℂ) * dE2z z‖ ≤ 2 * (1 + z.im) * (C2 * ‖Work.Kernels.qParamFun z‖ ^ 3) := by
      rw [norm_mul]
      exact mul_le_mul hzr hd2 (norm_nonneg _) (by positivity)
    have h1 : ‖2 * GtTr z * ((z : ℂ) * dE2z z)‖
        ≤ 4 * (194 + 6 / Real.pi) * C2 * (1 + z.im) ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
      have hgt : 2 * ‖GtTr z‖ ≤ 2 * (97 * (2 * (1 + z.im)) + 6 / Real.pi) := by
        have h1 := mul_le_mul_of_nonneg_left hzr (by norm_num : (0 : ℝ) ≤ 97)
        linarith
      calc ‖2 * GtTr z * ((z : ℂ) * dE2z z)‖
          = 2 * ‖GtTr z‖ * ‖(z : ℂ) * dE2z z‖ := by
            simp only [norm_mul, Complex.norm_ofNat]
        _ ≤ 2 * (97 * (2 * (1 + z.im)) + 6 / Real.pi)
              * (2 * (1 + z.im) * (C2 * ‖Work.Kernels.qParamFun z‖ ^ 3)) :=
            mul_le_mul hgt hDz (norm_nonneg _) (by positivity)
        _ ≤ 4 * (194 + 6 / Real.pi) * C2 * (1 + z.im) ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
            have hmn : 2 * (97 * (2 * (1 + z.im)) + 6 / Real.pi)
                ≤ 2 * ((194 + 6 / Real.pi) * (1 + z.im)) := by linarith [hb2]
            calc 2 * (97 * (2 * (1 + z.im)) + 6 / Real.pi)
                  * (2 * (1 + z.im) * (C2 * ‖Work.Kernels.qParamFun z‖ ^ 3))
                ≤ 2 * ((194 + 6 / Real.pi) * (1 + z.im))
                  * (2 * (1 + z.im) * (C2 * ‖Work.Kernels.qParamFun z‖ ^ 3)) :=
                  mul_le_mul_of_nonneg_right hmn (by positivity)
              _ = 4 * (194 + 6 / Real.pi) * C2 * (1 + z.im) ^ 2
                  * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
    have h2' : ‖((z : ℂ) * dE2z z) ^ 2‖
        ≤ 4 * C2 ^ 2 * (1 + z.im) ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
      rw [norm_pow]
      have hsq : (2 * (1 + z.im) * (C2 * ‖Work.Kernels.qParamFun z‖ ^ 3)) ^ 2
          ≤ 4 * C2 ^ 2 * (1 + z.im) ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
        calc (2 * (1 + z.im) * (C2 * ‖Work.Kernels.qParamFun z‖ ^ 3)) ^ 2
            = 4 * C2 ^ 2 * (1 + z.im) ^ 2 * (‖Work.Kernels.qParamFun z‖ ^ 3) ^ 2 := by ring
          _ ≤ 4 * C2 ^ 2 * (1 + z.im) ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
              refine mul_le_mul_of_nonneg_left hq32 ?_
              positivity
      exact le_trans (pow_le_pow_left₀ (norm_nonneg _) hDz 2) hsq
    calc ‖2 * GtTr z * ((z : ℂ) * dE2z z) + ((z : ℂ) * dE2z z) ^ 2‖
        ≤ ‖2 * GtTr z * ((z : ℂ) * dE2z z)‖ + ‖((z : ℂ) * dE2z z) ^ 2‖ := norm_add_le _ _
      _ ≤ 4 * (194 + 6 / Real.pi) * C2 * (1 + z.im) ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3
          + 4 * C2 ^ 2 * (1 + z.im) ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3 :=
          add_le_add h1 h2'
      _ = (4 * (194 + 6 / Real.pi) * C2 + 4 * C2 ^ 2) * (1 + z.im) ^ 2
          * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
  have hphit2 : ‖phit2Ztr z‖ ≤ (194 + 6 / Real.pi) ^ 2 * (1 + z.im) ^ 2 := by
    have hb1 := phit2Ztr_bound z hz1
    have hgt : 97 * ‖(z : ℂ)‖ + 6 / Real.pi ≤ (194 + 6 / Real.pi) * (1 + z.im) := by
      nlinarith [hzr, hp6, him]
    calc ‖phit2Ztr z‖ ≤ (97 * ‖(z : ℂ)‖ + 6 / Real.pi) ^ 2 := hb1
      _ ≤ ((194 + 6 / Real.pi) * (1 + z.im)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hgt 2
      _ = (194 + 6 / Real.pi) ^ 2 * (1 + z.im) ^ 2 := by ring
  have hdev4 : ‖(Work.Kernels.E4Fun z) ^ 2 - (E4Ztr z) ^ 2‖
      ≤ C4 * (CE4 + 2401) * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    have hkey : (Work.Kernels.E4Fun z) ^ 2 - (E4Ztr z) ^ 2
        = dE4z z * (Work.Kernels.E4Fun z + E4Ztr z) := by
      rw [show (Work.Kernels.E4Fun z) ^ 2 - (E4Ztr z) ^ 2
          = (Work.Kernels.E4Fun z - E4Ztr z) * (Work.Kernels.E4Fun z + E4Ztr z) by ring]
      rfl
    rw [hkey, norm_mul]
    have hsum : ‖Work.Kernels.E4Fun z + E4Ztr z‖ ≤ CE4 + 2401 := by
      have h1 := norm_add_le (Work.Kernels.E4Fun z) (E4Ztr z)
      have hz4 := E4Ztr_bound z hz1
      linarith
    calc ‖dE4z z‖ * ‖Work.Kernels.E4Fun z + E4Ztr z‖
        ≤ (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) * (CE4 + 2401) :=
          mul_le_mul hd4 hsum (norm_nonneg _) (by positivity)
      _ = C4 * (CE4 + 2401) * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
  have hsplit : KD1 z = (Work.Kernels.phitVec z 2 - phit2Ztr z) * (Work.Kernels.E4Fun z) ^ 2
      + phit2Ztr z * ((Work.Kernels.E4Fun z) ^ 2 - (E4Ztr z) ^ 2) := by
    rw [KD1]; ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have hA : ‖(Work.Kernels.phitVec z 2 - phit2Ztr z) * (Work.Kernels.E4Fun z) ^ 2‖
      ≤ ((4 * (194 + 6 / Real.pi) * C2 + 4 * C2 ^ 2) * (1 + z.im) ^ 2
          * ‖Work.Kernels.qParamFun z‖ ^ 3) * CE4 ^ 2 := by
    rw [norm_mul]
    exact mul_le_mul hDelta hE4sq (norm_nonneg _) (by positivity)
  have hB : ‖phit2Ztr z * ((Work.Kernels.E4Fun z) ^ 2 - (E4Ztr z) ^ 2)‖
      ≤ ((194 + 6 / Real.pi) ^ 2 * (1 + z.im) ^ 2)
          * (C4 * (CE4 + 2401) * ‖Work.Kernels.qParamFun z‖ ^ 3) := by
    rw [norm_mul]
    exact mul_le_mul hphit2 hdev4 (norm_nonneg _) (by positivity)
  refine le_trans (add_le_add hA hB) ?_
  have hEpt6 : ‖Work.Residues.Ept z‖ ^ 6 = ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    rw [Work.Asymptotics.Small.qParamFun_eq_Ept_sq z, norm_pow]; ring
  rw [hEpt6]
  have heq : ((4 * (194 + 6 / Real.pi) * C2 + 4 * C2 ^ 2) * (1 + z.im) ^ 2
        * ‖Work.Kernels.qParamFun z‖ ^ 3) * CE4 ^ 2
      + ((194 + 6 / Real.pi) ^ 2 * (1 + z.im) ^ 2)
        * (C4 * (CE4 + 2401) * ‖Work.Kernels.qParamFun z‖ ^ 3)
      = ((4 * (194 + 6 / Real.pi) * C2 + 4 * C2 ^ 2) * CE4 ^ 2
        + (194 + 6 / Real.pi) ^ 2 * (C4 * (CE4 + 2401))) * (1 + z.im) ^ 2
        * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
  linarith [heq]

private lemma KD2_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 3 ≤ z.im → -1 ≤ z.re → z.re ≤ 2 →
    ‖KD2 z‖ ≤ C * (1 + z.im) ^ 2 * ‖Work.Residues.Ept z‖ ^ 6 := by
  obtain ⟨C2, hC2, h2⟩ := dE2z_bound1
  obtain ⟨C4, hC4, h4⟩ := dE4z_bound1
  obtain ⟨C6, hC6, h6⟩ := dE6z_bound1
  obtain ⟨CE4, hCE4, hE4⟩ := Work.Asymptotics.E4Fun_bound
  obtain ⟨CE6, hCE6, hE6⟩ := Work.Asymptotics.E6Fun_bound
  refine ⟨4 * C2 * (CE4 * CE6) + 2 * (194 + 6 / Real.pi) * (C4 * CE6 + 2401 * C6),
    by positivity, fun z hz3 hre1 hre2 => ?_⟩
  have hz1 : (1 : ℝ) ≤ z.im := by linarith
  have him : (1 : ℝ) ≤ 1 + z.im := by linarith
  have hp6 : (0 : ℝ) ≤ 6 / Real.pi := by positivity
  have hzr : ‖(z : ℂ)‖ ≤ 2 * (1 + z.im) :=
    Work.Asymptotics.KhatE1.kdevA4_norm_z_le z z.im hre1 hre2 rfl
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := Ept_q_le_one hz1
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have Q3 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 := pow_nonneg hq0 _
  have hE4b : ‖Work.Kernels.E4Fun z‖ ≤ CE4 := hE4 z hz1
  have hE6b : ‖Work.Kernels.E6Fun z‖ ≤ CE6 := hE6 z hz1
  have hd2 := h2 z hz1
  have hd4 := h4 z hz1
  have hd6 := h6 z hz1
  have hGt := GtTr_bound z hz1
  -- factor 1
  have hF1 : ‖Work.Kernels.phitVec z 1 - phit1Ztr z‖
      ≤ 4 * C2 * (1 + z.im) ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    have hs : Work.Kernels.phitVec z 1 - phit1Ztr z = (z : ℂ) * ((z : ℂ) * dE2z z) := by
      rw [phitVec_one_split]; ring
    rw [hs]
    have hDz : ‖(z : ℂ) * dE2z z‖ ≤ 2 * (1 + z.im) * (C2 * ‖Work.Kernels.qParamFun z‖ ^ 3) := by
      rw [norm_mul]
      exact mul_le_mul hzr hd2 (norm_nonneg _) (by positivity)
    calc ‖(z : ℂ) * ((z : ℂ) * dE2z z)‖ = ‖(z : ℂ)‖ * ‖(z : ℂ) * dE2z z‖ := norm_mul _ _
      _ ≤ (2 * (1 + z.im)) * (2 * (1 + z.im) * (C2 * ‖Work.Kernels.qParamFun z‖ ^ 3)) :=
          mul_le_mul hzr hDz (norm_nonneg _) (by positivity)
      _ = 4 * C2 * (1 + z.im) ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
  have hE4E6 : ‖Work.Kernels.E4Fun z * Work.Kernels.E6Fun z‖ ≤ CE4 * CE6 := by
    rw [norm_mul]; exact mul_le_mul hE4b hE6b (norm_nonneg _) (by positivity)
  have hphit1 : ‖phit1Ztr z‖ ≤ 2 * (194 + 6 / Real.pi) * (1 + z.im) ^ 2 := by
    have hb1 := phit1Ztr_bound z hz1
    have hgt : 97 * ‖(z : ℂ)‖ + 6 / Real.pi ≤ (194 + 6 / Real.pi) * (1 + z.im) := by
      nlinarith [hzr, hp6, him]
    calc ‖phit1Ztr z‖ ≤ ‖(z : ℂ)‖ * (97 * ‖(z : ℂ)‖ + 6 / Real.pi) := hb1
      _ ≤ (2 * (1 + z.im)) * ((194 + 6 / Real.pi) * (1 + z.im)) :=
          mul_le_mul hzr hgt (by positivity) (by positivity)
      _ = 2 * (194 + 6 / Real.pi) * (1 + z.im) ^ 2 := by ring
  have hdev3 : ‖Work.Kernels.E4Fun z * Work.Kernels.E6Fun z - E4Ztr z * E6Ztr z‖
      ≤ (C4 * CE6 + 2401 * C6) * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    have hkey : Work.Kernels.E4Fun z * Work.Kernels.E6Fun z - E4Ztr z * E6Ztr z
        = dE4z z * Work.Kernels.E6Fun z + E4Ztr z * dE6z z := by
      rw [E4Fun_eq_trunc_add z, E6Fun_eq_trunc_add z]; ring
    rw [hkey]
    have hz4 := E4Ztr_bound z hz1
    calc ‖dE4z z * Work.Kernels.E6Fun z + E4Ztr z * dE6z z‖
        ≤ ‖dE4z z * Work.Kernels.E6Fun z‖ + ‖E4Ztr z * dE6z z‖ := norm_add_le _ _
      _ ≤ (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) * CE6
            + 2401 * (C6 * ‖Work.Kernels.qParamFun z‖ ^ 3) := by
          refine add_le_add ?_ ?_
          · rw [norm_mul]; exact mul_le_mul hd4 hE6b (norm_nonneg _) (by positivity)
          · rw [norm_mul]; exact mul_le_mul hz4 hd6 (norm_nonneg _) (by positivity)
      _ = (C4 * CE6 + 2401 * C6) * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
  have hsplit : KD2 z = (Work.Kernels.phitVec z 1 - phit1Ztr z)
        * (Work.Kernels.E4Fun z * Work.Kernels.E6Fun z)
      + phit1Ztr z * (Work.Kernels.E4Fun z * Work.Kernels.E6Fun z - E4Ztr z * E6Ztr z) := by
    rw [KD2]; ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have hA : ‖(Work.Kernels.phitVec z 1 - phit1Ztr z)
        * (Work.Kernels.E4Fun z * Work.Kernels.E6Fun z)‖
      ≤ (4 * C2 * (1 + z.im) ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3) * (CE4 * CE6) := by
    rw [norm_mul]
    exact mul_le_mul hF1 hE4E6 (norm_nonneg _) (by positivity)
  have hB : ‖phit1Ztr z * (Work.Kernels.E4Fun z * Work.Kernels.E6Fun z - E4Ztr z * E6Ztr z)‖
      ≤ (2 * (194 + 6 / Real.pi) * (1 + z.im) ^ 2)
          * ((C4 * CE6 + 2401 * C6) * ‖Work.Kernels.qParamFun z‖ ^ 3) := by
    rw [norm_mul]
    exact mul_le_mul hphit1 hdev3 (norm_nonneg _) (by positivity)
  refine le_trans (add_le_add hA hB) ?_
  have hEpt6 : ‖Work.Residues.Ept z‖ ^ 6 = ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    rw [Work.Asymptotics.Small.qParamFun_eq_Ept_sq z, norm_pow]; ring
  rw [hEpt6]
  have heq : (4 * C2 * (1 + z.im) ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3) * (CE4 * CE6)
      + (2 * (194 + 6 / Real.pi) * (1 + z.im) ^ 2)
        * ((C4 * CE6 + 2401 * C6) * ‖Work.Kernels.qParamFun z‖ ^ 3)
      = (4 * C2 * (CE4 * CE6) + 2 * (194 + 6 / Real.pi) * (C4 * CE6 + 2401 * C6))
        * (1 + z.im) ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
  linarith [heq]

private lemma bnd_KD1 : FunnelBnd 0 6 (fun _ z => KD1 z) := by
  obtain ⟨C, hC, h⟩ := KD1_bound
  exact FunnelBnd.ofZ_u2 hC h

private lemma bnd_KD2 : FunnelBnd 0 6 (fun _ z => KD2 z) := by
  obtain ⟨C, hC, h⟩ := KD2_bound
  exact FunnelBnd.ofZ_u2 hC h

/-! ## The assembly -/

private def DevRemS1 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -3456 * Work.Kernels.E4Fun τ * Work.Asymptotics.Compact.E10ref z * rL ℓ z
    + -3456 * Work.Kernels.E4Fun τ * rE10 z * Work.Asymptotics.Compact.Lref ℓ z
    + -3456 * Work.Kernels.E4Fun τ * (rE10 z * Work.Asymptotics.Compact.dL ℓ z
          + dE10pol z * rL ℓ z)

private def DevRemTB (z : ℍ) : ℂ :=
  (Work.Asymptotics.Compact.E8ref z * rW z - Work.Asymptotics.Compact.E6ref z * rD2 z)
    + (rE8 z * Work.Asymptotics.Compact.Wref z - rE6 z * Work.Asymptotics.Compact.D2ref z)
    + (rE8 z * Work.Asymptotics.Compact.dW z + dE8pol z * rW z
        - rE6 z * Work.Asymptotics.Compact.dD2 z - dE6pol z * rD2 z)

private def DevRemTC (τ z : ℍ) : ℂ :=
  ((1728 * Work.Kernels.DeltaFun τ - Work.Kernels.E4Fun τ ^ 3)
        * Work.Asymptotics.Compact.E8ref z * rW z
      + Work.Kernels.E4Fun τ ^ 3 * Work.Asymptotics.Compact.E6ref z * rD2 z)
    + ((1728 * Work.Kernels.DeltaFun τ - Work.Kernels.E4Fun τ ^ 3)
        * rE8 z * Work.Asymptotics.Compact.Wref z
      + Work.Kernels.E4Fun τ ^ 3 * rE6 z * Work.Asymptotics.Compact.D2ref z)
    + ((1728 * Work.Kernels.DeltaFun τ - Work.Kernels.E4Fun τ ^ 3)
        * (rE8 z * Work.Asymptotics.Compact.dW z + dE8pol z * rW z)
      + Work.Kernels.E4Fun τ ^ 3
        * (rE6 z * Work.Asymptotics.Compact.dD2 z + dE6pol z * rD2 z))

private theorem Dev8Rem_eq_parts (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Dev8Rem ℓ τ z = Work.Kernels.DeltaFun τ * DevRemS1 ℓ τ z
      + Work.Kernels.psi2 ℓ τ * Work.Kernels.E14Fun τ * DevRemTB z
      + Work.Kernels.psi4 ℓ τ * DevRemTC τ z := by
  rw [Dev8Rem, DevRemS1, DevRemTB, DevRemTC]
  ring

private lemma bnd_S1 (ℓ : Work.Kernels.LogLambdaData) :
    FunnelBnd 0 5 (fun τ z => DevRemS1 ℓ τ z) := by
  have hA : FunnelBnd 0 5 (fun τ z => -3456 * Work.Kernels.E4Fun τ
      * Work.Asymptotics.Compact.E10ref z * rL ℓ z) :=
    FunnelBnd.mul (FunnelBnd.mul (FunnelBnd.cmul (-3456) bnd_E4) bnd_E10ref) (bnd_rL ℓ)
  have hB : FunnelBnd 0 6 (fun τ z => -3456 * Work.Kernels.E4Fun τ
      * rE10 z * Work.Asymptotics.Compact.Lref ℓ z) :=
    FunnelBnd.mul (FunnelBnd.mul (FunnelBnd.cmul (-3456) bnd_E4) bnd_rE10) (bnd_Lref ℓ)
  have hC : FunnelBnd 0 9 (fun τ z => -3456 * Work.Kernels.E4Fun τ
      * (rE10 z * Work.Asymptotics.Compact.dL ℓ z + dE10pol z * rL ℓ z)) :=
    FunnelBnd.mul (FunnelBnd.cmul (-3456) bnd_E4)
      (FunnelBnd.add (FunnelBnd.mul bnd_rE10 (bnd_dL ℓ)) (FunnelBnd.mul bnd_dE10pol (bnd_rL ℓ)))
  exact FunnelBnd.add (FunnelBnd.add hA hB) hC

private lemma bnd_TB : FunnelBnd 0 6 (fun _ z => DevRemTB z) := by
  have ha : FunnelBnd 0 6 (fun _ z => Work.Asymptotics.Compact.E8ref z * rW z) :=
    FunnelBnd.mul bnd_E8ref bnd_rW
  have hb : FunnelBnd 0 6 (fun _ z => Work.Asymptotics.Compact.E6ref z * rD2 z) :=
    FunnelBnd.mul bnd_E6ref bnd_rD2
  have hc : FunnelBnd 0 6 (fun _ z => rE8 z * Work.Asymptotics.Compact.Wref z) :=
    FunnelBnd.mul bnd_rE8 bnd_Wref
  have hd : FunnelBnd 0 6 (fun _ z => rE6 z * Work.Asymptotics.Compact.D2ref z) :=
    FunnelBnd.mul bnd_rE6 bnd_D2ref
  have he : FunnelBnd 0 9 (fun _ z => rE8 z * Work.Asymptotics.Compact.dW z) :=
    FunnelBnd.mul bnd_rE8 bnd_dW
  have hf : FunnelBnd 0 10 (fun _ z => dE8pol z * rW z) := FunnelBnd.mul bnd_dE8pol bnd_rW
  have hg : FunnelBnd 0 9 (fun _ z => rE6 z * Work.Asymptotics.Compact.dD2 z) :=
    FunnelBnd.mul bnd_rE6 bnd_dD2
  have hh : FunnelBnd 0 10 (fun _ z => dE6pol z * rD2 z) := FunnelBnd.mul bnd_dE6pol bnd_rD2
  have h3 : FunnelBnd 0 9 (fun _ z => rE8 z * Work.Asymptotics.Compact.dW z
      + dE8pol z * rW z - rE6 z * Work.Asymptotics.Compact.dD2 z
      - dE6pol z * rD2 z) :=
    FunnelBnd.sub (FunnelBnd.sub (FunnelBnd.add he hf) hg) (FunnelBnd.mono_k hh (by norm_num))
  exact FunnelBnd.add (FunnelBnd.add (FunnelBnd.sub ha hb) (FunnelBnd.sub hc hd)) h3

private lemma bnd_TC : FunnelBnd 0 6 (fun τ z => DevRemTC τ z) := by
  have hX : FunnelBnd 0 0 (fun τ _ => 1728 * Work.Kernels.DeltaFun τ - Work.Kernels.E4Fun τ ^ 3) :=
    FunnelBnd.sub (FunnelBnd.mono_e (FunnelBnd.cmul 1728 bnd_Delta) (by norm_num : 0 ≤ 1)) (FunnelBnd.pow bnd_E4 3)
  have hp4 : FunnelBnd 0 0 (fun τ _ => Work.Kernels.E4Fun τ ^ 3) := FunnelBnd.pow bnd_E4 3
  have ht1a : FunnelBnd 0 6 (fun τ z => (1728 * Work.Kernels.DeltaFun τ - Work.Kernels.E4Fun τ ^ 3)
      * Work.Asymptotics.Compact.E8ref z * rW z) := FunnelBnd.mul (FunnelBnd.mul hX bnd_E8ref) bnd_rW
  have ht1b : FunnelBnd 0 6 (fun τ z => Work.Kernels.E4Fun τ ^ 3
      * Work.Asymptotics.Compact.E6ref z * rD2 z) := FunnelBnd.mul (FunnelBnd.mul hp4 bnd_E6ref) bnd_rD2
  have hs1 : FunnelBnd 0 6 (fun τ z => (1728 * Work.Kernels.DeltaFun τ - Work.Kernels.E4Fun τ ^ 3)
        * Work.Asymptotics.Compact.E8ref z * rW z
      + Work.Kernels.E4Fun τ ^ 3 * Work.Asymptotics.Compact.E6ref z * rD2 z) :=
    FunnelBnd.add ht1a ht1b
  have ht2a : FunnelBnd 0 6 (fun τ z => (1728 * Work.Kernels.DeltaFun τ - Work.Kernels.E4Fun τ ^ 3)
      * rE8 z * Work.Asymptotics.Compact.Wref z) := FunnelBnd.mul (FunnelBnd.mul hX bnd_rE8) bnd_Wref
  have ht2b : FunnelBnd 0 6 (fun τ z => Work.Kernels.E4Fun τ ^ 3
      * rE6 z * Work.Asymptotics.Compact.D2ref z) := FunnelBnd.mul (FunnelBnd.mul hp4 bnd_rE6) bnd_D2ref
  have hs2 : FunnelBnd 0 6 (fun τ z => (1728 * Work.Kernels.DeltaFun τ - Work.Kernels.E4Fun τ ^ 3)
        * rE8 z * Work.Asymptotics.Compact.Wref z
      + Work.Kernels.E4Fun τ ^ 3 * rE6 z * Work.Asymptotics.Compact.D2ref z) :=
    FunnelBnd.add ht2a ht2b
  have ht3a : FunnelBnd 0 9 (fun τ z => (1728 * Work.Kernels.DeltaFun τ - Work.Kernels.E4Fun τ ^ 3)
      * (rE8 z * Work.Asymptotics.Compact.dW z + dE8pol z * rW z)) :=
    FunnelBnd.mul hX (FunnelBnd.add (FunnelBnd.mul bnd_rE8 bnd_dW) (FunnelBnd.mul bnd_dE8pol bnd_rW))
  have ht3b : FunnelBnd 0 9 (fun τ z => Work.Kernels.E4Fun τ ^ 3
      * (rE6 z * Work.Asymptotics.Compact.dD2 z + dE6pol z * rD2 z)) :=
    FunnelBnd.mul hp4 (FunnelBnd.add (FunnelBnd.mul bnd_rE6 bnd_dD2) (FunnelBnd.mul bnd_dE6pol bnd_rD2))
  have hs3 : FunnelBnd 0 9 (fun τ z => (1728 * Work.Kernels.DeltaFun τ - Work.Kernels.E4Fun τ ^ 3)
        * (rE8 z * Work.Asymptotics.Compact.dW z + dE8pol z * rW z)
      + Work.Kernels.E4Fun τ ^ 3
        * (rE6 z * Work.Asymptotics.Compact.dD2 z + dE6pol z * rD2 z)) :=
    FunnelBnd.add ht3a ht3b
  exact FunnelBnd.add (FunnelBnd.add hs1 hs2) hs3

private lemma kdevNum0Rem_eq_KD (τ z : ℍ) :
    kdevNum0Rem τ z = (τ : ℂ) * Work.Kernels.E6Fun τ * KD1 z
      - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * KD2 z := by
  rw [kdevNum0Rem, KD1, KD2]

private theorem bnd_WresPolyDevRem (ℓ : Work.Kernels.LogLambdaData) :
    FunnelBnd 3 2 (fun τ z => WresPolyDevRem ℓ τ z) := by
  have hT1 : FunnelBnd 3 2 (fun τ z => ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
      * (Work.Kernels.DeltaFun τ * (Work.Kernels.DeltaFun τ * DevRemS1 ℓ τ z))) :=
    Bnd_up (FunnelBnd.cmul ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
      (FunnelBnd.mul bnd_Delta (FunnelBnd.mul bnd_Delta (bnd_S1 ℓ)))) (by norm_num) (by norm_num)
  have hT2 : FunnelBnd 3 2 (fun τ z => ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
      * (Work.Kernels.DeltaFun τ
        * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E14Fun τ * DevRemTB z))) :=
    Bnd_up (FunnelBnd.cmul ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
      (FunnelBnd.mul bnd_Delta (FunnelBnd.mul (FunnelBnd.mul (bnd_psi2 ℓ) bnd_E14) bnd_TB)))
      (by norm_num) (by norm_num)
  have hT3 : FunnelBnd 3 2 (fun τ z => ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
      * (Work.Kernels.DeltaFun τ * (Work.Kernels.psi4 ℓ τ * DevRemTC τ z))) :=
    Bnd_up (FunnelBnd.cmul ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
      (FunnelBnd.mul bnd_Delta (FunnelBnd.mul (bnd_psi4 ℓ) bnd_TC))) (by norm_num) (by norm_num)
  have hSum : FunnelBnd 3 2 (fun τ z => ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
      * (Work.Kernels.DeltaFun τ * Dev8Rem ℓ τ z)) :=
    (FunnelBnd.add (FunnelBnd.add hT1 hT2) hT3).congr_on (fun τ z t hτ ht ha hb hzt => by
      rw [Dev8Rem_eq_parts ℓ τ z]; ring)
  have hK1 : FunnelBnd 2 6 (fun τ z => Work.Kernels.DeltaFun τ * (Work.Kernels.DeltaFun τ
      * ((τ : ℂ) * Work.Kernels.E6Fun τ * KD1 z))) :=
    FunnelBnd.mul bnd_Delta (FunnelBnd.mul bnd_Delta (FunnelBnd.mul (FunnelBnd.mul bnd_tau bnd_E6) bnd_KD1))
  have hK2 : FunnelBnd 2 6 (fun τ z => Work.Kernels.DeltaFun τ * (Work.Kernels.DeltaFun τ
      * (2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * KD2 z))) :=
    FunnelBnd.mul bnd_Delta (FunnelBnd.mul bnd_Delta
      (FunnelBnd.mul (FunnelBnd.mul (FunnelBnd.cmul 2 bnd_phi0) bnd_E4) bnd_KD2))
  have hK : FunnelBnd 3 2 (fun τ z => Work.Asymptotics.Compact.tailC⁻¹
      * (Work.Kernels.DeltaFun τ * (Work.Kernels.DeltaFun τ * kdevNum0Rem τ z))) := by
    have hsub : FunnelBnd 2 6 (fun τ z => Work.Kernels.DeltaFun τ * (Work.Kernels.DeltaFun τ
        * ((τ : ℂ) * Work.Kernels.E6Fun τ * KD1 z
            - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * KD2 z))) :=
      (FunnelBnd.sub hK1 hK2).congr_on (fun τ z t _ _ _ _ _ => by ring)
    refine Bnd_up (FunnelBnd.cmul (Work.Asymptotics.Compact.tailC⁻¹) hsub) (by norm_num) (by norm_num)
  have hD : FunnelBnd 3 2 (fun τ z => ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
      * (Work.Kernels.DeltaFun τ * Dev8Rem ℓ τ z)
      - Work.Asymptotics.Compact.tailC⁻¹
        * (Work.Kernels.DeltaFun τ * (Work.Kernels.DeltaFun τ * kdevNum0Rem τ z))) :=
    FunnelBnd.sub hSum hK
  exact hD.congr_on (fun τ z t _ _ _ _ _ => by rw [WresPolyDevRem]; ring)

end

theorem Kdev8WresPolyDevBound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1.WresPolyDevRem ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
              * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
  simpa only [FunnelBnd] using bnd_WresPolyDevRem ℓ

end Work.Asymptotics.KhatE1
