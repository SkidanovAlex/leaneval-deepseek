import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.BigCalc
import Submission.Work.Asymptotics.KhatE1Sharp.KdevA3_bound
import Submission.Work.Asymptotics.KhatE1Core.E1combo8_second_order
import Submission.Work.Asymptotics.KhatE1Core.psi_second_order
import Submission.Work.Asymptotics.KhatE1Sharp.Kdev8WresTailPoly
import Submission.Work.Asymptotics.KhatE1.KdevA4Sharp
import Submission.Work.Asymptotics.KhatE1.KdevA5Sharp
import Submission.Work.Asymptotics.KhatE1.KdevE2_strip_bound
import Submission.Work.Asymptotics.KhatE1.E1combo8_bound
import Submission.Work.Asymptotics.KhatE1Sharp.Kdev8WresZAtoms
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.KhatE1.KdevA4Book

/-!
# The polynomial part of the cleared sharp residual is `O(‖q(τ)‖³‖Ept z‖²(scale τ)^N(1+t)^M)`

This file proves the `WresPoly` estimate needed by
`KhatE1Core.Kdev8WresAssembly.Kdev8Bracket_tail_of_WresBounds`.

The central device is the predicate `Bd p F` (`‖F τ z‖ ≤ C‖q(τ)‖^p(scale τ)^N(1+t)^M` on the
funnel strip) with its multiplicative/additive calculus, together with the atom instances.  The
`u`-coefficients `p_k` of `WresPolyPol` (`u = Ept z`) are then bounded by

* `p₃ = Δ²·KdevA3`          → `Bd 3`,
* `p₄ = Δ²·KdevA4`          → `Bd 2`,
* `p₅` (combined `ψ`-pair)   → `Bd 2`,
* `p₆, …, p₁₆`              → `Bd 1`,

and the sum `Σ_k p_k u^k` is bounded using `‖u‖² ≤ ‖q(τ)‖`, `‖u‖³ ≤ ‖q(τ)‖^{3/2}`.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

set_option maxHeartbeats 8000000

open Work.Kernels

/-- **The strip bound predicate.**  `Bd p F` means: on the funnel strip
(`Funnel τ`, `τ.im + 1 ≤ t`, `-1 ≤ z.re ≤ 2`, `z.im = t`),

  `‖F τ z‖ ≤ C · ‖q(τ)‖^p · (scale τ)^N · (1+t)^M`.

Larger `p` is a stronger statement, since `‖q(τ)‖ ≤ 1` on the funnel. -/
def Bd (p : ℕ) (F : ℍ → ℍ → ℂ) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t → -1 ≤ z.re → z.re ≤ 2 →
      z.im = t → ‖F τ z‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ p
        * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M

namespace Bd

lemma one_le_one_add_t (τ : ℍ) (t : ℝ) (hτ : Work.Asymptotics.Funnel τ)
    (ht : τ.im + 1 ≤ t) : (1 : ℝ) ≤ 1 + t := by
  have h2 : (2 : ℝ) ≤ τ.im := hτ.2
  linarith

lemma S_nonneg (τ : ℍ) (N : ℝ) : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N :=
  Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N

lemma q_nonneg (τ : ℍ) : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _

lemma q_le_one (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) :
    ‖Work.Kernels.qParamFun τ‖ ≤ 1 :=
  Work.Asymptotics.KhatE1Core.Big.qnorm_le_one τ hτ

/-- Monotonicity in the `q`-exponent: a stronger (larger) exponent implies a weaker one. -/
lemma mono {p q : ℕ} {F : ℍ → ℍ → ℂ} (h : Bd p F) (hpq : q ≤ p) : Bd q F := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hτ ht ha hb' hzt => ?_⟩
  refine le_trans (hb τ z t hτ ht ha hb' hzt) ?_
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := q_nonneg τ
  have hq1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := q_le_one τ hτ
  have hle : ‖Work.Kernels.qParamFun τ‖ ^ p ≤ ‖Work.Kernels.qParamFun τ‖ ^ q :=
    pow_le_pow_of_le_one hq0 hq1 hpq
  have hR0 : (0 : ℝ) ≤ (1 + t) ^ M :=
    Real.rpow_nonneg (le_trans zero_le_one (one_le_one_add_t τ t hτ ht)) M
  have hS0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N := S_nonneg τ N
  calc C * ‖Work.Kernels.qParamFun τ‖ ^ p * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
      = (C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M) * ‖Work.Kernels.qParamFun τ‖ ^ p := by
        ring
    _ ≤ (C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M) * ‖Work.Kernels.qParamFun τ‖ ^ q :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = C * ‖Work.Kernels.qParamFun τ‖ ^ q * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
        ring

/-- `Bd` is invariant under pointwise equality on the strip. -/
lemma congr_on {p : ℕ} {F G : ℍ → ℍ → ℂ} (h : Bd p F)
    (hFG : ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t → -1 ≤ z.re →
      z.re ≤ 2 → z.im = t → F τ z = G τ z) : Bd p G := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  exact ⟨C, N, M, hC, hN, hM, fun τ z t hτ ht ha hb' hzt => by
    rw [← hFG τ z t hτ ht ha hb' hzt]; exact hb τ z t hτ ht ha hb' hzt⟩

/-- Constants. -/
lemma const (c : ℂ) : Bd 0 (fun _ _ => c) :=
  ⟨‖c‖ + 1, 0, 0, by positivity, le_rfl, le_rfl, fun τ z t _ _ _ _ _ => by
    rw [Real.rpow_zero, Real.rpow_zero, pow_zero]
    nlinarith [norm_nonneg c]⟩

lemma one : Bd 0 (fun _ _ => (1 : ℂ)) := by
  simpa using const (1 : ℂ)

lemma neg {p : ℕ} {F : ℍ → ℍ → ℂ} (h : Bd p F) : Bd p (fun τ z => -F τ z) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  exact ⟨C, N, M, hC, hN, hM, fun τ z t hτ ht ha hb' hzt => by
    rw [norm_neg]; exact hb τ z t hτ ht ha hb' hzt⟩

lemma cmul (c : ℂ) {p : ℕ} {F : ℍ → ℍ → ℂ} (h : Bd p F) :
    Bd p (fun τ z => c * F τ z) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨(‖c‖ + 1) * (C + 1), N, M, by positivity, hN, hM,
    fun τ z t hτ ht ha hb' hzt => ?_⟩
  have hR : (1 : ℝ) ≤ 1 + t := one_le_one_add_t τ t hτ ht
  have hcoef : ‖c‖ * C ≤ (‖c‖ + 1) * (C + 1) := by nlinarith [norm_nonneg c, hC]
  have hS0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N := S_nonneg τ N
  have hR0 : (0 : ℝ) ≤ (1 + t) ^ M := Real.rpow_nonneg (le_trans zero_le_one hR) M
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ p :=
    pow_nonneg (q_nonneg τ) p
  rw [norm_mul]
  calc ‖c‖ * ‖F τ z‖
      ≤ ‖c‖ * (C * ‖Work.Kernels.qParamFun τ‖ ^ p
          * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M) :=
        mul_le_mul_of_nonneg_left (hb τ z t hτ ht ha hb' hzt) (norm_nonneg c)
    _ = (‖c‖ * C) * (‖Work.Kernels.qParamFun τ‖ ^ p * (Work.Kernels.scale τ) ^ N
          * (1 + t) ^ M) := by ring
    _ ≤ ((‖c‖ + 1) * (C + 1)) * (‖Work.Kernels.qParamFun τ‖ ^ p
          * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = (‖c‖ + 1) * (C + 1) * ‖Work.Kernels.qParamFun τ‖ ^ p
          * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by ring

lemma add {p q : ℕ} {F G : ℍ → ℍ → ℂ} (hF : Bd p F) (hG : Bd q G) :
    Bd (min p q) (fun τ z => F τ z + G τ z) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, h1⟩ := hF
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, h2⟩ := hG
  refine ⟨C1 + C2, max N1 N2, max M1 M2, by positivity, le_max_of_le_left hN1,
    le_max_of_le_left hM1, fun τ z t hτ ht ha hb hzt => ?_⟩
  have hS1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hR : (1 : ℝ) ≤ 1 + t := one_le_one_add_t τ t hτ ht
  have e1S : (Work.Kernels.scale τ) ^ N1 ≤ (Work.Kernels.scale τ) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hS1 (le_max_left _ _)
  have e2S : (Work.Kernels.scale τ) ^ N2 ≤ (Work.Kernels.scale τ) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hS1 (le_max_right _ _)
  have e1R : (1 + t) ^ M1 ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le hR (le_max_left _ _)
  have e2R : (1 + t) ^ M2 ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le hR (le_max_right _ _)
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := q_nonneg τ
  have hq1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := q_le_one τ hτ
  have hqp : ‖Work.Kernels.qParamFun τ‖ ^ p ≤ ‖Work.Kernels.qParamFun τ‖ ^ min p q :=
    pow_le_pow_of_le_one hq0 hq1 (min_le_left _ _)
  have hqq : ‖Work.Kernels.qParamFun τ‖ ^ q ≤ ‖Work.Kernels.qParamFun τ‖ ^ min p q :=
    pow_le_pow_of_le_one hq0 hq1 (min_le_right _ _)
  have hSmax : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ (max N1 N2) := S_nonneg τ _
  have hRmax : (0 : ℝ) ≤ (1 + t) ^ (max M1 M2) := Real.rpow_nonneg (le_trans zero_le_one hR) _
  have hS1n : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N1 := S_nonneg τ N1
  have hR1n : (0 : ℝ) ≤ (1 + t) ^ M1 := Real.rpow_nonneg (le_trans zero_le_one hR) M1
  have hS2n : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N2 := S_nonneg τ N2
  have hR2n : (0 : ℝ) ≤ (1 + t) ^ M2 := Real.rpow_nonneg (le_trans zero_le_one hR) M2
  have A1 : ‖F τ z‖ ≤ C1 * ‖Work.Kernels.qParamFun τ‖ ^ min p q
      * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) := by
    refine le_trans (h1 τ z t hτ ht ha hb hzt) ?_
    calc C1 * ‖Work.Kernels.qParamFun τ‖ ^ p * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
        = (C1 * ‖Work.Kernels.qParamFun τ‖ ^ p)
            * ((Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1) := by ring
      _ ≤ (C1 * ‖Work.Kernels.qParamFun τ‖ ^ min p q)
            * ((Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hqp hC1.le)
            (mul_le_mul e1S e1R hR1n hSmax) (mul_nonneg hS1n hR1n) (by positivity)
      _ = C1 * ‖Work.Kernels.qParamFun τ‖ ^ min p q * (Work.Kernels.scale τ) ^ (max N1 N2)
            * (1 + t) ^ (max M1 M2) := by ring
  have A2 : ‖G τ z‖ ≤ C2 * ‖Work.Kernels.qParamFun τ‖ ^ min p q
      * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) := by
    refine le_trans (h2 τ z t hτ ht ha hb hzt) ?_
    calc C2 * ‖Work.Kernels.qParamFun τ‖ ^ q * (Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2
        = (C2 * ‖Work.Kernels.qParamFun τ‖ ^ q)
            * ((Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2) := by ring
      _ ≤ (C2 * ‖Work.Kernels.qParamFun τ‖ ^ min p q)
            * ((Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hqq hC2.le)
            (mul_le_mul e2S e2R hR2n hSmax) (mul_nonneg hS2n hR2n) (by positivity)
      _ = C2 * ‖Work.Kernels.qParamFun τ‖ ^ min p q * (Work.Kernels.scale τ) ^ (max N1 N2)
            * (1 + t) ^ (max M1 M2) := by ring
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add A1 A2) (le_of_eq ?_)
  ring

lemma sub {p : ℕ} {F G : ℍ → ℍ → ℂ} (hF : Bd p F) (hG : Bd p G) :
    Bd p (fun τ z => F τ z - G τ z) := by
  have h := add hF (neg hG)
  rw [min_self] at h
  simpa only [sub_eq_add_neg] using h

lemma mul {p q : ℕ} {F G : ℍ → ℍ → ℂ} (hF : Bd p F) (hG : Bd q G) :
    Bd (p + q) (fun τ z => F τ z * G τ z) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, h1⟩ := hF
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, h2⟩ := hG
  refine ⟨C1 * C2, N1 + N2, M1 + M2, by positivity, by positivity, by positivity,
    fun τ z t hτ ht ha hb hzt => ?_⟩
  rw [norm_mul]
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := q_nonneg τ
  have hR : (1 : ℝ) ≤ 1 + t := one_le_one_add_t τ t hτ ht
  have hA : (0 : ℝ) ≤ C1 * ‖Work.Kernels.qParamFun τ‖ ^ p * (Work.Kernels.scale τ) ^ N1
      * (1 + t) ^ M1 := by
    refine mul_nonneg (mul_nonneg (mul_nonneg hC1.le (pow_nonneg hq0 _)) (S_nonneg τ N1))
      (Real.rpow_nonneg (le_trans zero_le_one hR) M1)
  refine le_trans (mul_le_mul (h1 τ z t hτ ht ha hb hzt) (h2 τ z t hτ ht ha hb hzt)
    (norm_nonneg _) hA) ?_
  refine le_of_eq ?_
  rw [Real.rpow_add (Work.Kernels.scale_pos τ),
    Real.rpow_add (lt_of_lt_of_le zero_lt_one hR), pow_add]
  ring

lemma pow {p : ℕ} {F : ℍ → ℍ → ℂ} (hF : Bd p F) (n : ℕ) :
    Bd (p * n) (fun τ z => F τ z ^ n) := by
  induction n with
  | zero =>
      have h := Bd.const (1 : ℂ)
      simpa only [mul_zero, pow_zero] using h
  | succ n ih =>
      have h : Bd (p * n + p) (fun τ z => F τ z ^ n * F τ z) := Bd.mul ih hF
      rw [show p * n + p = p * (n + 1) by ring] at h
      simpa only [pow_succ] using h


end Bd

/-! ## Atom instances -/

/-- A `Big` (`τ`-only) estimate is a `Bd` estimate. -/
lemma bd_of_big {p : ℕ} {f : ℍ → ℂ} (h : Big p f) : Bd p (fun τ _ => f τ) := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  refine ⟨C, N, 0, hC, hN, le_rfl, fun τ z t hτ ht ha hb' hzt => ?_⟩
  show ‖f τ‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ p * (Work.Kernels.scale τ) ^ N
    * (1 + t) ^ (0 : ℝ)
  rw [Real.rpow_zero, mul_one]
  calc ‖f τ‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ p :=
        hb τ hτ
    _ = C * ‖Work.Kernels.qParamFun τ‖ ^ p * (Work.Kernels.scale τ) ^ N := by ring

/-- `‖Δ(τ)‖ ≤ 2‖q(τ)‖` on the funnel. -/
lemma bd_Delta : Bd 1 (fun τ _ => Work.Kernels.DeltaFun τ) :=
  ⟨2, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hτ ht ha hb hzt => by
    show ‖Work.Kernels.DeltaFun τ‖ ≤ 2 * ‖Work.Kernels.qParamFun τ‖ ^ 1
      * (Work.Kernels.scale τ) ^ (0 : ℝ) * (1 + t) ^ (0 : ℝ)
    have h := Work.Asymptotics.DeltaFun_funnel_le τ hτ
    simpa only [pow_one, Real.rpow_zero, mul_one] using h⟩

/-- `‖E₄(τ)‖ ≤ C` on the funnel. -/
lemma big_E4 : Big 0 (fun τ => Work.Kernels.E4Fun τ) := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.E4Fun_bdd
  exact ⟨C, 0, hC, le_rfl, fun τ hτ => by
    have h := hb τ (by linarith [hτ.2])
    simpa only [pow_zero, Real.rpow_zero, mul_one] using h⟩

/-- `‖E₆(τ)‖ ≤ C` on the funnel. -/
lemma big_E6 : Big 0 (fun τ => Work.Kernels.E6Fun τ) := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.E6Fun_bdd
  exact ⟨C, 0, hC, le_rfl, fun τ hτ => by
    have h := hb τ (by linarith [hτ.2])
    simpa only [pow_zero, Real.rpow_zero, mul_one] using h⟩

/-- `‖E₂(τ)‖ ≤ C` on the funnel. -/
lemma big_E2 : Big 0 (fun τ => Work.Kernels.E2Fun τ) := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.E2Fun_bdd
  exact ⟨C, 0, hC, le_rfl, fun τ hτ => by
    have h := hb τ (by linarith [hτ.2])
    simpa only [pow_zero, Real.rpow_zero, mul_one] using h⟩

/-- `‖E₄(τ)⁻¹‖ ≤ 2` on the funnel. -/
lemma big_E4inv : Big 0 (fun τ => (Work.Kernels.E4Fun τ)⁻¹) := by
  refine ⟨2, 0, by norm_num, le_rfl, fun τ hτ => ?_⟩
  have h := Work.Asymptotics.funnel_E4_inv_le τ hτ
  simpa only [Real.rpow_zero, pow_zero, mul_one] using h

/-- `‖(τ : ℂ)‖ ≤ scale τ`. -/
lemma big_tau : Big 0 (fun τ => ((τ : ℍ) : ℂ)) := by
  refine ⟨1, 1, by norm_num, by norm_num, fun τ hτ => ?_⟩
  have h := Work.Kernels.coe_norm_le_scale τ
  simpa only [Real.rpow_one, pow_zero, mul_one, one_mul] using h

lemma bd_E4 : Bd 0 (fun τ _ => Work.Kernels.E4Fun τ) := bd_of_big big_E4
lemma bd_E6 : Bd 0 (fun τ _ => Work.Kernels.E6Fun τ) := bd_of_big big_E6
lemma bd_E2 : Bd 0 (fun τ _ => Work.Kernels.E2Fun τ) := bd_of_big big_E2
lemma bd_E4inv : Bd 0 (fun τ _ => (Work.Kernels.E4Fun τ)⁻¹) := bd_of_big big_E4inv
lemma bd_tau : Bd 0 (fun τ _ => ((τ : ℍ) : ℂ)) := bd_of_big big_tau

/-- `‖(z : ℂ)‖ ≤ 2(1+t)` on the strip. -/
lemma bd_z : Bd 0 (fun _ (z : ℍ) => ((z : ℍ) : ℂ)) :=
  ⟨2, 0, 1, by norm_num, le_rfl, by norm_num, fun τ z t hτ ht ha hb hzt => by
    show ‖((z : ℍ) : ℂ)‖ ≤ 2 * ‖Work.Kernels.qParamFun τ‖ ^ 0
      * (Work.Kernels.scale τ) ^ (0 : ℝ) * (1 + t) ^ (1 : ℝ)
    have h := Work.Asymptotics.KhatE1.kdevA4_norm_z_le z t ha hb hzt
    simpa only [pow_zero, Real.rpow_zero, Real.rpow_one, mul_one, one_mul] using h⟩

/-- `‖Xc ℓ z‖ ≤ (2π + 4log2)(1+t)` on the strip. -/
lemma bd_Xc (ℓ : Work.Kernels.LogLambdaData) :
    Bd 0 (fun _ z => Work.Asymptotics.Compact.Xc ℓ z) := by
  have hc : Work.Asymptotics.Compact.cuspC ℓ = 4 * (Real.log 2 : ℂ) :=
    Work.Asymptotics.CuspL_eq ℓ
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨2 * Real.pi + 4 * Real.log 2, 0, 1, by positivity, le_rfl, by positivity,
    fun τ z t hτ ht ha hb hzt => ?_⟩
  show ‖Work.Asymptotics.Compact.Xc ℓ z‖ ≤ (2 * Real.pi + 4 * Real.log 2)
    * ‖Work.Kernels.qParamFun τ‖ ^ 0 * (Work.Kernels.scale τ) ^ (0 : ℝ) * (1 + t) ^ (1 : ℝ)
  have hz := Work.Asymptotics.KhatE1.kdevA4_norm_z_le z t ha hb hzt
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h4 : (0 : ℝ) ≤ 4 * Real.log 2 := by positivity
  have hgoal : Work.Asymptotics.Compact.Xc ℓ z
      = (Real.pi : ℂ) * Complex.I * (z : ℂ) + 4 * (Real.log 2 : ℂ) := by
    rw [Work.Asymptotics.Compact.Xc, hc]
  rw [hgoal]
  have hmain : ‖(Real.pi : ℂ) * Complex.I * (z : ℂ) + 4 * (Real.log 2 : ℂ)‖
      ≤ (2 * Real.pi + 4 * Real.log 2) * (1 + t) := by
    calc ‖(Real.pi : ℂ) * Complex.I * (z : ℂ) + 4 * (Real.log 2 : ℂ)‖
        ≤ ‖(Real.pi : ℂ) * Complex.I * (z : ℂ)‖ + ‖(4 : ℂ) * (Real.log 2 : ℂ)‖ :=
          norm_add_le _ _
      _ = Real.pi * ‖(z : ℂ)‖ + 4 * Real.log 2 := by
          rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hπ, norm_mul, Complex.norm_ofNat, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hlog0]
      _ ≤ Real.pi * (2 * (1 + t)) + 4 * Real.log 2 := by
          have := mul_le_mul_of_nonneg_left hz hπ.le
          linarith
      _ ≤ (2 * Real.pi + 4 * Real.log 2) * (1 + t) := by
          have ht0 : (0 : ℝ) ≤ t := by linarith [hτ.2, ht]
          nlinarith [h4, Real.pi_pos, ht0]
  simpa only [pow_zero, Real.rpow_zero, Real.rpow_one, mul_one, one_mul] using hmain

/-- `‖φ₀(τ)‖` is `O(scale τ)` on the funnel. -/
lemma bd_phi0 : Bd 0 (fun τ _ => Work.Kernels.phi0 τ) := by
  have h1 : Bd 0 (fun τ _ => ((τ : ℍ) : ℂ) * Work.Kernels.E2Fun τ) := by
    simpa using Bd.mul bd_tau bd_E2
  have h : Bd 0 (fun τ _ => ((τ : ℍ) : ℂ) * Work.Kernels.E2Fun τ
      - 3 * Complex.I / (Real.pi : ℂ)) :=
    Bd.sub h1 (Bd.const (3 * Complex.I / (Real.pi : ℂ)))
  refine h.congr_on (fun τ z t hτ ht ha hb hzt => ?_)
  show ((τ : ℍ) : ℂ) * Work.Kernels.E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)
    = Work.Kernels.phi0 τ
  rw [Work.Kernels.phi0]

/-- `‖φ₂(τ)‖` is `O((scale τ)^N)` on the funnel. -/
lemma bd_phi2 : Bd 0 (fun τ _ => Work.Kernels.phi2 τ) := by
  have h1 : Bd 0 (fun τ _ => ((τ : ℍ) : ℂ) * Work.Kernels.E2Fun τ ^ 2) := by
    simpa using Bd.mul bd_tau (Bd.pow bd_E2 2)
  have h2 : Bd 0 (fun τ _ => (6 * Complex.I / (Real.pi : ℂ)) * Work.Kernels.E2Fun τ) :=
    Bd.cmul (6 * Complex.I / (Real.pi : ℂ)) bd_E2
  have h : Bd 0 (fun τ _ => ((τ : ℍ) : ℂ) * Work.Kernels.E2Fun τ ^ 2
      - (6 * Complex.I / (Real.pi : ℂ)) * Work.Kernels.E2Fun τ) :=
    Bd.sub h1 h2
  refine h.congr_on (fun τ z t hτ ht ha hb hzt => ?_)
  show ((τ : ℍ) : ℂ) * Work.Kernels.E2Fun τ ^ 2
      - (6 * Complex.I / (Real.pi : ℂ)) * Work.Kernels.E2Fun τ = Work.Kernels.phi2 τ
  rw [Work.Kernels.phi2]

/-- `‖ψ₂(τ)‖`, `‖ψ₄(τ)‖` are `O((scale τ)^N)` on the funnel. -/
lemma bd_psi (ℓ : Work.Kernels.LogLambdaData) :
    Bd 0 (fun τ _ => Work.Kernels.psi2 ℓ τ) ∧
      Bd 0 (fun τ _ => Work.Kernels.psi4 ℓ τ) := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.psi_scale_funnel ℓ
  constructor
  · refine ⟨C, N, 0, hC, hN, le_rfl, fun τ z t hτ ht ha hb hzt => ?_⟩
    show ‖Work.Kernels.psi2 ℓ τ‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 0
      * (Work.Kernels.scale τ) ^ N * (1 + t) ^ (0 : ℝ)
    have h2 := (h τ hτ).1
    simpa only [pow_zero, Real.rpow_zero, mul_one] using h2
  · refine ⟨C, N, 0, hC, hN, le_rfl, fun τ z t hτ ht ha hb hzt => ?_⟩
    show ‖Work.Kernels.psi4 ℓ τ‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 0
      * (Work.Kernels.scale τ) ^ N * (1 + t) ^ (0 : ℝ)
    have h4 := (h τ hτ).2
    simpa only [pow_zero, Real.rpow_zero, mul_one] using h4

lemma bd_psi2 (ℓ : Work.Kernels.LogLambdaData) :
    Bd 0 (fun τ _ => Work.Kernels.psi2 ℓ τ) := (bd_psi ℓ).1

lemma bd_psi4 (ℓ : Work.Kernels.LogLambdaData) :
    Bd 0 (fun τ _ => Work.Kernels.psi4 ℓ τ) := (bd_psi ℓ).2

/-- The imaginary unit. -/
lemma bd_I : Bd 0 (fun _ _ => Complex.I) := Bd.const Complex.I

/-- `E1combo8 = O(‖q(τ)‖(scale τ)^N)`. -/
lemma big_E1combo8 (ℓ : Work.Kernels.LogLambdaData) :
    Big 1 (fun τ => Work.Asymptotics.E1combo8 ℓ τ) := by
  obtain ⟨C, N, hC, hN, hb⟩ := Work.Asymptotics.KhatE1.E1combo8_bound ℓ
  exact ⟨C, N, hC, hN, fun τ hτ => by simpa only [pow_one] using hb τ hτ⟩

lemma bd_E1combo8 (ℓ : Work.Kernels.LogLambdaData) :
    Bd 1 (fun τ _ => Work.Asymptotics.E1combo8 ℓ τ) := bd_of_big (big_E1combo8 ℓ)

/-- `R8p0JF = 24·Δ(τ)·E1combo8 = O(‖q(τ)‖²(scale τ)^N)`. -/
lemma bd_R8p0JF (ℓ : Work.Kernels.LogLambdaData) :
    Bd 2 (fun τ _ => Work.Asymptotics.KhatE1.R8p0JF ℓ τ) := by
  have h : Bd 2 (fun τ _ => (24 : ℂ) * Work.Kernels.DeltaFun τ
      * Work.Asymptotics.E1combo8 ℓ τ) := by
    have h1 := Bd.mul (Bd.cmul (24 : ℂ) bd_Delta) (bd_E1combo8 ℓ)
    rw [show (1 : ℕ) + 1 = 2 from rfl] at h1
    exact h1
  refine h.congr_on (fun τ z t hτ ht ha hb hzt => ?_)
  show (24 : ℂ) * Work.Kernels.DeltaFun τ * Work.Asymptotics.E1combo8 ℓ τ
    = Work.Asymptotics.KhatE1.R8p0JF ℓ τ
  rw [← Work.Asymptotics.KhatE1.Delta_mul_R8p0 ℓ τ,
    Work.Asymptotics.KhatE1.R8_p0_eq_e1combo8 ℓ τ]
  ring

/-- The `d = 8` constant term `br0 8 = 3456·E₄(τ)·Xc − 1728·ψ₄` is `O((scale τ)^N(1+t)^M)`. -/
lemma bd_br0 (ℓ : Work.Kernels.LogLambdaData) :
    Bd 0 (fun τ z => Work.Asymptotics.Compact.br0 8 ℓ τ z) := by
  have h : Bd 0 (fun τ z => (3456 : ℂ) * Work.Kernels.E4Fun τ
      * Work.Asymptotics.Compact.Xc ℓ z - (1728 : ℂ) * Work.Kernels.psi4 ℓ τ) :=
    Bd.sub (Bd.mul (Bd.cmul (3456 : ℂ) bd_E4) (bd_Xc ℓ))
      (Bd.cmul (1728 : ℂ) (bd_psi4 ℓ))
  refine h.congr_on (fun τ z t hτ ht ha hb hzt => ?_)
  show (3456 : ℂ) * Work.Kernels.E4Fun τ * Work.Asymptotics.Compact.Xc ℓ z
      - (1728 : ℂ) * Work.Kernels.psi4 ℓ τ = Work.Asymptotics.Compact.br0 8 ℓ τ z
  rw [Work.Asymptotics.KhatE1.br0_eight_eq ℓ τ z]

/-- `KdevE2 = O(‖q(τ)‖(scale τ)^N(1+t)^M)`. -/
lemma bd_KdevE2 (ℓ : Work.Kernels.LogLambdaData) :
    Bd 1 (fun τ z => Work.Asymptotics.KhatE1.KdevE2 ℓ τ z) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := Work.Asymptotics.KhatE1.KdevE2_strip_bound ℓ
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hτ ht ha hb' hzt => ?_⟩
  show ‖Work.Asymptotics.KhatE1.KdevE2 ℓ τ z‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 1
    * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
  have h := hb τ z t hτ ht ha hb' hzt
  simpa only [pow_one] using h

/-- `A₁ = E₄ψ₄ - ψ₂E₆ = O(‖q(τ)‖(scale τ)^N)`. -/
lemma bd_A1 (ℓ : Work.Kernels.LogLambdaData) :
    Bd 1 (fun τ _ => Work.Kernels.E4Fun τ * Work.Kernels.psi4 ℓ τ
      - Work.Kernels.psi2 ℓ τ * Work.Kernels.E6Fun τ) := by
  have h : Bd 1 (fun τ _ => (Work.Kernels.DeltaFun τ * (Work.Kernels.E4Fun τ)⁻¹ ^ 2)
      * (Work.Asymptotics.E1combo8 ℓ τ
          - 576 * (2 * Work.Kernels.E4Fun τ - Work.Kernels.psi4 ℓ τ))) := by
    have hb : Bd 1 (fun τ _ => Work.Kernels.DeltaFun τ * (Work.Kernels.E4Fun τ)⁻¹ ^ 2) := by
      have h1 := Bd.mul bd_Delta (Bd.pow bd_E4inv 2)
      rw [show (1 : ℕ) + 0 * 2 = 1 from rfl] at h1
      exact h1
    have h2 : Bd 0 (fun τ _ => Work.Asymptotics.E1combo8 ℓ τ
        - 576 * (2 * Work.Kernels.E4Fun τ - Work.Kernels.psi4 ℓ τ)) :=
      Bd.sub ((bd_E1combo8 ℓ).mono (by norm_num))
        (Bd.cmul (576 : ℂ) (Bd.sub (Bd.cmul (2 : ℂ) bd_E4) (bd_psi4 ℓ)))
    have h3 := Bd.mul hb h2
    rw [show (1 : ℕ) + 0 = 1 from rfl] at h3
    exact h3
  refine h.congr_on (fun τ z t hτ ht ha hb hzt => ?_)
  show (Work.Kernels.DeltaFun τ * (Work.Kernels.E4Fun τ)⁻¹ ^ 2)
      * (Work.Asymptotics.E1combo8 ℓ τ
          - 576 * (2 * Work.Kernels.E4Fun τ - Work.Kernels.psi4 ℓ τ))
    = Work.Kernels.E4Fun τ * Work.Kernels.psi4 ℓ τ
      - Work.Kernels.psi2 ℓ τ * Work.Kernels.E6Fun τ
  have hE4 : Work.Kernels.E4Fun τ ≠ 0 := Work.Asymptotics.funnel_E4_ne_zero τ hτ
  have hΔ : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  simp only [Work.Asymptotics.E1combo8, Work.Kernels.jInvariantFun]
  field_simp
  ring





/-- The combined `ψ`-pair of the coefficients `p₅, …, p₉`: `c·Δ(τ)·π⁻¹·E₄(τ)²·A₁` with
`A₁ = E₄ψ₄ - ψ₂E₆ = O(‖q(τ)‖(scale τ)^N)`. -/
lemma bd_psi_pair (ℓ : Work.Kernels.LogLambdaData) (c : ℂ) :
    Bd 2 (fun τ _ => c * (Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹)
      * (Work.Kernels.E4Fun τ) ^ 2
      * (Work.Kernels.E4Fun τ * Work.Kernels.psi4 ℓ τ
          - Work.Kernels.psi2 ℓ τ * Work.Kernels.E6Fun τ))) := by
  have h1 : Bd 1 (fun τ _ => Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹)
      * (Work.Kernels.E4Fun τ) ^ 2) := by
    have h := Bd.mul (Bd.mul bd_Delta (Bd.const ((Real.pi : ℂ)⁻¹))) (Bd.pow bd_E4 2)
    exact Bd.mono h (by norm_num)
  have h2 : Bd 2 (fun τ _ => (Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹)
      * (Work.Kernels.E4Fun τ) ^ 2)
      * (Work.Kernels.E4Fun τ * Work.Kernels.psi4 ℓ τ
          - Work.Kernels.psi2 ℓ τ * Work.Kernels.E6Fun τ)) :=
    Bd.mono (Bd.mul h1 (bd_A1 ℓ)) (by norm_num)
  exact Bd.cmul c h2


/-- `p5` bound. -/
lemma p5_bound (ℓ : Work.Kernels.LogLambdaData) :
    Bd 2 (fun τ z => Work.Asymptotics.KhatE1.p5 ℓ τ z) := by
  have hcomb : Bd 2 (fun τ z => (((145 : ℂ) / 24)) * (Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 2) * (Work.Kernels.E4Fun τ * Work.Kernels.psi4 ℓ τ - Work.Kernels.psi2 ℓ τ * Work.Kernels.E6Fun τ))) := by
    simpa only [mul_assoc] using bd_psi_pair ℓ (((145 : ℂ) / 24))
  have hrest : Bd 2 (fun τ z => (((-415 : ℂ) / 8) * Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * Work.Asymptotics.KhatE1.R8p0JF ℓ τ) + ((-1) * (1086272 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.E4Fun τ) + ((-1) * (255384 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.psi4 ℓ τ) + (((-1 : ℂ) / 144) * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3) * Work.Asymptotics.KhatE1.R8p0JF ℓ τ)) := by
    exact Bd.mono (Bd.add (Bd.add (Bd.add (Bd.mul (Bd.mul (Bd.mul (Bd.const (((-415 : ℂ) / 8))) (bd_Delta)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_R8p0JF ℓ)) (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (1086272 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_E4))) (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (255384 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_psi4 ℓ))) (Bd.mul (Bd.mul (Bd.mul (Bd.const (((-1 : ℂ) / 144))) (Bd.const ((Real.pi : ℂ)⁻¹))) (Bd.pow (bd_E4) 3)) (bd_R8p0JF ℓ))) (by norm_num)
  refine (Bd.add hcomb hrest).congr_on ?_
  intro τ z t hτ ht ha hb hzt
  unfold Work.Asymptotics.KhatE1.p5
  ring

/-- `p6` bound. -/
lemma p6_bound (ℓ : Work.Kernels.LogLambdaData) :
    Bd 1 (fun τ z => Work.Asymptotics.KhatE1.p6 ℓ τ z) := by
  have hcomb : Bd 2 (fun τ z => (((1178 : ℂ) / 3)) * (Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 2) * (Work.Kernels.E4Fun τ * Work.Kernels.psi4 ℓ τ - Work.Kernels.psi2 ℓ τ * Work.Kernels.E6Fun τ))) := by
    simpa only [mul_assoc] using bd_psi_pair ℓ (((1178 : ℂ) / 3))
  have hrest : Bd 1 (fun τ z => ((3024 : ℂ) * Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3)) + ((-1) * (252 : ℂ) * Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2) * ((Work.Kernels.E4Fun τ) ^ 3)) + ((-1) * (9072 : ℂ) * Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (Complex.I ^ 2) * (((Real.pi : ℂ)⁻¹) ^ 2) * ((Work.Kernels.E4Fun τ) ^ 3)) + ((-1) * (252 : ℂ) * Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2) * ((Work.Kernels.E4Fun τ) ^ 2) * Work.Kernels.phi2 τ) + ((-1) * (3024 : ℂ) * Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * Work.Kernels.phi0 τ * ((Work.Kernels.E4Fun τ) ^ 4)) + ((504 : ℂ) * Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹ * ((z : ℂ) ^ 2) * Work.Kernels.phi0 τ * ((Work.Kernels.E4Fun τ) ^ 4)) + (((-7 : ℂ) / 96) * Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3) * Work.Asymptotics.Compact.br0 8 ℓ τ z) + ((-1) * (48 : ℂ) * Work.Kernels.DeltaFun τ * ((Work.Kernels.E4Fun τ) ^ 3) * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z) + ((-1) * (209018880 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹)) + ((18658944 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2)) + ((572313600 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (Complex.I ^ 2) * (((Real.pi : ℂ)⁻¹) ^ 2)) + ((264176640 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ) + ((-1) * (37490688 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * ((z : ℂ) ^ 2) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ) + ((1626768 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.E4Fun τ) + ((4900 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Asymptotics.Compact.br0 8 ℓ τ z) + ((748800 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.psi4 ℓ τ) + ((-1) * (358560 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z)) := by
    exact Bd.mono (Bd.add (Bd.add (Bd.add (Bd.add (Bd.add (Bd.add (Bd.add (Bd.add (Bd.add (Bd.add (Bd.add (Bd.add (Bd.add (Bd.add (Bd.add (Bd.add (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((3024 : ℂ))) (bd_Delta)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_tau)) (bd_E6)) (bd_z)) (bd_I)) (Bd.const ((Real.pi : ℂ)⁻¹))) (Bd.pow (bd_E4) 3)) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (252 : ℂ))) (bd_Delta)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_tau)) (bd_E6)) (Bd.pow (bd_z) 2)) (Bd.pow (bd_E4) 3))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (9072 : ℂ))) (bd_Delta)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_tau)) (bd_E6)) (Bd.pow (bd_I) 2)) (Bd.pow (Bd.const ((Real.pi : ℂ)⁻¹)) 2)) (Bd.pow (bd_E4) 3))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (252 : ℂ))) (bd_Delta)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_E6)) (Bd.pow (bd_z) 2)) (Bd.pow (bd_E4) 2)) (bd_phi2))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (3024 : ℂ))) (bd_Delta)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_z)) (bd_I)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_phi0)) (Bd.pow (bd_E4) 4))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((504 : ℂ))) (bd_Delta)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (Bd.pow (bd_z) 2)) (bd_phi0)) (Bd.pow (bd_E4) 4))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const (((-7 : ℂ) / 96))) (bd_Delta)) (Bd.const ((Real.pi : ℂ)⁻¹))) (Bd.pow (bd_E4) 3)) (bd_br0 ℓ))) (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (48 : ℂ))) (bd_Delta)) (Bd.pow (bd_E4) 3)) (bd_KdevE2 ℓ))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (209018880 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_tau)) (bd_E6)) (bd_z)) (bd_I)) (Bd.const ((Real.pi : ℂ)⁻¹)))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((18658944 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_tau)) (bd_E6)) (Bd.pow (bd_z) 2))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((572313600 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_tau)) (bd_E6)) (Bd.pow (bd_I) 2)) (Bd.pow (Bd.const ((Real.pi : ℂ)⁻¹)) 2))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((264176640 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_z)) (bd_I)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_phi0)) (bd_E4))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (37490688 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (Bd.pow (bd_z) 2)) (bd_phi0)) (bd_E4))) (Bd.mul (Bd.mul (Bd.mul (Bd.const ((1626768 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_E4))) (Bd.mul (Bd.mul (Bd.mul (Bd.const ((4900 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_br0 ℓ))) (Bd.mul (Bd.mul (Bd.mul (Bd.const ((748800 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_psi4 ℓ))) (Bd.mul (Bd.mul (Bd.const ((-1) * (358560 : ℂ))) (Bd.pow (bd_Delta) 2)) (bd_KdevE2 ℓ))) (by norm_num)
  refine (Bd.add hcomb hrest).congr_on ?_
  intro τ z t hτ ht ha hb hzt
  unfold Work.Asymptotics.KhatE1.p6
  ring

/-- `p7` bound. -/
lemma p7_bound (ℓ : Work.Kernels.LogLambdaData) :
    Bd 2 (fun τ z => Work.Asymptotics.KhatE1.p7 ℓ τ z) := by
  have hcomb : Bd 2 (fun τ z => ((-1) * (1870 : ℂ)) * (Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 2) * (Work.Kernels.E4Fun τ * Work.Kernels.psi4 ℓ τ - Work.Kernels.psi2 ℓ τ * Work.Kernels.E6Fun τ))) := by
    simpa only [mul_assoc] using bd_psi_pair ℓ ((-1) * (1870 : ℂ))
  have hrest : Bd 2 (fun τ z => ((-1) * (4900 : ℂ) * Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * Work.Asymptotics.KhatE1.R8p0JF ℓ τ) + ((-1) * (1444608 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.E4Fun τ) + ((-1) * (1002240 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.psi4 ℓ τ) + (((7 : ℂ) / 96) * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 3) * Work.Asymptotics.KhatE1.R8p0JF ℓ τ)) := by
    exact Bd.mono (Bd.add (Bd.add (Bd.add (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (4900 : ℂ))) (bd_Delta)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_R8p0JF ℓ)) (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (1444608 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_E4))) (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (1002240 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_psi4 ℓ))) (Bd.mul (Bd.mul (Bd.mul (Bd.const (((7 : ℂ) / 96))) (Bd.const ((Real.pi : ℂ)⁻¹))) (Bd.pow (bd_E4) 3)) (bd_R8p0JF ℓ))) (by norm_num)
  refine (Bd.add hcomb hrest).congr_on ?_
  intro τ z t hτ ht ha hb hzt
  unfold Work.Asymptotics.KhatE1.p7
  ring

/-- `p8` bound. -/
lemma p8_bound (ℓ : Work.Kernels.LogLambdaData) :
    Bd 2 (fun τ z => Work.Asymptotics.KhatE1.p8 ℓ τ z) := by
  have hcomb : Bd 2 (fun τ z => ((3959 : ℂ)) * (Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 2) * (Work.Kernels.E4Fun τ * Work.Kernels.psi4 ℓ τ - Work.Kernels.psi2 ℓ τ * Work.Kernels.E6Fun τ))) := by
    simpa only [mul_assoc] using bd_psi_pair ℓ ((3959 : ℂ))
  have hrest : Bd 2 (fun τ z => ((504 : ℂ) * Work.Kernels.DeltaFun τ * ((Work.Kernels.E4Fun τ) ^ 3) * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z) + ((-1) * (4943047680 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹)) + ((403932096 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2)) + ((13772851200 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (Complex.I ^ 2) * (((Real.pi : ℂ)⁻¹) ^ 2)) + ((5078039040 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ) + ((-1) * (582982272 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * ((z : ℂ) ^ 2) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ) + ((812592 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.E4Fun τ) + ((112050 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Asymptotics.Compact.br0 8 ℓ τ z) + ((743040 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.psi4 ℓ τ) + ((-1) * (33868800 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z)) := by
    exact Bd.mono (Bd.add (Bd.add (Bd.add (Bd.add (Bd.add (Bd.add (Bd.add (Bd.add (Bd.add (Bd.mul (Bd.mul (Bd.mul (Bd.const ((504 : ℂ))) (bd_Delta)) (Bd.pow (bd_E4) 3)) (bd_KdevE2 ℓ)) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (4943047680 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_tau)) (bd_E6)) (bd_z)) (bd_I)) (Bd.const ((Real.pi : ℂ)⁻¹)))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((403932096 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_tau)) (bd_E6)) (Bd.pow (bd_z) 2))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((13772851200 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_tau)) (bd_E6)) (Bd.pow (bd_I) 2)) (Bd.pow (Bd.const ((Real.pi : ℂ)⁻¹)) 2))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((5078039040 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_z)) (bd_I)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_phi0)) (bd_E4))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (582982272 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (Bd.pow (bd_z) 2)) (bd_phi0)) (bd_E4))) (Bd.mul (Bd.mul (Bd.mul (Bd.const ((812592 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_E4))) (Bd.mul (Bd.mul (Bd.mul (Bd.const ((112050 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_br0 ℓ))) (Bd.mul (Bd.mul (Bd.mul (Bd.const ((743040 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_psi4 ℓ))) (Bd.mul (Bd.mul (Bd.const ((-1) * (33868800 : ℂ))) (Bd.pow (bd_Delta) 2)) (bd_KdevE2 ℓ))) (by norm_num)
  refine (Bd.add hcomb hrest).congr_on ?_
  intro τ z t hτ ht ha hb hzt
  unfold Work.Asymptotics.KhatE1.p8
  ring

/-- `p9` bound. -/
lemma p9_bound (ℓ : Work.Kernels.LogLambdaData) :
    Bd 2 (fun τ z => Work.Asymptotics.KhatE1.p9 ℓ τ z) := by
  have hcomb : Bd 2 (fun τ z => ((-1) * (8842 : ℂ)) * (Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * ((Work.Kernels.E4Fun τ) ^ 2) * (Work.Kernels.E4Fun τ * Work.Kernels.psi4 ℓ τ - Work.Kernels.psi2 ℓ τ * Work.Kernels.E6Fun τ))) := by
    simpa only [mul_assoc] using bd_psi_pair ℓ ((-1) * (8842 : ℂ))
  have hrest : Bd 2 (fun τ z => ((-1) * (112050 : ℂ) * Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * Work.Asymptotics.KhatE1.R8p0JF ℓ τ) + ((-1) * (1486080 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Kernels.psi4 ℓ τ)) := by
    exact Bd.mono (Bd.add (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (112050 : ℂ))) (bd_Delta)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_R8p0JF ℓ)) (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (1486080 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_psi4 ℓ))) (by norm_num)
  refine (Bd.add hcomb hrest).congr_on ?_
  intro τ z t hτ ht ha hb hzt
  unfold Work.Asymptotics.KhatE1.p9
  ring

/-- `p10` bound. -/
lemma p10_bound (ℓ : Work.Kernels.LogLambdaData) :
    Bd 2 (fun τ z => Work.Asymptotics.KhatE1.p10 ℓ τ z) := by
  have hrest : Bd 2 (fun τ z => ((-1) * (42550272000 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹)) + ((2918799360 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2)) + ((120932352000 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (Complex.I ^ 2) * (((Real.pi : ℂ)⁻¹) ^ 2)) + ((40310784000 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ) + ((-1) * (4262492160 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * ((z : ℂ) ^ 2) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ) + ((972000 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Asymptotics.Compact.br0 8 ℓ τ z) + ((-1) * (774489600 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z)) := by
    exact Bd.mono (Bd.add (Bd.add (Bd.add (Bd.add (Bd.add (Bd.add (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (42550272000 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_tau)) (bd_E6)) (bd_z)) (bd_I)) (Bd.const ((Real.pi : ℂ)⁻¹))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((2918799360 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_tau)) (bd_E6)) (Bd.pow (bd_z) 2))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((120932352000 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_tau)) (bd_E6)) (Bd.pow (bd_I) 2)) (Bd.pow (Bd.const ((Real.pi : ℂ)⁻¹)) 2))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((40310784000 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_z)) (bd_I)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_phi0)) (bd_E4))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (4262492160 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (Bd.pow (bd_z) 2)) (bd_phi0)) (bd_E4))) (Bd.mul (Bd.mul (Bd.mul (Bd.const ((972000 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_br0 ℓ))) (Bd.mul (Bd.mul (Bd.const ((-1) * (774489600 : ℂ))) (Bd.pow (bd_Delta) 2)) (bd_KdevE2 ℓ))) (by norm_num)
  refine hrest.congr_on ?_
  intro τ z t hτ ht ha hb hzt
  unfold Work.Asymptotics.KhatE1.p10
  ring

/-- `p11` bound. -/
lemma p11_bound (ℓ : Work.Kernels.LogLambdaData) :
    Bd 3 (fun τ z => Work.Asymptotics.KhatE1.p11 ℓ τ z) := by
  have hrest : Bd 3 (fun τ z => ((-1) * (972000 : ℂ) * Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * Work.Asymptotics.KhatE1.R8p0JF ℓ τ)) := by
    exact Bd.mono (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (972000 : ℂ))) (bd_Delta)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_R8p0JF ℓ)) (by norm_num)
  refine hrest.congr_on ?_
  intro τ z t hτ ht ha hb hzt
  unfold Work.Asymptotics.KhatE1.p11
  ring

/-- `p12` bound. -/
lemma p12_bound (ℓ : Work.Kernels.LogLambdaData) :
    Bd 2 (fun τ z => Work.Asymptotics.KhatE1.p12 ℓ τ z) := by
  have hrest : Bd 2 (fun τ z => ((-1) * (124963430400 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹)) + ((4157982720 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2)) + ((362797056000 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * (Complex.I ^ 2) * (((Real.pi : ℂ)⁻¹) ^ 2)) + ((120932352000 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (z : ℂ) * Complex.I * ((Real.pi : ℂ)⁻¹) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ) + ((-1) * (14982174720 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * ((z : ℂ) ^ 2) * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ) + ((2916000 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * ((Real.pi : ℂ)⁻¹) * Work.Asymptotics.Compact.br0 8 ℓ τ z) + ((-1) * (6718464000 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z)) := by
    exact Bd.mono (Bd.add (Bd.add (Bd.add (Bd.add (Bd.add (Bd.add (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (124963430400 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_tau)) (bd_E6)) (bd_z)) (bd_I)) (Bd.const ((Real.pi : ℂ)⁻¹))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((4157982720 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_tau)) (bd_E6)) (Bd.pow (bd_z) 2))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((362797056000 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_tau)) (bd_E6)) (Bd.pow (bd_I) 2)) (Bd.pow (Bd.const ((Real.pi : ℂ)⁻¹)) 2))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((120932352000 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_z)) (bd_I)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_phi0)) (bd_E4))) (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (14982174720 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (Bd.pow (bd_z) 2)) (bd_phi0)) (bd_E4))) (Bd.mul (Bd.mul (Bd.mul (Bd.const ((2916000 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_br0 ℓ))) (Bd.mul (Bd.mul (Bd.const ((-1) * (6718464000 : ℂ))) (Bd.pow (bd_Delta) 2)) (bd_KdevE2 ℓ))) (by norm_num)
  refine hrest.congr_on ?_
  intro τ z t hτ ht ha hb hzt
  unfold Work.Asymptotics.KhatE1.p12
  ring

/-- `p13` bound. -/
lemma p13_bound (ℓ : Work.Kernels.LogLambdaData) :
    Bd 3 (fun τ z => Work.Asymptotics.KhatE1.p13 ℓ τ z) := by
  have hrest : Bd 3 (fun τ z => ((-1) * (2916000 : ℂ) * Work.Kernels.DeltaFun τ * ((Real.pi : ℂ)⁻¹) * Work.Asymptotics.KhatE1.R8p0JF ℓ τ)) := by
    exact Bd.mono (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (2916000 : ℂ))) (bd_Delta)) (Bd.const ((Real.pi : ℂ)⁻¹))) (bd_R8p0JF ℓ)) (by norm_num)
  refine hrest.congr_on ?_
  intro τ z t hτ ht ha hb hzt
  unfold Work.Asymptotics.KhatE1.p13
  ring

/-- `p14` bound. -/
lemma p14_bound (ℓ : Work.Kernels.LogLambdaData) :
    Bd 2 (fun τ z => Work.Asymptotics.KhatE1.p14 ℓ τ z) := by
  have hrest : Bd 2 (fun τ z => ((-1) * (21499084800 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2)) + ((-1) * (20155392000 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z)) := by
    exact Bd.mono (Bd.add (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (21499084800 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_tau)) (bd_E6)) (Bd.pow (bd_z) 2)) (Bd.mul (Bd.mul (Bd.const ((-1) * (20155392000 : ℂ))) (Bd.pow (bd_Delta) 2)) (bd_KdevE2 ℓ))) (by norm_num)
  refine hrest.congr_on ?_
  intro τ z t hτ ht ha hb hzt
  unfold Work.Asymptotics.KhatE1.p14
  ring

/-- `p15` bound. -/
lemma p15_bound (ℓ : Work.Kernels.LogLambdaData) :
    Bd 0 (fun τ z => Work.Asymptotics.KhatE1.p15 ℓ τ z) := by
  have hrest : Bd 0 (fun τ z => ((0 : ℂ))) := by
    exact Bd.mono (Bd.const ((0 : ℂ))) (by norm_num)
  refine hrest.congr_on ?_
  intro τ z t hτ ht ha hb hzt
  unfold Work.Asymptotics.KhatE1.p15
  ring

/-- `p16` bound. -/
lemma p16_bound (ℓ : Work.Kernels.LogLambdaData) :
    Bd 2 (fun τ z => Work.Asymptotics.KhatE1.p16 ℓ τ z) := by
  have hrest : Bd 2 (fun τ z => ((-1) * (24186470400 : ℂ) * ((Work.Kernels.DeltaFun τ) ^ 2) * Work.Asymptotics.Compact.tailC⁻¹ * (τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) ^ 2))) := by
    exact Bd.mono (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.mul (Bd.const ((-1) * (24186470400 : ℂ))) (Bd.pow (bd_Delta) 2)) (Bd.const (Work.Asymptotics.Compact.tailC⁻¹))) (bd_tau)) (bd_E6)) (Bd.pow (bd_z) 2)) (by norm_num)
  refine hrest.congr_on ?_
  intro τ z t hτ ht ha hb hzt
  unfold Work.Asymptotics.KhatE1.p16
  ring

/-! ## The rungs `p₃ = Δ²·KdevA3` and `p₄ = Δ²·KdevA4` -/

/-- **`p₃ = Δ(τ)²·KdevA3`.** -/
lemma p3_eq_Δ2_KdevA3 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    (Work.Kernels.DeltaFun τ) ^ 2 * Work.Asymptotics.KhatE1.KdevA3 ℓ τ
      = Work.Asymptotics.KhatE1.p3 ℓ τ z := by
  have hΔt : (Work.Kernels.DeltaFun τ) ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  simp only [Work.Asymptotics.KhatE1.p3, Work.Asymptotics.KhatE1.KdevA3,
    Work.Asymptotics.Compact.R8_p2, Work.Asymptotics.KhatE1.R8p0JF,
    Work.Kernels.jInvariantFun, Work.Kernels.E14Fun]
  field_simp
  ring_nf

lemma p3_bound (ℓ : Work.Kernels.LogLambdaData) :
    Bd 3 (fun τ z => Work.Asymptotics.KhatE1.p3 ℓ τ z) := by
  have hK : Bd 1 (fun τ _ => Work.Asymptotics.KhatE1.KdevA3 ℓ τ) := by
    obtain ⟨C, N, hC, hN, hb⟩ := Work.Asymptotics.KhatE1Core.KdevA3_bound ℓ
    refine ⟨C, N, 0, hC, hN, le_rfl, fun τ z t hτ ht ha hb' hzt => ?_⟩
    show ‖Work.Asymptotics.KhatE1.KdevA3 ℓ τ‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 1
      * (Work.Kernels.scale τ) ^ N * (1 + t) ^ (0 : ℝ)
    have h := hb τ hτ
    have h2 : C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖
        = C * ‖Work.Kernels.qParamFun τ‖ ^ 1 * (Work.Kernels.scale τ) ^ N := by
      rw [pow_one]; ring
    rw [h2] at h
    simpa only [Real.rpow_zero, mul_one] using h
  have h := Bd.mul (Bd.pow bd_Delta 2) hK
  refine h.congr_on (fun τ z t hτ ht ha hb hzt => ?_)
  show (Work.Kernels.DeltaFun τ) ^ 2 * Work.Asymptotics.KhatE1.KdevA3 ℓ τ
    = Work.Asymptotics.KhatE1.p3 ℓ τ z
  exact p3_eq_Δ2_KdevA3 ℓ τ z

/-- **`p₄ = Δ(τ)²·KdevA4`.** -/
lemma p4_eq_Δ2_KdevA4 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Asymptotics.KhatE1.p4 ℓ τ z
      = (Work.Kernels.DeltaFun τ) ^ 2 * Work.Asymptotics.KhatE1Core.KdevA4 ℓ τ z := by
  have hΔt : (Work.Kernels.DeltaFun τ) ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  simp only [Work.Asymptotics.KhatE1.p4]
  rw [Work.Asymptotics.KhatE1.br0_eight_eq ℓ τ z]
  simp only [Work.Asymptotics.KhatE1Core.KdevA4, Work.Asymptotics.KhatE1Core.KdevA4num,
    Work.Asymptotics.KhatE1Core.Phi4, Work.Asymptotics.KhatE1Core.Dev4,
    Work.Asymptotics.KhatE1.KdevE2, Work.Asymptotics.KhatE1.KdevE2plus,
    Work.Asymptotics.KhatE1.KdevE2minus,
    Work.Kernels.jInvariantFun, Work.Kernels.E14Fun, Work.Kernels.phi0, Work.Kernels.phi2]
  field_simp
  ring_nf

lemma p4_bound (ℓ : Work.Kernels.LogLambdaData) :
    Bd 2 (fun τ z => Work.Asymptotics.KhatE1.p4 ℓ τ z) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := Work.Asymptotics.KhatE1.KdevA4Sharp ℓ
  have h : Bd 2 (fun τ z => (Work.Kernels.DeltaFun τ) ^ 2
      * Work.Asymptotics.KhatE1Core.KdevA4 ℓ τ z) := by
    have hb' : ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1Core.KdevA4 ℓ τ z‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 0
          * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
      intro τ z t hτ ht h1 h2 h3
      have h := hb τ z t hτ ht h1 h2 h3
      simpa only [pow_zero, mul_one, one_mul] using h
    have h1 := Bd.mul (Bd.pow bd_Delta 2) (⟨C, N, M, hC, hN, hM, hb'⟩ :
      Bd 0 (fun τ z => Work.Asymptotics.KhatE1Core.KdevA4 ℓ τ z))
    rw [show (1 * 2 : ℕ) + 0 = 2 from rfl] at h1
    exact h1
  refine h.congr_on (fun τ z t hτ ht ha hb' hzt => ?_)
  exact (p4_eq_Δ2_KdevA4 ℓ τ z).symm

/-- **The `q`-power/Ept-power trade.**  On the funnel strip, `‖q(τ)‖^e ‖Ept z‖^k ≤ ‖q(τ)‖³‖Ept z‖²`
whenever `2e + k ≥ 8` and `k ≥ 2`. -/
lemma qpow_Ept_pow_le {τ z : ℍ} {t : ℝ} (hτ : Work.Asymptotics.Funnel τ)
    (ht : τ.im + 1 ≤ t) (hzt : z.im = t) {e k : ℕ} (hk : 2 ≤ k) (he : 8 ≤ 2 * e + k) :
    ‖Work.Kernels.qParamFun τ‖ ^ e * ‖Work.Residues.Ept z‖ ^ k
      ≤ ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 := by
  have hIm : (0 : ℝ) ≤ τ.im := le_of_lt τ.im_pos
  have he' : (8 : ℝ) ≤ 2 * (e : ℝ) + (k : ℝ) := by exact_mod_cast he
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) - 2 := by linarith
  have hcoef : (0 : ℝ) ≤ 2 * (e : ℝ) + (k : ℝ) - 8 := by linarith [he']
  have htu : (0 : ℝ) ≤ t - τ.im := by linarith
  have hsplit : 2 * ((e : ℝ) - 3) * τ.im + ((k : ℝ) - 2) * t
      = (2 * (e : ℝ) + (k : ℝ) - 8) * τ.im + ((k : ℝ) - 2) * (t - τ.im) := by ring
  have hkey : 0 ≤ 2 * ((e : ℝ) - 3) * τ.im + ((k : ℝ) - 2) * t := by
    rw [hsplit]
    have hA : 0 ≤ (2 * (e : ℝ) + (k : ℝ) - 8) * τ.im := mul_nonneg hcoef hIm
    have hB : 0 ≤ ((k : ℝ) - 2) * (t - τ.im) := mul_nonneg hk0 htu
    linarith [hA, hB]
  rw [Work.Asymptotics.norm_qParamFun, Work.Residues.norm_Ept, hzt,
    ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul,
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hfin : -((2 * Real.pi * τ.im) * 3) + -(Real.pi * t) * 2
      - (-(2 * Real.pi * τ.im) * (e : ℝ) + -(Real.pi * t) * (k : ℝ))
      = Real.pi * (2 * ((e : ℝ) - 3) * τ.im + ((k : ℝ) - 2) * t) := by ring
  have hmain := mul_nonneg Real.pi_pos.le hkey
  have hfin2 : (e : ℝ) * -(2 * Real.pi * τ.im) + (k : ℝ) * -(Real.pi * t)
      ≤ (3 : ℝ) * -(2 * Real.pi * τ.im) + (2 : ℝ) * -(Real.pi * t) := by
    nlinarith [hmain, Real.pi_pos, τ.im_pos]
  exact hfin2

/-- A single term `p_k·Ept^k` bounded with a common exponent pair `(N, M)`. -/
lemma strip_term_bound {e k : ℕ} {F : ℍ → ℍ → ℂ} {C N0 M0 N M : ℝ}
    (hk : 2 ≤ k) (he : 8 ≤ 2 * e + k) (hC : 0 ≤ C) (hN : N0 ≤ N) (hM : M0 ≤ M)
    {τ z : ℍ} {t : ℝ} (hτ : Work.Asymptotics.Funnel τ) (ht : τ.im + 1 ≤ t) (hzt : z.im = t)
    (hb : ‖F τ z‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ e * (Work.Kernels.scale τ) ^ N0
      * (1 + t) ^ M0) :
    ‖F τ z * (Work.Residues.Ept z) ^ k‖
      ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
        * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
  have hS1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hT1 : (1 : ℝ) ≤ 1 + t := Bd.one_le_one_add_t τ t hτ ht
  have hQ0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hU0 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
  have hrat := qpow_Ept_pow_le hτ ht hzt hk he
  have hNS : (Work.Kernels.scale τ) ^ N0 ≤ (Work.Kernels.scale τ) ^ N :=
    Real.rpow_le_rpow_of_exponent_le hS1 hN
  have hNT : (1 + t) ^ M0 ≤ (1 + t) ^ M := Real.rpow_le_rpow_of_exponent_le hT1 hM
  rw [norm_mul, norm_pow]
  calc ‖F τ z‖ * ‖Work.Residues.Ept z‖ ^ k
      ≤ (C * ‖Work.Kernels.qParamFun τ‖ ^ e * (Work.Kernels.scale τ) ^ N0 * (1 + t) ^ M0)
          * ‖Work.Residues.Ept z‖ ^ k := mul_le_mul_of_nonneg_right hb (pow_nonneg hU0 _)
    _ = (C * ((Work.Kernels.scale τ) ^ N0 * (1 + t) ^ M0))
          * (‖Work.Kernels.qParamFun τ‖ ^ e * ‖Work.Residues.Ept z‖ ^ k) := by ring
    _ ≤ (C * ((Work.Kernels.scale τ) ^ N0 * (1 + t) ^ M0))
          * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hrat (by positivity)
    _ = C * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
          * ((Work.Kernels.scale τ) ^ N0 * (1 + t) ^ M0) := by ring
    _ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
          * ((Work.Kernels.scale τ) ^ N * (1 + t) ^ M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hNS hNT (by positivity) (by positivity))
          (by positivity)
    _ = C * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
          * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by ring

/-- **The polynomial part of the cleared residual is `O(‖q(τ)‖³‖Ept z‖²(scale τ)^N(1+t)^M)`.** -/
theorem WresPolyPol_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1.WresPolyPol ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
              * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
  obtain ⟨C3, N3, M3, hC3, hN3, hM3, hb3⟩ := Work.Asymptotics.KhatE1Core.p3_bound ℓ
  obtain ⟨C4, N4, M4, hC4, hN4, hM4, hb4⟩ := Work.Asymptotics.KhatE1Core.p4_bound ℓ
  obtain ⟨C5, N5, M5, hC5, hN5, hM5, hb5⟩ := Work.Asymptotics.KhatE1Core.p5_bound ℓ
  obtain ⟨C6, N6, M6, hC6, hN6, hM6, hb6⟩ := Work.Asymptotics.KhatE1Core.p6_bound ℓ
  obtain ⟨C7, N7, M7, hC7, hN7, hM7, hb7⟩ := Work.Asymptotics.KhatE1Core.p7_bound ℓ
  obtain ⟨C8, N8, M8, hC8, hN8, hM8, hb8⟩ := Work.Asymptotics.KhatE1Core.p8_bound ℓ
  obtain ⟨C9, N9, M9, hC9, hN9, hM9, hb9⟩ := Work.Asymptotics.KhatE1Core.p9_bound ℓ
  obtain ⟨C10, N10, M10, hC10, hN10, hM10, hb10⟩ := Work.Asymptotics.KhatE1Core.p10_bound ℓ
  obtain ⟨C11, N11, M11, hC11, hN11, hM11, hb11⟩ := Work.Asymptotics.KhatE1Core.p11_bound ℓ
  obtain ⟨C12, N12, M12, hC12, hN12, hM12, hb12⟩ := Work.Asymptotics.KhatE1Core.p12_bound ℓ
  obtain ⟨C13, N13, M13, hC13, hN13, hM13, hb13⟩ := Work.Asymptotics.KhatE1Core.p13_bound ℓ
  obtain ⟨C14, N14, M14, hC14, hN14, hM14, hb14⟩ := Work.Asymptotics.KhatE1Core.p14_bound ℓ
  obtain ⟨C15, N15, M15, hC15, hN15, hM15, hb15⟩ := Work.Asymptotics.KhatE1Core.p15_bound ℓ
  obtain ⟨C16, N16, M16, hC16, hN16, hM16, hb16⟩ := Work.Asymptotics.KhatE1Core.p16_bound ℓ
  set Ntot : ℝ := N3 + N4 + N5 + N6 + N7 + N8 + N9 + N10 + N11 + N12 + N13 + N14 + N15 + N16 with hNtot
  set Mtot : ℝ := M3 + M4 + M5 + M6 + M7 + M8 + M9 + M10 + M11 + M12 + M13 + M14 + M15 + M16 with hMtot
  have hNtot0 : 0 ≤ Ntot := by rw [hNtot]; linarith [hN3, hN4, hN5, hN6, hN7, hN8, hN9, hN10, hN11, hN12, hN13, hN14, hN15, hN16]
  have hMtot0 : 0 ≤ Mtot := by rw [hMtot]; linarith [hM3, hM4, hM5, hM6, hM7, hM8, hM9, hM10, hM11, hM12, hM13, hM14, hM15, hM16]
  set Cbig : ℝ := 1 + C3 + C4 + C5 + C6 + C7 + C8 + C9 + C10 + C11 + C12 + C13 + C14 + C15 + C16 with hCbig
  refine ⟨17 * Cbig, Ntot, Mtot, by positivity, hNtot0, hMtot0, ?_⟩
  intro τ z t hτ ht h1 h2 hzt
  have hRAW0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) _)) (Real.rpow_nonneg (by linarith [hτ.2, ht]) _)
  have b0 : ‖Work.Asymptotics.KhatE1.p0 ℓ τ z‖ ≤ 1 * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    rw [Work.Asymptotics.KhatE1.p0_eq_zero ℓ τ z]
    simp only [norm_zero, zero_mul, one_mul]
    exact hRAW0
  have b1 : ‖Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z)‖ ≤ 1 * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    rw [Work.Asymptotics.KhatE1.p1_eq_zero ℓ τ z]
    simp only [norm_zero, zero_mul, one_mul]
    exact hRAW0
  have b2 : ‖Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖ ≤ 1 * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    rw [Work.Asymptotics.KhatE1.p2_eq_zero ℓ τ z]
    simp only [norm_zero, zero_mul, one_mul]
    exact hRAW0
  have b3 : ‖Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3‖ ≤ C3 * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    have h := strip_term_bound (e := 3) (k := 3) (C := C3) (N0 := N3) (M0 := M3) (N := Ntot) (M := Mtot)
      (F := fun τ z => Work.Asymptotics.KhatE1.p3 ℓ τ z) (by norm_num) (by norm_num) hC3.le
      (by rw [hNtot]; linarith [hN4, hN5, hN6, hN7, hN8, hN9, hN10, hN11, hN12, hN13, hN14, hN15, hN16]) (by rw [hMtot]; linarith [hM4, hM5, hM6, hM7, hM8, hM9, hM10, hM11, hM12, hM13, hM14, hM15, hM16]) hτ ht hzt
      (hb3 τ z t hτ ht h1 h2 hzt)
    simpa only [mul_assoc] using h
  have b4 : ‖Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4‖ ≤ C4 * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    have h := strip_term_bound (e := 2) (k := 4) (C := C4) (N0 := N4) (M0 := M4) (N := Ntot) (M := Mtot)
      (F := fun τ z => Work.Asymptotics.KhatE1.p4 ℓ τ z) (by norm_num) (by norm_num) hC4.le
      (by rw [hNtot]; linarith [hN3, hN5, hN6, hN7, hN8, hN9, hN10, hN11, hN12, hN13, hN14, hN15, hN16]) (by rw [hMtot]; linarith [hM3, hM5, hM6, hM7, hM8, hM9, hM10, hM11, hM12, hM13, hM14, hM15, hM16]) hτ ht hzt
      (hb4 τ z t hτ ht h1 h2 hzt)
    simpa only [mul_assoc] using h
  have b5 : ‖Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5‖ ≤ C5 * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    have h := strip_term_bound (e := 2) (k := 5) (C := C5) (N0 := N5) (M0 := M5) (N := Ntot) (M := Mtot)
      (F := fun τ z => Work.Asymptotics.KhatE1.p5 ℓ τ z) (by norm_num) (by norm_num) hC5.le
      (by rw [hNtot]; linarith [hN3, hN4, hN6, hN7, hN8, hN9, hN10, hN11, hN12, hN13, hN14, hN15, hN16]) (by rw [hMtot]; linarith [hM3, hM4, hM6, hM7, hM8, hM9, hM10, hM11, hM12, hM13, hM14, hM15, hM16]) hτ ht hzt
      (hb5 τ z t hτ ht h1 h2 hzt)
    simpa only [mul_assoc] using h
  have b6 : ‖Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6‖ ≤ C6 * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    have h := strip_term_bound (e := 1) (k := 6) (C := C6) (N0 := N6) (M0 := M6) (N := Ntot) (M := Mtot)
      (F := fun τ z => Work.Asymptotics.KhatE1.p6 ℓ τ z) (by norm_num) (by norm_num) hC6.le
      (by rw [hNtot]; linarith [hN3, hN4, hN5, hN7, hN8, hN9, hN10, hN11, hN12, hN13, hN14, hN15, hN16]) (by rw [hMtot]; linarith [hM3, hM4, hM5, hM7, hM8, hM9, hM10, hM11, hM12, hM13, hM14, hM15, hM16]) hτ ht hzt
      (hb6 τ z t hτ ht h1 h2 hzt)
    simpa only [mul_assoc] using h
  have b7 : ‖Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7‖ ≤ C7 * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    have h := strip_term_bound (e := 2) (k := 7) (C := C7) (N0 := N7) (M0 := M7) (N := Ntot) (M := Mtot)
      (F := fun τ z => Work.Asymptotics.KhatE1.p7 ℓ τ z) (by norm_num) (by norm_num) hC7.le
      (by rw [hNtot]; linarith [hN3, hN4, hN5, hN6, hN8, hN9, hN10, hN11, hN12, hN13, hN14, hN15, hN16]) (by rw [hMtot]; linarith [hM3, hM4, hM5, hM6, hM8, hM9, hM10, hM11, hM12, hM13, hM14, hM15, hM16]) hτ ht hzt
      (hb7 τ z t hτ ht h1 h2 hzt)
    simpa only [mul_assoc] using h
  have b8 : ‖Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8‖ ≤ C8 * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    have h := strip_term_bound (e := 2) (k := 8) (C := C8) (N0 := N8) (M0 := M8) (N := Ntot) (M := Mtot)
      (F := fun τ z => Work.Asymptotics.KhatE1.p8 ℓ τ z) (by norm_num) (by norm_num) hC8.le
      (by rw [hNtot]; linarith [hN3, hN4, hN5, hN6, hN7, hN9, hN10, hN11, hN12, hN13, hN14, hN15, hN16]) (by rw [hMtot]; linarith [hM3, hM4, hM5, hM6, hM7, hM9, hM10, hM11, hM12, hM13, hM14, hM15, hM16]) hτ ht hzt
      (hb8 τ z t hτ ht h1 h2 hzt)
    simpa only [mul_assoc] using h
  have b9 : ‖Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9‖ ≤ C9 * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    have h := strip_term_bound (e := 2) (k := 9) (C := C9) (N0 := N9) (M0 := M9) (N := Ntot) (M := Mtot)
      (F := fun τ z => Work.Asymptotics.KhatE1.p9 ℓ τ z) (by norm_num) (by norm_num) hC9.le
      (by rw [hNtot]; linarith [hN3, hN4, hN5, hN6, hN7, hN8, hN10, hN11, hN12, hN13, hN14, hN15, hN16]) (by rw [hMtot]; linarith [hM3, hM4, hM5, hM6, hM7, hM8, hM10, hM11, hM12, hM13, hM14, hM15, hM16]) hτ ht hzt
      (hb9 τ z t hτ ht h1 h2 hzt)
    simpa only [mul_assoc] using h
  have b10 : ‖Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10‖ ≤ C10 * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    have h := strip_term_bound (e := 2) (k := 10) (C := C10) (N0 := N10) (M0 := M10) (N := Ntot) (M := Mtot)
      (F := fun τ z => Work.Asymptotics.KhatE1.p10 ℓ τ z) (by norm_num) (by norm_num) hC10.le
      (by rw [hNtot]; linarith [hN3, hN4, hN5, hN6, hN7, hN8, hN9, hN11, hN12, hN13, hN14, hN15, hN16]) (by rw [hMtot]; linarith [hM3, hM4, hM5, hM6, hM7, hM8, hM9, hM11, hM12, hM13, hM14, hM15, hM16]) hτ ht hzt
      (hb10 τ z t hτ ht h1 h2 hzt)
    simpa only [mul_assoc] using h
  have b11 : ‖Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11‖ ≤ C11 * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    have h := strip_term_bound (e := 3) (k := 11) (C := C11) (N0 := N11) (M0 := M11) (N := Ntot) (M := Mtot)
      (F := fun τ z => Work.Asymptotics.KhatE1.p11 ℓ τ z) (by norm_num) (by norm_num) hC11.le
      (by rw [hNtot]; linarith [hN3, hN4, hN5, hN6, hN7, hN8, hN9, hN10, hN12, hN13, hN14, hN15, hN16]) (by rw [hMtot]; linarith [hM3, hM4, hM5, hM6, hM7, hM8, hM9, hM10, hM12, hM13, hM14, hM15, hM16]) hτ ht hzt
      (hb11 τ z t hτ ht h1 h2 hzt)
    simpa only [mul_assoc] using h
  have b12 : ‖Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12‖ ≤ C12 * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    have h := strip_term_bound (e := 2) (k := 12) (C := C12) (N0 := N12) (M0 := M12) (N := Ntot) (M := Mtot)
      (F := fun τ z => Work.Asymptotics.KhatE1.p12 ℓ τ z) (by norm_num) (by norm_num) hC12.le
      (by rw [hNtot]; linarith [hN3, hN4, hN5, hN6, hN7, hN8, hN9, hN10, hN11, hN13, hN14, hN15, hN16]) (by rw [hMtot]; linarith [hM3, hM4, hM5, hM6, hM7, hM8, hM9, hM10, hM11, hM13, hM14, hM15, hM16]) hτ ht hzt
      (hb12 τ z t hτ ht h1 h2 hzt)
    simpa only [mul_assoc] using h
  have b13 : ‖Work.Asymptotics.KhatE1.p13 ℓ τ z * (Work.Residues.Ept z) ^ 13‖ ≤ C13 * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    have h := strip_term_bound (e := 3) (k := 13) (C := C13) (N0 := N13) (M0 := M13) (N := Ntot) (M := Mtot)
      (F := fun τ z => Work.Asymptotics.KhatE1.p13 ℓ τ z) (by norm_num) (by norm_num) hC13.le
      (by rw [hNtot]; linarith [hN3, hN4, hN5, hN6, hN7, hN8, hN9, hN10, hN11, hN12, hN14, hN15, hN16]) (by rw [hMtot]; linarith [hM3, hM4, hM5, hM6, hM7, hM8, hM9, hM10, hM11, hM12, hM14, hM15, hM16]) hτ ht hzt
      (hb13 τ z t hτ ht h1 h2 hzt)
    simpa only [mul_assoc] using h
  have b14 : ‖Work.Asymptotics.KhatE1.p14 ℓ τ z * (Work.Residues.Ept z) ^ 14‖ ≤ C14 * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    have h := strip_term_bound (e := 2) (k := 14) (C := C14) (N0 := N14) (M0 := M14) (N := Ntot) (M := Mtot)
      (F := fun τ z => Work.Asymptotics.KhatE1.p14 ℓ τ z) (by norm_num) (by norm_num) hC14.le
      (by rw [hNtot]; linarith [hN3, hN4, hN5, hN6, hN7, hN8, hN9, hN10, hN11, hN12, hN13, hN15, hN16]) (by rw [hMtot]; linarith [hM3, hM4, hM5, hM6, hM7, hM8, hM9, hM10, hM11, hM12, hM13, hM15, hM16]) hτ ht hzt
      (hb14 τ z t hτ ht h1 h2 hzt)
    simpa only [mul_assoc] using h
  have b15 : ‖Work.Asymptotics.KhatE1.p15 ℓ τ z * (Work.Residues.Ept z) ^ 15‖ ≤ C15 * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    have h := strip_term_bound (e := 0) (k := 15) (C := C15) (N0 := N15) (M0 := M15) (N := Ntot) (M := Mtot)
      (F := fun τ z => Work.Asymptotics.KhatE1.p15 ℓ τ z) (by norm_num) (by norm_num) hC15.le
      (by rw [hNtot]; linarith [hN3, hN4, hN5, hN6, hN7, hN8, hN9, hN10, hN11, hN12, hN13, hN14, hN16]) (by rw [hMtot]; linarith [hM3, hM4, hM5, hM6, hM7, hM8, hM9, hM10, hM11, hM12, hM13, hM14, hM16]) hτ ht hzt
      (hb15 τ z t hτ ht h1 h2 hzt)
    simpa only [mul_assoc] using h
  have b16 : ‖Work.Asymptotics.KhatE1.p16 ℓ τ z * (Work.Residues.Ept z) ^ 16‖ ≤ C16 * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    have h := strip_term_bound (e := 2) (k := 16) (C := C16) (N0 := N16) (M0 := M16) (N := Ntot) (M := Mtot)
      (F := fun τ z => Work.Asymptotics.KhatE1.p16 ℓ τ z) (by norm_num) (by norm_num) hC16.le
      (by rw [hNtot]; linarith [hN3, hN4, hN5, hN6, hN7, hN8, hN9, hN10, hN11, hN12, hN13, hN14, hN15]) (by rw [hMtot]; linarith [hM3, hM4, hM5, hM6, hM7, hM8, hM9, hM10, hM11, hM12, hM13, hM14, hM15]) hτ ht hzt
      (hb16 τ z t hτ ht h1 h2 hzt)
    simpa only [mul_assoc] using h
  have b0' : ‖Work.Asymptotics.KhatE1.p0 ℓ τ z‖ ≤ Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    refine le_trans b0 (mul_le_mul_of_nonneg_right ?_ hRAW0)
    rw [hCbig]; linarith [hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC11, hC12, hC13, hC14, hC15, hC16]
  have b1' : ‖Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z)‖ ≤ Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    refine le_trans b1 (mul_le_mul_of_nonneg_right ?_ hRAW0)
    rw [hCbig]; linarith [hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC11, hC12, hC13, hC14, hC15, hC16]
  have b2' : ‖Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖ ≤ Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    refine le_trans b2 (mul_le_mul_of_nonneg_right ?_ hRAW0)
    rw [hCbig]; linarith [hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC11, hC12, hC13, hC14, hC15, hC16]
  have b3' : ‖Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3‖ ≤ Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    refine le_trans b3 (mul_le_mul_of_nonneg_right ?_ hRAW0)
    rw [hCbig]; linarith [hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC11, hC12, hC13, hC14, hC15, hC16]
  have b4' : ‖Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4‖ ≤ Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    refine le_trans b4 (mul_le_mul_of_nonneg_right ?_ hRAW0)
    rw [hCbig]; linarith [hC3, hC5, hC6, hC7, hC8, hC9, hC10, hC11, hC12, hC13, hC14, hC15, hC16]
  have b5' : ‖Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5‖ ≤ Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    refine le_trans b5 (mul_le_mul_of_nonneg_right ?_ hRAW0)
    rw [hCbig]; linarith [hC3, hC4, hC6, hC7, hC8, hC9, hC10, hC11, hC12, hC13, hC14, hC15, hC16]
  have b6' : ‖Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6‖ ≤ Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    refine le_trans b6 (mul_le_mul_of_nonneg_right ?_ hRAW0)
    rw [hCbig]; linarith [hC3, hC4, hC5, hC7, hC8, hC9, hC10, hC11, hC12, hC13, hC14, hC15, hC16]
  have b7' : ‖Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7‖ ≤ Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    refine le_trans b7 (mul_le_mul_of_nonneg_right ?_ hRAW0)
    rw [hCbig]; linarith [hC3, hC4, hC5, hC6, hC8, hC9, hC10, hC11, hC12, hC13, hC14, hC15, hC16]
  have b8' : ‖Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8‖ ≤ Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    refine le_trans b8 (mul_le_mul_of_nonneg_right ?_ hRAW0)
    rw [hCbig]; linarith [hC3, hC4, hC5, hC6, hC7, hC9, hC10, hC11, hC12, hC13, hC14, hC15, hC16]
  have b9' : ‖Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9‖ ≤ Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    refine le_trans b9 (mul_le_mul_of_nonneg_right ?_ hRAW0)
    rw [hCbig]; linarith [hC3, hC4, hC5, hC6, hC7, hC8, hC10, hC11, hC12, hC13, hC14, hC15, hC16]
  have b10' : ‖Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10‖ ≤ Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    refine le_trans b10 (mul_le_mul_of_nonneg_right ?_ hRAW0)
    rw [hCbig]; linarith [hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC11, hC12, hC13, hC14, hC15, hC16]
  have b11' : ‖Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11‖ ≤ Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    refine le_trans b11 (mul_le_mul_of_nonneg_right ?_ hRAW0)
    rw [hCbig]; linarith [hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC12, hC13, hC14, hC15, hC16]
  have b12' : ‖Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12‖ ≤ Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    refine le_trans b12 (mul_le_mul_of_nonneg_right ?_ hRAW0)
    rw [hCbig]; linarith [hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC11, hC13, hC14, hC15, hC16]
  have b13' : ‖Work.Asymptotics.KhatE1.p13 ℓ τ z * (Work.Residues.Ept z) ^ 13‖ ≤ Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    refine le_trans b13 (mul_le_mul_of_nonneg_right ?_ hRAW0)
    rw [hCbig]; linarith [hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC11, hC12, hC14, hC15, hC16]
  have b14' : ‖Work.Asymptotics.KhatE1.p14 ℓ τ z * (Work.Residues.Ept z) ^ 14‖ ≤ Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    refine le_trans b14 (mul_le_mul_of_nonneg_right ?_ hRAW0)
    rw [hCbig]; linarith [hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC11, hC12, hC13, hC15, hC16]
  have b15' : ‖Work.Asymptotics.KhatE1.p15 ℓ τ z * (Work.Residues.Ept z) ^ 15‖ ≤ Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    refine le_trans b15 (mul_le_mul_of_nonneg_right ?_ hRAW0)
    rw [hCbig]; linarith [hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC11, hC12, hC13, hC14, hC16]
  have b16' : ‖Work.Asymptotics.KhatE1.p16 ℓ τ z * (Work.Residues.Ept z) ^ 16‖ ≤ Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := by
    refine le_trans b16 (mul_le_mul_of_nonneg_right ?_ hRAW0)
    rw [hCbig]; linarith [hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10, hC11, hC12, hC13, hC14, hC15]
  have hn0 : ‖Work.Asymptotics.KhatE1.p0 ℓ τ z‖ ≤ 1 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by
    rw [one_mul]; exact b0'
  have hn1 : ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z)‖ ≤ 2 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by
    calc ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z)‖ = ‖(Work.Asymptotics.KhatE1.p0 ℓ τ z) + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z)‖ := rfl
      _ ≤ ‖Work.Asymptotics.KhatE1.p0 ℓ τ z‖ + ‖Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z)‖ := norm_add_le _ _
      _ ≤ 1 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) + Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := add_le_add hn0 b1'
      _ = 2 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by ring
  have hn2 : ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖ ≤ 3 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by
    calc ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖ = ‖(Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z)) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖ := rfl
      _ ≤ ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z)‖ + ‖Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖ := norm_add_le _ _
      _ ≤ 2 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) + Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := add_le_add hn1 b2'
      _ = 3 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by ring
  have hn3 : ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3‖ ≤ 4 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by
    calc ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3‖ = ‖(Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2) + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3‖ := rfl
      _ ≤ ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖ + ‖Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3‖ := norm_add_le _ _
      _ ≤ 3 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) + Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := add_le_add hn2 b3'
      _ = 4 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by ring
  have hn4 : ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4‖ ≤ 5 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by
    calc ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4‖ = ‖(Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3) + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4‖ := rfl
      _ ≤ ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3‖ + ‖Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4‖ := norm_add_le _ _
      _ ≤ 4 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) + Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := add_le_add hn3 b4'
      _ = 5 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by ring
  have hn5 : ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5‖ ≤ 6 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by
    calc ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5‖ = ‖(Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4) + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5‖ := rfl
      _ ≤ ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4‖ + ‖Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5‖ := norm_add_le _ _
      _ ≤ 5 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) + Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := add_le_add hn4 b5'
      _ = 6 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by ring
  have hn6 : ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6‖ ≤ 7 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by
    calc ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6‖ = ‖(Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5) + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6‖ := rfl
      _ ≤ ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5‖ + ‖Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6‖ := norm_add_le _ _
      _ ≤ 6 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) + Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := add_le_add hn5 b6'
      _ = 7 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by ring
  have hn7 : ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7‖ ≤ 8 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by
    calc ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7‖ = ‖(Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6) + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7‖ := rfl
      _ ≤ ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6‖ + ‖Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7‖ := norm_add_le _ _
      _ ≤ 7 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) + Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := add_le_add hn6 b7'
      _ = 8 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by ring
  have hn8 : ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8‖ ≤ 9 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by
    calc ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8‖ = ‖(Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7) + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8‖ := rfl
      _ ≤ ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7‖ + ‖Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8‖ := norm_add_le _ _
      _ ≤ 8 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) + Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := add_le_add hn7 b8'
      _ = 9 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by ring
  have hn9 : ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9‖ ≤ 10 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by
    calc ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9‖ = ‖(Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8) + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9‖ := rfl
      _ ≤ ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8‖ + ‖Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9‖ := norm_add_le _ _
      _ ≤ 9 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) + Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := add_le_add hn8 b9'
      _ = 10 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by ring
  have hn10 : ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10‖ ≤ 11 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by
    calc ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10‖ = ‖(Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9) + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10‖ := rfl
      _ ≤ ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9‖ + ‖Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10‖ := norm_add_le _ _
      _ ≤ 10 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) + Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := add_le_add hn9 b10'
      _ = 11 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by ring
  have hn11 : ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11‖ ≤ 12 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by
    calc ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11‖ = ‖(Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10) + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11‖ := rfl
      _ ≤ ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10‖ + ‖Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11‖ := norm_add_le _ _
      _ ≤ 11 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) + Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := add_le_add hn10 b11'
      _ = 12 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by ring
  have hn12 : ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11 + Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12‖ ≤ 13 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by
    calc ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11 + Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12‖ = ‖(Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11) + Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12‖ := rfl
      _ ≤ ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11‖ + ‖Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12‖ := norm_add_le _ _
      _ ≤ 12 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) + Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := add_le_add hn11 b12'
      _ = 13 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by ring
  have hn13 : ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11 + Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12 + Work.Asymptotics.KhatE1.p13 ℓ τ z * (Work.Residues.Ept z) ^ 13‖ ≤ 14 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by
    calc ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11 + Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12 + Work.Asymptotics.KhatE1.p13 ℓ τ z * (Work.Residues.Ept z) ^ 13‖ = ‖(Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11 + Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12) + Work.Asymptotics.KhatE1.p13 ℓ τ z * (Work.Residues.Ept z) ^ 13‖ := rfl
      _ ≤ ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11 + Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12‖ + ‖Work.Asymptotics.KhatE1.p13 ℓ τ z * (Work.Residues.Ept z) ^ 13‖ := norm_add_le _ _
      _ ≤ 13 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) + Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := add_le_add hn12 b13'
      _ = 14 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by ring
  have hn14 : ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11 + Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12 + Work.Asymptotics.KhatE1.p13 ℓ τ z * (Work.Residues.Ept z) ^ 13 + Work.Asymptotics.KhatE1.p14 ℓ τ z * (Work.Residues.Ept z) ^ 14‖ ≤ 15 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by
    calc ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11 + Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12 + Work.Asymptotics.KhatE1.p13 ℓ τ z * (Work.Residues.Ept z) ^ 13 + Work.Asymptotics.KhatE1.p14 ℓ τ z * (Work.Residues.Ept z) ^ 14‖ = ‖(Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11 + Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12 + Work.Asymptotics.KhatE1.p13 ℓ τ z * (Work.Residues.Ept z) ^ 13) + Work.Asymptotics.KhatE1.p14 ℓ τ z * (Work.Residues.Ept z) ^ 14‖ := rfl
      _ ≤ ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11 + Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12 + Work.Asymptotics.KhatE1.p13 ℓ τ z * (Work.Residues.Ept z) ^ 13‖ + ‖Work.Asymptotics.KhatE1.p14 ℓ τ z * (Work.Residues.Ept z) ^ 14‖ := norm_add_le _ _
      _ ≤ 14 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) + Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := add_le_add hn13 b14'
      _ = 15 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by ring
  have hn15 : ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11 + Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12 + Work.Asymptotics.KhatE1.p13 ℓ τ z * (Work.Residues.Ept z) ^ 13 + Work.Asymptotics.KhatE1.p14 ℓ τ z * (Work.Residues.Ept z) ^ 14 + Work.Asymptotics.KhatE1.p15 ℓ τ z * (Work.Residues.Ept z) ^ 15‖ ≤ 16 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by
    calc ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11 + Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12 + Work.Asymptotics.KhatE1.p13 ℓ τ z * (Work.Residues.Ept z) ^ 13 + Work.Asymptotics.KhatE1.p14 ℓ τ z * (Work.Residues.Ept z) ^ 14 + Work.Asymptotics.KhatE1.p15 ℓ τ z * (Work.Residues.Ept z) ^ 15‖ = ‖(Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11 + Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12 + Work.Asymptotics.KhatE1.p13 ℓ τ z * (Work.Residues.Ept z) ^ 13 + Work.Asymptotics.KhatE1.p14 ℓ τ z * (Work.Residues.Ept z) ^ 14) + Work.Asymptotics.KhatE1.p15 ℓ τ z * (Work.Residues.Ept z) ^ 15‖ := rfl
      _ ≤ ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11 + Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12 + Work.Asymptotics.KhatE1.p13 ℓ τ z * (Work.Residues.Ept z) ^ 13 + Work.Asymptotics.KhatE1.p14 ℓ τ z * (Work.Residues.Ept z) ^ 14‖ + ‖Work.Asymptotics.KhatE1.p15 ℓ τ z * (Work.Residues.Ept z) ^ 15‖ := norm_add_le _ _
      _ ≤ 15 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) + Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := add_le_add hn14 b15'
      _ = 16 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by ring
  have hn16 : ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11 + Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12 + Work.Asymptotics.KhatE1.p13 ℓ τ z * (Work.Residues.Ept z) ^ 13 + Work.Asymptotics.KhatE1.p14 ℓ τ z * (Work.Residues.Ept z) ^ 14 + Work.Asymptotics.KhatE1.p15 ℓ τ z * (Work.Residues.Ept z) ^ 15 + Work.Asymptotics.KhatE1.p16 ℓ τ z * (Work.Residues.Ept z) ^ 16‖ ≤ 17 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by
    calc ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11 + Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12 + Work.Asymptotics.KhatE1.p13 ℓ τ z * (Work.Residues.Ept z) ^ 13 + Work.Asymptotics.KhatE1.p14 ℓ τ z * (Work.Residues.Ept z) ^ 14 + Work.Asymptotics.KhatE1.p15 ℓ τ z * (Work.Residues.Ept z) ^ 15 + Work.Asymptotics.KhatE1.p16 ℓ τ z * (Work.Residues.Ept z) ^ 16‖ = ‖(Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11 + Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12 + Work.Asymptotics.KhatE1.p13 ℓ τ z * (Work.Residues.Ept z) ^ 13 + Work.Asymptotics.KhatE1.p14 ℓ τ z * (Work.Residues.Ept z) ^ 14 + Work.Asymptotics.KhatE1.p15 ℓ τ z * (Work.Residues.Ept z) ^ 15) + Work.Asymptotics.KhatE1.p16 ℓ τ z * (Work.Residues.Ept z) ^ 16‖ := rfl
      _ ≤ ‖Work.Asymptotics.KhatE1.p0 ℓ τ z + Work.Asymptotics.KhatE1.p1 ℓ τ z * (Work.Residues.Ept z) + Work.Asymptotics.KhatE1.p2 ℓ τ z * (Work.Residues.Ept z) ^ 2 + Work.Asymptotics.KhatE1.p3 ℓ τ z * (Work.Residues.Ept z) ^ 3 + Work.Asymptotics.KhatE1.p4 ℓ τ z * (Work.Residues.Ept z) ^ 4 + Work.Asymptotics.KhatE1.p5 ℓ τ z * (Work.Residues.Ept z) ^ 5 + Work.Asymptotics.KhatE1.p6 ℓ τ z * (Work.Residues.Ept z) ^ 6 + Work.Asymptotics.KhatE1.p7 ℓ τ z * (Work.Residues.Ept z) ^ 7 + Work.Asymptotics.KhatE1.p8 ℓ τ z * (Work.Residues.Ept z) ^ 8 + Work.Asymptotics.KhatE1.p9 ℓ τ z * (Work.Residues.Ept z) ^ 9 + Work.Asymptotics.KhatE1.p10 ℓ τ z * (Work.Residues.Ept z) ^ 10 + Work.Asymptotics.KhatE1.p11 ℓ τ z * (Work.Residues.Ept z) ^ 11 + Work.Asymptotics.KhatE1.p12 ℓ τ z * (Work.Residues.Ept z) ^ 12 + Work.Asymptotics.KhatE1.p13 ℓ τ z * (Work.Residues.Ept z) ^ 13 + Work.Asymptotics.KhatE1.p14 ℓ τ z * (Work.Residues.Ept z) ^ 14 + Work.Asymptotics.KhatE1.p15 ℓ τ z * (Work.Residues.Ept z) ^ 15‖ + ‖Work.Asymptotics.KhatE1.p16 ℓ τ z * (Work.Residues.Ept z) ^ 16‖ := norm_add_le _ _
      _ ≤ 16 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) + Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot) := add_le_add hn15 b16'
      _ = 17 * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) := by ring
  rw [Work.Asymptotics.KhatE1.WresPolyPol_eq_sum ℓ τ z, Work.Asymptotics.KhatE1.Puept]
  refine le_trans hn16 ?_
  rw [show (17:ℝ) * (Cbig * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot)) = (17 * Cbig) * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ Ntot * (1 + t) ^ Mtot from by ring]

end

end Work.Asymptotics.KhatE1Core
