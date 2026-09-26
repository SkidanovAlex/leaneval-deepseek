import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.KPlus24Refs
import Submission.Work.Asymptotics.KhatE1Core.PhiSplit
import Submission.Work.Asymptotics.KhatE1Core.DKPlusBounds
import Submission.Work.Asymptotics.K24FZ

/-!
# The `dSm4` row, first pieces: `r ^ n ≤ 1`, `‖E2SRef z‖ ≤ 99`, `dQ2 = O(q³)`

`dSm4 = 1728·r₀·dQ2 + 1728·r₂·dE4 - (1728·r₀·S0z² + 1728·r₂)·dE4c`, so it needs the `z`-side
cofactor norm `‖E2SRef z‖ ≤ 99` and the deviation `dQ2 = O(q³)`.  (The `τ`-side cofactors are
`K24F.tau_atom_bounds`.)
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-- `r ^ n ≤ 1` for `0 ≤ r ≤ 1` — the shape needed throughout, without `nlinarith`. -/
lemma pow_nat_le_one {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : ∀ n : ℕ, r ^ n ≤ 1
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ]
      exact le_trans (mul_le_of_le_one_right (pow_nonneg h0 n) h1) (pow_nat_le_one h0 h1 n)

/-- `‖q(z)‖ ≤ 1` on `1 ≤ z.im`. -/
lemma norm_q_le_one_of_im {z : ℍ} (hz : 1 ≤ z.im) :
    ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
  rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
  nlinarith [Real.pi_pos, hz]

/-- **`‖E2SRef z‖ ≤ 99`** on `1 ≤ z.im`.  `E2SRef z = S0z z - 24q - 72q²` is *left-associated*
subtraction, so the decomposition uses `norm_sub_le (S0z z - 24q) (72q²)`. -/
lemma norm_E2SRef_le {z : ℍ} (hz : 1 ≤ z.im) : ‖E2SRef z‖ ≤ 99 := by
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := norm_q_le_one_of_im hz
  have hS : ‖Work.Asymptotics.KhatE1.S0z z‖ ≤ 3 := Work.Asymptotics.K24F.zS0_norm z hz
  have a : ‖E2SRef z‖ ≤ ‖Work.Asymptotics.KhatE1.S0z z - 24 * Work.Kernels.qParamFun z‖
      + ‖(72 : ℂ) * (Work.Kernels.qParamFun z) ^ 2‖ := norm_sub_le _ _
  have b : ‖Work.Asymptotics.KhatE1.S0z z - 24 * Work.Kernels.qParamFun z‖
      ≤ ‖Work.Asymptotics.KhatE1.S0z z‖ + 24 * ‖Work.Kernels.qParamFun z‖ := by
    have h := norm_sub_le (Work.Asymptotics.KhatE1.S0z z)
      ((24 : ℂ) * Work.Kernels.qParamFun z)
    simpa only [norm_mul, Complex.norm_ofNat] using h
  have c : ‖(72 : ℂ) * (Work.Kernels.qParamFun z) ^ 2‖
      = 72 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
    simp only [norm_mul, norm_pow, Complex.norm_ofNat]
  rw [c] at a
  have e1 : 24 * ‖Work.Kernels.qParamFun z‖ ≤ 24 := mul_le_of_le_one_right (by norm_num) hq1
  have e2 : 72 * ‖Work.Kernels.qParamFun z‖ ^ 2 ≤ 72 :=
    mul_le_of_le_one_right (by norm_num) (pow_nat_le_one (norm_nonneg _) hq1 2)
  linarith [a, b, hS, e1, e2]

/-- **`dQ2 = O(‖q(z)‖³)`** for `dQ2 = 2·E2SRef·dE2S + dE2S²`.

The product bound is taken in the *fully typed* form: state `‖E2SRef z‖ * ‖dE2S z‖ ≤ 99 * (C₂·‖q‖³)`
by `mul_le_mul` with all four arguments present, and only then push the leading `2` through
(`mul_le_mul_of_nonneg_left`), which keeps Lean's positional unification unambiguous. -/
lemma dQ2_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖dQ2 z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨C2, hC2, h2⟩ := dE2S_bound
  refine ⟨2 * 99 * C2 + C2 ^ 2 + 1, by positivity, fun z hz => ?_⟩
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := norm_q_le_one_of_im hz
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hq3 : ‖Work.Kernels.qParamFun z‖ ^ 3 ≤ 1 := pow_nat_le_one hq0 hq1 3
  have hq3nn : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 := pow_nonneg hq0 3
  have hq6 : ‖Work.Kernels.qParamFun z‖ ^ 6 ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    have h : ‖Work.Kernels.qParamFun z‖ ^ 6
        = ‖Work.Kernels.qParamFun z‖ ^ 3 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
    rw [h]
    exact mul_le_of_le_one_right hq3nn hq3
  have hE := norm_E2SRef_le hz
  have hd := h2 z hz
  have hd0 : (0 : ℝ) ≤ ‖dE2S z‖ := norm_nonneg _
  have hc2nn : (0 : ℝ) ≤ C2 * ‖Work.Kernels.qParamFun z‖ ^ 3 :=
    mul_nonneg hC2.le hq3nn
  -- the product bound, all four `mul_le_mul` arguments explicit
  have hprod : ‖E2SRef z‖ * ‖dE2S z‖
      ≤ 99 * (C2 * ‖Work.Kernels.qParamFun z‖ ^ 3) :=
    mul_le_mul hE hd hd0 (by norm_num : (0 : ℝ) ≤ 99)
  have e1 : ‖2 * E2SRef z * dE2S z‖
      ≤ 2 * 99 * C2 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    have hnorm : ‖2 * E2SRef z * dE2S z‖ = 2 * (‖E2SRef z‖ * ‖dE2S z‖) := by
      rw [norm_mul, norm_mul]
      have h2n : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
      rw [h2n]; ring
    rw [hnorm]
    calc 2 * (‖E2SRef z‖ * ‖dE2S z‖) ≤ 2 * (99 * (C2 * ‖Work.Kernels.qParamFun z‖ ^ 3)) :=
          mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)
      _ = 2 * 99 * C2 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
  have e2 : ‖(dE2S z) ^ 2‖ ≤ C2 ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    have hsq : ‖(dE2S z) ^ 2‖ = ‖dE2S z‖ * ‖dE2S z‖ := by
      rw [norm_pow, pow_two]
    rw [hsq]
    calc ‖dE2S z‖ * ‖dE2S z‖
        ≤ (C2 * ‖Work.Kernels.qParamFun z‖ ^ 3) * (C2 * ‖Work.Kernels.qParamFun z‖ ^ 3) :=
          mul_le_mul hd hd hd0 hc2nn
      _ = C2 ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 6 := by ring
      _ ≤ C2 ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3 :=
          mul_le_mul_of_nonneg_left hq6 (pow_nonneg hC2.le 2)
  have hkey : dQ2 z = 2 * E2SRef z * dE2S z + (dE2S z) ^ 2 := rfl
  rw [hkey]
  calc ‖2 * E2SRef z * dE2S z + (dE2S z) ^ 2‖
      ≤ ‖2 * E2SRef z * dE2S z‖ + ‖(dE2S z) ^ 2‖ :=
        norm_add_le _ _
    _ ≤ 2 * 99 * C2 * ‖Work.Kernels.qParamFun z‖ ^ 3
          + C2 ^ 2 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by linarith [e1, e2]
    _ = (2 * 99 * C2 + C2 ^ 2) * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
    _ ≤ (2 * 99 * C2 + C2 ^ 2 + 1) * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
        nlinarith [hq3nn]

/-- **`dSm4 = O(scale τ · ‖q(z)‖³)`.**

Every `calc` step that would otherwise mismatch on the placement of parentheses inside
`norm_mul` is bridged by an explicit `= … := by ring` line, so no goal-level `rw [mul_assoc]`
is needed and the `(c * a) * b` versus `c * (a * b)` trap is bypassed entirely. -/
theorem dSm4_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖dSm4 τ z‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨CQ, hCQ, hQ⟩ := dQ2_bound
  obtain ⟨C4, hC4, h4⟩ := dE4_bound
  obtain ⟨Cc, hCc, hc⟩ := dE4c_bound
  obtain ⟨Cr, hCr, hr⟩ := Work.Asymptotics.K24F.tau_atom_bounds
  refine ⟨1728 * Cr * CQ + 1728 * Cr * C4 + 1728 * 10 * Cr * Cc + 1, 1,
    by positivity, by norm_num, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hz1' : (1 : ℝ) ≤ z.im := by have h2 : (2 : ℝ) ≤ τ.im := hF.2; linarith
  have hz3 : (3 : ℝ) ≤ z.im := by have h2 : (2 : ℝ) ≤ τ.im := hF.2; linarith
  have hr0 : ‖Work.Asymptotics.K24F.r0 τ‖ ≤ Cr * Work.Kernels.scale τ := (hr τ hF).1
  have hr2 : ‖Work.Asymptotics.K24F.r2 τ‖ ≤ Cr * Work.Kernels.scale τ := (hr τ hF).2.1
  have hS : ‖Work.Asymptotics.K24F.S0 z‖ ≤ 3 := Work.Asymptotics.K24F.zS0_norm z hz1'
  have hSn : (0 : ℝ) ≤ ‖Work.Asymptotics.K24F.S0 z‖ := norm_nonneg _
  have hSsq : ‖Work.Asymptotics.K24F.S0 z‖ ^ 2 ≤ 9 := by
    rw [pow_two]
    have h := mul_le_mul hS hS hSn (by norm_num : (0 : ℝ) ≤ 3)
    linarith
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hqnn3 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 := pow_nonneg hq0 3
  have hscale : (0 : ℝ) ≤ Work.Kernels.scale τ := (Work.Kernels.scale_pos τ).le
  have hQ' : ‖dQ2 z‖ ≤ CQ * ‖Work.Kernels.qParamFun z‖ ^ 3 := hQ z hz1'
  have h4' : ‖dE4 z‖ ≤ C4 * ‖Work.Kernels.qParamFun z‖ ^ 3 := h4 z hz1'
  have hc' : ‖dE4c z‖ ≤ Cc * ‖Work.Kernels.qParamFun z‖ ^ 3 := hc z hz1'
  have g1 : ‖(1728 : ℂ) * Work.Asymptotics.K24F.r0 τ * dQ2 z‖
      ≤ (1728 * Cr * CQ) * Work.Kernels.scale τ * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    rw [norm_mul, norm_mul]
    have h27 : ‖(1728 : ℂ)‖ = (1728 : ℝ) := by norm_num
    rw [h27]
    have hstep : ‖Work.Asymptotics.K24F.r0 τ‖ * ‖dQ2 z‖
        ≤ (Cr * Work.Kernels.scale τ) * (CQ * ‖Work.Kernels.qParamFun z‖ ^ 3) :=
      mul_le_mul hr0 hQ' (norm_nonneg _) (mul_nonneg hCr.le hscale)
    calc (1728 : ℝ) * ‖Work.Asymptotics.K24F.r0 τ‖ * ‖dQ2 z‖
        = 1728 * (‖Work.Asymptotics.K24F.r0 τ‖ * ‖dQ2 z‖) := by ring
      _ ≤ 1728 * ((Cr * Work.Kernels.scale τ) * (CQ * ‖Work.Kernels.qParamFun z‖ ^ 3)) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 1728)
      _ = (1728 * Cr * CQ) * Work.Kernels.scale τ * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
  have g2 : ‖(1728 : ℂ) * Work.Asymptotics.K24F.r2 τ * dE4 z‖
      ≤ (1728 * Cr * C4) * Work.Kernels.scale τ * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    rw [norm_mul, norm_mul]
    have h27 : ‖(1728 : ℂ)‖ = (1728 : ℝ) := by norm_num
    rw [h27]
    have hstep : ‖Work.Asymptotics.K24F.r2 τ‖ * ‖dE4 z‖
        ≤ (Cr * Work.Kernels.scale τ) * (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3) :=
      mul_le_mul hr2 h4' (norm_nonneg _) (mul_nonneg hCr.le hscale)
    calc (1728 : ℝ) * ‖Work.Asymptotics.K24F.r2 τ‖ * ‖dE4 z‖
        = 1728 * (‖Work.Asymptotics.K24F.r2 τ‖ * ‖dE4 z‖) := by ring
      _ ≤ 1728 * ((Cr * Work.Kernels.scale τ) * (C4 * ‖Work.Kernels.qParamFun z‖ ^ 3)) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 1728)
      _ = (1728 * Cr * C4) * Work.Kernels.scale τ * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
  have hU1 : ‖(1728 : ℂ) * Work.Asymptotics.K24F.r0 τ * (Work.Asymptotics.K24F.S0 z) ^ 2‖
      ≤ 1728 * 9 * Cr * Work.Kernels.scale τ := by
    rw [norm_mul, norm_mul, norm_pow]
    have h27 : ‖(1728 : ℂ)‖ = (1728 : ℝ) := by norm_num
    rw [h27]
    have hstep : ‖Work.Asymptotics.K24F.r0 τ‖ * ‖Work.Asymptotics.K24F.S0 z‖ ^ 2
        ≤ (Cr * Work.Kernels.scale τ) * 9 :=
      mul_le_mul hr0 hSsq (pow_nonneg hSn 2) (mul_nonneg hCr.le hscale)
    calc (1728 : ℝ) * ‖Work.Asymptotics.K24F.r0 τ‖ * ‖Work.Asymptotics.K24F.S0 z‖ ^ 2
        = 1728 * (‖Work.Asymptotics.K24F.r0 τ‖ * ‖Work.Asymptotics.K24F.S0 z‖ ^ 2) := by ring
      _ ≤ 1728 * ((Cr * Work.Kernels.scale τ) * 9) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 1728)
      _ = 1728 * 9 * Cr * Work.Kernels.scale τ := by ring
  have hU2 : ‖(1728 : ℂ) * Work.Asymptotics.K24F.r2 τ‖
      ≤ 1728 * Cr * Work.Kernels.scale τ := by
    rw [norm_mul]
    have h27 : ‖(1728 : ℂ)‖ = (1728 : ℝ) := by norm_num
    rw [h27]
    have hstep : ‖Work.Asymptotics.K24F.r2 τ‖ ≤ Cr * Work.Kernels.scale τ := hr2
    calc (1728 : ℝ) * ‖Work.Asymptotics.K24F.r2 τ‖
        = 1728 * ‖Work.Asymptotics.K24F.r2 τ‖ := by ring
      _ ≤ 1728 * (Cr * Work.Kernels.scale τ) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 1728)
      _ = 1728 * Cr * Work.Kernels.scale τ := by ring
  have hU : ‖(1728 : ℂ) * Work.Asymptotics.K24F.r0 τ * (Work.Asymptotics.K24F.S0 z) ^ 2
        + (1728 : ℂ) * Work.Asymptotics.K24F.r2 τ‖
      ≤ 1728 * 9 * Cr * Work.Kernels.scale τ + 1728 * Cr * Work.Kernels.scale τ :=
    le_trans (norm_add_le _ _) (add_le_add hU1 hU2)
  have g3 : ‖((1728 : ℂ) * Work.Asymptotics.K24F.r0 τ * (Work.Asymptotics.K24F.S0 z) ^ 2
          + (1728 : ℂ) * Work.Asymptotics.K24F.r2 τ) * dE4c z‖
      ≤ (1728 * 10 * Cr * Cc) * Work.Kernels.scale τ * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    rw [norm_mul]
    have hstep : (1728 * 9 * Cr * Work.Kernels.scale τ + 1728 * Cr * Work.Kernels.scale τ)
          * ‖dE4c z‖
        ≤ (1728 * 9 * Cr * Work.Kernels.scale τ + 1728 * Cr * Work.Kernels.scale τ)
          * (Cc * ‖Work.Kernels.qParamFun z‖ ^ 3) :=
      mul_le_mul_of_nonneg_left hc'
        (by positivity : (0 : ℝ) ≤ 1728 * 9 * Cr * Work.Kernels.scale τ
          + 1728 * Cr * Work.Kernels.scale τ)
    calc ‖(1728 : ℂ) * Work.Asymptotics.K24F.r0 τ * (Work.Asymptotics.K24F.S0 z) ^ 2
            + (1728 : ℂ) * Work.Asymptotics.K24F.r2 τ‖ * ‖dE4c z‖
        ≤ (1728 * 9 * Cr * Work.Kernels.scale τ + 1728 * Cr * Work.Kernels.scale τ)
            * (Cc * ‖Work.Kernels.qParamFun z‖ ^ 3) :=
          mul_le_mul hU hc' (norm_nonneg _)
            (by positivity : (0 : ℝ) ≤ 1728 * 9 * Cr * Work.Kernels.scale τ
              + 1728 * Cr * Work.Kernels.scale τ)
      _ = (1728 * 10 * Cr * Cc) * Work.Kernels.scale τ * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
          ring
  have hkey : dSm4 τ z = (1728 : ℂ) * Work.Asymptotics.K24F.r0 τ * dQ2 z
        + (1728 : ℂ) * Work.Asymptotics.K24F.r2 τ * dE4 z
        - ((1728 : ℂ) * Work.Asymptotics.K24F.r0 τ * (Work.Asymptotics.K24F.S0 z) ^ 2
            + (1728 : ℂ) * Work.Asymptotics.K24F.r2 τ) * dE4c z := rfl
  rw [hkey]
  have hsub := norm_sub_le ((1728 : ℂ) * Work.Asymptotics.K24F.r0 τ * dQ2 z
        + (1728 : ℂ) * Work.Asymptotics.K24F.r2 τ * dE4 z)
      (((1728 : ℂ) * Work.Asymptotics.K24F.r0 τ * (Work.Asymptotics.K24F.S0 z) ^ 2
          + (1728 : ℂ) * Work.Asymptotics.K24F.r2 τ) * dE4c z)
  have hadd := norm_add_le ((1728 : ℂ) * Work.Asymptotics.K24F.r0 τ * dQ2 z)
      ((1728 : ℂ) * Work.Asymptotics.K24F.r2 τ * dE4 z)
  have hsum : (1728 * Cr * CQ) * Work.Kernels.scale τ * ‖Work.Kernels.qParamFun z‖ ^ 3
        + (1728 * Cr * C4) * Work.Kernels.scale τ * ‖Work.Kernels.qParamFun z‖ ^ 3
        + (1728 * 10 * Cr * Cc) * Work.Kernels.scale τ * ‖Work.Kernels.qParamFun z‖ ^ 3
      = (1728 * Cr * CQ + 1728 * Cr * C4 + 1728 * 10 * Cr * Cc)
          * Work.Kernels.scale τ * ‖Work.Kernels.qParamFun z‖ ^ 3 := by ring
  have hfinal : (1728 * Cr * CQ + 1728 * Cr * C4 + 1728 * 10 * Cr * Cc)
        * Work.Kernels.scale τ * ‖Work.Kernels.qParamFun z‖ ^ 3
      ≤ (1728 * Cr * CQ + 1728 * Cr * C4 + 1728 * 10 * Cr * Cc + 1)
          * (Work.Kernels.scale τ) ^ (1 : ℝ) * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
    rw [Real.rpow_one]
    have hb : (0 : ℝ) ≤ Work.Kernels.scale τ * ‖Work.Kernels.qParamFun z‖ ^ 3 :=
      mul_nonneg hscale hqnn3
    nlinarith [hb]
  linarith [hsub, hadd, g1, g2, g3, hsum, hfinal]

end

end Work.Asymptotics.KhatE1Core
