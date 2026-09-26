/-
# The two `G_{1,0}` strip estimates of the far-region pair gate

This module proves the two remaining inputs of `Work.Asymptotics.pair_gate_far`:

* `PGGcusp10StripBound` : `‖G_{1,0}(w)‖ ≤ 5 (1 + ‖w‖) ‖nomeQ w‖` on the fundamental strip,
* `PGGcusp10DeltaBound` : `‖G_{1,0}(w+1) - G_{1,0}(w) + i·nomeQ w‖ ≤ 10^5 ‖nomeQ w‖²`.

Both are read off the reduced formulas (`Gcusp10_reduced`, `dg10_eq`)

  `2 G_{1,0} = w·Pnum + Cnum + W3`,  `2 (G_{1,0}(w+1) - G_{1,0}(w)) = Pnum + i·Xnum/1152`,

together with the explicit second-order `q`-expansions of `E₂,E₄,E₆` (`EisensteinQExp`), of the
theta quartics (`ThetaQExp`), of `𝓛 = Lfun` (`LfunQExp`), the constant `cuspL ℓ = 4 log 2`
(`CuspL_eq`) and the `S`-slash identities for `ξ₂, ξ₄` (`XiSlashS`).
-/
import Mathlib
import Submission.Work.Asymptotics.PGFar.Defs
import Submission.Work.Asymptotics.PGFar.Reduction
import Submission.Work.Asymptotics.FunnelAsm.StripBoundsProofsA
import Submission.Work.Asymptotics.FunnelAsm.EisensteinQExpA
import Submission.Work.Asymptotics.ThetaQExp
import Submission.Work.Asymptotics.LfunQExp
import Submission.Work.Asymptotics.CuspL_eq
import Submission.Work.Asymptotics.LogLambdaData_L_eq_Lfun
import Submission.Work.Residues.XiSlashS
import Submission.Work.Kernels.KernelFacts.psi2_T2
import Submission.Work.Residues.ThetaAux
import Submission.Work.Residues.LamSExpBound

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup
open scoped MatrixGroups ModularForm Modular Manifold Bundle

set_option maxHeartbeats 4000000

noncomputable section

/-! ## Generic polynomial estimates -/

/-- A polynomial in `q` is bounded by the weighted `ℓ¹`-norm of its coefficients. -/
lemma norm_sum_pow_le (q : ℂ) (r : ℝ) (hr : ‖q‖ ≤ r) (c : ℕ → ℂ) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, c k * q ^ k‖ ≤ ∑ k ∈ Finset.range n, ‖c k‖ * r ^ k := by
  calc ‖∑ k ∈ Finset.range n, c k * q ^ k‖ ≤ ∑ k ∈ Finset.range n, ‖c k * q ^ k‖ :=
        norm_sum_le _ _
    _ = ∑ k ∈ Finset.range n, ‖c k‖ * ‖q‖ ^ k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [norm_mul, norm_pow]
    _ ≤ ∑ k ∈ Finset.range n, ‖c k‖ * r ^ k := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hr k) (norm_nonneg _)

lemma norm_deg3_le (e a0 a1 a2 a3 : ℂ) :
    ‖a0 + a1 * e + a2 * e ^ 2 + a3 * e ^ 3‖
      ≤ ‖a0‖ + ‖a1‖ * ‖e‖ + ‖a2‖ * ‖e‖ ^ 2 + ‖a3‖ * ‖e‖ ^ 3 := by
  have h1 := norm_add_le (a0 + a1 * e + a2 * e ^ 2) (a3 * e ^ 3)
  have h2 := norm_add_le (a0 + a1 * e) (a2 * e ^ 2)
  have h3 := norm_add_le a0 (a1 * e)
  simp only [norm_mul, norm_pow] at h1 h2 h3
  linarith

lemma norm_deg4_le (e a0 a1 a2 a3 a4 : ℂ) :
    ‖a0 + a1 * e + a2 * e ^ 2 + a3 * e ^ 3 + a4 * e ^ 4‖
      ≤ ‖a0‖ + ‖a1‖ * ‖e‖ + ‖a2‖ * ‖e‖ ^ 2 + ‖a3‖ * ‖e‖ ^ 3 + ‖a4‖ * ‖e‖ ^ 4 := by
  have h1 := norm_add_le (a0 + a1 * e + a2 * e ^ 2 + a3 * e ^ 3) (a4 * e ^ 4)
  have h2 := norm_add_le (a0 + a1 * e + a2 * e ^ 2) (a3 * e ^ 3)
  have h3 := norm_add_le (a0 + a1 * e) (a2 * e ^ 2)
  have h4 := norm_add_le a0 (a1 * e)
  simp only [norm_mul, norm_pow] at h1 h2 h3 h4
  linarith

lemma norm_four_le (a b c d : ℂ) : ‖a + b - c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have h : a + b - c + d = (a + b) + (-c + d) := by ring
  rw [h]
  have h1 := norm_add_le (a + b) (-c + d)
  have h2 := norm_add_le a b
  have h3 := norm_add_le (-c) d
  rw [norm_neg] at h3
  linarith

/-! ## Elementary strip facts for the nome -/

/-- On the strip, `‖nomeE w‖ ≤ 1/500`. -/
lemma nomeE_norm_le_inv500 (w : UpperHalfPlane) (h : Strip w) : ‖nomeE w‖ ≤ 1 / 500 := by
  have hQ : ‖nomeQ w‖ ≤ 1 / 280000 := (strip_facts w h).1
  have h2 : ‖nomeE w‖ ^ 2 ≤ (1 / 500 : ℝ) ^ 2 := by
    rw [← norm_nomeQ_sq w]
    norm_num
    linarith [hQ]
  have h3 := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 500)] at h3

lemma nomeE_pow5_le (w : UpperHalfPlane) (h : Strip w) :
    ‖nomeE w‖ ^ 5 ≤ (1 / 500) * ‖nomeQ w‖ ^ 2 := by
  have h1 := nomeE_norm_le_inv500 w h
  have h2 : ‖nomeE w‖ ^ 2 = ‖nomeQ w‖ := (norm_nomeQ_sq w).symm
  calc ‖nomeE w‖ ^ 5 = ‖nomeE w‖ * (‖nomeE w‖ ^ 2) ^ 2 := by ring
    _ = ‖nomeE w‖ * ‖nomeQ w‖ ^ 2 := by rw [h2]
    _ ≤ (1 / 500) * ‖nomeQ w‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)

lemma nomeE_pow3_le (w : UpperHalfPlane) (h : Strip w) :
    ‖nomeE w‖ ^ 3 ≤ (1 / 250000) * ‖nomeE w‖ := by
  have h1 : ‖nomeE w‖ ^ 2 ≤ (1 / 250000 : ℝ) := by
    have hQ : ‖nomeQ w‖ ≤ 1 / 280000 := (strip_facts w h).1
    have h2 : ‖nomeE w‖ ^ 2 ≤ (1 / 500 : ℝ) ^ 2 := by
      rw [← norm_nomeQ_sq w]
      norm_num
      linarith [hQ]
    linarith [h2]
  have h3 : ‖nomeE w‖ ^ 3 = ‖nomeE w‖ ^ 2 * ‖nomeE w‖ := by ring
  rw [h3]
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

lemma nomeQ_pow3_le (w : UpperHalfPlane) (h : Strip w) :
    ‖nomeQ w‖ ^ 3 ≤ (1 / 280000) * ‖nomeQ w‖ ^ 2 := by
  have hQ : ‖nomeQ w‖ ≤ 1 / 280000 := (strip_facts w h).1
  have h3 : ‖nomeQ w‖ ^ 3 = ‖nomeQ w‖ * ‖nomeQ w‖ ^ 2 := by ring
  rw [h3]
  exact mul_le_mul_of_nonneg_right hQ (by positivity)

lemma nomeQ_pow4_le (w : UpperHalfPlane) (h : Strip w) :
    ‖nomeQ w‖ ^ 4 ≤ (1 / 280000) * ‖nomeQ w‖ ^ 2 := by
  have hQ : ‖nomeQ w‖ ≤ 1 / 280000 := (strip_facts w h).1
  have hnn : (0 : ℝ) ≤ ‖nomeQ w‖ := norm_nonneg _
  have h2 : ‖nomeQ w‖ ^ 2 ≤ ‖nomeQ w‖ := by
    calc ‖nomeQ w‖ ^ 2 ≤ ‖nomeQ w‖ ^ 1 :=
          pow_le_pow_of_le_one hnn (by linarith) (by norm_num)
      _ = ‖nomeQ w‖ := by ring
  calc ‖nomeQ w‖ ^ 4 ≤ (1 / 280000) * ‖nomeQ w‖ ^ 2 := by
        rw [show ‖nomeQ w‖ ^ 4 = ‖nomeQ w‖ ^ 2 * ‖nomeQ w‖ ^ 2 by ring]
        nlinarith [h2, hQ, hnn]

/-- `‖nomeQ w‖² ≤ 1/280000` on the strip. -/
lemma nomeQ_sq_le (w : UpperHalfPlane) (h : Strip w) : ‖nomeQ w‖ ^ 2 ≤ 1 / 280000 := by
  have hQ : ‖nomeQ w‖ ≤ 1 / 280000 := (strip_facts w h).1
  have hnn : (0 : ℝ) ≤ ‖nomeQ w‖ := norm_nonneg _
  nlinarith [hQ, hnn]

/-- `C · ‖nomeE w‖⁵ ≤ (C/500) · ‖nomeQ w‖²` on the strip. -/
lemma nomeE_pow5_mul_le (w : UpperHalfPlane) (h : Strip w) (C : ℝ) (hC : 0 ≤ C) :
    C * ‖nomeE w‖ ^ 5 ≤ (C / 500) * ‖nomeQ w‖ ^ 2 := by
  have h1 := nomeE_pow5_le w h
  calc C * ‖nomeE w‖ ^ 5 ≤ C * ((1 / 500) * ‖nomeQ w‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 hC
    _ = (C / 500) * ‖nomeQ w‖ ^ 2 := by ring

/-- The three power bounds for `‖nomeE w‖` used to bound the theta truncations. -/
lemma nomeE_pow_le_inv500 (w : UpperHalfPlane) (h : Strip w) :
    ‖nomeE w‖ ≤ 1 / 500 ∧ ‖nomeE w‖ ^ 2 ≤ (1 / 500 : ℝ) ^ 2
      ∧ ‖nomeE w‖ ^ 3 ≤ (1 / 500 : ℝ) ^ 3 ∧ ‖nomeE w‖ ^ 4 ≤ (1 / 500 : ℝ) ^ 4 := by
  have he := nomeE_norm_le_inv500 w h
  exact ⟨he, pow_le_pow_left₀ (norm_nonneg _) he 2, pow_le_pow_left₀ (norm_nonneg _) he 3,
    pow_le_pow_left₀ (norm_nonneg _) he 4⟩


/-! ## Norms of the truncated theta quartics -/

lemma Utrunc_norm (w : UpperHalfPlane) (h : Strip w) :
    ‖(1 : ℂ) + 8 * nomeE w + 24 * (nomeE w) ^ 2 + 32 * (nomeE w) ^ 3
      + 24 * (nomeE w) ^ 4‖ ≤ 3 / 2 := by
  obtain ⟨he, h2, h3, h4⟩ := nomeE_pow_le_inv500 w h
  have h := norm_deg4_le (nomeE w) 1 8 24 32 24
  simp only [norm_one, Complex.norm_ofNat] at h
  refine le_trans h ?_
  nlinarith [norm_nonneg (nomeE w), he, h2, h3, h4]

lemma Wtrunc_norm (w : UpperHalfPlane) (h : Strip w) :
    ‖(1 : ℂ) - 8 * nomeE w + 24 * (nomeE w) ^ 2 - 32 * (nomeE w) ^ 3
      + 24 * (nomeE w) ^ 4‖ ≤ 3 / 2 := by
  obtain ⟨he, h2, h3, h4⟩ := nomeE_pow_le_inv500 w h
  have h := norm_deg4_le (nomeE w) 1 (-8) 24 (-32) 24
  simp only [norm_one, Complex.norm_ofNat, norm_neg] at h
  have heq : ((1 : ℂ) - 8 * nomeE w + 24 * (nomeE w) ^ 2 - 32 * (nomeE w) ^ 3
      + 24 * (nomeE w) ^ 4)
      = ((1 : ℂ) + (-8) * nomeE w + 24 * (nomeE w) ^ 2 + (-32) * (nomeE w) ^ 3
        + 24 * (nomeE w) ^ 4) := by ring
  rw [heq]
  refine le_trans h ?_
  nlinarith [norm_nonneg (nomeE w), he, h2, h3, h4]

lemma Vtrunc_norm (w : UpperHalfPlane) (h : Strip w) :
    ‖(16 : ℂ) * nomeE w + 64 * (nomeE w) ^ 3‖ ≤ 1 / 4 := by
  have he := nomeE_norm_le_inv500 w h
  have h3 := pow_le_pow_left₀ (norm_nonneg (nomeE w)) he 3
  have h := norm_deg3_le (nomeE w) 0 16 0 64
  simp only [norm_zero, Complex.norm_ofNat, zero_mul, zero_add, add_zero] at h
  refine le_trans h ?_
  nlinarith [norm_nonneg (nomeE w), he, h3]

lemma Unorm (w : UpperHalfPlane) (h : Strip w) : ‖Work.Kernels.UFun w‖ ≤ 2 := by
  have h1 : ‖Work.Kernels.UFun w - (1 + 8 * nomeE w + 24 * (nomeE w) ^ 2
      + 32 * (nomeE w) ^ 3 + 24 * (nomeE w) ^ 4)‖ ≤ 1 / 2 := by
    refine le_trans (ThetaQExp.1 w h.2) ?_
    have hq := nomeE_pow5_mul_le w h 10000 (by norm_num)
    have hq2 := nomeQ_sq_le w h
    have hqnn : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 2 := by positivity
    nlinarith [hq, hq2, hqnn]
  have h2 := Utrunc_norm w h
  calc ‖Work.Kernels.UFun w‖
      = ‖(Work.Kernels.UFun w - (1 + 8 * nomeE w + 24 * (nomeE w) ^ 2
          + 32 * (nomeE w) ^ 3 + 24 * (nomeE w) ^ 4))
        + (1 + 8 * nomeE w + 24 * (nomeE w) ^ 2 + 32 * (nomeE w) ^ 3
          + 24 * (nomeE w) ^ 4)‖ := by rw [sub_add_cancel]
    _ ≤ ‖Work.Kernels.UFun w - (1 + 8 * nomeE w + 24 * (nomeE w) ^ 2
          + 32 * (nomeE w) ^ 3 + 24 * (nomeE w) ^ 4)‖
        + ‖(1 : ℂ) + 8 * nomeE w + 24 * (nomeE w) ^ 2 + 32 * (nomeE w) ^ 3
          + 24 * (nomeE w) ^ 4‖ := norm_add_le _ _
    _ ≤ 2 := by linarith

lemma Wnorm (w : UpperHalfPlane) (h : Strip w) : ‖Work.Kernels.WFun w‖ ≤ 2 := by
  have h1 : ‖Work.Kernels.WFun w - (1 - 8 * nomeE w + 24 * (nomeE w) ^ 2
      - 32 * (nomeE w) ^ 3 + 24 * (nomeE w) ^ 4)‖ ≤ 1 / 2 := by
    refine le_trans (ThetaQExp.2.1 w h.2) ?_
    have hq := nomeE_pow5_mul_le w h 10000 (by norm_num)
    have hq2 := nomeQ_sq_le w h
    have hqnn : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 2 := by positivity
    nlinarith [hq, hq2, hqnn]
  have h2 := Wtrunc_norm w h
  calc ‖Work.Kernels.WFun w‖
      = ‖(Work.Kernels.WFun w - (1 - 8 * nomeE w + 24 * (nomeE w) ^ 2
          - 32 * (nomeE w) ^ 3 + 24 * (nomeE w) ^ 4))
        + (1 - 8 * nomeE w + 24 * (nomeE w) ^ 2 - 32 * (nomeE w) ^ 3
          + 24 * (nomeE w) ^ 4)‖ := by rw [sub_add_cancel]
    _ ≤ ‖Work.Kernels.WFun w - (1 - 8 * nomeE w + 24 * (nomeE w) ^ 2
          - 32 * (nomeE w) ^ 3 + 24 * (nomeE w) ^ 4)‖
        + ‖(1 : ℂ) - 8 * nomeE w + 24 * (nomeE w) ^ 2 - 32 * (nomeE w) ^ 3
          + 24 * (nomeE w) ^ 4‖ := norm_add_le _ _
    _ ≤ 2 := by linarith

lemma Vnorm (w : UpperHalfPlane) (h : Strip w) : ‖Work.Kernels.VFun w‖ ≤ 1 / 2 := by
  have h1 : ‖Work.Kernels.VFun w - (16 * nomeE w + 64 * (nomeE w) ^ 3)‖ ≤ 1 / 100 := by
    refine le_trans (ThetaQExp.2.2 w h.2) ?_
    have hq := nomeE_pow5_mul_le w h 10000 (by norm_num)
    have hq2 := nomeQ_sq_le w h
    have hqnn : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 2 := by positivity
    nlinarith [hq, hq2, hqnn]
  have h2 := Vtrunc_norm w h
  calc ‖Work.Kernels.VFun w‖
      = ‖(Work.Kernels.VFun w - (16 * nomeE w + 64 * (nomeE w) ^ 3))
        + (16 * nomeE w + 64 * (nomeE w) ^ 3)‖ := by rw [sub_add_cancel]
    _ ≤ ‖Work.Kernels.VFun w - (16 * nomeE w + 64 * (nomeE w) ^ 3)‖
        + ‖(16 : ℂ) * nomeE w + 64 * (nomeE w) ^ 3‖ := norm_add_le _ _
    _ ≤ 1 / 2 := by linarith

/-! ## The theta quartics on the strip -/

lemma xi_strip_close (w : UpperHalfPlane) (h : Strip w) :
    ‖Work.Kernels.xi2Fun w - (2 + 48 * nomeQ w + 48 * (nomeQ w) ^ 2)‖ ≤ 1000 * ‖nomeQ w‖ ^ 2
      ∧ ‖Work.Kernels.xi4Fun w - (2 - 288 * nomeQ w - 1824 * (nomeQ w) ^ 2)‖
          ≤ 10000 * ‖nomeQ w‖ ^ 2 := by
  obtain ⟨hU, hW, hV⟩ := ThetaQExp
  have hUw := hU w h.2
  have hWw := hW w h.2
  have hVw := hV w h.2
  have hUn := Unorm w h
  have hWn := Wnorm w h
  have hVn := Vnorm w h
  have hPu := Utrunc_norm w h
  have hPw := Wtrunc_norm w h
  have hPv := Vtrunc_norm w h
  have he5 := nomeE_pow5_le w h
  have hq2 : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 2 := by positivity
  have hQ3 := nomeQ_pow3_le w h
  have hQ4nonneg : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 4 := by positivity
  constructor
  · have hkey : Work.Kernels.xi2Fun w - (2 + 48 * nomeQ w + 48 * (nomeQ w) ^ 2)
        = (Work.Kernels.UFun w - (1 + 8 * nomeE w + 24 * (nomeE w) ^ 2 + 32 * (nomeE w) ^ 3
              + 24 * (nomeE w) ^ 4))
          + (Work.Kernels.WFun w - (1 - 8 * nomeE w + 24 * (nomeE w) ^ 2 - 32 * (nomeE w) ^ 3
              + 24 * (nomeE w) ^ 4)) := by
      show (Work.Kernels.UFun w + Work.Kernels.WFun w) - (2 + 48 * nomeQ w + 48 * (nomeQ w) ^ 2)
          = _
      rw [nomeE_sq w]
      ring
    rw [hkey]
    refine le_trans (norm_add_le _ _) ?_
    have hqq : (20000 : ℝ) * ‖nomeE w‖ ^ 5 ≤ 1000 * ‖nomeQ w‖ ^ 2 := by
      have hq := nomeE_pow5_mul_le w h 20000 (by norm_num)
      nlinarith [hq, hq2]
    linarith [hUw, hWw, hqq]
  · have hkey : Work.Kernels.xi4Fun w - (2 - 288 * nomeQ w - 1824 * (nomeQ w) ^ 2)
        = ((Work.Kernels.UFun w) ^ 2
              - (1 + 8 * nomeE w + 24 * (nomeE w) ^ 2 + 32 * (nomeE w) ^ 3
                + 24 * (nomeE w) ^ 4) ^ 2)
          + ((Work.Kernels.WFun w) ^ 2
              - (1 - 8 * nomeE w + 24 * (nomeE w) ^ 2 - 32 * (nomeE w) ^ 3
                + 24 * (nomeE w) ^ 4) ^ 2)
          - 2 * ((Work.Kernels.VFun w) ^ 2 - (16 * nomeE w + 64 * (nomeE w) ^ 3) ^ 2)
          + ((1 + 8 * nomeE w + 24 * (nomeE w) ^ 2 + 32 * (nomeE w) ^ 3
                + 24 * (nomeE w) ^ 4) ^ 2
              + (1 - 8 * nomeE w + 24 * (nomeE w) ^ 2 - 32 * (nomeE w) ^ 3
                + 24 * (nomeE w) ^ 4) ^ 2
              - 2 * (16 * nomeE w + 64 * (nomeE w) ^ 3) ^ 2
              - (2 - 288 * nomeQ w - 1824 * (nomeQ w) ^ 2)) := by
      show (Work.Kernels.UFun w ^ 2 + Work.Kernels.WFun w ^ 2 - 2 * Work.Kernels.VFun w ^ 2)
          - (2 - 288 * nomeQ w - 1824 * (nomeQ w) ^ 2) = _
      rw [nomeE_sq w]
      ring
    have hsqU : ‖(Work.Kernels.UFun w) ^ 2
        - (1 + 8 * nomeE w + 24 * (nomeE w) ^ 2 + 32 * (nomeE w) ^ 3
          + 24 * (nomeE w) ^ 4) ^ 2‖ ≤ 40000 * ‖nomeE w‖ ^ 5 := by
      have h := norm_sq_sub_sq_le (Work.Kernels.UFun w)
        (1 + 8 * nomeE w + 24 * (nomeE w) ^ 2 + 32 * (nomeE w) ^ 3 + 24 * (nomeE w) ^ 4)
      have hb : ‖(1 : ℂ) + 8 * nomeE w + 24 * (nomeE w) ^ 2 + 32 * (nomeE w) ^ 3
          + 24 * (nomeE w) ^ 4‖ ≤ 3 / 2 := hPu
      have hb2 : ‖Work.Kernels.UFun w‖
          + ‖(1 : ℂ) + 8 * nomeE w + 24 * (nomeE w) ^ 2 + 32 * (nomeE w) ^ 3
            + 24 * (nomeE w) ^ 4‖ ≤ 4 := by linarith [hUn, hb]
      have h1 : ‖Work.Kernels.UFun w - (1 + 8 * nomeE w + 24 * (nomeE w) ^ 2
          + 32 * (nomeE w) ^ 3 + 24 * (nomeE w) ^ 4)‖
          * (‖Work.Kernels.UFun w‖ + ‖(1 : ℂ) + 8 * nomeE w + 24 * (nomeE w) ^ 2
            + 32 * (nomeE w) ^ 3 + 24 * (nomeE w) ^ 4‖) ≤ (10000 * ‖nomeE w‖ ^ 5) * 4 :=
        mul_le_mul hUw hb2 (by positivity) (by norm_num)
      nlinarith [h, h1, pow_nonneg (norm_nonneg (nomeE w)) 5]
    have hsqW : ‖(Work.Kernels.WFun w) ^ 2
        - (1 - 8 * nomeE w + 24 * (nomeE w) ^ 2 - 32 * (nomeE w) ^ 3
          + 24 * (nomeE w) ^ 4) ^ 2‖ ≤ 40000 * ‖nomeE w‖ ^ 5 := by
      have h := norm_sq_sub_sq_le (Work.Kernels.WFun w)
        (1 - 8 * nomeE w + 24 * (nomeE w) ^ 2 - 32 * (nomeE w) ^ 3 + 24 * (nomeE w) ^ 4)
      have hb : ‖(1 : ℂ) - 8 * nomeE w + 24 * (nomeE w) ^ 2 - 32 * (nomeE w) ^ 3
          + 24 * (nomeE w) ^ 4‖ ≤ 3 / 2 := hPw
      have hb2 : ‖Work.Kernels.WFun w‖
          + ‖(1 : ℂ) - 8 * nomeE w + 24 * (nomeE w) ^ 2 - 32 * (nomeE w) ^ 3
            + 24 * (nomeE w) ^ 4‖ ≤ 4 := by linarith [hWn, hb]
      have h1 : ‖Work.Kernels.WFun w - (1 - 8 * nomeE w + 24 * (nomeE w) ^ 2
          - 32 * (nomeE w) ^ 3 + 24 * (nomeE w) ^ 4)‖
          * (‖Work.Kernels.WFun w‖ + ‖(1 : ℂ) - 8 * nomeE w + 24 * (nomeE w) ^ 2
            - 32 * (nomeE w) ^ 3 + 24 * (nomeE w) ^ 4‖) ≤ (10000 * ‖nomeE w‖ ^ 5) * 4 :=
        mul_le_mul hWw hb2 (by positivity) (by norm_num)
      nlinarith [h, h1, pow_nonneg (norm_nonneg (nomeE w)) 5]
    have hsqV : ‖(Work.Kernels.VFun w) ^ 2 - (16 * nomeE w + 64 * (nomeE w) ^ 3) ^ 2‖
        ≤ 20000 * ‖nomeE w‖ ^ 5 := by
      have h := norm_sq_sub_sq_le (Work.Kernels.VFun w) (16 * nomeE w + 64 * (nomeE w) ^ 3)
      have hb2 : ‖Work.Kernels.VFun w‖ + ‖(16 : ℂ) * nomeE w + 64 * (nomeE w) ^ 3‖ ≤ 1 := by
        linarith [hVn, hPv]
      have h1 : ‖Work.Kernels.VFun w - (16 * nomeE w + 64 * (nomeE w) ^ 3)‖
          * (‖Work.Kernels.VFun w‖ + ‖(16 : ℂ) * nomeE w + 64 * (nomeE w) ^ 3‖)
          ≤ (10000 * ‖nomeE w‖ ^ 5) * 1 :=
        mul_le_mul hVw hb2 (by positivity) (by norm_num)
      nlinarith [h, h1, pow_nonneg (norm_nonneg (nomeE w)) 5]
    have hpoly : (1 + 8 * nomeE w + 24 * (nomeE w) ^ 2 + 32 * (nomeE w) ^ 3
          + 24 * (nomeE w) ^ 4) ^ 2
        + (1 - 8 * nomeE w + 24 * (nomeE w) ^ 2 - 32 * (nomeE w) ^ 3
          + 24 * (nomeE w) ^ 4) ^ 2
        - 2 * (16 * nomeE w + 64 * (nomeE w) ^ 3) ^ 2 - (2 - 288 * nomeQ w - 1824 * (nomeQ w) ^ 2)
        = -3840 * (nomeQ w) ^ 3 + 1152 * (nomeQ w) ^ 4 := by
      rw [nomeE_sq w]
      ring
    have hpolyb : ‖-3840 * (nomeQ w) ^ 3 + 1152 * (nomeQ w) ^ 4‖ ≤ 1000 * ‖nomeQ w‖ ^ 2 := by
      have h1 := norm_add_le ((-3840 : ℂ) * (nomeQ w) ^ 3) (1152 * (nomeQ w) ^ 4)
      simp only [norm_mul, norm_pow, norm_neg, Complex.norm_ofNat] at h1
      have h4 := nomeQ_pow4_le w h
      have h3 : (3840 : ℝ) * ‖nomeQ w‖ ^ 3 + 1152 * ‖nomeQ w‖ ^ 4 ≤ 1000 * ‖nomeQ w‖ ^ 2 := by
        nlinarith [hQ3, h4, hq2]
      linarith [h1, h3]
    rw [hkey, hpoly]
    refine le_trans (norm_four_le _ _ _ _) ?_
    have h2 : ‖(2 : ℂ) * ((Work.Kernels.VFun w) ^ 2 - (16 * nomeE w + 64 * (nomeE w) ^ 3) ^ 2)‖
        ≤ 2 * (20000 * ‖nomeE w‖ ^ 5) := by
      rw [norm_mul, Complex.norm_ofNat]
      linarith [hsqV]
    have hfin : 40000 * ‖nomeE w‖ ^ 5 + 40000 * ‖nomeE w‖ ^ 5 + 2 * (20000 * ‖nomeE w‖ ^ 5)
        + 1000 * ‖nomeQ w‖ ^ 2 ≤ 10000 * ‖nomeQ w‖ ^ 2 := by
      have hq := nomeE_pow5_mul_le w h 120000 (by norm_num)
      nlinarith [hq, hq2]
    linarith [hsqU, hsqW, h2, hpolyb, hfin]


/-! ## The truncated Eisenstein products -/

lemma E10_trunc (w : UpperHalfPlane) (h : Strip w) :
    ‖Work.Kernels.E10Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
        * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)‖ ≤ 3000000 * ‖nomeQ w‖ ^ 3 := by
  obtain ⟨_, he4, he6⟩ := EisensteinQExp
  obtain ⟨_, hb4, _, _, hE4, hE6⟩ := strip_trunc_bounds w h
  have h4 := he4 w h.2
  have h6 := he6 w h.2
  have hkey : Work.Kernels.E10Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
        * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)
      = (Work.Kernels.E4Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2))
          * Work.Kernels.E6Fun w
        + (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
          * (Work.Kernels.E6Fun w - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)) := by
    show (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)
        - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
          * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)
      = (Work.Kernels.E4Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2))
          * Work.Kernels.E6Fun w
        + (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
          * (Work.Kernels.E6Fun w - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
    ring
  rw [hkey]
  have h1 : ‖(Work.Kernels.E4Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2))
      * Work.Kernels.E6Fun w‖ ≤ (50000 * ‖nomeQ w‖ ^ 3) * 2 := by
    rw [norm_mul]
    exact mul_le_mul h4 hE6 (norm_nonneg _) (by positivity)
  have h2 : ‖(1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
      * (Work.Kernels.E6Fun w - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))‖
      ≤ 2 * (1000000 * ‖nomeQ w‖ ^ 3) := by
    rw [norm_mul]
    exact mul_le_mul hb4 h6 (norm_nonneg _) (by positivity)
  have hsum := norm_add_le ((Work.Kernels.E4Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2))
      * Work.Kernels.E6Fun w)
    ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
      * (Work.Kernels.E6Fun w - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)))
  have hq3 : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
  linarith [h1, h2, hsum, hq3]

lemma E8_trunc (w : UpperHalfPlane) (h : Strip w) :
    ‖Work.Kernels.E8Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2‖
      ≤ 1000000 * ‖nomeQ w‖ ^ 3 := by
  obtain ⟨_, he4, _⟩ := EisensteinQExp
  obtain ⟨_, hb4, _, _, hE4, _⟩ := strip_trunc_bounds w h
  have h4 := he4 w h.2
  have hkey : Work.Kernels.E8Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2
      = (Work.Kernels.E4Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2))
        * (Work.Kernels.E4Fun w + (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)) := by
    show (Work.Kernels.E4Fun w) ^ 2 - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2
      = (Work.Kernels.E4Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2))
        * (Work.Kernels.E4Fun w + (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2))
    ring
  rw [hkey, norm_mul]
  have hb : ‖Work.Kernels.E4Fun w + (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)‖ ≤ 4 := by
    have := norm_add_le (Work.Kernels.E4Fun w)
      (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
    linarith [this, hE4, hb4]
  have h1 : ‖Work.Kernels.E4Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)‖
      * ‖Work.Kernels.E4Fun w + (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)‖
      ≤ (50000 * ‖nomeQ w‖ ^ 3) * 4 :=
    mul_le_mul h4 hb (by positivity) (by norm_num)
  have hq3 : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
  linarith [h1]

lemma E10P_strip_close (w : UpperHalfPlane) (h : Strip w) :
    ‖Work.Kernels.E10Fun w - (1 - 264 * nomeQ w - 135432 * (nomeQ w) ^ 2)‖
        ≤ 10000000 * ‖nomeQ w‖ ^ 3
      ∧ ‖Work.Kernels.E8Fun w - (1 + 480 * nomeQ w + 61920 * (nomeQ w) ^ 2)‖
        ≤ 10000000 * ‖nomeQ w‖ ^ 3 := by
  constructor
  · have h1 := E10_trunc w h
    have hpoly : ‖(1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
          * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)
          - (1 - 264 * nomeQ w - 135432 * (nomeQ w) ^ 2)‖
        ≤ 6000000 * ‖nomeQ w‖ ^ 3 := by
      have hp : (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
            * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)
            - (1 - 264 * nomeQ w - 135432 * (nomeQ w) ^ 2)
          = (nomeQ w) ^ 3 * ((-5080320 : ℂ) + (-35925120) * nomeQ w) := by ring
      rw [hp, norm_mul, norm_pow]
      have hW : ‖(-5080320 : ℂ) + (-35925120) * nomeQ w‖ ≤ 5100000 := by
        have hh := norm_quadratic_le (nomeQ w) (-5080320) (-35925120) 0
        simp only [Complex.norm_ofNat, norm_zero, zero_mul, add_zero, norm_neg] at hh
        have hq1 : ‖nomeQ w‖ ≤ 1 / 280000 := (strip_facts w h).1
        nlinarith [hh, hq1, norm_nonneg (nomeQ w)]
      calc ‖nomeQ w‖ ^ 3 * ‖(-5080320 : ℂ) + (-35925120) * nomeQ w‖
          ≤ ‖nomeQ w‖ ^ 3 * 5100000 := mul_le_mul_of_nonneg_left hW (by positivity)
        _ ≤ 6000000 * ‖nomeQ w‖ ^ 3 := by
            have hq3 : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
            nlinarith [hq3]
    have hkey : Work.Kernels.E10Fun w - (1 - 264 * nomeQ w - 135432 * (nomeQ w) ^ 2)
        = (Work.Kernels.E10Fun w
            - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
              * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
          + ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
              * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)
              - (1 - 264 * nomeQ w - 135432 * (nomeQ w) ^ 2)) := by ring
    rw [hkey]
    have hsum := norm_add_le (Work.Kernels.E10Fun w
          - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
            * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
      ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
            * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)
            - (1 - 264 * nomeQ w - 135432 * (nomeQ w) ^ 2))
    have hq3 : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
    linarith [hsum, h1, hpoly]
  · have h1 := E8_trunc w h
    have hpoly : ‖(1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2
          - (1 + 480 * nomeQ w + 61920 * (nomeQ w) ^ 2)‖
        ≤ 2000000 * ‖nomeQ w‖ ^ 3 := by
      have hp : (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2
            - (1 + 480 * nomeQ w + 61920 * (nomeQ w) ^ 2)
          = (nomeQ w) ^ 3 * ((1036800 : ℂ) + 4665600 * nomeQ w) := by ring
      rw [hp, norm_mul, norm_pow]
      have hW : ‖(1036800 : ℂ) + 4665600 * nomeQ w‖ ≤ 1100000 := by
        have hh := norm_quadratic_le (nomeQ w) 1036800 4665600 0
        simp only [Complex.norm_ofNat, norm_zero, zero_mul, add_zero] at hh
        have hq1 : ‖nomeQ w‖ ≤ 1 / 280000 := (strip_facts w h).1
        nlinarith [hh, hq1, norm_nonneg (nomeQ w)]
      calc ‖nomeQ w‖ ^ 3 * ‖(1036800 : ℂ) + 4665600 * nomeQ w‖
          ≤ ‖nomeQ w‖ ^ 3 * 1100000 := mul_le_mul_of_nonneg_left hW (by positivity)
        _ ≤ 2000000 * ‖nomeQ w‖ ^ 3 := by
            have hq3 : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
            nlinarith [hq3]
    have hkey : Work.Kernels.E8Fun w - (1 + 480 * nomeQ w + 61920 * (nomeQ w) ^ 2)
        = (Work.Kernels.E8Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2)
          + ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2
              - (1 + 480 * nomeQ w + 61920 * (nomeQ w) ^ 2)) := by ring
    rw [hkey]
    have hsum := norm_add_le (Work.Kernels.E8Fun w
        - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2)
      ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2
              - (1 + 480 * nomeQ w + 61920 * (nomeQ w) ^ 2))
    have hq3 : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
    linarith [hsum, h1, hpoly]

/-! ## The `𝓛`/`𝓛_S` bounds on the strip -/

/-- `‖𝓛(w)‖ ≤ π‖w‖ + 4` on the strip. -/
lemma Lfun_strip_bound (w : UpperHalfPlane) (h : Strip w) :
    ‖Work.Kernels.LogLambda.Lfun (w : ℂ)‖ ≤ Real.pi * ‖(w : ℂ)‖ + 4 := by
  have him : (1 : ℝ) ≤ ((w : ℂ)).im := by rw [UpperHalfPlane.coe_im]; linarith [h.2]
  have he_le := nomeE_norm_le_inv500 w h
  have henn : (0 : ℝ) ≤ ‖nomeE w‖ := norm_nonneg _
  have hE0 : Complex.exp (Real.pi * Complex.I * (w : ℂ)) = nomeE w := (nomeE_def w).symm
  have hL0 : ‖Work.Kernels.LogLambda.Lfun (w : ℂ)
      - ((Real.pi : ℂ) * Complex.I * (w : ℂ) + 4 * (Real.log 2 : ℂ) - 8 * nomeE w
        + 12 * (nomeE w) ^ 2)‖ ≤ 10000 * ‖nomeE w‖ ^ 3 := by
    have hh := LfunQExp (w : ℂ) him
    rwa [hE0] at hh
  have hb : ‖(Real.pi : ℂ) * Complex.I * (w : ℂ) + 4 * (Real.log 2 : ℂ) - 8 * nomeE w
      + 12 * (nomeE w) ^ 2‖ ≤ Real.pi * ‖(w : ℂ)‖ + 4 * Real.log 2 + 8 * ‖nomeE w‖
        + 12 * ‖nomeE w‖ ^ 2 := by
    have hπ : ‖(Real.pi : ℂ) * Complex.I * (w : ℂ)‖ = Real.pi * ‖(w : ℂ)‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    have h4l : ‖(4 : ℂ) * (Real.log 2 : ℂ)‖ = 4 * Real.log 2 := by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.log_pos (by norm_num))]
    have h8 : ‖(8 : ℂ) * nomeE w‖ = 8 * ‖nomeE w‖ := by rw [norm_mul, Complex.norm_ofNat]
    have h12 : ‖(12 : ℂ) * (nomeE w) ^ 2‖ = 12 * ‖nomeE w‖ ^ 2 := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]
    have h := norm_four_le ((Real.pi : ℂ) * Complex.I * (w : ℂ)) ((4 : ℂ) * (Real.log 2 : ℂ))
      ((8 : ℂ) * nomeE w) ((12 : ℂ) * (nomeE w) ^ 2)
    rw [hπ, h4l, h8, h12] at h
    exact h
  have hsub : ‖Work.Kernels.LogLambda.Lfun (w : ℂ)‖
      ≤ ‖Work.Kernels.LogLambda.Lfun (w : ℂ)
          - ((Real.pi : ℂ) * Complex.I * (w : ℂ) + 4 * (Real.log 2 : ℂ) - 8 * nomeE w
            + 12 * (nomeE w) ^ 2)‖
        + ‖(Real.pi : ℂ) * Complex.I * (w : ℂ) + 4 * (Real.log 2 : ℂ) - 8 * nomeE w
            + 12 * (nomeE w) ^ 2‖ := by
    have hh := norm_add_le (Work.Kernels.LogLambda.Lfun (w : ℂ)
        - ((Real.pi : ℂ) * Complex.I * (w : ℂ) + 4 * (Real.log 2 : ℂ) - 8 * nomeE w
          + 12 * (nomeE w) ^ 2))
      ((Real.pi : ℂ) * Complex.I * (w : ℂ) + 4 * (Real.log 2 : ℂ) - 8 * nomeE w
          + 12 * (nomeE w) ^ 2)
    rwa [sub_add_cancel] at hh
  have hsum : Real.pi * ‖(w : ℂ)‖ + 4 * Real.log 2 + 8 * ‖nomeE w‖ + 12 * ‖nomeE w‖ ^ 2
      + 10000 * ‖nomeE w‖ ^ 3 ≤ Real.pi * ‖(w : ℂ)‖ + 4 := by
    have hlog : Real.log 2 < 0.7 := Real.log_two_lt_d9.trans_le (by norm_num)
    have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h2 := pow_le_pow_left₀ henn he_le 2
    have h3 := pow_le_pow_left₀ henn he_le 3
    nlinarith [he_le, henn, hlog, hlogpos, h2, h3]
  linarith [hsub, hb, hL0, hsum]

/-- `ℓ.L_S = Λ_S` on the strip, hence bounded by `30‖nomeE w‖`. -/
lemma LS_strip_bound (ℓ : Work.Kernels.LogLambdaData) (w : UpperHalfPlane) (h : Strip w) :
    ‖ℓ.L_S w‖ ≤ 30 * ‖nomeE w‖ := by
  have him : 1 / 2 < w.im := by linarith [h.2]
  rw [Work.Residues.LogLambdaData_LS_eq_LamS ℓ w him, norm_nomeE w]
  have him1 : (1 : ℝ) ≤ ((w : ℂ)).im := by rw [UpperHalfPlane.coe_im]; linarith [h.2]
  have h1 := Work.Residues.norm_log_thetaC01_le_exp (w : ℂ) him1
  have h2 := Work.Residues.norm_log_thetaC00_le_exp (w : ℂ) him1
  have he1 : -Real.pi * ((w : ℂ)).im = -(Real.pi * w.im) := by
    rw [UpperHalfPlane.coe_im]; ring
  rw [he1] at h1 h2
  have hb : ‖Work.Kernels.LogLambda.LamS (w : ℂ)‖ ≤ (192 / 7) * Real.exp (-(Real.pi * w.im)) := by
    rw [Work.Kernels.LogLambda.LamS]
    calc ‖(4 : ℂ) * Complex.log (Work.Kernels.LogLambda.thetaC01 (w : ℂ))
          - 4 * Complex.log (Work.Kernels.LogLambda.thetaC00 (w : ℂ))‖
        ≤ ‖(4 : ℂ) * Complex.log (Work.Kernels.LogLambda.thetaC01 (w : ℂ))‖
          + ‖(4 : ℂ) * Complex.log (Work.Kernels.LogLambda.thetaC00 (w : ℂ))‖ :=
          norm_sub_le _ _
      _ = 4 * ‖Complex.log (Work.Kernels.LogLambda.thetaC01 (w : ℂ))‖
          + 4 * ‖Complex.log (Work.Kernels.LogLambda.thetaC00 (w : ℂ))‖ := by
          rw [norm_mul, norm_mul, Complex.norm_ofNat]
      _ ≤ 4 * ((24 / 7) * Real.exp (-(Real.pi * w.im)))
          + 4 * ((24 / 7) * Real.exp (-(Real.pi * w.im))) := by linarith
      _ = (192 / 7) * Real.exp (-(Real.pi * w.im)) := by ring
  have hpos : 0 < Real.exp (-(Real.pi * w.im)) := Real.exp_pos _
  nlinarith [hb, hpos]

/-! ## Coefficient lists for the polynomial estimates -/

def cBr : ℕ → ℂ
  | 0 => 576
  | 1 => -18144
  | 2 => 133632
  | 3 => -347328
  | 4 => 17664
  | 5 => -827136
  | 6 => -40922496
  | 7 => -626365440
  | 8 => -751887360
  | 9 => -9079050240
  | 10 => -5347814400
  | 11 => -31651430400
  | 12 => -8360755200
  | 13 => -21499084800
  | 14 => 2687385600
  | _ => 0

def cSg : ℕ → ℂ
  | 0 => 1
  | 1 => 24
  | 2 => 24
  | 3 => 96
  | 4 => 24
  | _ => 0

def cSq : ℕ → ℂ
  | 0 => -1
  | 1 => 48
  | 2 => 144
  | 3 => 1344
  | 4 => 912
  | 5 => 5760
  | 6 => 1920
  | 7 => 4608
  | 8 => -576
  | _ => 0

lemma Br_strip_close (w : UpperHalfPlane) (h : Strip w) :
    ‖(Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) w * Work.Kernels.E10Fun w
      - (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) w * Work.Kernels.E8Fun w
      + 72 * nomeE w‖ ≤ 10000 * ‖nomeE w‖ ^ 2 := by
  rw [Work.Kernels.KernelFacts.xi2Fun_slash_S w, Work.Kernels.KernelFacts.xi4S_apply w]
  obtain ⟨hU, hW, hV⟩ := ThetaQExp
  have hUw := hU w h.2
  have hWw := hW w h.2
  have hVw := hV w h.2
  have hUn := Unorm w h
  have hWn := Wnorm w h
  have hVn := Vnorm w h
  have hPu := Utrunc_norm w h
  have hPw := Wtrunc_norm w h
  have hPv := Vtrunc_norm w h
  have hE10 := E10_trunc w h
  have hE8 := E8_trunc w h
  have hE4n : ‖Work.Kernels.E4Fun w‖ ≤ 2 := (strip_trunc_bounds w h).2.2.2.2.1
  have hE6n : ‖Work.Kernels.E6Fun w‖ ≤ 2 := (strip_trunc_bounds w h).2.2.2.2.2
  have hE10n : ‖Work.Kernels.E10Fun w‖ ≤ 4 := by
    show ‖Work.Kernels.E4Fun w * Work.Kernels.E6Fun w‖ ≤ 4
    rw [norm_mul]
    have := mul_le_mul hE4n hE6n (norm_nonneg _) (by norm_num)
    linarith
  have hE8n : ‖Work.Kernels.E8Fun w‖ ≤ 4 := by
    show ‖(Work.Kernels.E4Fun w) ^ 2‖ ≤ 4
    rw [norm_pow]
    nlinarith [hE4n, norm_nonneg (Work.Kernels.E4Fun w)]
  have he_le := nomeE_norm_le_inv500 w h
  have henn : (0 : ℝ) ≤ ‖nomeE w‖ := norm_nonneg _
  have he5 := nomeE_pow5_le w h
  have hqnn : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 2 := by positivity
  have hQ3 := nomeQ_pow3_le w h
  set Sg : ℂ := 1 + 24 * nomeE w + 24 * (nomeE w) ^ 2 + 96 * (nomeE w) ^ 3
      + 24 * (nomeE w) ^ 4 with hSg
  set Sq : ℂ := (1 + 8 * nomeE w + 24 * (nomeE w) ^ 2 + 32 * (nomeE w) ^ 3
        + 24 * (nomeE w) ^ 4) ^ 2
      + (16 * nomeE w + 64 * (nomeE w) ^ 3) ^ 2
      - 2 * (1 - 8 * nomeE w + 24 * (nomeE w) ^ 2 - 32 * (nomeE w) ^ 3
        + 24 * (nomeE w) ^ 4) ^ 2 with hSq
  set Tg : ℂ := (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
      * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) with hTg
  set Tq : ℂ := (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2 with hTq
  have hSgn : ‖Sg‖ ≤ 2 := by
    have hs := norm_sum_pow_le (nomeE w) (1 / 500) he_le cSg 5
    have hpoly : ∑ k ∈ Finset.range 5, cSg k * (nomeE w) ^ k = Sg := by
      rw [hSg]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, cSg, pow_zero, pow_one, mul_one,
        zero_add, norm_one, Complex.norm_ofNat, norm_neg] <;> ring
    rw [hpoly] at hs
    have hnum : (∑ k ∈ Finset.range 5, ‖cSg k‖ * (1 / 500 : ℝ) ^ k) ≤ 2 := by
      norm_num [Finset.sum_range_succ, Finset.sum_range_zero, cSg, pow_zero, pow_one,
        Complex.norm_ofNat, norm_neg, mul_one, zero_add, add_zero]
    linarith [hs, hnum]
  have hSqn : ‖Sq‖ ≤ 2 := by
    have hs := norm_sum_pow_le (nomeE w) (1 / 500) he_le cSq 9
    have hpoly : ∑ k ∈ Finset.range 9, cSq k * (nomeE w) ^ k = Sq := by
      rw [hSq]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, cSq, pow_zero, pow_one, mul_one,
        zero_add, norm_one, Complex.norm_ofNat, norm_neg] <;> ring
    rw [hpoly] at hs
    have hnum : (∑ k ∈ Finset.range 9, ‖cSq k‖ * (1 / 500 : ℝ) ^ k) ≤ 2 := by
      norm_num [Finset.sum_range_succ, Finset.sum_range_zero, cSq, pow_zero, pow_one,
        Complex.norm_ofNat, norm_neg, mul_one, zero_add, add_zero]
    linarith [hs, hnum]
  have hkey : -(Work.Kernels.UFun w + Work.Kernels.VFun w) * Work.Kernels.E10Fun w
        - (Work.Kernels.UFun w ^ 2 + Work.Kernels.VFun w ^ 2 - 2 * Work.Kernels.WFun w ^ 2)
          * Work.Kernels.E8Fun w + 72 * nomeE w
      = (-(Sg) * Tg - Sq * Tq + 72 * nomeE w)
        + (-(Sg * (Work.Kernels.E10Fun w - Tg)))
        - (Sq * (Work.Kernels.E8Fun w - Tq))
        + (-(((Work.Kernels.UFun w + Work.Kernels.VFun w) - Sg) * Work.Kernels.E10Fun w
            + ((Work.Kernels.UFun w ^ 2 + Work.Kernels.VFun w ^ 2
                - 2 * Work.Kernels.WFun w ^ 2) - Sq) * Work.Kernels.E8Fun w)) := by ring_nf
  rw [hkey]
  have hA : ‖-(Sg) * Tg - Sq * Tq + 72 * nomeE w‖ ≤ 700 * ‖nomeE w‖ ^ 2 := by
    have hpoly : -(Sg) * Tg - Sq * Tq + 72 * nomeE w
        = (nomeE w) ^ 2 * (∑ k ∈ Finset.range 15, cBr k * (nomeE w) ^ k) := by
      rw [hSg, hSq, hTg, hTq, nomeE_sq w]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, cBr, pow_zero, pow_one, mul_one,
        zero_add] <;> ring
    rw [hpoly, norm_mul, norm_pow]
    have hs := norm_sum_pow_le (nomeE w) (1 / 500) he_le cBr 15
    have hnum : (∑ k ∈ Finset.range 15, ‖cBr k‖ * (1 / 500 : ℝ) ^ k) ≤ 700 := by
      norm_num [Finset.sum_range_succ, Finset.sum_range_zero, cBr, pow_zero, pow_one,
        Complex.norm_ofNat, norm_neg, mul_one, zero_add, add_zero]
    have h1 : ‖nomeE w‖ ^ 2 * ‖∑ k ∈ Finset.range 15, cBr k * (nomeE w) ^ k‖
        ≤ ‖nomeE w‖ ^ 2 * 700 :=
      mul_le_mul_of_nonneg_left (le_trans hs hnum) (by positivity)
    linarith [h1]
  have hB : ‖-(Sg * (Work.Kernels.E10Fun w - Tg))‖ ≤ 2 * (3000000 * ‖nomeQ w‖ ^ 3) := by
    rw [norm_neg, norm_mul]
    refine mul_le_mul hSgn ?_ (norm_nonneg _) (by positivity)
    simpa [hTg] using hE10
  have hC : ‖Sq * (Work.Kernels.E8Fun w - Tq)‖ ≤ 2 * (1000000 * ‖nomeQ w‖ ^ 3) := by
    rw [norm_mul]
    refine mul_le_mul hSqn ?_ (norm_nonneg _) (by positivity)
    simpa [hTq] using hE8
  have hD : ‖-(((Work.Kernels.UFun w + Work.Kernels.VFun w) - Sg) * Work.Kernels.E10Fun w
        + ((Work.Kernels.UFun w ^ 2 + Work.Kernels.VFun w ^ 2
            - 2 * Work.Kernels.WFun w ^ 2) - Sq) * Work.Kernels.E8Fun w)‖
      ≤ (20000 * ‖nomeE w‖ ^ 5) * 4 + (150000 * ‖nomeE w‖ ^ 5) * 4 := by
    rw [norm_neg]
    have hD1 : ‖((Work.Kernels.UFun w + Work.Kernels.VFun w) - Sg) * Work.Kernels.E10Fun w‖
        ≤ (20000 * ‖nomeE w‖ ^ 5) * 4 := by
      rw [norm_mul]
      have hg : ‖(Work.Kernels.UFun w + Work.Kernels.VFun w) - Sg‖ ≤ 20000 * ‖nomeE w‖ ^ 5 := by
        have hg1 : (Work.Kernels.UFun w + Work.Kernels.VFun w) - Sg
            = (Work.Kernels.UFun w - (1 + 8 * nomeE w + 24 * (nomeE w) ^ 2
                + 32 * (nomeE w) ^ 3 + 24 * (nomeE w) ^ 4))
              + (Work.Kernels.VFun w - (16 * nomeE w + 64 * (nomeE w) ^ 3)) := by
          rw [hSg]; ring
        rw [hg1]
        have hsum := norm_add_le (Work.Kernels.UFun w - (1 + 8 * nomeE w + 24 * (nomeE w) ^ 2
            + 32 * (nomeE w) ^ 3 + 24 * (nomeE w) ^ 4))
          (Work.Kernels.VFun w - (16 * nomeE w + 64 * (nomeE w) ^ 3))
        linarith [hsum, hUw, hVw]
      exact mul_le_mul hg hE10n (norm_nonneg _) (by positivity)
    have hD2 : ‖((Work.Kernels.UFun w ^ 2 + Work.Kernels.VFun w ^ 2
            - 2 * Work.Kernels.WFun w ^ 2) - Sq) * Work.Kernels.E8Fun w‖
        ≤ (150000 * ‖nomeE w‖ ^ 5) * 4 := by
      rw [norm_mul]
      have hsqU : ‖(Work.Kernels.UFun w) ^ 2
          - (1 + 8 * nomeE w + 24 * (nomeE w) ^ 2 + 32 * (nomeE w) ^ 3
            + 24 * (nomeE w) ^ 4) ^ 2‖ ≤ 40000 * ‖nomeE w‖ ^ 5 := by
        have hh := norm_sq_sub_sq_le (Work.Kernels.UFun w)
          (1 + 8 * nomeE w + 24 * (nomeE w) ^ 2 + 32 * (nomeE w) ^ 3 + 24 * (nomeE w) ^ 4)
        have hb2 : ‖Work.Kernels.UFun w‖
            + ‖(1 : ℂ) + 8 * nomeE w + 24 * (nomeE w) ^ 2 + 32 * (nomeE w) ^ 3
              + 24 * (nomeE w) ^ 4‖ ≤ 4 := by linarith [hUn, hPu]
        have h1 : ‖Work.Kernels.UFun w - (1 + 8 * nomeE w + 24 * (nomeE w) ^ 2
            + 32 * (nomeE w) ^ 3 + 24 * (nomeE w) ^ 4)‖
            * (‖Work.Kernels.UFun w‖ + ‖(1 : ℂ) + 8 * nomeE w + 24 * (nomeE w) ^ 2
              + 32 * (nomeE w) ^ 3 + 24 * (nomeE w) ^ 4‖) ≤ (10000 * ‖nomeE w‖ ^ 5) * 4 :=
          mul_le_mul hUw hb2 (by positivity) (by norm_num)
        nlinarith [hh, h1, pow_nonneg henn 5]
      have hsqW : ‖(Work.Kernels.WFun w) ^ 2
          - (1 - 8 * nomeE w + 24 * (nomeE w) ^ 2 - 32 * (nomeE w) ^ 3
            + 24 * (nomeE w) ^ 4) ^ 2‖ ≤ 40000 * ‖nomeE w‖ ^ 5 := by
        have hh := norm_sq_sub_sq_le (Work.Kernels.WFun w)
          (1 - 8 * nomeE w + 24 * (nomeE w) ^ 2 - 32 * (nomeE w) ^ 3 + 24 * (nomeE w) ^ 4)
        have hb2 : ‖Work.Kernels.WFun w‖
            + ‖(1 : ℂ) - 8 * nomeE w + 24 * (nomeE w) ^ 2 - 32 * (nomeE w) ^ 3
              + 24 * (nomeE w) ^ 4‖ ≤ 4 := by linarith [hWn, hPw]
        have h1 : ‖Work.Kernels.WFun w - (1 - 8 * nomeE w + 24 * (nomeE w) ^ 2
            - 32 * (nomeE w) ^ 3 + 24 * (nomeE w) ^ 4)‖
            * (‖Work.Kernels.WFun w‖ + ‖(1 : ℂ) - 8 * nomeE w + 24 * (nomeE w) ^ 2
              - 32 * (nomeE w) ^ 3 + 24 * (nomeE w) ^ 4‖) ≤ (10000 * ‖nomeE w‖ ^ 5) * 4 :=
          mul_le_mul hWw hb2 (by positivity) (by norm_num)
        nlinarith [hh, h1, pow_nonneg henn 5]
      have hsqV : ‖(Work.Kernels.VFun w) ^ 2 - (16 * nomeE w + 64 * (nomeE w) ^ 3) ^ 2‖
          ≤ 20000 * ‖nomeE w‖ ^ 5 := by
        have hh := norm_sq_sub_sq_le (Work.Kernels.VFun w) (16 * nomeE w + 64 * (nomeE w) ^ 3)
        have hb2 : ‖Work.Kernels.VFun w‖ + ‖(16 : ℂ) * nomeE w + 64 * (nomeE w) ^ 3‖ ≤ 1 := by
          linarith [hVn, hPv]
        have h1 : ‖Work.Kernels.VFun w - (16 * nomeE w + 64 * (nomeE w) ^ 3)‖
            * (‖Work.Kernels.VFun w‖ + ‖(16 : ℂ) * nomeE w + 64 * (nomeE w) ^ 3‖)
            ≤ (10000 * ‖nomeE w‖ ^ 5) * 1 :=
          mul_le_mul hVw hb2 (by positivity) (by norm_num)
        nlinarith [hh, h1, pow_nonneg henn 5]
      have hq3 : ((Work.Kernels.UFun w ^ 2 + Work.Kernels.VFun w ^ 2
            - 2 * Work.Kernels.WFun w ^ 2) - Sq)
          = ((Work.Kernels.UFun w) ^ 2
                - (1 + 8 * nomeE w + 24 * (nomeE w) ^ 2 + 32 * (nomeE w) ^ 3
                  + 24 * (nomeE w) ^ 4) ^ 2)
              + ((Work.Kernels.VFun w) ^ 2 - (16 * nomeE w + 64 * (nomeE w) ^ 3) ^ 2)
              - 2 * ((Work.Kernels.WFun w) ^ 2
                - (1 - 8 * nomeE w + 24 * (nomeE w) ^ 2 - 32 * (nomeE w) ^ 3
                  + 24 * (nomeE w) ^ 4) ^ 2) := by
        rw [hSq]; ring
      rw [hq3]
      have hfin : ‖((Work.Kernels.UFun w) ^ 2
                - (1 + 8 * nomeE w + 24 * (nomeE w) ^ 2 + 32 * (nomeE w) ^ 3
                  + 24 * (nomeE w) ^ 4) ^ 2)
              + ((Work.Kernels.VFun w) ^ 2 - (16 * nomeE w + 64 * (nomeE w) ^ 3) ^ 2)
              - 2 * ((Work.Kernels.WFun w) ^ 2
                - (1 - 8 * nomeE w + 24 * (nomeE w) ^ 2 - 32 * (nomeE w) ^ 3
                  + 24 * (nomeE w) ^ 4) ^ 2)‖ ≤ 150000 * ‖nomeE w‖ ^ 5 := by
        have h2' : ‖(2 : ℂ) * ((Work.Kernels.WFun w) ^ 2
            - (1 - 8 * nomeE w + 24 * (nomeE w) ^ 2 - 32 * (nomeE w) ^ 3
              + 24 * (nomeE w) ^ 4) ^ 2)‖ ≤ 2 * (40000 * ‖nomeE w‖ ^ 5) := by
          rw [norm_mul, Complex.norm_ofNat]
          linarith [hsqW]
        have hsub := norm_sub_le (((Work.Kernels.UFun w) ^ 2
                - (1 + 8 * nomeE w + 24 * (nomeE w) ^ 2 + 32 * (nomeE w) ^ 3
                  + 24 * (nomeE w) ^ 4) ^ 2)
              + ((Work.Kernels.VFun w) ^ 2 - (16 * nomeE w + 64 * (nomeE w) ^ 3) ^ 2))
          (2 * ((Work.Kernels.WFun w) ^ 2
                - (1 - 8 * nomeE w + 24 * (nomeE w) ^ 2 - 32 * (nomeE w) ^ 3
                  + 24 * (nomeE w) ^ 4) ^ 2))
        have hadd := norm_add_le ((Work.Kernels.UFun w) ^ 2
                - (1 + 8 * nomeE w + 24 * (nomeE w) ^ 2 + 32 * (nomeE w) ^ 3
                  + 24 * (nomeE w) ^ 4) ^ 2)
          ((Work.Kernels.VFun w) ^ 2 - (16 * nomeE w + 64 * (nomeE w) ^ 3) ^ 2)
        linarith [hadd, hsub, hsqU, hsqV, h2', pow_nonneg henn 5]
      exact mul_le_mul hfin hE8n (norm_nonneg _) (by positivity)
    have hsplit := norm_add_le (((Work.Kernels.UFun w + Work.Kernels.VFun w) - Sg)
        * Work.Kernels.E10Fun w)
      (((Work.Kernels.UFun w ^ 2 + Work.Kernels.VFun w ^ 2 - 2 * Work.Kernels.WFun w ^ 2) - Sq)
        * Work.Kernels.E8Fun w)
    linarith [hsplit, hD1, hD2]
  have hsum := norm_four_le (-(Sg) * Tg - Sq * Tq + 72 * nomeE w)
    (-(Sg * (Work.Kernels.E10Fun w - Tg)))
    (Sq * (Work.Kernels.E8Fun w - Tq))
    (-(((Work.Kernels.UFun w + Work.Kernels.VFun w) - Sg) * Work.Kernels.E10Fun w
      + ((Work.Kernels.UFun w ^ 2 + Work.Kernels.VFun w ^ 2 - 2 * Work.Kernels.WFun w ^ 2) - Sq)
        * Work.Kernels.E8Fun w))
  have hfinal : 700 * ‖nomeE w‖ ^ 2 + 2 * (3000000 * ‖nomeQ w‖ ^ 3)
      + 2 * (1000000 * ‖nomeQ w‖ ^ 3) + ((20000 * ‖nomeE w‖ ^ 5) * 4
        + (150000 * ‖nomeE w‖ ^ 5) * 4) ≤ 10000 * ‖nomeE w‖ ^ 2 := by
    have hq := nomeE_pow5_mul_le w h 680000 (by norm_num)
    have he2 : ‖nomeE w‖ ^ 2 ≤ (1 / 250000 : ℝ) := by
      have h3 := nomeE_pow3_le w h
      have h2 := pow_le_pow_left₀ henn he_le 2
      nlinarith [h2]
    have he4 : ‖nomeE w‖ ^ 4 ≤ (1 / 250000 : ℝ) * ‖nomeE w‖ ^ 2 := by
      have h4 : ‖nomeE w‖ ^ 4 = ‖nomeE w‖ ^ 2 * ‖nomeE w‖ ^ 2 := by ring
      rw [h4]
      exact mul_le_mul_of_nonneg_right he2 (by positivity)
    have hqe : ‖nomeQ w‖ ^ 2 = ‖nomeE w‖ ^ 4 := by
      rw [norm_nomeQ_sq w]; ring
    nlinarith [hq, hqnn, hQ3, he5, he2, he4, hqe, pow_nonneg henn 5, pow_nonneg hqnn 1]
  linarith [hsum, hA, hB, hC, hD, hfinal]

def cX : ℕ → ℂ
  | 0 => -267264
  | 1 => -39168
  | 2 => 80002944
  | 3 => 1266554880
  | 4 => 6785648640
  | _ => 0

def cPm : ℕ → ℂ
  | 0 => 2568
  | 1 => 211078
  | 2 => 4191807
  | 3 => 18819144
  | 4 => 21249864
  | 5 => -877132800
  | 6 => -1452867840
  | _ => 0

def cA : ℕ → ℂ
  | 0 => -1
  | 1 => 6954
  | 2 => 388372
  | 3 => 4664358
  | 4 => 1632960
  | 5 => 27760320
  | _ => 0

def cDm : ℕ → ℂ
  | 0 => 1
  | 1 => -24
  | 2 => 98
  | 3 => 64017
  | 4 => 1944000
  | 5 => 5832000
  | _ => 0

lemma Xnum_strip_close (w : UpperHalfPlane) (h : Strip w) :
    ‖Xnum w + 1152 * nomeQ w‖ ≤ 1000000 * ‖nomeQ w‖ ^ 2 := by
  have hxi := xi_strip_close w h
  have hE10 := E10_trunc w h
  have hE8 := E8_trunc w h
  have hE4n : ‖Work.Kernels.E4Fun w‖ ≤ 2 := (strip_trunc_bounds w h).2.2.2.2.1
  have hE6n : ‖Work.Kernels.E6Fun w‖ ≤ 2 := (strip_trunc_bounds w h).2.2.2.2.2
  have hE10n : ‖Work.Kernels.E10Fun w‖ ≤ 4 := by
    show ‖Work.Kernels.E4Fun w * Work.Kernels.E6Fun w‖ ≤ 4
    rw [norm_mul]
    have hh := mul_le_mul hE4n hE6n (norm_nonneg _) (by norm_num)
    linarith
  have hE8n : ‖Work.Kernels.E8Fun w‖ ≤ 4 := by
    show ‖(Work.Kernels.E4Fun w) ^ 2‖ ≤ 4
    rw [norm_pow]
    nlinarith [hE4n, norm_nonneg (Work.Kernels.E4Fun w)]
  have hQ1 : ‖nomeQ w‖ ≤ 1 / 280000 := (strip_facts w h).1
  have hQnn : (0 : ℝ) ≤ ‖nomeQ w‖ := norm_nonneg _
  have hQ2 : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 2 := by positivity
  have hxi2n : ‖(2 : ℂ) + 48 * nomeQ w + 48 * (nomeQ w) ^ 2‖ ≤ 3 := by
    have hh := norm_quadratic_le (nomeQ w) 2 48 48
    simp only [Complex.norm_ofNat] at hh
    nlinarith [hh, hQ1, hQnn]
  have hxi4n : ‖(2 : ℂ) - 288 * nomeQ w - 1824 * (nomeQ w) ^ 2‖ ≤ 3 := by
    have hh := norm_quadratic_le (nomeQ w) 2 (-288) (-1824)
    simp only [Complex.norm_ofNat, norm_neg] at hh
    have heq : (2 : ℂ) + (-288) * nomeQ w + (-1824) * (nomeQ w) ^ 2
        = 2 - 288 * nomeQ w - 1824 * (nomeQ w) ^ 2 := by ring
    rw [heq] at hh
    nlinarith [hh, hQ1, hQnn]
  have hkey : Xnum w + 1152 * nomeQ w
      = ((2 + 48 * nomeQ w + 48 * (nomeQ w) ^ 2)
            * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
              * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
          - (2 - 288 * nomeQ w - 1824 * (nomeQ w) ^ 2)
            * (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2 + 1152 * nomeQ w)
        + (Work.Kernels.xi2Fun w - (2 + 48 * nomeQ w + 48 * (nomeQ w) ^ 2))
            * Work.Kernels.E10Fun w
        + (2 + 48 * nomeQ w + 48 * (nomeQ w) ^ 2)
            * (Work.Kernels.E10Fun w
              - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
                * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
        - (Work.Kernels.xi4Fun w - (2 - 288 * nomeQ w - 1824 * (nomeQ w) ^ 2))
            * Work.Kernels.E8Fun w
        + (-((2 - 288 * nomeQ w - 1824 * (nomeQ w) ^ 2)
            * (Work.Kernels.E8Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2))) := by
    simp only [Xnum, Work.Kernels.E10Fun, Work.Kernels.E8Fun]
    ring
  rw [hkey]
  have hm : ‖(2 + 48 * nomeQ w + 48 * (nomeQ w) ^ 2)
          * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
            * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
        - (2 - 288 * nomeQ w - 1824 * (nomeQ w) ^ 2)
          * (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2 + 1152 * nomeQ w‖
      ≤ 300000 * ‖nomeQ w‖ ^ 2 := by
    have hpoly : (2 + 48 * nomeQ w + 48 * (nomeQ w) ^ 2)
          * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
            * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
        - (2 - 288 * nomeQ w - 1824 * (nomeQ w) ^ 2)
          * (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2 + 1152 * nomeQ w
        = (nomeQ w) ^ 2 * (∑ k ∈ Finset.range 5, cX k * (nomeQ w) ^ k) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, cX, pow_zero, pow_one, mul_one,
        zero_add] <;> ring
    rw [hpoly, norm_mul, norm_pow]
    have hs := norm_sum_pow_le (nomeQ w) (1 / 280000) hQ1 cX 5
    have hnum : (∑ k ∈ Finset.range 5, ‖cX k‖ * (1 / 280000 : ℝ) ^ k) ≤ 300000 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, cX, pow_zero, pow_one,
        Complex.norm_ofNat, norm_neg, mul_one, zero_add, add_zero] <;> norm_num
    have h1 : ‖nomeQ w‖ ^ 2 * ‖∑ k ∈ Finset.range 5, cX k * (nomeQ w) ^ k‖
        ≤ ‖nomeQ w‖ ^ 2 * 300000 :=
      mul_le_mul_of_nonneg_left (le_trans hs hnum) (by positivity)
    linarith [h1]
  have h2a : ‖(Work.Kernels.xi2Fun w - (2 + 48 * nomeQ w + 48 * (nomeQ w) ^ 2))
      * Work.Kernels.E10Fun w‖ ≤ (1000 * ‖nomeQ w‖ ^ 2) * 4 := by
    rw [norm_mul]
    exact mul_le_mul hxi.1 hE10n (norm_nonneg _) (by positivity)
  have h2b : ‖(2 + 48 * nomeQ w + 48 * (nomeQ w) ^ 2)
      * (Work.Kernels.E10Fun w
        - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
          * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))‖
      ≤ 3 * (3000000 * ‖nomeQ w‖ ^ 3) := by
    rw [norm_mul]
    exact mul_le_mul hxi2n hE10 (norm_nonneg _) (by positivity)
  have h2c : ‖(Work.Kernels.xi4Fun w - (2 - 288 * nomeQ w - 1824 * (nomeQ w) ^ 2))
      * Work.Kernels.E8Fun w‖ ≤ (10000 * ‖nomeQ w‖ ^ 2) * 4 := by
    rw [norm_mul]
    exact mul_le_mul hxi.2 hE8n (norm_nonneg _) (by positivity)
  have h2d : ‖(2 - 288 * nomeQ w - 1824 * (nomeQ w) ^ 2)
      * (Work.Kernels.E8Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2)‖
      ≤ 3 * (1000000 * ‖nomeQ w‖ ^ 3) := by
    rw [norm_mul]
    exact mul_le_mul hxi4n hE8 (norm_nonneg _) (by positivity)
  have hcorr : ‖((2 + 48 * nomeQ w + 48 * (nomeQ w) ^ 2)
          * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
            * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
        - (2 - 288 * nomeQ w - 1824 * (nomeQ w) ^ 2)
          * (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2 + 1152 * nomeQ w)
      + (Work.Kernels.xi2Fun w - (2 + 48 * nomeQ w + 48 * (nomeQ w) ^ 2))
          * Work.Kernels.E10Fun w‖
      ≤ 300000 * ‖nomeQ w‖ ^ 2 + (1000 * ‖nomeQ w‖ ^ 2) * 4 := by
    have hh := norm_add_le ((2 + 48 * nomeQ w + 48 * (nomeQ w) ^ 2)
          * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
            * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
        - (2 - 288 * nomeQ w - 1824 * (nomeQ w) ^ 2)
          * (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2 + 1152 * nomeQ w)
      ((Work.Kernels.xi2Fun w - (2 + 48 * nomeQ w + 48 * (nomeQ w) ^ 2))
          * Work.Kernels.E10Fun w)
    linarith [hh, hm, h2a]
  have hsum := norm_four_le ((2 + 48 * nomeQ w + 48 * (nomeQ w) ^ 2)
          * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
            * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
        - (2 - 288 * nomeQ w - 1824 * (nomeQ w) ^ 2)
          * (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2 + 1152 * nomeQ w
      + (Work.Kernels.xi2Fun w - (2 + 48 * nomeQ w + 48 * (nomeQ w) ^ 2))
          * Work.Kernels.E10Fun w)
    ((2 + 48 * nomeQ w + 48 * (nomeQ w) ^ 2)
          * (Work.Kernels.E10Fun w
            - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
              * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)))
    ((Work.Kernels.xi4Fun w - (2 - 288 * nomeQ w - 1824 * (nomeQ w) ^ 2))
          * Work.Kernels.E8Fun w)
    (-((2 - 288 * nomeQ w - 1824 * (nomeQ w) ^ 2)
          * (Work.Kernels.E8Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2)))
  have hlast : ‖-((2 - 288 * nomeQ w - 1824 * (nomeQ w) ^ 2)
          * (Work.Kernels.E8Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2))‖
      ≤ 3 * (1000000 * ‖nomeQ w‖ ^ 3) := by
    rw [norm_neg]
    exact h2d
  have hfinal : 300000 * ‖nomeQ w‖ ^ 2 + (1000 * ‖nomeQ w‖ ^ 2) * 4
      + 3 * (3000000 * ‖nomeQ w‖ ^ 3) + (10000 * ‖nomeQ w‖ ^ 2) * 4
      + 3 * (1000000 * ‖nomeQ w‖ ^ 3) ≤ 1000000 * ‖nomeQ w‖ ^ 2 := by
    have hq3 : ‖nomeQ w‖ ^ 3 ≤ (1 / 280000 : ℝ) * ‖nomeQ w‖ ^ 2 := nomeQ_pow3_le w h
    nlinarith [hq3, hQ2, hQnn]
  linarith [hsum, hcorr, h2b, h2c, hlast, hfinal]

lemma W3_strip_bound (ℓ : Work.Kernels.LogLambdaData) (w : UpperHalfPlane) (h : Strip w) :
    ‖W3 ℓ w‖ ≤ 4 * (1 + ‖(w : ℂ)‖) * ‖nomeQ w‖ := by
  have hLb := Lfun_strip_bound w h
  have hLSb := LS_strip_bound ℓ w h
  have hXb := Xnum_strip_close w h
  have hBrb := Br_strip_close w h
  have hLw : ℓ.L w = Work.Kernels.LogLambda.Lfun (w : ℂ) := LogLambdaData_L_eq_Lfun ℓ w
  have hQ1 : ‖nomeQ w‖ ≤ 1 / 280000 := (strip_facts w h).1
  have hQnn : (0 : ℝ) ≤ ‖nomeQ w‖ := norm_nonneg _
  have hQ2 : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 2 := by positivity
  have henn : (0 : ℝ) ≤ ‖nomeE w‖ := norm_nonneg _
  have hXn : ‖Xnum w‖ ≤ 1156 * ‖nomeQ w‖ := by
    have h1 : ‖Xnum w‖ ≤ ‖Xnum w + 1152 * nomeQ w‖ + 1152 * ‖nomeQ w‖ := by
      have hh := norm_add_le (Xnum w + 1152 * nomeQ w) (-(1152 * nomeQ w))
      have heq : (Xnum w + 1152 * nomeQ w) + (-(1152 * nomeQ w)) = Xnum w := by ring
      rw [heq, norm_neg, norm_mul, Complex.norm_ofNat] at hh
      exact hh
    have hq : 1000000 * ‖nomeQ w‖ ^ 2 ≤ 4 * ‖nomeQ w‖ := by
      have h2 : ‖nomeQ w‖ ^ 2 ≤ (1 / 280000 : ℝ) * ‖nomeQ w‖ := by nlinarith [hQ1, hQnn]
      nlinarith [h2]
    linarith [h1, hXb, hq]
  have hBrn : ‖(Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) w * Work.Kernels.E10Fun w
      - (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) w * Work.Kernels.E8Fun w‖
      ≤ 100 * ‖nomeE w‖ := by
    have h1 : ‖(Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) w * Work.Kernels.E10Fun w
        - (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) w * Work.Kernels.E8Fun w‖
        ≤ ‖(Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) w * Work.Kernels.E10Fun w
            - (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) w * Work.Kernels.E8Fun w
            + 72 * nomeE w‖ + 72 * ‖nomeE w‖ := by
      have hh := norm_add_le ((Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) w
            * Work.Kernels.E10Fun w
          - (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) w * Work.Kernels.E8Fun w
            + 72 * nomeE w) (-(72 * nomeE w))
      have heq : ((Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) w * Work.Kernels.E10Fun w
          - (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) w * Work.Kernels.E8Fun w
            + 72 * nomeE w) + (-(72 * nomeE w))
          = (Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) w * Work.Kernels.E10Fun w
            - (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) w * Work.Kernels.E8Fun w := by ring
      rw [heq, norm_neg, norm_mul, Complex.norm_ofNat] at hh
      exact hh
    have he_le := nomeE_norm_le_inv500 w h
    nlinarith [h1, hBrb, henn, he_le, pow_nonneg henn 2]
  have hkey : W3 ℓ w
      = ((ℓ.L w) * Xnum w
          + (ℓ.L_S w) * ((Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) w
              * Work.Kernels.E10Fun w
            - (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) w * Work.Kernels.E8Fun w))
        / (1152 * (Real.pi : ℂ)) := by
    simp only [W3, Work.Kernels.psi2, Work.Kernels.psi4, Xnum]
    ring
  have hπ : ‖(1152 : ℂ) * (Real.pi : ℂ)‖ = 1152 * Real.pi := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have h1 : ‖(ℓ.L w) * Xnum w‖ ≤ (Real.pi * ‖(w : ℂ)‖ + 4)
      * (1156 * ‖nomeQ w‖) := by
    rw [norm_mul, hLw]
    exact mul_le_mul hLb hXn (norm_nonneg _) (by positivity)
  have h2 : ‖(ℓ.L_S w) * ((Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) w
        * Work.Kernels.E10Fun w
      - (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) w * Work.Kernels.E8Fun w)‖
      ≤ (30 * ‖nomeE w‖) * (100 * ‖nomeE w‖) := by
    rw [norm_mul]
    exact mul_le_mul hLSb hBrn (norm_nonneg _) (by positivity)
  have hbd : ‖(ℓ.L w) * Xnum w
      + (ℓ.L_S w) * ((Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) w
          * Work.Kernels.E10Fun w
        - (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) w * Work.Kernels.E8Fun w)‖
      ≤ (1152 * Real.pi) * (4 * (1 + ‖(w : ℂ)‖) * ‖nomeQ w‖) := by
    have hsum := norm_add_le ((ℓ.L w) * Xnum w)
      ((ℓ.L_S w) * ((Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) w
          * Work.Kernels.E10Fun w
        - (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) w * Work.Kernels.E8Fun w))
    have he2 : (30 * ‖nomeE w‖) * (100 * ‖nomeE w‖) = 3000 * ‖nomeQ w‖ := by
      have h2' : ‖nomeE w‖ * ‖nomeE w‖ = ‖nomeQ w‖ := by
        rw [← sq, ← norm_nomeQ_sq w]
      linarith [h2']
    have hf : (Real.pi * ‖(w : ℂ)‖ + 4) * (1156 * ‖nomeQ w‖)
        + (30 * ‖nomeE w‖) * (100 * ‖nomeE w‖)
        ≤ (1152 * Real.pi) * (4 * (1 + ‖(w : ℂ)‖) * ‖nomeQ w‖) := by
      rw [he2]
      have hrw : (Real.pi * ‖(w : ℂ)‖ + 4) * (1156 * ‖nomeQ w‖) + 3000 * ‖nomeQ w‖
          = ((Real.pi * ‖(w : ℂ)‖ + 4) * 1156 + 3000) * ‖nomeQ w‖ := by ring
      have hrw2 : (1152 * Real.pi) * (4 * (1 + ‖(w : ℂ)‖) * ‖nomeQ w‖)
          = (1152 * Real.pi * 4 * (1 + ‖(w : ℂ)‖)) * ‖nomeQ w‖ := by ring
      rw [hrw, hrw2]
      refine mul_le_mul_of_nonneg_right ?_ hQnn
      nlinarith [Real.pi_gt_three, norm_nonneg (w : ℂ)]
    linarith [hsum, h1, h2, hf]
  calc ‖W3 ℓ w‖ = ‖(ℓ.L w) * Xnum w
          + (ℓ.L_S w) * ((Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) w
              * Work.Kernels.E10Fun w
            - (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) w * Work.Kernels.E8Fun w)‖
        / (1152 * Real.pi) := by rw [hkey, norm_div, hπ]
    _ ≤ 4 * (1 + ‖(w : ℂ)‖) * ‖nomeQ w‖ := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1152 * Real.pi)]
        linarith [hbd]

lemma E4sqE6_trunc (w : UpperHalfPlane) (h : Strip w) :
    ‖(Work.Kernels.E4Fun w) ^ 2 * Work.Kernels.E6Fun w
      - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2
        * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)‖ ≤ 5000000 * ‖nomeQ w‖ ^ 3 := by
  obtain ⟨_, he4, he6⟩ := EisensteinQExp
  obtain ⟨_, hb4, _, _, hE4, hE6⟩ := strip_trunc_bounds w h
  have h4 := he4 w h.2
  have h6 := he6 w h.2
  have hq3 : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
  have hkey : (Work.Kernels.E4Fun w) ^ 2 * Work.Kernels.E6Fun w
      - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2
        * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)
      = ((Work.Kernels.E4Fun w) ^ 2
            - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2) * Work.Kernels.E6Fun w
        + (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2
          * (Work.Kernels.E6Fun w - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)) := by ring
  rw [hkey]
  have hsq : ‖(Work.Kernels.E4Fun w) ^ 2
      - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2‖ ≤ 200000 * ‖nomeQ w‖ ^ 3 := by
    have hh := norm_sq_sub_sq_le (Work.Kernels.E4Fun w)
      (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
    have hb : ‖Work.Kernels.E4Fun w‖
        + ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖ ≤ 4 := by linarith [hE4, hb4]
    have h1 := mul_le_mul h4 hb (by positivity) (by norm_num)
    nlinarith [hh, h1, hq3]
  have h1 : ‖((Work.Kernels.E4Fun w) ^ 2
        - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2) * Work.Kernels.E6Fun w‖
      ≤ (200000 * ‖nomeQ w‖ ^ 3) * 2 := by
    rw [norm_mul]
    exact mul_le_mul hsq hE6 (norm_nonneg _) (by positivity)
  have h2 : ‖(1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2
      * (Work.Kernels.E6Fun w - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))‖
      ≤ 4 * (1000000 * ‖nomeQ w‖ ^ 3) := by
    rw [norm_mul, norm_pow]
    have hb : ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖ ^ 2 ≤ 4 := by
      nlinarith [hb4, norm_nonneg ((1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)]
    exact mul_le_mul hb h6 (by positivity) (by positivity)
  have hsum := norm_add_le (((Work.Kernels.E4Fun w) ^ 2
        - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2) * Work.Kernels.E6Fun w)
    ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2
      * (Work.Kernels.E6Fun w - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)))
  linarith [hsum, h1, h2, hq3]

lemma E2sqE4E6_trunc (w : UpperHalfPlane) (h : Strip w) :
    ‖(Work.Kernels.E2Fun w) ^ 2 * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)
      - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) ^ 2
        * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
          * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))‖ ≤ 20000000 * ‖nomeQ w‖ ^ 3 := by
  obtain ⟨he2, _, _⟩ := EisensteinQExp
  obtain ⟨hb2, hb4, hb6, hE2, hE4, hE6⟩ := strip_trunc_bounds w h
  have h2 := he2 w h.2
  have hE10 := E10_trunc w h
  have hq3 : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
  have hkey : (Work.Kernels.E2Fun w) ^ 2 * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)
      - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) ^ 2
        * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
          * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
      = ((Work.Kernels.E2Fun w) ^ 2 - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) ^ 2)
          * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)
        + (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) ^ 2
          * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w
            - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
              * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)) := by ring
  rw [hkey]
  have hsq : ‖(Work.Kernels.E2Fun w) ^ 2
      - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) ^ 2‖ ≤ 4000 * ‖nomeQ w‖ ^ 3 := by
    have hh := norm_sq_sub_sq_le (Work.Kernels.E2Fun w)
      (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
    have hb : ‖Work.Kernels.E2Fun w‖
        + ‖(1 : ℂ) - 24 * nomeQ w - 72 * (nomeQ w) ^ 2‖ ≤ 4 := by linarith [hE2, hb2]
    have h1 := mul_le_mul h2 hb (by positivity) (by norm_num)
    nlinarith [hh, h1, hq3]
  have h1 : ‖((Work.Kernels.E2Fun w) ^ 2
        - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) ^ 2)
      * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)‖ ≤ (4000 * ‖nomeQ w‖ ^ 3) * 4 := by
    rw [norm_mul]
    refine mul_le_mul hsq ?_ (norm_nonneg _) (by positivity)
    rw [norm_mul]
    have := mul_le_mul hE4 hE6 (norm_nonneg _) (by norm_num)
    linarith
  have h2 : ‖(1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) ^ 2
      * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w
        - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
          * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))‖
      ≤ 4 * (3000000 * ‖nomeQ w‖ ^ 3) := by
    rw [norm_mul, norm_pow]
    have hb : ‖(1 : ℂ) - 24 * nomeQ w - 72 * (nomeQ w) ^ 2‖ ^ 2 ≤ 4 := by
      nlinarith [hb2, norm_nonneg ((1 : ℂ) - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)]
    refine mul_le_mul hb ?_ (norm_nonneg _) (by positivity)
    show ‖Work.Kernels.E10Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
      * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)‖ ≤ 3000000 * ‖nomeQ w‖ ^ 3
    exact hE10
  have hsum := norm_add_le (((Work.Kernels.E2Fun w) ^ 2
        - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) ^ 2)
      * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w))
    ((1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) ^ 2
      * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w
        - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
          * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)))
  linarith [hsum, h1, h2, hq3]

lemma E2E4E6_trunc (w : UpperHalfPlane) (h : Strip w) :
    ‖Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)
      - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
        * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
          * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))‖ ≤ 20000000 * ‖nomeQ w‖ ^ 3 := by
  obtain ⟨he2, _, _⟩ := EisensteinQExp
  obtain ⟨hb2, hb4, _, hE2, hE4, hE6⟩ := strip_trunc_bounds w h
  have h2 := he2 w h.2
  have hE10 := E10_trunc w h
  have hq3 : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
  have hkey : Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)
      - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
        * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
          * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
      = (Work.Kernels.E2Fun w - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2))
          * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)
        + (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
          * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w
            - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
              * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)) := by ring
  rw [hkey]
  have h1 : ‖(Work.Kernels.E2Fun w - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2))
      * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)‖ ≤ (1000 * ‖nomeQ w‖ ^ 3) * 4 := by
    rw [norm_mul]
    refine mul_le_mul h2 ?_ (norm_nonneg _) (by positivity)
    rw [norm_mul]
    have := mul_le_mul hE4 hE6 (norm_nonneg _) (by norm_num)
    linarith
  have h2' : ‖(1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
      * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w
        - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
          * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))‖
      ≤ 2 * (3000000 * ‖nomeQ w‖ ^ 3) := by
    rw [norm_mul]
    refine mul_le_mul hb2 ?_ (norm_nonneg _) (by positivity)
    show ‖Work.Kernels.E10Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
      * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)‖ ≤ 3000000 * ‖nomeQ w‖ ^ 3
    exact hE10
  have hsum := norm_add_le ((Work.Kernels.E2Fun w - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2))
      * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w))
    ((1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
      * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w
        - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
          * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)))
  linarith [hsum, h1, h2', hq3]

lemma E2E4cube_trunc (w : UpperHalfPlane) (h : Strip w) :
    ‖Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w) ^ 3
      - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * (1 + 240 * nomeQ w
          + 2160 * (nomeQ w) ^ 2) ^ 3‖ ≤ 2000000 * ‖nomeQ w‖ ^ 3 := by
  obtain ⟨he2, he4, _⟩ := EisensteinQExp
  obtain ⟨hb2, hb4, _, hE2, hE4, _⟩ := strip_trunc_bounds w h
  have h2 := he2 w h.2
  have h4 := he4 w h.2
  have hq3 : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
  have hcube : ‖(Work.Kernels.E4Fun w) ^ 3
      - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3‖ ≤ 600000 * ‖nomeQ w‖ ^ 3 := by
    have hh := norm_cube_sub_cube_le (Work.Kernels.E4Fun w)
      (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
    have hb : ‖Work.Kernels.E4Fun w‖ ^ 2 + ‖Work.Kernels.E4Fun w‖
        * ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖
        + ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖ ^ 2 ≤ 12 := by
      have i1 : ‖Work.Kernels.E4Fun w‖ ^ 2 ≤ 4 := by
        nlinarith [hE4, norm_nonneg (Work.Kernels.E4Fun w)]
      have i2 : ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖ ^ 2 ≤ 4 := by
        nlinarith [hb4, norm_nonneg ((1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)]
      have i3 : ‖Work.Kernels.E4Fun w‖
          * ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖ ≤ 4 := by
        have := mul_le_mul hE4 hb4 (norm_nonneg _) (by norm_num)
        linarith
      linarith
    have h1 := mul_le_mul h4 hb (by positivity) (by norm_num)
    have hq3' : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
    linarith [hh, h1]
  have hkey : Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w) ^ 3
      - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
        * (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3
      = (Work.Kernels.E2Fun w - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2))
          * (Work.Kernels.E4Fun w) ^ 3
        + (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
          * ((Work.Kernels.E4Fun w) ^ 3
            - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3) := by ring
  rw [hkey]
  have hE4n3 : ‖(Work.Kernels.E4Fun w) ^ 3‖ ≤ 8 := by
    have h3 := pow_le_pow_left₀ (norm_nonneg (Work.Kernels.E4Fun w)) hE4 3
    norm_num at h3
    rw [norm_pow]
    exact h3
  have h1 : ‖(Work.Kernels.E2Fun w - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2))
      * (Work.Kernels.E4Fun w) ^ 3‖ ≤ (1000 * ‖nomeQ w‖ ^ 3) * 8 := by
    rw [norm_mul]
    exact mul_le_mul h2 hE4n3 (norm_nonneg _) (by positivity)
  have h2' : ‖(1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
      * ((Work.Kernels.E4Fun w) ^ 3
        - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3)‖
      ≤ 2 * (600000 * ‖nomeQ w‖ ^ 3) := by
    rw [norm_mul]
    exact mul_le_mul hb2 hcube (norm_nonneg _) (by positivity)
  have hsum := norm_add_le ((Work.Kernels.E2Fun w - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2))
      * (Work.Kernels.E4Fun w) ^ 3)
    ((1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
      * ((Work.Kernels.E4Fun w) ^ 3
        - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3))
  linarith [hsum, h1, h2', hq3]

lemma Delta_trunc (w : UpperHalfPlane) (h : Strip w) :
    ‖Work.Kernels.DeltaFun w - ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3
        - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728‖
      ≤ 3000 * ‖nomeQ w‖ ^ 3 := by
  obtain ⟨_, he4, he6⟩ := EisensteinQExp
  obtain ⟨_, hb4, hb6, _, hE4, hE6⟩ := strip_trunc_bounds w h
  have h4 := he4 w h.2
  have h6 := he6 w h.2
  have hq3 : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
  have hΔ : Work.Kernels.DeltaFun w
      = ((Work.Kernels.E4Fun w) ^ 3 - (Work.Kernels.E6Fun w) ^ 2) / 1728 :=
    ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq w
  rw [hΔ]
  have hkey : ((Work.Kernels.E4Fun w) ^ 3 - (Work.Kernels.E6Fun w) ^ 2) / 1728
      - ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3
          - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728
      = (((Work.Kernels.E4Fun w) ^ 3
            - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3)
          - ((Work.Kernels.E6Fun w) ^ 2
            - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2)) / 1728 := by ring
  rw [hkey, norm_div]
  have hc3 : ‖(Work.Kernels.E4Fun w) ^ 3
      - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3‖ ≤ 600000 * ‖nomeQ w‖ ^ 3 := by
    have hh := norm_cube_sub_cube_le (Work.Kernels.E4Fun w)
      (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
    have hb : ‖Work.Kernels.E4Fun w‖ ^ 2 + ‖Work.Kernels.E4Fun w‖
        * ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖
        + ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖ ^ 2 ≤ 12 := by
      have i1 : ‖Work.Kernels.E4Fun w‖ ^ 2 ≤ 4 := by
        nlinarith [hE4, norm_nonneg (Work.Kernels.E4Fun w)]
      have i2 : ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖ ^ 2 ≤ 4 := by
        nlinarith [hb4, norm_nonneg ((1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)]
      have i3 : ‖Work.Kernels.E4Fun w‖
          * ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖ ≤ 4 := by
        have := mul_le_mul hE4 hb4 (norm_nonneg _) (by norm_num)
        linarith
      linarith
    have h1 := mul_le_mul h4 hb (by positivity) (by norm_num)
    have hq3' : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
    linarith [hh, h1]
  have hc2 : ‖(Work.Kernels.E6Fun w) ^ 2
      - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2‖ ≤ 4000000 * ‖nomeQ w‖ ^ 3 := by
    have hh := norm_sq_sub_sq_le (Work.Kernels.E6Fun w)
      (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)
    have hb : ‖Work.Kernels.E6Fun w‖
        + ‖(1 : ℂ) - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2‖ ≤ 4 := by linarith [hE6, hb6]
    have h1 := mul_le_mul h6 hb (by positivity) (by norm_num)
    have hq3' : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
    linarith [hh, h1]
  have hnorm : ‖(1728 : ℂ)‖ = 1728 := by norm_num
  rw [hnorm]
  have hsub := norm_sub_le ((Work.Kernels.E4Fun w) ^ 3
            - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3)
    ((Work.Kernels.E6Fun w) ^ 2
            - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2)
  have hfin : (600000 * ‖nomeQ w‖ ^ 3 + 4000000 * ‖nomeQ w‖ ^ 3) / 1728
      ≤ 3000 * ‖nomeQ w‖ ^ 3 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1728)]
    nlinarith [hq3]
  linarith [hsub, hc3, hc2, hfin]

lemma E2Delta_trunc (w : UpperHalfPlane) (h : Strip w) :
    ‖Work.Kernels.E2Fun w * Work.Kernels.DeltaFun w
      - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
        * (((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3
          - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728)‖
      ≤ 100000 * ‖nomeQ w‖ ^ 3 := by
  obtain ⟨he2, _, _⟩ := EisensteinQExp
  obtain ⟨hb2, _, _, hE2, _, _⟩ := strip_trunc_bounds w h
  have h2 := he2 w h.2
  have hd := Delta_trunc w h
  obtain ⟨_, he4, he6⟩ := EisensteinQExp
  obtain ⟨_, _, _, _, hE4, hE6⟩ := strip_trunc_bounds w h
  have hq3 : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
  have hkey : Work.Kernels.E2Fun w * Work.Kernels.DeltaFun w
      - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
        * (((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3
          - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728)
      = (Work.Kernels.E2Fun w - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2))
          * Work.Kernels.DeltaFun w
        + (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
          * (Work.Kernels.DeltaFun w
            - ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3
              - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728) := by ring
  rw [hkey]
  have hDn : ‖Work.Kernels.DeltaFun w‖ ≤ 1 := by
    have hΔ : Work.Kernels.DeltaFun w
        = ((Work.Kernels.E4Fun w) ^ 3 - (Work.Kernels.E6Fun w) ^ 2) / 1728 :=
      ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq w
    rw [hΔ, norm_div]
    have hnorm : ‖(1728 : ℂ)‖ = 1728 := by norm_num
    rw [hnorm]
    have hsub := norm_sub_le ((Work.Kernels.E4Fun w) ^ 3) ((Work.Kernels.E6Fun w) ^ 2)
    have h1 : ‖(Work.Kernels.E4Fun w) ^ 3‖ ≤ 8 := by
      have h3 := pow_le_pow_left₀ (norm_nonneg (Work.Kernels.E4Fun w)) hE4 3
      norm_num at h3
      rw [norm_pow]
      exact h3
    have h2' : ‖(Work.Kernels.E6Fun w) ^ 2‖ ≤ 4 := by
      have h3 := pow_le_pow_left₀ (norm_nonneg (Work.Kernels.E6Fun w)) hE6 2
      norm_num at h3
      rw [norm_pow]
      exact h3
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1728)]
    linarith
  have h1 : ‖(Work.Kernels.E2Fun w - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2))
      * Work.Kernels.DeltaFun w‖ ≤ (1000 * ‖nomeQ w‖ ^ 3) * 1 := by
    rw [norm_mul]
    exact mul_le_mul h2 hDn (norm_nonneg _) (by positivity)
  have h2'' : ‖(1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
      * (Work.Kernels.DeltaFun w
        - ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3
          - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728)‖
      ≤ 2 * (3000 * ‖nomeQ w‖ ^ 3) := by
    rw [norm_mul]
    exact mul_le_mul hb2 hd (norm_nonneg _) (by positivity)
  have hsum := norm_add_le ((Work.Kernels.E2Fun w - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2))
      * Work.Kernels.DeltaFun w)
    ((1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
      * (Work.Kernels.DeltaFun w
        - ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3
          - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728))
  linarith [hsum, h1, h2'', hq3]

theorem PnumCnum_strip_bound (ℓ : Work.Kernels.LogLambdaData) (w : UpperHalfPlane)
    (h : Strip w) :
    ‖Pnum w + Complex.I * nomeQ w‖ ≤ 10000 * ‖nomeQ w‖ ^ 2
      ∧ ‖Cnum ℓ w‖ ≤ 2 * ‖nomeQ w‖ := by
  have hE2 := (EisensteinQExp.1 w h.2)
  have hE4 := (EisensteinQExp.2.1 w h.2)
  have hE6 := (EisensteinQExp.2.2 w h.2)
  obtain ⟨hb2, hb4, hb6, hE2n, hE4n, hE6n⟩ := strip_trunc_bounds w h
  have hT10 := E10_trunc w h
  have hA1 := E4sqE6_trunc w h
  have hA2 := E2sqE4E6_trunc w h
  have hA3 := E2E4cube_trunc w h
  have hA5 := E2E4E6_trunc w h
  have hA4 := E2Delta_trunc w h
  have hΔd := Delta_trunc w h
  have hQ1 := (strip_facts w h).1
  have hQnn : (0 : ℝ) ≤ ‖nomeQ w‖ := norm_nonneg _
  have hQ2 : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 2 := by positivity
  have hQ3 : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
  have hI288 : ‖Complex.I / 288‖ = 1 / 288 := by
    rw [norm_div, Complex.norm_I, Complex.norm_ofNat]
  have hI144 : ‖Complex.I / 144‖ = 1 / 144 := by
    rw [norm_div, Complex.norm_I, Complex.norm_ofNat]
  have hI7 : ‖(7 : ℂ) * Complex.I‖ = 7 := by rw [norm_mul, Complex.norm_ofNat, Complex.norm_I,
    mul_one]
  have hpin : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  constructor
  · -- `Pnum`
    have hmodelP : ((-(Complex.I / 288))
          * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2
              * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)
            + (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) ^ 2
              * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
                * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)))
        + (Complex.I / 144) * ((1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
            * (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3)
        - 7 * Complex.I * ((1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
            * (((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3
              - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728))
        + Complex.I * nomeQ w)
        = Complex.I * ((nomeQ w) ^ 2 * (∑ k ∈ Finset.range 7, cPm k * (nomeQ w) ^ k)) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, cPm, pow_zero, pow_one, mul_one,
        zero_add] <;> ring_nf
    have hkey : Pnum w + Complex.I * nomeQ w
        = ((-(Complex.I / 288))
          * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2
              * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)
            + (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) ^ 2
              * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
                * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)))
        + (Complex.I / 144) * ((1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
            * (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3)
        - 7 * Complex.I * ((1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
            * (((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3
              - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728))
        + Complex.I * nomeQ w)
          + ((-(Complex.I / 288)) * (((Work.Kernels.E4Fun w) ^ 2 * Work.Kernels.E6Fun w
                - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2
                  * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
              + ((Work.Kernels.E2Fun w) ^ 2
                  * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)
                - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) ^ 2
                  * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
                    * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)))))
          + ((Complex.I / 144) * (Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w) ^ 3
              - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
                * (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3))
          + ((-(7 * Complex.I)) * (Work.Kernels.E2Fun w * Work.Kernels.DeltaFun w
              - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
                * (((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3
                  - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728))) := by
      simp only [Pnum]
      ring_nf
    rw [hkey, hmodelP]
    have hm : ‖Complex.I * ((nomeQ w) ^ 2 * (∑ k ∈ Finset.range 7, cPm k * (nomeQ w) ^ k))‖ ≤ 2600 * ‖nomeQ w‖ ^ 2 := by
      rw [norm_mul, Complex.norm_I, one_mul, norm_mul, norm_pow]
      have hs := norm_sum_pow_le (nomeQ w) (1 / 280000) hQ1 cPm 7
      have hnum : (∑ k ∈ Finset.range 7, ‖cPm k‖ * (1 / 280000 : ℝ) ^ k) ≤ 2600 := by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, cPm, pow_zero, pow_one,
          Complex.norm_ofNat, norm_neg, mul_one, zero_add, add_zero] <;> norm_num
      have h1 : ‖∑ k ∈ Finset.range 7, cPm k * (nomeQ w) ^ k‖ ≤ 2600 := le_trans hs hnum
      calc ‖nomeQ w‖ ^ 2 * ‖∑ k ∈ Finset.range 7, cPm k * (nomeQ w) ^ k‖
          ≤ ‖nomeQ w‖ ^ 2 * 2600 := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2600 * ‖nomeQ w‖ ^ 2 := by ring
    have hb1 : ‖(-(Complex.I / 288)) * (((Work.Kernels.E4Fun w) ^ 2 * Work.Kernels.E6Fun w
                - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2
                  * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
              + ((Work.Kernels.E2Fun w) ^ 2
                  * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)
                - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) ^ 2
                  * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
                    * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))))‖
        ≤ (1 / 288) * (5000000 * ‖nomeQ w‖ ^ 3 + 20000000 * ‖nomeQ w‖ ^ 3) := by
      rw [norm_mul]
      have hn : ‖-(Complex.I / 288)‖ = 1 / 288 := by rw [norm_neg, hI288]
      rw [hn]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have hh := norm_add_le ((Work.Kernels.E4Fun w) ^ 2 * Work.Kernels.E6Fun w
                - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2
                  * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
        ((Work.Kernels.E2Fun w) ^ 2 * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)
                - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) ^ 2
                  * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
                    * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)))
      linarith [hh, hA1, hA2]
    have hb2 : ‖(Complex.I / 144) * (Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w) ^ 3
              - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
                * (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3)‖ ≤ (1 / 144) * (2000000 * ‖nomeQ w‖ ^ 3) := by
      rw [norm_mul, hI144]
      exact mul_le_mul_of_nonneg_left hA3 (by norm_num)
    have hb3 : ‖(-(7 * Complex.I)) * (Work.Kernels.E2Fun w * Work.Kernels.DeltaFun w
              - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
                * (((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3
                  - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728))‖ ≤ 7 * (100000 * ‖nomeQ w‖ ^ 3) := by
      rw [norm_mul, norm_neg, hI7]
      exact mul_le_mul_of_nonneg_left hA4 (by norm_num)
    have ht1 := norm_add_le (Complex.I * ((nomeQ w) ^ 2 * (∑ k ∈ Finset.range 7, cPm k * (nomeQ w) ^ k))) ((-(Complex.I / 288)) * (((Work.Kernels.E4Fun w) ^ 2 * Work.Kernels.E6Fun w
                - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2
                  * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
              + ((Work.Kernels.E2Fun w) ^ 2
                  * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)
                - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) ^ 2
                  * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
                    * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)))))
    have ht2 := norm_add_le ((Complex.I * ((nomeQ w) ^ 2 * (∑ k ∈ Finset.range 7, cPm k * (nomeQ w) ^ k))) + ((-(Complex.I / 288)) * (((Work.Kernels.E4Fun w) ^ 2 * Work.Kernels.E6Fun w
                - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2
                  * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
              + ((Work.Kernels.E2Fun w) ^ 2
                  * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)
                - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) ^ 2
                  * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
                    * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)))))) ((Complex.I / 144) * (Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w) ^ 3
              - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
                * (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3))
    have ht3 := norm_add_le (((Complex.I * ((nomeQ w) ^ 2 * (∑ k ∈ Finset.range 7, cPm k * (nomeQ w) ^ k))) + ((-(Complex.I / 288)) * (((Work.Kernels.E4Fun w) ^ 2 * Work.Kernels.E6Fun w
                - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2
                  * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
              + ((Work.Kernels.E2Fun w) ^ 2
                  * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)
                - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) ^ 2
                  * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
                    * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)))))) + ((Complex.I / 144) * (Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w) ^ 3
              - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
                * (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3))) ((-(7 * Complex.I)) * (Work.Kernels.E2Fun w * Work.Kernels.DeltaFun w
              - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
                * (((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3
                  - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728)))
    have hfinal : 2600 * ‖nomeQ w‖ ^ 2
        + (1 / 288) * (5000000 * ‖nomeQ w‖ ^ 3 + 20000000 * ‖nomeQ w‖ ^ 3)
        + (1 / 144) * (2000000 * ‖nomeQ w‖ ^ 3) + 7 * (100000 * ‖nomeQ w‖ ^ 3)
        ≤ 10000 * ‖nomeQ w‖ ^ 2 := by
      have hq3 : ‖nomeQ w‖ ^ 3 ≤ (1 / 280000 : ℝ) * ‖nomeQ w‖ ^ 2 := nomeQ_pow3_le w h
      nlinarith [hq3, hQ2, hQnn]
    linarith [ht1, ht2, ht3, hm, hb1, hb2, hb3, hfinal]
  · -- `Cnum`
    have hlog : 4 * Real.log 2 ≤ 2.78 := by
      have := Real.log_two_lt_d9
      nlinarith [this]
    have hlog' : |4 * Real.log 2 - 22| ≤ 19.3 := by
      rw [abs_le]
      constructor
      · have := Real.log_two_gt_d9
        nlinarith [this]
      · have := Real.log_two_lt_d9
        nlinarith [this]
    have hmodel : (((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))) / 48 + (((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728) * (4 * (Real.log 2 : ℂ) - 22))
        = (nomeQ w) * (∑ k ∈ Finset.range 6, cA k * (nomeQ w) ^ k) + 4 * (Real.log 2 : ℂ) * ((nomeQ w) * (∑ k ∈ Finset.range 6, cDm k * (nomeQ w) ^ k)) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, cA, cDm, pow_zero, pow_one,
        mul_one, zero_add] <;> ring_nf
    have hkey : Cnum ℓ w = ((((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))) / 48 + (((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728) * (4 * (Real.log 2 : ℂ) - 22)) + (((Work.Kernels.E4Fun w) ^ 3 - Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)) / 48 - ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))) / 48 + (Work.Kernels.DeltaFun w - (((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728)) * (4 * (Real.log 2 : ℂ) - 22))) / (Real.pi : ℂ) := by
      rw [Cnum, CuspL_eq ℓ]
      ring_nf
    have hAn : ‖(nomeQ w) * (∑ k ∈ Finset.range 6, cA k * (nomeQ w) ^ k)‖ ≤ 1.1 * ‖nomeQ w‖ := by
      rw [norm_mul]
      have hs := norm_sum_pow_le (nomeQ w) (1 / 280000) hQ1 cA 6
      have hnum : (∑ k ∈ Finset.range 6, ‖cA k‖ * (1 / 280000 : ℝ) ^ k) ≤ 1.1 := by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, cA, pow_zero, pow_one,
          Complex.norm_ofNat, norm_neg, mul_one, zero_add, add_zero] <;> norm_num
      have h1 : ‖∑ k ∈ Finset.range 6, cA k * (nomeQ w) ^ k‖ ≤ 1.1 := le_trans hs hnum
      calc ‖nomeQ w‖ * ‖∑ k ∈ Finset.range 6, cA k * (nomeQ w) ^ k‖
          ≤ ‖nomeQ w‖ * 1.1 := mul_le_mul_of_nonneg_left h1 hQnn
        _ = 1.1 * ‖nomeQ w‖ := by ring
    have hDmn : ‖(nomeQ w) * (∑ k ∈ Finset.range 6, cDm k * (nomeQ w) ^ k)‖
        ≤ 1.1 * ‖nomeQ w‖ := by
      rw [norm_mul]
      have hs := norm_sum_pow_le (nomeQ w) (1 / 280000) hQ1 cDm 6
      have hnum : (∑ k ∈ Finset.range 6, ‖cDm k‖ * (1 / 280000 : ℝ) ^ k) ≤ 1.1 := by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, cDm, pow_zero, pow_one,
          Complex.norm_ofNat, norm_neg, mul_one, zero_add, add_zero] <;> norm_num
      have h1 : ‖∑ k ∈ Finset.range 6, cDm k * (nomeQ w) ^ k‖ ≤ 1.1 := le_trans hs hnum
      calc ‖nomeQ w‖ * ‖∑ k ∈ Finset.range 6, cDm k * (nomeQ w) ^ k‖
          ≤ ‖nomeQ w‖ * 1.1 := mul_le_mul_of_nonneg_left h1 hQnn
        _ = 1.1 * ‖nomeQ w‖ := by ring
    have hclog : ‖(4 : ℂ) * (Real.log 2 : ℂ)‖ = 4 * Real.log 2 := by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.log_pos (by norm_num))]
    have hnumM : ‖(nomeQ w) * (∑ k ∈ Finset.range 6, cA k * (nomeQ w) ^ k) + 4 * (Real.log 2 : ℂ) * ((nomeQ w) * (∑ k ∈ Finset.range 6, cDm k * (nomeQ w) ^ k))‖ ≤ 4.2 * ‖nomeQ w‖ := by
      have hsum := norm_add_le ((nomeQ w) * (∑ k ∈ Finset.range 6, cA k * (nomeQ w) ^ k))
        (4 * (Real.log 2 : ℂ)
          * ((nomeQ w) * (∑ k ∈ Finset.range 6, cDm k * (nomeQ w) ^ k)))
      have h2 : ‖(4 : ℂ) * (Real.log 2 : ℂ)
          * ((nomeQ w) * (∑ k ∈ Finset.range 6, cDm k * (nomeQ w) ^ k))‖
          ≤ 4 * Real.log 2 * (1.1 * ‖nomeQ w‖) := by
        rw [norm_mul, hclog]
        exact mul_le_mul_of_nonneg_left hDmn (by positivity)
      have h4 : 1.1 * ‖nomeQ w‖ + 4 * Real.log 2 * (1.1 * ‖nomeQ w‖) ≤ 4.2 * ‖nomeQ w‖ := by
        nlinarith [hlog, hQnn]
      linarith [hsum, hAn, h2, h4]
    have herr : ‖(((Work.Kernels.E4Fun w) ^ 3 - Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)) / 48 - ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))) / 48 + (Work.Kernels.DeltaFun w - (((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728)) * (4 * (Real.log 2 : ℂ) - 22))‖ ≤ 2000000 * ‖nomeQ w‖ ^ 3 := by
      have hcube : ‖(Work.Kernels.E4Fun w) ^ 3
          - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3‖ ≤ 600000 * ‖nomeQ w‖ ^ 3 := by
        have hh := norm_cube_sub_cube_le (Work.Kernels.E4Fun w)
          (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
        have hb : ‖Work.Kernels.E4Fun w‖ ^ 2 + ‖Work.Kernels.E4Fun w‖
            * ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖
            + ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖ ^ 2 ≤ 12 := by
          have i1 : ‖Work.Kernels.E4Fun w‖ ^ 2 ≤ 4 := by
            nlinarith [hE4n, norm_nonneg (Work.Kernels.E4Fun w)]
          have i2 : ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖ ^ 2 ≤ 4 := by
            nlinarith [hb4, norm_nonneg ((1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)]
          have i3 : ‖Work.Kernels.E4Fun w‖
              * ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖ ≤ 4 := by
            have := mul_le_mul hE4n hb4 (norm_nonneg _) (by norm_num)
            linarith
          linarith
        have h1 := mul_le_mul hE4 hb (by positivity) (by norm_num)
        linarith [hh, h1]
      have hfirst : ‖((Work.Kernels.E4Fun w) ^ 3 - Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)) / 48 - ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))) / 48‖ ≤ 1000000 * ‖nomeQ w‖ ^ 3 := by
        have heq : ((Work.Kernels.E4Fun w) ^ 3 - Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)) / 48 - ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))) / 48
            = ((Work.Kernels.E4Fun w) ^ 3
                  - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3
                - (Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)
                  - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
                    * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
                      * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)))) / 48 := by ring
        rw [heq, norm_div]
        have hnorm : ‖(48 : ℂ)‖ = 48 := by norm_num
        rw [hnorm]
        have hsub := norm_sub_le ((Work.Kernels.E4Fun w) ^ 3
                  - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3)
          (Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)
                  - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
                    * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
                      * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)))
        have hfin : (600000 * ‖nomeQ w‖ ^ 3 + 20000000 * ‖nomeQ w‖ ^ 3) / 48
            ≤ 1000000 * ‖nomeQ w‖ ^ 3 := by
          rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 48)]
          nlinarith [hQ3]
        calc ‖(Work.Kernels.E4Fun w) ^ 3
                  - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3
                - (Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)
                  - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
                    * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
                      * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)))‖ / 48
            ≤ (600000 * ‖nomeQ w‖ ^ 3 + 20000000 * ‖nomeQ w‖ ^ 3) / 48 :=
              div_le_div_of_nonneg_right (by linarith [hsub, hcube, hA5]) (by norm_num)
          _ ≤ 1000000 * ‖nomeQ w‖ ^ 3 := hfin
      have hsecond : ‖(Work.Kernels.DeltaFun w - (((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728)) * (4 * (Real.log 2 : ℂ) - 22)‖ ≤ 200000 * ‖nomeQ w‖ ^ 3 := by
        rw [norm_mul]
        have hc : (4 : ℂ) * (Real.log 2 : ℂ) - 22 = ((4 * Real.log 2 - 22 : ℝ) : ℂ) := by
          push_cast; ring
        rw [hc, Complex.norm_real, Real.norm_eq_abs]
        calc ‖Work.Kernels.DeltaFun w
                - (((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3
                  - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728)‖
              * |4 * Real.log 2 - 22| ≤ (3000 * ‖nomeQ w‖ ^ 3) * 19.3 :=
              mul_le_mul hΔd hlog' (abs_nonneg _) (by positivity)
          _ ≤ 200000 * ‖nomeQ w‖ ^ 3 := by nlinarith [hQ3]
      have hsum := norm_add_le (((Work.Kernels.E4Fun w) ^ 3 - Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)) / 48 - ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))) / 48) ((Work.Kernels.DeltaFun w - (((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728)) * (4 * (Real.log 2 : ℂ) - 22))
      linarith [hsum, hfirst, hsecond, hQ3]
    have htot : (4.2 * ‖nomeQ w‖ + 2000000 * ‖nomeQ w‖ ^ 3) / Real.pi ≤ 2 * ‖nomeQ w‖ := by
      rw [div_le_iff₀ Real.pi_pos]
      have hq3 : ‖nomeQ w‖ ^ 3 ≤ (1 / 280000 : ℝ) * ‖nomeQ w‖ ^ 2 := nomeQ_pow3_le w h
      nlinarith [hq3, hQnn, hQ2, Real.pi_gt_three]
    have hnum2 : ‖((nomeQ w) * (∑ k ∈ Finset.range 6, cA k * (nomeQ w) ^ k) + 4 * (Real.log 2 : ℂ) * ((nomeQ w) * (∑ k ∈ Finset.range 6, cDm k * (nomeQ w) ^ k))) + ((((Work.Kernels.E4Fun w) ^ 3 - Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)) / 48 - ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))) / 48 + (Work.Kernels.DeltaFun w - (((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728)) * (4 * (Real.log 2 : ℂ) - 22)))‖ ≤ 4.2 * ‖nomeQ w‖ + 2000000 * ‖nomeQ w‖ ^ 3 := by
      have hsum := norm_add_le ((nomeQ w) * (∑ k ∈ Finset.range 6, cA k * (nomeQ w) ^ k) + 4 * (Real.log 2 : ℂ) * ((nomeQ w) * (∑ k ∈ Finset.range 6, cDm k * (nomeQ w) ^ k))) ((((Work.Kernels.E4Fun w) ^ 3 - Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)) / 48 - ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))) / 48 + (Work.Kernels.DeltaFun w - (((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728)) * (4 * (Real.log 2 : ℂ) - 22)))
      linarith [hsum, hnumM, herr]
    calc ‖Cnum ℓ w‖ = ‖((((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))) / 48 + (((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728) * (4 * (Real.log 2 : ℂ) - 22)) + (((Work.Kernels.E4Fun w) ^ 3 - Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)) / 48 - ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))) / 48 + (Work.Kernels.DeltaFun w - (((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728)) * (4 * (Real.log 2 : ℂ) - 22))) / (Real.pi : ℂ)‖ := by rw [hkey]
      _ = ‖(((nomeQ w) * (∑ k ∈ Finset.range 6, cA k * (nomeQ w) ^ k) + 4 * (Real.log 2 : ℂ) * ((nomeQ w) * (∑ k ∈ Finset.range 6, cDm k * (nomeQ w) ^ k))) + (((Work.Kernels.E4Fun w) ^ 3 - Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)) / 48 - ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))) / 48 + (Work.Kernels.DeltaFun w - (((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728)) * (4 * (Real.log 2 : ℂ) - 22))) / (Real.pi : ℂ)‖ := by rw [hmodel]
      _ = ‖((nomeQ w) * (∑ k ∈ Finset.range 6, cA k * (nomeQ w) ^ k) + 4 * (Real.log 2 : ℂ) * ((nomeQ w) * (∑ k ∈ Finset.range 6, cDm k * (nomeQ w) ^ k))) + (((Work.Kernels.E4Fun w) ^ 3 - Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)) / 48 - ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))) / 48 + (Work.Kernels.DeltaFun w - (((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2) / 1728)) * (4 * (Real.log 2 : ℂ) - 22))‖ / Real.pi := by rw [norm_div, hpin]
      _ ≤ (4.2 * ‖nomeQ w‖ + 2000000 * ‖nomeQ w‖ ^ 3) / Real.pi :=
            div_le_div_of_nonneg_right hnum2 (le_of_lt Real.pi_pos)
      _ ≤ 2 * ‖nomeQ w‖ := htot

/-! ## The two target estimates -/

lemma Gcusp10_eq_Gcusp24 (ℓ : Work.Kernels.LogLambdaData) (w : UpperHalfPlane) :
    Gcusp ℓ 24 1 0 w = Gcusp24 ℓ 1 0 w := rfl

lemma PGGcusp10StripBound (ℓ : Work.Kernels.LogLambdaData) (w : UpperHalfPlane) (h : Strip w) :
    ‖Gcusp ℓ 24 1 0 w‖ ≤ 5 * (1 + ‖(w : ℂ)‖) * ‖nomeQ w‖ := by
  have hred : 2 * Gcusp ℓ 24 1 0 w = (w : ℂ) * Pnum w + Cnum ℓ w + W3 ℓ w :=
    Gcusp10_reduced ℓ w
  have hP := PnumCnum_strip_bound ℓ w h
  have hW := W3_strip_bound ℓ w h
  have hQ1 := (strip_facts w h).1
  have hQnn : (0 : ℝ) ≤ ‖nomeQ w‖ := norm_nonneg _
  have hw : (0 : ℝ) ≤ ‖(w : ℂ)‖ := norm_nonneg _
  have hPn : ‖Pnum w‖ ≤ 2 * ‖nomeQ w‖ := by
    have h1 : ‖Pnum w‖ ≤ ‖Pnum w + Complex.I * nomeQ w‖ + ‖nomeQ w‖ := by
      have hh := norm_add_le (Pnum w + Complex.I * nomeQ w) (-(Complex.I * nomeQ w))
      have heq : (Pnum w + Complex.I * nomeQ w) + (-(Complex.I * nomeQ w)) = Pnum w := by ring
      rw [heq, norm_neg, norm_mul, Complex.norm_I, one_mul] at hh
      exact hh
    have h2 : 10000 * ‖nomeQ w‖ ^ 2 ≤ ‖nomeQ w‖ := by
      have h3 : ‖nomeQ w‖ ^ 2 ≤ (1 / 280000 : ℝ) * ‖nomeQ w‖ := by nlinarith [hQ1, hQnn]
      nlinarith [h3, hQnn]
    linarith [h1, hP.1, h2]
  have htri : ‖(w : ℂ) * Pnum w + Cnum ℓ w + W3 ℓ w‖
      ≤ 10 * (1 + ‖(w : ℂ)‖) * ‖nomeQ w‖ := by
    have h1 := norm_add_le ((w : ℂ) * Pnum w + Cnum ℓ w) (W3 ℓ w)
    have h2 := norm_add_le ((w : ℂ) * Pnum w) (Cnum ℓ w)
    have h3 : ‖(w : ℂ) * Pnum w‖ ≤ ‖(w : ℂ)‖ * (2 * ‖nomeQ w‖) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hPn hw
    have hfin : ‖(w : ℂ)‖ * (2 * ‖nomeQ w‖) + 2 * ‖nomeQ w‖
        + 4 * (1 + ‖(w : ℂ)‖) * ‖nomeQ w‖ ≤ 10 * (1 + ‖(w : ℂ)‖) * ‖nomeQ w‖ := by
      nlinarith [hQnn, hw]
    linarith [h1, h2, h3, hP.2, hW, hfin]
  have h2 : ‖2 * Gcusp ℓ 24 1 0 w‖ = 2 * ‖Gcusp ℓ 24 1 0 w‖ := by
    rw [norm_mul, Complex.norm_ofNat]
  rw [hred] at h2
  linarith [h2, htri]

lemma PGGcusp10DeltaBound (ℓ : Work.Kernels.LogLambdaData) (w : UpperHalfPlane) (h : Strip w) :
    ‖Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ w) - Gcusp ℓ 24 1 0 w + Complex.I * nomeQ w‖
      ≤ 100000 * ‖nomeQ w‖ ^ 2 := by
  have hdg : 2 * (Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ w) - Gcusp ℓ 24 1 0 w)
      = Pnum w + Complex.I * Xnum w / 1152 := dg10_eq ℓ w
  have hP := PnumCnum_strip_bound ℓ w h
  have hX := Xnum_strip_close w h
  have hkey : Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ w) - Gcusp ℓ 24 1 0 w + Complex.I * nomeQ w
      = (Pnum w + Complex.I * nomeQ w) / 2
        + Complex.I * (Xnum w + 1152 * nomeQ w) / 2304 := by
    linear_combination (1 / 2) * hdg
  rw [hkey]
  have h1a : ‖(Pnum w + Complex.I * nomeQ w) / 2‖ ≤ 10000 * ‖nomeQ w‖ ^ 2 / 2 := by
    rw [norm_div, Complex.norm_ofNat]
    linarith [hP.1]
  have h1b : ‖Complex.I * (Xnum w + 1152 * nomeQ w) / 2304‖
      ≤ (1000000 * ‖nomeQ w‖ ^ 2) / 2304 := by
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_ofNat]
    linarith [hX]
  have h1 : ‖(Pnum w + Complex.I * nomeQ w) / 2
        + Complex.I * (Xnum w + 1152 * nomeQ w) / 2304‖
      ≤ 10000 * ‖nomeQ w‖ ^ 2 / 2 + (1000000 * ‖nomeQ w‖ ^ 2) / 2304 := by
    have hsum := norm_add_le ((Pnum w + Complex.I * nomeQ w) / 2)
      (Complex.I * (Xnum w + 1152 * nomeQ w) / 2304)
    linarith [hsum, h1a, h1b]
  have hfin : 10000 * ‖nomeQ w‖ ^ 2 / 2 + (1000000 * ‖nomeQ w‖ ^ 2) / 2304
      ≤ 100000 * ‖nomeQ w‖ ^ 2 := by
    nlinarith [pow_nonneg (norm_nonneg (nomeQ w)) 2]
  linarith [h1, hfin]

end

end Work.Asymptotics
