import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseGateFS.alpha_ratio_est
import Submission.Work.BoseGateFS.arith_lip2
import Submission.Work.BoseGateFS.perMode_bounds_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseGateFS.alpha_lip_abs2` — the Lipschitz bound on the squeezing parameter

This is the node `K3`/`alpha_lip` of the `BoseB7A` interface (`Q3Kernel.alpha_lip`),
in its *absolute* (non-existential) form: the constant

`K₀ = 10 ^ 12 * (Cw + Cg + Cτ + 1) ^ 4 * (1 + 1/cτ) ^ 4 * (1 + 1/a) ^ 4`

exhibited explicitly, from the per-mode cutoff bounds on `P_H^q`, the gradient rows
of `τ` (`Cτ`, growth `‖p‖+‖q‖`) and of `Ŵ₁` (`Cg`, growth `1`), and the pointwise
bound `|Ŵ₁| ≤ C_w a` — **no decay of `Ŵ₁`** is assumed (this is the difference with
`Work.BoseGateFS.alpha_lip_abs`, which needs `|Ŵ₁(k)|(1+‖k‖)² ≤ C_w a`).

## The argument

Write `𝒜_k = E.A k`, `ℬ_k = E.B k`, `s = K_H·a`, `M = max 𝒜_p 𝒜_q`,
`R = max ‖k_p‖ ‖k_q‖`, `F = max (|ℬ_p|/𝒜_p) (|ℬ_q|/𝒜_q)`, `d = ‖k_p − k_q‖`.

1. `α_k = h(ℬ_k/𝒜_k)` with `h r = r/(1+√(1-r²))`; `h` is `4`-Lipschitz on `[-½,½]`
   and `|ℬ_k/𝒜_k| ≤ ½` on `P_H^q` (`hAB`), so `Work.BoseGateFS.alpha_ratio_est`
   gives `|Δα| ≤ 4(|Δℬ|/M + F|Δ𝒜|/M)`.
2. On `P_H^q` one has `𝒜 ≥ 1/(32s²)` (`hAge` + the cutoff), `1/M ≤ 32s²` and
   `F ≤ 32 s² ρ C_w a` (`Work.BoseGateFS.perMode_bounds_le`), while `F ≤ ½`
   (`hAB`) and `1/M ≤ 2/R² ≤ 32 s²` (`hAge`, `R ≥ 1/(4s)`).
   Splitting `Δ𝒜 = Δτ + ρΔŴ₁`:
   * the `Δℬ` piece and the `ρΔŴ₁` piece carry a factor `ρ` and no growth in `R`,
     so `1/M ≤ 32s²` is used (`hW1grad`, `hA`, `hB`);
   * the `Δτ` piece grows like `R`, and there `1/M ≤ 2/R²` and `1/R ≤ 4s` give
     `|Δτ|/M ≤ 16 Cτ s d` (`htau_grad`).
   This yields `|Δα| ≤ (192 ρC_g a s² + 2048 ρC_w a Cτ s³) d`.
3. The arithmetic (`Work.BoseGateFS.arith_lip2`): with `ρ ≤ 3μ/2`, `s ≥ 1`,
   `a > 0`, `s = K_Ha`, the coefficient is `≤ 10^12 (Cw+Cg+Cτ+1)^4 (1+1/cτ)^4
   (1+1/a)^4 · 𝓁 · s`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseGateFS

theorem alpha_lip_abs2 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} {E : Work.BoseB7.Q3Env Mode}
    {Cw Cg Cτ cτ : ℝ} (hCw : 0 ≤ Cw) (hCg : 0 ≤ Cg) (hCτ : 0 ≤ Cτ) (hcτ : 0 < cτ)
    (hKH : 0 < E.KH) (ha : 0 < E.aScat) (hKHa : 1 ≤ E.KH * E.aScat)
    (hlille : E.lille = E.mu * E.aScat ^ 3 * E.KH ^ 2)
    (hrho0 : 0 ≤ E.rho) (hrho : E.rho ≤ 3 * E.mu / 2)
    (hW1le : ∀ k : Mode, |E.W1 k| ≤ Cw * E.aScat)
    (hW1grad : ∀ p q : Mode, |E.W1 p - E.W1 q| ≤ Cg * E.aScat * ‖F.kmom p - F.kmom q‖)
    (htau_grad : ∀ p q : Mode, F.PHq E.KH E.aScat p → F.PHq E.KH E.aScat q →
      |E.tau p - E.tau q| ≤ Cτ * (‖F.kmom p‖ + ‖F.kmom q‖) * ‖F.kmom p - F.kmom q‖)
    (htau_lb : ∀ q : Mode, F.PHq E.KH E.aScat q → cτ * ‖F.kmom q‖ ^ 2 ≤ E.tau q)
    (hA : ∀ k : Mode, E.A k = E.tau k + E.rho * E.W1 k)
    (hB : ∀ k : Mode, E.B k = E.rho * E.W1 k)
    (hAge : ∀ q : Mode, F.PHq E.KH E.aScat q → ‖F.kmom q‖ ^ 2 / 2 ≤ E.A q)
    (hAB : ∀ q : Mode, F.PHq E.KH E.aScat q → 2 * |E.B q| ≤ E.A q) :
    ∀ p q : Mode, F.PHq E.KH E.aScat p → F.PHq E.KH E.aScat q →
      |E.alpha p - E.alpha q|
        ≤ 10 ^ 12 * (Cw + Cg + Cτ + 1) ^ 4 * (1 + 1 / cτ) ^ 4 * (1 + 1 / E.aScat) ^ 4
            * E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖ := by
  intro p q hp hq
  -- ## 0. the per-mode bounds on `P_H^q`
  obtain ⟨hA_lb0, hBA0, hMinv0, hInvR0⟩ :=
    perMode_bounds_le (F := F) (E := E) hCw hKH ha hKHa hrho0 hW1le hB hAge hAB
  set s : ℝ := E.KH * E.aScat with hs_def
  have hs1 : 1 ≤ s := by rw [hs_def]; exact hKHa
  have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have h32 : 0 < 32 * s ^ 2 := by
    have := sq_pos_of_ne_zero (ne_of_gt hs_pos)
    nlinarith
  have hAp : 0 < E.A p := lt_of_lt_of_le (one_div_pos.mpr h32) (hA_lb0 p hp)
  have hAq : 0 < E.A q := lt_of_lt_of_le (one_div_pos.mpr h32) (hA_lb0 q hq)
  have hmu0 : 0 ≤ E.mu := by linarith
  have hCwa : 0 ≤ Cw * E.aScat := mul_nonneg hCw ha.le
  -- ## 1. abbreviations
  set d : ℝ := ‖F.kmom p - F.kmom q‖ with hd_def
  have hd0 : 0 ≤ d := by rw [hd_def]; positivity
  set R : ℝ := max ‖F.kmom p‖ ‖F.kmom q‖ with hR_def
  set M : ℝ := max (E.A p) (E.A q) with hM_def
  set FM : ℝ := max (|E.B p| / E.A p) (|E.B q| / E.A q) with hFM_def
  have hM_pos : 0 < M := by
    rw [hM_def]; exact lt_of_lt_of_le hAp (le_max_left _ _)
  have hM_nn : 0 ≤ M := hM_pos.le
  have hFM_nn : 0 ≤ FM := by
    rw [hFM_def]
    exact le_trans (div_nonneg (abs_nonneg _) hAp.le) (le_max_left _ _)
  have hMinv : 1 / M ≤ 32 * s ^ 2 := by rw [hM_def]; exact hMinv0 p q hp hq
  have hFM_le : FM ≤ 32 * s ^ 2 * (E.rho * (Cw * E.aScat)) := by
    rw [hFM_def]; exact max_le (hBA0 p hp) (hBA0 q hq)
  have hratio_p : |E.B p| / E.A p ≤ 1 / 2 := by
    rw [div_le_iff₀ hAp]; linarith [hAB p hp]
  have hratio_q : |E.B q| / E.A q ≤ 1 / 2 := by
    rw [div_le_iff₀ hAq]; linarith [hAB q hq]
  have hFM_half : FM ≤ 1 / 2 := by rw [hFM_def]; exact max_le hratio_p hratio_q
  -- ## 2. the two Lipschitz rows, in terms of `d`
  have hW1grad_pq : |E.W1 p - E.W1 q| ≤ Cg * E.aScat * d := by
    have h := hW1grad p q; rw [← hd_def] at h; exact h
  have htau_grad_pq : |E.tau p - E.tau q| ≤ Cτ * (‖F.kmom p‖ + ‖F.kmom q‖) * d := by
    have h := htau_grad p q hp hq; rw [← hd_def] at h; exact h
  -- ## 3. `α` as a function of the ratio: Lipschitz + ratio difference
  have hstep : |Work.BoseB7.alphaCoef (E.A p) (E.B p)
        - Work.BoseB7.alphaCoef (E.A q) (E.B q)|
      ≤ 4 * (|E.B p - E.B q| / M + FM * |E.A p - E.A q| / M) := by
    have h := alpha_ratio_est (Ap := E.A p) (Aq := E.A q) (Bp := E.B p) (Bq := E.B q)
      hAp hAq (hAB p hp) (hAB q hq)
    rw [← hM_def, ← hFM_def] at h
    exact h
  -- ## 4. the three pieces of the right-hand side
  have hBdiff : |E.B p - E.B q| ≤ E.rho * (Cg * E.aScat) * d := by
    rw [hB p, hB q, ← mul_sub, abs_mul, abs_of_nonneg hrho0]
    calc E.rho * |E.W1 p - E.W1 q| ≤ E.rho * (Cg * E.aScat * d) :=
          mul_le_mul_of_nonneg_left hW1grad_pq hrho0
      _ = E.rho * (Cg * E.aScat) * d := by ring
  have hBd_nn : 0 ≤ E.rho * (Cg * E.aScat) * d :=
    mul_nonneg (mul_nonneg hrho0 (mul_nonneg hCg ha.le)) hd0
  have htermA : |E.B p - E.B q| / M ≤ 32 * s ^ 2 * (E.rho * (Cg * E.aScat)) * d := by
    rw [div_eq_mul_one_div]
    calc |E.B p - E.B q| * (1 / M)
        ≤ (E.rho * (Cg * E.aScat) * d) * (1 / M) :=
          mul_le_mul_of_nonneg_right hBdiff (div_nonneg zero_le_one hM_nn)
      _ ≤ (E.rho * (Cg * E.aScat) * d) * (32 * s ^ 2) :=
          mul_le_mul_of_nonneg_left hMinv hBd_nn
      _ = 32 * s ^ 2 * (E.rho * (Cg * E.aScat)) * d := by ring
  have hAdiff : |E.A p - E.A q| ≤ |E.tau p - E.tau q| + E.rho * |E.W1 p - E.W1 q| := by
    have h1 : E.A p - E.A q = (E.tau p - E.tau q) + E.rho * (E.W1 p - E.W1 q) := by
      rw [hA p, hA q]; ring
    rw [h1]
    calc |(E.tau p - E.tau q) + E.rho * (E.W1 p - E.W1 q)|
        ≤ |E.tau p - E.tau q| + |E.rho * (E.W1 p - E.W1 q)| := abs_add_le _ _
      _ = |E.tau p - E.tau q| + E.rho * |E.W1 p - E.W1 q| := by
          rw [abs_mul, abs_of_nonneg hrho0]
  have hRlb : 1 / (4 * s) ≤ R := by
    rw [hR_def]
    have hpR : 1 / (4 * s) ≤ ‖F.kmom p‖ := by
      have h := hp
      simp only [Work.BoseB7.FockData.PHq] at h
      have h4 : 4 * s = 4 * E.KH * E.aScat := by rw [hs_def]; ring
      rwa [h4]
    exact le_trans hpR (le_max_left _ _)
  have hRpos : 0 < R := by
    have h4s : 0 < 4 * s := by linarith
    have hpos : 0 < 1 / (4 * s) := one_div_pos.mpr h4s
    linarith
  have hR2pos : 0 < R ^ 2 := pow_pos hRpos 2
  have hM_le_R2 : 1 / M ≤ 2 / R ^ 2 := by
    have hp2 : ‖F.kmom p‖ ^ 2 / 2 ≤ E.A p := hAge p hp
    have hq2 : ‖F.kmom q‖ ^ 2 / 2 ≤ E.A q := hAge q hq
    have hMp : ‖F.kmom p‖ ^ 2 / 2 ≤ M := by
      rw [hM_def]; exact le_trans hp2 (le_max_left _ _)
    have hMq : ‖F.kmom q‖ ^ 2 / 2 ≤ M := by
      rw [hM_def]; exact le_trans hq2 (le_max_right _ _)
    rw [div_le_div_iff₀ hM_pos hR2pos]
    rw [hR_def]
    rcases le_total ‖F.kmom p‖ ‖F.kmom q‖ with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hInvR : 1 / R ≤ 4 * s := by rw [hR_def]; exact hInvR0 p q hp hq
  have htauR : |E.tau p - E.tau q| ≤ 2 * Cτ * R * d := by
    have h2 : ‖F.kmom p‖ + ‖F.kmom q‖ ≤ 2 * R := by
      rw [hR_def]
      have h1 := le_max_left (‖F.kmom p‖) (‖F.kmom q‖)
      have h3 := le_max_right (‖F.kmom p‖) (‖F.kmom q‖)
      linarith
    calc |E.tau p - E.tau q| ≤ Cτ * (‖F.kmom p‖ + ‖F.kmom q‖) * d := htau_grad_pq
      _ ≤ Cτ * (2 * R) * d := by
          refine mul_le_mul_of_nonneg_right ?_ hd0
          exact mul_le_mul_of_nonneg_left h2 hCτ
      _ = 2 * Cτ * R * d := by ring
  have hcoef1_nn : 0 ≤ 32 * s ^ 2 * (E.rho * (Cw * E.aScat)) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg s)) (mul_nonneg hrho0 hCwa)
  have hTauR_nn : 0 ≤ 2 * Cτ * R * d :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCτ) hRpos.le) hd0
  have hterm_tau : FM * |E.tau p - E.tau q| / M ≤
      512 * E.rho * (Cw * E.aScat) * Cτ * s ^ 3 * d := by
    calc FM * |E.tau p - E.tau q| / M
        = FM * |E.tau p - E.tau q| * (1 / M) := by ring
      _ ≤ (32 * s ^ 2 * (E.rho * (Cw * E.aScat))) * (2 * Cτ * R * d) * (1 / M) := by
          refine mul_le_mul_of_nonneg_right ?_ (div_nonneg zero_le_one hM_nn)
          exact mul_le_mul hFM_le htauR (abs_nonneg _) hcoef1_nn
      _ ≤ (32 * s ^ 2 * (E.rho * (Cw * E.aScat))) * (2 * Cτ * R * d) * (2 / R ^ 2) := by
          refine mul_le_mul_of_nonneg_left hM_le_R2 ?_
          exact mul_nonneg hcoef1_nn hTauR_nn
      _ = 128 * s ^ 2 * (E.rho * (Cw * E.aScat)) * Cτ * d * (1 / R) := by
          field_simp
          ring
      _ ≤ 128 * s ^ 2 * (E.rho * (Cw * E.aScat)) * Cτ * d * (4 * s) := by
          refine mul_le_mul_of_nonneg_left hInvR ?_
          exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
            (sq_nonneg s)) (mul_nonneg hrho0 hCwa)) hCτ) hd0
      _ = 512 * E.rho * (Cw * E.aScat) * Cτ * s ^ 3 * d := by ring
  have hW1diff : E.rho * |E.W1 p - E.W1 q| ≤ E.rho * (Cg * E.aScat) * d := by
    calc E.rho * |E.W1 p - E.W1 q| ≤ E.rho * (Cg * E.aScat * d) :=
          mul_le_mul_of_nonneg_left hW1grad_pq hrho0
      _ = E.rho * (Cg * E.aScat) * d := by ring
  have hterm_W : FM * (E.rho * |E.W1 p - E.W1 q|) / M ≤
      16 * s ^ 2 * (E.rho * (Cg * E.aScat)) * d := by
    have h2nn : 0 ≤ E.rho * |E.W1 p - E.W1 q| := mul_nonneg hrho0 (abs_nonneg _)
    calc FM * (E.rho * |E.W1 p - E.W1 q|) / M
        = FM * (E.rho * |E.W1 p - E.W1 q|) * (1 / M) := by ring
      _ ≤ (1 / 2) * (E.rho * (Cg * E.aScat) * d) * (32 * s ^ 2) := by
          refine mul_le_mul (mul_le_mul hFM_half hW1diff h2nn (by norm_num)) hMinv
            (div_nonneg zero_le_one hM_nn) (mul_nonneg (by norm_num) hBd_nn)
      _ = 16 * s ^ 2 * (E.rho * (Cg * E.aScat)) * d := by ring
  have hFMdA : FM * |E.A p - E.A q| / M ≤
      512 * E.rho * (Cw * E.aScat) * Cτ * s ^ 3 * d
        + 16 * s ^ 2 * (E.rho * (Cg * E.aScat)) * d := by
    calc FM * |E.A p - E.A q| / M
        ≤ FM * (|E.tau p - E.tau q| + E.rho * |E.W1 p - E.W1 q|) / M :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hAdiff hFM_nn) hM_pos.le
      _ = FM * |E.tau p - E.tau q| / M + FM * (E.rho * |E.W1 p - E.W1 q|) / M := by ring
      _ ≤ 512 * E.rho * (Cw * E.aScat) * Cτ * s ^ 3 * d
            + 16 * s ^ 2 * (E.rho * (Cg * E.aScat)) * d := add_le_add hterm_tau hterm_W
  -- ## 5. assembly
  have hmain : |E.alpha p - E.alpha q| ≤
      (192 * E.rho * Cg * E.aScat * s ^ 2 + 2048 * E.rho * Cw * E.aScat * Cτ * s ^ 3) * d := by
    have hαeq : E.alpha p - E.alpha q =
        Work.BoseB7.alphaCoef (E.A p) (E.B p) - Work.BoseB7.alphaCoef (E.A q) (E.B q) := by
      simp only [Work.BoseB7.Q3Env.alpha]
    rw [hαeq]
    calc |Work.BoseB7.alphaCoef (E.A p) (E.B p) - Work.BoseB7.alphaCoef (E.A q) (E.B q)|
        ≤ 4 * (|E.B p - E.B q| / M + FM * |E.A p - E.A q| / M) := hstep
      _ ≤ 4 * (32 * s ^ 2 * (E.rho * (Cg * E.aScat)) * d
            + (512 * E.rho * (Cw * E.aScat) * Cτ * s ^ 3 * d
              + 16 * s ^ 2 * (E.rho * (Cg * E.aScat)) * d)) := by
          have h := add_le_add htermA hFMdA
          linarith
      _ = (192 * E.rho * Cg * E.aScat * s ^ 2
            + 2048 * E.rho * Cw * E.aScat * Cτ * s ^ 3) * d := by ring
  -- ## 6. the arithmetic of the constant
  have harith := arith_lip2 (Cw := Cw) (Cg := Cg) (Cτ := Cτ) (cτ := cτ) (ρ := E.rho)
    (μ := E.mu) (a := E.aScat) (KH := E.KH) hCw hCg hCτ hcτ ha hKH hmu0 hrho0 hrho hs1
  calc |E.alpha p - E.alpha q|
      ≤ (192 * E.rho * Cg * E.aScat * s ^ 2
          + 2048 * E.rho * Cw * E.aScat * Cτ * s ^ 3) * d := hmain
    _ ≤ (10 ^ 12 * (Cw + Cg + Cτ + 1) ^ 4 * (1 + 1 / cτ) ^ 4
          * (1 + 1 / E.aScat) ^ 4 * (E.mu * E.aScat ^ 3 * E.KH ^ 2) * s) * d :=
        mul_le_mul_of_nonneg_right harith hd0
    _ = 10 ^ 12 * (Cw + Cg + Cτ + 1) ^ 4 * (1 + 1 / cτ) ^ 4
          * (1 + 1 / E.aScat) ^ 4 * E.lille * s * d := by rw [hlille]
    _ = 10 ^ 12 * (Cw + Cg + Cτ + 1) ^ 4 * (1 + 1 / cτ) ^ 4 * (1 + 1 / E.aScat) ^ 4
          * E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖ := by
        simp only [hs_def, hd_def]

end Work.BoseGateFS
