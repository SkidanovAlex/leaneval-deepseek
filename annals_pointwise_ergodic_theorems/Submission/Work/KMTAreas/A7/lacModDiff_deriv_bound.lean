/-
# Mikhlin bound for the first derivative of the lacunary modulated difference symbol

For a `Lam`-lacunary scale sequence `σ` (`σ (n+1) ≥ Lam σ n`, `Lam > 1`), a modulation `λ` with
`|λ n| ≤ cbar · σ n`, arbitrary coefficients `‖ε n‖ ≤ 1`, and a bump `Φ` vanishing off `[-1,1]`
together with its derivative, the symbol

  `ξ ↦ ∑_{n < K} ε n · (modBlockD Φ (σ (n+1)) (λ (n+1)) ξ - modBlockD Φ (σ n) (λ n) ξ)`

satisfies the Mikhlin-type estimate `|ξ| · ‖·‖ ≤ C (1 + cbar)^2` with a constant `C` depending
only on `Lam`, `M0 = sup ‖Φ‖` and `M1 = sup ‖Φ'‖` -- uniformly in the number of terms `K`, the
signs `ε`, the frequency `ξ` and the parameters.

The mechanism is the one of `Work.KMTAreas.A7.lacunarySum_norm_bound`.  Each single block
derivative `modBlockD Φ (σ m) (λ m) ξ` is bounded by `(M1 + 2π cbar M0) σ m`, and it *vanishes*
as soon as `1 < σ m · |ξ|`.  Hence, after the triangle inequality (which costs a factor `2`,
because the summands are consecutive differences), the sum to be bounded is
`∑_{σ m |ξ| ≤ 1} |ξ| σ m`, which lacunarity turns into the geometric series
`2 / (1 - Lam⁻¹)`.  No flatness of `Φ` near the origin and no use of the increments
`|λ (n+1) - λ n| ≤ cbar σ n` is needed for this first-derivative estimate.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacModDiffDefs

set_option autoImplicit false

namespace Work.KMTAreas.A7

open scoped BigOperators
open Finset

noncomputable section

private lemma norm_two_pi_I_mul_real' (a : ℝ) :
    ‖(2 * Real.pi * Complex.I * (a : ℂ) : ℂ)‖ = 2 * Real.pi * |a| := by
  have h : (2 * Real.pi * Complex.I * (a : ℂ) : ℂ) = Complex.I * ((2 * Real.pi * a : ℝ) : ℂ) := by
    push_cast; ring
  rw [h, Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0:ℝ) < 2)]

private lemma modBlockD_norm_bound' {M0 M1 cbar : ℝ} (hM0 : 0 ≤ M0) (_hM1 : 0 ≤ M1)
    (_hcbar : 0 ≤ cbar) {Φ : ℝ → ℂ} (hΦb : ∀ u : ℝ, ‖Φ u‖ ≤ M0)
    (hΦdb : ∀ u : ℝ, ‖deriv Φ u‖ ≤ M1) {sigma lam : ℕ → ℝ} (hpos : ∀ n, 0 < sigma n)
    (hlam : ∀ n, |lam n| ≤ cbar * sigma n) (ξ : ℝ) (m : ℕ) :
    ‖modBlockD Φ (sigma m) (lam m) ξ‖ ≤ (M1 + 2 * Real.pi * cbar * M0) * sigma m := by
  have hs : 0 < sigma m := hpos m
  have h1 : ‖(sigma m : ℂ) * deriv Φ (sigma m * ξ) * ee (lam m * ξ)‖ ≤ M1 * sigma m := by
    calc ‖(sigma m : ℂ) * deriv Φ (sigma m * ξ) * ee (lam m * ξ)‖
        ≤ ‖(sigma m : ℂ) * deriv Φ (sigma m * ξ)‖ * ‖ee (lam m * ξ)‖ := norm_mul_le _ _
      _ ≤ (‖(sigma m : ℂ)‖ * ‖deriv Φ (sigma m * ξ)‖) * ‖ee (lam m * ξ)‖ := by
          have h := norm_mul_le (sigma m : ℂ) (deriv Φ (sigma m * ξ))
          have h2 : (0:ℝ) ≤ ‖ee (lam m * ξ)‖ := norm_nonneg _
          nlinarith [norm_nonneg ((sigma m : ℂ) * deriv Φ (sigma m * ξ))]
      _ ≤ (sigma m * M1) * 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, norm_ee_eq_one]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hΦdb _) hs.le) (by norm_num)
      _ = M1 * sigma m := by ring
  have h2 : ‖Φ (sigma m * ξ) * (2 * Real.pi * Complex.I * (lam m : ℂ) * ee (lam m * ξ))‖
      ≤ 2 * Real.pi * cbar * M0 * sigma m := by
    calc ‖Φ (sigma m * ξ) * (2 * Real.pi * Complex.I * (lam m : ℂ) * ee (lam m * ξ))‖
        ≤ ‖Φ (sigma m * ξ)‖ * ‖(2 * Real.pi * Complex.I * (lam m : ℂ)) * ee (lam m * ξ)‖ :=
          norm_mul_le _ _
      _ ≤ M0 * ((2 * Real.pi * |lam m|) * 1) := by
          apply mul_le_mul (hΦb _) _ (norm_nonneg _) hM0
          calc ‖(2 * Real.pi * Complex.I * (lam m : ℂ)) * ee (lam m * ξ)‖
              ≤ ‖(2 * Real.pi * Complex.I * (lam m : ℂ) : ℂ)‖ * ‖ee (lam m * ξ)‖ := norm_mul_le _ _
            _ = (2 * Real.pi * |lam m|) * 1 := by
                rw [norm_two_pi_I_mul_real', norm_ee_eq_one]
      _ ≤ M0 * ((2 * Real.pi * (cbar * sigma m)) * 1) := by
          apply mul_le_mul_of_nonneg_left _ hM0
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          exact mul_le_mul_of_nonneg_left (hlam m) (by positivity)
      _ = 2 * Real.pi * cbar * M0 * sigma m := by ring
  have hlong : ‖(sigma m : ℂ) * deriv Φ (sigma m * ξ) * ee (lam m * ξ)
      + Φ (sigma m * ξ) * (2 * Real.pi * Complex.I * (lam m : ℂ) * ee (lam m * ξ))‖
      ≤ (M1 + 2 * Real.pi * cbar * M0) * sigma m := by
    have h := norm_add_le ((sigma m : ℂ) * deriv Φ (sigma m * ξ) * ee (lam m * ξ))
      (Φ (sigma m * ξ) * (2 * Real.pi * Complex.I * (lam m : ℂ) * ee (lam m * ξ)))
    linarith [h1, h2, h]
  simpa only [modBlockD] using hlong

private lemma modBlockD_eq_zero' {Φ : ℝ → ℂ}
    (hΦsupp : ∀ u : ℝ, 1 ≤ |u| → Φ u = 0) (hΦdsupp : ∀ u : ℝ, 1 ≤ |u| → deriv Φ u = 0)
    {sigma lam : ℕ → ℝ} (hpos : ∀ n, 0 < sigma n) (ξ : ℝ) (m : ℕ)
    (h : 1 < sigma m * |ξ|) : modBlockD Φ (sigma m) (lam m) ξ = 0 := by
  have hs : 0 < sigma m := hpos m
  have h1 : 1 ≤ |sigma m * ξ| := by
    rw [abs_mul, abs_of_pos hs]; exact h.le
  rw [modBlockD, hΦdsupp (sigma m * ξ) h1, hΦsupp (sigma m * ξ) h1]
  ring

theorem lacModDiff_deriv_bound {Lam M0 M1 : ℝ} (hLam : 1 < Lam) (hM0 : 0 ≤ M0)
    (hM1 : 0 ≤ M1) {Φ : ℝ → ℂ} (hΦb : ∀ u : ℝ, ‖Φ u‖ ≤ M0)
    (hΦsupp : ∀ u : ℝ, 1 ≤ |u| → Φ u = 0) (hΦdb : ∀ u : ℝ, ‖deriv Φ u‖ ≤ M1)
    (hΦdsupp : ∀ u : ℝ, 1 ≤ |u| → deriv Φ u = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {cbar : ℝ}, 0 ≤ cbar →
      ∀ {sigma : ℕ → ℝ}, (∀ n : ℕ, 0 < sigma n) →
        (∀ n : ℕ, Lam * sigma n ≤ sigma (n + 1)) →
      ∀ {lam : ℕ → ℝ}, (∀ n : ℕ, |lam n| ≤ cbar * sigma n) →
        (∀ n : ℕ, |lam (n + 1) - lam n| ≤ cbar * sigma n) →
      ∀ (K : ℕ) (eps : ℕ → ℂ), (∀ n : ℕ, ‖eps n‖ ≤ 1) → ∀ ξ : ℝ,
        |ξ| * ‖∑ n ∈ Finset.range K, eps n * (modBlockD Φ (sigma (n + 1)) (lam (n + 1)) ξ
          - modBlockD Φ (sigma n) (lam n) ξ)‖ ≤ C * (1 + cbar) ^ 2 := by
  have hKpos : 0 < 1 - Lam⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hLam)
  have hCnn : 0 ≤ 4 * (M1 + 2 * Real.pi * M0) / (1 - Lam⁻¹) :=
    div_nonneg (by positivity) hKpos.le
  refine ⟨4 * (M1 + 2 * Real.pi * M0) / (1 - Lam⁻¹), hCnn, ?_⟩
  intro cbar hcbar sigma hpos hstep lam hlam hlamd K eps heps ξ
  set C0 : ℝ := M1 + 2 * Real.pi * cbar * M0 with hC0def
  have hC0nn : 0 ≤ C0 := by
    rw [hC0def]
    exact add_nonneg hM1 (mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi) hcbar) hM0)
  set F : ℕ → ℂ := fun m => modBlockD Φ (sigma m) (lam m) ξ with hF
  have hFeq : ∀ m : ℕ, F m = modBlockD Φ (sigma m) (lam m) ξ := fun m => by simp only [hF]
  have hFa : ∀ m : ℕ, ‖F m‖ ≤ C0 * sigma m := by
    intro m
    rw [hFeq m, hC0def]
    exact modBlockD_norm_bound' hM0 hM1 hcbar hΦb hΦdb hpos hlam ξ m
  have hFz : ∀ m : ℕ, 1 < sigma m * |ξ| → F m = 0 := by
    intro m h
    rw [hFeq m]
    exact modBlockD_eq_zero' hΦsupp hΦdsupp hpos ξ m h
  have hsumrewrite : (∑ n ∈ Finset.range K, eps n * (modBlockD Φ (sigma (n + 1)) (lam (n + 1)) ξ
        - modBlockD Φ (sigma n) (lam n) ξ))
      = ∑ n ∈ Finset.range K, eps n * (F (n + 1) - F n) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [hFeq (n + 1), hFeq n]
  rw [hsumrewrite]
  by_cases hξ : ξ = 0
  · rw [hξ, abs_zero, zero_mul]
    exact mul_nonneg hCnn (sq_nonneg _)
  · have hxi_norm : ‖((|ξ| : ℝ) : ℂ)‖ = |ξ| := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (abs_nonneg ξ)]
    have hB : (∑ m ∈ Finset.range (K + 1), ‖((|ξ| : ℝ) : ℂ) * F m‖) ≤ 2 * C0 / (1 - Lam⁻¹) := by
      refine lacunarySum_norm_bound (D := Finset.range (K + 1)) (σ := sigma)
        (f := fun m => ((|ξ| : ℝ) : ℂ) * F m) (C := C0) hLam ?_ hξ hC0nn ?_ ?_
      · exact lacunaryFam_range hLam hpos hstep (K + 1)
      · intro m _ hle
        calc ‖((|ξ| : ℝ) : ℂ) * F m‖ = |ξ| * ‖F m‖ := by rw [norm_mul, hxi_norm]
          _ ≤ |ξ| * (C0 * sigma m) := mul_le_mul_of_nonneg_left (hFa m) (abs_nonneg ξ)
          _ = C0 * (sigma m * |ξ|) := by ring
      · intro m _ hgt
        rw [hFz m hgt, mul_zero]
    have hN : ‖∑ n ∈ Finset.range K, eps n * (F (n + 1) - F n)‖
        ≤ 2 * ∑ m ∈ Finset.range (K + 1), ‖F m‖ := by
      calc ‖∑ n ∈ Finset.range K, eps n * (F (n + 1) - F n)‖
          ≤ ∑ n ∈ Finset.range K, ‖eps n * (F (n + 1) - F n)‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.range K, ‖F (n + 1) - F n‖ := by
            apply Finset.sum_le_sum
            intro n _
            calc ‖eps n * (F (n + 1) - F n)‖ ≤ ‖eps n‖ * ‖F (n + 1) - F n‖ := norm_mul_le _ _
              _ ≤ 1 * ‖F (n + 1) - F n‖ := mul_le_mul_of_nonneg_right (heps n) (norm_nonneg _)
              _ = ‖F (n + 1) - F n‖ := one_mul _
        _ ≤ ∑ n ∈ Finset.range K, (‖F (n + 1)‖ + ‖F n‖) := by
            apply Finset.sum_le_sum
            intro n _
            exact norm_sub_le _ _
        _ = ∑ n ∈ Finset.range K, ‖F (n + 1)‖ + ∑ n ∈ Finset.range K, ‖F n‖ :=
            Finset.sum_add_distrib
        _ ≤ 2 * ∑ m ∈ Finset.range (K + 1), ‖F m‖ := by
            have h1 : ∑ n ∈ Finset.range K, ‖F (n + 1)‖ ≤ ∑ m ∈ Finset.range (K + 1), ‖F m‖ := by
              have hsr := Finset.sum_range_succ' (fun m : ℕ => ‖F m‖) K
              have h0 := norm_nonneg (F 0)
              linarith [hsr]
            have h2 : ∑ n ∈ Finset.range K, ‖F n‖ ≤ ∑ m ∈ Finset.range (K + 1), ‖F m‖ :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ K))
                (fun i _ _ => norm_nonneg (F i))
            linarith [h1, h2]
    have hsum_eq : (∑ m ∈ Finset.range (K + 1), ‖((|ξ| : ℝ) : ℂ) * F m‖)
        = |ξ| * (∑ m ∈ Finset.range (K + 1), ‖F m‖) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by rw [norm_mul, hxi_norm])
    have hC0le : C0 ≤ (M1 + 2 * Real.pi * M0) * (1 + cbar) ^ 2 := by
      rw [hC0def]
      have h1 : (1 : ℝ) + cbar ≤ (1 + cbar) ^ 2 := by nlinarith [hcbar, sq_nonneg cbar]
      have hP0 : 0 ≤ 2 * Real.pi * M0 :=
        mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hM0
      have h2 : M1 + 2 * Real.pi * cbar * M0 ≤ (M1 + 2 * Real.pi * M0) * (1 + cbar) := by
        have hMc : 0 ≤ M1 * cbar := mul_nonneg hM1 hcbar
        have hPc : 0 ≤ 2 * Real.pi * M0 * cbar := mul_nonneg hP0 hcbar
        nlinarith [hMc, hPc, hP0]
      calc M1 + 2 * Real.pi * cbar * M0 ≤ (M1 + 2 * Real.pi * M0) * (1 + cbar) := h2
        _ ≤ (M1 + 2 * Real.pi * M0) * (1 + cbar) ^ 2 :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
    calc |ξ| * ‖∑ n ∈ Finset.range K, eps n * (F (n + 1) - F n)‖
        ≤ |ξ| * (2 * ∑ m ∈ Finset.range (K + 1), ‖F m‖) :=
          mul_le_mul_of_nonneg_left hN (abs_nonneg ξ)
      _ = 2 * (∑ m ∈ Finset.range (K + 1), ‖((|ξ| : ℝ) : ℂ) * F m‖) := by rw [hsum_eq]; ring
      _ ≤ 2 * (2 * C0 / (1 - Lam⁻¹)) := mul_le_mul_of_nonneg_left hB (by norm_num)
      _ = 4 * C0 / (1 - Lam⁻¹) := by ring
      _ ≤ 4 * (M1 + 2 * Real.pi * M0) / (1 - Lam⁻¹) * (1 + cbar) ^ 2 := by
          have h4 : 4 * C0 ≤ 4 * ((M1 + 2 * Real.pi * M0) * (1 + cbar) ^ 2) := by
            linarith [hC0le]
          calc 4 * C0 / (1 - Lam⁻¹)
              ≤ 4 * ((M1 + 2 * Real.pi * M0) * (1 + cbar) ^ 2) / (1 - Lam⁻¹) :=
                div_le_div_of_nonneg_right h4 hKpos.le
            _ = 4 * (M1 + 2 * Real.pi * M0) / (1 - Lam⁻¹) * (1 + cbar) ^ 2 := by ring
      _ = (4 * (M1 + 2 * Real.pi * M0) / (1 - Lam⁻¹)) * (1 + cbar) ^ 2 := by ring

end

end Work.KMTAreas.A7
