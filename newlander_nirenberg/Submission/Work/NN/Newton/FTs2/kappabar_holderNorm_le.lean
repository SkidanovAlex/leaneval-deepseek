import Mathlib
import Submission.Work.NN.Newton.FTdefs
import Submission.Work.NN.Newton.FTfibre.holderNorm_comp_apply_le
import Submission.Work.NN.Core.Lev.sharpCut_fderiv_bounds
import Submission.Work.NN.Core.Lev.holderNorm_one_le_of_deriv_bounds
import Submission.Work.NN.Newton.FTsharp.dbarC_bounds
import Submission.Work.NN.Newton.FTsharp.smoothTransition_deriv3_data
import Submission.Work.NN.Newton.holderNorm_one_le_of_pointwise_bounds
import Submission.Work.NN.Newton.holderNorm_one_fderiv_coeff_le
import Submission.Work.NN.Core.TelTwoDF.EstimateDefs
import Submission.Work.NN.Core.TelTwoDF.Defs

set_option maxHeartbeats 1000000

namespace Work.NN.Newton.FTs2

open scoped NNReal ENNReal ContDiff
open Set

-- GOAL: `holderNorm 1 α (kappabar (ftG δ) s) (Eset (ftG δ) s) ≤ M/δ^6` with `M` INDEPENDENT
-- of `δ`.  The true size is `O(δ^{-3})`, so the exponent 6 is deliberately generous: any bound
-- `≤ M'/λ^k` with `λ = b^2 - a^2 ≥ δ/16` and `k ≤ 6` is enough.  (`Eset (ftG δ) s` means
-- `Eset (ftG δ) (s : ℕ)`; that is the region the consumer uses.)
--
-- USEFUL IDENTITIES.  `kappabar G s z = Work.CR.Flat.dbarC (Work.NN.Core.sharpCut (G.a s) (G.b s)) (z s)`.
--
-- ROUTE (used below).
-- (0) The analytic input about the planar cutoff is the third-order Lipschitz datum
--     `‖D²φ x - D²φ y‖ ≤ C (1/(b-a)³ + 1/(b-a)²) ‖x-y‖` for `φ = sharpCut a b` (`1/2 ≤ a < b`),
--     proved in `Work.NN.Newton.FTs2.sharpCut_fderiv2_lipschitz_le4`; the first-order datum
--     `‖Dφ‖ ≤ C/(b-a)`, `‖Dφ x - Dφ y‖ ≤ C (1/(a(b-a)) + 1/(b-a)²)‖x-y‖` is
--     `Work.NN.Core.Lev.sharpCut_fderiv_bounds`.
-- (1) `Work.NN.Newton.FTsharp.dbarC_bounds` transports these to `∂̄φ = dbarC φ`, and
--     `Work.NN.Core.Lev.holderNorm_one_le_of_deriv_bounds` gives
--     `holderNorm 1 α (dbarC φ) univ ≤ ofReal (3 M₁ + 4 M₂ + M₃)` with
--     `M₁ = C₁/(b-a)`, `M₂ = C₁ (1/(a(b-a)) + 1/(b-a)²)`, `M₃ = C (1/(b-a)³ + 1/(b-a)²)`.
-- (2) The elementary arithmetic `3 M₁ + 4 M₂ + M₃ ≤ 40 (C₁ + C₂ + 1) (b/(b-a))⁴`
--     (`b ≥ 1/2`, `s = b/(b-a) ≥ 1`).
-- (3) `kappabar G s` is `dbarC φ` composed with the coordinate projection `z ↦ z s`, so
--     `Work.NN.Newton.FTfibre.holderNorm_comp_apply_le` bounds its norm on `Eset G s` by the
--     norm of `dbarC φ` on the closed ball of radius `b = G.b s`.
-- (4) `λ = b² - a² = (δ/16)(2 - 29δ/16) ≥ δ/16` for `δ ≤ 1/4`, so `b/(b-a) ≤ 16/δ` and hence
--     `(b/(b-a))⁴ ≤ 16⁴/δ⁴ ≤ 16⁴/δ⁶` as `δ ≤ 1`.

/-- The `C^{k,α}`-norm over a closed ball of positive radius is bounded by the one over all of
`ℂ`: the closed ball is a set of unique differentiability, so its within-derivatives agree with
the genuine ones and the suprema defining the norm are only extended. -/
theorem holderNorm_closedBall_le_univ' {α : ℝ} {k : ℕ} {f : ℂ → ℂ}
    (hf : ContDiff ℝ k f) {M : ℝ} (hM : 0 < M) :
    Work.CR.Flat.holderNorm k α f (Metric.closedBall (0 : ℂ) M)
      ≤ Work.CR.Flat.holderNorm k α f Set.univ := by
  have hne : (interior (Metric.closedBall (0 : ℂ) M)).Nonempty :=
    ⟨0, Metric.ball_subset_interior_closedBall (by simp [Metric.mem_ball, hM])⟩
  have hs : UniqueDiffOn ℝ (Metric.closedBall (0 : ℂ) M) := fun x hx =>
    uniqueDiffWithinAt_convex (convex_closedBall 0 M) hne (subset_closure hx)
  have ht : UniqueDiffOn ℝ (Set.univ : Set ℂ) := isOpen_univ.uniqueDiffOn
  refine Finset.sum_le_sum fun i hi => add_le_add ?_ ?_
  · refine iSup₂_le fun x hx => ?_
    have hfi : ContDiffOn ℝ (i : WithTop ℕ∞) f (Set.univ : Set ℂ) :=
      (hf.of_le (m := (i : WithTop ℕ∞)) (by exact_mod_cast (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))).contDiffOn
    rw [iteratedFDerivWithin_subset (by simp) hs ht hfi hx]
    exact Work.CR.Flat.le_iterDerivNorm i f Set.univ (by simp)
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    have hfi : ContDiffOn ℝ (i : WithTop ℕ∞) f (Set.univ : Set ℂ) :=
      (hf.of_le (m := (i : WithTop ℕ∞)) (by exact_mod_cast (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))).contDiffOn
    rw [iteratedFDerivWithin_subset (by simp) hs ht hfi hx,
      iteratedFDerivWithin_subset (by simp) hs ht hfi hy]
    exact Work.CR.Flat.le_holderSeminorm i α f Set.univ (by simp) (by simp) hxy

/-- **The `C^{1,α}`-norm of `∂̄ (sharpCut a b)` on a closed ball, with exponent `4`.**

For `1/2 ≤ a < b` and `0 < M` the `C^{1,α}`-norm of `ζ ↦ ∂̄ (sharpCut a b) ζ` on the closed
ball of radius `M` is at most `K (b/(b-a))⁴`, with `K` independent of `a`, `b`, `M`.  This is
the quantitative input needed for `kappabar`; note the exponent `4` (not the `8` of
`Work.NN.Newton.FTsharp.sharpCut_norm_le`, which is too weak for the `δ`-arithmetic), it comes
from the true order `1/(b-a)³` of that norm.

The hypothesis `hF2` is the third-order Lipschitz datum of `sharpCut a b`
(`Work.NN.Newton.FTs2.sharpCut_fderiv2_lipschitz_le4`). -/
theorem dbarC_sharpCut_holderNorm_one_le_of
    (hF2 : ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℝ), 1 / 2 ≤ a → a < b → ∀ x y : ℂ,
        ‖fderiv ℝ (fun w => fderiv ℝ (Work.NN.Core.sharpCut a b) w) x
            - fderiv ℝ (fun w => fderiv ℝ (Work.NN.Core.sharpCut a b) w) y‖
          ≤ C * (1 / (b - a) ^ 3 + 1 / (b - a) ^ 2) * ‖x - y‖)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a b M : ℝ), 1 / 2 ≤ a → a < b → 0 < M → M ≤ 4 * b →
      Work.CR.Flat.holderNorm 1 α
          (fun ζ : ℂ => Work.CR.Flat.dbarC (Work.NN.Core.sharpCut a b) ζ)
          (Metric.closedBall (0 : ℂ) M)
        ≤ ENNReal.ofReal (K * (b / (b - a)) ^ 4) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.NN.Core.Lev.sharpCut_fderiv_bounds
  obtain ⟨C₂, hC₂pos, hC₂⟩ := hF2
  refine ⟨40 * (C₁ + C₂ + 1), by positivity, ?_⟩
  intro a b M ha2 hab hMpos _
  have ha : 0 < a := lt_of_lt_of_le (by norm_num) ha2
  have hb : 0 < b := lt_trans ha hab
  have hba : 0 < b - a := by linarith
  have hb12 : (1 : ℝ) / 2 ≤ b := le_trans ha2 hab.le
  set s : ℝ := b / (b - a) with hsdef
  have hs1 : 1 ≤ s := by rw [hsdef, le_div_iff₀ hba]; linarith
  -- elementary size comparisons
  have h2b : (1 : ℝ) ≤ 2 * b := by linarith
  have h4ab : (1 : ℝ) ≤ 4 * (a * b) := by nlinarith [ha2, hb12]
  have h4b2 : (1 : ℝ) ≤ 4 * b ^ 2 := by nlinarith [h2b]
  have h8b3 : (1 : ℝ) ≤ 8 * b ^ 3 := by nlinarith [h2b]
  have h1δ : 1 / (b - a) ≤ 2 * s := by
    have heq : (2 * s) * (b - a) = 2 * b := by rw [hsdef]; field_simp
    rw [div_le_iff₀ hba, heq]; exact h2b
  have h1ad : 1 / (a * (b - a)) ≤ 4 * s := by
    have heq : (4 * s) * (a * (b - a)) = 4 * (a * b) := by rw [hsdef]; field_simp
    rw [div_le_iff₀ (mul_pos ha hba), heq]; exact h4ab
  have h1δ2 : 1 / (b - a) ^ 2 ≤ 4 * s ^ 2 := by
    have heq : (4 * s ^ 2) * (b - a) ^ 2 = 4 * b ^ 2 := by rw [hsdef]; field_simp
    rw [div_le_iff₀ (pow_pos hba 2), heq]; exact h4b2
  have h1δ3 : 1 / (b - a) ^ 3 ≤ 8 * s ^ 3 := by
    have heq : (8 * s ^ 3) * (b - a) ^ 3 = 8 * b ^ 3 := by rw [hsdef]; field_simp
    rw [div_le_iff₀ (pow_pos hba 3), heq]; exact h8b3
  have hs4 : s ≤ s ^ 4 := by
    simpa using pow_le_pow_right₀ hs1 (by norm_num : (1 : ℕ) ≤ 4)
  have hs24 : s ^ 2 ≤ s ^ 4 := pow_le_pow_right₀ hs1 (by norm_num : (2 : ℕ) ≤ 4)
  have hs34 : s ^ 3 ≤ s ^ 4 := pow_le_pow_right₀ hs1 (by norm_num : (3 : ℕ) ≤ 4)
  -- the arithmetic reduction
  have hL1 : C₁ * (1 / (b - a)) ≤ 2 * C₁ * s ^ 4 := by
    calc C₁ * (1 / (b - a)) ≤ C₁ * (2 * s) := mul_le_mul_of_nonneg_left h1δ hC₁pos.le
      _ = 2 * C₁ * s := by ring
      _ ≤ 2 * C₁ * s ^ 4 := by
          have : (0 : ℝ) ≤ 2 * C₁ := by positivity
          nlinarith [hs4, this]
  have hL2 : C₁ * (1 / (a * (b - a)) + 1 / (b - a) ^ 2) ≤ 8 * C₁ * s ^ 4 := by
    have hsum : 1 / (a * (b - a)) + 1 / (b - a) ^ 2 ≤ 8 * s ^ 4 := by
      linarith [h1ad, h1δ2, hs4, hs24]
    calc C₁ * (1 / (a * (b - a)) + 1 / (b - a) ^ 2) ≤ C₁ * (8 * s ^ 4) :=
          mul_le_mul_of_nonneg_left hsum hC₁pos.le
      _ = 8 * C₁ * s ^ 4 := by ring
  have hM3 : C₂ * (1 / (b - a) ^ 3 + 1 / (b - a) ^ 2) ≤ 12 * C₂ * s ^ 4 := by
    have hsum : 1 / (b - a) ^ 3 + 1 / (b - a) ^ 2 ≤ 12 * s ^ 4 := by
      linarith [h1δ3, h1δ2, hs34, hs24]
    calc C₂ * (1 / (b - a) ^ 3 + 1 / (b - a) ^ 2) ≤ C₂ * (12 * s ^ 4) :=
          mul_le_mul_of_nonneg_left hsum hC₂pos.le
      _ = 12 * C₂ * s ^ 4 := by ring
  have key : 3 * (C₁ * (1 / (b - a))) + 4 * (C₁ * (1 / (a * (b - a)) + 1 / (b - a) ^ 2))
        + C₂ * (1 / (b - a) ^ 3 + 1 / (b - a) ^ 2)
      ≤ 40 * (C₁ + C₂ + 1) * s ^ 4 := by
    have hmid : 3 * (C₁ * (1 / (b - a))) + 4 * (C₁ * (1 / (a * (b - a)) + 1 / (b - a) ^ 2))
        + C₂ * (1 / (b - a) ^ 3 + 1 / (b - a) ^ 2) ≤ (38 * C₁ + 12 * C₂) * s ^ 4 := by
      linarith [hL1, hL2, hM3]
    have hconst : (38 : ℝ) * C₁ + 12 * C₂ ≤ 40 * (C₁ + C₂ + 1) := by
      nlinarith [hC₁pos.le, hC₂pos.le]
    calc 3 * (C₁ * (1 / (b - a))) + 4 * (C₁ * (1 / (a * (b - a)) + 1 / (b - a) ^ 2))
          + C₂ * (1 / (b - a) ^ 3 + 1 / (b - a) ^ 2)
        ≤ (38 * C₁ + 12 * C₂) * s ^ 4 := hmid
      _ ≤ 40 * (C₁ + C₂ + 1) * s ^ 4 := mul_le_mul_of_nonneg_right hconst (by positivity)
  -- the analytic transfer to `∂̄` of the cutoff
  have hM1nn : 0 ≤ C₁ * (1 / (b - a)) := by positivity
  have hM2nn : 0 ≤ C₁ * (1 / (a * (b - a)) + 1 / (b - a) ^ 2) := by positivity
  have hM3nn : 0 ≤ C₂ * (1 / (b - a) ^ 3 + 1 / (b - a) ^ 2) := by positivity
  have hfcd2 : ContDiff ℝ 2 (Work.NN.Core.sharpCut a b) :=
    (Work.NN.Core.contDiff_sharpCut (a := a) (b := b)).of_le (by simp)
  obtain ⟨hF1, -, hF3⟩ := hC₁ a b ha hab
  obtain ⟨hgcd, hg1, hg2, hg3⟩ := Work.NN.Newton.FTsharp.dbarC_bounds hfcd2 hM1nn hM2nn hM3nn
    (fun z => hF1 z) (fun z w => hF3 z w) (fun z w => hC₂ a b ha2 hab z w)
  have hnorm : Work.CR.Flat.holderNorm 1 α
        (fun ζ : ℂ => Work.CR.Flat.dbarC (Work.NN.Core.sharpCut a b) ζ) Set.univ
      ≤ ENNReal.ofReal (3 * (C₁ * (1 / (b - a)))
          + 4 * (C₁ * (1 / (a * (b - a)) + 1 / (b - a) ^ 2))
          + C₂ * (1 / (b - a) ^ 3 + 1 / (b - a) ^ 2)) :=
    Work.NN.Core.Lev.holderNorm_one_le_of_deriv_bounds isOpen_univ convex_univ hα0 hα1 hgcd
      hM1nn hM2nn hM3nn (fun z _ => hg1 z) (fun z _ => hg2 z) (fun z _ w _ => hg3 z w)
  have hball : Work.CR.Flat.holderNorm 1 α
        (fun ζ : ℂ => Work.CR.Flat.dbarC (Work.NN.Core.sharpCut a b) ζ) (Metric.closedBall (0 : ℂ) M)
      ≤ Work.CR.Flat.holderNorm 1 α
        (fun ζ : ℂ => Work.CR.Flat.dbarC (Work.NN.Core.sharpCut a b) ζ) Set.univ :=
    holderNorm_closedBall_le_univ' hgcd hMpos
  exact le_trans (le_trans hball hnorm) (ENNReal.ofReal_le_ofReal key)

/-- `kappabar G s` is the planar `∂̄` of the cutoff in the coordinate `s`, composed with the
coordinate projection `z ↦ z s`; hence its `C^{1,α}`-norm on the tracking polydisc `Eset G s`
is bounded by the one of that planar function on the closed ball of radius `G.b s`. -/
theorem holderNorm_kappabar_le_sharpCut {n : ℕ} (G : Work.NN.Core.TelTwoDF.Geom n) (s : Fin n)
    {α : ℝ} (hα : 0 ≤ α) :
    Work.CR.Flat.holderNorm 1 α (Work.NN.Core.TelTwoDF.kappabar G s)
        (Work.NN.Core.TelTwoDF.Eset G s)
      ≤ Work.CR.Flat.holderNorm 1 α
          (fun ζ : ℂ => Work.CR.Flat.dbarC (Work.NN.Core.sharpCut (G.a s) (G.b s)) ζ)
          (Metric.closedBall (0 : ℂ) (G.b s)) := by
  have hQ : ∀ j : Fin n, 0 < Work.NN.Core.TelTwoDF.Erad G s j := by
    intro j
    by_cases h : (j : ℕ) < s <;>
      simp [Work.NN.Core.TelTwoDF.Erad, h, G.he j, G.b_pos j]
  have hQR : Work.NN.Core.TelTwoDF.Erad G s s ≤ G.b s := Work.NN.Core.TelTwoDF.Erad_le_b G s s
  have hf : ContDiff ℝ 1
      (fun ζ : ℂ => Work.CR.Flat.dbarC (Work.NN.Core.sharpCut (G.a s) (G.b s)) ζ) :=
    (Work.NN.Core.TelTwoDF.contDiff_dbarC_sharpCut_aux (a := G.a s) (b := G.b s)).of_le (by simp)
  have hmain := Work.NN.Newton.FTfibre.holderNorm_comp_apply_le (α := α) (k := 1) s
    (Q := Work.NN.Core.TelTwoDF.Erad G s) (R := G.b s) hQR hQ hf hα
  exact hmain

/-- **The `δ`-uniform bound for `kappabar`, conditional on the third-order Lipschitz datum of
the planar cutoff.** -/
theorem kappabar_holderNorm_le_of_child {n : ℕ} {α : ℝ}
    (hF2 : ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℝ), 1 / 2 ≤ a → a < b → ∀ x y : ℂ,
        ‖fderiv ℝ (fun w => fderiv ℝ (Work.NN.Core.sharpCut a b) w) x
            - fderiv ℝ (fun w => fderiv ℝ (Work.NN.Core.sharpCut a b) w) y‖
          ≤ C * (1 / (b - a) ^ 3 + 1 / (b - a) ^ 2) * ‖x - y‖)
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) (s : Fin n),
      Work.CR.Flat.holderNorm 1 α
          (Work.NN.Core.TelTwoDF.kappabar (Work.NN.Newton.ftG (n := n) δ hδ0 hδ4) s)
          (Work.NN.Core.TelTwoDF.Eset (Work.NN.Newton.ftG (n := n) δ hδ0 hδ4) s)
        ≤ ENNReal.ofReal (M / δ ^ 6) := by
  obtain ⟨K, hKpos, hK⟩ := dbarC_sharpCut_holderNorm_one_le_of hF2 hα0 hα1
  refine ⟨65536 * K, by positivity, ?_⟩
  intro δ hδ0 hδ4 s
  set G : Work.NN.Core.TelTwoDF.Geom n := Work.NN.Newton.ftG (n := n) δ hδ0 hδ4 with hG
  have ha_eq : G.a s = 1 - 15 * δ / 16 := by
    rw [hG]; exact Work.NN.Newton.ftG_a δ hδ0 hδ4 s
  have hb_eq : G.b s = 1 - 7 * δ / 8 := by
    rw [hG]; exact Work.NN.Newton.ftG_b δ hδ0 hδ4 s
  have hba_eq : G.b s - G.a s = δ / 16 := by rw [ha_eq, hb_eq]; ring
  have hbpos : 0 < G.b s := by rw [hb_eq]; linarith
  have ha2 : 1 / 2 ≤ G.a s := by rw [ha_eq]; linarith
  have hab : G.a s < G.b s := by rw [ha_eq, hb_eq]; linarith
  have hb4 : G.b s ≤ 4 * G.b s := by linarith
  -- the two inputs: composition with the projection, and the planar bound
  have hcomp := holderNorm_kappabar_le_sharpCut G s hα0.le
  have hS := hK (G.a s) (G.b s) (G.b s) ha2 hab hbpos hb4
  -- the `δ`-geometry
  have harith : K * (G.b s / (G.b s - G.a s)) ^ 4 ≤ 65536 * K / δ ^ 6 := by
    have hδ1 : δ ≤ 1 := by linarith
    have hsq : δ ^ 2 ≤ 1 := by nlinarith [hδ0.le, hδ1]
    have hden : 0 < G.b s - G.a s := by rw [hba_eq]; positivity
    have hb1 : G.b s ≤ 1 := by rw [hb_eq]; linarith
    have hratio : G.b s / (G.b s - G.a s) ≤ 16 / δ := by
      have h2 : (1 : ℝ) / (G.b s - G.a s) = 16 / δ := by rw [hba_eq, one_div_div]
      rw [← h2]
      exact div_le_div_of_nonneg_right hb1 hden.le
    have hratio_nonneg : 0 ≤ G.b s / (G.b s - G.a s) := div_nonneg hbpos.le hden.le
    have h4 : (G.b s / (G.b s - G.a s)) ^ 4 ≤ (16 / δ) ^ 4 :=
      pow_le_pow_left₀ hratio_nonneg hratio 4
    have h5 : (16 / δ) ^ 4 = 65536 / δ ^ 4 := by rw [div_pow]; norm_num
    have h6 : (65536 : ℝ) / δ ^ 4 ≤ 65536 / δ ^ 6 := by
      have hle : δ ^ 6 ≤ δ ^ 4 := by
        have h : δ ^ 4 * δ ^ 2 ≤ δ ^ 4 * 1 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        nlinarith [h]
      have h7 : (1 : ℝ) / δ ^ 4 ≤ 1 / δ ^ 6 :=
        one_div_le_one_div_of_le (by positivity) hle
      calc (65536 : ℝ) / δ ^ 4 = 65536 * (1 / δ ^ 4) := by ring
        _ ≤ 65536 * (1 / δ ^ 6) := mul_le_mul_of_nonneg_left h7 (by norm_num)
        _ = 65536 / δ ^ 6 := by ring
    calc K * (G.b s / (G.b s - G.a s)) ^ 4 ≤ K * (16 / δ) ^ 4 :=
          mul_le_mul_of_nonneg_left h4 hKpos.le
      _ = K * (65536 / δ ^ 4) := by rw [h5]
      _ = 65536 * K / δ ^ 4 := by ring
      _ ≤ 65536 * K / δ ^ 6 := by
          calc 65536 * K / δ ^ 4 = K * (65536 / δ ^ 4) := by ring
            _ ≤ K * (65536 / δ ^ 6) := mul_le_mul_of_nonneg_left h6 hKpos.le
            _ = 65536 * K / δ ^ 6 := by ring
  exact le_trans (le_trans hcomp hS) (ENNReal.ofReal_le_ofReal harith)


/-! ## The chain-rule data of the one-variable radial profile `sharpCutReal a b` -/

/-- The one-variable profile `χ = sharpCutReal a b = σ ∘ ((b²-·)/(b²-a²))` (`σ` the smooth
transition) has all three derivatives bounded by `Cₖ/(b²-a²)^k`, and each of the first two
derivatives is again differentiable with the expected derivative.  This is the input for the
radial composition computation below. -/
theorem sharpCutReal_deriv_data_aux :
    ∃ C₁ C₂ C₃ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧
      ∀ (a b : ℝ), 0 ≤ a → a < b →
        (∀ u : ℝ, |deriv (Work.NN.Core.sharpCutReal a b) u| ≤ C₁ / (b ^ 2 - a ^ 2)) ∧
        (∀ u : ℝ, HasDerivAt (deriv (Work.NN.Core.sharpCutReal a b))
            (deriv (deriv (Work.NN.Core.sharpCutReal a b)) u) u) ∧
        (∀ u : ℝ, |deriv (deriv (Work.NN.Core.sharpCutReal a b)) u|
            ≤ C₂ / (b ^ 2 - a ^ 2) ^ 2) ∧
        (∀ u : ℝ, HasDerivAt (deriv (deriv (Work.NN.Core.sharpCutReal a b)))
            (deriv (deriv (deriv (Work.NN.Core.sharpCutReal a b))) u) u) ∧
        (∀ u : ℝ, |deriv (deriv (deriv (Work.NN.Core.sharpCutReal a b))) u|
            ≤ C₃ / (b ^ 2 - a ^ 2) ^ 3) := by
  obtain ⟨C₁, C₂, hC₁0, hC₂0, hC₁, hC₂, -, -⟩ := Work.NN.Core.Lev.smoothTransition_deriv_bounds
  obtain ⟨C₃, hC₃0, hC₃, -, -⟩ := Work.NN.Newton.FTsharp.smoothTransition_deriv3_data
  refine ⟨C₁, C₂, C₃, hC₁0, hC₂0, hC₃0, ?_⟩
  intro a b ha hab
  set lam : ℝ := b ^ 2 - a ^ 2 with hlamdef
  have hlampos : 0 < lam := by
    rw [hlamdef]; exact Work.NN.Core.sharpCut_sq_sub_pos ha hab
  have hlamne : lam ≠ 0 := ne_of_gt hlampos
  -- the affine change of variable
  have hT : ∀ u : ℝ, HasDerivAt (fun u : ℝ => (b ^ 2 - u) / lam) (-(1 / lam)) u := by
    intro u
    have h1 := (hasDerivAt_const (x := u) (c := b ^ 2)).sub (hasDerivAt_id u)
    have h2 := h1.div_const lam
    convert h2 using 1
    ext v
    simp only [Pi.sub_apply, id_eq]
    ring
  have hχ_eq : Work.NN.Core.sharpCutReal a b
      = fun u : ℝ => Real.smoothTransition ((b ^ 2 - u) / lam) := rfl
  -- differentiability of σ, σ', σ''
  have hσd : ∀ t : ℝ, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition t) t :=
    fun t => ((Work.NN.Core.Lev.contDiff_smoothTransition.differentiable (by simp)) t).hasDerivAt
  have hσ'd : ∀ t : ℝ, HasDerivAt (deriv Real.smoothTransition)
      (deriv (deriv Real.smoothTransition) t) t :=
    fun t => ((Work.NN.Core.Lev.contDiff_deriv_smoothTransition.differentiable (by simp)) t).hasDerivAt
  have hσ''cd : ContDiff ℝ ∞ (deriv (deriv Real.smoothTransition)) := by
    have h := Work.NN.Core.Lev.contDiff_smoothTransition.iterate_deriv 2
    rwa [show (deriv^[2] Real.smoothTransition) = deriv (deriv Real.smoothTransition) from by
      funext x; simp [Function.iterate_succ, Function.comp_apply]] at h
  have hσ''d : ∀ t : ℝ, HasDerivAt (deriv (deriv Real.smoothTransition))
      (deriv (deriv (deriv Real.smoothTransition)) t) t :=
    fun t => ((hσ''cd.differentiable (by simp)) t).hasDerivAt
  -- first derivative
  have hd1 : ∀ u : ℝ, deriv (Work.NN.Core.sharpCutReal a b) u
      = deriv Real.smoothTransition ((b ^ 2 - u) / lam) * (-(1 / lam)) := by
    intro u
    have h : HasDerivAt (fun u : ℝ => Real.smoothTransition ((b ^ 2 - u) / lam))
        (deriv Real.smoothTransition ((b ^ 2 - u) / lam) * (-(1 / lam))) u := by
      simpa only [Function.comp_def] using ((hσd ((b ^ 2 - u) / lam)).comp u (hT u))
    rw [hχ_eq]
    exact h.deriv
  -- second derivative
  have hd2 : ∀ u : ℝ, deriv (deriv (Work.NN.Core.sharpCutReal a b)) u
      = deriv (deriv Real.smoothTransition) ((b ^ 2 - u) / lam) * (-(1 / lam)) * (-(1 / lam)) := by
    intro u
    have hψ : deriv (Work.NN.Core.sharpCutReal a b)
        = fun u : ℝ => deriv Real.smoothTransition ((b ^ 2 - u) / lam) * (-(1 / lam)) :=
      funext hd1
    have h : HasDerivAt (fun u : ℝ => deriv Real.smoothTransition ((b ^ 2 - u) / lam) * (-(1 / lam)))
        ((deriv (deriv Real.smoothTransition) ((b ^ 2 - u) / lam) * (-(1 / lam))) * (-(1 / lam))) u :=
      ((hσ'd ((b ^ 2 - u) / lam)).comp u (hT u)).mul_const (-(1 / lam))
    rw [hψ]
    exact h.deriv
  -- third derivative
  have hd3 : ∀ u : ℝ, deriv (deriv (deriv (Work.NN.Core.sharpCutReal a b))) u
      = deriv (deriv (deriv Real.smoothTransition)) ((b ^ 2 - u) / lam) * (-(1 / lam)) * (-(1 / lam))
        * (-(1 / lam)) := by
    intro u
    have hψ : deriv (deriv (Work.NN.Core.sharpCutReal a b))
        = fun u : ℝ => deriv (deriv Real.smoothTransition) ((b ^ 2 - u) / lam) * (-(1 / lam)) * (-(1 / lam)) :=
      funext hd2
    have h : HasDerivAt
        (fun u : ℝ => deriv (deriv Real.smoothTransition) ((b ^ 2 - u) / lam) * (-(1 / lam)) * (-(1 / lam)))
        ((deriv (deriv (deriv Real.smoothTransition)) ((b ^ 2 - u) / lam) * (-(1 / lam)) * (-(1 / lam)))
          * (-(1 / lam))) u :=
      (((hσ''d ((b ^ 2 - u) / lam)).comp u (hT u)).mul_const (-(1 / lam))).mul_const (-(1 / lam))
    rw [hψ]
    exact h.deriv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u
    rw [hd1 u, abs_mul]
    have h2 : |(-(1 / lam) : ℝ)| = 1 / lam := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
    rw [h2]
    calc |deriv Real.smoothTransition ((b ^ 2 - u) / lam)| * (1 / lam) ≤ C₁ * (1 / lam) :=
          mul_le_mul_of_nonneg_right (hC₁ _) (by positivity)
      _ = C₁ / lam := by ring
  · intro u
    have hψ : deriv (Work.NN.Core.sharpCutReal a b)
        = fun u : ℝ => deriv Real.smoothTransition ((b ^ 2 - u) / lam) * (-(1 / lam)) := funext hd1
    have h : HasDerivAt (fun u : ℝ => deriv Real.smoothTransition ((b ^ 2 - u) / lam) * (-(1 / lam)))
        ((deriv (deriv Real.smoothTransition) ((b ^ 2 - u) / lam) * (-(1 / lam))) * (-(1 / lam))) u :=
      ((hσ'd ((b ^ 2 - u) / lam)).comp u (hT u)).mul_const (-(1 / lam))
    rw [hd2 u, hψ]
    exact h
  · intro u
    rw [hd2 u, abs_mul, abs_mul]
    have h2 : |(-(1 / lam) : ℝ)| = 1 / lam := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
    simp only [h2]
    have hle : (0 : ℝ) ≤ 1 / lam := by positivity
    have hs : |deriv (deriv Real.smoothTransition) ((b ^ 2 - u) / lam)| ≤ C₂ := hC₂ _
    calc |deriv (deriv Real.smoothTransition) ((b ^ 2 - u) / lam)| * (1 / lam) * (1 / lam)
        ≤ C₂ * (1 / lam) * (1 / lam) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hle) hle
      _ = C₂ / lam ^ 2 := by ring_nf
  · intro u
    have hψ : deriv (deriv (Work.NN.Core.sharpCutReal a b))
        = fun u : ℝ => deriv (deriv Real.smoothTransition) ((b ^ 2 - u) / lam) * (-(1 / lam))
            * (-(1 / lam)) :=
      funext hd2
    have h : HasDerivAt
        (fun u : ℝ => deriv (deriv Real.smoothTransition) ((b ^ 2 - u) / lam) * (-(1 / lam))
          * (-(1 / lam)))
        (((deriv (deriv (deriv Real.smoothTransition)) ((b ^ 2 - u) / lam) * (-(1 / lam)))
          * (-(1 / lam))) * (-(1 / lam))) u :=
      (((hσ''d ((b ^ 2 - u) / lam)).comp u (hT u)).mul_const (-(1 / lam))).mul_const (-(1 / lam))
    rw [hd3 u, hψ]
    exact h
  · intro u
    rw [hd3 u, abs_mul, abs_mul, abs_mul]
    have h2 : |(-(1 / lam) : ℝ)| = 1 / lam := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
    simp only [h2]
    have hle : (0 : ℝ) ≤ 1 / lam := by positivity
    have hs : |deriv (deriv (deriv Real.smoothTransition)) ((b ^ 2 - u) / lam)| ≤ C₃ := hC₃ _
    calc |deriv (deriv (deriv Real.smoothTransition)) ((b ^ 2 - u) / lam)| * (1 / lam) * (1 / lam)
          * (1 / lam)
        ≤ C₃ * (1 / lam) * (1 / lam) * (1 / lam) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hle) hle) hle
      _ = C₃ / lam ^ 3 := by ring_nf

/-! ## The `C^{1,α}`-bound for a radial product `z ↦ ψ(‖φ z‖²) • φ z` -/

/-- **`C^{1,α}`-bound for a radial product.**

Let `X` be a real normed space, `φ : X →L[ℝ] ℂ` a continuous linear map of norm at most `1`,
`Ω ⊆ X` open and convex with `‖φ z‖ ≤ b` on `Ω`, and let `ψ : ℝ → ℝ` have `|ψ| ≤ K₀`,
`ψ' = (ψ)'` with `|ψ'| ≤ K₁` and `ψ'' = (ψ')'` with `|ψ''| ≤ K₂` globally.  Then
`g : z ↦ ψ(‖φ z‖²) • φ z` satisfies `‖g‖ ≤ K₀ b`, `‖Dg‖ ≤ 2 K₁ b² + K₀` and
`‖Dg x - Dg y‖ ≤ (4 K₂ b³ + 6 K₁ b) ‖x - y‖` on `Ω`, so that (comparing `‖x - y‖` with
`‖x - y‖ ^ α` according to whether it is at most `1`)

  `holderNorm 1 α g Ω ≤ ofReal (3 (K₀ b) + 4 (2 K₁ b² + K₀) + max (2 (2 K₁ b² + K₀)) (4 K₂ b³ + 6 K₁ b))`.

This is the quantitative core of the bound on `kappabar`: there `φ` is the coordinate projection
and `ψ = deriv (sharpCutReal a b)`. -/
theorem holderNorm_radial_prod_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : X →L[ℝ] ℂ) (hφ1 : ‖φ‖ ≤ 1) {b K₀ K₁ K₂ : ℝ}
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hb : 0 ≤ b)
    {ψ ψ' ψ'' : ℝ → ℝ} (hψ : ∀ u : ℝ, |ψ u| ≤ K₀)
    (hψd : ∀ u : ℝ, HasDerivAt ψ (ψ' u) u) (hψ' : ∀ u : ℝ, |ψ' u| ≤ K₁)
    (hψ'd : ∀ u : ℝ, HasDerivAt ψ' (ψ'' u) u) (hψ'' : ∀ u : ℝ, |ψ'' u| ≤ K₂)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {Ω : Set X} (hΩop : IsOpen Ω)
    (hΩcv : Convex ℝ Ω) (hΩb : ∀ z ∈ Ω, ‖φ z‖ ≤ b) :
    Work.CR.Flat.holderNorm 1 α
        (fun z : X => (ψ (Complex.normSq (φ z))) • φ z) Ω
      ≤ ENNReal.ofReal (3 * (K₀ * b) + 4 * (2 * K₁ * b ^ 2 + K₀)
          + max (2 * (2 * K₁ * b ^ 2 + K₀)) (4 * K₂ * b ^ 3 + 6 * K₁ * b)) := by
  have hφle : ∀ v : X, ‖φ v‖ ≤ ‖v‖ := by
    intro v
    calc ‖φ v‖ ≤ ‖φ‖ * ‖v‖ := φ.le_opNorm v
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hφ1 (norm_nonneg v)
      _ = ‖v‖ := one_mul _
  have hφsub : ∀ x y : X, ‖φ x - φ y‖ ≤ ‖x - y‖ := by
    intro x y
    rw [← map_sub]
    exact hφle (x - y)
  -- the derivative of `z ↦ ‖φ z‖²`
  set dn := (fun z : X => 2 • ((innerSL ℝ) (φ z)).comp φ) with hdndef
  have hdn_has : ∀ z : X, HasFDerivAt (fun w : X => Complex.normSq (φ w)) (dn z) z := by
    intro z
    have h1 := Work.CR.Flat.hasFDerivAt_normSq_aux (φ z)
    have h := h1.comp z (ContinuousLinearMap.hasFDerivAt φ)
    simpa only [hdndef, Function.comp_def, ContinuousLinearMap.smul_comp] using h
  have hdnp_has : ∀ z : X,
      HasFDerivAt (fun w : X => ψ (Complex.normSq (φ w))) ((ψ' (Complex.normSq (φ z))) • dn z) z :=
    fun z => (hψd (Complex.normSq (φ z))).comp_hasFDerivAt z (hdn_has z)
  have hL_has : ∀ z : X,
      HasFDerivAt (fun w : X => (ψ (Complex.normSq (φ w))) • φ w)
        ((ψ (Complex.normSq (φ z))) • φ
          + ((ψ' (Complex.normSq (φ z))) • dn z).smulRight (φ z)) z :=
    fun z => (hdnp_has z).smul (ContinuousLinearMap.hasFDerivAt φ)
  -- the pointwise value of the derivative
  have hL_apply : ∀ (z : X) (v : X),
      ((ψ (Complex.normSq (φ z))) • φ
          + ((ψ' (Complex.normSq (φ z))) • dn z).smulRight (φ z)) v
        = (ψ (Complex.normSq (φ z))) • (φ v)
          + (ψ' (Complex.normSq (φ z)) • (dn z v)) • (φ z) := by
    intro z v
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  -- the values of `dn`
  have hdn_apply : ∀ (z v : X), dn z v = 2 * (((innerSL ℝ) (φ z)) (φ v)) := by
    intro z v
    simp only [hdndef, ContinuousLinearMap.comp_apply, smul_apply]
    ring
  have hdn_le : ∀ (z v : X), |dn z v| ≤ 2 * ‖φ z‖ * ‖v‖ := by
    intro z v
    have h1 : |((innerSL ℝ) (φ z)) (φ v)| ≤ ‖φ z‖ * ‖v‖ := by
      calc |((innerSL ℝ) (φ z)) (φ v)| ≤ ‖((innerSL ℝ) (φ z))‖ * ‖φ v‖ := by
            simpa only [Real.norm_eq_abs] using
              ContinuousLinearMap.le_opNorm ((innerSL ℝ) (φ z)) (φ v)
        _ ≤ (‖(innerSL ℝ : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ))‖ * ‖φ z‖) * ‖v‖ :=
            mul_le_mul (ContinuousLinearMap.le_opNorm (innerSL ℝ) (φ z)) (hφle v)
              (norm_nonneg _) (by positivity)
        _ ≤ (1 * ‖φ z‖) * ‖v‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (norm_innerSL_le ℝ) (norm_nonneg _)) (norm_nonneg _)
        _ = ‖φ z‖ * ‖v‖ := by ring
    rw [hdn_apply z v, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [h1, norm_nonneg (φ z), norm_nonneg v]
  have hdn_diff : ∀ (x y v : X),
      dn x v - dn y v = 2 * (((innerSL ℝ) (φ x - φ y)) (φ v)) := by
    intro x y v
    have h2 : ((innerSL ℝ) (φ x)) (φ v) - ((innerSL ℝ) (φ y)) (φ v)
        = ((innerSL ℝ) (φ x - φ y)) (φ v) := by
      rw [← sub_apply, map_sub]
    rw [hdn_apply x v, hdn_apply y v, ← mul_sub, h2]
  -- constants
  have hK0b : 0 ≤ K₀ * b := mul_nonneg hK₀ hb
  have hM1nn : 0 ≤ 2 * K₁ * b ^ 2 + K₀ := by positivity
  have hM2c : 0 ≤ 4 * K₂ * b ^ 3 + 6 * K₁ * b := by positivity
  have hMmax : 0 ≤ max (2 * (2 * K₁ * b ^ 2 + K₀)) (4 * K₂ * b ^ 3 + 6 * K₁ * b) :=
    le_trans (by positivity) (le_max_left _ _)
  -- Lipschitz bounds for `ψ` and `ψ'`
  have hψ_lip : ∀ u u' : ℝ, |ψ u - ψ u'| ≤ K₁ * |u - u'| := by
    intro u u'
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := ψ) (s := Set.univ) (C := K₁)
      (fun t _ => (hψd t).differentiableAt)
      (fun t _ => by rw [(hψd t).deriv, Real.norm_eq_abs]; exact hψ' t)
      convex_univ (Set.mem_univ u') (Set.mem_univ u)
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h
  have hψ'_lip : ∀ u u' : ℝ, |ψ' u - ψ' u'| ≤ K₂ * |u - u'| := by
    intro u u'
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := ψ') (s := Set.univ) (C := K₂)
      (fun t _ => (hψ'd t).differentiableAt)
      (fun t _ => by rw [(hψ'd t).deriv, Real.norm_eq_abs]; exact hψ'' t)
      convex_univ (Set.mem_univ u') (Set.mem_univ u)
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h
  -- `|‖φ x‖² - ‖φ y‖²| ≤ 2 b ‖x - y‖` on `Ω`
  have hnormSq_diff : ∀ x ∈ Ω, ∀ y ∈ Ω,
      |Complex.normSq (φ x) - Complex.normSq (φ y)| ≤ 2 * b * ‖x - y‖ := by
    intro x hx y hy
    have h1 : Complex.normSq (φ x) - Complex.normSq (φ y)
        = (‖φ x‖ - ‖φ y‖) * (‖φ x‖ + ‖φ y‖) := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      ring
    have h2 : |‖φ x‖ - ‖φ y‖| ≤ ‖x - y‖ := by
      have h3 : |‖φ x‖ - ‖φ y‖| ≤ ‖φ x - φ y‖ := abs_norm_sub_norm_le _ _
      linarith [hφsub x y]
    have h5 : ‖φ x‖ + ‖φ y‖ ≤ 2 * b := by
      have hx' := hΩb x hx
      have hy' := hΩb y hy
      linarith
    rw [h1, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    calc |‖φ x‖ - ‖φ y‖| * (‖φ x‖ + ‖φ y‖) ≤ ‖x - y‖ * (2 * b) :=
          mul_le_mul h2 h5 (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
      _ = 2 * b * ‖x - y‖ := by ring
  -- order `0`
  have h0 : ∀ z ∈ Ω, ‖(ψ (Complex.normSq (φ z))) • φ z‖ ≤ K₀ * b := by
    intro z hz
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hψ _) (hΩb z hz) (norm_nonneg _) hK₀
  -- order `1`
  have h1 : ∀ z ∈ Ω,
      ‖fderiv ℝ (fun w : X => (ψ (Complex.normSq (φ w))) • φ w) z‖
        ≤ 2 * K₁ * b ^ 2 + K₀ := by
    intro z hz
    rw [(hL_has z).fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ hM1nn fun v => ?_
    rw [hL_apply z v]
    have hdnv : |dn z v| ≤ 2 * b * ‖v‖ :=
      le_trans (hdn_le z v) (by nlinarith [hΩb z hz, norm_nonneg v])
    have ht1 : ‖(ψ (Complex.normSq (φ z))) • (φ v)‖ ≤ K₀ * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hψ _) (hφle v) (norm_nonneg _) hK₀
    have ht2 : ‖(ψ' (Complex.normSq (φ z)) • (dn z v)) • (φ z)‖ ≤ K₁ * (2 * b * ‖v‖) * b := by
      rw [norm_smul, Real.norm_eq_abs]
      have ha : |ψ' (Complex.normSq (φ z)) • (dn z v)| ≤ K₁ * (2 * b * ‖v‖) := by
        rw [smul_eq_mul, abs_mul]
        exact mul_le_mul (hψ' _) hdnv (abs_nonneg _) hK₁
      exact mul_le_mul ha (hΩb z hz) (norm_nonneg _) (by positivity)
    have hsum := norm_add_le ((ψ (Complex.normSq (φ z))) • (φ v))
      ((ψ' (Complex.normSq (φ z)) • (dn z v)) • (φ z))
    have htarget : (2 * K₁ * b ^ 2 + K₀) * ‖v‖ = K₀ * ‖v‖ + K₁ * (2 * b * ‖v‖) * b := by ring
    linarith [hsum, ht1, ht2]
  -- the difference bound
  have hdiff_lip : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ v : X,
      ‖(fderiv ℝ (fun w : X => (ψ (Complex.normSq (φ w))) • φ w) x
          - fderiv ℝ (fun w : X => (ψ (Complex.normSq (φ w))) • φ w) y) v‖
        ≤ (4 * K₂ * b ^ 3 + 6 * K₁ * b) * ‖x - y‖ * ‖v‖ := by
    intro x hx y hy v
    rw [sub_apply, (hL_has x).fderiv, (hL_has y).fderiv, hL_apply x v, hL_apply y v]
    have hsplit : (ψ (Complex.normSq (φ x))) • (φ v)
            + (ψ' (Complex.normSq (φ x)) • (dn x v)) • (φ x)
          - ((ψ (Complex.normSq (φ y))) • (φ v)
            + (ψ' (Complex.normSq (φ y)) • (dn y v)) • (φ y))
        = (ψ (Complex.normSq (φ x)) - ψ (Complex.normSq (φ y))) • (φ v)
          + ((ψ' (Complex.normSq (φ x)) - ψ' (Complex.normSq (φ y))) * (dn x v)) • (φ x)
          + (ψ' (Complex.normSq (φ y)) * (dn x v - dn y v)) • (φ x)
          + (ψ' (Complex.normSq (φ y)) * (dn y v)) • (φ x - φ y) := by
      module
    rw [hsplit]
    have hdx : |Complex.normSq (φ x) - Complex.normSq (φ y)| ≤ 2 * b * ‖x - y‖ :=
      hnormSq_diff x hx y hy
    have hxy : 0 ≤ ‖x - y‖ := norm_nonneg _
    have hdnxv : |dn x v| ≤ 2 * b * ‖v‖ :=
      le_trans (hdn_le x v) (by nlinarith [hΩb x hx, norm_nonneg v])
    have hdnyv : |dn y v| ≤ 2 * b * ‖v‖ :=
      le_trans (hdn_le y v) (by nlinarith [hΩb y hy, norm_nonneg v])
    have hdnd : |dn x v - dn y v| ≤ 2 * ‖x - y‖ * ‖v‖ := by
      rw [hdn_diff x y v, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have h1 : |((innerSL ℝ) (φ x - φ y)) (φ v)| ≤ ‖x - y‖ * ‖v‖ := by
        calc |((innerSL ℝ) (φ x - φ y)) (φ v)|
            ≤ ‖((innerSL ℝ) (φ x - φ y))‖ * ‖φ v‖ := by
              simpa only [Real.norm_eq_abs] using
                ContinuousLinearMap.le_opNorm ((innerSL ℝ) (φ x - φ y)) (φ v)
          _ ≤ (‖(innerSL ℝ : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ))‖ * ‖x - y‖) * ‖v‖ := by
              refine mul_le_mul ?_ (hφle v) (norm_nonneg _) (by positivity)
              calc ‖(innerSL ℝ) (φ x - φ y)‖
                  ≤ ‖(innerSL ℝ : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ))‖ * ‖φ x - φ y‖ :=
                    ContinuousLinearMap.le_opNorm _ _
                _ ≤ ‖(innerSL ℝ : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ))‖ * ‖x - y‖ :=
                    mul_le_mul_of_nonneg_left (hφsub x y)
                      (ContinuousLinearMap.opNorm_nonneg _)
          _ ≤ (1 * ‖x - y‖) * ‖v‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (norm_innerSL_le ℝ) (norm_nonneg _)) (norm_nonneg _)
          _ = ‖x - y‖ * ‖v‖ := by ring
      nlinarith [h1, norm_nonneg v]
    have hvs : ‖φ v‖ ≤ ‖v‖ := hφle v
    have hzus : ‖φ x‖ ≤ b := hΩb x hx
    have hzys : ‖φ y‖ ≤ b := hΩb y hy
    have hsubxy : ‖φ x - φ y‖ ≤ ‖x - y‖ := hφsub x y
    have hs1 : |ψ (Complex.normSq (φ x)) - ψ (Complex.normSq (φ y))| ≤ K₁ * (2 * b * ‖x - y‖) :=
      le_trans (hψ_lip _ _) (mul_le_mul_of_nonneg_left hdx hK₁)
    have hs2 : |ψ' (Complex.normSq (φ x)) - ψ' (Complex.normSq (φ y))| ≤ K₂ * (2 * b * ‖x - y‖) :=
      le_trans (hψ'_lip _ _) (mul_le_mul_of_nonneg_left hdx hK₂)
    have ht1 : ‖(ψ (Complex.normSq (φ x)) - ψ (Complex.normSq (φ y))) • (φ v)‖
        ≤ (K₁ * (2 * b * ‖x - y‖)) * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hs1 hvs (norm_nonneg _) (by positivity)
    have ht2 : ‖((ψ' (Complex.normSq (φ x)) - ψ' (Complex.normSq (φ y))) * (dn x v)) • (φ x)‖
        ≤ (K₂ * (2 * b * ‖x - y‖)) * (2 * b * ‖v‖) * b := by
      rw [norm_smul, Real.norm_eq_abs]
      have ha : |(ψ' (Complex.normSq (φ x)) - ψ' (Complex.normSq (φ y))) * (dn x v)|
          ≤ (K₂ * (2 * b * ‖x - y‖)) * (2 * b * ‖v‖) := by
        rw [abs_mul]
        exact mul_le_mul hs2 hdnxv (abs_nonneg _) (by positivity)
      exact mul_le_mul ha hzus (norm_nonneg _) (by positivity)
    have ht3 : ‖(ψ' (Complex.normSq (φ y)) * (dn x v - dn y v)) • (φ x)‖
        ≤ (K₁ * (2 * ‖x - y‖ * ‖v‖)) * b := by
      rw [norm_smul, Real.norm_eq_abs]
      have ha : |ψ' (Complex.normSq (φ y)) * (dn x v - dn y v)| ≤ K₁ * (2 * ‖x - y‖ * ‖v‖) := by
        rw [abs_mul]
        exact mul_le_mul (hψ' _) hdnd (abs_nonneg _) hK₁
      exact mul_le_mul ha hzus (norm_nonneg _) (by positivity)
    have ht4 : ‖(ψ' (Complex.normSq (φ y)) * (dn y v)) • (φ x - φ y)‖
        ≤ (K₁ * (2 * b * ‖v‖)) * ‖x - y‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have ha : |ψ' (Complex.normSq (φ y)) * (dn y v)| ≤ K₁ * (2 * b * ‖v‖) := by
        rw [abs_mul]
        exact mul_le_mul (hψ' _) hdnyv (abs_nonneg _) hK₁
      exact mul_le_mul ha hsubxy (norm_nonneg _) (by positivity)
    have hsum1 := norm_add_le ((ψ (Complex.normSq (φ x)) - ψ (Complex.normSq (φ y))) • (φ v))
      (((ψ' (Complex.normSq (φ x)) - ψ' (Complex.normSq (φ y))) * (dn x v)) • (φ x))
    have hsum2 := norm_add_le
      ((ψ (Complex.normSq (φ x)) - ψ (Complex.normSq (φ y))) • (φ v)
        + ((ψ' (Complex.normSq (φ x)) - ψ' (Complex.normSq (φ y))) * (dn x v)) • (φ x))
      ((ψ' (Complex.normSq (φ y)) * (dn x v - dn y v)) • (φ x))
    have hsum3 := norm_add_le
      ((ψ (Complex.normSq (φ x)) - ψ (Complex.normSq (φ y))) • (φ v)
        + ((ψ' (Complex.normSq (φ x)) - ψ' (Complex.normSq (φ y))) * (dn x v)) • (φ x)
        + (ψ' (Complex.normSq (φ y)) * (dn x v - dn y v)) • (φ x))
      ((ψ' (Complex.normSq (φ y)) * (dn y v)) • (φ x - φ y))
    have htarget : (4 * K₂ * b ^ 3 + 6 * K₁ * b) * ‖x - y‖ * ‖v‖
        = (K₁ * (2 * b * ‖x - y‖)) * ‖v‖ + (K₂ * (2 * b * ‖x - y‖)) * (2 * b * ‖v‖) * b
          + (K₁ * (2 * ‖x - y‖ * ‖v‖)) * b + (K₁ * (2 * b * ‖v‖)) * ‖x - y‖ := by ring
    linarith [hsum1, hsum2, hsum3, ht1, ht2, ht3, ht4]
  -- the `α`-Hölder form
  have hbound2 : ∀ x ∈ Ω, ∀ y ∈ Ω,
      ‖fderiv ℝ (fun w : X => (ψ (Complex.normSq (φ w))) • φ w) x
          - fderiv ℝ (fun w : X => (ψ (Complex.normSq (φ w))) • φ w) y‖
        ≤ max (2 * (2 * K₁ * b ^ 2 + K₀)) (4 * K₂ * b ^ 3 + 6 * K₁ * b) * ‖x - y‖ ^ α := by
    intro x hx y hy
    by_cases hd : ‖x - y‖ ≤ 1
    · have hdα : ‖x - y‖ ≤ ‖x - y‖ ^ α := by
        rcases eq_or_ne x y with hxy | hxy
        · rw [hxy, sub_self, norm_zero, Real.zero_rpow hα0.ne']
        · have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
          have h2 : ‖x - y‖ ^ (1 : ℝ) ≤ ‖x - y‖ ^ α :=
            Real.rpow_le_rpow_of_exponent_ge hpos hd hα1.le
          rwa [Real.rpow_one] at h2
      have hle : ‖fderiv ℝ (fun w : X => (ψ (Complex.normSq (φ w))) • φ w) x
            - fderiv ℝ (fun w : X => (ψ (Complex.normSq (φ w))) • φ w) y‖
          ≤ (4 * K₂ * b ^ 3 + 6 * K₁ * b) * ‖x - y‖ :=
        ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => hdiff_lip x hx y hy v)
      calc _ ≤ (4 * K₂ * b ^ 3 + 6 * K₁ * b) * ‖x - y‖ := hle
        _ ≤ (4 * K₂ * b ^ 3 + 6 * K₁ * b) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_left hdα hM2c
        _ ≤ max (2 * (2 * K₁ * b ^ 2 + K₀)) (4 * K₂ * b ^ 3 + 6 * K₁ * b) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) α)
    · have hd1 : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow (le_of_lt (not_le.mp hd)) hα0.le
      have hx1 : ‖fderiv ℝ (fun w : X => (ψ (Complex.normSq (φ w))) • φ w) x‖
          ≤ 2 * K₁ * b ^ 2 + K₀ := h1 x hx
      have hy1 : ‖fderiv ℝ (fun w : X => (ψ (Complex.normSq (φ w))) • φ w) y‖
          ≤ 2 * K₁ * b ^ 2 + K₀ := h1 y hy
      calc _ ≤ ‖fderiv ℝ (fun w : X => (ψ (Complex.normSq (φ w))) • φ w) x‖
              + ‖fderiv ℝ (fun w : X => (ψ (Complex.normSq (φ w))) • φ w) y‖ := norm_sub_le _ _
        _ ≤ (2 * K₁ * b ^ 2 + K₀) + (2 * K₁ * b ^ 2 + K₀) := add_le_add hx1 hy1
        _ = 2 * (2 * K₁ * b ^ 2 + K₀) := by ring
        _ ≤ 2 * (2 * K₁ * b ^ 2 + K₀) * ‖x - y‖ ^ α := by nlinarith [hd1, hM1nn]
        _ ≤ max (2 * (2 * K₁ * b ^ 2 + K₀)) (4 * K₂ * b ^ 3 + 6 * K₁ * b) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) α)
  -- assemble
  have hdiff : ∀ x ∈ Ω,
      DifferentiableAt ℝ (fun w : X => (ψ (Complex.normSq (φ w))) • φ w) x :=
    fun x _ => (hL_has x).differentiableAt
  exact Work.NN.Newton.holderNorm_one_le_of_pointwise_bounds hΩop hΩcv hα0 hα1
    hK0b hM1nn hMmax hdiff h0 h1 hbound2

/-! ## The `δ`-uniform bound for `kappabar` -/

/-- **The requested bound.**  There is a constant `M`, independent of `δ`, such that for every
`0 < δ ≤ 1/4` and every coordinate `s` the `C^{1,α}`-norm of `kappabar (ftG δ) s` on the
tracking polydisc `Eset (ftG δ) s` is at most `M / δ⁶`. -/
theorem kappabar_holderNorm_le {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) (s : Fin n),
      Work.CR.Flat.holderNorm 1 α
          (Work.NN.Core.TelTwoDF.kappabar (Work.NN.Newton.ftG (n := n) δ hδ0 hδ4) s)
          (Work.NN.Core.TelTwoDF.Eset (Work.NN.Newton.ftG (n := n) δ hδ0 hδ4) s)
        ≤ ENNReal.ofReal (M / δ ^ 6) := by
  obtain ⟨C₁, C₂, C₃, hC₁0, hC₂0, hC₃0, hdat⟩ := sharpCutReal_deriv_data_aux
  refine ⟨16 ^ 6 * (9 * C₁ + 18 * C₂ + 4 * C₃ + 1), by positivity, ?_⟩
  intro δ hδ0 hδ4 s
  set G : Work.NN.Core.TelTwoDF.Geom n := Work.NN.Newton.ftG (n := n) δ hδ0 hδ4 with hG
  have ha_eq : G.a s = 1 - 15 * δ / 16 := by rw [hG]; exact Work.NN.Newton.ftG_a δ hδ0 hδ4 s
  have hb_eq : G.b s = 1 - 7 * δ / 8 := by rw [hG]; exact Work.NN.Newton.ftG_b δ hδ0 hδ4 s
  have ha0 : 0 ≤ G.a s := by rw [ha_eq]; linarith
  have hab : G.a s < G.b s := G.hab s
  have hb0 : 0 ≤ G.b s := (G.b_pos s).le
  have hb1 : G.b s ≤ 1 := by rw [hb_eq]; linarith
  have hSq : G.b s ^ 2 ≤ 1 := by
    calc G.b s ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hb0 hb1 2
      _ = 1 := one_pow 2
  have hCu : G.b s ^ 3 ≤ 1 := by
    calc G.b s ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ hb0 hb1 3
      _ = 1 := one_pow 3
  -- the analytic data of the profile at `(G.a s, G.b s)`
  obtain ⟨hd1, hd2, hd3, hd4, hd5⟩ := hdat (G.a s) (G.b s) ha0 hab
  set lam := G.b s ^ 2 - G.a s ^ 2 with hlamdef
  have hlam0 : 0 < lam := by
    rw [hlamdef, ha_eq, hb_eq]; nlinarith [hδ0, hδ4]
  have hlam1 : lam ≤ 1 := by
    rw [hlamdef, hb_eq]; nlinarith [hδ0, hδ4]
  have hlam_ge : δ / 16 ≤ lam := by
    rw [hlamdef, ha_eq, hb_eq]; nlinarith [hδ0, hδ4]
  set mu := 1 / lam with hmudef
  have hmu0 : 0 ≤ mu := by rw [hmudef]; positivity
  have hmu1 : 1 ≤ mu := by
    rw [hmudef, le_div_iff₀ hlam0]; linarith
  have hmu_d : mu ≤ 16 / δ := by
    rw [hmudef, div_le_div_iff₀ hlam0 hδ0]; nlinarith [hlam_ge]
  have hmu23 : mu ^ 2 ≤ mu ^ 3 := pow_le_pow_right₀ hmu1 (by norm_num)
  have hmu13 : mu ≤ mu ^ 3 := by
    calc mu = mu ^ 1 := (pow_one mu).symm
      _ ≤ mu ^ 3 := pow_le_pow_right₀ hmu1 (by norm_num)
  -- the projection and the geometry of `Eset`
  set proj : (Fin n → ℂ) →L[ℝ] ℂ :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) s with hprojdef
  have hproj_norm : ‖proj‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound proj zero_le_one fun z => ?_
    rw [one_mul, show proj z = z s from ContinuousLinearMap.proj_apply s z]
    exact norm_le_pi_norm z s
  have hΩb : ∀ z ∈ Work.NN.Core.TelTwoDF.Eset G s, ‖proj z‖ ≤ G.b s := by
    intro z hz
    have hzs : ‖z s‖ < Work.NN.Core.TelTwoDF.Erad G (s : ℕ) s := by
      rw [Work.NN.Core.TelTwoDF.mem_Eset] at hz
      exact hz s
    rw [Work.NN.Core.TelTwoDF.Erad_self] at hzs
    rw [show proj z = z s from ContinuousLinearMap.proj_apply s z]
    exact le_of_lt hzs
  have hΩop : IsOpen (Work.NN.Core.TelTwoDF.Eset G s) := Work.NN.Core.TelTwoDF.isOpen_Eset G s
  have hΩcv : Convex ℝ (Work.NN.Core.TelTwoDF.Eset G s) := by
    rw [Work.NN.Core.TelTwoDF.Eset]
    exact Work.NN.Newton.convex_polydisc_zero (Work.NN.Core.TelTwoDF.Erad G s)
  -- the one-variable data in terms of `mu = 1/lam`
  have hpsi : ∀ u : ℝ, |deriv (Work.NN.Core.sharpCutReal (G.a s) (G.b s)) u| ≤ C₁ * mu := by
    intro u
    have h := hd1 u
    rw [div_eq_mul_inv] at h
    rw [hmudef, one_div]
    exact h
  have hpsi' : ∀ u : ℝ,
      |deriv (deriv (Work.NN.Core.sharpCutReal (G.a s) (G.b s))) u| ≤ C₂ * mu ^ 2 := by
    intro u
    have h := hd3 u
    rw [div_eq_mul_inv, ← inv_pow] at h
    rw [hmudef, one_div]
    exact h
  have hpsi'' : ∀ u : ℝ,
      |deriv (deriv (deriv (Work.NN.Core.sharpCutReal (G.a s) (G.b s)))) u| ≤ C₃ * mu ^ 3 := by
    intro u
    have h := hd5 u
    rw [div_eq_mul_inv, ← inv_pow] at h
    rw [hmudef, one_div]
    exact h
  have hrad := holderNorm_radial_prod_le (X := Fin n → ℂ) (φ := proj) hproj_norm
    (b := G.b s) (K₀ := C₁ * mu) (K₁ := C₂ * mu ^ 2) (K₂ := C₃ * mu ^ 3)
    (ψ := deriv (Work.NN.Core.sharpCutReal (G.a s) (G.b s)))
    (ψ' := deriv (deriv (Work.NN.Core.sharpCutReal (G.a s) (G.b s))))
    (ψ'' := deriv (deriv (deriv (Work.NN.Core.sharpCutReal (G.a s) (G.b s)))))
    (mul_nonneg hC₁0 hmu0) (mul_nonneg hC₂0 (by positivity)) (mul_nonneg hC₃0 (by positivity))
    hb0 hpsi hd2 hpsi' hd4 hpsi'' hα0 hα1 hΩop hΩcv hΩb
  -- the identification with `kappabar`
  have hkapp : (fun z : Fin n → ℂ =>
        (deriv (Work.NN.Core.sharpCutReal (G.a s) (G.b s)) (Complex.normSq (proj z))) • proj z)
      = fun z : Fin n → ℂ => Work.NN.Core.TelTwoDF.kappabar G s z := by
    funext z
    rw [Work.NN.Core.TelTwoDF.kappabar, Work.NN.Core.TelTwoDF.dbarC_sharpCut_eq_aux (z s),
      ContinuousLinearMap.proj_apply, Algebra.smul_def]
    rfl
  rw [hkapp] at hrad
  -- the arithmetic
  have harith : 3 * ((C₁ * mu) * G.b s) + 4 * (2 * (C₂ * mu ^ 2) * G.b s ^ 2 + C₁ * mu)
      + max (2 * (2 * (C₂ * mu ^ 2) * G.b s ^ 2 + C₁ * mu))
          (4 * (C₃ * mu ^ 3) * G.b s ^ 3 + 6 * (C₂ * mu ^ 2) * G.b s)
      ≤ 16 ^ 6 * (9 * C₁ + 18 * C₂ + 4 * C₃ + 1) / δ ^ 6 := by
    have hsqu : (1 : ℝ) ≤ mu * mu := by nlinarith [hmu1, hmu0]
    have hA : 4 * C₂ * mu ^ 2 * G.b s ^ 2 ≤ 4 * C₂ * mu ^ 3 := by
      have h1 : 4 * C₂ * mu ^ 2 * G.b s ^ 2 ≤ 4 * C₂ * mu ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hSq (by positivity)
      have h2 : 4 * C₂ * mu ^ 2 * 1 ≤ 4 * C₂ * mu ^ 2 * mu :=
        mul_le_mul_of_nonneg_left hmu1 (by positivity)
      have h3 : 4 * C₂ * mu ^ 2 * mu = 4 * C₂ * mu ^ 3 := by ring
      linarith [h1, h2, h3]
    have hB : 2 * C₁ * mu ≤ 2 * C₁ * mu ^ 3 := by
      have h2 : 2 * C₁ * mu * 1 ≤ 2 * C₁ * mu * (mu * mu) :=
        mul_le_mul_of_nonneg_left hsqu (by positivity)
      have h3 : 2 * C₁ * mu * (mu * mu) = 2 * C₁ * mu ^ 3 := by ring
      have h4 : 2 * C₁ * mu * 1 = 2 * C₁ * mu := by ring
      linarith [h2, h3, h4]
    have hC : 0 ≤ 4 * C₃ * mu ^ 3 := by positivity
    have hD : 4 * C₃ * mu ^ 3 * G.b s ^ 3 ≤ 4 * C₃ * mu ^ 3 := by
      have h1 : 4 * C₃ * mu ^ 3 * G.b s ^ 3 ≤ 4 * C₃ * mu ^ 3 * 1 :=
        mul_le_mul_of_nonneg_left hCu (by positivity)
      have h2 : 4 * C₃ * mu ^ 3 * 1 = 4 * C₃ * mu ^ 3 := by ring
      linarith [h1, h2]
    have hE : 6 * C₂ * mu ^ 2 * G.b s ≤ 6 * C₂ * mu ^ 3 := by
      have h1 : 6 * C₂ * mu ^ 2 * G.b s ≤ 6 * C₂ * mu ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hb1 (by positivity)
      have h2 : 6 * C₂ * mu ^ 2 * 1 ≤ 6 * C₂ * mu ^ 2 * mu :=
        mul_le_mul_of_nonneg_left hmu1 (by positivity)
      have h3 : 6 * C₂ * mu ^ 2 * mu = 6 * C₂ * mu ^ 3 := by ring
      linarith [h1, h2, h3]
    have hF : 0 ≤ 2 * C₁ * mu ^ 3 := by positivity
    have hM1 : 2 * (2 * (C₂ * mu ^ 2) * G.b s ^ 2 + C₁ * mu)
        ≤ (2 * C₁ + 10 * C₂ + 4 * C₃) * mu ^ 3 := by
      nlinarith [hA, hB, hC]
    have hM2 : 4 * (C₃ * mu ^ 3) * G.b s ^ 3 + 6 * (C₂ * mu ^ 2) * G.b s
        ≤ (2 * C₁ + 10 * C₂ + 4 * C₃) * mu ^ 3 := by
      nlinarith [hD, hE, hF]
    have hmax : max (2 * (2 * (C₂ * mu ^ 2) * G.b s ^ 2 + C₁ * mu))
        (4 * (C₃ * mu ^ 3) * G.b s ^ 3 + 6 * (C₂ * mu ^ 2) * G.b s)
        ≤ (2 * C₁ + 10 * C₂ + 4 * C₃) * mu ^ 3 := by
      rw [max_le_iff]
      exact ⟨hM1, hM2⟩
    have hG : 3 * ((C₁ * mu) * G.b s) ≤ 3 * C₁ * mu ^ 3 := by
      have h0 : C₁ * mu * G.b s ≤ C₁ * mu * 1 :=
        mul_le_mul_of_nonneg_left hb1 (by positivity)
      have h1 : 3 * (C₁ * mu * G.b s) ≤ 3 * (C₁ * mu * 1) :=
        mul_le_mul_of_nonneg_left h0 (by norm_num)
      have h0' : C₁ * mu * 1 ≤ C₁ * mu * (mu * mu) :=
        mul_le_mul_of_nonneg_left hsqu (by positivity)
      have h2 : 3 * (C₁ * mu * 1) ≤ 3 * (C₁ * mu * (mu * mu)) :=
        mul_le_mul_of_nonneg_left h0' (by norm_num)
      have h3 : 3 * (C₁ * mu * (mu * mu)) = 3 * C₁ * mu ^ 3 := by ring
      have h4 : 3 * (C₁ * mu * 1) = 3 * (C₁ * mu) := by ring
      linarith [h1, h2, h3, h4]
    have hH : 0 ≤ mu ^ 3 := by positivity
    have htot : 3 * ((C₁ * mu) * G.b s) + 4 * (2 * (C₂ * mu ^ 2) * G.b s ^ 2 + C₁ * mu)
        + max (2 * (2 * (C₂ * mu ^ 2) * G.b s ^ 2 + C₁ * mu))
            (4 * (C₃ * mu ^ 3) * G.b s ^ 3 + 6 * (C₂ * mu ^ 2) * G.b s)
        ≤ (9 * C₁ + 18 * C₂ + 4 * C₃ + 1) * mu ^ 3 := by
      nlinarith [hmax, hG, hH, hmu0]
    have hmu_pow : mu ^ 3 ≤ (16 / δ) ^ 3 := pow_le_pow_left₀ hmu0 hmu_d 3
    have hδ_pow : (16 / δ) ^ 3 ≤ 16 ^ 6 / δ ^ 6 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have h : δ ^ 3 ≤ 16 ^ 3 := pow_le_pow_left₀ hδ0.le (by linarith) 3
      have hδ3 : 0 ≤ δ ^ 3 := by positivity
      have h1 : δ ^ 6 ≤ 16 ^ 3 * δ ^ 3 := by
        calc δ ^ 6 = δ ^ 3 * δ ^ 3 := by ring
          _ ≤ 16 ^ 3 * δ ^ 3 := mul_le_mul_of_nonneg_right h hδ3
      calc 16 ^ 3 * δ ^ 6 ≤ 16 ^ 3 * (16 ^ 3 * δ ^ 3) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = 16 ^ 6 * δ ^ 3 := by ring
    calc 3 * ((C₁ * mu) * G.b s) + 4 * (2 * (C₂ * mu ^ 2) * G.b s ^ 2 + C₁ * mu)
          + max (2 * (2 * (C₂ * mu ^ 2) * G.b s ^ 2 + C₁ * mu))
              (4 * (C₃ * mu ^ 3) * G.b s ^ 3 + 6 * (C₂ * mu ^ 2) * G.b s)
        ≤ (9 * C₁ + 18 * C₂ + 4 * C₃ + 1) * mu ^ 3 := htot
      _ ≤ (9 * C₁ + 18 * C₂ + 4 * C₃ + 1) * (16 / δ) ^ 3 :=
          mul_le_mul_of_nonneg_left hmu_pow (by positivity)
      _ ≤ (9 * C₁ + 18 * C₂ + 4 * C₃ + 1) * (16 ^ 6 / δ ^ 6) :=
          mul_le_mul_of_nonneg_left hδ_pow (by positivity)
      _ = 16 ^ 6 * (9 * C₁ + 18 * C₂ + 4 * C₃ + 1) / δ ^ 6 := by ring
  exact le_trans hrad (ENNReal.ofReal_le_ofReal harith)
