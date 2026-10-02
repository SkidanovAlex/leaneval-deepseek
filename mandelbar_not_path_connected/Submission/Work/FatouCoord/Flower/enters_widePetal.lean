/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoord team
-/
import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Flower.GermDefs
import Submission.Work.FatouCoord.Repelling.near_translation_mod
import Submission.Work.FatouCoord.Flower.widePetal_growth

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Every orbit converging to `0` enters the wide petal

If `f^[n] u → 0` and `f^[n] u ≠ 0` for all `n`, then some iterate of `u` lies in the wide petal
`WidePetal M` (for any fixed level `M`).  The chart coordinate `W_n = -1/(f^[n] u)` has
`‖W_n‖ → ∞`; past the region where `f` is controlled the chart dynamics is a translation by
`1` up to `o(1)`, so `Re W_n → +∞`, and eventually `sgauge W_n > M`.
-/

open scoped Topology
open Set Filter Metric Function

namespace Work.FatouCoord.Flower

open Work.FatouCoord

noncomputable section

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}

theorem enters_widePetal (hb : ParabolicBounds f h a r A A')
    {M : ℝ} (hM : 1 ≤ M) (hMr : 1 / r < M)
    (hgr : ∀ W : ℂ, M < sgauge W →
      M < sgauge (wMap f W) ∧ (wMap f W).re ≥ W.re + 1 / 2) :
    ∀ u : ℂ, Tendsto (fun n : ℕ => f^[n] u) atTop (nhds 0) → (∀ n : ℕ, f^[n] u ≠ 0) →
      ∃ n : ℕ, f^[n] u ∈ WidePetal M := by
  intro u ht hne
  by_contra hcon
  have hcon' : ∀ n : ℕ, f^[n] u ∉ WidePetal M := fun n hn => hcon ⟨n, hn⟩
  have hKnn : 0 ≤ Estimate.Ksub A a := Estimate.Ksub_nonneg hb.hA a
  set K := Estimate.Ksub A a with hKdef
  set W : ℕ → ℂ := fun n => -1 / (f^[n] u) with hWdef
  have hW_eq : ∀ n : ℕ, W n = (-1 : ℂ) / (f^[n] u) := fun n => rfl
  have hWle : ∀ n : ℕ, sgauge (W n) ≤ M := by
    intro n
    by_contra h
    exact hcon' n ⟨hne n, not_le.mp h⟩
  have hWnorm_eq : ∀ n : ℕ, ‖W n‖ = (‖f^[n] u‖)⁻¹ := by
    intro n
    rw [hW_eq n]
    exact norm_chart (hne n)
  -- the chart coordinate blows up
  have hWnorm : Tendsto (fun n : ℕ => ‖W n‖) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro c
    have h1 : ∀ᶠ n in atTop, ‖f^[n] u‖ < 1 / (max c 0 + 1) := by
      obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp ht (1 / (max c 0 + 1)) (by positivity)
      exact eventually_atTop.mpr ⟨N₀, fun n hn => by
        have h2 := hN₀ n hn
        rwa [dist_zero_right] at h2⟩
    filter_upwards [h1] with n hn
    have hpos : 0 < ‖f^[n] u‖ := norm_pos_iff.mpr (hne n)
    have hb0 : 0 < 1 / (max c 0 + 1) := by positivity
    have h4 : (1 / (max c 0 + 1))⁻¹ < (‖f^[n] u‖)⁻¹ := (inv_lt_inv₀ hb0 hpos).2 hn
    rw [one_div, inv_inv] at h4
    have h5 : max c 0 + 1 ≤ ‖W n‖ := by rw [hWnorm_eq n]; linarith
    linarith [le_max_left c 0]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, max (1 / r) (max 4 (4 * K)) < ‖W n‖ :=
    eventually_atTop.mp (hWnorm.eventually (eventually_gt_atTop _))
  have hrec : ∀ n : ℕ, W (n + 1) = wMap f (W n) := by
    intro n
    show -1 / (f^[n + 1] u) = wMap f (-1 / (f^[n] u))
    rw [Function.iterate_succ_apply', wMap_apply]
    congr 1
    field_simp
  -- the real part grows
  have hgrowth : ∀ n : ℕ, N ≤ n → (W n).re + 1 / 2 ≤ (W (n + 1)).re := by
    intro n hn
    have h1 := hN n hn
    have h2 : 1 / r < ‖W n‖ := lt_of_le_of_lt (le_max_left _ _) h1
    have h24 : (4 : ℝ) ≤ ‖W n‖ :=
      le_of_lt (lt_of_le_of_lt (le_trans (le_max_left 4 (4 * K)) (le_max_right _ _)) h1)
    have h4 := Repelling.near_translation_mod hb h2 h24
    have hpos : (0 : ℝ) < ‖W n‖ := by linarith
    have hKle : Estimate.Ksub A a / ‖W n‖ < 1 / 4 := by
      rw [div_lt_iff₀ hpos]
      have h5 : 4 * K < ‖W n‖ :=
        lt_of_le_of_lt (le_trans (le_max_right 4 (4 * K)) (le_max_right _ _)) h1
      linarith
    have h5 : |(wMap f (W n) - W n - 1).re| ≤ ‖wMap f (W n) - W n - 1‖ :=
      Complex.abs_re_le_norm _
    have h6 : |(wMap f (W n) - W n - 1).re| ≤ 1 / 4 := le_trans h5 (le_trans h4 hKle.le)
    have h7 : -(1 / 4 : ℝ) ≤ (wMap f (W n) - W n - 1).re := (abs_le.mp h6).1
    simp only [Complex.sub_re, Complex.one_re] at h7
    rw [hrec n]
    linarith
  have hre_growth : ∀ m : ℕ, (W N).re + (m : ℝ) / 2 ≤ (W (N + m)).re := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have h3 := hgrowth (N + m) (Nat.le_add_right N m)
        have heq : N + (m + 1) = (N + m) + 1 := by ring
        rw [heq]
        have h5 : (((m + 1 : ℕ)) : ℝ) / 2 = (m : ℝ) / 2 + 1 / 2 := by push_cast; ring
        rw [h5]
        linarith
  -- contradiction
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * (M - (W N).re) + 1)
  have hMm : M < (W (N + m)).re := by
    have h1 := hre_growth m
    have h2 : M - (W N).re < (m : ℝ) / 2 := by linarith
    linarith
  have h3 := hWle (N + m)
  rw [sgauge] at h3
  have h4 : (0 : ℝ) ≤ |(W (N + m)).im| := abs_nonneg _
  linarith

end

end Work.FatouCoord.Flower
