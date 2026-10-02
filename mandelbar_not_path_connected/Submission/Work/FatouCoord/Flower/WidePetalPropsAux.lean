/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoord team
-/
import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Flower.GermDefs
import Submission.Work.FatouCoord.Flower.widePetal_growth

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The wide petal: openness, connectedness, invariance and escape (auxiliary copy)

This is a verbatim copy of `Submission/Work/FatouCoord/Flower/widePetal_props.lean` placed in
the namespace `Work.FatouCoord.Flower.WPA`.

The copy exists because the lemma `neg_one_div_neg_one_div` is declared in *both*
`Flower/widePetal_props.lean` and `Flower/exists_anti_shift.lean` with the same full name
`Work.FatouCoord.Flower.neg_one_div_neg_one_div`, so the two modules cannot be imported into
the same file.  `Work.FatouCoord.Flower.germ_parabolicFlower` needs the properties of the wide
petal *and* `exists_anti_shift`; this namespace-separated copy breaks the clash.
-/

open scoped Topology
open Set Filter Metric Function

namespace Work.FatouCoord.Flower.WPA

open Work.FatouCoord

noncomputable section

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}

theorem continuous_sgauge : Continuous sgauge := by
  unfold sgauge
  fun_prop

theorem isOpen_sgauge_gt (M : ℝ) : IsOpen {W : ℂ | M < sgauge W} :=
  isOpen_lt continuous_const continuous_sgauge

theorem sgauge_le_sqrt_two_norm (W : ℂ) : sgauge W ≤ Real.sqrt 2 * ‖W‖ := by
  have hsharp : (sgauge W) ^ 2 ≤ 2 * ‖W‖ ^ 2 := by
    rw [sgauge, Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_abs W.re, sq_abs W.im, abs_nonneg W.im, le_abs_self W.re, neg_abs_le W.re,
      sq_nonneg (W.re - |W.im|)]
  have hb : (Real.sqrt 2 * ‖W‖) ^ 2 = 2 * ‖W‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hb0 : 0 ≤ Real.sqrt 2 * ‖W‖ := by positivity
  by_cases h : 0 ≤ sgauge W
  · nlinarith [hsharp, hb, hb0, h]
  · linarith

theorem neg_one_div_neg_one_div {u : ℂ} (hu : u ≠ 0) : -1 / (-1 / u) = u := by
  field_simp

theorem WidePetal_eq_sgauge {M : ℝ} (hM : 0 < M) :
    WidePetal M = {u : ℂ | M < sgauge (-1 / u)} := by
  ext u
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    intro hu
    rw [hu] at h
    simp [sgauge] at h
    linarith

theorem WidePetal_eq_image {M : ℝ} (hM : 0 < M) :
    WidePetal M = (fun W : ℂ => -1 / W) '' {W : ℂ | M < sgauge W} := by
  rw [WidePetal_eq_sgauge hM]
  ext u
  constructor
  · intro h
    refine ⟨-1 / u, h, ?_⟩
    exact neg_one_div_neg_one_div (fun hu => by
      rw [hu] at h
      simp [sgauge] at h
      linarith)
  · rintro ⟨W, hW, rfl⟩
    change M < sgauge (-1 / (-1 / W))
    rw [neg_one_div_neg_one_div (fun h0 => by
      rw [h0] at hW
      simp [sgauge] at hW
      linarith)]
    exact hW

theorem widePetal_open (M : ℝ) : IsOpen (WidePetal M) := by
  rw [isOpen_iff_mem_nhds]
  intro u hu
  obtain ⟨hu0, hMu⟩ := hu
  have hcont : ContinuousAt (fun u : ℂ => (-1 : ℂ) / u) u :=
    continuousAt_const.div continuousAt_id hu0
  have h1 : (fun u : ℂ => (-1 : ℂ) / u) ⁻¹' {W : ℂ | M < sgauge W} ∈ nhds u :=
    hcont.preimage_mem_nhds ((isOpen_sgauge_gt M).mem_nhds hMu)
  have h2 : {u : ℂ | u ≠ 0} ∈ nhds u :=
    isOpen_compl_singleton.mem_nhds (by simpa using hu0)
  have h3 : WidePetal M
      = {u : ℂ | u ≠ 0} ∩ (fun u : ℂ => (-1 : ℂ) / u) ⁻¹' {W : ℂ | M < sgauge W} := by
    ext v
    simp only [WidePetal, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
  rw [h3]
  exact Filter.inter_mem h2 h1

theorem widePetal_preconnected (M : ℝ) (hM : 0 < M) : IsPreconnected (WidePetal M) := by
  rw [WidePetal_eq_image hM]
  exact (isPreconnected_sgauge_gt M).image (fun W : ℂ => -1 / W)
    (continuousOn_const.div continuousOn_id (fun x hx => by
      intro h0; rw [h0] at hx; simp [sgauge] at hx; linarith))

theorem zero_notMem_widePetal (M : ℝ) : (0 : ℂ) ∉ WidePetal M := fun h => h.1 rfl

theorem widePetal_subset_ball (M : ℝ) (hM : 0 < M) :
    WidePetal M ⊆ ball 0 (Real.sqrt 2 / M) := by
  intro u hu
  obtain ⟨hu0, h⟩ := hu
  have hW0 : (-1 / u : ℂ) ≠ 0 := fun h0 => by
    rw [h0] at h; simp [sgauge] at h; linarith
  have hsqrt2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h1 : M < Real.sqrt 2 * ‖(-1 / u : ℂ)‖ :=
    lt_of_lt_of_le h (sgauge_le_sqrt_two_norm _)
  have h2 : M / Real.sqrt 2 < ‖(-1 / u : ℂ)‖ := by
    rw [div_lt_iff₀ hsqrt2pos]
    rwa [mul_comm]
  have hnorm : ‖u‖ = 1 / ‖(-1 / u : ℂ)‖ := by
    have h3 : ‖(-1 / u : ℂ)‖ = (‖u‖)⁻¹ := by
      rw [← norm_chart hu0]; rfl
    rw [h3, one_div, inv_inv]
  rw [mem_ball_zero_iff, hnorm]
  calc 1 / ‖(-1 / u : ℂ)‖ < 1 / (M / Real.sqrt 2) :=
        one_div_lt_one_div_of_lt (by positivity) h2
    _ = Real.sqrt 2 / M := by field_simp

theorem widePetal_mapsTo {M : ℝ} (hM : 0 ≤ M)
    (hgr : ∀ W : ℂ, M < sgauge W → M < sgauge (wMap f W)) :
    MapsTo f (WidePetal M) (WidePetal M) := by
  intro u hu
  obtain ⟨hu0, h⟩ := hu
  have h1 : sgauge (-1 / f u) = sgauge (wMap f (-1 / u)) := by
    rw [wMap_apply, neg_one_div_neg_one_div hu0]
  have h2 : M < sgauge (-1 / f u) := by rw [h1]; exact hgr _ h
  refine ⟨?_, h2⟩
  intro hf0
  rw [hf0] at h2
  simp [sgauge] at h2
  linarith

theorem widePetal_tendsto {M : ℝ} (hM : 0 ≤ M)
    (hgr : ∀ W : ℂ, M < sgauge W → M < sgauge (wMap f W) ∧ (wMap f W).re ≥ W.re + 1 / 2) :
    ∀ u ∈ WidePetal M, Tendsto (fun n : ℕ => f^[n] u) atTop (nhds 0) := by
  intro u hu
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hmaps : MapsTo f (WidePetal M) (WidePetal M) :=
    widePetal_mapsTo hM0 (fun W hW => (hgr W hW).1)
  have hmem : ∀ n : ℕ, f^[n] u ∈ WidePetal M := fun n => mapsTo_iterate_of_mapsTo hmaps n hu
  set W : ℕ → ℂ := fun n => -1 / (f^[n] u) with hWdef
  have hW_ne : ∀ n : ℕ, f^[n] u ≠ 0 := fun n => (hmem n).1
  have hWmem : ∀ n : ℕ, M < sgauge (W n) := fun n => (hmem n).2
  have hrec : ∀ n : ℕ, W (n + 1) = wMap f (W n) := by
    intro n
    simp only [hWdef]
    rw [Function.iterate_succ_apply', wMap_apply, neg_one_div_neg_one_div (hW_ne n)]
  have hre : ∀ n : ℕ, (W 0).re + (n : ℝ) / 2 ≤ (W n).re := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have h1 := (hgr (W n) (hWmem n)).2
        rw [← hrec n] at h1
        have h2 : (((n : ℕ) + 1 : ℕ) : ℝ) / 2 = (n : ℝ) / 2 + 1 / 2 := by push_cast; ring
        rw [h2]
        linarith
  have hnormW : ∀ n : ℕ, ‖f^[n] u‖ = 1 / ‖W n‖ := by
    intro n
    have h3 : ‖W n‖ = (‖f^[n] u‖)⁻¹ := by
      rw [← norm_chart (hW_ne n)]; rfl
    rw [h3, one_div, inv_inv]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (|(W 0).re| + 1 / ε + 1))
  refine ⟨N, fun n hn => ?_⟩
  have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hge : 1 / ε < (W n).re := by
    have h1 := hre n
    have h2 : |(W 0).re| + 1 / ε + 1 < (N : ℝ) / 2 := by linarith
    have h3 : -|(W 0).re| ≤ (W 0).re := neg_abs_le _
    nlinarith
  have hposW : 0 < (W n).re := lt_trans (by positivity) hge
  have hWnorm_ge : (W n).re ≤ ‖W n‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
  have hlt : 1 / ‖W n‖ < ε := by
    have h1 : 0 < ‖W n‖ := lt_of_lt_of_le hposW hWnorm_ge
    rw [div_lt_iff₀ h1]
    calc 1 < ε * (W n).re := by
          have h2 := mul_lt_mul_of_pos_left hge hε
          rw [mul_one_div, div_self (ne_of_gt hε)] at h2
          exact h2
      _ ≤ ε * ‖W n‖ := mul_le_mul_of_nonneg_left hWnorm_ge hε.le
  rw [dist_zero_right, hnormW n]
  exact hlt

theorem widePetal_props (hb : ParabolicBounds f h a r A A')
    {M : ℝ} (hM : 1 ≤ M) (hMr : 1 / r < M)
    (hgr : ∀ W : ℂ, M < sgauge W →
      M < sgauge (wMap f W) ∧ (wMap f W).re ≥ W.re + 1 / 2) :
    IsOpen (WidePetal M) ∧ IsPreconnected (WidePetal M) ∧ (0 : ℂ) ∉ WidePetal M ∧
    MapsTo f (WidePetal M) (WidePetal M) ∧
    (∀ u ∈ WidePetal M, Tendsto (fun n : ℕ => f^[n] u) atTop (nhds 0)) ∧
    WidePetal M ⊆ ball 0 (Real.sqrt 2 / M) :=
  ⟨widePetal_open M, widePetal_preconnected M (by linarith),
    zero_notMem_widePetal M, widePetal_mapsTo (by linarith) (fun W hW => (hgr W hW).1),
    widePetal_tendsto (by linarith) hgr, widePetal_subset_ball M (by linarith)⟩

end

end Work.FatouCoord.Flower.WPA
