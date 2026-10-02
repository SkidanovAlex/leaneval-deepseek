import Mathlib
import Submission.Work.NAKANE2.Defs
import Submission.Work.NAKANE2.IFT.Basic
import Submission.Work.NAKANE2.Far.farTerm_differentiableAt_and_bound
import Submission.Work.NAKANE2.Far.norm_critZ_growth
import Submission.Work.Bottcher.Contraction.FarFoundation

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Strict differentiability of the Böttcher series in the parameter

`farSeries N = ∑' n, farTerm N · n` is a series of functions of the parameter `c` which are
real-smooth on the far region `{farRadius (‖c₀‖+1) < ‖critZ c₀ N‖}`.  We show that it is strictly
differentiable there, by combining the bound of `farTerm_differentiableAt_and_bound` with the
Weierstrass-type theorem `Work.NAKANE2.hasStrictFDerivAt_tsum_of_isPreconnected_real`.

The only non-trivial additional input is the *continuity* of the sum of the derivatives; we obtain
it from `tendstoUniformlyOn_tsum` (the bound is summable) together with the continuity of each
`c ↦ fderiv ℝ (farTerm N · n) c`, which follows from `ContDiffAt.continuousAt_fderiv` and the
fact that `farTerm N · n` is locally `C¹` on the far region (it is a composition of the smooth
`normFactor`, the smooth critical orbit and the complex logarithm on the slit plane).
-/

set_option maxHeartbeats 1000000

namespace Work.NAKANE2.FarN

open Filter Set
open scoped Topology
open Work.NAKANE2 (farTerm farSeries critZ)

noncomputable section

/-! ## Smoothness of the individual terms -/

theorem contDiff_critZ_param (k : ℕ) : ContDiff ℝ ⊤ (fun c : ℂ => critZ c k) := by
  induction k with
  | zero =>
    rw [show (fun c : ℂ => critZ c 0) = id from rfl]
    exact contDiff_id
  | succ k ih =>
    have h : (fun c : ℂ => critZ c (k + 1)) =
        fun c : ℂ => (critZ c k ^ 2 + (starRingEnd ℂ) c) ^ 2 + c := by
      funext c
      rw [critZ_succ, Work.Bottcher.pMap_apply]
    rw [h]
    have hc : ContDiff ℝ ⊤ (fun c : ℂ => (starRingEnd ℂ) c) := Complex.conjCLE.contDiff
    exact (((ih.pow 2).add hc).pow 2).add contDiff_id

/-- `3/2 (1 + x) ≤ farRadius (x + 1)` for `x ≥ 0`; this is the far condition required by
`summable_bottcherTerm_far` at the `N`-th critical-orbit point. -/
theorem three_halves_le_farRadius (x : ℝ) (hx : 0 ≤ x) :
    3 / 2 * (1 + x) ≤ Work.NAKANE.farRadius (x + 1) := by
  have hmax : max 2 (1 + (x + 1)) = x + 2 := by
    have h2 : (2 : ℝ) ≤ 1 + (x + 1) := by linarith
    rw [max_eq_right h2]
    ring
  rw [Work.NAKANE.farRadius, hmax]
  nlinarith [hx]

/-- On the far region, `c ↦ farTerm N c n` is (locally) `C¹`. -/
theorem contDiffAt_farTerm (N n : ℕ) {c : ℂ} (h1 : 1 + ‖c‖ ≤ ‖critZ c (N + n)‖) :
    ContDiffAt ℝ 1 (fun w : ℂ => farTerm N w n) c := by
  have hz : critZ c (N + n) ≠ 0 := by
    have : (0 : ℝ) < ‖critZ c (N + n)‖ := lt_of_lt_of_le (by linarith [norm_nonneg c]) h1
    exact norm_pos_iff.mp this
  have hψ : ContDiffAt ℝ ⊤ (fun w : ℂ => (w, critZ w (N + n))) c :=
    contDiffAt_id.prodMk ((contDiff_critZ_param (N + n)).contDiffAt)
  have hp1 : ContDiffAt ℝ ⊤ (fun p : ℂ × ℂ => p.1) (c, critZ c (N + n)) := by fun_prop
  have hp2 : ContDiffAt ℝ ⊤ (fun p : ℂ × ℂ => p.2) (c, critZ c (N + n)) := by fun_prop
  have hconj : ContDiffAt ℝ ⊤ (fun p : ℂ × ℂ => (starRingEnd ℂ) p.1) (c, critZ c (N + n)) := by
    have hc : ContDiff ℝ ⊤ (fun c : ℂ => (starRingEnd ℂ) c) := Complex.conjCLE.contDiff
    have h := (hc.contDiffAt).comp (c, critZ c (N + n)) hp1
    simpa [Function.comp_def] using h
  have hnum : ContDiffAt ℝ ⊤
      (fun p : ℂ × ℂ => (p.2 ^ 2 + (starRingEnd ℂ) p.1) ^ 2 + p.1) (c, critZ c (N + n)) :=
    (((hp2.pow 2).add hconj).pow 2).add hp1
  have hden : ContDiffAt ℝ ⊤ (fun p : ℂ × ℂ => p.2 ^ 4) (c, critZ c (N + n)) := hp2.pow 4
  have hden' : ContDiffAt ℝ ⊤ (fun p : ℂ × ℂ => (p.2 ^ 4)⁻¹) (c, critZ c (N + n)) :=
    hden.inv (by simpa using pow_ne_zero 4 hz)
  have hnf : ContDiffAt ℝ ⊤ (fun p : ℂ × ℂ => Work.Bottcher.normFactor p.1 p.2)
      (c, critZ c (N + n)) := by
    have h := hnum.mul hden'
    convert h using 1
    ext p
    simp only [Work.Bottcher.normFactor, Work.Bottcher.pMap_apply, div_eq_mul_inv]
  have hcomp : ContDiffAt ℝ ⊤ (fun w : ℂ => Work.Bottcher.normFactor w (critZ w (N + n))) c := by
    have h := hnf.comp c hψ
    simpa [Function.comp_def] using h
  have hslit : Work.Bottcher.normFactor c (critZ c (N + n)) ∈ Complex.slitPlane :=
    Work.Bottcher.Core.normFactor_mem_slitPlane c _ h1
  have hlogT : ContDiffAt ℝ ⊤
      (fun w : ℂ => Complex.log (Work.Bottcher.normFactor w (critZ w (N + n)))) c := by
    have h := ((Complex.contDiffAt_log hslit).restrict_scalars ℝ).comp c hcomp
    simpa [Function.comp_def] using h
  have hlog : ContDiffAt ℝ 1
      (fun w : ℂ => Complex.log (Work.Bottcher.normFactor w (critZ w (N + n)))) c :=
    hlogT.of_le le_top
  have hconst : ContDiffAt ℝ 1 (fun _ : ℂ => ((1 / 4 : ℝ) ^ (n + 1) : ℂ)) c := contDiffAt_const
  have hmul : ContDiffAt ℝ 1 (fun w : ℂ => ((1 / 4 : ℝ) ^ (n + 1) : ℂ) *
      Complex.log (Work.Bottcher.normFactor w (critZ w (N + n)))) c := hconst.mul hlog
  have hfun : (fun w : ℂ => farTerm N w n) = fun w : ℂ => ((1 / 4 : ℝ) ^ (n + 1) : ℂ) *
      Complex.log (Work.Bottcher.normFactor w (critZ w (N + n))) := by
    funext w
    simp only [farTerm, Work.Bottcher.bottcherTerm, pMap_iterate_critZ]
  rw [hfun]
  exact hmul

/-- Consequently the derivative of each term is continuous on any region where the far inequality
holds. -/
theorem continuousOn_fderiv_farTerm (N n : ℕ) {s : Set ℂ}
    (hs : ∀ c ∈ s, 1 + ‖c‖ ≤ ‖critZ c (N + n)‖) :
    ContinuousOn (fun c : ℂ => fderiv ℝ (fun w : ℂ => farTerm N w n) c) s :=
  fun c hc =>
    ((contDiffAt_farTerm N n (hs c hc)).continuousAt_fderiv (by norm_num)).continuousWithinAt

/-! ## The series -/

/-- **The Böttcher series is strictly differentiable in the parameter.** -/
theorem farSeries_hasStrictFDerivAt {N : ℕ} {c₀ : ℂ}
    (hfar : Work.NAKANE.farRadius (‖c₀‖ + 1) < ‖critZ c₀ N‖) :
    ∃ L : ℂ →L[ℝ] ℂ, HasStrictFDerivAt (farSeries N) L c₀ := by
  classical
  obtain ⟨δ, hδpos, C, _hC0, hbound⟩ :=
    Work.NAKANE2.Far.farTerm_differentiableAt_and_bound N hfar
  set B : ℝ := ‖c₀‖ + 1 with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hRge : B + 2 ≤ Work.NAKANE.farRadius B :=
    Work.NAKANE2.Far.critZGrowth_farRadius_ge B hB0
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.continuousAt_iff.mp
    ((Work.NAKANE2.Far.critZGrowth_continuous N).continuousAt (x := c₀))
    (‖critZ c₀ N‖ - Work.NAKANE.farRadius B) (by rw [hB]; linarith)
  set ε : ℝ := min δ (min δ₁ 1) with hε
  have hεpos : 0 < ε := lt_min hδpos (lt_min hδ₁pos one_pos)
  set s : Set ℂ := Metric.ball c₀ ε with hs
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεδ₁ : ε ≤ δ₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hε1 : ε ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hmem : ∀ c : ℂ, c ∈ s → ‖c - c₀‖ < ε := by
    intro c hc
    rwa [hs, Metric.mem_ball, dist_eq_norm] at hc
  have hfar_on : ∀ c ∈ s, ∀ n : ℕ, 1 + ‖c‖ ≤ ‖critZ c (N + n)‖ := by
    intro c hc n
    have hcδ : ‖c - c₀‖ < δ := lt_of_lt_of_le (hmem c hc) hεδ
    have hcδ₁ : ‖c - c₀‖ < δ₁ := lt_of_lt_of_le (hmem c hc) hεδ₁
    have hc1 : ‖c - c₀‖ < 1 := lt_of_lt_of_le (hmem c hc) hε1
    have hcB : ‖c‖ ≤ B := by
      have h1 : ‖c‖ ≤ ‖c₀‖ + ‖c - c₀‖ := by
        calc ‖c‖ = ‖(c - c₀) + c₀‖ := by ring_nf
          _ ≤ ‖c - c₀‖ + ‖c₀‖ := norm_add_le _ _
          _ = ‖c₀‖ + ‖c - c₀‖ := by ring
      rw [hB]; linarith
    have hR : Work.NAKANE.farRadius B ≤ ‖critZ c N‖ := by
      have h := hδ₁ (by rw [dist_eq_norm]; exact hcδ₁)
      rw [dist_eq_norm] at h
      have h2 : ‖critZ c₀ N‖ ≤ ‖critZ c N - critZ c₀ N‖ + ‖critZ c N‖ := by
        have hh := norm_add_le (critZ c₀ N - critZ c N) (critZ c N)
        rw [sub_add_cancel] at hh
        rwa [norm_sub_rev] at hh
      linarith
    have hbase : 2 + ‖c‖ ≤ ‖critZ c N‖ := by linarith
    have := Work.NAKANE2.Far.critZGrowth_two_add_le c N hbase n
    linarith
  have hx₀ : c₀ ∈ s := by rw [hs, Metric.mem_ball, dist_self]; exact hεpos
  have hs_open : IsOpen s := by rw [hs]; exact Metric.isOpen_ball
  have hs_pre : IsPreconnected s := by rw [hs]; exact Metric.isPreconnected_ball
  have hu : Summable (fun n : ℕ => C * (1 / 4 : ℝ) ^ n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left C
  have hf : ∀ n : ℕ, ∀ x ∈ s, HasFDerivAt (fun w : ℂ => farTerm N w n)
      (fderiv ℝ (fun w : ℂ => farTerm N w n) x) x := by
    intro n x hx
    exact ((hbound n x (lt_of_lt_of_le (hmem x hx) hεδ)).1).hasFDerivAt
  have hf' : ∀ n : ℕ, ∀ x ∈ s,
      ‖fderiv ℝ (fun w : ℂ => farTerm N w n) x‖ ≤ C * (1 / 4 : ℝ) ^ n := by
    intro n x hx
    exact (hbound n x (lt_of_lt_of_le (hmem x hx) hεδ)).2
  have hG : ∀ n : ℕ, ContinuousOn (fun x : ℂ => fderiv ℝ (fun w : ℂ => farTerm N w n) x) s :=
    fun n => continuousOn_fderiv_farTerm N n (fun c hc => hfar_on c hc n)
  have hcont : ContinuousOn
      (fun x : ℂ => ∑' n : ℕ, fderiv ℝ (fun w : ℂ => farTerm N w n) x) s := by
    have hunif := tendstoUniformlyOn_tsum (u := fun n : ℕ => C * (1 / 4 : ℝ) ^ n) hu
      (s := s) (f := fun (n : ℕ) (x : ℂ) => fderiv ℝ (fun w : ℂ => farTerm N w n) x) hf'
    refine hunif.continuousOn (Filter.Frequently.of_forall fun t => ?_)
    exact continuousOn_finsetSum t (fun n _ => hG n)
  have hf0 : Summable (fun n : ℕ => farTerm N c₀ n) := by
    have hz : 3 / 2 * (1 + ‖c₀‖) ≤ ‖critZ c₀ N‖ := by
      have h3 : 3 / 2 * (1 + ‖c₀‖) ≤ Work.NAKANE.farRadius (‖c₀‖ + 1) :=
        three_halves_le_farRadius _ (norm_nonneg c₀)
      rw [← hB] at h3
      linarith [hfar]
    exact Work.Bottcher.Contraction.summable_bottcherTerm_far c₀ (critZ c₀ N) hz
  refine ⟨∑' n : ℕ, fderiv ℝ (fun w : ℂ => farTerm N w n) c₀, ?_⟩
  have hmain := Work.NAKANE2.hasStrictFDerivAt_tsum_of_isPreconnected_real
    (α := ℕ) hu hs_open hs_pre hf hf' hcont hx₀ hf0 hx₀
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards with y
  exact (rfl : (∑' n : ℕ, farTerm N y n) = farSeries N y)

end

end Work.NAKANE2.FarN
