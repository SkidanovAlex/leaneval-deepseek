import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_XiAux
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhExplicit_XiStrip
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhExplicit_XiOrdLeZeta1
import Submission.Work.LinnikAreas.DhExplicit.zeta1_sphere_bound
import Submission.Commons.NumberTheory.Zeta.zeta1_re_two_lower
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
import Submission.Commons.NumberTheory.Zeta.zeta_norm_le_const_of_three_le_re
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity

open Complex Filter
open scoped Classical BigOperators Topology

noncomputable section

namespace Work.LinnikAreas.DhExplicit

open Work.LinnikAreas.DhK

set_option maxHeartbeats 1600000

/-!
# Unit-window zero count for `Ξ`

`Work.LinnikAreas.DhK.Xi` is the entire completion `Ξ(s) = 1/2 + (1/2)s(s-1)Λ₀(s)` of the Riemann
zeta function.  This is the *local* (Riemann–von Mangoldt) count for a unit window: there is an
absolute constant `C > 0` such that for every height `t : ℝ` and every finite set `S : Finset ℂ`
of points with `|u.im - t| ≤ 1`, the total vanishing order of `Ξ` over `S` is at most
`C (log (2 + |t|) + 2)`.

This is the exact analogue of `Work.LinnikAreas.FarRepel.window1_count`
(module `Submission.Work.LinnikAreas.FarRepel.zeroSumInvSqBound`, which CANNOT be imported here —
read and copy it; that module pulls in `completedL_pf_identity_rect`, whose `pfP` clashes with
`logDeriv_pf_identity`, already in the environment through `DhK.XiAux`).

Proof route (copying `window1_count`):
* For `u ∈ S` with `analyticOrderNatAt Xi u ≠ 0` one has `Ξ u = 0`, so `u` lies in the open
  critical strip `0 < Re u < 1` — `Work.LinnikAreas.DhExplicit.Xi_zero_strip` from the sibling
  module `Submission.Work.LinnikAreas.DhExplicit.XiStrip` (import it) — and hence in the closed
  disk of radius `23/10` about `c := 2 + t·I` (geometry: `(Re u - 2)^2 + (Im u - t)^2 < 4 + 1`).
* Jensen (`AnalyticOnNhd.sum_divisor_le`, module
  `Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity`) applied to the entire
  function `ζ₁ = riemannZeta₁` on the disk `closedBall c (5/2)` (the disk of radius `23/10` is
  strictly inside), using `|ζ₁ c| ≥ 1/4` (`Commons.NumberTheory.Zeta.zeta1_re_two_lower`, so
  `ζ₁ c ≠ 0`) and the upper bound `‖ζ₁ z‖ ≤ M` on the circle `‖z - c‖ = 5/2`: for `Re z ∈ [-1,3]`
  use `Commons.NumberTheory.Zeta.zeta_strip_polyGrowth`, for `Re z ≥ 3` use
  `Commons.NumberTheory.Zeta.zeta_norm_le_const_of_three_le_re`; the circle has `Re z ∈ [-1/2, 9/2]`
  and `|Im z| ≤ |t| + 5/2`, and `‖ζ₁ z‖ = ‖(z-1)ζ z‖ ≤ (|t| + 9)·‖ζ z‖`.
* Transfer to `Ξ` by the pointwise inequality `analyticOrderNatAt Xi u ≤ analyticOrderNatAt riemannZeta₁ u`
  (equality for zeros in the strip: locally `Ξ = (1/2)·s·Γ_ℝ·ζ₁`, see
  `Work.LinnikAreas.DhK.Xi_eq_half_mul`, `riemannZeta_def_of_ne_zero`, `Gammaℝ_ne_zero_of_re_pos`);
  the divisor sum of `ζ₁` over the ball bounds the sum of the vanishing orders of `ζ₁` over `S`.
* Absorb the constant term with `log (2 + |t|) + 2 ≥ 2 + log 2` (as `jensen_log_bound` does).
-/
/-- The logarithmic ratio appearing in Jensen's inequality is `O(log M)`. -/
lemma xiUnitWindow_jensen_log_bound (M m : ℝ) (hM : 1 ≤ M) (hmlo : (1:ℝ)/4 ≤ m) :
    Real.log (M / m) / Real.log ((5:ℝ)/2 / (23/10))
      ≤ 12.5 * (Real.log M + Real.log 4) := by
  have hmp : 0 < m := lt_of_lt_of_le (by norm_num) hmlo
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hratio : Real.log ((5:ℝ)/2 / (23/10)) ≥ 2/25 := by
    have heq : ((5:ℝ)/2 / (23/10)) = 25/23 := by norm_num
    rw [heq]
    have h2 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 23/25 by norm_num)
    have h3 : Real.log (23/25) = - Real.log (25/23) := by
      rw [show (23:ℝ)/25 = (25/23)⁻¹ by norm_num, Real.log_inv]
    linarith
  have hpos : 0 < Real.log ((5:ℝ)/2 / (23/10)) := by linarith
  have hK : (1:ℝ) / Real.log ((5:ℝ)/2 / (23/10)) ≤ 25/2 := by
    rw [div_le_iff₀ hpos]
    linarith
  have hnum : Real.log (M / m) ≤ Real.log M + Real.log 4 := by
    rw [Real.log_div (ne_of_gt hMpos) (ne_of_gt hmp)]
    have h1 : Real.log ((1:ℝ)/4) ≤ Real.log m := Real.log_le_log (by norm_num) hmlo
    have h2 : Real.log ((1:ℝ)/4) = - Real.log 4 := by
      rw [show ((1:ℝ)/4) = (4:ℝ)⁻¹ by norm_num, Real.log_inv]
    linarith
  have hA : 0 ≤ Real.log M + Real.log 4 := by
    have h1 : 0 ≤ Real.log M := Real.log_nonneg hM
    have h2 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  calc Real.log (M / m) / Real.log ((5:ℝ)/2 / (23/10))
      ≤ (Real.log M + Real.log 4) / Real.log ((5:ℝ)/2 / (23/10)) :=
        div_le_div_of_nonneg_right hnum (le_of_lt hpos)
    _ = (Real.log M + Real.log 4) * (1 / Real.log ((5:ℝ)/2 / (23/10))) := by ring
    _ ≤ (Real.log M + Real.log 4) * (25/2) := mul_le_mul_of_nonneg_left hK hA
    _ = 12.5 * (Real.log M + Real.log 4) := by ring

theorem XiUnitWindowCount : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ∀ S : Finset ℂ,
    (∀ u ∈ S, |u.im - t| ≤ 1) →
    ∑ u ∈ S, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ)
      ≤ C * (Real.log (2 + |t|) + 2) := by
  obtain ⟨K, hK1, hKsph⟩ := zeta1_sphere_bound
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨12.5 * (20 + Real.log K + Real.log 4) + 63, by linarith, ?_⟩
  intro t S hS
  set c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ) with hc
  set S' : Finset ℂ := S.filter (fun u => analyticOrderNatAt Xi u ≠ 0) with hS'
  have hsumS : ∑ u ∈ S, (analyticOrderNatAt Xi u : ℝ)
      = ∑ u ∈ S', (analyticOrderNatAt Xi u : ℝ) := by
    rw [hS', Finset.sum_filter]
    apply Finset.sum_congr rfl; intro u _
    by_cases h : analyticOrderNatAt Xi u ≠ 0
    · rw [if_pos h]
    · rw [if_neg h, not_not.mp h]; simp
  rw [hsumS]
  have hstripS : ∀ u ∈ S', 0 < u.re ∧ u.re < 1 := by
    intro u hu
    have hne : analyticOrderNatAt Xi u ≠ 0 := (Finset.mem_filter.mp hu).2
    exact Xi_zero_strip (apply_eq_zero_of_analyticOrderNatAt_ne_zero hne)
  have hmem_ball : ∀ u ∈ S', u ∈ Metric.closedBall c (23/10) := by
    intro u hu
    obtain ⟨h0, h1⟩ := hstripS u hu
    have him : |u.im - t| ≤ 1 := hS u (Finset.mem_filter.mp hu).1
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsq : ‖u - c‖ ^ 2 = (u.re - 2) ^ 2 + (u.im - t) ^ 2 := by
      have hre : (u - c).re = u.re - 2 := by simp [hc]
      have him' : (u - c).im = u.im - t := by simp [hc]
      rw [Complex.sq_norm, Complex.normSq_apply, hre, him']; ring
    have h2 : ‖u - c‖ ^ 2 < (23/10) ^ 2 := by
      rw [hsq]
      have h3 := abs_le.mp him
      nlinarith [h0, h1, h3.1, h3.2]
    nlinarith [norm_nonneg (u - c)]
  have hΓlower : (1:ℝ)/4 ≤ ‖riemannZeta₁ c‖ := by
    have h := Commons.NumberTheory.Zeta.zeta1_re_two_lower t
    simpa [hc] using h
  have hjensen : ∀ M : ℝ, 1 ≤ M → (∀ z ∈ Metric.sphere c |(5:ℝ)/2|, ‖riemannZeta₁ z‖ ≤ M) →
      ∑ u ∈ S', (analyticOrderNatAt Xi u : ℝ)
        ≤ Real.log (M / ‖riemannZeta₁ c‖) / Real.log ((5:ℝ)/2 / (23/10)) := by
    intro M hM hbound
    have hΓpos : 0 < ‖riemannZeta₁ c‖ := lt_of_lt_of_le (by norm_num) hΓlower
    have hcne : riemannZeta₁ c ≠ 0 := fun h0 => by rw [h0] at hΓpos; simp at hΓpos
    have hAnal : AnalyticOnNhd ℂ riemannZeta₁ (Metric.closedBall c |(5:ℝ)/2|) :=
      fun z _ => differentiable_riemannZeta₁.analyticAt z
    have hJ := AnalyticOnNhd.sum_divisor_le (c := c) (r := (23:ℝ)/10) (R := (5:ℝ)/2) (M := M)
      (f := riemannZeta₁) (r_pos := by norm_num) (r_lt_R := by norm_num) (hM := hM)
      (h₁f := hAnal) (h₂f := hcne) (f_bound := hbound)
    have hJ' : ↑(∑ᶠ u : ℂ, (MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c (23/10))) u)
        ≤ Real.log (M / ‖riemannZeta₁ c‖) / Real.log ((5:ℝ)/2 / (23/10)) := by
      rw [show |(23:ℝ)/10| = 23/10 by norm_num] at hJ
      exact hJ
    have hfin : (Function.support (fun u : ℂ =>
        (MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c (23/10))) u)).Finite :=
      (MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c (23/10))).finiteSupport
        (isCompact_closedBall c (23/10))
    have hmem : ∀ u : ℂ, u ∈ hfin.toFinset ↔
        (MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c (23/10))) u ≠ 0 :=
      fun u => Set.Finite.mem_toFinset hfin
    have hval : ∀ u ∈ Metric.closedBall c (23/10),
        (MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c (23/10))) u
          = (analyticOrderNatAt riemannZeta₁ u : ℤ) := fun u hu =>
      Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast
        (fun z _ => differentiable_riemannZeta₁.analyticAt z) hu
    have hfinsum_eq : (∑ᶠ u : ℂ, (MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c (23/10))) u)
        = ∑ u ∈ hfin.toFinset, (MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c (23/10))) u := by
      refine finsum_eq_sum_of_support_subset _ ?_
      intro u hu
      rw [Function.mem_support] at hu
      exact (hmem u).mpr hu
    have hsub : S' ⊆ hfin.toFinset := by
      intro u hu
      have hne : analyticOrderNatAt Xi u ≠ 0 := (Finset.mem_filter.mp hu).2
      have hlt : 0 < analyticOrderNatAt riemannZeta₁ u :=
        lt_of_lt_of_le (Nat.pos_of_ne_zero hne) (XiOrdLeZeta1 u)
      refine (hmem u).mpr ?_
      rw [hval u (hmem_ball u hu)]
      exact_mod_cast hlt.ne'
    have hle : ∀ u ∈ S', (analyticOrderNatAt Xi u : ℝ)
        ≤ (((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c (23/10))) u : ℤ) : ℝ) := by
      intro u hu
      rw [hval u (hmem_ball u hu)]
      exact_mod_cast XiOrdLeZeta1 u
    have hDnn : ∀ u ∈ hfin.toFinset, u ∉ S' →
        0 ≤ (((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c (23/10))) u : ℤ) : ℝ) := by
      intro u hu _
      by_cases huc : u ∈ Metric.closedBall c (23/10)
      · rw [hval u huc]; exact_mod_cast Nat.cast_nonneg _
      · have h0 : (MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c (23/10))) u = 0 := by
          rw [MeromorphicOn.divisor_def, if_neg]
          exact fun hc' => huc hc'.2
        rw [h0]; simp
    have hfin_eq : ∑ u ∈ hfin.toFinset,
          (((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c (23/10))) u : ℤ) : ℝ)
        = ((∑ᶠ u : ℂ, (MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c (23/10))) u : ℤ) : ℝ) := by
      have h1 : ((∑ u ∈ hfin.toFinset, (MeromorphicOn.divisor riemannZeta₁
          (Metric.closedBall c (23/10))) u : ℤ) : ℝ)
          = ∑ u ∈ hfin.toFinset, (((MeromorphicOn.divisor riemannZeta₁
            (Metric.closedBall c (23/10))) u : ℤ) : ℝ) :=
        map_sum (Int.castRingHom ℝ) _ hfin.toFinset
      rw [← h1, hfinsum_eq]
    exact le_trans (le_trans (Finset.sum_le_sum hle)
      (Finset.sum_le_sum_of_subset_of_nonneg hsub hDnn)) (le_trans (le_of_eq hfin_eq) hJ')
  -- the circle bound
  set M : ℝ := K * (|t| + 9) ^ 5 with hMdef
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    have h1 : (1:ℝ) ≤ (|t| + 9) ^ 5 := one_le_pow₀ (by linarith [abs_nonneg t])
    nlinarith [hK1, h1, hKpos]
  have hbd : ∀ z ∈ Metric.sphere c |(5:ℝ)/2|, ‖riemannZeta₁ z‖ ≤ M := by
    intro z hz
    have hzn : ‖z - c‖ = 5/2 := by
      have h := hz
      rw [Metric.mem_sphere, dist_eq_norm] at h
      rw [h, abs_of_pos (by norm_num : (0:ℝ) < 5/2)]
    rw [hMdef]
    exact hKsph t z (by rw [← hc]; exact hzn)
  have h1 := hjensen M hM1 hbd
  have h2 := xiUnitWindow_jensen_log_bound M ‖riemannZeta₁ c‖ hM1 hΓlower
  have hlogM : Real.log M = Real.log K + 5 * Real.log (|t| + 9) := by
    rw [hMdef, Real.log_mul (ne_of_gt hKpos) (by positivity), Real.log_pow]
    push_cast; ring
  set L : ℝ := Real.log (2 + |t|) + 2 with hLdef
  set A : ℝ := 12.5 * (Real.log K + Real.log 4) with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; linarith
  have hL0 : 0 ≤ L := by
    rw [hLdef]; have := Real.log_nonneg (by linarith [abs_nonneg t] : (1:ℝ) ≤ 2 + |t|); linarith
  have hL1 : 1 ≤ L := by
    rw [hLdef]; have := Real.log_nonneg (by linarith [abs_nonneg t] : (1:ℝ) ≤ 2 + |t|); linarith
  have hlog93 : Real.log (|t| + 9) ≤ L + 2 := by
    have hle : |t| + 9 ≤ (2 + |t|) * 9 := by linarith [abs_nonneg t]
    have h1 : Real.log (|t| + 9) ≤ Real.log ((2 + |t|) * 9) :=
      Real.log_le_log (by positivity) hle
    rw [Real.log_mul (by positivity) (by norm_num)] at h1
    have h2 : Real.log 9 ≤ 4 := by
      have h3 : Real.log 9 = 2 * Real.log 3 := by
        rw [show (9:ℝ) = 3 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
        ring
      have h4 : Real.log 3 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num); linarith
      linarith
    rw [hLdef]; linarith
  have hstep : 12.5 * (Real.log K + 5 * (L + 2) + Real.log 4) = A + 62.5 * L + 125 := by
    rw [hAdef]; ring
  have hgoal : A + 62.5 * L + 125 ≤ (12.5 * (20 + Real.log K + Real.log 4) + 63) * L := by
    have h313 : 12.5 * (20 + Real.log K + Real.log 4) + 63 = A + 313 := by
      rw [hAdef]; ring
    rw [h313]
    nlinarith [hL1, hA0]
  calc ∑ u ∈ S', (analyticOrderNatAt Xi u : ℝ)
      ≤ Real.log (M / ‖riemannZeta₁ c‖) / Real.log ((5:ℝ)/2 / (23/10)) := h1
    _ ≤ 12.5 * (Real.log M + Real.log 4) := h2
    _ ≤ 12.5 * (Real.log K + 5 * (L + 2) + Real.log 4) := by
        have h3 : Real.log M ≤ Real.log K + 5 * (L + 2) := by rw [hlogM]; linarith [hlog93]
        linarith
    _ = A + 62.5 * L + 125 := hstep
    _ ≤ (12.5 * (20 + Real.log K + Real.log 4) + 63) * L := hgoal


end Work.LinnikAreas.DhExplicit
