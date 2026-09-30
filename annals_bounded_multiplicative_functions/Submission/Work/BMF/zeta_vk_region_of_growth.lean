import Mathlib
import Submission.Work.BMF.VKdenom
import Submission.Work.BMF.zeta_arc_cost_def
import Submission.Work.BMF.zeta_sphere_avoid
import Submission.Work.BMF.zeta_zeroFree_compact
import Submission.Work.BMF.zeta_logDeriv_341
import Submission.Work.BMF.zeta_circle_zeta_lower
import Submission.Work.BMF.zeta_circle_arc_A
import Submission.Work.BMF.zeta_circle_cos_weight
import Submission.Work.BMF.zeta_circle_regionB_pointwise
import Submission.Work.BMF.zeta_circle_regionC_pointwise
import Submission.Work.BMF.zeta_vk_arith
import Submission.Work.BMF.zeta_logDeriv_bound_vk
import Submission.Commons.Analysis.Complex.jensenCarleman
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Complex Metric
open scoped Real Topology BigOperators
open MeasureTheory

noncomputable section




set_option maxHeartbeats 4000000

/-- `ζ` is analytic on a closed disc avoiding `1`. -/
private lemma analyticOnNhd_zeta_closedBall {a : ℂ} {R : ℝ}
    (h1 : 1 ∉ Metric.closedBall a |R|) :
    AnalyticOnNhd ℂ riemannZeta (Metric.closedBall a |R|) :=
  analyticOn_riemannZeta.mono (fun z hz => by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    exact h1 (h ▸ hz))

private lemma riemannZeta_ne_zero_fn : riemannZeta ≠ 0 := by
  intro h
  have h2 : riemannZeta 2 = 0 := by rw [h]; rfl
  exact riemannZeta_ne_zero_of_one_le_re (s := (2 : ℂ)) (by norm_num) h2

/-- The Jensen–Carleman divisor sum is `≤ 0` when every interior zero of `f` lies strictly to the
left of the centre. -/
private lemma finsum_divisor_nonpos {f : ℂ → ℂ} {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall a |R|))
    (ha : f a ≠ 0) (hsphere : ∀ u : ℂ, ‖u - a‖ = R → f u ≠ 0)
    (hleft : ∀ u : ℂ, f u = 0 → u ∈ Metric.closedBall a |R| → u.re < a.re) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall a |R|)) u : ℤ) : ℝ) *
        (u - a).re * ((‖u - a‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹)) ≤ 0 := by
  set F : ℂ → ℝ := fun u =>
    (((MeromorphicOn.divisor f (Metric.closedBall a |R|)) u : ℤ) : ℝ) *
      (u - a).re * ((‖u - a‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹) with hF
  have hRR : R⁻¹ * R⁻¹ = (R ^ 2)⁻¹ := by rw [sq, mul_inv]
  have hle0 : ∀ u : ℂ, F u ≤ 0 := by
    intro u
    by_cases hd : (MeromorphicOn.divisor f (Metric.closedBall a |R|)) u = 0
    · simp [hF, hd]
    · have hmem : u ∈ Metric.closedBall a |R| :=
        (MeromorphicOn.divisor f (Metric.closedBall a |R|)).supportWithinDomain hd
      have hfu : f u = 0 := by
        by_contra hfu
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hmem] at hd
        simp [analyticOrderAt_eq_zero.mpr (Or.inr hfu)] at hd
      have hre : (u - a).re < 0 := by
        have h := hleft u hfu hmem
        simpa using sub_neg.mpr h
      have hleR : ‖u - a‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm, abs_of_pos hR] using hmem
      have hnormlt : ‖u - a‖ < R := lt_of_le_of_ne hleR (fun h => hsphere u h hfu)
      have hcoef : 0 < (‖u - a‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹ := by
        rw [hRR]
        have hne : u ≠ a := fun h => ha (h ▸ hfu)
        have hp : 0 < ‖u - a‖ ^ 2 := by
          have : 0 < ‖u - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
          positivity
        have hR2 : 0 < R ^ 2 := by positivity
        have hlt : ‖u - a‖ ^ 2 < R ^ 2 := by nlinarith [norm_nonneg (u - a), hR]
        have := (inv_lt_inv₀ hR2 hp).mpr hlt
        linarith
      have hdivnn : (0 : ℤ) ≤ (MeromorphicOn.divisor f (Metric.closedBall a |R|)) u := by
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hmem]
        cases h : analyticOrderAt f u with
        | top => simp
        | coe n => simp
      have hdivpos : (0 : ℝ) < (((MeromorphicOn.divisor f (Metric.closedBall a |R|)) u : ℤ) : ℝ) := by
        have : (0 : ℤ) < (MeromorphicOn.divisor f (Metric.closedBall a |R|)) u :=
          lt_of_le_of_ne hdivnn (Ne.symm hd)
        exact_mod_cast this
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hdivpos.le hre.le) hcoef.le
  have hfin : (MeromorphicOn.divisor f (Metric.closedBall a |R|)).support.Finite :=
    (MeromorphicOn.divisor f (Metric.closedBall a |R|)).finiteSupport (isCompact_closedBall a |R|)
  rw [finsum_eq_sum_of_support_subset F (s := hfin.toFinset) (by
    intro u hu
    have hd : (MeromorphicOn.divisor f (Metric.closedBall a |R|)) u ≠ 0 := by
      intro h0
      exact (Function.mem_support.mp hu) (by simp [hF, h0])
    exact (Set.Finite.mem_toFinset hfin).mpr (Function.mem_support.mpr hd))]
  exact Finset.sum_nonpos (fun u _ => hle0 u)

/-- The Jensen–Carleman divisor sum is bounded by the single term of a given interior zero `ρ`
(of multiplicity at least one). -/
private lemma finsum_divisor_le_zero_term {f : ℂ → ℂ} {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall a |R|))
    (ha : f a ≠ 0) (hsphere : ∀ u : ℂ, ‖u - a‖ = R → f u ≠ 0)
    (hleft : ∀ u : ℂ, f u = 0 → u ∈ Metric.closedBall a |R| → u.re < a.re)
    {ρ : ℂ} (hρ : f ρ = 0) (hρin : ρ ∈ Metric.closedBall a |R|)
    (hρd : (1 : ℤ) ≤ MeromorphicOn.divisor f (Metric.closedBall a |R|) ρ) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall a |R|)) u : ℤ) : ℝ) *
        (u - a).re * ((‖u - a‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹)) ≤
      (ρ - a).re * ((‖ρ - a‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹) := by
  set F : ℂ → ℝ := fun u =>
    (((MeromorphicOn.divisor f (Metric.closedBall a |R|)) u : ℤ) : ℝ) *
      (u - a).re * ((‖u - a‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹) with hF
  have hRR : R⁻¹ * R⁻¹ = (R ^ 2)⁻¹ := by rw [sq, mul_inv]
  have hfin : (MeromorphicOn.divisor f (Metric.closedBall a |R|)).support.Finite :=
    (MeromorphicOn.divisor f (Metric.closedBall a |R|)).finiteSupport (isCompact_closedBall a |R|)
  have hsupp : Function.support F ⊆ ↑(hfin.toFinset) := by
    intro u hu
    have hd : (MeromorphicOn.divisor f (Metric.closedBall a |R|)) u ≠ 0 := by
      intro h0
      exact (Function.mem_support.mp hu) (by simp [hF, h0])
    exact (Set.Finite.mem_toFinset hfin).mpr (Function.mem_support.mpr hd)
  have hle0 : ∀ u : ℂ, F u ≤ 0 := by
    intro u
    by_cases hd : (MeromorphicOn.divisor f (Metric.closedBall a |R|)) u = 0
    · simp [hF, hd]
    · have hmem : u ∈ Metric.closedBall a |R| :=
        (MeromorphicOn.divisor f (Metric.closedBall a |R|)).supportWithinDomain hd
      have hfu : f u = 0 := by
        by_contra hfu
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hmem] at hd
        simp [analyticOrderAt_eq_zero.mpr (Or.inr hfu)] at hd
      have hre : (u - a).re < 0 := by
        have h := hleft u hfu hmem
        simpa using sub_neg.mpr h
      have hleR : ‖u - a‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm, abs_of_pos hR] using hmem
      have hnormlt : ‖u - a‖ < R := lt_of_le_of_ne hleR (fun h => hsphere u h hfu)
      have hne : u ≠ a := fun h => ha (h ▸ hfu)
      have hcoef : 0 ≤ (‖u - a‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹ := by
        rw [hRR]
        have hp : 0 < ‖u - a‖ ^ 2 := by
          have : 0 < ‖u - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
          positivity
        have hR2 : 0 < R ^ 2 := by positivity
        have hlt : ‖u - a‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg (u - a), hR]
        exact sub_nonneg.mpr ((inv_le_inv₀ hR2 hp).mpr hlt)
      have hdivnn : (0 : ℤ) ≤ (MeromorphicOn.divisor f (Metric.closedBall a |R|)) u := by
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hmem]
        cases h : analyticOrderAt f u with
        | top => simp
        | coe n => simp
      have hdivpos : (0 : ℝ) ≤ (((MeromorphicOn.divisor f (Metric.closedBall a |R|)) u : ℤ) : ℝ) := by
        exact_mod_cast hdivnn
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hdivpos hre.le) hcoef
  -- the target product is `≤ 0`
  have hXnonpos : (ρ - a).re * ((‖ρ - a‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹) ≤ 0 := by
    have hre : (ρ - a).re < 0 := by
      have h := hleft ρ hρ hρin
      simpa using sub_neg.mpr h
    have hleR : ‖ρ - a‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm, abs_of_pos hR] using hρin
    have hcoef : 0 ≤ (‖ρ - a‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹ := by
      rw [hRR]
      have hne : ρ ≠ a := fun h => ha (h ▸ hρ)
      have hp : 0 < ‖ρ - a‖ ^ 2 := by
        have : 0 < ‖ρ - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
        positivity
      have hR2 : 0 < R ^ 2 := by positivity
      have hlt : ‖ρ - a‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg (ρ - a), hR]
      exact sub_nonneg.mpr ((inv_le_inv₀ hR2 hp).mpr hlt)
    exact mul_nonpos_of_nonpos_of_nonneg hre.le hcoef
  rw [finsum_eq_sum_of_support_subset F (s := hfin.toFinset) hsupp]
  by_cases hρs : ρ ∈ hfin.toFinset
  · rw [← Finset.sum_erase_add (hfin.toFinset) F hρs]
    have h2 : ∑ x ∈ hfin.toFinset.erase ρ, F x ≤ 0 := Finset.sum_nonpos (fun x _ => hle0 x)
    have h3 : F ρ = (((MeromorphicOn.divisor f (Metric.closedBall a |R|)) ρ : ℤ) : ℝ) *
        ((ρ - a).re * ((‖ρ - a‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹)) := by
      simp only [hF]
      ring
    have hd1 : (1 : ℝ) ≤ (((MeromorphicOn.divisor f (Metric.closedBall a |R|)) ρ : ℤ) : ℝ) := by
      exact_mod_cast hρd
    have h4 : (((MeromorphicOn.divisor f (Metric.closedBall a |R|)) ρ : ℤ) : ℝ) *
        ((ρ - a).re * ((‖ρ - a‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹)) ≤
        (ρ - a).re * ((‖ρ - a‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹) := by
      nlinarith [hXnonpos, hd1]
    linarith [h2, h3, h4]
  · have h0 : F ρ = 0 := by
      by_contra hne
      exact hρs (hsupp (Function.mem_support.mpr hne))
    have hdq : (((MeromorphicOn.divisor f (Metric.closedBall a |R|)) ρ : ℤ) : ℝ) ≠ 0 := by
      have := hρd
      have : (0 : ℤ) < MeromorphicOn.divisor f (Metric.closedBall a |R|) ρ := by omega
      exact_mod_cast ne_of_gt this
    have hX0 : (ρ - a).re * ((‖ρ - a‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹) = 0 := by
      have h3 : F ρ = (((MeromorphicOn.divisor f (Metric.closedBall a |R|)) ρ : ℤ) : ℝ) *
          ((ρ - a).re * ((‖ρ - a‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹)) := by
        simp only [hF]; ring
      rw [h3] at h0
      exact (mul_eq_zero.mp h0).resolve_left hdq
    have hsum0 : ∑ u ∈ hfin.toFinset, F u ≤ 0 := Finset.sum_nonpos (fun u _ => hle0 u)
    rw [hX0]
    exact hsum0

/-- **Multiplicity of a zero of `ζ` is at least one.** -/
private lemma zeta_divisor_one_le {U : Set ℂ} {ρ : ℂ} (han : AnalyticOnNhd ℂ riemannZeta U)
    (hρU : ρ ∈ U) (hρ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1) :
    (1 : ℤ) ≤ MeromorphicOn.divisor riemannZeta U ρ := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply han hρU]
  have hρan : AnalyticAt ℂ riemannZeta ρ := han ρ hρU
  have hne0 : analyticOrderAt riemannZeta ρ ≠ 0 := (AnalyticAt.analyticOrderAt_ne_zero hρan).2 hρ
  have h2an : AnalyticAt ℂ riemannZeta (2 : ℂ) := analyticOn_riemannZeta (2 : ℂ) (by simp)
  have h2 : analyticOrderAt riemannZeta (2 : ℂ) ≠ ⊤ := by
    have h0 : analyticOrderAt riemannZeta (2 : ℂ) = 0 :=
      (AnalyticAt.analyticOrderAt_eq_zero h2an).2
        (riemannZeta_ne_zero_of_one_le_re (s := (2 : ℂ)) (by norm_num))
    rw [h0]
    exact ENat.zero_ne_top
  have hnetop : analyticOrderAt riemannZeta ρ ≠ ⊤ :=
    AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (f := riemannZeta)
      analyticOn_riemannZeta
      (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
      (by norm_num) (by simpa using hρ1) h2
  rcases ENat.ne_top_iff_exists.mp hnetop with ⟨m, hm⟩
  rw [← hm, ENat.map_natCast, WithTop.untop₀_coe]
  have hm0 : 0 < m := by
    by_contra h
    have hz : m = 0 := Nat.eq_zero_of_not_pos h
    exact hne0 (by rw [← hm, hz]; simp)
  exact_mod_cast hm0

/-- The circle bound of `zeta_circle_bound` for a centre of *any* real height `t`, with the
constants expressed in terms of `|t|`.

The pointwise ingredients (`zeta_circle_zeta_lower`, `zeta_circle_regionB_pointwise`,
`zeta_circle_regionC_pointwise` on the two halves of the circle) are blind to the sign of the
height, so the proof of `Submission.Work.BMF.zeta_circle_bound` applies verbatim once the height
is replaced by `|t|` in the constants and `|t + R sin θ| ≤ 2 |t|`, `3 ≤ |t + R sin θ|` are used. -/
private lemma zeta_circle_bound_abs {A B x t R : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hgr : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ < 1 → 3 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        A * (|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) * (Real.log (|t| + 3)) ^ (2 / 3 : ℝ))
    (hx : 0 < x) (hR : 0 < R) (hR1 : R ≤ 1 / 2) (hxR : x + R ≤ 1) (ht : 4 ≤ |t|) :
    ∃ G : ℝ → ℝ, IntervalIntegrable G MeasureTheory.volume 0 (2 * Real.pi) ∧
      (∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc 0 (2 * Real.pi))),
        -(Real.cos θ * Real.log ‖riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I +
          (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖) ≤ G θ) ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), G θ) ≤
        2 * Real.log (1 / R) + 2 * Real.log (A + 1) + 2 * B * R ^ (3 / 2 : ℝ) * Real.log (2 * |t| + 3)
          + 2 * Real.log (Real.log (2 * |t| + 3) + 1) + 12
          + 4 * (x / R) ^ (3 / 2 : ℝ) * (Real.log (1 / x) + 1) := by
  -- ### constants
  set Xb : ℝ := Real.log (A + 1) + B * R ^ (3 / 2 : ℝ) * Real.log (2 * |t| + 3)
    + Real.log (Real.log (2 * |t| + 3) + 1) with hXb
  set Xc : ℝ := Real.log (Real.log (2 * |t| + 3) + 4) with hXc
  set M : ℝ := max Xb Xc with hM
  -- ### the two pieces of the majorant
  set Hf : ℝ → ℝ := fun θ =>
    (if 0 < Real.cos θ then Real.cos θ * (1 + Real.log (1 / (R * Real.cos θ))) else 0) with hHf
  set Pf : ℝ → ℝ := fun θ => max (-(Real.cos θ)) 0 with hPf
  set G : ℝ → ℝ := fun θ => Hf θ + M * Pf θ with hG
  have hHint : IntervalIntegrable Hf volume (0 : ℝ) (2 * Real.pi) := by
    rw [hHf]; exact (zeta_circle_arc_A hR hR1).1
  have hHval : (∫ θ in (0 : ℝ)..(2 * Real.pi), Hf θ) ≤ 2 * Real.log (1 / R) + 4 := by
    rw [hHf]; exact (zeta_circle_arc_A hR hR1).2
  have hPint : IntervalIntegrable Pf volume (0 : ℝ) (2 * Real.pi) := by
    rw [hPf]; exact (Real.continuous_cos.neg.max continuous_const).intervalIntegrable _ _
  have hPval : (∫ θ in (0 : ℝ)..(2 * Real.pi), Pf θ) = 2 := by
    rw [hPf]; exact zeta_circle_cos_weight
  have hGint : IntervalIntegrable G volume (0 : ℝ) (2 * Real.pi) := by
    rw [hG]; exact hHint.add (hPint.const_mul M)
  have hGval : (∫ θ in (0 : ℝ)..(2 * Real.pi), G θ)
      = (∫ θ in (0 : ℝ)..(2 * Real.pi), Hf θ) + M * (∫ θ in (0 : ℝ)..(2 * Real.pi), Pf θ) := by
    rw [hG, intervalIntegral.integral_add hHint (hPint.const_mul M),
      intervalIntegral.integral_const_mul]
  -- ### bound on `M`
  have htlog_nn : 0 ≤ Real.log (2 * |t| + 3) := by
    apply Real.log_nonneg; linarith [abs_nonneg t]
  have htlogpos : 0 < Real.log (2 * |t| + 3) := by
    apply Real.log_pos; linarith [abs_nonneg t]
  have hAnonneg : 0 ≤ Real.log (A + 1) := Real.log_nonneg (by linarith)
  have hBRnn : 0 ≤ B * R ^ (3 / 2 : ℝ) * Real.log (2 * |t| + 3) :=
    mul_nonneg (mul_nonneg (le_of_lt hB) (Real.rpow_nonneg (le_of_lt hR) _)) htlog_nn
  have hMbound : M ≤ Real.log (A + 1) + B * R ^ (3 / 2 : ℝ) * Real.log (2 * |t| + 3)
      + Real.log (Real.log (2 * |t| + 3) + 1) + Real.log 4 := by
    rw [hM]
    apply max_le
    · rw [hXb]; linarith [Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)]
    · rw [hXc]
      have h1 : Real.log (2 * |t| + 3) + 4 ≤ 4 * (Real.log (2 * |t| + 3) + 1) := by linarith
      have h2 : Real.log (Real.log (2 * |t| + 3) + 4)
          ≤ Real.log (4 * (Real.log (2 * |t| + 3) + 1)) :=
        Real.log_le_log (by linarith) h1
      have h3 : Real.log (4 * (Real.log (2 * |t| + 3) + 1))
          = Real.log 4 + Real.log (Real.log (2 * |t| + 3) + 1) :=
        Real.log_mul (by norm_num) (by linarith)
      linarith [hAnonneg, hBRnn]
  have hGbound : (∫ θ in (0 : ℝ)..(2 * Real.pi), G θ)
      ≤ 2 * Real.log (1 / R) + 4 + 2 * M := by
    rw [hGval, hPval]; linarith [hHval]
  -- ### pointwise domination
  have hsθ : ∀ θ : ℝ, (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I
      + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
      = (((1 + x + R * Real.cos θ : ℝ)) : ℂ)
        + (((t + R * Real.sin θ : ℝ)) : ℂ) * Complex.I := by
    intro θ
    rw [mul_comm Complex.I ((θ : ℂ)), Complex.exp_ofReal_mul_I]
    push_cast
    ring
  have hdom : ∀ θ : ℝ,
      -(Real.cos θ * Real.log ‖riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I +
        (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖) ≤ G θ := by
    intro θ
    rw [hsθ θ]
    have hsinR : |R * Real.sin θ| ≤ R := by
      rw [abs_mul, abs_of_pos hR]; nlinarith [Real.abs_sin_le_one θ]
    have httabs : 3 ≤ |t + R * Real.sin θ| := by
      have h1 : |t| ≤ |t + R * Real.sin θ| + |R * Real.sin θ| := by
        calc |t| = |(t + R * Real.sin θ) - R * Real.sin θ| := by ring_nf
          _ ≤ |t + R * Real.sin θ| + |R * Real.sin θ| := abs_sub _ _
      linarith [hsinR, ht, hR1]
    have htt2T : |t + R * Real.sin θ| ≤ 2 * |t| := by
      have h1 : |t + R * Real.sin θ| ≤ |t| + |R * Real.sin θ| := abs_add_le _ _
      linarith [hsinR, ht, hR1]
    have hσhalf : 1 / 2 ≤ 1 + x + R * Real.cos θ := by
      nlinarith [Real.neg_one_le_cos θ, hR, hR1, hx]
    rw [hG]
    by_cases hcos : 0 < Real.cos θ
    · -- region A
      simp only [hHf, hPf, if_pos hcos]
      have hPθ : max (-(Real.cos θ)) 0 = 0 :=
        le_antisymm (max_le (by linarith) le_rfl) (le_max_right _ _)
      rw [hPθ, mul_zero, add_zero]
      have hσgt : 1 < 1 + x + R * Real.cos θ := by nlinarith [hx, hR, hcos]
      have hre : ((((1 + x + R * Real.cos θ : ℝ)) : ℂ)
          + (((t + R * Real.sin θ : ℝ)) : ℂ) * Complex.I).re = 1 + x + R * Real.cos θ := by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_mul, add_zero]
      have hlow := zeta_circle_zeta_lower
        (s := ((((1 + x + R * Real.cos θ : ℝ)) : ℂ)
          + (((t + R * Real.sin θ : ℝ)) : ℂ) * Complex.I)) (by rw [hre]; exact hσgt)
      rw [hre, show 1 + x + R * Real.cos θ - 1 = x + R * Real.cos θ by ring] at hlow
      have hlogineq : Real.log (1 + 1 / (x + R * Real.cos θ))
          ≤ 1 + Real.log (1 / (R * Real.cos θ)) := by
        have hden : 0 < x + R * Real.cos θ := by nlinarith [hx, hR, hcos]
        have hden2 : 0 < R * Real.cos θ := by nlinarith [hR, hcos]
        have ha : 1 / (x + R * Real.cos θ) ≤ 1 / (R * Real.cos θ) :=
          one_div_le_one_div_of_le hden2 (by linarith)
        have hb : 1 + 1 / (x + R * Real.cos θ) ≤ 2 * (1 / (R * Real.cos θ)) := by
          have h2 : 1 ≤ 1 / (R * Real.cos θ) := by
            rw [le_div_iff₀ hden2]; nlinarith [hR, hR1, hcos.le, Real.cos_le_one θ]
          linarith
        calc Real.log (1 + 1 / (x + R * Real.cos θ))
            ≤ Real.log (2 * (1 / (R * Real.cos θ))) :=
              Real.log_le_log (by positivity) hb
          _ = Real.log 2 + Real.log (1 / (R * Real.cos θ)) :=
              Real.log_mul (by norm_num) (by positivity)
          _ ≤ 1 + Real.log (1 / (R * Real.cos θ)) := by
              have h2 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
              linarith
      rw [← mul_neg]
      exact mul_le_mul_of_nonneg_left (le_trans hlow hlogineq) (le_of_lt hcos)
    · -- cos θ ≤ 0
      simp only [hHf, hPf, if_neg hcos]
      have hPθ : max (-(Real.cos θ)) 0 = -(Real.cos θ) :=
        le_antisymm (max_le le_rfl (by linarith [le_of_not_gt hcos])) (le_max_left _ _)
      rw [hPθ, zero_add]
      by_cases hzero : Real.cos θ = 0
      · rw [hzero]; simp
      · have hcosneg : Real.cos θ < 0 := lt_of_le_of_ne (le_of_not_gt hcos) hzero
        have hncos : 0 < -(Real.cos θ) := neg_pos.mpr hcosneg
        rw [← neg_mul, mul_comm M (-Real.cos θ)]
        by_cases hσ1 : 1 + x + R * Real.cos θ < 1
        · -- region B
          have hbnd := zeta_circle_regionB_pointwise (A := A) (B := B)
            (σ := 1 + x + R * Real.cos θ) (t := t + R * Real.sin θ) (τ := |t|) (R := R)
            hA hB hgr hσhalf hσ1 httabs (le_of_lt hR)
            (by nlinarith [hx, hR, Real.neg_one_le_cos θ])
            (by linarith [htt2T])
          have hbndX : Real.log ‖riemannZeta
              ((((1 + x + R * Real.cos θ : ℝ)) : ℂ)
                + (((t + R * Real.sin θ : ℝ)) : ℂ) * Complex.I)‖ ≤ Xb := by
            rw [hXb]; exact hbnd
          have hXbM : Xb ≤ M := by rw [hM]; exact le_max_left _ _
          exact mul_le_mul_of_nonneg_left (le_trans hbndX hXbM) (le_of_lt hncos)
        · -- region C
          have hσge : 1 ≤ 1 + x + R * Real.cos θ := le_of_not_gt hσ1
          have hbnd := zeta_circle_regionC_pointwise (σ := 1 + x + R * Real.cos θ)
            (t := t + R * Real.sin θ) (τ := |t|) hσge httabs (by linarith [htt2T])
          have hbndX : Real.log ‖riemannZeta
              ((((1 + x + R * Real.cos θ : ℝ)) : ℂ)
                + (((t + R * Real.sin θ : ℝ)) : ℂ) * Complex.I)‖ ≤ Xc := by
            rw [hXc]; exact hbnd
          have hXcM : Xc ≤ M := by rw [hM]; exact le_max_right _ _
          exact mul_le_mul_of_nonneg_left (le_trans hbndX hXcM) (le_of_lt hncos)
  -- ### final arithmetic
  have hlog4 : 2 * Real.log 4 ≤ 8 := by
    have h2 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num)
    linarith
  have hxpart : 0 ≤ 4 * (x / R) ^ (3 / 2 : ℝ) * (Real.log (1 / x) + 1) := by
    have h1 : 0 ≤ Real.log (1 / x) := Real.log_nonneg (by rw [one_le_div hx]; linarith)
    have h2 : 0 ≤ (x / R) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
    have h3 : 0 ≤ 4 * (x / R) ^ (3 / 2 : ℝ) := by linarith
    exact mul_nonneg h3 (by linarith)
  refine ⟨G, hGint, ?_, ?_⟩
  · exact Filter.Eventually.of_forall hdom
  · linarith [hGbound, hMbound, hlog4, hxpart]


/-- The `cos θ`-weighted circle integral of `log ‖ζ‖` dominates `-ArcCost/(πR)`.

This is the circle estimate needed by the Jensen/Carleman zero-detection argument: it combines
`zeta_circle_bound_abs` with the elementary comparison `K ≤ ArcCost` (all terms of the elementary
majorant are absorbed by the generous coefficients of `ArcCost`, using `A ≥ 1`,
`2 (σ-1) ≤ R` and `|t| ≥ 4`). -/
private lemma zeta_arc_cost_bound {A B σ t R : ℝ} (hA : 1 ≤ A) (hB : 0 < B) (hR : 0 < R)
    (hσ1 : 1 < σ) (hσR : σ + R ≤ 5 / 4) (hR4 : R ≤ 1 / 4)
    (hσR2 : (1 / 2 : ℝ) ≤ σ - R) (h2xR : 2 * (σ - 1) ≤ R) (ht : 4 ≤ |t|)
    (hgr : ∀ σ' t' : ℝ, 1 / 2 ≤ σ' → σ' < 1 → 3 ≤ |t'| →
      ‖riemannZeta ((σ' : ℂ) + (t' : ℂ) * Complex.I)‖ ≤
        A * (|t'| + 3) ^ (B * (1 - σ') ^ (3 / 2 : ℝ)) * (Real.log (|t'| + 3)) ^ (2 / 3 : ℝ)) :
    -(1 / (Real.pi * R)) * ArcCost A B σ t R ≤
      (1 / (Real.pi * R)) * (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.cos θ * Real.log ‖riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I) +
          (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖) := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hx : 0 < σ - 1 := by linarith
  have hxR : σ - 1 + R ≤ 1 := by linarith
  have hR1 : R ≤ 1 / 2 := by linarith
  obtain ⟨G, hGint, hGdom, hGbound⟩ :=
    zeta_circle_bound_abs (A := A) (B := B) (x := σ - 1) (t := t) (R := R)
      hApos hB hgr hx hR hR1 hxR ht
  set F : ℝ → ℝ := fun θ => Real.cos θ * Real.log ‖riemannZeta
    (((σ : ℂ) + (t : ℂ) * Complex.I) + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ with hF
  have hcen : ∀ θ : ℝ, (((1 + (σ - 1) : ℝ) : ℂ) + (t : ℂ) * Complex.I
      + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
      = (((σ : ℂ) + (t : ℂ) * Complex.I) + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
    intro θ; push_cast; ring
  have hGdom' : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc 0 (2 * Real.pi))), -(F θ) ≤ G θ := by
    filter_upwards [hGdom] with θ hθ
    rw [hcen θ] at hθ
    simpa only [hF] using hθ
  -- elementary comparison of the two constants
  have hlog8 : (1 : ℝ) ≤ Real.log 8 := by
    have h : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    rw [h]; linarith [Real.log_two_gt_d9]
  have hxlog1 : 1 ≤ Real.log (2 / (σ - 1)) := by
    have h1 : (8 : ℝ) ≤ 2 / (σ - 1) := by
      rw [le_div_iff₀ hx]
      have h2 : σ - 1 < 1 / 4 := by linarith
      linarith
    exact le_trans hlog8 (Real.log_le_log (by norm_num) h1)
  have hlog2le : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlogL1 : 1 ≤ Real.log (|t| + 3) := by
    rw [Real.le_log_iff_exp_le (by linarith [abs_nonneg t])]
    linarith [Real.exp_one_lt_d9, abs_nonneg t, ht]
  have hloglognn : 0 ≤ Real.log (Real.log (|t| + 3) + 1) :=
    Real.log_nonneg (by linarith)
  have f1 : 2 * Real.log (1 / R) ≤ 2 * Real.log (2 / (σ - 1)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ hR hx]
    linarith
  have f2 : 2 * Real.log (A + 1) ≤ 4 * Real.log A + 4 := by
    have h1 : A + 1 ≤ 2 * A := by linarith
    have h2 : Real.log (A + 1) ≤ Real.log (2 * A) := Real.log_le_log (by linarith) h1
    have h3 : Real.log (2 * A) = Real.log 2 + Real.log A := Real.log_mul (by norm_num) (by linarith)
    have h4 : 0 ≤ Real.log A := Real.log_nonneg hA
    linarith
  have f3 : 2 * B * R ^ (3 / 2 : ℝ) * Real.log (2 * |t| + 3)
      ≤ 4 * B * R ^ (3 / 2 : ℝ) * (Real.log (|t| + 3) + 1) := by
    have h1 : (2 * |t| + 3) ≤ (|t| + 3) ^ 2 := by nlinarith [abs_nonneg t]
    have h2 : Real.log (2 * |t| + 3) ≤ 2 * Real.log (|t| + 3) := by
      calc Real.log (2 * |t| + 3) ≤ Real.log ((|t| + 3) ^ 2) :=
            Real.log_le_log (by linarith [abs_nonneg t]) h1
        _ = 2 * Real.log (|t| + 3) := by rw [Real.log_pow]; norm_num
    have h5 : Real.log (2 * |t| + 3) ≤ 2 * (Real.log (|t| + 3) + 1) := by linarith
    have h6 : 0 ≤ B * R ^ (3 / 2 : ℝ) := by positivity
    calc 2 * B * R ^ (3 / 2 : ℝ) * Real.log (2 * |t| + 3)
        = 2 * (B * R ^ (3 / 2 : ℝ)) * Real.log (2 * |t| + 3) := by ring
      _ ≤ 2 * (B * R ^ (3 / 2 : ℝ)) * (2 * (Real.log (|t| + 3) + 1)) :=
          mul_le_mul_of_nonneg_left h5 (by linarith)
      _ = 4 * B * R ^ (3 / 2 : ℝ) * (Real.log (|t| + 3) + 1) := by ring
  have f4 : 2 * Real.log (Real.log (2 * |t| + 3) + 1)
      ≤ 2 * Real.log (Real.log (|t| + 3) + 1) + 2 := by
    have h1 : (2 * |t| + 3) ≤ (|t| + 3) ^ 2 := by nlinarith [abs_nonneg t]
    have h2 : Real.log (2 * |t| + 3) ≤ 2 * Real.log (|t| + 3) := by
      calc Real.log (2 * |t| + 3) ≤ Real.log ((|t| + 3) ^ 2) :=
            Real.log_le_log (by linarith [abs_nonneg t]) h1
        _ = 2 * Real.log (|t| + 3) := by rw [Real.log_pow]; norm_num
    have h3 : Real.log (2 * |t| + 3) + 1 ≤ 2 * (Real.log (|t| + 3) + 1) := by linarith
    have hpos : 0 < Real.log (2 * |t| + 3) + 1 := by
      have hp := Real.log_pos (show (1 : ℝ) < 2 * |t| + 3 by linarith [abs_nonneg t])
      linarith
    have h4 : Real.log (Real.log (2 * |t| + 3) + 1) ≤ Real.log (2 * (Real.log (|t| + 3) + 1)) :=
      Real.log_le_log hpos h3
    have h5 : Real.log (2 * (Real.log (|t| + 3) + 1))
        = Real.log 2 + Real.log (Real.log (|t| + 3) + 1) :=
      Real.log_mul (by norm_num) (by linarith)
    linarith
  have f5 : 4 * ((σ - 1) / R) ^ (3 / 2 : ℝ) * (Real.log (1 / (σ - 1)) + 1)
      ≤ 2 * Real.log (2 / (σ - 1)) + 2 := by
    have hxR2 : (σ - 1) / R ≤ 1 / 2 := by
      rw [div_le_iff₀ hR]; linarith
    have hpow : ((σ - 1) / R) ^ (3 / 2 : ℝ) ≤ 1 / 2 := by
      have hnn : 0 ≤ (σ - 1) / R := by positivity
      have h1 : ((σ - 1) / R) ^ (3 / 2 : ℝ)
          = ((σ - 1) / R) * ((σ - 1) / R) ^ (1 / 2 : ℝ) := by
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity),
          Real.rpow_one]
      have h2 : ((σ - 1) / R) ^ (1 / 2 : ℝ) ≤ 1 :=
        Real.rpow_le_one hnn (by linarith) (by norm_num)
      have h3 : ((σ - 1) / R) * ((σ - 1) / R) ^ (1 / 2 : ℝ) ≤ (1 / 2) * 1 :=
        mul_le_mul hxR2 h2 (Real.rpow_nonneg hnn _) (by norm_num)
      linarith [h1, h3]
    have hlog1 : 0 ≤ Real.log (1 / (σ - 1)) :=
      Real.log_nonneg (by rw [one_le_div hx]; linarith)
    have hlog2 : Real.log (1 / (σ - 1)) ≤ Real.log (2 / (σ - 1)) :=
      Real.log_le_log (by positivity) (by
        rw [div_le_div_iff₀ hx hx]; linarith)
    have h3 : 4 * ((σ - 1) / R) ^ (3 / 2 : ℝ) * (Real.log (1 / (σ - 1)) + 1)
        ≤ 4 * (1 / 2) * (Real.log (2 / (σ - 1)) + 1) := by
      calc 4 * ((σ - 1) / R) ^ (3 / 2 : ℝ) * (Real.log (1 / (σ - 1)) + 1)
          ≤ 4 * (1 / 2) * (Real.log (1 / (σ - 1)) + 1) :=
            mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        _ ≤ 4 * (1 / 2) * (Real.log (2 / (σ - 1)) + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    linarith [h3]
  have hBRnn : 0 ≤ B * R ^ (3 / 2 : ℝ) * (Real.log (|t| + 3) + 1) :=
    mul_nonneg (by positivity)
      (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ |t| + 3 by linarith [abs_nonneg t])])
  have hKle : 2 * Real.log (1 / R) + 2 * Real.log (A + 1)
      + 2 * B * R ^ (3 / 2 : ℝ) * Real.log (2 * |t| + 3)
      + 2 * Real.log (Real.log (2 * |t| + 3) + 1) + 12
      + 4 * ((σ - 1) / R) ^ (3 / 2 : ℝ) * (Real.log (1 / (σ - 1)) + 1)
      ≤ ArcCost A B σ t R := by
    rw [ArcCost]
    linarith [f1, f2, f3, f4, f5, hxlog1, hBRnn, hloglognn]
  by_cases hfint : IntervalIntegrable F MeasureTheory.volume (0 : ℝ) (2 * Real.pi)
  · have hmono : (∫ θ in (0 : ℝ)..(2 * Real.pi), -(F θ))
        ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), G θ :=
      intervalIntegral.integral_mono_ae_restrict (by linarith [Real.pi_pos]) hfint.neg hGint hGdom'
    have hnegi : (∫ θ in (0 : ℝ)..(2 * Real.pi), -(F θ))
        = -(∫ θ in (0 : ℝ)..(2 * Real.pi), F θ) :=
      intervalIntegral.integral_neg
    have h1 : -(∫ θ in (0 : ℝ)..(2 * Real.pi), F θ) ≤ ArcCost A B σ t R := by
      linarith [hmono, hnegi, hGbound, hKle]
    have h2 : (1 / (Real.pi * R)) * (-(∫ θ in (0 : ℝ)..(2 * Real.pi), F θ))
        ≤ (1 / (Real.pi * R)) * ArcCost A B σ t R :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : -(1 / (Real.pi * R)) * ArcCost A B σ t R
        ≤ (1 / (Real.pi * R)) * (∫ θ in (0 : ℝ)..(2 * Real.pi), F θ) := by
      have e : -(1 / (Real.pi * R)) * ArcCost A B σ t R
          = (1 / (Real.pi * R)) * (-(ArcCost A B σ t R)) := by ring
      rw [e]; linarith [h2]
    simpa [hF] using h3
  · rw [intervalIntegral.integral_undef hfint]
    have hArc : 0 ≤ ArcCost A B σ t R := by
      rw [ArcCost]
      have h1 : 0 ≤ Real.log (2 / (σ - 1)) := Real.log_nonneg (by
        rw [le_div_iff₀ hx]; linarith)
      have h2 : 0 ≤ Real.log A := Real.log_nonneg hA
      have h3 : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
      have h4 : 0 ≤ Real.log (Real.log (|t| + 3) + 1) := hloglognn
      linarith [hBRnn]
    have h4 : 0 ≤ (1 / (Real.pi * R)) * ArcCost A B σ t R :=
      mul_nonneg (by positivity) hArc
    have h5 : -(1 / (Real.pi * R)) * ArcCost A B σ t R
        = -((1 / (Real.pi * R)) * ArcCost A B σ t R) := by ring
    rw [h5]
    linarith

/-- **Disc bound with a zero.** Jensen–Carleman plus the circle estimate. -/
private lemma zeta_disc_bound_zero {A B σ τ R β : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall (((σ : ℂ) + (τ : ℂ) * Complex.I)) |R|))
    (ha0 : riemannZeta (((σ : ℂ) + (τ : ℂ) * Complex.I)) ≠ 0)
    (hsphere : ∀ u : ℂ, ‖u - (((σ : ℂ) + (τ : ℂ) * Complex.I))‖ = R → riemannZeta u ≠ 0)
    (hleft : ∀ u : ℂ, riemannZeta u = 0 →
      u ∈ Metric.closedBall (((σ : ℂ) + (τ : ℂ) * Complex.I)) |R| →
      u.re < (((σ : ℂ) + (τ : ℂ) * Complex.I)).re)
    (harc : -(1 / (Real.pi * R)) * ArcCost A B σ τ R ≤
      (1 / (Real.pi * R)) * (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.cos θ * Real.log ‖riemannZeta (((σ : ℂ) + (τ : ℂ) * Complex.I) +
          (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖))
    {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hρin : ρ ∈ Metric.closedBall (((σ : ℂ) + (τ : ℂ) * Complex.I)) |R|)
    (hρd : (1 : ℤ) ≤ MeromorphicOn.divisor riemannZeta
      (Metric.closedBall (((σ : ℂ) + (τ : ℂ) * Complex.I)) |R|) ρ)
    (hρsub : ρ - (((σ : ℂ) + (τ : ℂ) * Complex.I)) = ((β - σ : ℝ) : ℂ)) :
    (1 / (σ - β)) * (1 - ((σ - β) / R) ^ 2) - (1 / (Real.pi * R)) * ArcCost A B σ τ R ≤
      (deriv riemannZeta (((σ : ℂ) + (τ : ℂ) * Complex.I)) /
        riemannZeta (((σ : ℂ) + (τ : ℂ) * Complex.I))).re := by
  have hid := Commons.Analysis.Complex.jensenCarleman hR hf ha0 hsphere
  have hsum := finsum_divisor_le_zero_term hR hf ha0 hsphere hleft hρ hρin hρd
  have hρre : ρ.re = β := by
    have h := congrArg Complex.re hρsub
    simp at h
    linarith
  have hβσ : β < σ := by
    have h := hleft ρ hρ hρin
    have hre : (((σ : ℂ) + (τ : ℂ) * Complex.I)).re = σ := by simp
    rw [hρre, hre] at h
    exact h
  have hterm : (ρ - (((σ : ℂ) + (τ : ℂ) * Complex.I))).re *
      ((‖ρ - (((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹)
      = -(1 / (σ - β)) + (σ - β) / R ^ 2 := by
    have hre : (ρ - (((σ : ℂ) + (τ : ℂ) * Complex.I))).re = β - σ := by rw [hρsub]; simp
    have hnorm : ‖ρ - (((σ : ℂ) + (τ : ℂ) * Complex.I))‖ = σ - β := by
      rw [hρsub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith : β - σ < 0)]
      ring
    rw [hre, hnorm]
    have h1 : (σ - β) ≠ 0 := by linarith
    have h1' : (β - σ) ≠ 0 := by linarith
    have hR0 : R ≠ 0 := ne_of_gt hR
    field_simp
    ring
  have h2 : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta
      (Metric.closedBall (((σ : ℂ) + (τ : ℂ) * Complex.I)) |R|)) u : ℤ) : ℝ) *
      (u - (((σ : ℂ) + (τ : ℂ) * Complex.I))).re *
      ((‖u - (((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹))
      ≤ -(1 / (σ - β)) + (σ - β) / R ^ 2 := by
    rw [← hterm]; exact hsum
  rw [hid]
  have hEq : (1 / (σ - β)) * (1 - ((σ - β) / R) ^ 2) = (1 / (σ - β)) - (σ - β) / R ^ 2 := by
    rw [div_pow, mul_sub, mul_one]
    congr 1
    field_simp
  linarith [h2, harc, hEq]

/-- **Disc bound without a zero.** The divisor sum is dropped entirely. -/
private lemma zeta_disc_bound_nozero {A B σ τ R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall (((σ : ℂ) + (τ : ℂ) * Complex.I)) |R|))
    (ha0 : riemannZeta (((σ : ℂ) + (τ : ℂ) * Complex.I)) ≠ 0)
    (hsphere : ∀ u : ℂ, ‖u - (((σ : ℂ) + (τ : ℂ) * Complex.I))‖ = R → riemannZeta u ≠ 0)
    (hleft : ∀ u : ℂ, riemannZeta u = 0 →
      u ∈ Metric.closedBall (((σ : ℂ) + (τ : ℂ) * Complex.I)) |R| →
      u.re < (((σ : ℂ) + (τ : ℂ) * Complex.I)).re)
    (harc : -(1 / (Real.pi * R)) * ArcCost A B σ τ R ≤
      (1 / (Real.pi * R)) * (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.cos θ * Real.log ‖riemannZeta (((σ : ℂ) + (τ : ℂ) * Complex.I) +
          (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖)) :
    -(1 / (Real.pi * R)) * ArcCost A B σ τ R ≤
      (deriv riemannZeta (((σ : ℂ) + (τ : ℂ) * Complex.I)) /
        riemannZeta (((σ : ℂ) + (τ : ℂ) * Complex.I))).re := by
  have hid := Commons.Analysis.Complex.jensenCarleman hR hf ha0 hsphere
  have hsum := finsum_divisor_nonpos hR hf ha0 hsphere hleft
  rw [hid]
  have h2 : (0 : ℝ) ≤ -(∑ᶠ u : ℂ, (((MeromorphicOn.divisor riemannZeta
      (Metric.closedBall (((σ : ℂ) + (τ : ℂ) * Complex.I)) |R|)) u : ℤ) : ℝ) *
      (u - (((σ : ℂ) + (τ : ℂ) * Complex.I))).re *
      ((‖u - (((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹)) := by linarith
  linarith [h2, harc]

/-- **Vinogradov–Korobov zero-free region for `ζ`, from the VK growth bound.** -/
private theorem zeta_zeroFree_of_growth (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hgr : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ < 1 → 3 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        A * (|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) * (Real.log (|t| + 3)) ^ (2 / 3 : ℝ)) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ t σ : ℝ, 3 ≤ |t| →
      1 - c₁ / VKd (|t| + 3) ≤ σ → σ ≤ 1 →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound
  -- Normalise the growth constant: WLOG `1 ≤ A`, since the factor
  -- `(|t|+3) ^ (B (1-σ)^{3/2}) (log (|t|+3))^{2/3}` is nonnegative, so enlarging `A` preserves `hgr`.
  set A' : ℝ := max A 1 with hA'def
  have hA'1 : 1 ≤ A' := by rw [hA'def]; exact le_max_right A 1
  have hA'pos : 0 < A' := lt_of_lt_of_le zero_lt_one hA'1
  have hA'2 : A ≤ A' := by rw [hA'def]; exact le_max_left A 1
  have hgr' : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ < 1 → 3 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        A' * (|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) * (Real.log (|t| + 3)) ^ (2 / 3 : ℝ) := by
    intro σ t h1 h2 h3
    refine le_trans (hgr σ t h1 h2 h3) ?_
    have hP : 0 ≤ (|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) *
        (Real.log (|t| + 3)) ^ (2 / 3 : ℝ) := by
      have hlog : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hlog _)
    calc A * (|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) * (Real.log (|t| + 3)) ^ (2 / 3 : ℝ)
        = A * ((|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) *
            (Real.log (|t| + 3)) ^ (2 / 3 : ℝ)) := by ring
      _ ≤ A' * ((|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) *
            (Real.log (|t| + 3)) ^ (2 / 3 : ℝ)) := mul_le_mul_of_nonneg_right hA'2 hP
      _ = A' * (|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) *
            (Real.log (|t| + 3)) ^ (2 / 3 : ℝ) := by ring
  obtain ⟨T₁, c₁, c₀, hT₁, hc₁, hc₀, hc₁c₀, harith⟩ := zeta_vk_arith A' B C₀ hA'pos hB hC₀pos.le
  obtain ⟨ε, hεpos, hcomp⟩ := zeta_zeroFree_compact (max T₁ 4)
    (by have h := le_max_right T₁ 4; linarith)
  refine ⟨min c₁ (ε * VKd 6), lt_min hc₁ (mul_pos hεpos (VKd_pos (by norm_num))), ?_⟩
  intro t σ ht hσlo hσle
  by_cases hsmall : |t| ≤ max T₁ 4
  · refine hcomp t σ ht hsmall ?_ (by linarith)
    have hVK : VKd (6 : ℝ) ≤ VKd (|t| + 3) := VKd_mono (by norm_num) (by linarith [abs_nonneg t])
    have hVKpos : 0 < VKd (|t| + 3) := VKd_pos (by linarith [abs_nonneg t])
    have hle : min c₁ (ε * VKd 6) ≤ ε * VKd 6 := min_le_right _ _
    have : min c₁ (ε * VKd 6) / VKd (|t| + 3) ≤ ε := by
      rw [div_le_iff₀ hVKpos]
      exact le_trans hle (mul_le_mul_of_nonneg_left hVK hεpos.le)
    linarith
  · by_contra hz
    have hT1le : T₁ ≤ |t| := le_trans (le_max_left _ _) (le_of_lt (lt_of_not_ge hsmall))
    have ht4 : 4 ≤ |t| := le_trans hT₁ hT1le
    obtain ⟨a_, b_, ha_pos, hab, hb8, h2xa, hcond⟩ := harith t hT1le
    obtain ⟨R, haR, hbR, hgood⟩ := zeta_sphere_avoid
      (fun j : Fin 2 =>
        if j = 0 then (((1 + c₀ / VKd (|t| + 3) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        else (((1 + c₀ / VKd (|t| + 3) : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I))
      ha_pos hab
    set x : ℝ := c₀ / VKd (|t| + 3) with hxdef
    have hVKpos : 0 < VKd (|t| + 3) := VKd_pos (by linarith [abs_nonneg t])
    have hxpos : 0 < x := div_pos hc₀ hVKpos
    have hRpos : 0 < R := lt_of_lt_of_le ha_pos haR
    have h2xR : 2 * x ≤ R := le_trans h2xa.le haR
    have hR4 : R ≤ 1 / 4 := by linarith [le_trans hbR hb8]
    have hxR : x + R ≤ 1 / 4 := by
      have : x ≤ 1 / 16 := by linarith [h2xR, le_trans hbR hb8]
      linarith
    have h2t4 : 4 ≤ |2 * t| := by
      have h : |2 * t| = 2 * |t| := by rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      rw [h]; linarith
    have hδle : 1 - σ ≤ c₁ / VKd (|t| + 3) := by
      have h1 : min c₁ (ε * VKd 6) / VKd (|t| + 3) ≤ c₁ / VKd (|t| + 3) :=
        div_le_div_of_nonneg_right (min_le_left _ _) (le_of_lt hVKpos)
      linarith
    have hδx : 1 - σ ≤ x / 24 := by
      have hx24 : x / 24 = (c₀ / 24) / VKd (|t| + 3) := by
        rw [hxdef]; field_simp
      have h2 : c₁ / VKd (|t| + 3) ≤ (c₀ / 24) / VKd (|t| + 3) := by
        rw [div_le_div_iff₀ hVKpos hVKpos]
        exact mul_le_mul_of_nonneg_right hc₁c₀ hVKpos.le
      rw [hx24]
      linarith
    -- the two circles avoid zeros of ζ
    have hsphere1 : ∀ u : ℂ, ‖u - (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ = R →
        riemannZeta u ≠ 0 := by
      intro u hu hu0
      have h := hgood 0 u hu0
      rw [hxdef] at h
      simpa using h hu
    have hsphere2 : ∀ u : ℂ, ‖u - (((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)‖ = R →
        riemannZeta u ≠ 0 := by
      intro u hu hu0
      have h := hgood 1 u hu0
      rw [hxdef] at h
      simpa using h hu
    -- analyticity
    have hf1 : AnalyticOnNhd ℂ riemannZeta
        (Metric.closedBall (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I) |R|) := by
      refine analyticOnNhd_zeta_closedBall ?_
      intro hmem
      rw [Metric.mem_closedBall, dist_eq_norm, abs_of_pos hRpos] at hmem
      have hge : |t| ≤ ‖(1 : ℂ) - (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
        have h := Complex.abs_im_le_norm ((1 : ℂ) - (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I))
        have him : ((1 : ℂ) - (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im = -t := by simp
        rwa [him, abs_neg] at h
      linarith
    have hf2 : AnalyticOnNhd ℂ riemannZeta
        (Metric.closedBall (((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) |R|) := by
      refine analyticOnNhd_zeta_closedBall ?_
      intro hmem
      rw [Metric.mem_closedBall, dist_eq_norm, abs_of_pos hRpos] at hmem
      have hge : |2 * t| ≤ ‖(1 : ℂ) - (((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)‖ := by
        have h := Complex.abs_im_le_norm ((1 : ℂ) - (((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I))
        have him : ((1 : ℂ) - (((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).im = -(2 * t) := by simp
        rwa [him, abs_neg] at h
      linarith
    have ha01 : riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_le_re
      have hre : (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = 1 + x := by simp
      rw [hre]; linarith
    have ha02 : riemannZeta (((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_le_re
      have hre : (((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I).re = 1 + x := by simp
      rw [hre]; linarith
    -- left conditions
    have hleft1 : ∀ u : ℂ, riemannZeta u = 0 →
        u ∈ Metric.closedBall (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I) |R| →
        u.re < (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I).re := by
      intro u hu _
      have hlt : u.re < 1 := by
        by_contra h
        exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h) hu
      have hre : (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = 1 + x := by simp
      rw [hre]; linarith
    have hleft2 : ∀ u : ℂ, riemannZeta u = 0 →
        u ∈ Metric.closedBall (((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) |R| →
        u.re < (((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I).re := by
      intro u hu _
      have hlt : u.re < 1 := by
        by_contra h
        exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h) hu
      have hre : (((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I).re = 1 + x := by simp
      rw [hre]; linarith
    -- circle estimates
    have harc1 : -(1 / (Real.pi * R)) * ArcCost A' B (1 + x) t R ≤
        (1 / (Real.pi * R)) * (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.cos θ * Real.log ‖riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I +
            (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖) := by
      have h := zeta_arc_cost_bound (A := A') (B := B) (σ := 1 + x) (t := t) (R := R)
        hA'1 hB hRpos (by linarith) (by linarith) hR4 (by linarith)
        (by linarith [h2xR]) ht4 hgr'
      simpa using h
    have harc2 : -(1 / (Real.pi * R)) * ArcCost A' B (1 + x) (2 * t) R ≤
        (1 / (Real.pi * R)) * (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.cos θ * Real.log ‖riemannZeta (((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I +
            (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖) := by
      have h := zeta_arc_cost_bound (A := A') (B := B) (σ := 1 + x) (t := 2 * t) (R := R)
        hA'1 hB hRpos (by linarith) (by linarith) hR4 (by linarith)
        (by linarith [h2xR]) h2t4 hgr'
      simpa using h
    -- the zero and its divisor
    have hρsub1 : ((σ : ℂ) + (t : ℂ) * Complex.I) -
        (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I) = ((σ - (1 + x) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    have hρin1 : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈
        Metric.closedBall (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I) |R| := by
      rw [Metric.mem_closedBall, dist_eq_norm, abs_of_pos hRpos, hρsub1, Complex.norm_real,
        Real.norm_eq_abs, abs_of_neg (by linarith : σ - (1 + x) < 0)]
      linarith
    have hρd1 : (1 : ℤ) ≤ MeromorphicOn.divisor riemannZeta
        (Metric.closedBall (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I) |R|)
        ((σ : ℂ) + (t : ℂ) * Complex.I) := by
      refine zeta_divisor_one_le hf1 hρin1 (by simpa using hz) ?_
      intro h
      have him : t = 0 := by
        have h' := congrArg Complex.im h
        simpa using h'
      rw [him] at ht4
      norm_num at ht4
    -- apply the two disc bounds
    have hd1 := zeta_disc_bound_zero (A := A') (B := B) (σ := 1 + x) (τ := t) (R := R) (β := σ)
      hRpos hf1 ha01 hsphere1 hleft1 harc1 (ρ := ((σ : ℂ) + (t : ℂ) * Complex.I))
      (by simpa using hz) hρin1 hρd1 hρsub1
    have hd2 := zeta_disc_bound_nozero (A := A') (B := B) (σ := 1 + x) (τ := 2 * t) (R := R)
      hRpos hf2 ha02 hsphere2 hleft2 harc2
    have h341 := zeta_logDeriv_341 (1 + x) t (by linarith)
    have hpole : (-deriv riemannZeta (((1 + x : ℝ) : ℂ)) / riemannZeta (((1 + x : ℝ) : ℂ))).re
        ≤ 1 / x + C₀ := by
      have h := hC₀ (1 + x) (by linarith) (by linarith)
      have hxe : (1 + x) - 1 = x := by ring
      rw [hxe] at h
      exact h
    -- numeric conditions
    obtain ⟨hnum1, hnum2, hnum3, hnum4⟩ := hcond R haR hbR
    -- convert everything to `-Re(ζ'/ζ)`
    have h341' : 0 ≤ 3 * (-(deriv riemannZeta (((1 + x : ℝ) : ℂ)) /
            riemannZeta (((1 + x : ℝ) : ℂ))).re)
        + 4 * (-(deriv riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
            riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re)
        + (-(deriv riemannZeta (((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) /
            riemannZeta (((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re) := by
      have h := h341
      have e0 : (-deriv riemannZeta (((1 + x : ℝ) : ℂ)) / riemannZeta (((1 + x : ℝ) : ℂ))).re
          = -(deriv riemannZeta (((1 + x : ℝ) : ℂ)) / riemannZeta (((1 + x : ℝ) : ℂ))).re := by
        rw [neg_div, Complex.neg_re]
      have e1 : (-deriv riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
          riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
          = -(deriv riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
              riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
        rw [neg_div, Complex.neg_re]
      have e2 : (-deriv riemannZeta (((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) /
          riemannZeta (((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re
          = -(deriv riemannZeta (((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) /
              riemannZeta (((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re := by
        rw [neg_div, Complex.neg_re]
      rw [e0, e1, e2] at h
      exact h
    have hpole' : -(deriv riemannZeta (((1 + x : ℝ) : ℂ)) /
        riemannZeta (((1 + x : ℝ) : ℂ))).re ≤ 1 / x + C₀ := by
      have e0 : (-deriv riemannZeta (((1 + x : ℝ) : ℂ)) / riemannZeta (((1 + x : ℝ) : ℂ))).re
          = -(deriv riemannZeta (((1 + x : ℝ) : ℂ)) / riemannZeta (((1 + x : ℝ) : ℂ))).re := by
        rw [neg_div, Complex.neg_re]
      rw [e0] at hpole
      exact hpole
    -- key combination
    have hstep : 4 * ((1 / ((1 + x) - σ)) * (1 - (((1 + x) - σ) / R) ^ 2)
        - (1 / (Real.pi * R)) * ArcCost A' B (1 + x) t R)
        ≤ 3 * (1 / x + C₀) + (1 / (Real.pi * R)) * ArcCost A' B (1 + x) (2 * t) R := by
      linarith [hd1, hd2, h341', hpole']
    -- multiply by ((1+x)-σ)/4
    have hrpos : 0 < (1 + x) - σ := by linarith
    have hmul := mul_le_mul_of_nonneg_right hstep
      (le_of_lt (by positivity : (0:ℝ) < ((1 + x) - σ) / 4))
    have e1 : 4 * ((1 / ((1 + x) - σ)) * (1 - (((1 + x) - σ) / R) ^ 2)
        - (1 / (Real.pi * R)) * ArcCost A' B (1 + x) t R) * (((1 + x) - σ) / 4)
        = (1 - (((1 + x) - σ) / R) ^ 2)
          - ((1 + x) - σ) * (1 / (Real.pi * R)) * ArcCost A' B (1 + x) t R := by
      have h1 : ((1 + x) - σ) ≠ 0 := ne_of_gt hrpos
      field_simp
    have e2 : (3 * (1 / x + C₀) + (1 / (Real.pi * R)) * ArcCost A' B (1 + x) (2 * t) R)
        * (((1 + x) - σ) / 4)
        = (3 / 4) * (((1 + x) - σ) / x) + (3 * C₀ / 4) * ((1 + x) - σ)
          + ((1 + x) - σ) * (1 / (Real.pi * R)) * ArcCost A' B (1 + x) (2 * t) R / 4 := by
      ring
    rw [e1, e2] at hmul
    -- the main inequality
    have hmain : 1 / 4 - ((x + (1 - σ)) / R) ^ 2 - (3 / 4) * ((1 - σ) / x)
        - (3 * C₀ / 4) * (x + (1 - σ))
        - ((x + (1 - σ)) / (Real.pi * R)) *
          (ArcCost A' B (1 + x) t R + ArcCost A' B (1 + x) (2 * t) R / 4) ≤ 0 := by
      have h3 : (3 / 4) * (((1 + x) - σ) / x) = 3 / 4 + (3 / 4) * ((1 - σ) / x) := by
        field_simp
        ring
      have h4 : (1 + x) - σ = x + (1 - σ) := by ring
      rw [h3] at hmul
      rw [h4] at hmul
      have hsplit : ((x + (1 - σ)) / (Real.pi * R))
            * (ArcCost A' B (1 + x) t R + ArcCost A' B (1 + x) (2 * t) R / 4)
          = (x + (1 - σ)) * (1 / (Real.pi * R)) * ArcCost A' B (1 + x) t R
            + (x + (1 - σ)) * (1 / (Real.pi * R)) * ArcCost A' B (1 + x) (2 * t) R / 4 := by
        field_simp [Real.pi_ne_zero, hRpos.ne']
      rw [hsplit]
      linarith [hmul]
    -- the numeric positivity
    have hkey : 0 < 1 / 4 - ((x + (1 - σ)) / R) ^ 2 - (3 / 4) * ((1 - σ) / x)
        - (3 * C₀ / 4) * (x + (1 - σ))
        - ((x + (1 - σ)) / (Real.pi * R)) *
          (ArcCost A' B (1 + x) t R + ArcCost A' B (1 + x) (2 * t) R / 4) := by
      have hxσ : x + (1 - σ) ≤ 2 * x := by linarith
      have h1 : ((x + (1 - σ)) / R) ^ 2 ≤ 1 / 100 := by
        have hle : (x + (1 - σ)) / R ≤ 2 * x / R :=
          div_le_div_of_nonneg_right hxσ (le_of_lt hRpos)
        have hnn : 0 ≤ (x + (1 - σ)) / R := div_nonneg (by linarith) (le_of_lt hRpos)
        have hnn2 : 0 ≤ 2 * x / R := div_nonneg (by linarith) (le_of_lt hRpos)
        nlinarith [hnum1]
      have h2 : (3 / 4) * ((1 - σ) / x) ≤ 3 / 4 * (1 / 24) := by
        have h : (1 - σ) / x ≤ 1 / 24 := by
          rw [div_le_iff₀ hxpos]
          linarith [hδx]
        linarith
      have h3 : (3 * C₀ / 4) * (x + (1 - σ)) ≤ 3 / 100 := by
        have h5 : (3 * C₀ / 4) * (2 * x) ≤ 1 / 100 := hnum3
        have h6 : (3 * C₀ / 4) * (x + (1 - σ)) ≤ (3 * C₀ / 4) * (2 * x) := by
          exact mul_le_mul_of_nonneg_left hxσ (by positivity)
        linarith
      have h4 : ((x + (1 - σ)) / (Real.pi * R)) *
          (ArcCost A' B (1 + x) t R + ArcCost A' B (1 + x) (2 * t) R / 4) ≤ 1 / 100 := by
        by_cases hsign : 0 ≤ ArcCost A' B (1 + x) t R + ArcCost A' B (1 + x) (2 * t) R / 4
        · have hnum4' : 2 * x / (Real.pi * R) *
              (ArcCost A' B (1 + x) t R + ArcCost A' B (1 + x) (2 * t) R / 4) ≤ 1 / 100 := by
            have hcost : ArcCost A' B (1 + x) |t| R + ArcCost A' B (1 + x) (2 * |t|) R / 4
                = ArcCost A' B (1 + x) t R + ArcCost A' B (1 + x) (2 * t) R / 4 := by
              simp only [ArcCost, abs_mul, abs_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
            rw [← hcost]
            exact hnum4
          have hstep2 : (x + (1 - σ)) / (Real.pi * R) ≤ 2 * x / (Real.pi * R) := by
            apply div_le_div_of_nonneg_right hxσ
            positivity
          exact le_trans (mul_le_mul_of_nonneg_right hstep2 hsign) hnum4'
        · have hsign' : ArcCost A' B (1 + x) t R + ArcCost A' B (1 + x) (2 * t) R / 4 < 0 :=
            lt_of_not_ge hsign
          have : (x + (1 - σ)) / (Real.pi * R) *
              (ArcCost A' B (1 + x) t R + ArcCost A' B (1 + x) (2 * t) R / 4) < 0 :=
            mul_neg_of_pos_of_neg (by positivity) hsign'
          linarith
      linarith
    linarith [hkey, hmain]


/-- **The Vinogradov–Korobov zero-free region for ζ, and the logarithmic-derivative bound in
it, from the VK growth bound.**

Input: the growth bound `‖ζ(σ+it)‖ ≤ A (|t|+3)^{B(1-σ)^{3/2}} log^{2/3}(|t|+3)` for
`1/2 ≤ σ < 1`, `|t| ≥ 3` (Ford, "Zero-free regions for the Riemann zeta function"; this is the
input supplied by the VK exponential-sum estimate).

Output:
* the zero-free region: for some `c₁ > 0`, `ζ(σ+it) ≠ 0` whenever `|t| ≥ 3` and
  `1 - c₁/VKd(|t|+3) ≤ σ ≤ 1`, where `VKd y = (log y)^{2/3}(log log y)^{1/3}`
  (`Submission.Work.BMF.VKdenom`);
* the logarithmic-derivative bound: for some `c₂ > 0`, `B > 0`,
  `‖ζ′/ζ(σ+it)‖ ≤ B·(log(|t|+3))²` whenever `|t| ≥ 3` and `1 - c₂/VKd(|t|+3) ≤ σ ≤ 2`.

The two constants are independent on purpose: it is standard that the bound
`‖ζ′/ζ‖ ≪ VKd(|t|+3)·log` (Bellotti, arXiv:2210.06457, Thm 1.3) holds in the region, and the
cruder `≪ (log)²` form used here follows from it for large `|t|` (since
`VKd y · log y ≤ (log y)^2`, available as `VKd_le_log`); the narrower region `1 - c₂/VKd` leaves
room for the standard Borel–Carathéodory / Landau argument (zeros are then at distance ≫ c₂/VKd
from a contour point).

The proof of the first conjunct is the Landau/Jensen–Carleman zero-detection argument of
Ford/Bellotti: at the two centres `1+x+iτ` and `1+x+2iτ` (with `x = c₀/VKd(|τ|+3)`) the
Jensen–Carleman formula `Commons.Analysis.Complex.jensenCarleman` bounds `Re(ζ′/ζ)` above by the
contribution of the zero plus the circle integral, which is controlled by the VK growth bound
(`zeta_circle_bound_abs` below); combined with `3 + 4cos θ + cos 2θ ≥ 0`
(`Submission.Work.BMF.zeta_logDeriv_341`) and the pole bound on the real axis
(`Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound`) this gives the contradiction unless
`1 - β ≥ c₁/VKd`.  The second conjunct is proved in
`Submission.Work.BMF.zeta_logDeriv_bound_vk` from the zero-free region. -/
theorem zeta_vk_region_of_growth
    (hgr : ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ < 1 → 3 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        A * (|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) * (Real.log (|t| + 3)) ^ (2 / 3 : ℝ)) :
    (∃ c₁ : ℝ, 0 < c₁ ∧ ∀ t σ : ℝ, 3 ≤ |t| → 1 - c₁ / VKd (|t| + 3) ≤ σ → σ ≤ 1 →
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) ∧
    (∃ c₂ B : ℝ, 0 < c₂ ∧ 0 < B ∧ ∀ t σ : ℝ, 3 ≤ |t| →
        1 - c₂ / VKd (|t| + 3) ≤ σ → σ ≤ 2 →
        ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
          riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B * (Real.log (|t| + 3)) ^ 2) := by
  obtain ⟨A, B, hA, hB, hgro⟩ := hgr
  obtain ⟨c₁, hc₁, hzf⟩ := zeta_zeroFree_of_growth A B hA hB hgro
  exact ⟨⟨c₁, hc₁, hzf⟩, zeta_logDeriv_bound_vk c₁ hc₁ hzf⟩

end

end Work.BMF
