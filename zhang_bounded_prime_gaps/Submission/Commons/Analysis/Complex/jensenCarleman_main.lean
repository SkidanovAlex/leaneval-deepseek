import Mathlib
import Submission.Commons.Analysis.Complex.cosAvg_analytic
import Submission.Commons.Analysis.Complex.partialX_log_norm
import Submission.Commons.Analysis.Complex.sphere_mirror_norm
import Submission.Commons.Analysis.Complex.sphere_mirror_log
import Submission.Commons.Analysis.Complex.re_one_sub_mirror
import Submission.Commons.Analysis.Complex.norm_mirror
import Submission.Commons.Analysis.Complex.re_one_sub
import Submission.Commons.Analysis.Complex.harmonicOnNhd_finset_sum
import Submission.Commons.Analysis.Complex.harmonicOnNhd_log_norm_sub
import Submission.Commons.Analysis.Complex.cosAvg_harmonic
import Submission.Commons.Analysis.Complex.zeroFactor_g
import Submission.Commons.Analysis.Complex.log_boundary_factor
import Submission.Commons.Analysis.Complex.deriv_log_factor
import Submission.Commons.Analysis.Complex.deriv_aux_harmonic
import Submission.Commons.Analysis.TrigIntegrals.cosPeriodZero

open Complex Metric MeasureTheory Set
open scoped Interval BigOperators ComplexConjugate Topology
noncomputable section

namespace Commons.Analysis.Complex
-- 1. Support of divisor lies in the open ball (analytic, nonzero at center & on sphere)
lemma divisor_support_openBall {a : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall a R)) (hfa : f a ≠ 0)
    (hsphere : ∀ u, ‖u - a‖ = R → f u ≠ 0) :
    ∀ u : ℂ, MeromorphicOn.divisor f (Metric.closedBall a R) u ≠ 0 → ‖u - a‖ < R := by
  intro u hu
  have huCB : u ∈ Metric.closedBall a R :=
    (MeromorphicOn.divisor f (Metric.closedBall a R)).supportWithinDomain hu
  have hle : ‖u - a‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using huCB
  have hne : ‖u - a‖ ≠ R := by
    intro h
    have hfz : f u ≠ 0 := hsphere u h
    have hord : analyticOrderAt f u = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hfz)
    have hD0 : (MeromorphicOn.divisor f (Metric.closedBall a R)) u = 0 := by
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf huCB]
      simp [hord]
    exact hu hD0
  exact lt_of_le_of_ne hle hne

lemma divisor_zero_at_center {a : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall a R)) (hfa : f a ≠ 0) :
    MeromorphicOn.divisor f (Metric.closedBall a R) a = 0 := by
  have haCB : a ∈ Metric.closedBall a R := by simp [hR.le]
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf haCB]
  have hord : analyticOrderAt f a = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hfa)
  simp [hord]

lemma circleMap_eq_exp (a : ℂ) (R θ : ℝ) :
    circleMap a R θ = a + (R : ℂ) * cexp (Complex.I * (θ : ℂ)) := by
  have h0 : circleMap a R θ = a + circleMap 0 R θ := by
    rw [← circleMap_sub_center a R θ]
    ring
  rw [h0]
  rw [circleMap_zero]
  congr 1
  have harg : (↑θ : ℂ) * Complex.I = Complex.I * (↑θ : ℂ) := by ring
  rw [harg]

open scoped BigOperators in
theorem jensenCarleman_main {a : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall a |R|))
    (hfa : f a ≠ 0)
    (hfc : ∀ u : ℂ, ‖u - a‖ = R → f u ≠ 0) :
    (deriv f a / f a).re =
      - (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall a |R|)) u : ℤ) : ℝ) *
          ((u - a).re) * (((‖u - a‖ : ℝ) ^ 2)⁻¹ - (R : ℝ)⁻¹ * (R : ℝ)⁻¹)) +
      (1 / (Real.pi * R)) * (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.cos θ * Real.log ‖f (a + (R : ℝ) * Complex.exp (Complex.I * (θ : ℂ)))‖) := by
  classical
  have hRle : 0 ≤ R := hR.le
  have hfR : AnalyticOnNhd ℂ f (Metric.closedBall a R) := by
    simpa [abs_of_pos hR] using hf
  have hballEq : Metric.closedBall a |R| = Metric.closedBall a R := by
    ext z
    rw [Metric.mem_closedBall, Metric.mem_closedBall]
    rw [abs_of_pos hR]
  have hDiv (u : ℂ) : (MeromorphicOn.divisor f (Metric.closedBall a |R|)) u =
      (MeromorphicOn.divisor f (Metric.closedBall a R)) u := by
    rw [hballEq]
  obtain ⟨g, ε, hε0, hg_an, hg_nz, hfac⟩ := zeroFactor_g hR hfR hfa hfc
  have hfac_abs : ∀ z ∈ Metric.closedBall a R,
      f z = (∏ᶠ u : ℂ, (z - u) ^ ((MeromorphicOn.divisor f (Metric.closedBall a |R|)) u : ℤ)) * g z := by
    intro z hz
    have hz0 := hfac z hz
    have hP : (∏ᶠ u : ℂ, (z - u) ^ ((MeromorphicOn.divisor f (Metric.closedBall a R)) u : ℤ)) =
        (∏ᶠ u : ℂ, (z - u) ^ ((MeromorphicOn.divisor f (Metric.closedBall a |R|)) u : ℤ)) := by
      apply finprod_congr
      intro u
      congr 1
      exact (hDiv u).symm
    rw [hP] at hz0
    exact hz0
  let mu : ℂ → ℝ := fun u => (((MeromorphicOn.divisor f (Metric.closedBall a |R|)) u : ℤ) : ℝ)
  have hfin : (MeromorphicOn.divisor f (Metric.closedBall a |R|)).support.Finite := by
    exact (MeromorphicOn.divisor f (Metric.closedBall a |R|)).finiteSupport
      (isCompact_closedBall a |R|)
  let S : Finset ℂ := hfin.toFinset
  have hS_mem : ∀ u : ℂ, u ∈ S ↔ (MeromorphicOn.divisor f (Metric.closedBall a |R|)) u ≠ 0 := by
    intro u
    rw [Set.Finite.mem_toFinset, Function.mem_support]
  have hS_ball : ∀ u ∈ S, ‖u - a‖ < R := by
    intro u hu
    have hDneR : (MeromorphicOn.divisor f (Metric.closedBall a R)) u ≠ 0 := by
      rw [← hDiv u]
      exact (hS_mem u).mp hu
    exact divisor_support_openBall hR hfR hfa hfc u hDneR
  have hS_ne_a : ∀ u ∈ S, u ≠ a := by
    intro u hu hua
    have hD0R : (MeromorphicOn.divisor f (Metric.closedBall a R)) a = 0 :=
      divisor_zero_at_center hR hfR hfa
    have hDneR : (MeromorphicOn.divisor f (Metric.closedBall a R)) u ≠ 0 := by
      rw [← hDiv u]
      exact (hS_mem u).mp hu
    exact hDneR (by simpa [hua] using hD0R)
  let M : ℂ → ℂ := fun u => a + ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹
  have hM_out {u : ℂ} (huS : u ∈ S) : M u ∉ Metric.closedBall a |R| := by
    intro hmem
    have huρ : ‖u - a‖ < R := hS_ball u huS
    have hua : u ≠ a := hS_ne_a u huS
    have hnorm : ‖M u - a‖ = (R * R : ℝ) / ‖u - a‖ := by
      simpa [M] using norm_mirror hR hua
    have hpos : 0 < ‖u - a‖ := by exact norm_pos_iff.mpr (sub_ne_zero.mpr hua)
    have hgt : R < ‖M u - a‖ := by
      rw [hnorm]
      rw [lt_div_iff₀ hpos]
      nlinarith [sq_pos_of_pos hR]
    have hleR : ‖M u - a‖ ≤ |R| := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hmem
    have hleR' : ‖M u - a‖ ≤ R := by simpa [abs_of_pos hR] using hleR
    exact (not_lt_of_ge hleR') hgt
  have hM_ne_a {u : ℂ} (huS : u ∈ S) : a - M u ≠ 0 := by
    have hua : u ≠ a := hS_ne_a u huS
    have hnorm : ‖M u - a‖ = (R * R : ℝ) / ‖u - a‖ := by
      simpa [M] using norm_mirror hR hua
    have hpos : 0 < ‖u - a‖ := by exact norm_pos_iff.mpr (sub_ne_zero.mpr hua)
    have hnorm0 : 0 < ‖a - M u‖ := by
      rw [norm_sub_rev]
      rw [hnorm]
      exact div_pos (mul_pos hR hR) hpos
    exact norm_pos_iff.mp hnorm0
  let H : ℂ → ℝ := fun z => Real.log ‖g z‖ +
      ∑ u ∈ S, mu u * Real.log ‖z - M u‖
  let Cc : ℝ := ∑ u ∈ S, mu u * Real.log (‖u - a‖ / R)
  let Hp : ℂ → ℝ := fun z => H z + Cc
  have hg_a : DifferentiableAt ℂ g a := (hg_an a (Metric.mem_ball_self (add_pos hR hε0))).differentiableAt
  have hg0 : g a ≠ 0 := hg_nz a (Metric.mem_ball_self (add_pos hR hε0))
  have hBoundary : ∀ z : ℂ, ‖z - a‖ = R → Real.log ‖f z‖ = Hp z := by
    intro z hz
    have hb := log_boundary_factor hR hfac_abs
      (fun z hz => hg_nz z (Metric.closedBall_subset_ball (lt_add_of_pos_right R hε0) hz))
      hf hfa hfc (S := S) hS_mem hz
    have hsplit : (∑ u ∈ S, mu u * (Real.log ‖z - M u‖ + Real.log (‖u - a‖ / R))) =
        (∑ u ∈ S, mu u * Real.log ‖z - M u‖) +
          (∑ u ∈ S, mu u * Real.log (‖u - a‖ / R)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u hu
      ring
    dsimp [Hp, H, Cc]
    calc
      Real.log ‖f z‖ = Real.log ‖g z‖ +
          ∑ u ∈ S, mu u * (Real.log ‖z - M u‖ + Real.log (‖u - a‖ / R)) := by
        simpa [M, mu] using hb
      _ = Real.log ‖g z‖ + ((∑ u ∈ S, mu u * Real.log ‖z - M u‖) +
            (∑ u ∈ S, mu u * Real.log (‖u - a‖ / R))) := by
        rw [hsplit]
      _ = (Real.log ‖g z‖ + ∑ u ∈ S, mu u * Real.log ‖z - M u‖) +
            (∑ u ∈ S, mu u * Real.log (‖u - a‖ / R)) := by ring
  have hHarmonic : InnerProductSpace.HarmonicOnNhd H (Metric.closedBall a |R|) := by
    have hLogG : InnerProductSpace.HarmonicOnNhd (fun z : ℂ => Real.log ‖g z‖)
        (Metric.closedBall a |R|) := by
      intro x hx
      have hxBall : x ∈ Metric.ball a (R + ε) := by
        exact Metric.mem_ball.mpr (by
          rw [dist_eq_norm]
          have hle : ‖x - a‖ ≤ |R| := by
            simpa [Metric.mem_closedBall, dist_eq_norm] using hx
          have : ‖x - a‖ ≤ R := by simpa [abs_of_pos hR] using hle
          exact lt_of_le_of_lt this (lt_add_of_pos_right R hε0))
      exact (hg_an x hxBall).harmonicAt_log_norm (hg_nz x hxBall)
    have hLogM : ∀ u ∈ S, InnerProductSpace.HarmonicOnNhd
        (fun z : ℂ => Real.log ‖z - M u‖) (Metric.closedBall a |R|) := by
      intro u hu
      exact harmonicOnNhd_log_norm_sub hR (hM_out hu)
    have hSumH : InnerProductSpace.HarmonicOnNhd
        (fun z : ℂ => ∑ u ∈ S, mu u * Real.log ‖z - M u‖)
        (Metric.closedBall a |R|) := by
      exact harmonicOnNhd_finset_sum (s := S) (c := mu)
        (h := fun u z => Real.log ‖z - M u‖) hLogM
    have hH_eq : H = (fun z : ℂ => Real.log ‖g z‖) +
        (fun z : ℂ => ∑ u ∈ S, mu u * Real.log ‖z - M u‖) := by
      funext z
      rfl
    rw [hH_eq]
    exact hLogG.add hSumH
  have hHarmonicP : InnerProductSpace.HarmonicOnNhd Hp (Metric.closedBall a |R|) := by
    have hConst : InnerProductSpace.HarmonicOnNhd (fun _ : ℂ => Cc)
        (Metric.closedBall a |R|) := by
      simpa using (InnerProductSpace.harmonicOnNhd_const Cc : InnerProductSpace.HarmonicOnNhd (fun _ : ℂ => Cc) (Metric.closedBall a |R|))
    have hEq : Hp = (fun z : ℂ => H z) + (fun _ : ℂ => Cc) := by rfl
    rw [hEq]
    exact hHarmonic.add hConst
  have hCosAvgP : (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ * Hp (circleMap a R θ)) =
      Real.pi * R * deriv (fun t : ℝ => Hp (a + (t : ℂ))) 0 :=
    cosAvg_harmonic hR hHarmonicP
  have hDerivH : HasDerivAt (fun t : ℝ => H (a + (t : ℂ)))
      (Complex.re (deriv g a / g a) +
        ∑ u ∈ S, mu u * Complex.re (1 / (a - M u))) 0 := by
    have hst := deriv_aux_harmonic hR (g := g) (M := M)
      (D := fun u => MeromorphicOn.divisor f (Metric.closedBall a |R|) u) (S := S)
      hg_a hg0 (fun u hu => hM_ne_a hu)
    simpa [H, mu, M] using hst
  have hDerivHp : deriv (fun t : ℝ => Hp (a + (t : ℂ))) 0 =
      (Complex.re (deriv g a / g a) +
        ∑ u ∈ S, mu u * Complex.re (1 / (a - M u))) := by
    have hc : HasDerivAt (fun _ : ℝ => Cc) 0 0 := by
      simpa using (hasDerivAt_const (0 : ℝ) Cc)
    have hAdd0 : HasDerivAt ((fun t : ℝ => H (a + (t : ℂ))) + (fun _ : ℝ => Cc))
        (Complex.re (deriv g a / g a) +
          ∑ u ∈ S, mu u * Complex.re (1 / (a - M u))) 0 := by
      simpa using (hDerivH.add hc)
    have hcur : (fun t : ℝ => H (a + (t : ℂ))) + (fun _ : ℝ => Cc) =ᶠ[𝓝 (0 : ℝ)]
        (fun t : ℝ => H (a + (t : ℂ)) + Cc) := by
      exact Filter.Eventually.of_forall (fun t => rfl)
    have hAdd : HasDerivAt (fun t : ℝ => H (a + (t : ℂ)) + Cc)
        (Complex.re (deriv g a / g a) +
          ∑ u ∈ S, mu u * Complex.re (1 / (a - M u))) 0 :=
      hAdd0.congr_of_eventuallyEq hcur
    have hcur' : (fun t : ℝ => Hp (a + (t : ℂ))) =ᶠ[𝓝 (0 : ℝ)]
        (fun t : ℝ => H (a + (t : ℂ)) + Cc) := by
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [Hp])
    have hAddP : HasDerivAt (fun t : ℝ => Hp (a + (t : ℂ)))
        (Complex.re (deriv g a / g a) +
          ∑ u ∈ S, mu u * Complex.re (1 / (a - M u))) 0 :=
      hAdd.congr_of_eventuallyEq hcur'.symm
    exact hAddP.deriv
  have hMirrorSum : (∑ u ∈ S, mu u * Complex.re (1 / (a - M u))) =
      - (∑ u ∈ S, mu u * (u - a).re * ((R : ℝ)⁻¹ * (R : ℝ)⁻¹)) := by
    have hdiv : (R * R : ℝ)⁻¹ = (R : ℝ)⁻¹ * (R : ℝ)⁻¹ := by rw [mul_inv]
    calc
      (∑ u ∈ S, mu u * Complex.re (1 / (a - M u)))
          = (∑ u ∈ S, mu u * (-((u - a).re) / (R * R : ℝ))) := by
              apply Finset.sum_congr rfl
              intro u hu
              congr 1
              exact re_one_sub_mirror hR (hS_ne_a u hu)
      _ = ∑ u ∈ S, -(mu u * (u - a).re * ((R * R : ℝ)⁻¹)) := by
              apply Finset.sum_congr rfl
              intro u hu
              ring
      _ = - (∑ u ∈ S, mu u * (u - a).re * ((R * R : ℝ)⁻¹)) := by
              rw [Finset.sum_neg_distrib]
      _ = - (∑ u ∈ S, mu u * (u - a).re * ((R : ℝ)⁻¹ * (R : ℝ)⁻¹)) := by
              congr 1
              apply Finset.sum_congr rfl
              intro u hu
              rw [hdiv]
  have hLHS : (deriv f a / f a).re =
      (deriv g a / g a).re +
        ∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall a |R|)) u : ℤ) : ℝ) *
          (1 / (a - u)).re := by
    exact deriv_log_factor hR hfac_abs hf hg_a hg0 hfa hfc
  have hLHS_fin : (deriv f a / f a).re =
      (deriv g a / g a).re +
        ∑ u ∈ S, mu u * (1 / (a - u)).re := by
    rw [hLHS]
    congr 1
    apply finsum_eq_sum_of_support_subset
    intro u hu
    rw [Function.mem_support] at hu
    have hcoef_ne : (((MeromorphicOn.divisor f (Metric.closedBall a |R|)) u : ℤ) : ℝ) ≠ 0 := by
      intro hc
      apply hu
      simp [hc]
    have hDne : (MeromorphicOn.divisor f (Metric.closedBall a |R|)) u ≠ 0 := by
      intro hD
      apply hcoef_ne
      simp [hD]
    simpa using (hS_mem u).mpr hDne
  have hSumSub : (∑ u ∈ S, mu u * (1 / (a - u)).re) =
      - (∑ u ∈ S, mu u * (u - a).re * (((‖u - a‖ : ℝ) ^ 2)⁻¹)) := by
    calc
      (∑ u ∈ S, mu u * (1 / (a - u)).re)
          = (∑ u ∈ S, mu u * (-((u - a).re) / ‖u - a‖ ^ 2)) := by
              apply Finset.sum_congr rfl
              intro u hu
              rw [re_one_sub (hS_ne_a u hu)]
      _ = ∑ u ∈ S, -(mu u * (u - a).re * ((‖u - a‖ : ℝ) ^ 2)⁻¹) := by
              apply Finset.sum_congr rfl
              intro u hu
              ring
      _ = - (∑ u ∈ S, mu u * (u - a).re * (((‖u - a‖ : ℝ) ^ 2)⁻¹)) := by
              rw [Finset.sum_neg_distrib]
  have hL : (deriv f a / f a).re =
      (deriv g a / g a).re -
        (∑ u ∈ S, mu u * (u - a).re * (((‖u - a‖ : ℝ) ^ 2)⁻¹)) := by
    rw [hLHS_fin, hSumSub]
    ring
  have hIcircle : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.cos θ * Real.log ‖f (circleMap a R θ)‖) =
      Real.pi * R * deriv (fun t : ℝ => Hp (a + (t : ℂ))) 0 := by
    calc
      (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ * Real.log ‖f (circleMap a R θ)‖)
          = (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ * Hp (circleMap a R θ)) := by
              apply intervalIntegral.integral_congr
              intro θ hθ
              have hsp : ‖circleMap a R θ - a‖ = R := by
                rw [circleMap_sub_center a R θ, norm_circleMap_zero, abs_of_pos hR]
              change Real.cos θ * Real.log ‖f (circleMap a R θ)‖ =
                Real.cos θ * Hp (circleMap a R θ)
              rw [hBoundary (circleMap a R θ) hsp]
      _ = Real.pi * R * deriv (fun t : ℝ => Hp (a + (t : ℂ))) 0 := hCosAvgP
  have hArg (θ : ℝ) : a + (R : ℝ) * cexp (Complex.I * (θ : ℂ)) = circleMap a R θ := by
    rw [← circleMap_eq_exp a R θ]
  have hIarg : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.cos θ * Real.log ‖f (a + (R : ℝ) * cexp (Complex.I * (θ : ℂ)))‖) =
      (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ * Real.log ‖f (circleMap a R θ)‖) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    change Real.cos θ * Real.log ‖f (a + (R : ℝ) * cexp (Complex.I * (θ : ℂ)))‖ =
      Real.cos θ * Real.log ‖f (circleMap a R θ)‖
    rw [hArg θ]
  have hBval : (1 / (Real.pi * R)) * (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.cos θ * Real.log ‖f (a + (R : ℝ) * Complex.exp (Complex.I * (θ : ℂ)))‖) =
      (deriv g a / g a).re -
        (∑ u ∈ S, mu u * (u - a).re * ((R : ℝ)⁻¹ * (R : ℝ)⁻¹)) := by
    have hpi0 : Real.pi * R ≠ 0 := by positivity
    calc
      (1 / (Real.pi * R)) * (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.cos θ * Real.log ‖f (a + (R : ℝ) * cexp (Complex.I * (θ : ℂ)))‖)
          = (1 / (Real.pi * R)) * (Real.pi * R * deriv (fun t : ℝ => Hp (a + (t : ℂ))) 0) := by
              rw [hIarg, hIcircle]
      _ = deriv (fun t : ℝ => Hp (a + (t : ℂ))) 0 := by
              field_simp [hpi0]
      _ = (Complex.re (deriv g a / g a) +
          ∑ u ∈ S, mu u * Complex.re (1 / (a - M u))) := hDerivHp
      _ = (deriv g a / g a).re -
          (∑ u ∈ S, mu u * (u - a).re * ((R : ℝ)⁻¹ * (R : ℝ)⁻¹)) := by
          rw [hMirrorSum]
          ring
  have hFinR : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall a |R|)) u : ℤ) : ℝ) *
          ((u - a).re) * (((‖u - a‖ : ℝ) ^ 2)⁻¹ - (R : ℝ)⁻¹ * (R : ℝ)⁻¹)) =
      ∑ u ∈ S, mu u * (u - a).re * (((‖u - a‖ : ℝ) ^ 2)⁻¹ - (R : ℝ)⁻¹ * (R : ℝ)⁻¹) := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    rw [Function.mem_support] at hu
    have hcoef_ne : (((MeromorphicOn.divisor f (Metric.closedBall a |R|)) u : ℤ) : ℝ) ≠ 0 := by
      intro hc
      apply hu
      simp [hc]
    have hDne : (MeromorphicOn.divisor f (Metric.closedBall a |R|)) u ≠ 0 := by
      intro hD
      apply hcoef_ne
      simp [hD]
    simpa using (hS_mem u).mpr hDne
  have hA : (∑ u ∈ S, mu u * (u - a).re * (((‖u - a‖ : ℝ) ^ 2)⁻¹ - (R : ℝ)⁻¹ * (R : ℝ)⁻¹)) =
      (∑ u ∈ S, mu u * (u - a).re * (((‖u - a‖ : ℝ) ^ 2)⁻¹)) -
        (∑ u ∈ S, mu u * (u - a).re * ((R : ℝ)⁻¹ * (R : ℝ)⁻¹)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    ring
  rw [hL]
  rw [hFinR]
  rw [hA]
  rw [hBval]
  ring
