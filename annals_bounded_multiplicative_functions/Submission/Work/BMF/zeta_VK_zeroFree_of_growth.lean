import Mathlib
import Submission.Commons.Analysis.Complex.jensenCarleman_main
import Submission.Commons.NumberTheory.Zeta.zeta_strip_growth
import Submission.Commons.NumberTheory.Zeta.zeta_lower_bound_right_of_one
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_largeHeight
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis
import Submission.Commons.NumberTheory.Zeta.mangoldt_series_re
import Submission.Work.BMF.VKdenom
import Submission.Commons.Analysis.ExpLog.sum_Icc_one_div_le_log_add_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false
set_option maxHeartbeats 3000000

namespace Work.BMF

open Complex Metric Set Filter
open scoped Real Topology BigOperators

noncomputable section

/-! ## Jensen/Carlemann zero-detection on a ball, restricted to a subset of zeros -/

lemma jensenCarleman_subset {f : ℂ → ℂ} {a : ℂ} {R K : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall a |R|)) (hfa : f a ≠ 0)
    (hsphere : ∀ u : ℂ, ‖u - a‖ = R → f u ≠ 0)
    (hleft : ∀ u : ℂ, f u = 0 → u ∈ Metric.closedBall a |R| → u.re < a.re)
    (S : Finset ℂ) (hS : ∀ u ∈ S, f u = 0 ∧ u ∈ Metric.closedBall a |R|)
    (harc : ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (-Real.cos θ) * Real.log ‖f (a + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ ≤ K) :
    -(deriv f a / f a).re ≤
      (∑ u ∈ S, ((MeromorphicOn.divisor f (Metric.closedBall a |R|)) u : ℝ) *
        (u - a).re * ((‖u - a‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹)) + K / (Real.pi * R) := by
  classical
  set Dl : Function.locallyFinsuppWithin (Metric.closedBall a |R|) ℤ :=
    MeromorphicOn.divisor f (Metric.closedBall a |R|) with hDl
  set D : ℂ → ℤ := ⇑Dl with hD
  set g : ℂ → ℝ := fun u => (D u : ℝ) * (u - a).re * ((‖u - a‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹) with hg
  have hfin : D.support.Finite := Dl.finiteSupport (isCompact_closedBall a |R|)
  set T : Finset ℂ := hfin.toFinset with hT
  have hTmem : ∀ u : ℂ, u ∈ T ↔ D u ≠ 0 := by
    intro u; rw [hT, Set.Finite.mem_toFinset, Function.mem_support]
  let I0 : ℝ := ∫ θ in (0:ℝ)..(2*Real.pi),
    Real.cos θ * Real.log ‖f (a + (R:ℂ) * Complex.exp (Complex.I * (θ:ℂ)))‖
  let J0 : ℝ := ∫ θ in (0:ℝ)..(2*Real.pi),
    (-Real.cos θ) * Real.log ‖f (a + (R:ℂ) * Complex.exp (Complex.I * (θ:ℂ)))‖
  have hid : (deriv f a / f a).re = -(∑ᶠ u : ℂ, g u) + 1/(Real.pi * R) * I0 := by
    have h := Commons.Analysis.Complex.jensenCarleman_main hR hf hfa hsphere
    simp only [hg, hD, hDl, I0] at h ⊢
    simpa using h
  have hJI : J0 = -I0 := by
    simp only [J0, I0]
    rw [show (∫ θ in (0:ℝ)..(2*Real.pi),
          (-Real.cos θ) * Real.log ‖f (a + (R:ℂ) * Complex.exp (Complex.I * (θ:ℂ)))‖)
        = ∫ θ in (0:ℝ)..(2*Real.pi),
            -(Real.cos θ * Real.log ‖f (a + (R:ℂ) * Complex.exp (Complex.I * (θ:ℂ)))‖) from by
          apply intervalIntegral.integral_congr; intro θ _; ring]
    rw [intervalIntegral.integral_neg]
  have hJle : J0 ≤ K := by simp only [J0, I0] at *; exact harc
  have hB : -(deriv f a / f a).re ≤ (∑ᶠ u : ℂ, g u) + K/(Real.pi*R) := by
    have hmain : -(deriv f a / f a).re = (∑ᶠ u : ℂ, g u) - (1/(Real.pi*R)) * I0 := by
      rw [hid]; ring
    rw [hmain]
    have hineq : -((1/(Real.pi*R)) * I0) ≤ K/(Real.pi*R) := by
      have h2 : -((1/(Real.pi*R)) * I0) = (1/(Real.pi*R)) * J0 := by rw [hJI]; ring
      rw [h2]
      have h3 : (1/(Real.pi*R)) * J0 ≤ (1/(Real.pi*R)) * K :=
        mul_le_mul_of_nonneg_left hJle (by positivity)
      have h4 : (1/(Real.pi*R)) * K = K/(Real.pi*R) := by ring
      linarith [h3, h4.le, h4.ge]
    calc (∑ᶠ u : ℂ, g u) - (1/(Real.pi*R)) * I0
        = (∑ᶠ u : ℂ, g u) + (-((1/(Real.pi*R)) * I0)) := by ring
      _ ≤ (∑ᶠ u : ℂ, g u) + K/(Real.pi*R) := add_le_add (le_refl _) hineq
  have hC : (∑ᶠ u : ℂ, g u) ≤ ∑ u ∈ S, g u := by
    have heq : (∑ᶠ u : ℂ, g u) = ∑ u ∈ T, g u := by
      refine finsum_eq_sum_of_support_subset g ?_
      intro u hu
      rw [Function.mem_support] at hu
      simp only [Finset.mem_coe]
      rw [hTmem]
      intro h0; exact hu (by simp [hg, h0])
    rw [heq]
    have hg_nonpos : ∀ u ∈ T, u ∉ S → g u ≤ 0 := by
      intro u huT huS
      have hDne : D u ≠ 0 := (hTmem u).mp huT
      have hDne' : Dl u ≠ 0 := by rwa [hD] at hDne
      have huzero : f u = 0 := Commons.Analysis.Complex.zero_of_divisor_ne_zero hf hDne'
      have hucb : u ∈ Metric.closedBall a |R| := Dl.supportWithinDomain hDne'
      have hDpos : (0:ℝ) < (D u : ℝ) := by
        have hnn : (0:ℝ) ≤ ((D u : ℤ) : ℝ) := by
          have h2 : (0:ℝ) ≤ ((Dl u : ℤ) : ℝ) := by
            exact_mod_cast Commons.Analysis.Complex.divisor_nonneg_on_closedBall hf u
          rwa [← hD] at h2
        have hne : ((D u : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hDne
        exact lt_of_le_of_ne hnn (Ne.symm hne)
      have hre : (u - a).re < 0 := by
        have h := hleft u huzero hucb
        simp only [Complex.sub_re]
        linarith
      have hnorm_lt : ‖u - a‖ < R := by
        have hle : ‖u - a‖ ≤ R := by
          have hh := Metric.mem_closedBall.mp hucb
          rw [dist_eq_norm] at hh; rw [abs_of_pos hR] at hh; exact hh
        rcases lt_or_eq_of_le hle with h | h
        · exact h
        · exact absurd (hsphere u h) (by simp [huzero])
      have hnorm_pos : 0 < ‖u - a‖ := by
        rw [norm_pos_iff]; intro h0
        have hua : u = a := sub_eq_zero.mp h0
        rw [hua] at huzero; exact hfa huzero
      have hcoef : 0 < (‖u - a‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹ := by
        have h1 : ‖u - a‖ ^ 2 < R ^ 2 := by nlinarith [hnorm_lt, hnorm_pos]
        have h2 : (0:ℝ) < ‖u - a‖ ^ 2 := by positivity
        have h3 : (R ^ 2)⁻¹ < (‖u - a‖ ^ 2)⁻¹ := by
          rw [inv_lt_inv₀ (by positivity : (0:ℝ) < R^2) h2]; exact h1
        have h4 : R⁻¹ * R⁻¹ = (R^2)⁻¹ := by rw [← mul_inv]; ring
        rw [h4]; linarith
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hDpos.le hre.le) hcoef.le
    have hsplitT : ∑ u ∈ T, g u = ∑ u ∈ T.filter (fun u => u ∈ S), g u +
        ∑ u ∈ T.filter (fun u => ¬ u ∈ S), g u := by
      rw [Finset.sum_filter_add_sum_filter_not]
    have hsplitS : ∑ u ∈ S, g u = ∑ u ∈ S.filter (fun u => u ∈ T), g u +
        ∑ u ∈ S.filter (fun u => ¬ u ∈ T), g u := by
      rw [Finset.sum_filter_add_sum_filter_not]
    have hneg : ∑ u ∈ T.filter (fun u => ¬ u ∈ S), g u ≤ 0 := by
      apply Finset.sum_nonpos
      intro u hu
      rw [Finset.mem_filter] at hu
      exact hg_nonpos u hu.1 hu.2
    have hzero : ∑ u ∈ S.filter (fun u => ¬ u ∈ T), g u = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨huS, huT⟩ := hu
      have hD0 : D u = 0 := by
        by_contra h; exact huT ((hTmem u).mpr h)
      simp [hg, hD0]
    have hfilt : T.filter (fun u => u ∈ S) = S.filter (fun u => u ∈ T) := by
      ext u; simp only [Finset.mem_filter]; tauto
    rw [hsplitT, hsplitS, hfilt]
    linarith [hneg, hzero]
  have hfin2 : (∑ u ∈ S, g u) = ∑ u ∈ S,
      ((MeromorphicOn.divisor f (Metric.closedBall a |R|)) u : ℝ) *
        (u - a).re * ((‖u - a‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹) := by
    apply Finset.sum_congr rfl
    intro u _
    simp only [hg, hD, hDl]
  rw [← hfin2]
  exact hB.trans (add_le_add hC le_rfl)

/-! ## The 3-4-1 trigonometric inequality for the log-derivative of ζ -/

lemma zeta_logDeriv_three_four_one (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (-deriv riemannZeta ((σ : ℂ)) / riemannZeta ((σ : ℂ))).re
      + 4 * (-deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) /
              riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))).re
      + (-deriv riemannZeta (((σ : ℂ) + (2 * t : ℂ) * Complex.I)) /
              riemannZeta (((σ : ℂ) + (2 * t : ℂ) * Complex.I))).re := by
  have hcos_summable : ∀ s : ℝ, Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt (n+1) : ℝ) * Real.cos (s * Real.log ((n+1:ℕ):ℝ)) /
        ((n+1:ℕ):ℝ)^σ) := by
    intro s
    have hbase : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt (n+1) : ℝ) /
        ((n+1:ℕ):ℝ)^σ) :=
      (summable_nat_add_iff 1).2 (Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow (σ := σ) hσ)
    refine Summable.of_norm ?_
    apply Summable.of_nonneg_of_le
      (g := fun n : ℕ => ‖(ArithmeticFunction.vonMangoldt (n+1) : ℝ) *
        Real.cos (s * Real.log ((n+1:ℕ):ℝ)) / ((n+1:ℕ):ℝ)^σ‖)
      (f := fun n : ℕ => (ArithmeticFunction.vonMangoldt (n+1) : ℝ) / ((n+1:ℕ):ℝ)^σ)
    · intro n; exact norm_nonneg _
    · intro n
      have hpos : (0:ℝ) < ((n+1:ℕ):ℝ)^σ := Real.rpow_pos_of_pos (by positivity) σ
      have hΛ0 : 0 ≤ (ArithmeticFunction.vonMangoldt (n+1) : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
      have hc : |Real.cos (s * Real.log ((n+1:ℕ):ℝ))| ≤ 1 := Real.abs_cos_le_one _
      rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hΛ0,
        abs_of_nonneg hpos.le]
      exact div_le_div_of_nonneg_right (mul_le_of_le_one_right hΛ0 hc) hpos.le
    · exact hbase
  set f0 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt (n+1) : ℝ) *
      Real.cos (0 * Real.log ((n+1:ℕ):ℝ)) / ((n+1:ℕ):ℝ)^σ with hf0def
  set f1 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt (n+1) : ℝ) *
      Real.cos (t * Real.log ((n+1:ℕ):ℝ)) / ((n+1:ℕ):ℝ)^σ with hf1def
  set f2 : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt (n+1) : ℝ) *
      Real.cos ((2*t) * Real.log ((n+1:ℕ):ℝ)) / ((n+1:ℕ):ℝ)^σ with hf2def
  have hs0 : Summable f0 := by simpa only [hf0def] using hcos_summable 0
  have hs1 : Summable f1 := by simpa only [hf1def] using hcos_summable t
  have hs2 : Summable f2 := by simpa only [hf2def] using hcos_summable (2*t)
  have e0 : (-deriv riemannZeta ((σ : ℂ)) / riemannZeta ((σ : ℂ))).re = ∑' n, f0 n := by
    have h := Commons.NumberTheory.Zeta.mangoldt_series_re σ hσ 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
    rw [h]
    apply tsum_congr; intro n; simp [hf0def]
  have e1 : (-deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) /
              riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))).re = ∑' n, f1 n := by
    have h := Commons.NumberTheory.Zeta.mangoldt_series_re σ hσ t
    rw [h]
  have e2 : (-deriv riemannZeta (((σ : ℂ) + (2 * t : ℂ) * Complex.I)) /
              riemannZeta (((σ : ℂ) + (2 * t : ℂ) * Complex.I))).re = ∑' n, f2 n := by
    have h := Commons.NumberTheory.Zeta.mangoldt_series_re σ hσ (2*t)
    have harg : ((σ : ℂ) + (2 * t : ℂ) * Complex.I) =
        ((σ : ℂ) + ((2*t : ℝ) : ℂ) * Complex.I) := by push_cast; ring
    rw [harg, h]
  have hlin : 3 * (∑' n, f0 n) + 4 * (∑' n, f1 n) + (∑' n, f2 n) =
      ∑' n, (3 * f0 n + 4 * f1 n + f2 n) := by
    have hfg : Summable (fun n => 3 * f0 n + 4 * f1 n) := (hs0.mul_left 3).add (hs1.mul_left 4)
    calc 3 * (∑' n, f0 n) + 4 * (∑' n, f1 n) + (∑' n, f2 n)
        = (∑' n, 3 * f0 n) + (∑' n, 4 * f1 n) + (∑' n, f2 n) := by
            rw [tsum_mul_left, tsum_mul_left]
      _ = (∑' n, (3 * f0 n + 4 * f1 n)) + (∑' n, f2 n) := by
            rw [← (hs0.mul_left 3).tsum_add (hs1.mul_left 4)]
      _ = ∑' n, ((3 * f0 n + 4 * f1 n) + f2 n) := by rw [← hfg.tsum_add hs2]
      _ = ∑' n, (3 * f0 n + 4 * f1 n + f2 n) := by
            apply tsum_congr; intro n; ring
  rw [e0, e1, e2, hlin]
  apply tsum_nonneg
  intro n
  have hθ : 0 ≤ 3 + 4 * Real.cos (t * Real.log ((n+1:ℕ):ℝ)) +
      Real.cos (2 * (t * Real.log ((n+1:ℕ):ℝ))) := by
    have h2 : Real.cos (2 * (t * Real.log ((n+1:ℕ):ℝ))) =
        2 * Real.cos (t*Real.log ((n+1:ℕ):ℝ))^2 - 1 := Real.cos_two_mul _
    rw [h2]
    nlinarith [sq_nonneg (1 + Real.cos (t*Real.log ((n+1:ℕ):ℝ)))]
  have hΛ0 : 0 ≤ (ArithmeticFunction.vonMangoldt (n+1) : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have hpos : 0 < ((n+1:ℕ):ℝ)^σ := Real.rpow_pos_of_pos (by positivity) σ
  have key : 3 * f0 n + 4 * f1 n + f2 n
      = (ArithmeticFunction.vonMangoldt (n+1) : ℝ) *
        (3 + 4 * Real.cos (t * Real.log ((n+1:ℕ):ℝ)) +
          Real.cos (2 * (t * Real.log ((n+1:ℕ):ℝ)))) / ((n+1:ℕ):ℝ)^σ := by
    simp only [hf0def, hf1def, hf2def]
    rw [zero_mul, Real.cos_zero, mul_one]
    have h2t : (2*t) * Real.log ((n+1:ℕ):ℝ) = 2 * (t * Real.log ((n+1:ℕ):ℝ)) := by ring
    rw [h2t]; ring
  rw [key]
  exact div_nonneg (mul_nonneg hΛ0 hθ) hpos.le

/-! ## A logarithmic upper bound for ζ on `1 ≤ Re s ≤ 2` -/

lemma zeta_log_bound_right :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * Real.log (|t| + 3) := by
  refine ⟨10, by norm_num, ?_⟩
  intro σ t hσ1 hσ2 ht
  set N : ℕ := ⌊|t|⌋₊ + 4 with hNdef
  have hN1 : 1 ≤ N := by rw [hNdef]; omega
  have hN1' : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
  have hNpos : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le zero_lt_one hN1'
  have hNt : |t| + 3 ≤ (N:ℝ) := by
    have h1 : ((⌊|t|⌋₊ : ℕ) : ℝ) ≤ |t| := Nat.floor_le (abs_nonneg t)
    have h2 : |t| < ((⌊|t|⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one |t|
    rw [hNdef]; push_cast; linarith
  have hNle : (N:ℝ) ≤ |t| + 4 := by
    have h1 : ((⌊|t|⌋₊ : ℕ) : ℝ) ≤ |t| := Nat.floor_le (abs_nonneg t)
    rw [hNdef]; push_cast; linarith
  set s : ℂ := (σ:ℂ) + (t:ℂ)*Complex.I with hs
  have hsr : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hs0 : 0 < s.re := by rw [hsr]; linarith
  have hs1 : s ≠ 1 := by
    intro h; have h2 : s.im = 0 := by rw [h]; simp
    rw [hsim] at h2; rw [h2] at ht; simp at ht; linarith
  have hem := Commons.NumberTheory.Zeta.zeta_eq_emN hs0 hs1 N hN1
  have hlem := Commons.NumberTheory.Zeta.emTerm_tsum_le N hN1 s hs0 hs1
  have hP : ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s)))‖ ≤ Real.log (N:ℝ) + 1 := by
    have h2 : ∀ n ∈ Finset.Icc 1 N, ‖(((n : ℕ) : ℂ) ^ (-s))‖ ≤ 1/(n:ℝ) := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hn1' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
      rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < n) (-s), Complex.neg_re, hsr,
          Real.rpow_neg hnpos.le]
      have h3 : (n:ℝ)^(1:ℝ) ≤ (n:ℝ)^σ := Real.rpow_le_rpow_of_exponent_le hn1' (by linarith)
      rw [Real.rpow_one] at h3
      simpa [one_div] using one_div_le_one_div_of_le hnpos h3
    calc ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s)))‖
        ≤ ∑ n ∈ Finset.Icc 1 N, ‖(((n : ℕ) : ℂ) ^ (-s))‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 N, 1/(n:ℝ) := Finset.sum_le_sum h2
      _ ≤ Real.log (N:ℝ) + 1 := Commons.Analysis.ExpLog.sum_Icc_one_div_le_log_add_one hN1
  have hM : ‖(((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (by omega : 0 < N) (1 - s)]
    rw [show (1 - s).re = 1 - σ from by simp [Complex.sub_re, hsr]]
    have h2 : (N:ℝ)^(1-σ) ≤ 1 := by
      have h3 : (N:ℝ)^(0:ℝ) = 1 := Real.rpow_zero _
      have h4 : (N:ℝ)^(1-σ) ≤ (N:ℝ)^(0:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
      rw [h3] at h4; exact h4
    have h4 : |t| ≤ ‖s - 1‖ := by
      have hh := Complex.abs_im_le_norm (s - 1)
      rw [Complex.sub_im, Complex.one_im, sub_zero, hsim] at hh
      exact hh
    have h5 : (0:ℝ) < ‖s-1‖ := lt_of_lt_of_le (by linarith : (0:ℝ) < |t|) h4
    calc (N:ℝ)^(1-σ)/‖s-1‖ ≤ 1/‖s-1‖ := div_le_div_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ 1 := by rw [div_le_one h5]; linarith
  have hT : ‖(∑' m : ℕ, ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) /
            (1 - s))))‖ ≤ 1 := by
    have h1 := norm_tsum_le_tsum_norm hlem.1.norm
    have h2 : ‖s‖ / s.re * ((N:ℝ) ^ (-s.re)) ≤ 1 := by
      have hsnorm : ‖s‖ ≤ σ + |t| := by
        calc ‖s‖ = ‖(σ:ℂ) + ((t:ℂ)*Complex.I)‖ := by rw [hs]
          _ ≤ ‖(σ:ℂ)‖ + ‖((t:ℂ)*Complex.I)‖ := norm_add_le _ _
          _ = σ + |t| := by
              rw [Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (by linarith : (0:ℝ) ≤ σ)]
              congr 1
              rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have h3 : ((N:ℝ)^(-σ)) ≤ ((N:ℝ)^(-1:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
      have h4 : ‖s‖ / σ ≤ σ + |t| := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < σ)]
        nlinarith [hsnorm, hσ1]
      have h5 : ((N:ℝ)^(-1:ℝ)) ≤ ((|t|+3)⁻¹) := by
        rw [Real.rpow_neg_one]
        simpa [one_div] using one_div_le_one_div_of_le (by linarith : (0:ℝ) < |t|+3) hNt
      calc ‖s‖ / s.re * ((N:ℝ)^(-s.re))
          = ‖s‖ / σ * ((N:ℝ)^(-σ)) := by rw [hsr]
        _ ≤ (σ+|t|) * ((N:ℝ)^(-1:ℝ)) :=
            mul_le_mul h4 h3 (Real.rpow_nonneg hNpos.le _) (by positivity)
        _ ≤ (σ+|t|) * ((|t|+3)⁻¹) := mul_le_mul_of_nonneg_left h5 (by positivity)
        _ ≤ 1 := by
            rw [mul_inv_le_iff₀ (by linarith : (0:ℝ) < |t|+3)]
            linarith
    linarith [h1, h2, hlem.2]
  have hmain : ‖riemannZeta s‖ ≤ Real.log (N:ℝ) + 3 := by
    rw [hem]
    have hthis : ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s))) +
        (((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1) +
        (∑' m : ℕ, ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) /
            (1 - s))))‖ ≤ (Real.log (N:ℝ) + 1) + 1 + 1 := by
      have hA : ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s))) +
          (((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1)‖ ≤
          (Real.log (N:ℝ) + 1) + 1 := by
        calc ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s))) +
              (((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1)‖
            ≤ ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s)))‖ +
              ‖(((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1)‖ := norm_add_le _ _
          _ ≤ (Real.log (N:ℝ) + 1) + 1 := add_le_add hP hM
      calc _ ≤ ‖(∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s))) +
              (((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1)‖ +
              ‖(∑' m : ℕ, ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
                (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) -
                  (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))))‖ := norm_add_le _ _
        _ ≤ ((Real.log (N:ℝ) + 1) + 1) + 1 := add_le_add hA hT
    linarith [hthis]
  have hlogN : Real.log (N:ℝ) ≤ Real.log (|t|+4) := Real.log_le_log hNpos hNle
  have hlog4 : Real.log (|t|+4) ≤ Real.log (|t|+3) + Real.log 2 := by
    rw [← Real.log_mul (by linarith : (|t|+3:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
    exact Real.log_le_log (by linarith) (by linarith)
  have hlog3 : (1:ℝ) ≤ Real.log (|t|+3) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_three]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  calc ‖riemannZeta s‖ ≤ Real.log (N:ℝ) + 3 := hmain
    _ ≤ Real.log (|t|+4) + 3 := by linarith
    _ ≤ (Real.log (|t|+3) + Real.log 2) + 3 := by linarith
    _ ≤ 10 * Real.log (|t|+3) := by linarith

/-! ## Bound for the circle integral of `-cos θ · log‖ζ‖` -/

lemma zeta_arc_bound {A B C c δ τ R : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hc : 0 < c) (hδ : 0 < δ) (hR : 0 < R) (hR1 : R ≤ 1 / 2) (hR4 : 4 * δ + R ≤ 1 / 4)
    (hτ : 4 ≤ |τ|)
    (hgr : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ < 1 → 3 ≤ |t| →
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          A * (|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) * (Real.log (|t| + 3)) ^ (2 / 3 : ℝ))
    (hlogbound : ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → 1 ≤ |t| →
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * Real.log (|t| + 3))
    (hlow : ∀ h t : ℝ, 0 < h → h ≤ 1 / 4 →
        c * h ≤ ‖riemannZeta (((1 + h : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)
    (havoid : ∀ θ : ℝ, riemannZeta (((1 + 4 * δ : ℝ) : ℂ) + (τ : ℂ) * Complex.I +
        (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) ≠ 0) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (-Real.cos θ) * Real.log ‖riemannZeta (((1 + 4 * δ : ℝ) : ℂ) +
          (τ : ℂ) * Complex.I + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ ≤
      2 * Real.pi * (max 0 (Real.log (1 / (4 * c * δ)))
        + max 0 (Real.log A + B * R ^ (3 / 2 : ℝ) * Real.log (|τ| + R + 3)
            + (2 / 3 : ℝ) * Real.log (Real.log (|τ| + R + 3)))
        + max 0 (Real.log C + Real.log (Real.log (|τ| + R + 3)))) := by
  set w : ℝ → ℂ := fun θ => ((1 + 4 * δ : ℝ) : ℂ) + (τ : ℂ) * Complex.I +
      (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) with hwdef
  have hexpre : ∀ θ : ℝ, Complex.exp (Complex.I * (θ : ℂ)) =
      (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := fun θ => by
    rw [mul_comm, Complex.exp_ofReal_mul_I θ]
  have hwre : ∀ θ : ℝ, (w θ).re = 1 + 4 * δ + R * Real.cos θ := by
    intro θ
    simp only [hwdef, hexpre θ, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hwim : ∀ θ : ℝ, (w θ).im = τ + R * Real.sin θ := by
    intro θ
    simp only [hwdef, hexpre θ, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hw_ne_one : ∀ θ : ℝ, w θ ≠ 1 := by
    intro θ h
    have h2 : (w θ).im = 0 := by rw [h]; simp
    have h3 : |τ| ≤ R := by
      have h4 : |τ| ≤ |(w θ).im| + R := by
        rw [hwim θ]
        have h5 : |R * Real.sin θ| ≤ R := by
          rw [abs_mul, abs_of_pos hR]; nlinarith [Real.abs_sin_le_one θ]
        have h6 : |τ| ≤ |τ + R * Real.sin θ| + |R * Real.sin θ| := by
          calc |τ| = |(τ + R*Real.sin θ) + (-(R*Real.sin θ))| := by ring_nf
            _ ≤ |τ + R * Real.sin θ| + |-(R*Real.sin θ)| := abs_add_le _ _
            _ = |τ + R * Real.sin θ| + |R * Real.sin θ| := by rw [abs_neg]
        linarith
      rw [h2] at h4; simpa using h4
    linarith [hτ, hR1]
  set Λ : ℝ := Real.log (1 / (4 * c * δ)) with hΛdef
  set P : ℝ := Real.log A + B * R ^ (3 / 2 : ℝ) * Real.log (|τ| + R + 3)
        + (2 / 3 : ℝ) * Real.log (Real.log (|τ| + R + 3)) with hPdef
  set Q : ℝ := Real.log C + Real.log (Real.log (|τ| + R + 3)) with hQdef
  have hw_cont : Continuous w := by rw [hwdef]; fun_prop
  have hf_cont : ContinuousOn (fun θ : ℝ => (-Real.cos θ) * Real.log ‖riemannZeta (w θ)‖)
      (Set.Icc 0 (2 * Real.pi)) := by
    intro θ hθ
    have hζ : ContinuousAt (fun θ : ℝ => riemannZeta (w θ)) θ :=
      (differentiableAt_riemannZeta (hw_ne_one θ)).continuousAt.comp hw_cont.continuousAt
    exact ((Real.continuous_cos.continuousAt.neg).mul
      (hζ.norm.log (by rw [norm_ne_zero_iff]; exact havoid θ))).continuousWithinAt
  have hpt : ∀ θ : ℝ, (-Real.cos θ) * Real.log ‖riemannZeta (w θ)‖ ≤ max 0 Λ + max 0 P + max 0 Q := by
    intro θ
    have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hcosm1 : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
    have hτab : |(w θ).im| ≤ |τ| + R := by
      rw [hwim θ]
      calc |τ + R * Real.sin θ| ≤ |τ| + |R * Real.sin θ| := abs_add_le _ _
        _ ≤ |τ| + R := by
            have h5 : |R * Real.sin θ| ≤ R := by
              rw [abs_mul, abs_of_pos hR]; nlinarith [Real.abs_sin_le_one θ]
            linarith
    have hτlow : 3 ≤ |(w θ).im| := by
      have h5 : |τ| - R ≤ |(w θ).im| := by
        rw [hwim θ]
        have h6 : |R * Real.sin θ| ≤ R := by
          rw [abs_mul, abs_of_pos hR]; nlinarith [Real.abs_sin_le_one θ]
        have h7 : |τ| ≤ |τ + R * Real.sin θ| + |R * Real.sin θ| := by
          calc |τ| = |(τ + R*Real.sin θ) + (-(R*Real.sin θ))| := by ring_nf
            _ ≤ |τ + R * Real.sin θ| + |-(R*Real.sin θ)| := abs_add_le _ _
            _ = |τ + R * Real.sin θ| + |R * Real.sin θ| := by rw [abs_neg]
        linarith
      linarith [hτ, hR1]
    by_cases hcθ : 0 ≤ Real.cos θ
    · have hσre : (w θ).re = 1 + 4 * δ + R * Real.cos θ := hwre θ
      have hh0 : 0 < (w θ).re - 1 := by rw [hσre]; nlinarith [hδ, hcθ, hR]
      have hhle : (w θ).re - 1 ≤ 1 / 4 := by rw [hσre]; nlinarith [hcos1, hR4, hR]
      have hge := hlow ((w θ).re - 1) ((w θ).im) hh0 hhle
      have harg : ((((1 + ((w θ).re - 1) : ℝ)) : ℂ) + ((w θ).im : ℂ) * Complex.I) = w θ := by
        rw [show (1 + ((w θ).re - 1) : ℝ) = (w θ).re from by ring]
        exact Complex.re_add_im (w θ)
      rw [harg] at hge
      have hge2 : c * (4 * δ) ≤ ‖riemannZeta (w θ)‖ := by
        have h4 : 4 * δ ≤ (w θ).re - 1 := by rw [hσre]; nlinarith [hcθ, hR]
        nlinarith [hge, h4, hc]
      have hlog : Real.log (c * (4 * δ)) ≤ Real.log ‖riemannZeta (w θ)‖ :=
        Real.log_le_log (by positivity) hge2
      have hΛeq : Real.log (c * (4 * δ)) = -Λ := by
        rw [hΛdef, show c * (4 * δ) = 4 * c * δ from by ring, one_div, Real.log_inv]
        ring
      have hneg : -Real.log ‖riemannZeta (w θ)‖ ≤ Λ := by linarith [hlog, hΛeq]
      rw [show (-Real.cos θ) * Real.log ‖riemannZeta (w θ)‖ =
          Real.cos θ * (-Real.log ‖riemannZeta (w θ)‖) from by ring]
      by_cases h : 0 ≤ -Real.log ‖riemannZeta (w θ)‖
      · have h1 : Real.cos θ * (-Real.log ‖riemannZeta (w θ)‖) ≤ max 0 Λ := by
          by_cases hL : Λ ≤ 0
          · rw [max_eq_left hL]
            nlinarith [h, hneg, hcθ]
          · push_neg at hL
            rw [max_eq_right hL.le]
            nlinarith [hneg, hcθ, hcos1]
        linarith [h1, le_max_left (0:ℝ) P, le_max_left (0:ℝ) Q]
      · have hlt : -Real.log ‖riemannZeta (w θ)‖ < 0 := lt_of_not_ge h
        have h3 : Real.cos θ * (-Real.log ‖riemannZeta (w θ)‖) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hcθ hlt.le
        linarith [h3, le_max_left (0:ℝ) Λ, le_max_left (0:ℝ) P, le_max_left (0:ℝ) Q]
    · push_neg at hcθ
      have hΨb : Real.log ‖riemannZeta (w θ)‖ ≤ P ∨ Real.log ‖riemannZeta (w θ)‖ ≤ Q := by
        rcases lt_or_ge (w θ).re 1 with hσlt | hσge
        · left
          have hσhalf : 1 / 2 ≤ (w θ).re := by rw [hwre θ]; nlinarith [hR1, hcosm1, hR, hδ]
          have hgg := hgr (w θ).re (w θ).im hσhalf hσlt hτlow
          rw [Complex.re_add_im (w θ)] at hgg
          have hlt1 : (1 - (w θ).re) ≤ R := by rw [hwre θ]; nlinarith [hcθ, hR]
          have hlt0 : 0 ≤ 1 - (w θ).re := by linarith
          have hexp : ((1 - (w θ).re)) ^ (3 / 2 : ℝ) ≤ R ^ (3 / 2 : ℝ) :=
            Real.rpow_le_rpow hlt0 hlt1 (by norm_num)
          have hX1 : (|(w θ).im| + 3) ^ (B * (1 - (w θ).re) ^ (3 / 2 : ℝ)) ≤
              (|τ| + R + 3) ^ (B * R ^ (3 / 2 : ℝ)) := by
            have hle1 : B * (1 - (w θ).re) ^ (3 / 2 : ℝ) ≤ B * R ^ (3 / 2 : ℝ) := by
              nlinarith [hexp, hB]
            calc (|(w θ).im| + 3) ^ (B * (1 - (w θ).re) ^ (3 / 2 : ℝ))
                ≤ (|(w θ).im| + 3) ^ (B * R ^ (3 / 2 : ℝ)) :=
                  Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (w θ).im]) hle1
              _ ≤ (|τ| + R + 3) ^ (B * R ^ (3 / 2 : ℝ)) :=
                  Real.rpow_le_rpow (by positivity) (by linarith [hτab]) (by positivity)
          have hX2 : (Real.log (|(w θ).im| + 3)) ^ (2 / 3 : ℝ) ≤
              (Real.log (|τ| + R + 3)) ^ (2 / 3 : ℝ) :=
            Real.rpow_le_rpow (Real.log_nonneg (by linarith [abs_nonneg (w θ).im]))
              (Real.log_le_log (by linarith [abs_nonneg (w θ).im]) (by linarith [hτab]))
              (by norm_num)
          have hfin : ‖riemannZeta (w θ)‖ ≤ A * ((|τ| + R + 3) ^ (B * R ^ (3 / 2 : ℝ)) *
              (Real.log (|τ| + R + 3)) ^ (2 / 3 : ℝ)) := by
            have h1 : A * (|(w θ).im| + 3) ^ (B * (1 - (w θ).re) ^ (3 / 2 : ℝ)) *
                (Real.log (|(w θ).im| + 3)) ^ (2 / 3 : ℝ) ≤
                A * ((|τ| + R + 3) ^ (B * R ^ (3 / 2 : ℝ)) *
                  (Real.log (|τ| + R + 3)) ^ (2 / 3 : ℝ)) := by
              calc A * (|(w θ).im| + 3) ^ (B * (1 - (w θ).re) ^ (3 / 2 : ℝ)) *
                    (Real.log (|(w θ).im| + 3)) ^ (2 / 3 : ℝ)
                  = A * ((|(w θ).im| + 3) ^ (B * (1 - (w θ).re) ^ (3 / 2 : ℝ)) *
                    (Real.log (|(w θ).im| + 3)) ^ (2 / 3 : ℝ)) := by ring
                _ ≤ A * ((|τ| + R + 3) ^ (B * R ^ (3 / 2 : ℝ)) *
                    (Real.log (|τ| + R + 3)) ^ (2 / 3 : ℝ)) :=
                    mul_le_mul_of_nonneg_left
                      (mul_le_mul hX1 hX2
                        (Real.rpow_nonneg (Real.log_nonneg
                          (by linarith [abs_nonneg (w θ).im])) _)
                        (Real.rpow_nonneg (by linarith [hτ, abs_nonneg τ, hR]) _)) hA.le
            exact le_trans hgg h1
          have hZpos : (0:ℝ) < |τ| + R + 3 := by linarith [hτ, abs_nonneg τ, hR]
          have hlogZ : (0:ℝ) < Real.log (|τ| + R + 3) := Real.log_pos (by linarith [hτ, abs_nonneg τ, hR])
          have hlogfin : Real.log ‖riemannZeta (w θ)‖ ≤
              Real.log (A * ((|τ| + R + 3) ^ (B * R ^ (3 / 2 : ℝ)) *
                (Real.log (|τ| + R + 3)) ^ (2 / 3 : ℝ))) :=
            Real.log_le_log (by rw [norm_pos_iff]; exact havoid θ) hfin
          have e1 : Real.log (A * ((|τ| + R + 3) ^ (B * R ^ (3 / 2 : ℝ)) *
                (Real.log (|τ| + R + 3)) ^ (2 / 3 : ℝ)))
              = Real.log A + B * R ^ (3 / 2 : ℝ) * Real.log (|τ| + R + 3)
                + (2 / 3 : ℝ) * Real.log (Real.log (|τ| + R + 3)) := by
            rw [Real.log_mul hA.ne' (mul_ne_zero
                  (ne_of_gt (Real.rpow_pos_of_pos hZpos _))
                  (ne_of_gt (Real.rpow_pos_of_pos hlogZ _))),
                Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hZpos _))
                  (ne_of_gt (Real.rpow_pos_of_pos hlogZ _)),
                Real.log_rpow hZpos (B * R ^ (3 / 2 : ℝ)),
                Real.log_rpow hlogZ (2 / 3 : ℝ)]
            ring
          rw [hPdef]
          linarith [hlogfin, e1.le, e1.ge]
        · right
          have hσ2 : (w θ).re ≤ 2 := by rw [hwre θ]; nlinarith [hcosm1, hR4, hR]
          have ht1 : 1 ≤ |(w θ).im| := le_trans (by norm_num) hτlow
          have hb := hlogbound (w θ).re (w θ).im hσge hσ2 ht1
          rw [Complex.re_add_im (w θ)] at hb
          have hfin : ‖riemannZeta (w θ)‖ ≤ C * Real.log (|τ| + R + 3) :=
            le_trans hb (mul_le_mul_of_nonneg_left
              (Real.log_le_log (by linarith [abs_nonneg (w θ).im]) (by linarith [hτab])) hC.le)
          have hlogfin : Real.log ‖riemannZeta (w θ)‖ ≤ Real.log (C * Real.log (|τ| + R + 3)) :=
            Real.log_le_log (by rw [norm_pos_iff]; exact havoid θ) hfin
          have e1 : Real.log (C * Real.log (|τ| + R + 3)) =
              Real.log C + Real.log (Real.log (|τ| + R + 3)) :=
            Real.log_mul hC.ne' (ne_of_gt (Real.log_pos (by linarith [hτ, abs_nonneg τ, hR])))
          rw [hQdef]
          linarith [hlogfin, e1.le, e1.ge]
      rcases hΨb with hb | hb
      · by_cases h : 0 ≤ Real.log ‖riemannZeta (w θ)‖
        · have h1 : (-Real.cos θ) * Real.log ‖riemannZeta (w θ)‖ ≤ Real.log ‖riemannZeta (w θ)‖ := by
            nlinarith [h, hcθ, hcosm1]
          have h2 : Real.log ‖riemannZeta (w θ)‖ ≤ max 0 P := le_trans hb (le_max_right 0 P)
          linarith [h1, h2, le_max_left (0:ℝ) Λ, le_max_left (0:ℝ) Q]
        · have hlt : Real.log ‖riemannZeta (w θ)‖ < 0 := lt_of_not_ge h
          have h1 : (-Real.cos θ) * Real.log ‖riemannZeta (w θ)‖ ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by linarith [hcθ]) hlt.le
          linarith [h1, le_max_left (0:ℝ) Λ, le_max_left (0:ℝ) P, le_max_left (0:ℝ) Q]
      · by_cases h : 0 ≤ Real.log ‖riemannZeta (w θ)‖
        · have h1 : (-Real.cos θ) * Real.log ‖riemannZeta (w θ)‖ ≤ Real.log ‖riemannZeta (w θ)‖ := by
            nlinarith [h, hcθ, hcosm1]
          have h2 : Real.log ‖riemannZeta (w θ)‖ ≤ max 0 Q := le_trans hb (le_max_right 0 Q)
          linarith [h1, h2, le_max_left (0:ℝ) Λ, le_max_left (0:ℝ) P]
        · have hlt : Real.log ‖riemannZeta (w θ)‖ < 0 := lt_of_not_ge h
          have h1 : (-Real.cos θ) * Real.log ‖riemannZeta (w θ)‖ ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by linarith [hcθ]) hlt.le
          linarith [h1, le_max_left (0:ℝ) Λ, le_max_left (0:ℝ) P, le_max_left (0:ℝ) Q]
  have hint1 : IntervalIntegrable (fun θ : ℝ => (-Real.cos θ) * Real.log ‖riemannZeta (w θ)‖)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    ContinuousOn.intervalIntegrable_of_Icc (by positivity) hf_cont
  have hint2 : IntervalIntegrable (fun _ : ℝ => max 0 Λ + max 0 P + max 0 Q)
      MeasureTheory.volume 0 (2 * Real.pi) := intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono (by positivity : (0:ℝ) ≤ 2 * Real.pi) hint1 hint2
      (fun θ => hpt θ)
  have hgoal : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (-Real.cos θ) * Real.log ‖riemannZeta (((1 + 4 * δ : ℝ) : ℂ) +
          (τ : ℂ) * Complex.I + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖) =
      (∫ θ in (0 : ℝ)..(2 * Real.pi), (-Real.cos θ) * Real.log ‖riemannZeta (w θ)‖) := rfl
  rw [hgoal]
  calc (∫ θ in (0 : ℝ)..(2 * Real.pi), (-Real.cos θ) * Real.log ‖riemannZeta (w θ)‖)
      ≤ (∫ θ in (0 : ℝ)..(2 * Real.pi), (max 0 Λ + max 0 P + max 0 Q)) := hmono
    _ = 2 * Real.pi * (max 0 Λ + max 0 P + max 0 Q) := by
        rw [intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]

/-! ## A radius whose circle avoids the zeros of ζ -/

lemma exists_good_sphere (a : ℂ) {x y : ℝ} (hxy : x < y) :
    ∃ R : ℝ, x ≤ R ∧ R ≤ y ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 → ‖ρ - a‖ ≠ R := by
  have hfin : (Metric.closedBall a y ∩ riemannZetaZeros).Finite :=
    (isCompact_closedBall a y).inter_riemannZetaZeros_finite
  set B : Set ℝ := (fun ρ : ℂ => ‖ρ - a‖) '' (Metric.closedBall a y ∩ riemannZetaZeros) with hB
  have hBfin : B.Finite := hfin.image _
  have hnot : ¬ (Set.Icc x y ⊆ B) := fun hsub =>
    (Set.Icc_infinite hxy) (hBfin.subset hsub)
  obtain ⟨R, hR, hRB⟩ := Set.not_subset.mp hnot
  refine ⟨R, hR.1, hR.2, fun ρ hρ heq => hRB ?_⟩
  rw [hB]
  refine ⟨ρ, ⟨?_, ?_⟩, heq⟩
  · rw [Metric.mem_closedBall, dist_eq_norm]
    rw [heq]; exact hR.2
  · rwa [mem_riemannZetaZeros]

/-! ## ζ is zero-free in a strip of bounded height -/

lemma zeta_zeroFree_bounded_height (T : ℝ) (hT : 4 ≤ T) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ σ t : ℝ, |t| ≤ T → 1 - ε ≤ σ → σ ≤ 2 →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  let S₀ : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
    (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (-T) T)
  have hS₀compact : IsCompact S₀ := by
    dsimp [S₀]
    exact (IsCompact.prod isCompact_Icc isCompact_Icc).image
      (by fun_prop : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I))
  have hZfin : (S₀ ∩ riemannZetaZeros).Finite := hS₀compact.inter_riemannZetaZeros_finite
  have hZm : ∀ z : ℂ, z ∈ S₀ ∩ riemannZetaZeros →
      (1 / 2 : ℝ) ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ T ∧ riemannZeta z = 0 := by
    intro z hz
    rcases hz.1 with ⟨p, hp, hpeq⟩
    have hzre : z.re = p.1 := by rw [← hpeq]; simp
    have hzim : z.im = p.2 := by rw [← hpeq]; simp
    refine ⟨by linarith [hp.1.1, hzre], by linarith [hp.1.2, hzre],
      abs_le.mpr (by simpa [hzim] using hp.2), ?_⟩
    simpa [riemannZetaZeros] using hz.2
  have hZre : ∀ z : ℂ, z ∈ S₀ ∩ riemannZetaZeros → z.re < 1 := fun z hz =>
    lt_of_not_ge fun hge => riemannZeta_ne_zero_of_one_le_re (s := z) hge (hZm z hz).2.2.2
  by_cases hemp : (S₀ ∩ riemannZetaZeros) = ∅
  · refine ⟨(1 / 2 : ℝ), by norm_num, fun σ t ht hσlo hσhi hz0 => ?_⟩
    have hsS : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ S₀ := by
      refine ⟨(σ, t), ⟨⟨by linarith, by linarith⟩, abs_le.mp ht⟩, rfl⟩
    have hsZ : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ S₀ ∩ riemannZetaZeros :=
      ⟨hsS, by simpa [riemannZetaZeros] using hz0⟩
    rw [hemp] at hsZ; exact hsZ
  · have hne : (S₀ ∩ riemannZetaZeros).Nonempty := Set.nonempty_iff_ne_empty.mpr hemp
    have hne' : (hZfin.toFinset.image (fun z : ℂ => 1 - z.re)).Nonempty := by
      rcases hne with ⟨z, hz⟩
      exact ⟨1 - z.re, Finset.mem_image.mpr ⟨z, hZfin.mem_toFinset.mpr hz, rfl⟩⟩
    set d : ℝ := (hZfin.toFinset.image (fun z : ℂ => 1 - z.re)).min' hne' with hd
    have hdm : d ∈ hZfin.toFinset.image (fun z : ℂ => 1 - z.re) := Finset.min'_mem _ hne'
    obtain ⟨z₀, hz₀m, hz₀eq⟩ := Finset.mem_image.mp hdm
    have hz₀Z : z₀ ∈ S₀ ∩ riemannZetaZeros := hZfin.mem_toFinset.mp hz₀m
    have hd0 : 0 < d := by have h := hZre z₀ hz₀Z; rw [← hz₀eq]; linarith
    have hdle : ∀ z : ℂ, z ∈ S₀ ∩ riemannZetaZeros → d ≤ 1 - z.re := fun z hz =>
      Finset.min'_le _ _ (Finset.mem_image.mpr ⟨z, hZfin.mem_toFinset.mpr hz, rfl⟩)
    have hdle1 : d ≤ 1 := by
      have h1 := hdle z₀ hz₀Z
      have h2 := (hZm z₀ hz₀Z).1
      linarith
    refine ⟨d / 2, by positivity, fun σ t ht hσlo hσhi hz0 => ?_⟩
    have hsS : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ S₀ := by
      refine ⟨(σ, t), ⟨⟨by linarith [hσlo, hdle1], by linarith⟩, abs_le.mp ht⟩, rfl⟩
    have hsZ : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ S₀ ∩ riemannZetaZeros :=
      ⟨hsS, by simpa [riemannZetaZeros] using hz0⟩
    have h1 : d ≤ 1 - σ := by
      have := hdle _ hsZ
      simpa using this
    have h2 : σ ≤ 1 - d / 2 := by linarith
    linarith

/-! ## A radius avoiding the zeros of ζ on two circles -/

lemma exists_good_sphere_two (a₁ a₂ : ℂ) {x y : ℝ} (hxy : x < y) :
    ∃ R : ℝ, x ≤ R ∧ R ≤ y ∧ (∀ ρ : ℂ, riemannZeta ρ = 0 → ‖ρ - a₁‖ ≠ R) ∧
      (∀ ρ : ℂ, riemannZeta ρ = 0 → ‖ρ - a₂‖ ≠ R) := by
  set B : Set ℝ := (fun ρ : ℂ => ‖ρ - a₁‖) '' (Metric.closedBall a₁ y ∩ riemannZetaZeros) ∪
      (fun ρ : ℂ => ‖ρ - a₂‖) '' (Metric.closedBall a₂ y ∩ riemannZetaZeros) with hB
  have hBfin : B.Finite := by
    rw [hB]
    exact ((isCompact_closedBall a₁ y).inter_riemannZetaZeros_finite.image _).union
      ((isCompact_closedBall a₂ y).inter_riemannZetaZeros_finite.image _)
  have hnot : ¬ (Set.Icc x y ⊆ B) := fun hsub => (Set.Icc_infinite hxy) (hBfin.subset hsub)
  obtain ⟨R, hR, hRB⟩ := Set.not_subset.mp hnot
  refine ⟨R, hR.1, hR.2, ?_, ?_⟩
  · intro ρ hρ heq
    apply hRB; rw [hB]; left
    exact ⟨ρ, ⟨by rw [Metric.mem_closedBall, dist_eq_norm]; rw [heq]; exact hR.2,
      mem_riemannZetaZeros.mpr hρ⟩, heq⟩
  · intro ρ hρ heq
    apply hRB; rw [hB]; right
    exact ⟨ρ, ⟨by rw [Metric.mem_closedBall, dist_eq_norm]; rw [heq]; exact hR.2,
      mem_riemannZetaZeros.mpr hρ⟩, heq⟩

/-! ## The divisor at a zero of ζ is at least one -/

lemma divisor_one_le_at_zero {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : ∀ z ∈ Metric.closedBall a |R|, z ≠ 1) (hfa : riemannZeta a ≠ 0)
    {ρ : ℂ} (hρ : ρ ∈ Metric.ball a R) (hz : riemannZeta ρ = 0) :
    (1 : ℝ) ≤ ((MeromorphicOn.divisor riemannZeta (Metric.closedBall a |R|)) ρ : ℝ) := by
  have hf : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall a |R|) :=
    analyticOn_riemannZeta.mono (fun z hz1 => by simpa using hball z hz1)
  have hρc : ρ ∈ Metric.closedBall a |R| := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h := Metric.mem_ball.mp hρ
    rw [dist_eq_norm] at h
    rw [abs_of_pos hR]
    exact le_of_lt h
  have hρ1 : ρ ≠ 1 := hball ρ hρc
  have hn0 : analyticOrderAt riemannZeta ρ ≠ 0 := by
    intro h0
    rcases (analyticOrderAt_eq_zero.mp h0) with h | h
    · exact h (analyticOn_riemannZeta ρ (by simpa using hρ1))
    · exact h hz
  have hntop : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have hev : riemannZeta =ᶠ[𝓝 ρ] fun _ => (0 : ℂ) := htop
    have hpre : IsPreconnected (Metric.ball a |R|) := (convex_ball a |R|).isPreconnected
    have hfU : AnalyticOnNhd ℂ riemannZeta (Metric.ball a |R|) :=
      hf.mono Metric.ball_subset_closedBall
    have hρb : ρ ∈ Metric.ball a |R| := by rwa [abs_of_pos hR]
    have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hfU analyticOnNhd_const hpre
      hρb hev
    exact hfa (heq (Metric.mem_ball_self (by rw [abs_of_pos hR]; exact hR)))
  have htn : 1 ≤ (analyticOrderAt riemannZeta ρ).toNat := ENat.toNat_pos hn0 hntop
  have hun : (ENat.map Nat.cast ((analyticOrderAt riemannZeta ρ).toNat : ℕ∞)).untop₀ =
      ((analyticOrderAt riemannZeta ρ).toNat : ℤ) := by
    rw [ENat.map_coe, WithTop.untop₀_coe]
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hρc, (ENat.coe_toNat hntop).symm, hun]
  exact_mod_cast htn

/-! ## Arithmetic lemmas for the closing step -/

lemma vk_close_arith {z aa Kb Kc2 : ℝ} (haa : 0 < aa) (hz : 0 < z)
    (hmain : z ≤ Kb * Real.log z + Kc2) (hzge : aa ≤ z) (hKb_le : Kb ≤ aa)
    (hKbnb : 0 ≤ Kb) (hfa : 0 < aa - Kb * Real.log aa - Kc2) : False := by
  have hlogaa : Real.log z - Real.log aa ≤ z / aa - 1 := by
    have h1 : 0 < z / aa := div_pos hz haa
    have h2 := Real.log_le_sub_one_of_pos h1
    rwa [Real.log_div (ne_of_gt hz) (ne_of_gt haa)] at h2
  have hstep : Kb * Real.log z ≤ Kb * Real.log aa + (Kb / aa) * z - Kb := by
    have h1 : Kb * (Real.log z - Real.log aa) ≤ Kb * (z / aa - 1) :=
      mul_le_mul_of_nonneg_left hlogaa hKbnb
    have h2 : Kb * (Real.log z - Real.log aa) = Kb * Real.log z - Kb * Real.log aa := by ring
    have h3 : Kb * (z / aa - 1) = (Kb / aa) * z - Kb := by ring
    linarith only [h1, h2.le, h2.ge, h3.le, h3.ge]
  have hzK : z - (Kb / aa) * z ≤ Kb * Real.log aa - Kb + Kc2 := by
    linarith only [hmain, hstep]
  have hK5le1 : Kb / aa ≤ 1 := by rw [div_le_one haa]; exact hKb_le
  have h4 : aa * (Kb / aa) = Kb := mul_div_cancel₀ Kb (ne_of_gt haa)
  have h1 : aa - Kb ≤ z - (Kb / aa) * z := by
    have h2 : aa * (1 - Kb / aa) ≤ z * (1 - Kb / aa) :=
      mul_le_mul_of_nonneg_right hzge (by linarith only [hK5le1])
    have h3 : aa * (1 - Kb / aa) = aa - Kb := by
      rw [mul_sub, mul_one, h4]
    have h4' : z * (1 - Kb / aa) = z - (Kb / aa) * z := by ring
    linarith only [h2, h3.le, h3.ge, h4'.le, h4'.ge]
  linarith only [h1, hzK, hfa]

lemma vk_z_bound {z δ R V M B Cz K1 K2 : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hδ : 0 < δ) (h8d : 8 * δ ≤ R) (hz : z = 1/δ)
    (hcomb : 1/(20*δ) ≤ 3*Cz + 20*δ/R^2 + (4*K1+K2)/(Real.pi*R))
    (hCzV : 3*Cz ≤ V/10)
    (hRinv : 1/R ≤ 4*(V/M))
    (hK1b : K1/(Real.pi*R) ≤ 8*(V*Real.log z/M) + 8*((10+B)*V))
    (hK2b : K2/(Real.pi*R) ≤ 8*(V*Real.log z/M) + 8*((10+B)*V)) :
    z ≤ (800*(V/M)) * Real.log z + (800*((10+B)*V) + 320*(V/M) + 2*V) := by
  have hz20 : 1/(20*δ) = z/20 := by rw [hz]; field_simp <;> ring
  have h20 : 20*δ/R^2 ≤ 4/R := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < R^2) hR]
    nlinarith only [h8d, hδ, hR]
  have h4R : 4/R ≤ 16*(V/M) := by
    have h := mul_le_mul_of_nonneg_left hRinv (by norm_num : (0:ℝ) ≤ 4)
    have e1 : (4:ℝ) * (4*(V/M)) = 16*(V/M) := by ring
    have e2 : (4:ℝ)/R = 4*(1/R) := by ring
    linarith only [h, e1.le, e1.ge, e2.le, e2.ge]
  have hk : (4*K1+K2)/(Real.pi*R) ≤ 40*(V*Real.log z/M) + 40*((10+B)*V) := by
    have h1 : (4:ℝ) * (K1/(Real.pi*R)) ≤ 4*(8*(V*Real.log z/M) + 8*((10+B)*V)) :=
      mul_le_mul_of_nonneg_left hK1b (by norm_num)
    have e : (4*K1+K2)/(Real.pi*R) = 4*(K1/(Real.pi*R)) + K2/(Real.pi*R) := by ring
    rw [e]
    have e2 : (4:ℝ)*(8*(V*Real.log z/M) + 8*((10+B)*V)) + (8*(V*Real.log z/M) + 8*((10+B)*V))
        = 40*(V*Real.log z/M) + 40*((10+B)*V) := by ring
    linarith only [h1, hK2b, e2.le, e2.ge]
  have h7 : z/20 ≤ V/10 + 16*(V/M) + (40*(V*Real.log z/M) + 40*((10+B)*V)) := by
    linarith only [hcomb, hz20, h20, hCzV, h4R, hk]
  have h8 : z ≤ 20*(V/10 + 16*(V/M) + (40*(V*Real.log z/M) + 40*((10+B)*V))) := by
    have h := mul_le_mul_of_nonneg_left h7 (by norm_num : (0:ℝ) ≤ 20)
    have e : (20:ℝ)*(z/20) = z := by ring
    linarith only [h, e.le, e.ge]
  have h9 : (20:ℝ)*(V/10 + 16*(V/M) + (40*(V*Real.log z/M) + 40*((10+B)*V)))
      = 2*V + 320*(V/M) + 800*(V*Real.log z/M) + 800*((10+B)*V) := by ring
  rw [h9] at h8
  have h10 : 800*(V*Real.log z/M) = (800*(V/M)) * Real.log z := by ring
  rw [h10] at h8
  linarith only [h8]

lemma vk_hfa {V M Kc B aa : ℝ} (hV : 0 < V) (hM1 : 1 ≤ M) (hKcB : 1 + B ≤ Kc) (hB : 0 ≤ B)
    (haa : aa = V * 1000000 * Kc) (hlogaa : Real.log aa ≤ 3 * M) :
    0 < aa - (800 * (V / M)) * Real.log aa - (800 * ((10 + B) * V) + 320 * (V / M) + 2 * V) := by
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hKc1 : 1 ≤ Kc := by linarith only [hKcB, hB]
  have h1 : (800 * (V / M)) * Real.log aa ≤ 2400 * V := by
    have e : (800 * (V / M)) * Real.log aa = 800 * V * (Real.log aa / M) := by field_simp <;> ring
    rw [e]
    have h2 : Real.log aa / M ≤ 3 := by rw [div_le_iff₀ hM0]; linarith only [hlogaa]
    have h3 : (0:ℝ) ≤ 800 * V := by positivity
    nlinarith only [h2, h3]
  have h4 : 320 * (V / M) ≤ 320 * V := by
    have e : (320:ℝ) * (V/M) = 320*V/M := by ring
    rw [e, div_le_iff₀ hM0]
    nlinarith only [hM1, hV]
  have h5 : 800 * ((10 + B) * V) ≤ 8800 * Kc * V := by
    have h6 : (10 + B : ℝ) ≤ 11 * Kc := by linarith only [hKcB, hB]
    nlinarith only [h6, hV]
  rw [haa] at h1
  rw [haa]
  nlinarith only [h1, h4, h5, hV, hKc1]

lemma vk_large {A B Cz clamp clog : ℝ} (hA : 0 < A) (hB : 0 < B) (hCz : 0 < Cz)
    (hclamp : 0 < clamp) (hclog : 0 < clog)
    (hgr : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ < 1 → 3 ≤ |t| →
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          A * (|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) * (Real.log (|t| + 3)) ^ (2 / 3 : ℝ))
    (haxis : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
        (-deriv riemannZeta ((σ : ℂ)) / riemannZeta ((σ : ℂ))).re ≤ 1 / (σ - 1) + Cz)
    (hlow : ∀ h t : ℝ, 0 < h → h ≤ 1 / 4 →
        clamp * h ≤ ‖riemannZeta (((1 + h : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)
    (hlog : ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → 1 ≤ |t| →
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ clog * Real.log (|t| + 3)) :
    ∃ T₀ c : ℝ, 0 < T₀ ∧ 0 < c ∧ ∀ β γ : ℝ, T₀ ≤ |γ| →
      riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) = 0 → 1 - β ≥ c / VKd (|γ| + 3) := by
  have hclamp_inv_pos : 0 < 1 / clamp := by positivity
  refine ⟨Real.exp (Real.exp (Real.exp (10 ^ 12 * (1 + A + B + Cz + clamp + clog + 1 / clamp +
        (1 + A) * (1 + B) * (1 + Cz) * (1 + clamp) * (1 + clog))))),
    1 / (10 ^ 6 * ((1 + A) * (1 + B) * (1 + Cz) * (1 + clamp) * (1 + clog))),
    Real.exp_pos _, by positivity, ?_⟩
  intro β γ hγ hzero
  set Kc : ℝ := (1 + A) * (1 + B) * (1 + Cz) * (1 + clamp) * (1 + clog) with hKc
  set B0 : ℝ := 10 ^ 12 * (1 + A + B + Cz + clamp + clog + 1 / clamp + Kc) with hB0
  set ρ : ℂ := (β : ℂ) + (γ : ℂ) * Complex.I with hρ
  set γ₀ : ℝ := |γ| with hγ₀
  set δ : ℝ := 1 - β with hδ
  set L : ℝ := Real.log (γ₀ + 3) with hL
  set M : ℝ := Real.log L with hM
  set V : ℝ := VKd (γ₀ + 3) with hV
  set c : ℝ := 1 / (10 ^ 6 * Kc) with hc
  have hKcge1 : 1 ≤ Kc := by
    rw [hKc]
    have h1 : 1 ≤ 1 + A := by linarith
    have h2 : 1 ≤ 1 + B := by linarith
    have h3 : 1 ≤ 1 + Cz := by linarith
    have h4 : 1 ≤ 1 + clamp := by linarith
    have h5 : 1 ≤ 1 + clog := by linarith
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)) (by linarith))
        (by linarith)) (by linarith)
  have hKcpos : 0 < Kc := lt_of_lt_of_le zero_lt_one hKcge1
  have hcpos : 0 < c := by rw [hc]; positivity
  have hB0ge1 : 1 ≤ B0 := by
    rw [hB0]
    nlinarith [hA, hB, hCz, hclamp, hclog, hKcge1, hclamp_inv_pos]
  have hγ₀ge : Real.exp (Real.exp (Real.exp B0)) ≤ γ₀ := by rw [hγ₀, hB0, hKc]; exact hγ
  -- L ≥ 10^12
  have hexp_mono : Real.exp (Real.exp B0) ≤ L := by
    rw [hL]
    have h1 : Real.exp (Real.exp B0) ≤ Real.exp (Real.exp (Real.exp B0)) := by
      have := Real.add_one_le_exp (Real.exp B0)
      exact Real.exp_le_exp.mpr (by linarith)
    have h2 : (0:ℝ) < Real.exp (Real.exp B0) := Real.exp_pos _
    have h3 : Real.exp (Real.exp (Real.exp B0)) ≤ γ₀ + 3 := by linarith [hγ₀ge]
    calc Real.exp (Real.exp B0) = Real.log (Real.exp (Real.exp (Real.exp B0))) :=
          (Real.log_exp _).symm
      _ ≤ Real.log (γ₀ + 3) := Real.log_le_log (Real.exp_pos _) h3
  have hLge : (10:ℝ) ^ 12 ≤ L := by
    have h1 : (10:ℝ) ^ 12 ≤ Real.exp (Real.exp B0) := by
      have h2 : (10:ℝ) ^ 12 ≤ Real.exp B0 := by
        have h3 : (10:ℝ) ^ 12 ≤ B0 := by
          rw [hB0]
          nlinarith [hA, hB, hCz, hclamp, hclog, hKcge1, hclamp_inv_pos]
        linarith [Real.add_one_le_exp B0]
      linarith [Real.add_one_le_exp (Real.exp B0)]
    linarith [hexp_mono]
  have hLpos : 0 < L := by linarith
  have hMge : B0 ≤ M := by
    rw [hM]
    have h1 : B0 ≤ Real.exp B0 := by linarith [Real.add_one_le_exp B0]
    have h2 : (0:ℝ) < Real.exp B0 := Real.exp_pos _
    calc B0 ≤ Real.exp B0 := h1
      _ = Real.log (Real.exp (Real.exp B0)) := (Real.log_exp _).symm
      _ ≤ Real.log L := Real.log_le_log (Real.exp_pos _) hexp_mono
  have hMpos : 0 < M := by linarith [hMge]
  have hMle16 : M ≤ L / 16 := by
    have hsqrt32 : (32:ℝ) ≤ Real.sqrt L := by
      rw [show (32:ℝ) = Real.sqrt (32 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by linarith)
    have hlogs : Real.log (Real.sqrt L) = M / 2 := by
      rw [Real.log_sqrt hLpos.le, hM]
    have h1 : M ≤ 2 * Real.sqrt L := by
      have hh := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hLpos)
      rw [hlogs] at hh
      have h2 : (0:ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hLpos
      linarith
    have h2 : 2 * Real.sqrt L ≤ L / 16 := by
      have h4 : Real.sqrt L * Real.sqrt L = L := by
        rw [← sq, Real.sq_sqrt hLpos.le]
      nlinarith [hsqrt32, Real.sqrt_nonneg L]
    linarith
  have hVge1 : 1 ≤ V := by
    rw [hV, VKd_def]
    refine one_le_mul_of_one_le_of_one_le ?_ ?_
    · exact Real.one_le_rpow (by linarith) (by norm_num)
    · exact Real.one_le_rpow (by linarith) (by norm_num)
  have hVpos : 0 < V := lt_of_lt_of_le zero_lt_one hVge1
  have hβlt1 : β < 1 := by
    by_contra hcon
    have h1 : (1:ℝ) ≤ β := not_lt.mp hcon
    exact riemannZeta_ne_zero_of_one_le_re (s := ((β : ℂ) + (γ : ℂ) * Complex.I))
      (by simpa using h1) hzero
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hc_le : c ≤ 1 / 10 ^ 6 := by
    rw [hc]
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 10^6 * Kc) (by norm_num : (0:ℝ) < 10^6)]
    nlinarith [hKcge1]
  have hcV_le_c : c / V ≤ c := by
    rw [div_le_iff₀ hVpos]; nlinarith [hcpos, hVge1]
  by_contra hcon
  have hδltcV : δ < c / V := not_le.mp hcon
  have hδlt1 : δ < 1 := by linarith
  have hδlt32 : δ ≤ 1 / 32 := by linarith
  -- set up geometry
  set σ₀ : ℝ := 1 + 4 * δ with hσ₀
  set Rhi : ℝ := (1 / 2) * (M / L) ^ (2 / 3 : ℝ) with hRhi
  have hσ₀gt1 : 1 < σ₀ := by rw [hσ₀]; linarith
  have hRhi_pos : 0 < Rhi := by
    rw [hRhi]
    have h1 : 0 < M / L := div_pos hMpos hLpos
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos h1 _)
  have hRhi_le : Rhi ≤ 1 / 8 := by
    rw [hRhi]
    have h1 : M / L ≤ 1 / 16 := by
      rw [div_le_iff₀ hLpos]; linarith
    have h2 : (M / L) ^ (2 / 3 : ℝ) ≤ (1 / 16 : ℝ) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (le_of_lt (div_pos hMpos hLpos)) h1 (by norm_num)
    have h3 : ((1 / 16 : ℝ)) ^ (2 / 3 : ℝ) ≤ 1 / 4 := by
      have h4 : ((1 / 16 : ℝ)) ^ (2 / 3 : ℝ) ≤ ((1 / 16 : ℝ)) ^ ((1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
      have h5 : ((1 / 16 : ℝ)) ^ ((1 / 2 : ℝ)) = 1 / 4 := by
        rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1 / 4)]
        norm_num
      linarith
    nlinarith [h2, h3]
  have hRhieq : Rhi * V = M / 2 := by
    have h1 : Real.log (γ₀ + 3) = L := hL.symm
    have h2 : Real.log (Real.log (γ₀ + 3)) = M := by rw [h1, hM]
    rw [hRhi, hV, VKd_def, h1, h2]
    have hh1 : (M / L) ^ (2 / 3 : ℝ) * L ^ (2 / 3 : ℝ) = M ^ (2 / 3 : ℝ) := by
      rw [← Real.mul_rpow (by positivity : (0:ℝ) ≤ M / L) (by linarith : (0:ℝ) ≤ L),
        show M / L * L = M from by field_simp]
    have hh2 : M ^ (2 / 3 : ℝ) * M ^ (1 / 3 : ℝ) = M := by
      rw [← Real.rpow_add (by linarith : (0:ℝ) < M),
        show (2 / 3 : ℝ) + 1 / 3 = 1 by norm_num, Real.rpow_one]
    have key : (1 / 2 : ℝ) * (M / L) ^ (2 / 3 : ℝ) * (L ^ (2 / 3 : ℝ) * M ^ (1 / 3 : ℝ)) = M / 2 := by
      calc (1 / 2 : ℝ) * (M / L) ^ (2 / 3 : ℝ) * (L ^ (2 / 3 : ℝ) * M ^ (1 / 3 : ℝ))
          = (1 / 2) * ((M / L) ^ (2 / 3 : ℝ) * L ^ (2 / 3 : ℝ) * M ^ (1 / 3 : ℝ)) := by ring
        _ = (1 / 2) * (M ^ (2 / 3 : ℝ) * M ^ (1 / 3 : ℝ)) := by rw [hh1]
        _ = (1 / 2) * M := by rw [hh2]
        _ = M / 2 := by ring
    rw [key]
  have hδltRhi : 8 * δ < Rhi := by
    have hRhi_eq : Rhi = M / (2 * V) := by
      field_simp
      linarith [hRhieq]
    rw [hRhi_eq]
    have h1 : 8 * δ < 8 * (c / V) := by linarith
    have h2 : 8 * (c / V) = (16 * c / M) * (M / (2 * V)) := by field_simp; ring
    have h4 : 16 * c / M ≤ 1 := by
      rw [div_le_one hMpos]
      have h6 : (16:ℝ) * c ≤ 1 := by
        rw [hc, mul_one_div, div_le_one (by positivity : (0:ℝ) < 10 ^ 6 * Kc)]
        nlinarith [hKcge1]
      have h8 : (1:ℝ) ≤ M := le_trans hB0ge1 hMge
      nlinarith [h6, h8, hMpos]
    have h5 : (0:ℝ) < M / (2 * V) := by positivity
    calc 8 * δ < 8 * (c / V) := h1
      _ = (16 * c / M) * (M / (2 * V)) := h2
      _ ≤ 1 * (M / (2 * V)) := mul_le_mul_of_nonneg_right h4 h5.le
      _ = M / (2 * V) := by ring
  have hRlo_lt : max (8 * δ) (Rhi / 2) < Rhi := by
    apply max_lt
    · linarith [hδltRhi]
    · linarith [hRhi_pos]
  -- choose R
  set a₁ : ℂ := ((σ₀ : ℝ) : ℂ) + (γ : ℂ) * Complex.I with ha₁
  set a₂ : ℂ := ((σ₀ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I with ha₂
  obtain ⟨R, hRge, hRle, hav1, hav2⟩ := exists_good_sphere_two a₁ a₂
    (x := max (8 * δ) (Rhi / 2)) (y := Rhi) hRlo_lt
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hRge
  have hRhalf : R ≤ 1 / 2 := by linarith [hRle, hRhi_le]
  have hRquarter : 4 * δ + R ≤ 1 / 4 := by linarith [hRle, hRhi_le, hδlt32]
  have hτ1 : 4 ≤ |γ| := by
    have hx : Real.exp (Real.exp (Real.exp B0)) ≤ |γ| := hγ
    have h2 : (4:ℝ) ≤ Real.exp (Real.exp (Real.exp B0)) := by
      linarith [Real.add_one_le_exp B0, Real.add_one_le_exp (Real.exp B0),
        Real.add_one_le_exp (Real.exp (Real.exp B0)), hB0ge1]
    linarith
  have hτ2 : 4 ≤ |2 * γ| := by
    rw [abs_mul, show |(2:ℝ)| = 2 by norm_num]; linarith [hτ1]
  -- zeros have real part < 1
  have hzeros : ∀ u : ℂ, riemannZeta u = 0 → u.re < 1 := by
    intro u hu
    by_contra hc
    exact riemannZeta_ne_zero_of_one_le_re (s := u) (not_lt.mp hc) hu
  -- the zero is inside the disc around a₁
  have hρ_eq : ρ - a₁ = ((-5 * δ : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [ha₁, hσ₀, hδ, hρ] <;> ring
  have hρnorm : ‖ρ - a₁‖ = 5 * δ := by
    rw [hρ_eq, Complex.norm_real, Real.norm_eq_abs,
      show (-5 * δ : ℝ) = -(5 * δ) by ring, abs_neg,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 5 * δ)]
  have hρc : ρ ∈ Metric.closedBall a₁ |R| := by
    rw [Metric.mem_closedBall, dist_eq_norm, abs_of_pos hRpos, hρnorm]
    linarith [le_trans (le_max_left (8 * δ) (Rhi / 2)) hRge]
  -- analyticity on the two discs
  have hne_one₁ : ∀ z ∈ Metric.closedBall a₁ |R|, z ≠ 1 := by
    intro z hz hz1
    rw [hz1] at hz
    have h3 : ‖(1:ℂ) - a₁‖ ≤ R := by
      have := Metric.mem_closedBall.mp hz
      rw [dist_eq_norm] at this
      rwa [abs_of_pos hRpos] at this
    have him : ((1:ℂ) - a₁).im = -γ := by simp [ha₁]
    have h4 : |γ| ≤ R := by
      calc |γ| = |((1:ℂ) - a₁).im| := by rw [him, abs_neg]
        _ ≤ ‖(1:ℂ) - a₁‖ := Complex.abs_im_le_norm _
        _ ≤ R := h3
    linarith [h4, hτ1, hRhalf]
  have hne_one₂ : ∀ z ∈ Metric.closedBall a₂ |R|, z ≠ 1 := by
    intro z hz hz1
    rw [hz1] at hz
    have h3 : ‖(1:ℂ) - a₂‖ ≤ R := by
      have := Metric.mem_closedBall.mp hz
      rw [dist_eq_norm] at this
      rwa [abs_of_pos hRpos] at this
    have him : ((1:ℂ) - a₂).im = -(2 * γ) := by simp [ha₂]
    have h4 : |2 * γ| ≤ R := by
      calc |2 * γ| = |((1:ℂ) - a₂).im| := by rw [him, abs_neg]
        _ ≤ ‖(1:ℂ) - a₂‖ := Complex.abs_im_le_norm _
        _ ≤ R := h3
    linarith [h4, hτ2, hRhalf]
  have hf1 : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall a₁ |R|) :=
    analyticOn_riemannZeta.mono (fun z hz => by simpa using hne_one₁ z hz)
  have hf2 : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall a₂ |R|) :=
    analyticOn_riemannZeta.mono (fun z hz => by simpa using hne_one₂ z hz)
  have ha₁re : a₁.re = σ₀ := by simp [ha₁]
  have ha₂re : a₂.re = σ₀ := by simp [ha₂]
  have hfa1 : riemannZeta a₁ ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (s := a₁) (by rw [ha₁re]; linarith)
  have hfa2 : riemannZeta a₂ ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (s := a₂) (by rw [ha₂re]; linarith)
  have hleft1 : ∀ u : ℂ, riemannZeta u = 0 → u ∈ Metric.closedBall a₁ |R| → u.re < a₁.re := by
    intro u hu _
    have := hzeros u hu
    rw [ha₁re]; linarith
  have hleft2 : ∀ u : ℂ, riemannZeta u = 0 → u ∈ Metric.closedBall a₂ |R| → u.re < a₂.re := by
    intro u hu _
    have := hzeros u hu
    rw [ha₂re]; linarith
  have hsphere1 : ∀ u : ℂ, ‖u - a₁‖ = R → riemannZeta u ≠ 0 := fun u hu h0 => hav1 u h0 hu
  have hsphere2 : ∀ u : ℂ, ‖u - a₂‖ = R → riemannZeta u ≠ 0 := fun u hu h0 => hav2 u h0 hu
  have hS1 : ∀ u ∈ ({ρ} : Finset ℂ), riemannZeta u = 0 ∧ u ∈ Metric.closedBall a₁ |R| := by
    intro u hu
    rw [Finset.mem_singleton] at hu
    rw [hu]; exact ⟨hzero, hρc⟩
  -- circle-avoidance in the form required by the arc bound
  have havoid₁ : ∀ θ : ℝ, riemannZeta (((1 + 4 * δ : ℝ) : ℂ) + (γ : ℂ) * Complex.I +
      (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) ≠ 0 := by
    intro θ h0
    have he : (((1 + 4 * δ : ℝ) : ℂ) + (γ : ℂ) * Complex.I +
        (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - a₁ =
        (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
      rw [ha₁, hσ₀]; ring
    have h1 : ‖(((1 + 4 * δ : ℝ) : ℂ) + (γ : ℂ) * Complex.I +
        (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - a₁‖ = R := by
      rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos, Complex.norm_exp,
        Complex.mul_re, Complex.I_re, Complex.I_im]
      norm_num
    exact hav1 _ h0 h1
  have havoid₂ : ∀ θ : ℝ, riemannZeta (((1 + 4 * δ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I +
      (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) ≠ 0 := by
    intro θ h0
    have he : (((1 + 4 * δ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I +
        (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - a₂ =
        (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
      rw [ha₂, hσ₀]; ring
    have h1 : ‖(((1 + 4 * δ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I +
        (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - a₂‖ = R := by
      rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos, Complex.norm_exp,
        Complex.mul_re, Complex.I_re, Complex.I_im]
      norm_num
    exact hav2 _ h0 h1
  -- the two circle-integral bounds
  have harc1 := zeta_arc_bound (A := A) (B := B) (C := clog) (c := clamp) (δ := δ)
    (τ := γ) (R := R) hA hB hclog hclamp hδpos hRpos hRhalf hRquarter hτ1 hgr hlog hlow havoid₁
  have harc2 := zeta_arc_bound (A := A) (B := B) (C := clog) (c := clamp) (δ := δ)
    (τ := 2 * γ) (R := R) hA hB hclog hclamp hδpos hRpos hRhalf hRquarter hτ2 hgr hlog hlow havoid₂
  -- the two discriminant bounds
  set P1 : ℝ := Real.log A + B * R ^ (3 / 2 : ℝ) * Real.log (|γ| + R + 3) +
      (2 / 3 : ℝ) * Real.log (Real.log (|γ| + R + 3)) with hP1
  set Q1 : ℝ := Real.log clog + Real.log (Real.log (|γ| + R + 3)) with hQ1
  set P2 : ℝ := Real.log A + B * R ^ (3 / 2 : ℝ) * Real.log (|2 * γ| + R + 3) +
      (2 / 3 : ℝ) * Real.log (Real.log (|2 * γ| + R + 3)) with hP2
  set Q2 : ℝ := Real.log clog + Real.log (Real.log (|2 * γ| + R + 3)) with hQ2
  set Λ : ℝ := Real.log (1 / (4 * clamp * δ)) with hΛ
  set K1 : ℝ := 2 * Real.pi * (max 0 Λ + max 0 P1 + max 0 Q1) with hK1
  set K2 : ℝ := 2 * Real.pi * (max 0 Λ + max 0 P2 + max 0 Q2) with hK2
  have hdb1 : -(deriv riemannZeta a₁ / riemannZeta a₁).re ≤
      (∑ u ∈ ({ρ} : Finset ℂ), ((MeromorphicOn.divisor riemannZeta (Metric.closedBall a₁ |R|)) u : ℝ) *
        (u - a₁).re * ((‖u - a₁‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹)) + K1 / (Real.pi * R) :=
    jensenCarleman_subset hRpos hf1 hfa1 hsphere1 hleft1 _ hS1
      (by simpa only [hK1, hΛ, hP1, hQ1, ha₁, hσ₀] using harc1)
  have hdb2 : -(deriv riemannZeta a₂ / riemannZeta a₂).re ≤
      (∑ u ∈ (∅ : Finset ℂ), ((MeromorphicOn.divisor riemannZeta (Metric.closedBall a₂ |R|)) u : ℝ) *
        (u - a₂).re * ((‖u - a₂‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹)) + K2 / (Real.pi * R) :=
    jensenCarleman_subset hRpos hf2 hfa2 hsphere2 hleft2 _ (by intro u hu; simp at hu)
      (by simpa only [hK2, hΛ, hP2, hQ2, ha₂, hσ₀] using harc2)
  set z : ℝ := 1 / δ with hzdef
  set aa : ℝ := V / c with hadef
  -- ==================== elementary bounds ====================
  have hth : A ≤ B0 ∧ clog ≤ B0 ∧ Cz ≤ B0 ∧ Kc ≤ B0 ∧ 1 / clamp ≤ B0 ∧
      (1:ℝ) ≤ B0 ∧ (10:ℝ) ^ 6 ≤ B0 := by
    rw [hB0]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hA, hB, hCz, hclamp, hclog, hKcge1, hclamp_inv_pos]
  have hthA : A ≤ B0 := hth.1
  have hthc : clog ≤ B0 := hth.2.1
  have hthCz : Cz ≤ B0 := hth.2.2.1
  have hthKc : Kc ≤ B0 := hth.2.2.2.1
  have hthci : 1 / clamp ≤ B0 := hth.2.2.2.2.1
  have hth1 : (1:ℝ) ≤ B0 := hth.2.2.2.2.2.1
  have hth6 : (10:ℝ) ^ 6 ≤ B0 := hth.2.2.2.2.2.2
  have hM1 : (1:ℝ) ≤ M := le_trans hth1 hMge
  have hM2 : (2:ℝ) ≤ M :=
    le_trans (by norm_num : (2:ℝ) ≤ (10:ℝ) ^ 6) (le_trans hth6 hMge)
  have hlogA : Real.log A ≤ M := by
    have h1 : Real.log A ≤ A := Real.log_le_self hA.le
    linarith only [h1, hthA, hMge]
  have hlogc : Real.log clog ≤ M := by
    have h1 : Real.log clog ≤ clog := Real.log_le_self hclog.le
    linarith only [h1, hthc, hMge]
  have hKcM : Kc ≤ M := le_trans hthKc hMge
  have hlogKc : Real.log Kc ≤ M := by
    have h1 : Real.log Kc ≤ Kc := Real.log_le_self hKcpos.le
    linarith only [h1, hKcM]
  have hlog6 : Real.log (1000000:ℝ) ≤ M := by
    have h2 : Real.log (1000000:ℝ) ≤ 1000000 := Real.log_le_self (by norm_num)
    have h3 : (1000000:ℝ) ≤ M :=
      le_trans (by norm_num : (1000000:ℝ) ≤ (10:ℝ)^6) (le_trans hth6 hMge)
    linarith only [h2, h3]
  have hlogM : Real.log M ≤ M := Real.log_le_self hMpos.le
  have hlogV : Real.log V ≤ M := by
    have hVval : V = L ^ (2 / 3 : ℝ) * M ^ (1 / 3 : ℝ) := by
      rw [hV, VKd_def, ← hL, ← hM]
    have hlogM' : Real.log (Real.log L) ≤ Real.log L := by simpa only [hM] using hlogM
    rw [hVval, Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hLpos (2 / 3 : ℝ), Real.log_rpow hMpos (1 / 3 : ℝ), hM]
    linarith only [hlogM']
  have hclampinv : Real.log (1 / (4 * clamp)) ≤ M := by
    have h1 : (0:ℝ) < 1 / (4 * clamp) := by positivity
    have h2 : Real.log (1 / (4 * clamp)) ≤ 1 / (4 * clamp) := Real.log_le_self h1.le
    have h3 : 1 / (4 * clamp) ≤ 1 / clamp := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 4 * clamp) (by positivity : (0:ℝ) < clamp)]
      nlinarith only [hclamp]
    linarith only [h2, h3, hthci, hMge]
  -- `M` is small compared with `L^{2/3}`
  have hMle23 : M ≤ L ^ (2 / 3 : ℝ) / 32 := by
    have h1 : M ≤ 2 * Real.sqrt L := by
      have hh := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hLpos)
      rw [Real.log_sqrt hLpos.le] at hh
      linarith only [hh, hM]
    have hsq : Real.sqrt L = L ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow L
    have h2 : L ^ (2 / 3 : ℝ) = L ^ (1 / 2 : ℝ) * L ^ (1 / 6 : ℝ) := by
      rw [← Real.rpow_add (by linarith : (0:ℝ) < L)]
      norm_num
    have h6 : (64:ℝ) ≤ L ^ (1 / 6 : ℝ) := by
      have h7 : ((10:ℝ) ^ 12) ^ (1 / 6 : ℝ) ≤ L ^ (1 / 6 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hLge (by norm_num)
      have h8 : ((10:ℝ) ^ 12) ^ (1 / 6 : ℝ) = 100 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      linarith only [h7, h8.le]
    have h9 : (0:ℝ) ≤ L ^ (1 / 2 : ℝ) := Real.rpow_nonneg hLpos.le _
    have h10 : L ^ (1 / 2 : ℝ) * 64 ≤ L ^ (1 / 2 : ℝ) * L ^ (1 / 6 : ℝ) :=
      mul_le_mul_of_nonneg_left h6 h9
    rw [h2]
    nlinarith only [h1, hsq, h10]
  have hCzV : 3 * Cz ≤ V / 10 := by
    have hVge : L ^ (2 / 3 : ℝ) ≤ V := by
      rw [hV, VKd_def, ← hL, ← hM]
      exact le_mul_of_one_le_right (by positivity)
        (Real.one_le_rpow (by linarith only [hM1]) (by norm_num))
    have hVge32 : L ^ (2 / 3 : ℝ) / 32 ≤ V / 32 :=
      div_le_div_of_nonneg_right hVge (by norm_num)
    have h1 : Cz ≤ V / 32 :=
      le_trans (le_trans hthCz hMge) (le_trans hMle23 hVge32)
    have h2 : 3 * Cz ≤ 3 * (V / 32) := mul_le_mul_of_nonneg_left h1 (by norm_num)
    have h3 : 3 * (V / 32) ≤ V / 10 := by
      have e1 : (3:ℝ) * (V / 32) = V * (3 / 32) := by ring
      have e2 : V / 10 = V * (1 / 10) := by ring
      rw [e1, e2]
      nlinarith only [hVpos]
    linarith only [h2, h3]
  -- powers of `R`
  have hRrpow : R ^ (3 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ (3 / 2 : ℝ) * (M / L) := by
    have h1 : R ^ (3 / 2 : ℝ) ≤ Rhi ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow hRpos.le hRle (by norm_num)
    have hML : (0:ℝ) ≤ M / L := div_nonneg hMpos.le hLpos.le
    have h2 : Rhi ^ (3 / 2 : ℝ) = (1 / 2 : ℝ) ^ (3 / 2 : ℝ) * (M / L) := by
      rw [hRhi, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hML (2 / 3 : ℝ))]
      rw [← Real.rpow_mul hML, show (2 / 3 : ℝ) * (3 / 2 : ℝ) = 1 by norm_num,
        Real.rpow_one]
    linarith only [h1, h2.le, h2.ge]
  have hhalf : (1 / 2 : ℝ) ^ (3 / 2 : ℝ) ≤ 1 / 2 := by
    have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0:ℝ) < 1/2)
      (by norm_num : (1/2:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 3/2)
    simpa using h
  have hlogt : Real.log (|γ| + R + 3) ≤ 2 * L := by
    have h2 : |γ| + R + 3 ≤ 2 * (γ₀ + 3) := by
      rw [hγ₀]
      linarith only [hRle, hRhi_le, hτ1]
    calc Real.log (|γ| + R + 3) ≤ Real.log (2 * (γ₀ + 3)) :=
          Real.log_le_log (by linarith only [hτ1, hRpos]) h2
      _ = Real.log 2 + L := by rw [Real.log_mul (by norm_num) (by positivity), hL]
      _ ≤ 2 * L := by linarith only [Real.log_le_self (by norm_num : (0:ℝ) ≤ 2), hLge]
  have hlogt2 : Real.log (|2 * γ| + R + 3) ≤ 2 * L := by
    have h2 : |2 * γ| + R + 3 ≤ 2 * (γ₀ + 3) := by
      rw [hγ₀, abs_mul, show |(2:ℝ)| = 2 by norm_num]
      linarith only [hRle, hRhi_le, hτ1]
    calc Real.log (|2 * γ| + R + 3) ≤ Real.log (2 * (γ₀ + 3)) :=
          Real.log_le_log (by linarith only [hτ2, hRpos]) h2
      _ = Real.log 2 + L := by rw [Real.log_mul (by norm_num) (by positivity), hL]
      _ ≤ 2 * L := by linarith only [Real.log_le_self (by norm_num : (0:ℝ) ≤ 2), hLge]
  have hllog : Real.log (Real.log (|γ| + R + 3)) ≤ 2 * M := by
    calc Real.log (Real.log (|γ| + R + 3)) ≤ Real.log (2 * L) :=
          Real.log_le_log (Real.log_pos (by linarith only [hτ1, hRpos])) hlogt
      _ = Real.log 2 + M := by rw [Real.log_mul (by norm_num) (by positivity), hM]
      _ ≤ 2 * M := by linarith only [Real.log_le_self (by norm_num : (0:ℝ) ≤ 2), hM2]
  have hllog2 : Real.log (Real.log (|2 * γ| + R + 3)) ≤ 2 * M := by
    calc Real.log (Real.log (|2 * γ| + R + 3)) ≤ Real.log (2 * L) :=
          Real.log_le_log (Real.log_pos (by linarith only [hτ2, hRpos])) hlogt2
      _ = Real.log 2 + M := by rw [Real.log_mul (by norm_num) (by positivity), hM]
      _ ≤ 2 * M := by linarith only [Real.log_le_self (by norm_num : (0:ℝ) ≤ 2), hM2]
  have hRlog : R ^ (3 / 2 : ℝ) * Real.log (|γ| + R + 3) ≤ M := by
    have hLR : (0:ℝ) ≤ Real.log (|γ| + R + 3) := Real.log_nonneg (by linarith only [hτ1, hRpos])
    have hb : (0:ℝ) ≤ (1 / 2 : ℝ) ^ (3 / 2 : ℝ) * (M / L) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (div_nonneg hMpos.le hLpos.le)
    have hstep : R ^ (3 / 2 : ℝ) * Real.log (|γ| + R + 3) ≤
        ((1 / 2 : ℝ) ^ (3 / 2 : ℝ) * (M / L)) * (2 * L) := mul_le_mul hRrpow hlogt hLR hb
    have hkey : ((1 / 2 : ℝ) ^ (3 / 2 : ℝ) * (M / L)) * (2 * L) =
        (2 * (1 / 2 : ℝ) ^ (3 / 2 : ℝ)) * M := by field_simp <;> ring
    rw [hkey] at hstep
    nlinarith only [hstep, hhalf, hMpos]
  have hRlog2 : R ^ (3 / 2 : ℝ) * Real.log (|2 * γ| + R + 3) ≤ M := by
    have hLR : (0:ℝ) ≤ Real.log (|2 * γ| + R + 3) := Real.log_nonneg (by linarith only [hτ2, hRpos])
    have hb : (0:ℝ) ≤ (1 / 2 : ℝ) ^ (3 / 2 : ℝ) * (M / L) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (div_nonneg hMpos.le hLpos.le)
    have hstep : R ^ (3 / 2 : ℝ) * Real.log (|2 * γ| + R + 3) ≤
        ((1 / 2 : ℝ) ^ (3 / 2 : ℝ) * (M / L)) * (2 * L) := mul_le_mul hRrpow hlogt2 hLR hb
    have hkey : ((1 / 2 : ℝ) ^ (3 / 2 : ℝ) * (M / L)) * (2 * L) =
        (2 * (1 / 2 : ℝ) ^ (3 / 2 : ℝ)) * M := by field_simp <;> ring
    rw [hkey] at hstep
    nlinarith only [hstep, hhalf, hMpos]
  -- bounds on the log-derivative error terms
  have hP1b : P1 ≤ (6 + B) * M := by
    rw [hP1]
    have hb0 : B * (R ^ (3 / 2 : ℝ) * Real.log (|γ| + R + 3)) ≤ B * M :=
      mul_le_mul_of_nonneg_left hRlog hB.le
    have hbe : B * (R ^ (3 / 2 : ℝ) * Real.log (|γ| + R + 3)) =
        B * R ^ (3 / 2 : ℝ) * Real.log (|γ| + R + 3) := by ring
    have hb : B * R ^ (3 / 2 : ℝ) * Real.log (|γ| + R + 3) ≤ B * M := by
      linarith only [hb0, hbe.le, hbe.ge]
    have hl : (2 / 3 : ℝ) * Real.log (Real.log (|γ| + R + 3)) ≤ (4 / 3) * M := by
      have h := mul_le_mul_of_nonneg_left hllog (by norm_num : (0:ℝ) ≤ 2 / 3)
      have e : (2 / 3 : ℝ) * (2 * M) = (4 / 3) * M := by ring
      linarith only [h, e.le, e.ge]
    have hsum : Real.log A + B * R ^ (3 / 2 : ℝ) * Real.log (|γ| + R + 3) +
        (2 / 3 : ℝ) * Real.log (Real.log (|γ| + R + 3)) ≤ M + B * M + (4 / 3) * M :=
      by linarith only [hlogA, hb, hl]
    have hdist : M + B * M + (4 / 3) * M ≤ (6 + B) * M := by nlinarith only [hMpos]
    linarith only [hsum, hdist]
  have hQ1b : Q1 ≤ 3 * M := by
    rw [hQ1]
    linarith only [hlogc, hllog]
  have hP2b : P2 ≤ (6 + B) * M := by
    rw [hP2]
    have hb0 : B * (R ^ (3 / 2 : ℝ) * Real.log (|2 * γ| + R + 3)) ≤ B * M :=
      mul_le_mul_of_nonneg_left hRlog2 hB.le
    have hbe : B * (R ^ (3 / 2 : ℝ) * Real.log (|2 * γ| + R + 3)) =
        B * R ^ (3 / 2 : ℝ) * Real.log (|2 * γ| + R + 3) := by ring
    have hb : B * R ^ (3 / 2 : ℝ) * Real.log (|2 * γ| + R + 3) ≤ B * M := by
      linarith only [hb0, hbe.le, hbe.ge]
    have hl : (2 / 3 : ℝ) * Real.log (Real.log (|2 * γ| + R + 3)) ≤ (4 / 3) * M := by
      have h := mul_le_mul_of_nonneg_left hllog2 (by norm_num : (0:ℝ) ≤ 2 / 3)
      have e : (2 / 3 : ℝ) * (2 * M) = (4 / 3) * M := by ring
      linarith only [h, e.le, e.ge]
    have hsum : Real.log A + B * R ^ (3 / 2 : ℝ) * Real.log (|2 * γ| + R + 3) +
        (2 / 3 : ℝ) * Real.log (Real.log (|2 * γ| + R + 3)) ≤ M + B * M + (4 / 3) * M :=
      by linarith only [hlogA, hb, hl]
    have hdist : M + B * M + (4 / 3) * M ≤ (6 + B) * M := by nlinarith only [hMpos]
    linarith only [hsum, hdist]
  have hQ2b : Q2 ≤ 3 * M := by
    rw [hQ2]
    linarith only [hlogc, hllog2]
  have hΛb : Λ ≤ Real.log z + M := by
    rw [hΛ, hzdef]
    have h1 : (1:ℝ) / (4 * clamp * δ) = (1 / δ) * (1 / (4 * clamp)) := by ring
    rw [h1, Real.log_mul (by positivity) (by positivity)]
    linarith only [hclampinv]
  have hRinv : 1 / R ≤ 4 * (V / M) := by
    have hRhi_eq : Rhi = M / (2 * V) := by
      rw [eq_div_iff (by positivity : (2:ℝ) * V ≠ 0)]
      nlinarith only [hRhieq]
    have h1 : Rhi / 2 ≤ R := le_trans (le_max_right (8 * δ) (Rhi / 2)) hRge
    have h2 : M ≤ 4 * V * R := by
      have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 4 * V)
      have h4 : 4 * V * (Rhi / 2) = M := by rw [hRhi_eq]; field_simp <;> ring
      linarith only [h3, h4.le, h4.ge]
    rw [show (4:ℝ) * (V / M) = 4 * V / M from by ring, le_div_iff₀ hMpos]
    rw [show (1:ℝ) / R * M = M / R from by ring, div_le_iff₀ hRpos]
    exact h2
  have hz3 : (3:ℝ) ≤ z := by rw [hzdef, le_div_iff₀ hδpos]; linarith only [hδlt32]
  have hLz : (0:ℝ) ≤ Real.log z := by
    have h1 : (1:ℝ) ≤ Real.log z := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (by linarith only [Real.exp_one_lt_three, hz3])
    linarith only [h1]
  have hK1b : K1 / (Real.pi * R) ≤ 8 * (V * Real.log z / M) + 8 * ((10 + B) * V) := by
    have h1 : max 0 Λ + max 0 P1 + max 0 Q1 ≤ Real.log z + (10 + B) * M := by
      have h2 : max 0 Λ ≤ Real.log z + M := max_le (by linarith only [hLz, hMpos]) hΛb
      have h3 : max 0 P1 ≤ (6 + B) * M := max_le (by nlinarith only [hB, hMpos]) hP1b
      have h4 : max 0 Q1 ≤ 3 * M := max_le (by linarith only [hMpos]) hQ1b
      linarith only [h2, h3, h4]
    have h2 : (0:ℝ) ≤ Real.log z + (10 + B) * M := by nlinarith only [hLz, hMpos, hB]
    have h3 : K1 / (Real.pi * R) = 2 * (max 0 Λ + max 0 P1 + max 0 Q1) / R := by
      rw [hK1]; field_simp <;> ring
    rw [h3]
    have h4 : 2 * (max 0 Λ + max 0 P1 + max 0 Q1) / R
        ≤ 2 * (Real.log z + (10 + B) * M) * (4 * (V / M)) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul (by linarith only [h1]) hRinv (by positivity) (by linarith only [h2])
    have h5 : 2 * (Real.log z + (10 + B) * M) * (4 * (V / M)) =
        8 * (V * Real.log z / M) + 8 * ((10 + B) * V) := by field_simp <;> ring
    linarith only [h4, h5.le, h5.ge]
  have hK2b : K2 / (Real.pi * R) ≤ 8 * (V * Real.log z / M) + 8 * ((10 + B) * V) := by
    have h1 : max 0 Λ + max 0 P2 + max 0 Q2 ≤ Real.log z + (10 + B) * M := by
      have h2 : max 0 Λ ≤ Real.log z + M := max_le (by linarith only [hLz, hMpos]) hΛb
      have h3 : max 0 P2 ≤ (6 + B) * M := max_le (by nlinarith only [hB, hMpos]) hP2b
      have h4 : max 0 Q2 ≤ 3 * M := max_le (by linarith only [hMpos]) hQ2b
      linarith only [h2, h3, h4]
    have h2 : (0:ℝ) ≤ Real.log z + (10 + B) * M := by nlinarith only [hLz, hMpos, hB]
    have h3 : K2 / (Real.pi * R) = 2 * (max 0 Λ + max 0 P2 + max 0 Q2) / R := by
      rw [hK2]; field_simp <;> ring
    rw [h3]
    have h4 : 2 * (max 0 Λ + max 0 P2 + max 0 Q2) / R
        ≤ 2 * (Real.log z + (10 + B) * M) * (4 * (V / M)) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul (by linarith only [h1]) hRinv (by positivity) (by linarith only [h2])
    have h5 : 2 * (Real.log z + (10 + B) * M) * (4 * (V / M)) =
        8 * (V * Real.log z / M) + 8 * ((10 + B) * V) := by field_simp <;> ring
    linarith only [h4, h5.le, h5.ge]
  -- ==================== the single-zero divisor sum ====================
  have h5d : 0 < 5 * δ := by linarith only [hδpos]
  have h8d : 8 * δ ≤ R := le_trans (le_max_left (8 * δ) (Rhi / 2)) hRge
  have h5lt : 5 * δ < R := by linarith only [h8d, hδpos]
  have hρball : ρ ∈ Metric.ball a₁ R := by
    rw [Metric.mem_ball, dist_eq_norm, hρnorm]
    exact h5lt
  have hD1 : (1:ℝ) ≤ ((MeromorphicOn.divisor riemannZeta (Metric.closedBall a₁ |R|)) ρ : ℝ) :=
    divisor_one_le_at_zero hRpos hne_one₁ hfa1 hρball hzero
  have hsum1 : (∑ u ∈ ({ρ} : Finset ℂ),
        ((MeromorphicOn.divisor riemannZeta (Metric.closedBall a₁ |R|)) u : ℝ) *
          (u - a₁).re * ((‖u - a₁‖ ^ 2)⁻¹ - R⁻¹ * R⁻¹))
      ≤ -(1 / (5 * δ)) + 5 * δ / R ^ 2 := by
    rw [Finset.sum_singleton]
    have hbr : 0 < ((5 * δ) ^ 2)⁻¹ - R⁻¹ * R⁻¹ := by
      have h1 : (5 * δ) ^ 2 < R ^ 2 := by nlinarith only [h5d, h5lt]
      have h2 : (0:ℝ) < (5 * δ) ^ 2 := by positivity
      have h3 : (0:ℝ) < R ^ 2 := by positivity
      have h4 : R⁻¹ * R⁻¹ = (R ^ 2)⁻¹ := by rw [← mul_inv, pow_two]
      have h5 : (R ^ 2)⁻¹ < ((5 * δ) ^ 2)⁻¹ := (inv_lt_inv₀ h3 h2).mpr h1
      linarith only [h4.le, h4.ge, h5]
    have hre : (ρ - a₁).re = -(5 * δ) := by rw [hρ_eq, Complex.ofReal_re]; ring
    rw [hre, hρnorm]
    have hstep : ((MeromorphicOn.divisor riemannZeta (Metric.closedBall a₁ |R|)) ρ : ℝ) *
          (-(5 * δ)) * (((5 * δ) ^ 2)⁻¹ - R⁻¹ * R⁻¹)
        ≤ 1 * (-(5 * δ)) * (((5 * δ) ^ 2)⁻¹ - R⁻¹ * R⁻¹) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonpos_right hD1 (by linarith only [hδpos] : -(5 * δ) ≤ 0)) hbr.le
    have hkey : 1 * (-(5 * δ)) * (((5 * δ) ^ 2)⁻¹ - R⁻¹ * R⁻¹) =
        -(1 / (5 * δ)) + 5 * δ / R ^ 2 := by field_simp <;> ring
    linarith only [hstep, hkey.le, hkey.ge]
  have hA1 : -(deriv riemannZeta a₁ / riemannZeta a₁).re ≤
      -(1 / (5 * δ)) + 5 * δ / R ^ 2 + K1 / (Real.pi * R) := by
    linarith only [hdb1, hsum1]
  have hA2 : -(deriv riemannZeta a₂ / riemannZeta a₂).re ≤ K2 / (Real.pi * R) := by
    simpa using hdb2
  -- ==================== 3-4-1 and the pole bound ====================
  have h341' : 0 ≤ 3 * (-deriv riemannZeta (((σ₀ : ℝ) : ℂ)) /
          riemannZeta (((σ₀ : ℝ) : ℂ))).re
      + 4 * (-deriv riemannZeta a₁ / riemannZeta a₁).re
      + (-deriv riemannZeta a₂ / riemannZeta a₂).re := by
    have h := zeta_logDeriv_three_four_one σ₀ γ hσ₀gt1
    have e1 : (((σ₀ : ℝ) : ℂ) + (γ : ℂ) * Complex.I) = a₁ := by rw [ha₁]
    have e2 : (((σ₀ : ℝ) : ℂ) + (2 * γ : ℂ) * Complex.I) = a₂ := by
      rw [ha₂]; congr 1; push_cast; ring
    rw [e1, e2] at h
    exact h
  have hA0' : (-deriv riemannZeta (((σ₀ : ℝ) : ℂ)) /
      riemannZeta (((σ₀ : ℝ) : ℂ))).re ≤ 1 / (4 * δ) + Cz := by
    have h := haxis σ₀ hσ₀gt1 (by rw [hσ₀]; linarith only [hδlt32])
    have h1 : σ₀ - 1 = 4 * δ := by rw [hσ₀]; ring
    rw [h1] at h
    exact h
  have hA1' : (-deriv riemannZeta a₁ / riemannZeta a₁).re ≤
      -(1 / (5 * δ)) + 5 * δ / R ^ 2 + K1 / (Real.pi * R) := by
    have he : (-deriv riemannZeta a₁ / riemannZeta a₁).re =
        -(deriv riemannZeta a₁ / riemannZeta a₁).re := by rw [neg_div, Complex.neg_re]
    rw [he]; exact hA1
  have hA2' : (-deriv riemannZeta a₂ / riemannZeta a₂).re ≤ K2 / (Real.pi * R) := by
    have he : (-deriv riemannZeta a₂ / riemannZeta a₂).re =
        -(deriv riemannZeta a₂ / riemannZeta a₂).re := by rw [neg_div, Complex.neg_re]
    rw [he]; exact hA2
  have hcomb0 : 1 / (20 * δ) ≤ 3 * Cz + 20 * δ / R ^ 2 + (4 * K1 + K2) / (Real.pi * R) := by
    have he : (1:ℝ) / (20 * δ) = 4 * (1 / (5 * δ)) - 3 * (1 / (4 * δ)) := by
      field_simp <;> ring
    have hd : (20:ℝ) * δ / R ^ 2 = 4 * (5 * δ / R ^ 2) := by ring
    have h1 : (4 * K1 + K2) / (Real.pi * R) =
        4 * (K1 / (Real.pi * R)) + K2 / (Real.pi * R) := by ring
    rw [he, hd, h1]
    linarith only [h341', hA0', hA1', hA2']
  -- ==================== assembly ====================
  have hzpos : 0 < z := by rw [hzdef]; positivity
  have haapos : 0 < aa := by rw [hadef]; positivity
  have hmain2 : z ≤ (800 * (V / M)) * Real.log z +
      (800 * ((10 + B) * V) + 320 * (V / M) + 2 * V) :=
    vk_z_bound hMpos hRpos hδpos h8d hzdef hcomb0 hCzV hRinv hK1b hK2b
  have hzge : aa ≤ z := by
    have h1 : δ * V < c := by rw [lt_div_iff₀ hVpos] at hδltcV; exact hδltcV
    rw [hadef, hzdef, div_le_iff₀ hcpos, show (1:ℝ) / δ * c = c / δ from by ring,
      le_div_iff₀ hδpos]
    linarith only [h1]
  have hKb_le : 800 * (V / M) ≤ aa := by
    have h1 : 800 * c ≤ M := by
      have h2 : 800 * c ≤ 800 * (1 / 10 ^ 6) :=
        mul_le_mul_of_nonneg_left hc_le (by norm_num)
      linarith only [h2, hM1]
    rw [hadef]
    rw [show (800:ℝ) * (V / M) = 800 * V / M from by ring, div_le_iff₀ hMpos]
    rw [show (V / c) * M = V * M / c from by ring, le_div_iff₀ hcpos]
    nlinarith only [h1, hVpos]
  have hKbnb : (0:ℝ) ≤ 800 * (V / M) := by positivity
  have haa_eq : aa = V * 1000000 * Kc := by
    rw [hadef, hc]; field_simp <;> ring
  have hlogaa : Real.log aa ≤ 3 * M := by
    rw [haa_eq, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
    linarith only [hlogV, hlog6, hlogKc]
  have hKcB : 1 + B ≤ Kc := by
    rw [hKc]
    have h1 : (1:ℝ) ≤ 1 + A := by linarith only [hA]
    have h2 : (1:ℝ) ≤ 1 + Cz := by linarith only [hCz]
    have h3 : (1:ℝ) ≤ 1 + clamp := by linarith only [hclamp]
    have h4 : (1:ℝ) ≤ 1 + clog := by linarith only [hclog]
    calc (1 + B : ℝ) ≤ (1 + A) * (1 + B) := le_mul_of_one_le_left (by linarith only [hB]) h1
      _ ≤ (1 + A) * (1 + B) * (1 + Cz) := le_mul_of_one_le_right (by positivity) h2
      _ ≤ (1 + A) * (1 + B) * (1 + Cz) * (1 + clamp) :=
          le_mul_of_one_le_right (by positivity) h3
      _ ≤ (1 + A) * (1 + B) * (1 + Cz) * (1 + clamp) * (1 + clog) :=
          le_mul_of_one_le_right (by positivity) h4
  have hfa : 0 < aa - (800 * (V / M)) * Real.log aa -
      (800 * ((10 + B) * V) + 320 * (V / M) + 2 * V) :=
    vk_hfa hVpos hM1 hKcB hB.le haa_eq hlogaa
  exact vk_close_arith haapos hzpos hmain2 hzge hKb_le hKbnb hfa

theorem zeta_VK_zeroFree_of_growth
    (hgr : ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      (∀ σ t : ℝ, 1 / 2 ≤ σ → σ < 1 → 3 ≤ |t| →
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          A * (|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) *
            (Real.log (|t| + 3)) ^ (2 / 3 : ℝ))) :
    ∃ c : ℝ, 0 < c ∧
      (∀ σ t : ℝ, 3 ≤ |t| →
        1 - c / ((Real.log (|t| + 3)) ^ (2 / 3 : ℝ) *
            (Real.log (Real.log (|t| + 3))) ^ (1 / 3 : ℝ)) ≤ σ →
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) := by
  obtain ⟨A, B, hA, hB, hgr'⟩ := hgr
  obtain ⟨Cz, hCzpos, hCz⟩ := Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound
  obtain ⟨clamp, hclamp, hlow⟩ := Commons.NumberTheory.Zeta.zeta_lower_bound_right_of_one
  obtain ⟨clog, hclog, hlog⟩ := zeta_log_bound_right
  have hlow' : ∀ h t : ℝ, 0 < h → h ≤ 1 / 4 →
      clamp * h ≤ ‖riemannZeta (((1 + h : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
    intro h t h1 h2
    rw [mul_comm (t : ℂ) Complex.I]
    exact hlow h t h1 h2
  obtain ⟨T₀, cL, hT₀, hcL, hlarge⟩ := vk_large hA hB hCzpos hclamp hclog hgr' hCz hlow' hlog
  obtain ⟨ε, hε, hstrip⟩ := zeta_zeroFree_bounded_height (max T₀ 4) (le_max_right _ _)
  have hV6pos : 0 < VKd (6:ℝ) := VKd_pos (by norm_num)
  refine ⟨min (cL / 2) (ε * VKd 6), lt_min (by linarith) (mul_pos hε hV6pos), ?_⟩
  intro σ t ht hσ hzero
  by_cases hσ1 : 1 ≤ σ
  · exact riemannZeta_ne_zero_of_one_le_re (s := ((σ : ℂ) + (t : ℂ) * Complex.I))
      (by simpa using hσ1) hzero
  · push_neg at hσ1
    have hσV : 1 - min (cL / 2) (ε * VKd 6) / VKd (|t| + 3) ≤ σ := by
      simpa only [VKd_def] using hσ
    have hVpos : 0 < VKd (|t| + 3) := VKd_pos (by linarith)
    by_cases htT : T₀ ≤ |t|
    · have hmin : min (cL / 2) (ε * VKd 6) ≤ cL / 2 := min_le_left _ _
      have h1 : (min (cL / 2) (ε * VKd 6)) / VKd (|t| + 3) ≤ (cL / 2) / VKd (|t| + 3) :=
        div_le_div_of_nonneg_right hmin hVpos.le
      have h2 := hlarge σ t htT hzero
      have h3 : 1 - (cL / 2) / VKd (|t| + 3) ≤ σ := by linarith [hσV, h1]
      have h4 : cL / 2 < cL := by linarith [hcL]
      have h5 : (cL / 2) / VKd (|t| + 3) < cL / VKd (|t| + 3) :=
        div_lt_div_of_pos_right h4 hVpos
      have h6 : (1:ℝ) - cL / VKd (|t| + 3) < 1 - (cL / 2) / VKd (|t| + 3) := by linarith
      linarith [h2, h3, h6]
    · push_neg at htT
      have hV6 : VKd 6 ≤ VKd (|t| + 3) := VKd_mono (by norm_num) (by linarith)
      have hc_le : (min (cL / 2) (ε * VKd 6)) / VKd (|t| + 3) ≤ ε := by
        have h4 : min (cL / 2) (ε * VKd 6) ≤ ε * VKd 6 := min_le_right _ _
        have h5 : ε * VKd 6 ≤ ε * VKd (|t| + 3) := mul_le_mul_of_nonneg_left hV6 hε.le
        rw [div_le_iff₀ hVpos]
        linarith [h4, h5, hVpos]
      have hlt : |t| ≤ max T₀ 4 := by linarith [htT, le_max_left T₀ 4]
      have h1e : 1 - ε ≤ σ := by linarith [hσV, hc_le]
      have h2e : σ ≤ 2 := by linarith
      exact (hstrip σ t hlt h1e h2e) hzero

end
end Work.BMF
