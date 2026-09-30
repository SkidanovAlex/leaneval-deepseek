import Mathlib
import Submission.Work.BMF.VKStripDefs
import Submission.Work.BMF.vk_L_lower
import Submission.Work.BMF.N4chain.L_goodRadius
import Submission.Work.BMF.N4chain.LFunction_norm_lower_of_re
import Submission.Commons.Analysis.Complex.logDeriv_sub_divisor_le
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
import Submission.Commons.Analysis.Complex.divisor_subBall_factor
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Complex Metric MeromorphicOn
open scoped Topology

/-! ### Divisor sums and real parts -/

private lemma Finset_sum_re (Z : Finset ℂ) (g : ℂ → ℂ) :
    (∑ u ∈ Z, g u).re = ∑ u ∈ Z, (g u).re := by
  classical
  refine Finset.induction_on Z ?base ?step
  · simp
  · intro a Z' ha ih
    rw [Finset.sum_insert ha, Complex.add_re, Finset.sum_insert ha, ih]

private lemma re_coe_mul (n : ℤ) (z : ℂ) : (((n : ℤ) : ℂ) * z).re = (n : ℝ) * z.re := by
  rw [Complex.mul_re]
  have h1 : (((n : ℤ) : ℂ)).re = (n : ℝ) := by simp
  have h2 : (((n : ℤ) : ℂ)).im = 0 := by simp
  rw [h1, h2]
  ring

private lemma finsum_re_eq {d : ℂ → ℤ} (hfin : (Function.support d).Finite) (g : ℂ → ℂ) :
    (∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * g u).re = ∑ᶠ u : ℂ, ((d u : ℤ) : ℝ) * (g u).re := by
  classical
  let S : Finset ℂ := hfin.toFinset
  have hsub1 : Function.support (fun u : ℂ => ((d u : ℤ) : ℂ) * g u) ⊆ (S : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    have hd : d u ≠ 0 := fun hd0 => hu (by simp [hd0])
    exact hfin.mem_toFinset.mpr hd
  have hsub2 : Function.support (fun u : ℂ => ((d u : ℤ) : ℝ) * (g u).re) ⊆ (S : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    have hd : d u ≠ 0 := fun hd0 => hu (by simp [hd0])
    exact hfin.mem_toFinset.mpr hd
  rw [finsum_eq_sum_of_support_subset (f := fun u : ℂ => ((d u : ℤ) : ℂ) * g u)
        (s := S) hsub1]
  rw [finsum_eq_sum_of_support_subset (f := fun u : ℂ => ((d u : ℤ) : ℝ) * (g u).re)
        (s := S) hsub2]
  rw [Finset_sum_re]
  exact Finset.sum_congr rfl (fun u _ => re_coe_mul (d u) (g u))

/-- `Re (1/(cc-u)) ≥ 0` whenever `Re u ≤ Re cc`. -/
private lemma re_inv_sub_nonneg {cc u : ℂ} (h : u.re ≤ cc.re) : 0 ≤ (1 / (cc - u)).re := by
  rw [one_div, Complex.inv_re]
  refine div_nonneg ?_ (Complex.normSq_nonneg _)
  rw [Complex.sub_re]
  linarith

/-- The divisor coefficient at a zero of `f` strictly inside the analyticity ball is non-zero. -/
private lemma divisor_ne_zero_at_zero {f : ℂ → ℂ} {cc : ℂ} {R : ℝ}
    (hR : 0 < R) (hfan : AnalyticOnNhd ℂ f (Metric.closedBall cc R)) (hfc : f cc ≠ 0)
    {ρ : ℂ} (hρball : ρ ∈ Metric.closedBall cc (R / 2)) (hfρ : f ρ = 0) :
    MeromorphicOn.divisor f (Metric.closedBall cc (R / 2)) ρ ≠ 0 := by
  have hR2pos : 0 < R / 2 := by linarith
  have hρR : ρ ∈ Metric.closedBall cc R := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hρball ⊢
    linarith
  have hρballR : ρ ∈ Metric.ball cc R := by
    rw [Metric.mem_ball, dist_eq_norm]
    rw [Metric.mem_closedBall, dist_eq_norm] at hρball
    linarith
  have hfan_ball : AnalyticOnNhd ℂ f (Metric.ball cc R) :=
    hfan.mono Metric.ball_subset_closedBall
  have hord_ne_top : analyticOrderAt f ρ ≠ ⊤ := by
    intro htop
    have hev : f =ᶠ[𝓝 ρ] 0 := (analyticOrderAt_eq_top).mp htop
    have hcc_ball : cc ∈ Metric.ball cc R := by
      rw [Metric.mem_ball, dist_self]; exact hR
    have hzeroOn := hfan_ball.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isPreconnected_ball) hρballR hev
    exact hfc (hzeroOn hcc_ball)
  have hρan : AnalyticAt ℂ f ρ := hfan ρ hρR
  have hord_ne_zero : analyticOrderAt f ρ ≠ 0 :=
    (AnalyticAt.analyticOrderAt_ne_zero hρan).mpr hfρ
  have hfan2 : AnalyticOnNhd ℂ f (Metric.closedBall cc (R / 2)) :=
    hfan.mono (by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
      linarith)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hord_ne_top
  have hn0 : n ≠ 0 := by
    intro h0
    exact hord_ne_zero (by rw [← hn, h0]; rfl)
  intro hd0
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfan2 hρball, ← hn, ENat.map_natCast,
    WithTop.untop₀_coe] at hd0
  exact hn0 (by exact_mod_cast hd0)

/-! ### Jensen bound with one zero split off -/

/-- **Log-derivative bound with one zero split off.**  If `f` is analytic on the closed ball of
radius `R` around `cc`, nonzero at `cc` and on the two circles of radii `R` and `R/2`, bounded
by `A' ‖f cc‖` on the outer circle, and all zeros of `f` in the half-ball lie weakly to the left
of `cc`, then for any zero `ρ` of `f` in the half-ball,
`-Re (f'/f)(cc) ≤ -Re (1/(cc-ρ)) + 16 log A' / R`. -/
private lemma logDeriv_re_le_of_div_pole {f : ℂ → ℂ} {cc ρ : ℂ} {R A' : ℝ}
    (hR : 0 < R) (hA'1 : (1 : ℝ) ≤ A')
    (hfan : AnalyticOnNhd ℂ f (Metric.closedBall cc R))
    (hfc : f cc ≠ 0)
    (hcirc_out : ∀ w : ℂ, ‖w - cc‖ = R → f w ≠ 0)
    (hcirc_in : ∀ w : ℂ, ‖w - cc‖ = R / 2 → f w ≠ 0)
    (hAb : ∀ w : ℂ, ‖w - cc‖ = R → ‖f w‖ ≤ A' * ‖f cc‖)
    (hzero_re : ∀ u : ℂ, ‖u - cc‖ ≤ R / 2 → f u = 0 → u.re ≤ cc.re)
    (hρball : ρ ∈ Metric.closedBall cc (R / 2)) (hfρ : f ρ = 0) :
    (-logDeriv f cc).re ≤ -(1 / (cc - ρ)).re + 16 * Real.log A' / R := by
  have hα0 : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hα : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  have hs : ‖cc - cc‖ ≤ (1 / 4) * R := by
    rw [sub_self, norm_zero]; linarith
  have hb := Commons.Analysis.Complex.logDeriv_sub_divisor_le (f := f) (c := cc) (R := R)
    (A := A') (α := 1 / 4) hR hA'1 hα0 hα hfan hfc hcirc_out hcirc_in hAb (s := cc) hs hfc
  have hfan2 : AnalyticOnNhd ℂ f (Metric.closedBall cc (R / 2)) :=
    hfan.mono (by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
      linarith)
  let d : ℂ → ℤ := MeromorphicOn.divisor f (Metric.closedBall cc (R / 2))
  have hdsupp : (Function.support d).Finite := by
    dsimp only [d]
    exact MeromorphicOn.divisor_support_finite_of_subset (f := f)
      (U := Metric.closedBall cc (R / 2)) (V := Metric.closedBall cc (R / 2))
      hfan2.meromorphicOn (isCompact_closedBall cc (R / 2)) (by intro z hz; exact hz)
  let Su : ℂ := ∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * (1 / (cc - u))
  have hre : Su.re = ∑ᶠ u : ℂ, ((d u : ℤ) : ℝ) * (1 / (cc - u)).re := by
    dsimp only [Su]
    exact finsum_re_eq hdsupp (fun u => 1 / (cc - u))
  have hterm_nonneg : ∀ u : ℂ, 0 ≤ ((d u : ℤ) : ℝ) * (1 / (cc - u)).re := by
    intro u
    by_cases hd : d u = 0
    · simp [hd]
    · have humem : u ∈ Metric.closedBall cc (R / 2) := by
        by_contra hout
        exact hd (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hout)
      have hfz : f u = 0 :=
        Commons.Analysis.Complex.zero_of_divisor_ne_zero (f := f) (a := cc) (ρ := R / 2)
          hfan2 (u := u) (by dsimp only [d] at hd; exact hd)
      have hnm : ‖u - cc‖ ≤ R / 2 := by
        rw [Metric.mem_closedBall, dist_eq_norm] at humem; exact humem
      exact mul_nonneg
        (by exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfan2 u))
        (re_inv_sub_nonneg (hzero_re u hnm hfz))
  have hρd : d ρ ≠ 0 := by
    dsimp only [d]
    exact divisor_ne_zero_at_zero hR hfan hfc hρball hfρ
  have hρval_nonneg : 0 ≤ (1 / (cc - ρ)).re := by
    refine re_inv_sub_nonneg ?_
    have hnm : ‖ρ - cc‖ ≤ R / 2 := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hρball; exact hρball
    exact hzero_re ρ hnm hfρ
  have hSu_ge : (1 / (cc - ρ)).re ≤ Su.re := by
    rw [hre]
    have hSfin : (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ) * (1 / (cc - u)).re)
        = ∑ u ∈ hdsupp.toFinset, ((d u : ℤ) : ℝ) * (1 / (cc - u)).re := by
      refine finsum_eq_sum_of_support_subset _ ?_
      intro u hu
      rw [Function.mem_support] at hu
      exact hdsupp.mem_toFinset.mpr (fun hd0 => hu (by simp [hd0]))
    rw [hSfin]
    have hρmem : ρ ∈ hdsupp.toFinset := hdsupp.mem_toFinset.mpr hρd
    have hge1 : (1 : ℤ) ≤ d ρ := by
      have h0 : (0 : ℤ) ≤ d ρ := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfan2 ρ
      omega
    have hge1' : (1 : ℝ) ≤ (d ρ : ℝ) := by exact_mod_cast hge1
    calc (1 / (cc - ρ)).re ≤ ((d ρ : ℤ) : ℝ) * (1 / (cc - ρ)).re := by nlinarith
      _ ≤ ∑ u ∈ hdsupp.toFinset, ((d u : ℤ) : ℝ) * (1 / (cc - u)).re :=
          Finset.single_le_sum (fun u _ => hterm_nonneg u) hρmem
  have hstep1 : (-logDeriv f cc).re ≤ -Su.re + ‖logDeriv f cc - Su‖ := by
    have hEq : -(logDeriv f cc) = -Su + -(logDeriv f cc - Su) := by ring
    have h1 : (-logDeriv f cc).re = -Su.re + (-(logDeriv f cc - Su)).re := by
      rw [hEq, Complex.add_re, Complex.neg_re, Complex.neg_re]
    have h2 : (-(logDeriv f cc - Su)).re ≤ ‖logDeriv f cc - Su‖ := by
      rw [Complex.neg_re]
      exact le_trans (neg_le_abs _) (Complex.abs_re_le_norm _)
    linarith
  have hb' : ‖logDeriv f cc - Su‖ ≤ 16 * Real.log A' / R := by
    have hden : (1 - 2 * (1 / 4 : ℝ)) ^ 2 = (1 / 4 : ℝ) := by norm_num
    have hval : 4 * Real.log A' / (R * (1 - 2 * (1 / 4 : ℝ)) ^ 2) = 16 * Real.log A' / R := by
      rw [hden]
      field_simp
      ring
    have hb2 : ‖logDeriv f cc - Su‖ ≤ 4 * Real.log A' / (R * (1 - 2 * (1 / 4 : ℝ)) ^ 2) := by
      convert hb using 2
    rw [hval] at hb2
    exact hb2
  linarith

/-! ### Growth on the ball -/

private lemma LFunction_norm_le_growth_ball {A c : ℝ} (h : VKGrowth A c)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {γ x η : ℝ}
    (hγ : 10 ≤ |γ|) (hx : 0 < x) (hxη : x ≤ η / 8) (hx2η : x + 2 * η ≤ 1)
    (hη : η ≤ (c / 4) * Real.log (|γ| + 3) ^ (-(6 / 7 : ℝ))) :
    ∀ w : ℂ, ‖w - (((1 + x : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 2 * η →
      ‖DirichletCharacter.LFunction χ w‖ ≤
        2 * max A 1 * (N : ℝ) * Real.log (|γ| + 3) ^ (6 / 7 : ℝ) := by
  obtain ⟨hA, hc, hgr⟩ := h
  have h2η1 : 2 * η ≤ 1 := by linarith
  have hTpos : 0 < |γ| + 3 := by linarith [abs_nonneg γ]
  have hlogTpos : 0 < Real.log (|γ| + 3) := Real.log_pos (by linarith)
  intro w hw
  set s : ℂ := ((1 + x : ℝ) : ℂ) + (γ : ℂ) * Complex.I with hs
  have hre_sub : (w - s).re = w.re - (1 + x) := by rw [hs]; simp
  have him_sub : (w - s).im = w.im - γ := by rw [hs]; simp
  have hre_le : |w.re - (1 + x)| ≤ 2 * η := by
    calc |w.re - (1 + x)| = |(w - s).re| := by rw [hre_sub]
      _ ≤ ‖w - s‖ := Complex.abs_re_le_norm _
      _ ≤ 2 * η := hw
  have him_le : |w.im - γ| ≤ 2 * η := by
    calc |w.im - γ| = |(w - s).im| := by rw [him_sub]
      _ ≤ ‖w - s‖ := Complex.abs_im_le_norm _
      _ ≤ 2 * η := hw
  have hwre_ge : 1 + x - 2 * η ≤ w.re := by
    have := (abs_le.mp hre_le).1; linarith
  have hwre_le : w.re ≤ 1 + x + 2 * η := by
    have := (abs_le.mp hre_le).2; linarith
  have hwim_ge : |γ| - 2 * η ≤ |w.im| := by
    have h := abs_sub_abs_le_abs_sub γ w.im
    rw [abs_sub_comm] at h
    have h2 : |γ| - |w.im| ≤ 2 * η := le_trans h him_le
    linarith
  have h3im : 3 ≤ |w.im| := by linarith [hγ, hwim_ge, h2η1]
  have hre2 : w.re ≤ 2 := by linarith [hwre_le, hx2η]
  have habs : |w.im| ≤ |γ| + 2 * η := by
    have h := abs_add_le γ (w.im - γ)
    have h2 : γ + (w.im - γ) = w.im := by ring
    rw [h2] at h
    linarith
  have him_bound : |w.im| + 3 ≤ 2 * (|γ| + 3) := by
    linarith [habs, hγ, h2η1, abs_nonneg γ]
  have hlog_le : Real.log (|w.im| + 3) ≤ 2 * Real.log (|γ| + 3) := by
    have hpos1 : 0 < |w.im| + 3 := by linarith [abs_nonneg w.im]
    have h1 : Real.log (|w.im| + 3) ≤ Real.log (2 * (|γ| + 3)) :=
      Real.log_le_log hpos1 him_bound
    have h2 : Real.log (2 * (|γ| + 3)) = Real.log 2 + Real.log (|γ| + 3) :=
      Real.log_mul (by norm_num) hTpos.ne'
    have h3 : Real.log 2 ≤ Real.log (|γ| + 3) :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hrpow_ge : (1 / 2) * Real.log (|γ| + 3) ^ (-(6 / 7 : ℝ)) ≤
      Real.log (|w.im| + 3) ^ (-(6 / 7 : ℝ)) := by
    have hp1 : 0 < Real.log (|w.im| + 3) := Real.log_pos (by linarith [abs_nonneg w.im])
    have h1 : (2 * Real.log (|γ| + 3)) ^ (-(6 / 7 : ℝ)) ≤
        Real.log (|w.im| + 3) ^ (-(6 / 7 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hp1 hlog_le (by norm_num)
    have h2 : (2 * Real.log (|γ| + 3)) ^ (-(6 / 7 : ℝ)) =
        2 ^ (-(6 / 7 : ℝ)) * Real.log (|γ| + 3) ^ (-(6 / 7 : ℝ)) :=
      Real.mul_rpow (by norm_num) hlogTpos.le
    have h3 : (1 / 2 : ℝ) ≤ 2 ^ (-(6 / 7 : ℝ)) := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (-1 : ℝ) ≤ -(6 / 7 : ℝ))
      rw [Real.rpow_neg_one] at h
      rw [one_div]
      exact h
    rw [h2] at h1
    calc (1 / 2) * Real.log (|γ| + 3) ^ (-(6 / 7 : ℝ))
        ≤ 2 ^ (-(6 / 7 : ℝ)) * Real.log (|γ| + 3) ^ (-(6 / 7 : ℝ)) :=
          mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hlogTpos.le _)
      _ ≤ Real.log (|w.im| + 3) ^ (-(6 / 7 : ℝ)) := h1
  have hgrowth_lo : 1 - c * Real.log (|w.im| + 3) ^ (-(6 / 7 : ℝ)) ≤ w.re := by
    have h2 : 2 * η ≤ (c / 2) * Real.log (|γ| + 3) ^ (-(6 / 7 : ℝ)) := by linarith [hη]
    have h3 : c * ((1 / 2) * Real.log (|γ| + 3) ^ (-(6 / 7 : ℝ))) ≤
        c * Real.log (|w.im| + 3) ^ (-(6 / 7 : ℝ)) :=
      mul_le_mul_of_nonneg_left hrpow_ge hc.le
    nlinarith [hwre_ge, h2, h3]
  have hval := hgr N χ w.re w.im h3im hgrowth_lo hre2
  rw [show ((w.re : ℂ) + (w.im : ℂ) * Complex.I) = w from Complex.re_add_im w] at hval
  have hlogrpow : Real.log (|w.im| + 3) ^ (6 / 7 : ℝ) ≤
      2 * Real.log (|γ| + 3) ^ (6 / 7 : ℝ) := by
    have hp : 0 ≤ (6 / 7 : ℝ) := by norm_num
    have h1 : Real.log (|w.im| + 3) ^ (6 / 7 : ℝ) ≤ (2 * Real.log (|γ| + 3)) ^ (6 / 7 : ℝ) :=
      Real.rpow_le_rpow (Real.log_nonneg (by linarith [abs_nonneg w.im])) hlog_le hp
    have h2 : (2 * Real.log (|γ| + 3)) ^ (6 / 7 : ℝ) =
        2 ^ (6 / 7 : ℝ) * Real.log (|γ| + 3) ^ (6 / 7 : ℝ) :=
      Real.mul_rpow (by norm_num) hlogTpos.le
    have h3 : (2 : ℝ) ^ (6 / 7 : ℝ) ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (6 / 7 : ℝ) ≤ 1)
      simpa using h
    rw [h2] at h1
    calc Real.log (|w.im| + 3) ^ (6 / 7 : ℝ)
        ≤ (2 : ℝ) ^ (6 / 7 : ℝ) * Real.log (|γ| + 3) ^ (6 / 7 : ℝ) := h1
      _ ≤ 2 * Real.log (|γ| + 3) ^ (6 / 7 : ℝ) :=
          mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hlogTpos.le _)
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  calc ‖DirichletCharacter.LFunction χ w‖
      ≤ A * (N : ℝ) * Real.log (|w.im| + 3) ^ (6 / 7 : ℝ) := hval
    _ ≤ A * (N : ℝ) * (2 * Real.log (|γ| + 3) ^ (6 / 7 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogrpow (mul_nonneg hA.le hN0)
    _ = 2 * A * (N : ℝ) * Real.log (|γ| + 3) ^ (6 / 7 : ℝ) := by ring
    _ ≤ 2 * max A 1 * (N : ℝ) * Real.log (|γ| + 3) ^ (6 / 7 : ℝ) := by
        have hX : 0 ≤ Real.log (|γ| + 3) ^ (6 / 7 : ℝ) := Real.rpow_nonneg hlogTpos.le _
        have hA1 : A ≤ max A 1 := le_max_left _ _
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA1 (by norm_num)) hN0) hX

/-! ### The logarithmic denominator -/

private lemma one_le_VKDenom {N : ℕ} [NeZero N] {γ η x : ℝ}
    (hγ : 10 ≤ |γ|) (hx : 0 < x) (hx1 : x ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) :
    1 ≤ VKDenom N γ η x := by
  rw [VKDenom]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have h1 : 0 ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hlog3 : (1 : ℝ) ≤ Real.log (|γ| + 3) :=
    le_trans log_three_ge_one
      (Real.log_le_log (by norm_num) (by linarith [abs_nonneg γ]))
  have h2 : 0 ≤ Real.log (Real.log (|γ| + 3)) := Real.log_nonneg hlog3
  have h3 : 0 ≤ Real.log (1 / η) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hη]; linarith
  have h4 : 0 ≤ Real.log (1 / x) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hx]; linarith
  linarith

/-- **The logarithmic ratio `log(M/m)` is dominated by `VKDenom`.** -/
private lemma log_M_div_m_le {A C₀ : ℝ} (hC₀ : 1 ≤ C₀) {N : ℕ} [NeZero N] {γ η x : ℝ}
    (hγ : 10 ≤ |γ|) (hx : 0 < x) (hx1 : x ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) :
    Real.log ((2 * max A 1 * (N : ℝ) * Real.log (|γ| + 3) ^ (6 / 7 : ℝ)) / (x / C₀))
      ≤ (Real.log (max A 1) + Real.log C₀ + 4) * VKDenom N γ η x := by
  have hTpos : 0 < |γ| + 3 := by linarith [abs_nonneg γ]
  have hlogTpos : 0 < Real.log (|γ| + 3) := Real.log_pos (by linarith)
  have hmax1 : (1 : ℝ) ≤ max A 1 := le_max_right _ _
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  set M : ℝ := 2 * max A 1 * (N : ℝ) * Real.log (|γ| + 3) ^ (6 / 7 : ℝ) with hMdef
  set m : ℝ := x / C₀ with hmdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hmpos : 0 < m := by rw [hmdef]; positivity
  have hlogM : Real.log M = Real.log 2 + Real.log (max A 1) + Real.log (N : ℝ) +
      (6 / 7) * Real.log (Real.log (|γ| + 3)) := by
    rw [hMdef]
    rw [show 2 * max A 1 * (N : ℝ) * Real.log (|γ| + 3) ^ (6 / 7 : ℝ)
        = (2 * max A 1 * (N : ℝ)) * Real.log (|γ| + 3) ^ (6 / 7 : ℝ) by ring]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [show (2 : ℝ) * max A 1 * (N : ℝ) = (2 * max A 1) * (N : ℝ) by ring]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by norm_num) (by positivity)]
    rw [Real.log_rpow hlogTpos]
  have hlogm : Real.log m = Real.log x - Real.log C₀ := by
    rw [hmdef, Real.log_div hx.ne' (by positivity)]
  have hD1 : 1 ≤ VKDenom N γ η x := one_le_VKDenom hγ hx hx1 hη hη1
  have hlogN : Real.log (N : ℝ) ≤ VKDenom N γ η x := by
    have hle : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [VKDenom]
    have h1 : 0 ≤ Real.log (Real.log (|γ| + 3)) := by
      have hlog3 : (1 : ℝ) ≤ Real.log (|γ| + 3) :=
        le_trans log_three_ge_one
          (Real.log_le_log (by norm_num) (by linarith [abs_nonneg γ]))
      exact Real.log_nonneg hlog3
    have h3 : 0 ≤ Real.log (1 / η) := by
      apply Real.log_nonneg; rw [le_div_iff₀ hη]; linarith
    have h4 : 0 ≤ Real.log (1 / x) := by
      apply Real.log_nonneg; rw [le_div_iff₀ hx]; linarith
    linarith
  have hloglogT : (6 / 7) * Real.log (Real.log (|γ| + 3)) ≤ VKDenom N γ η x := by
    have hnn : 0 ≤ Real.log (Real.log (|γ| + 3)) := by
      have hlog3 : (1 : ℝ) ≤ Real.log (|γ| + 3) :=
        le_trans log_three_ge_one
          (Real.log_le_log (by norm_num) (by linarith [abs_nonneg γ]))
      exact Real.log_nonneg hlog3
    have hle : Real.log (Real.log (|γ| + 3)) ≤ VKDenom N γ η x := by
      rw [VKDenom]
      have h1 : 0 ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith)
      have h3 : 0 ≤ Real.log (1 / η) := by
        apply Real.log_nonneg; rw [le_div_iff₀ hη]; linarith
      have h4 : 0 ≤ Real.log (1 / x) := by
        apply Real.log_nonneg; rw [le_div_iff₀ hx]; linarith
      linarith
    linarith
  have hlogx : -Real.log x ≤ VKDenom N γ η x := by
    have h4 : 0 ≤ Real.log (1 / x) := by
      apply Real.log_nonneg; rw [le_div_iff₀ hx]; linarith
    have hxe : Real.log (1 / x) = -Real.log x := by
      rw [one_div, Real.log_inv]
    rw [VKDenom]
    have h1 : 0 ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ Real.log (Real.log (|γ| + 3)) := by
      have hlog3 : (1 : ℝ) ≤ Real.log (|γ| + 3) :=
        le_trans log_three_ge_one
          (Real.log_le_log (by norm_num) (by linarith [abs_nonneg γ]))
      exact Real.log_nonneg hlog3
    have h3 : 0 ≤ Real.log (1 / η) := by
      apply Real.log_nonneg; rw [le_div_iff₀ hη]; linarith
    linarith [h4, hxe]
  have hlogA_nn : 0 ≤ Real.log (max A 1) := Real.log_nonneg hmax1
  have hlogC_nn : 0 ≤ Real.log C₀ := Real.log_nonneg hC₀
  have hlog2_le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  rw [Real.log_div hMpos.ne' hmpos.ne', hlogM, hlogm]
  have h1 : Real.log (max A 1) ≤ Real.log (max A 1) * VKDenom N γ η x := by
    nlinarith [hlogA_nn, hD1]
  have h2 : Real.log C₀ ≤ Real.log C₀ * VKDenom N γ η x := by
    nlinarith [hlogC_nn, hD1]
  have h3 : Real.log 2 ≤ VKDenom N γ η x := le_trans hlog2_le hD1
  linarith [hlogN, hloglogT, hlogx, h1, h2, h3]

/-! ### The core estimate -/

private lemma strip_core {A c : ℝ} (h : VKGrowth A c) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {γ x η : ℝ}
    (hγ : 10 ≤ |γ|) (hx : 0 < x) (hxη : x ≤ η / 8) (hx2η : x + 2 * η ≤ 1)
    (hη : η ≤ (c / 4) * Real.log (|γ| + 3) ^ (-(6 / 7 : ℝ))) :
    (∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
        ‖ρ - (((1 + x : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ η / 4 →
        0 ≤ (1 / ((((1 + x : ℝ) : ℂ) + (γ : ℂ) * Complex.I) - ρ)).re) ∧
    (∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
        ‖ρ - (((1 + x : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ η / 4 →
        (-logDeriv (DirichletCharacter.LFunction χ)
            (((1 + x : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re ≤
          -(1 / ((((1 + x : ℝ) : ℂ) + (γ : ℂ) * Complex.I) - ρ)).re +
            32 * (Real.log (max A 1) + Real.log 2 + 4) * VKDenom N γ η x / η) ∧
    ((∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
        η / 4 < ‖ρ - (((1 + x : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖) →
      (-logDeriv (DirichletCharacter.LFunction χ)
          (((1 + x : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re ≤
        32 * (Real.log (max A 1) + Real.log 2 + 4) * VKDenom N γ η x / η) := by
  have hηpos : 0 < η := by linarith
  have hη1 : η ≤ 1 := by linarith
  have hx1 : x ≤ 1 := by linarith
  set s : ℂ := ((1 + x : ℝ) : ℂ) + (γ : ℂ) * Complex.I with hs
  set M : ℝ := 2 * max A 1 * (N : ℝ) * Real.log (|γ| + 3) ^ (6 / 7 : ℝ) with hMdef
  set m : ℝ := x / 2 with hmdef
  have hmpos : 0 < m := by rw [hmdef]; linarith
  have hfs : DirichletCharacter.LFunction χ s ≠ 0 := by
    have hs1 : 1 ≤ s.re := by rw [hs]; simp; linarith
    have hsne : s ≠ 1 := by
      intro h1
      have hre1 : s.re = 1 := by rw [h1]; simp
      rw [hs] at hre1
      simp at hre1
      linarith
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hsne) hs1
  have hmfs : m ≤ ‖DirichletCharacter.LFunction χ s‖ := by
    have hh := Work.BMF.N4chain.LFunction_norm_lower_of_re χ (s := s) (y := x) hx hx1
      (by rw [hs]; simp)
    rw [hmdef]; exact hh
  have hM : ∀ w : ℂ, ‖w - s‖ ≤ 2 * η → ‖DirichletCharacter.LFunction χ w‖ ≤ M := by
    intro w hw
    rw [hMdef]
    have hh := LFunction_norm_le_growth_ball (A := A) (c := c) h (N := N) χ hγ hx hxη hx2η hη
    exact hh w (by rw [← hs]; exact hw)
  have hmM : m ≤ M := le_trans hmfs (hM s (by rw [sub_self, norm_zero]; linarith))
  have hMpos : 0 < M := lt_of_lt_of_le hmpos hmM
  have hzero : ∀ u : ℂ, DirichletCharacter.LFunction χ u = 0 → ‖u - s‖ ≤ 2 * η →
      u.re ≤ s.re := by
    intro u hu hdist
    by_contra hlt
    rw [not_le] at hlt
    have hsre : s.re = 1 + x := by rw [hs]; simp
    have h1 : 1 ≤ u.re := by rw [hsre] at hlt; linarith
    have hune : u ≠ 1 := by
      intro h1c
      have hge : |γ| ≤ ‖(1 : ℂ) - s‖ := by
        have him : ((1 : ℂ) - s).im = -γ := by rw [hs]; simp
        calc |γ| = |((1 : ℂ) - s).im| := by rw [him]; simp
          _ ≤ ‖(1 : ℂ) - s‖ := Complex.abs_im_le_norm _
      rw [h1c] at hdist
      linarith [hγ, hge, hdist, hx2η, hx]
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hune) h1) hu
  have hge1s : |γ| ≤ ‖(1 : ℂ) - s‖ := by
    have him : ((1 : ℂ) - s).im = -γ := by rw [hs]; simp
    calc |γ| = |((1 : ℂ) - s).im| := by rw [him]; simp
      _ ≤ ‖(1 : ℂ) - s‖ := Complex.abs_im_le_norm _
  have hne1 : ∀ w : ℂ, w ∈ Metric.ball s (η + 1) → w ≠ 1 := by
    intro w hw hw1
    have hdist : ‖w - s‖ < η + 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hw; exact hw
    rw [hw1] at hdist
    linarith [hγ, hge1s, hdist, hη1]
  have hL_an : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ)
      (Metric.closedBall s (2 * η)) := by
    refine LFunction_analyticOnNhd_closedBall χ (c := s) (R := 2 * η) ?_
    intro hmem
    rw [Metric.mem_closedBall, dist_eq_norm] at hmem
    linarith [hγ, hge1s, hmem, hx2η, hx]
  obtain ⟨R', hR'1, hR'2, hcirc_out, hcirc_in⟩ :=
    Work.BMF.N4chain.L_goodRadius χ (cc := s) (η := η) hηpos hne1 hfs
  have key : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ‖ρ - s‖ ≤ R' / 2 →
      (-logDeriv (DirichletCharacter.LFunction χ) s).re ≤
        -(1 / (s - ρ)).re + 32 * (Real.log (max A 1) + Real.log 2 + 4) *
          VKDenom N γ η x / η := by
    intro ρ hρ hρR
    have hR'pos : 0 < R' := by linarith
    have hA'1 : 1 ≤ M / m := (one_le_div hmpos).mpr hmM
    have hfan : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall s R') :=
      hL_an.mono (fun z hz => by
        rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
        linarith [hR'2])
    have hAb : ∀ w : ℂ, ‖w - s‖ = R' →
        ‖DirichletCharacter.LFunction χ w‖ ≤ (M / m) * ‖DirichletCharacter.LFunction χ s‖ := by
      intro w hw
      have h1 : ‖DirichletCharacter.LFunction χ w‖ ≤ M := hM w (by rw [hw]; linarith [hR'2])
      have h2 : M ≤ (M / m) * ‖DirichletCharacter.LFunction χ s‖ := by
        have h3 : (M / m) * m = M := div_mul_cancel₀ M hmpos.ne'
        have h4 : (M / m) * m ≤ (M / m) * ‖DirichletCharacter.LFunction χ s‖ :=
          mul_le_mul_of_nonneg_left hmfs (div_nonneg hMpos.le hmpos.le)
        linarith
      linarith
    have hzeroR : ∀ u : ℂ, ‖u - s‖ ≤ R' / 2 →
        DirichletCharacter.LFunction χ u = 0 → u.re ≤ s.re :=
      fun u hu hu0 => hzero u hu0 (by linarith [hR'2, hu])
    have hJ := logDeriv_re_le_of_div_pole (f := DirichletCharacter.LFunction χ) (cc := s)
      (ρ := ρ) (R := R') (A' := M / m) hR'pos hA'1 hfan hfs hcirc_out hcirc_in hAb hzeroR
      (hρball := by rw [Metric.mem_closedBall, dist_eq_norm]; exact hρR) (hfρ := hρ)
    have hRe : 0 ≤ (1 / (s - ρ)).re :=
      re_inv_sub_nonneg (hzero ρ hρ (by linarith [hR'2, hρR, hηpos]))
    have hbound : 16 * Real.log (M / m) / R' ≤ 32 * Real.log (M / m) / η := by
      have h1 : 1 / R' ≤ 2 / η := by
        have hhalf : 0 < η / 2 := by linarith
        have hle := one_div_le_one_div_of_le hhalf (by linarith : η / 2 ≤ R')
        have heq : 1 / (η / 2) = 2 / η := by field_simp
        rwa [heq] at hle
      calc 16 * Real.log (M / m) / R' = 16 * Real.log (M / m) * (1 / R') := by ring
        _ ≤ 16 * Real.log (M / m) * (2 / η) :=
            mul_le_mul_of_nonneg_left h1 (by linarith [Real.log_nonneg hA'1])
        _ = 32 * Real.log (M / m) / η := by ring
    have hKD : 32 * Real.log (M / m) ≤
        32 * (Real.log (max A 1) + Real.log 2 + 4) * VKDenom N γ η x := by
      have hDL := log_M_div_m_le (A := A) (C₀ := 2) (by norm_num) (N := N) (γ := γ) (η := η)
        (x := x) hγ hx hx1 hηpos hη1
      have hm2 : m = x / (2 : ℝ) := hmdef
      have hDM : Real.log (M / m) ≤
          (Real.log (max A 1) + Real.log 2 + 4) * VKDenom N γ η x := by
        rw [hMdef, hm2]; exact hDL
      nlinarith [hDM]
    have h16 : 16 * Real.log (M / m) / R' ≤ 32 * Real.log (M / m) / η := hbound
    have h32 : 32 * Real.log (M / m) / η ≤
        32 * (Real.log (max A 1) + Real.log 2 + 4) * VKDenom N γ η x / η :=
      div_le_div_of_nonneg_right hKD hηpos.le
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro ρ hρ hρs
    exact re_inv_sub_nonneg (hzero ρ hρ (by linarith))
  · intro ρ hρ hρs
    exact key ρ hρ (by linarith [hR'1])
  · intro hno
    have hzf : ∀ w : ℂ, w ∈ Metric.ball s (η / 4) → DirichletCharacter.LFunction χ w ≠ 0 := by
      intro w hw hw0
      have hws : ‖w - s‖ < η / 4 := by
        rw [Metric.mem_ball, dist_eq_norm] at hw; exact hw
      exact absurd (hno w hw0) (not_lt.mpr (le_of_lt hws))
    have hgM : ∀ w : ℂ, w ∈ Metric.ball s (η / 4) → ‖DirichletCharacter.LFunction χ w‖ ≤ M := by
      intro w hw
      apply hM w
      rw [Metric.mem_ball, dist_eq_norm] at hw
      linarith
    have hR4 : (0 : ℝ) < η / 4 := by linarith
    have hmono : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.ball s (η / 4)) :=
      hL_an.mono (fun z hz => by
        rw [Metric.mem_ball, dist_eq_norm] at hz
        rw [Metric.mem_closedBall, dist_eq_norm]
        linarith)
    have hb := Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
      (g := DirichletCharacter.LFunction χ) (c := s) (R := η / 4) (m := m) (M := M)
      hR4 hmpos hmM hmono hzf hgM hmfs
      (z₀ := s) (Metric.mem_ball_self hR4) (η / 8) (by linarith) (by
        rw [sub_self, norm_zero]; linarith)
    have hb3 : ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤
        16 * (Real.log (2 * M) - Real.log m) / η := by
      have hthis := hb
      rw [sub_self, norm_zero, zero_add] at hthis
      have hsimp : 2 * (Real.log (2 * M) - Real.log m) * (η / 8) /
            ((η / 4 - 0 - η / 8) * (η / 8))
          = 16 * (Real.log (2 * M) - Real.log m) / η := by
        rw [show η / 4 - 0 - η / 8 = η / 8 by ring]
        rw [div_eq_div_iff (by positivity : (η / 8) * (η / 8) ≠ 0) hηpos.ne']
        ring
      rwa [hsimp] at hthis
    have hlog2M : Real.log (2 * M) - Real.log m = Real.log 2 + Real.log (M / m) := by
      rw [← Real.log_div (mul_ne_zero (by norm_num) hMpos.ne') hmpos.ne']
      rw [show 2 * M / m = 2 * (M / m) by ring]
      rw [Real.log_mul (by norm_num) (div_ne_zero hMpos.ne' hmpos.ne')]
    have hfin : 16 * (Real.log (2 * M) - Real.log m) ≤
        32 * (Real.log (max A 1) + Real.log 2 + 4) * VKDenom N γ η x := by
      have hDL := log_M_div_m_le (A := A) (C₀ := 2) (by norm_num) (N := N) (γ := γ) (η := η)
        (x := x) hγ hx hx1 hηpos hη1
      have hm2 : m = x / (2 : ℝ) := hmdef
      have hDM : Real.log (M / m) ≤
          (Real.log (max A 1) + Real.log 2 + 4) * VKDenom N γ η x := by
        rw [hMdef, hm2]; exact hDL
      have hD1 : 1 ≤ VKDenom N γ η x := one_le_VKDenom hγ hx hx1 hηpos hη1
      have hDnn : 0 ≤ VKDenom N γ η x := le_trans zero_le_one hD1
      have hlog2le : Real.log 2 ≤ VKDenom N γ η x := by
        have h2le : Real.log 2 ≤ 1 := by
          have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
          linarith
        linarith
      have hK4 : (4 : ℝ) ≤ Real.log (max A 1) + Real.log 2 + 4 := by
        have h1 : 0 ≤ Real.log (max A 1) := Real.log_nonneg (le_max_right (A) (1 : ℝ))
        have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        linarith
      rw [hlog2M]
      have hstep : 16 * (Real.log 2 + Real.log (M / m)) ≤
          16 * VKDenom N γ η x +
            16 * ((Real.log (max A 1) + Real.log 2 + 4) * VKDenom N γ η x) := by
        nlinarith [hlog2le, hDM]
      have h16 : 16 * VKDenom N γ η x +
          16 * ((Real.log (max A 1) + Real.log 2 + 4) * VKDenom N γ η x) ≤
          32 * (Real.log (max A 1) + Real.log 2 + 4) * VKDenom N γ η x := by
        nlinarith [hDnn, hK4]
      linarith
    have h1 : (-logDeriv (DirichletCharacter.LFunction χ) s).re ≤
        ‖logDeriv (DirichletCharacter.LFunction χ) s‖ := by
      rw [Complex.neg_re]
      exact le_trans (neg_le_abs _) (Complex.abs_re_le_norm _)
    calc (-logDeriv (DirichletCharacter.LFunction χ) s).re
        ≤ ‖logDeriv (DirichletCharacter.LFunction χ) s‖ := h1
      _ ≤ 16 * (Real.log (2 * M) - Real.log m) / η := hb3
      _ ≤ 32 * (Real.log (max A 1) + Real.log 2 + 4) * VKDenom N γ η x / η :=
          div_le_div_of_nonneg_right hfin hηpos.le

/-- **Strip logarithmic-derivative bounds of Vinogradov–Korobov type, from the growth bound.**

Given `VKGrowth A c` (node `V2`: `‖L(σ+it,ψ)‖ ≤ A M (log(|t|+3))^{6/7}` for `3 ≤ |t|`,
`1 - c (log(|t|+3))^{-6/7} ≤ σ ≤ 2`, every character `ψ` mod `M`), there is a constant
`E > 0` such that `VKStrip (c/4) E` holds: for every character `χ` mod `N`, every `|γ| ≥ 10`,
`0 < x`, `x ≤ η/8`, `x + 2η ≤ 1`, `η ≤ (c/4)(log(|γ|+3))^{-6/7}`,

* (regular form) `-Re (L'/L)(1+x+iγ, χ) ≤ E · VKDenom N γ η x / η`;
* (pole form) if moreover `0 < β < 1`, `1-β ≤ η/16` and `L(β+iγ, χ) = 0`, then
  `-Re (L'/L)(1+x+iγ, χ) ≤ -1/(x+1-β) + E · VKDenom N γ η x / η`.

ROUTE.  Fix `N`, `χ`, `γ`, `x`, `η` with the stated hypotheses; put `T := |γ| + 3`,
`s := 1+x+iγ`, `Q₀ := log(N+2) + log log T`, and `M := 2 * max A 1 * N * (log T)^{6/7}`
(an `M` of this shape suffices; any constant factor is absorbed into `E`), with `m := x / C₀`
where `C₀` is the constant of `Work.BMF.exists_LFunction_norm_lower_one_add` (which gives
`m ≤ ‖L(s,χ)‖`, since `x ≤ η/8` and `x + 2η ≤ 1` give `x ≤ 1/17 ≤ 1/2`); use
`Work.BMF.LFunction_analyticOnNhd_closedBall` for analyticity on balls around `s`, allowed
because `‖1 - s‖ ≥ |γ| ≥ 10 > 2η`.  (You will want to import
`Submission.Commons.Analysis.Complex.logDeriv_sub_divisor_le`,
`Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic` and
`Submission.Commons.Analysis.Complex.divisor_subBall_factor`.)

1. GROWTH ON THE BALL.  For `‖w - s‖ ≤ 2η`: `Re w ≥ 1 + x - 2η ≥ 1 - (c/2)(log T)^{-6/7}`,
   `|Im w| ≥ |γ| - 2η ≥ 3`, `|Im w| + 3 ≤ 2|γ| + 3 ≤ 2(|γ|+3)`, hence
   `log(|Im w|+3) ≤ 2 log T` and `(log(|Im w|+3))^{-6/7} ≥ 2^{-6/7}(log T)^{-6/7} ≥ (1/2)(log T)^{-6/7}`,
   so the `VKGrowth` hypothesis applies: `‖L(w,χ)‖ ≤ M`.  Also `Re w ≤ 1 + x + 2η ≤ 2`.

2. ZEROS INSIDE THE BALL HAVE `Re < 1 + x`.  For `‖u - s‖ ≤ 2η` one has `u ≠ 1`, so
   `L(u,χ) ≠ 0` for `u.re ≥ 1` (`DirichletCharacter.LFunction_ne_zero_of_one_le_re` with `Or.inr`).

3. JENSEN WITH ONE POLE SPLIT OFF (a helper to prove in this file): if `f` is analytic on
   `closedBall s (2R)`, `f s ≠ 0`, `‖f‖ ≤ M` there, `m ≤ ‖f s‖`, every zero of `f` in
   `closedBall s (2R)` has real part `≤ s.re`, and `ρ` is a zero with `‖ρ - s‖ ≤ R/4`, then
   `(-logDeriv f s).re ≤ -(1/(s-ρ)).re + 4 log (M/m) / R`.  Proof: the set of bad radii
   `{|ρ' - s| : f ρ' = 0, ‖ρ'-s‖ ≤ 2R} ∪ {2|ρ'-s| : ...}` is finite
   (`Commons.Analysis.Complex.divisor_support_finite_closedBall` for
   `AnalyticOnNhd ℂ f (closedBall s (2R))`, with `AnalyticAt.analyticOrderAt_eq_zero_not` and
   `MeromorphicOn.AnalyticOnNhd.divisor_apply` to see that every zero lies in the divisor
   support); hence there is `R'` with `R < R' < 2R` such that `f ≠ 0` on the circles of radii
   `R'` and `R'/2` around `s`.  Apply `Commons.Analysis.Complex.logDeriv_sub_divisor_le` with
   `A := M/m`, `α := 0` and the evaluation point `s`, then use that `Re (1/(s-u)) > 0` for every
   zero `u` in the divisor sum (part 2), so that
   `(∑ᶠ u, d_u (1/(s-u))).re ≥ d_ρ · Re (1/(s-ρ)) ≥ Re (1/(s-ρ))`.

4. CONCLUSION.
   * REGULAR FORM: if some zero `ρ` of `L(·,χ)` satisfies `‖ρ - s‖ ≤ η/4`, apply step 3 with
     `R := η`; since `Re (1/(s-ρ)) > 0` (part 2), the pole term is `≤ 0` and
     `(-logDeriv L(·,χ) s).re ≤ 4 log (M/m)/η`.  If there is no such zero, apply
     `Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic` on the ball of radius
     `η/4` around `s` with `ρ := η/8`, `z₀ := s`, giving
     `‖L'/L(s)‖ ≤ 16 (log (2M) - log m)/η` and hence the same conclusion.
   * POLE FORM: with `ρ := β + iγ` one has `‖ρ - s‖ = x + 1 - β ≤ 3η/16 ≤ η/4`, so step 3 gives
     `(-logDeriv L(·,χ) s).re ≤ -1/(x + 1 - β) + 4 log (M/m)/η`.

5. CONSTANTS.  `log(M/m) ≤ log(max A 1) + log 2 + log N + (6/7) log log T + log C₀ + log(1/x)`, and
   each of `log N`, `log log T`, `log C₀`, `log(1/x)` is `≤ C · VKDenom N γ η x` for a constant `C`
   depending only on `A` (note `VKDenom N γ η x = log(N+2) + log log(|γ|+3) + log(1/η) + log(1/x) + 1 ≥ 1`).
   Hence `E := 4 C` works (`C` may depend on `A` and `c`, which are fixed parameters of the theorem). -/
theorem LFunction_strip_VK (A c : ℝ) (h : VKGrowth A c) :
    ∃ E : ℝ, 0 < E ∧ VKStrip (c / 4) E := by
  have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hEpos : 0 < 32 * (Real.log (max A 1) + Real.log 2 + 4) + 16 * Real.log 2 + 16 := by
    have h1 : 0 ≤ Real.log (max A 1) := Real.log_nonneg (le_max_right (A) (1 : ℝ))
    linarith
  refine ⟨32 * (Real.log (max A 1) + Real.log 2 + 4) + 16 * Real.log 2 + 16,
    hEpos, hEpos, ?_, ?_⟩
  · intro N hN χ γ x η hγ hx hxη hx2η hη
    obtain ⟨hpos, hkey, hdirect⟩ :=
      strip_core (A := A) (c := c) h (N := N) χ hγ hx hxη hx2η hη
    have hηpos : 0 < η := by linarith
    have hx1 : x ≤ 1 := by linarith
    have hη1 : η ≤ 1 := by linarith
    have hD1 : 1 ≤ VKDenom N γ η x := one_le_VKDenom hγ hx hx1 hηpos hη1
    have hDnn : 0 ≤ VKDenom N γ η x / η := div_nonneg (le_trans zero_le_one hD1) hηpos.le
    have hC : 32 * (Real.log (max A 1) + Real.log 2 + 4) ≤
        32 * (Real.log (max A 1) + Real.log 2 + 4) + 16 * Real.log 2 + 16 := by
      linarith
    have hC' : 32 * (Real.log (max A 1) + Real.log 2 + 4) * (VKDenom N γ η x / η) ≤
        (32 * (Real.log (max A 1) + Real.log 2 + 4) + 16 * Real.log 2 + 16) *
          (VKDenom N γ η x / η) := mul_le_mul_of_nonneg_right hC hDnn
    set s : ℂ := ((1 + x : ℝ) : ℂ) + (γ : ℂ) * Complex.I with hs
    by_cases hz : ∃ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 ∧ ‖ρ - s‖ ≤ η / 4
    · obtain ⟨ρ, hρ, hρs⟩ := hz
      have h1 := hkey ρ hρ hρs
      have h2 := hpos ρ hρ hρs
      calc (-logDeriv (DirichletCharacter.LFunction χ) s).re
          ≤ -(1 / (s - ρ)).re + 32 * (Real.log (max A 1) + Real.log 2 + 4) *
              VKDenom N γ η x / η := h1
        _ ≤ 0 + 32 * (Real.log (max A 1) + Real.log 2 + 4) * VKDenom N γ η x / η := by
            linarith
        _ = 32 * (Real.log (max A 1) + Real.log 2 + 4) * (VKDenom N γ η x / η) := by ring
        _ ≤ (32 * (Real.log (max A 1) + Real.log 2 + 4) + 16 * Real.log 2 + 16) *
              (VKDenom N γ η x / η) := hC'
        _ = (32 * (Real.log (max A 1) + Real.log 2 + 4) + 16 * Real.log 2 + 16) *
              VKDenom N γ η x / η := by ring
    · have hno : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → η / 4 < ‖ρ - s‖ := by
        intro ρ hρ
        by_contra hcon
        exact hz ⟨ρ, hρ, le_of_not_gt hcon⟩
      have h1 := hdirect hno
      calc (-logDeriv (DirichletCharacter.LFunction χ) s).re
          ≤ 32 * (Real.log (max A 1) + Real.log 2 + 4) * VKDenom N γ η x / η := h1
        _ = 32 * (Real.log (max A 1) + Real.log 2 + 4) * (VKDenom N γ η x / η) := by ring
        _ ≤ (32 * (Real.log (max A 1) + Real.log 2 + 4) + 16 * Real.log 2 + 16) *
              (VKDenom N γ η x / η) := hC'
        _ = (32 * (Real.log (max A 1) + Real.log 2 + 4) + 16 * Real.log 2 + 16) *
              VKDenom N γ η x / η := by ring
  · intro N hN χ γ x η β hγ hx hxη hx2η hη hβ0 hβ1 hβη hLβ
    obtain ⟨hpos, hkey, hdirect⟩ :=
      strip_core (A := A) (c := c) h (N := N) χ hγ hx hxη hx2η hη
    have hηpos : 0 < η := by linarith
    have hx1 : x ≤ 1 := by linarith
    have hη1 : η ≤ 1 := by linarith
    have hD1 : 1 ≤ VKDenom N γ η x := one_le_VKDenom hγ hx hx1 hηpos hη1
    have hDnn : 0 ≤ VKDenom N γ η x / η := div_nonneg (le_trans zero_le_one hD1) hηpos.le
    have hC : 32 * (Real.log (max A 1) + Real.log 2 + 4) ≤
        32 * (Real.log (max A 1) + Real.log 2 + 4) + 16 * Real.log 2 + 16 := by
      linarith
    have hC' : 32 * (Real.log (max A 1) + Real.log 2 + 4) * (VKDenom N γ η x / η) ≤
        (32 * (Real.log (max A 1) + Real.log 2 + 4) + 16 * Real.log 2 + 16) *
          (VKDenom N γ η x / η) := mul_le_mul_of_nonneg_right hC hDnn
    set s : ℂ := ((1 + x : ℝ) : ℂ) + (γ : ℂ) * Complex.I with hs
    set ρ : ℂ := (β : ℂ) + (γ : ℂ) * Complex.I with hρdef
    have hρ : DirichletCharacter.LFunction χ ρ = 0 := by rw [hρdef]; exact hLβ
    have hsub : ρ - s = ((β - (1 + x) : ℝ) : ℂ) := by
      rw [hs, hρdef]
      apply Complex.ext <;> simp
    have hnorm : ‖ρ - s‖ = 1 + x - β := by
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      ring
    have hρs : ‖ρ - s‖ ≤ η / 4 := by
      rw [hnorm]; linarith
    have h1 := hkey ρ hρ hρs
    have hsub2 : s - ρ = ((1 + x - β : ℝ) : ℂ) := by
      rw [hs, hρdef]
      apply Complex.ext <;> simp
    have hpole : (1 / (s - ρ)).re = 1 / (x + 1 - β) := by
      rw [hsub2, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
      ring_nf
    calc (-logDeriv (DirichletCharacter.LFunction χ) s).re
        ≤ -(1 / (s - ρ)).re + 32 * (Real.log (max A 1) + Real.log 2 + 4) *
            VKDenom N γ η x / η := h1
      _ = -1 / (x + 1 - β) + 32 * (Real.log (max A 1) + Real.log 2 + 4) *
            VKDenom N γ η x / η := by rw [hpole]; ring
      _ ≤ -1 / (x + 1 - β) + (32 * (Real.log (max A 1) + Real.log 2 + 4) +
            16 * Real.log 2 + 16) * VKDenom N γ η x / η := by
          have h3 : 32 * (Real.log (max A 1) + Real.log 2 + 4) * VKDenom N γ η x / η
              = 32 * (Real.log (max A 1) + Real.log 2 + 4) * (VKDenom N γ η x / η) := by
            ring
          have h6 : (32 * (Real.log (max A 1) + Real.log 2 + 4) + 16 * Real.log 2 + 16) *
                VKDenom N γ η x / η
              = (32 * (Real.log (max A 1) + Real.log 2 + 4) + 16 * Real.log 2 + 16) *
                (VKDenom N γ η x / η) := by ring
          rw [h3, h6]
          linarith [hC']
      _ = -1 / (x + 1 - β) + (32 * (Real.log (max A 1) + Real.log 2 + 4) +
            16 * Real.log 2 + 16) * VKDenom N γ η x / η := by ring

end Work.BMF
