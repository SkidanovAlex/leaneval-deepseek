import Mathlib
import Submission.Commons.Analysis.Complex.divisor_subBall_factor
import Submission.Commons.Analysis.Complex.cartan_polynomial
import Submission.Commons.Analysis.Complex.Blaschke.blaschke_factor_norm
import Submission.Commons.Analysis.Complex.Harmonic.harnack_inequality_ball
import Submission.Commons.Analysis.Complex.disk_limsup_max_principle

set_option maxHeartbeats 2000000

open Complex Filter Function Metric MeromorphicOn Set Topology
open scoped Topology BigOperators

namespace Commons.Analysis.Complex

lemma riesz_cartan_log_norm_le_of_analytic_limsup {f : ℂ → ℂ} {M : ℝ} (_hM : 0 < M)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1)) (hne : ∀ z ∈ Metric.ball 0 1, f z ≠ 0)
    (hlim : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 ζ,
      ∀ z ∈ Metric.ball 0 1, z ∈ U → Real.log ‖f z‖ < Real.log M + ε) :
    ∀ z ∈ Metric.ball 0 1, Real.log ‖f z‖ ≤ Real.log M := by
  have hharm : InnerProductSpace.HarmonicOnNhd (fun z => Real.log ‖f z‖ - Real.log M)
      (Metric.ball 0 1) := by
    intro z hz
    exact ((hf z hz).harmonicAt_log_norm (hne z hz)).sub
      (InnerProductSpace.harmonicAt_const (Real.log M))
  have hmain := disk_limsup_max_principle (u := fun z => Real.log ‖f z‖ - Real.log M) hharm
    (fun ζ hζ ε hε => by
      obtain ⟨U, hU, hUl⟩ := hlim ζ hζ ε hε
      exact ⟨U, hU, fun z hz hzU => by have := hUl z hz hzU; linarith⟩)
  intro z hz
  have := hmain z hz
  linarith

/-- Per-factor geometric bound: for `‖u‖ ≤ rr`, `‖z‖ ≤ ρ`, `ρ < rr < 1`,
`(1+ρrr)/(ρ+rr) * ‖z-u‖ ≤ ‖1 - conj u * z‖`. -/
lemma riesz_cartan_perfactor (rr ρ : ℝ) (hρ0 : 0 < ρ) (hρrr : ρ < rr) (hrr1 : rr < 1)
    (u z : ℂ) (hu : ‖u‖ ≤ rr) (hz : ‖z‖ ≤ ρ) :
    ((1 + ρ*rr)/(ρ+rr)) * ‖z - u‖ ≤ ‖1 - (starRingEnd ℂ) u * z‖ := by
  have hrr0 : 0 < rr := lt_trans hρ0 hρrr
  have hρ1 : ρ < 1 := lt_trans hρrr hrr1
  have hdpos : 0 < ρ + rr := by linarith
  set c : ℝ := (1 + ρ*rr)/(ρ+rr) with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hcge1 : 1 ≤ c := by
    rw [hcdef, le_div_iff₀ hdpos, one_mul]; nlinarith
  have hcore : c * (‖u‖ + ‖z‖) ≤ 1 + ‖u‖*‖z‖ := by
    rw [hcdef, div_mul_eq_mul_div, div_le_iff₀ hdpos]
    have hD : (1 + ‖u‖*‖z‖)*(ρ+rr) - (1+ρ*rr)*(‖u‖+‖z‖) ≥ 0 := by
      have e1 : (1 + ‖u‖*‖z‖)*(ρ+rr) - (1+ρ*rr)*(‖u‖+‖z‖)
          - ((1 + rr*‖z‖)*(ρ+rr) - (1+ρ*rr)*(rr+‖z‖))
          = (‖u‖ - rr) * (‖z‖*(ρ+rr) - (1+ρ*rr)) := by ring
      have e2 : (1 + rr*‖z‖)*(ρ+rr) - (1+ρ*rr)*(rr+‖z‖)
          - ((1 + rr*ρ)*(ρ+rr) - (1+ρ*rr)*(rr+ρ))
          = (‖z‖ - ρ) * (rr*(ρ+rr) - (1+ρ*rr)) := by ring
      have e3 : (1 + rr*ρ)*(ρ+rr) - (1+ρ*rr)*(rr+ρ) = 0 := by ring
      have hA : (‖u‖ - rr) * (‖z‖*(ρ+rr) - (1+ρ*rr)) ≥ 0 := by
        apply mul_nonneg_of_nonpos_of_nonpos
        · linarith
        · nlinarith
      have hB : (‖z‖ - ρ) * (rr*(ρ+rr) - (1+ρ*rr)) ≥ 0 := by
        apply mul_nonneg_of_nonpos_of_nonpos
        · linarith
        · nlinarith
      linarith [e1, e2, e3, hA, hB]
    linarith
  have hsq : (c * ‖z-u‖)^2 ≤ ‖(1:ℂ) - (starRingEnd ℂ) u * z‖^2 := by
    rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_sub,
      Complex.normSq_one, Complex.normSq_mul, Complex.normSq_conj]
    have hU : Complex.normSq u = ‖u‖^2 := Complex.normSq_eq_norm_sq u
    have hZ : Complex.normSq z = ‖z‖^2 := Complex.normSq_eq_norm_sq z
    rw [hU, hZ]
    have hconj : (starRingEnd ℂ) ((starRingEnd ℂ) u * z) = u * (starRingEnd ℂ) z := by
      simp [map_mul]
    rw [hconj]
    have hPeq : (u * (starRingEnd ℂ) z).re = (z * (starRingEnd ℂ) u).re := by
      have h2 : u * (starRingEnd ℂ) z = (starRingEnd ℂ) ((starRingEnd ℂ) u * z) := by
        simp [map_mul]
      rw [h2]
      simp [Complex.conj_re, mul_comm]
    simp only [one_mul]
    rw [hPeq]
    have hQle : (z * (starRingEnd ℂ) u).re ≤ ‖u‖ * ‖z‖ := by
      calc (z * (starRingEnd ℂ) u).re ≤ ‖z * (starRingEnd ℂ) u‖ := Complex.re_le_norm _
        _ = ‖z‖ * ‖u‖ := by rw [norm_mul, norm_conj]
        _ = ‖u‖ * ‖z‖ := by ring
    have hQge : -(‖u‖ * ‖z‖) ≤ (z * (starRingEnd ℂ) u).re := by
      have h := Complex.re_le_norm (-(z * (starRingEnd ℂ) u))
      rw [Complex.neg_re, norm_neg, norm_mul, norm_conj] at h
      have h2 : ‖z‖ * ‖u‖ = ‖u‖ * ‖z‖ := by ring
      rw [h2] at h
      linarith [h]
    have key : 1 + ‖u‖^2*‖z‖^2 - 2*(z * (starRingEnd ℂ) u).re
          - c^2*(‖u‖^2 + ‖z‖^2 - 2*(z * (starRingEnd ℂ) u).re)
        = ((1+‖u‖*‖z‖)^2 - c^2*(‖u‖+‖z‖)^2)
          - 2*(1-c^2)*((z * (starRingEnd ℂ) u).re + ‖u‖*‖z‖) := by ring
    have h1nn : 0 ≤ c*(‖u‖+‖z‖) := by positivity
    have h2nn : 0 ≤ 1 + ‖u‖*‖z‖ := by positivity
    have hcsq : c^2 * (‖u‖+‖z‖)^2 ≤ (1+‖u‖*‖z‖)^2 := by
      have : (c*(‖u‖+‖z‖))^2 ≤ (1+‖u‖*‖z‖)^2 := by nlinarith [hcore, h1nn, h2nn]
      nlinarith [this]
    have hQab : 0 ≤ (z * (starRingEnd ℂ) u).re + ‖u‖*‖z‖ := by linarith
    have hB : 2*(1-c^2)*((z * (starRingEnd ℂ) u).re + ‖u‖*‖z‖) ≤ 0 := by
      have h1 : 1 - c^2 ≤ 0 := by nlinarith [hcge1]
      nlinarith [h1, hQab]
    linarith [key, hcsq, hB]
  calc c * ‖z-u‖ = |c * ‖z-u‖| := by rw [abs_of_nonneg (by positivity)]
    _ = Real.sqrt ((c*‖z-u‖)^2) := by rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt (‖(1:ℂ) - (starRingEnd ℂ) u * z‖^2) := Real.sqrt_le_sqrt hsq
    _ = ‖(1:ℂ) - (starRingEnd ℂ) u * z‖ := Real.sqrt_sq (norm_nonneg _)

end Commons.Analysis.Complex

namespace Commons.Analysis.Complex

open Complex Filter Function Metric MeromorphicOn Set Topology
open scoped Topology BigOperators

theorem riesz_cartan_disk_nonzero (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G (Metric.closedBall 0 1))
    {δ H : ℝ} (hδ0 : 0 < δ) (hδ3 : δ < 1 / 3) (hH0 : 0 < H) (hH1 : H ≤ 1)
    {m M : ℝ} (hm : ∃ z : ℂ, ‖z‖ ≤ 1 - 3 * δ ∧ G z ≠ 0 ∧ m ≤ Real.log ‖G z‖)
    (hM1 : 1 ≤ M) (hMb : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖G z‖ ≤ M) :
    ∃ (s : Finset ℂ) (r : ℂ → ℝ), (∀ z ∈ s, 0 < r z) ∧ (∑ z ∈ s, r z ≤ 5 * H) ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 - 2 * δ → (∀ w ∈ s, r w ≤ ‖z - w‖) →
        m - (Real.log M - m) *
          (2 * δ⁻¹ ^ 3 * Real.log (2 / δ) + δ⁻¹ ^ 2 * Real.log (2 * Real.exp 1 / H))
          ≤ Real.log ‖G z‖ := by
  obtain ⟨z₀, hz₀le, hGz₀, hmz₀⟩ := hm
  have hδ1 : δ < 1 := by linarith
  set ρ : ℝ := 1 - 3 * δ with hρdef
  set r₁ : ℝ := 1 - 2 * δ with hr₁def
  set rr : ℝ := 1 - δ with hrrdef
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  have hρ_lt_r₁ : ρ < r₁ := by rw [hρdef, hr₁def]; linarith
  have hr₁_lt_rr : r₁ < rr := by rw [hr₁def, hrrdef]; linarith
  have hrr_lt_one : rr < 1 := by rw [hrrdef]; linarith
  have hrr0 : 0 < rr := lt_of_lt_of_le hρ0 (le_trans hρ_lt_r₁.le hr₁_lt_rr.le)
  have hz₀_lt_rr : ‖z₀‖ < rr := lt_of_lt_of_le (lt_of_le_of_lt hz₀le hρ_lt_r₁) hr₁_lt_rr.le
  have hz₀_lt_one : ‖z₀‖ < 1 := lt_trans hz₀_lt_rr hrr_lt_one
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hlogM : m ≤ Real.log M := by
    have h2 : ‖G z₀‖ ≤ M := hMb z₀ hz₀_lt_one.le
    have h3 : 0 < ‖G z₀‖ := norm_pos_iff.mpr hGz₀
    exact le_trans hmz₀ (Real.log_le_log h3 h2)
  set A : ℝ := Real.log M - m with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; linarith
  -- factorization on a ball slightly larger than the closed unit disk
  have hopen : IsOpen {z : ℂ | AnalyticAt ℂ G z} := isOpen_setOf_analyticAt G
  have hsubW : Metric.closedBall (0:ℂ) 1 ⊆ {z : ℂ | AnalyticAt ℂ G z} := fun z hz => hG z hz
  obtain ⟨d₁, hd₁, hthick⟩ :=
    (isCompact_closedBall (0:ℂ) 1).exists_thickening_subset_open hopen hsubW
  have hball_sub : Metric.ball (0:ℂ) (1 + d₁) ⊆ Metric.thickening d₁ (Metric.closedBall (0:ℂ) 1) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [Metric.mem_thickening_iff]
    by_cases h : ‖z‖ ≤ 1
    · exact ⟨z, by simpa [Metric.mem_closedBall, dist_eq_norm] using h, by rw [dist_self]; exact hd₁⟩
    · push_neg at h
      have hz0 : (0:ℝ) < ‖z‖ := lt_of_lt_of_le zero_lt_one h.le
      refine ⟨((‖z‖⁻¹ : ℝ) : ℂ) * z, ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_mul_cancel₀ (ne_of_gt hz0)]
      · rw [dist_eq_norm]
        rw [show z - ((‖z‖⁻¹ : ℝ) : ℂ) * z = ((1 - ‖z‖⁻¹ : ℝ) : ℂ) * z by push_cast; ring]
        rw [norm_mul, Complex.norm_real]
        have h1 : (0:ℝ) ≤ 1 - ‖z‖⁻¹ := by
          have : ‖z‖⁻¹ ≤ 1 := by rw [inv_le_one₀ hz0]; linarith
          linarith
        rw [Real.norm_of_nonneg h1, sub_mul, one_mul, inv_mul_cancel₀ (ne_of_gt hz0)]
        linarith
  have hGanU : AnalyticOnNhd ℂ G (Metric.ball (0:ℂ) (1 + d₁)) := fun z hz => hthick (hball_sub hz)
  have hd₁' : 0 < d₁ := hd₁
  have hmer : MeromorphicOn G (Metric.ball (0:ℂ) (1 + d₁)) := hGanU.meromorphicOn
  have hz₀U : z₀ ∈ Metric.ball (0:ℂ) (1 + d₁) := by
    rw [Metric.mem_ball, dist_zero_right]; linarith [hd₁]
  have horder : ∀ z ∈ Metric.ball (0:ℂ) (1 + d₁), meromorphicOrderAt G z ≠ ⊤ := by
    have hconn : IsConnected (Metric.ball (0:ℂ) (1 + d₁)) := Metric.isConnected_ball (by linarith [hd₁])
    have hex : ∃ u : Metric.ball (0:ℂ) (1 + d₁), meromorphicOrderAt G (u:ℂ) ≠ ⊤ :=
      ⟨⟨z₀, hz₀U⟩, meromorphicOrderAt_ne_top_of_analytic_ne_zero (hGanU z₀ hz₀U) hGz₀⟩
    have hall := (MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall hmer hconn).mp hex
    intro z hz
    exact hall ⟨z, hz⟩
  have hdivfin : (MeromorphicOn.divisor G (Metric.closedBall (0:ℂ) 1)).support.Finite :=
    MeromorphicOn.divisor_support_finite_of_subset hG.meromorphicOn
      (isCompact_closedBall (0:ℂ) 1) (subset_rfl)
  obtain ⟨g, hgan, hgnz, hgfac⟩ :=
    factor_subBall_divisor (U := Metric.ball (0:ℂ) (1 + d₁)) (V := Metric.closedBall (0:ℂ) 1)
      (fun z hz => by
        rw [Metric.mem_closedBall, dist_zero_right] at hz
        rw [Metric.mem_ball, dist_zero_right]
        linarith [hd₁]) hmer horder hGanU hdivfin
  set Du : ℂ → ℤ := fun u => MeromorphicOn.divisor G (Metric.closedBall (0:ℂ) 1) u with hDudef
  have hDufin : (Function.support Du).Finite := by
    have h : (Function.support Du) = (MeromorphicOn.divisor G (Metric.closedBall (0:ℂ) 1)).support := rfl
    rw [h]; exact hdivfin
  have hDunn : ∀ u : ℂ, 0 ≤ Du u := by
    intro u; rw [hDudef]
    exact AnalyticOnNhd.divisor_nonneg hG u
  have hDu0 : Du z₀ = 0 := by
    rw [hDudef]
    change (MeromorphicOn.divisor G (Metric.closedBall (0:ℂ) 1)) z₀ = 0
    rw [MeromorphicOn.divisor_apply hG.meromorphicOn (by
          rw [Metric.mem_closedBall, dist_zero_right]; exact hz₀_lt_one.le),
        meromorphicOrderAt_eq_zero_of_ne_zero (hG z₀ (by
          rw [Metric.mem_closedBall, dist_zero_right]; exact hz₀_lt_one.le)) hGz₀]
    rfl
  set S : Finset ℂ := hDufin.toFinset with hSdef
  have hSmem : ∀ u : ℂ, u ∈ S ↔ Du u ≠ 0 := by
    intro u; rw [hSdef, Set.Finite.mem_toFinset, Function.mem_support]
  have hSsub : ∀ u ∈ S, ‖u‖ ≤ 1 := by
    intro u hu
    rw [hSdef, Set.Finite.mem_toFinset] at hu
    rw [hDudef] at hu
    have := Function.locallyFinsuppWithin.supportWithinDomain _ hu
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  set P_all : Polynomial ℂ := ∏ u ∈ S, (Polynomial.X - Polynomial.C u) ^ (Du u).toNat with hPalldef
  have hPall_monic : P_all.Monic := by
    rw [hPalldef]
    exact Polynomial.monic_prod_of_monic _ _ (fun u _ => (Polynomial.monic_X_sub_C u).pow _)
  have hPall_eval : ∀ z : ℂ, P_all.eval z = ∏ u ∈ S, (z - u) ^ (Du u).toNat := by
    intro z
    rw [hPalldef, Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro u _
    rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hfinprod : ∀ z : ℂ, (∏ᶠ u : ℂ, (z - u) ^ (Du u : ℤ)) = P_all.eval z := by
    intro z
    rw [finprod_eq_prod_of_mulSupport_subset (f := fun u : ℂ => (z - u) ^ (Du u : ℤ)) (s := S)]
    · rw [hPall_eval]
      apply Finset.prod_congr rfl
      intro u hu
      rw [show (Du u : ℤ) = ((Du u).toNat : ℤ) from (Int.toNat_of_nonneg (hDunn u)).symm]
      exact zpow_natCast (z - u) ((Du u).toNat)
    · intro u hu
      rw [Finset.mem_coe, hSmem]
      intro hD0
      rw [Function.mem_mulSupport] at hu
      exact hu (by rw [hD0]; simp)
  have hballU : ∀ z ∈ Metric.ball (0:ℂ) 1, z ∈ Metric.ball (0:ℂ) (1 + d₁) := by
    intro z hz; rw [Metric.mem_ball, dist_zero_right] at hz ⊢; linarith [hd₁]
  have hGfacU : ∀ z ∈ Metric.ball (0:ℂ) (1 + d₁), G z = P_all.eval z * g z := by
    intro z hz
    rw [← hfinprod z, hgfac z hz]
  have hGfacP : ∀ z ∈ Metric.ball (0:ℂ) 1, G z = P_all.eval z * g z :=
    fun z hz => hGfacU z (hballU z hz)
  -- Q
  set Qpoly : Polynomial ℂ := ∏ u ∈ S, (1 - Polynomial.C ((starRingEnd ℂ) u) * Polynomial.X) ^ (Du u).toNat with hQdef
  have hQeval : ∀ z : ℂ, Qpoly.eval z = ∏ u ∈ S, (1 - (starRingEnd ℂ) u * z) ^ (Du u).toNat := by
    intro z
    rw [hQdef, Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro u _
    rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one]
  have hQne : ∀ z ∈ Metric.ball (0:ℂ) 1, Qpoly.eval z ≠ 0 := by
    intro z hz
    rw [hQeval]
    rw [Finset.prod_ne_zero_iff]
    intro u hu
    apply pow_ne_zero
    intro h0
    have h1 : (starRingEnd ℂ) u * z = 1 := by linear_combination -h0
    have h2 : ‖u‖ * ‖z‖ = 1 := by
      have := congrArg norm h1
      simpa [norm_mul, norm_conj, norm_one] using this
    have hu1 : ‖u‖ ≤ 1 := hSsub u hu
    have hz1 : ‖z‖ < 1 := by rwa [Metric.mem_ball, dist_zero_right] at hz
    nlinarith [norm_nonneg u, norm_nonneg z]
  -- ============ the maximum-modulus bound for Phi = g*Q ============
  have hz₀ball : z₀ ∈ Metric.ball (0:ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]; exact hz₀_lt_one
  have hroot_mem : ∀ z : ℂ, P_all.eval z = 0 → z ∈ S := by
    intro z hz
    rw [hPall_eval] at hz
    rw [Finset.prod_eq_zero_iff] at hz
    obtain ⟨u, hu, hu0⟩ := hz
    have hDun : (Du u).toNat ≠ 0 := by
      intro h0
      have hz' : Du u = 0 := le_antisymm (Int.toNat_eq_zero.mp h0) (hDunn u)
      exact (hSmem u).mp hu hz'
    rw [sub_eq_zero.mp ((pow_eq_zero_iff hDun).mp hu0)]
    exact hu
  have hQzero_of_Pzero : ∀ z : ℂ, ‖z‖ = 1 → P_all.eval z = 0 → Qpoly.eval z = 0 := by
    intro z hz hP
    have hzS : z ∈ S := hroot_mem z hP
    rw [hQeval]
    rw [Finset.prod_eq_zero_iff]
    refine ⟨z, hzS, ?_⟩
    have hDuz : (Du z).toNat ≠ 0 := by
      intro h0
      exact (hSmem z).1 hzS (le_antisymm (Int.toNat_eq_zero.mp h0) (hDunn z))
    rw [show (1:ℂ) - (starRingEnd ℂ) z * z = 0 by
      have h1 : (starRingEnd ℂ) z * z = ((‖z‖^2 : ℝ) : ℂ) := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      rw [h1, hz]; norm_num]
    exact zero_pow hDuz
  have hQnorm_sphere : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖Qpoly.eval ζ‖ = ‖P_all.eval ζ‖ := by
    intro ζ hζ
    rw [hQeval, hPall_eval, norm_prod, norm_prod]
    apply Finset.prod_congr rfl
    intro u _
    rw [norm_pow, norm_pow]
    congr 1
    have hkey : (1 : ℂ) - u * (starRingEnd ℂ) ζ = (starRingEnd ℂ) ζ * (ζ - u) := by
      have h : (starRingEnd ℂ) ζ * ζ = 1 := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hζ]; norm_num
      linear_combination -h
    rw [show (1:ℂ) - (starRingEnd ℂ) u * ζ = (starRingEnd ℂ) ((1:ℂ) - u * (starRingEnd ℂ) ζ) by
      simp [map_mul]]
    rw [norm_conj, hkey, norm_mul, norm_conj, hζ, one_mul]
  have hPhi_an : AnalyticOnNhd ℂ (fun z => g z * Qpoly.eval z) (Metric.ball (0:ℂ) (1 + d₁)) :=
    hgan.mul (fun z _ => (Polynomial.differentiable Qpoly).analyticAt z)
  have hPhi_bound : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖g z * Qpoly.eval z‖ ≤ M := by
    intro z hz
    have hmono : Metric.ball (0:ℂ) 1 ⊆ Metric.ball (0:ℂ) (1 + d₁) :=
      Metric.ball_subset_ball (by linarith [hd₁])
    have hdiff : DiffContOnCl ℂ (fun z => g z * Qpoly.eval z) (Metric.ball (0:ℂ) 1) :=
      DiffContOnCl.mk (hPhi_an.differentiableOn.mono hmono)
        (hPhi_an.continuousOn.mono (by
          rw [closure_ball (0:ℂ) one_ne_zero]
          exact Metric.closedBall_subset_ball (by linarith [hd₁])))
    have hfront : ∀ ζ : ℂ, ζ ∈ frontier (Metric.ball (0:ℂ) 1) → ‖g ζ * Qpoly.eval ζ‖ ≤ M := by
      intro ζ hζ
      rw [frontier_ball (0:ℂ) one_ne_zero, Metric.mem_sphere, dist_zero_right] at hζ
      by_cases hP : P_all.eval ζ = 0
      · rw [hQzero_of_Pzero ζ hζ hP, mul_zero, norm_zero]
        exact hMpos.le
      · have hζb : ζ ∈ Metric.ball (0:ℂ) (1 + d₁) := by
          rw [Metric.mem_ball, dist_zero_right, hζ]; linarith [hd₁]
        have hgζ : g ζ = G ζ / P_all.eval ζ := by
          have hfac := hGfacU ζ hζb
          rw [hfac, mul_div_cancel_left₀ _ hP]
        calc ‖g ζ * Qpoly.eval ζ‖ = ‖g ζ‖ * ‖Qpoly.eval ζ‖ := norm_mul _ _
          _ = (‖G ζ‖ / ‖P_all.eval ζ‖) * ‖P_all.eval ζ‖ := by
              rw [hgζ, norm_div, hQnorm_sphere ζ hζ]
          _ = ‖G ζ‖ := div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hP)
          _ ≤ M := hMb ζ hζ.le
    have hzcl : z ∈ closure (Metric.ball (0:ℂ) 1) := by
      rw [closure_ball (0:ℂ) one_ne_zero, Metric.mem_closedBall, dist_zero_right]; exact hz
    exact Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdiff hfront hzcl
  -- ============ the mass bound ============
  have hPz₀ : P_all.eval z₀ ≠ 0 := fun h => (hSmem z₀).mp (hroot_mem z₀ h) hDu0
  have hL1 : δ^2 ≤ Real.log ((1 + ρ*rr)/(ρ+rr)) := by
    have hnum : 0 < 1 + ρ*rr := by positivity
    have hden : 0 < ρ + rr := by linarith
    have h2 := Real.one_sub_inv_le_log_of_pos (show 0 < (1 + ρ*rr)/(ρ+rr) by positivity)
    rw [inv_div] at h2
    have h3 : (1:ℝ) - (ρ+rr)/(1+ρ*rr) = 3*δ^2/(1+ρ*rr) := by
      rw [one_sub_div (ne_of_gt hnum)]
      rw [show (1 + ρ*rr) - (ρ+rr) = 3*δ^2 by rw [hρdef, hrrdef]; ring]
    rw [h3] at h2
    have h4 : δ^2 ≤ 3*δ^2/(1+ρ*rr) := by
      rw [le_div_iff₀ hnum]
      have h5 : 1 + ρ*rr ≤ 3 := by rw [hρdef, hrrdef]; nlinarith [hδ0, hδ3, sq_nonneg δ]
      have := mul_le_mul_of_nonneg_left h5 (sq_nonneg δ)
      linarith
    linarith
  set Srr : Finset ℂ := S.filter (fun u => ‖u‖ < rr) with hSrrdef
  set Nr : ℕ := ∑ u ∈ Srr, (Du u).toNat with hNrdef
  have hNr : Nr = ∑ u ∈ S, if ‖u‖ < rr then (Du u).toNat else 0 := by
    rw [hNrdef, hSrrdef, Finset.sum_filter]
  have hone : ∀ u ∈ S, (1 : ℂ) - (starRingEnd ℂ) u * z₀ ≠ 0 := by
    intro u hu h0
    have h1 : (starRingEnd ℂ) u * z₀ = 1 := by linear_combination -h0
    have h2 : ‖u‖ * ‖z₀‖ = 1 := by
      have := congrArg norm h1
      simpa [norm_mul, norm_conj, norm_one] using this
    have hu1 : ‖u‖ ≤ 1 := hSsub u hu
    nlinarith [norm_nonneg u, norm_nonneg z₀, hz₀_lt_one]
  have hzu_ne : ∀ u ∈ S, z₀ - u ≠ 0 := by
    intro u hu
    exact sub_ne_zero.mpr (fun h => (hSmem u).mp hu (by rw [← h]; exact hDu0))
  have hmass : (Nr : ℝ) * Real.log ((1 + ρ*rr)/(ρ+rr)) ≤ A := by
    have hlogG : Real.log ‖G z₀‖ = Real.log ‖g z₀‖ + Real.log ‖P_all.eval z₀‖ := by
      rw [hGfacP z₀ hz₀ball, norm_mul, mul_comm,
        Real.log_mul (norm_ne_zero_iff.mpr (hgnz z₀ (Metric.ball_subset_closedBall hz₀ball)))
          (norm_ne_zero_iff.mpr hPz₀)]
    have hlogQ : Real.log ‖Qpoly.eval z₀‖
        = ∑ u ∈ S, ((Du u).toNat : ℝ) * Real.log ‖1 - (starRingEnd ℂ) u * z₀‖ := by
      rw [hQeval, norm_prod, Real.log_prod]
      · apply Finset.sum_congr rfl
        intro u _
        rw [norm_pow, Real.log_pow]
      · intro u hu
        exact norm_ne_zero_iff.mpr (pow_ne_zero _ (hone u hu))
    have hlogP : Real.log ‖P_all.eval z₀‖
        = ∑ u ∈ S, ((Du u).toNat : ℝ) * Real.log ‖z₀ - u‖ := by
      rw [hPall_eval, norm_prod, Real.log_prod]
      · apply Finset.sum_congr rfl
        intro u _
        rw [norm_pow, Real.log_pow]
      · intro u hu
        exact norm_ne_zero_iff.mpr (pow_ne_zero _ (hzu_ne u hu))
    have hbound : Real.log ‖g z₀ * Qpoly.eval z₀‖ ≤ Real.log M :=
      Real.log_le_log (norm_pos_iff.mpr (mul_ne_zero
        (hgnz z₀ (Metric.ball_subset_closedBall hz₀ball)) (hQne z₀ hz₀ball)))
        (hPhi_bound z₀ hz₀_lt_one.le)
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hgnz z₀ (Metric.ball_subset_closedBall hz₀ball)))
      (norm_ne_zero_iff.mpr (hQne z₀ hz₀ball))] at hbound
    have hkey : ∑ u ∈ S, ((Du u).toNat : ℝ) * Real.log (‖1 - (starRingEnd ℂ) u * z₀‖/‖z₀-u‖)
        ≤ Real.log M - Real.log ‖G z₀‖ := by
      have hsplit : ∑ u ∈ S, ((Du u).toNat : ℝ) * Real.log (‖1 - (starRingEnd ℂ) u * z₀‖/‖z₀-u‖)
          = ∑ u ∈ S, ((Du u).toNat : ℝ) * Real.log ‖1 - (starRingEnd ℂ) u * z₀‖
            - ∑ u ∈ S, ((Du u).toNat : ℝ) * Real.log ‖z₀-u‖ := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro u hu
        have hpos : 0 < ‖z₀-u‖ := norm_pos_iff.mpr (hzu_ne u hu)
        rw [Real.log_div (by rw [norm_ne_zero_iff]; exact hone u hu) hpos.ne']
        ring
      rw [hsplit, ← hlogQ, ← hlogP]
      linarith [hbound, hlogG]
    have hpoint : ∀ u ∈ S, ((Du u).toNat : ℝ) * (if ‖u‖ < rr then Real.log ((1+ρ*rr)/(ρ+rr)) else 0)
        ≤ ((Du u).toNat : ℝ) * Real.log (‖1 - (starRingEnd ℂ) u * z₀‖/‖z₀-u‖) := by
      intro u hu
      have hpos : 0 < ‖z₀-u‖ := norm_pos_iff.mpr (hzu_ne u hu)
      by_cases hc : ‖u‖ < rr
      · rw [if_pos hc]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hpf := riesz_cartan_perfactor rr ρ hρ0 (lt_trans hρ_lt_r₁ hr₁_lt_rr) hrr_lt_one u z₀ hc.le (by
          rw [hρdef]; exact hz₀le)
        have h2 := Real.log_le_log (by positivity) hpf
        rw [Real.log_mul (by positivity) hpos.ne'] at h2
        have h3 : Real.log ((1+ρ*rr)/(ρ+rr))
            ≤ Real.log (‖1 - (starRingEnd ℂ) u * z₀‖/‖z₀-u‖) := by
          rw [Real.log_div (by rw [norm_ne_zero_iff]; exact hone u hu) hpos.ne']
          linarith [h2]
        exact h3
      · rw [if_neg hc, mul_zero]
        apply mul_nonneg (by positivity)
        apply Real.log_nonneg
        rw [one_le_div hpos]
        have hbl : ‖z₀ - u‖ ≤ ‖1 - (starRingEnd ℂ) u * z₀‖ := by
          have hid : ‖1 - (starRingEnd ℂ) u * z₀‖^2 - ‖z₀ - u‖^2
              = (1 - ‖u‖^2)*(1 - ‖z₀‖^2) := by
            rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_sub,
              Complex.normSq_one, Complex.normSq_mul, Complex.normSq_conj]
            have hU : Complex.normSq u = ‖u‖^2 := Complex.normSq_eq_norm_sq u
            have hZ : Complex.normSq z₀ = ‖z₀‖^2 := Complex.normSq_eq_norm_sq z₀
            rw [hU, hZ]
            have hconj : (starRingEnd ℂ) ((starRingEnd ℂ) u * z₀) = u * (starRingEnd ℂ) z₀ := by
              simp [map_mul]
            rw [hconj]
            have hPeq : (u * (starRingEnd ℂ) z₀).re = (z₀ * (starRingEnd ℂ) u).re := by
              have h2 : u * (starRingEnd ℂ) z₀ = (starRingEnd ℂ) ((starRingEnd ℂ) u * z₀) := by
                simp [map_mul]
              rw [h2]; simp [Complex.conj_re, mul_comm]
            simp only [one_mul]
            rw [hPeq]; ring
          have hu1 : ‖u‖ ≤ 1 := hSsub u hu
          have hnn : 0 ≤ (1 - ‖u‖^2)*(1 - ‖z₀‖^2) := by
            have h1 : ‖u‖^2 ≤ 1 := pow_le_one₀ (norm_nonneg u) hu1
            have h2 : ‖z₀‖^2 ≤ 1 := pow_le_one₀ (norm_nonneg z₀) hz₀_lt_one.le
            nlinarith
          have hsq : ‖z₀ - u‖^2 ≤ ‖1 - (starRingEnd ℂ) u * z₀‖^2 := by linarith [hid, hnn]
          nlinarith [hsq, norm_nonneg (z₀-u), norm_nonneg (1 - (starRingEnd ℂ) u * z₀)]
        exact hbl
    calc (Nr : ℝ) * Real.log ((1 + ρ*rr)/(ρ+rr))
        = ∑ u ∈ S, ((Du u).toNat : ℝ) * (if ‖u‖ < rr then Real.log ((1+ρ*rr)/(ρ+rr)) else 0) := by
          rw [hNr]
          push_cast
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro u hu
          by_cases hc : ‖u‖ < rr <;> simp [hc]
      _ ≤ ∑ u ∈ S, ((Du u).toNat : ℝ) * Real.log (‖1 - (starRingEnd ℂ) u * z₀‖/‖z₀-u‖) :=
          Finset.sum_le_sum hpoint
      _ ≤ Real.log M - Real.log ‖G z₀‖ := hkey
      _ ≤ A := by rw [hAdef]; linarith [hmz₀]
  -- ============ P_rr, P_out, Qrr, Phi_rr ============
  set Sout : Finset ℂ := S.filter (fun u => ¬ ‖u‖ < rr) with hSoutdef
  set P_rr : Polynomial ℂ := ∏ u ∈ Srr, (Polynomial.X - Polynomial.C u) ^ (Du u).toNat with hPrrdef
  set P_out : Polynomial ℂ := ∏ u ∈ Sout, (Polynomial.X - Polynomial.C u) ^ (Du u).toNat with hPoutdef
  have hPall_split : P_all = P_rr * P_out := by
    rw [hPalldef, hPrrdef, hPoutdef, hSrrdef, hSoutdef]
    exact (Finset.prod_filter_mul_prod_filter_not S (fun u => ‖u‖ < rr)
      (fun u => (Polynomial.X - Polynomial.C u) ^ (Du u).toNat)).symm
  have hPall_eval' : ∀ z : ℂ, P_all.eval z = P_rr.eval z * P_out.eval z := by
    intro z
    rw [hPall_split, Polynomial.eval_mul]
  have hPrr_monic : P_rr.Monic := by
    rw [hPrrdef]
    exact Polynomial.monic_prod_of_monic _ _ (fun u _ => (Polynomial.monic_X_sub_C u).pow _)
  have hPrr_eval : ∀ z : ℂ, P_rr.eval z = ∏ u ∈ Srr, (z - u) ^ (Du u).toNat := by
    intro z
    rw [hPrrdef, Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro u _
    rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hPrr_root : ∀ z : ℂ, P_rr.eval z = 0 → ‖z‖ ≤ 1 := by
    intro z hz
    refine hSsub z (hroot_mem z ?_)
    rw [hPall_eval' z, hz, zero_mul]
  have hSrr_lt : ∀ u ∈ Srr, ‖u‖ < rr := by
    intro u hu
    rw [hSrrdef] at hu
    exact (Finset.mem_filter.mp hu).2
  have hSrrS : ∀ u ∈ Srr, u ∈ S := by
    intro u hu
    rw [hSrrdef] at hu
    exact (Finset.mem_filter.mp hu).1
  set Qrr : Polynomial ℂ := ∏ u ∈ Srr,
      (Polynomial.C ((rr^2 : ℝ) : ℂ) - Polynomial.C ((starRingEnd ℂ) u) * Polynomial.X) ^ (Du u).toNat
    with hQrrdef
  have hQrr_eval : ∀ z : ℂ, Qrr.eval z = ∏ u ∈ Srr, (rr^2 - (starRingEnd ℂ) u * z) ^ (Du u).toNat := by
    intro z
    rw [hQrrdef, Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro u _
    rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_C]
    congr 1
    push_cast
    ring
  have hQrr_norm : ∀ ζ : ℂ, ‖ζ‖ = rr → ‖Qrr.eval ζ‖ = rr^Nr * ‖P_rr.eval ζ‖ := by
    intro ζ hζ
    rw [hQrr_eval, hPrr_eval, norm_prod, norm_prod]
    have hterm : ∀ u ∈ Srr, ‖(rr^2 - (starRingEnd ℂ) u * ζ) ^ (Du u).toNat‖
        = rr ^ (Du u).toNat * ‖(ζ - u) ^ (Du u).toNat‖ := by
      intro u hu
      rw [norm_pow, norm_pow, ← mul_pow]
      have hu1 : ‖u‖ < rr := hSrr_lt u hu
      have hbf := (Commons.Analysis.Complex.Blaschke.blaschke_factor_norm (r := rr) hrr0
        (u := u) (z := ζ) hu1).2.2 hζ
      have hnorm : ‖(rr : ℂ) * (ζ - u)‖ = ‖(rr : ℂ)^2 - (starRingEnd ℂ) u * ζ‖ := by
        rw [norm_div] at hbf
        have h0 : ‖(rr : ℂ)^2 - (starRingEnd ℂ) u * ζ‖ ≠ 0 := by
          intro h
          rw [h] at hbf
          simp at hbf
        rw [div_eq_iff h0, one_mul] at hbf
        exact hbf
      rw [← hnorm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrr0]
    rw [Finset.prod_congr rfl hterm]
    rw [Finset.prod_mul_distrib]
    rw [show (∏ u ∈ Srr, rr ^ (Du u).toNat) = rr ^ Nr by
      rw [hNrdef]
      exact Finset.prod_pow_eq_pow_sum _ _ _]

  -- ============ Phi_rr ============
  have hSout_ge : ∀ u ∈ Sout, rr ≤ ‖u‖ := by
    intro u hu
    rw [hSoutdef] at hu
    have := (Finset.mem_filter.mp hu).2
    push Not at this
    exact this
  have hSoutS : ∀ u ∈ Sout, u ∈ S := by
    intro u hu
    rw [hSoutdef] at hu
    exact (Finset.mem_filter.mp hu).1
  set Phi_rr : ℂ → ℂ :=
    fun w => (P_out.eval w * g w) * Qrr.eval w / ((rr^Nr : ℝ) : ℂ) with hPhirrdef
  have hPhi_rr_an : AnalyticOnNhd ℂ Phi_rr (Metric.ball (0:ℂ) (1 + d₁)) := by
    rw [hPhirrdef]
    have h1 : AnalyticOnNhd ℂ (fun w => P_out.eval w) (Metric.ball (0:ℂ) (1 + d₁)) :=
      fun w _ => (Polynomial.differentiable P_out).analyticAt w
    have h2 : AnalyticOnNhd ℂ (fun w => Qrr.eval w) (Metric.ball (0:ℂ) (1 + d₁)) :=
      fun w _ => (Polynomial.differentiable Qrr).analyticAt w
    exact AnalyticOnNhd.div ((h1.mul hgan).mul h2) (analyticOnNhd_const) (fun x _ => by
      rw [Complex.ofReal_ne_zero]; exact ne_of_gt (by positivity))
  have hPrr_zero_mem : ∀ z : ℂ, P_rr.eval z = 0 → z ∈ Srr := by
    intro z hz
    rw [hPrr_eval] at hz
    rw [Finset.prod_eq_zero_iff] at hz
    obtain ⟨u, hu, hu0⟩ := hz
    have hDun : (Du u).toNat ≠ 0 := by
      intro h0
      exact (hSmem u).mp (hSrrS u hu) (le_antisymm (Int.toNat_eq_zero.mp h0) (hDunn u))
    rw [sub_eq_zero.mp ((pow_eq_zero_iff hDun).mp hu0)]
    exact hu
  have hQrr_zero_of_Prr_zero : ∀ z : ℂ, ‖z‖ = rr → P_rr.eval z = 0 → Qrr.eval z = 0 := by
    intro z hz hP
    have hzSrr : z ∈ Srr := hPrr_zero_mem z hP
    rw [hQrr_eval]
    rw [Finset.prod_eq_zero_iff]
    refine ⟨z, hzSrr, ?_⟩
    have hDuz : (Du z).toNat ≠ 0 := by
      intro h0
      exact (hSmem z).mp (hSrrS z hzSrr) (le_antisymm (Int.toNat_eq_zero.mp h0) (hDunn z))
    rw [show rr^2 - (starRingEnd ℂ) z * z = 0 by
      have h1 : (starRingEnd ℂ) z * z = ((‖z‖^2 : ℝ) : ℂ) := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      rw [h1, hz]; push_cast; ring]
    exact zero_pow hDuz
  have hg_on_sphere_rr : ∀ ζ : ℂ, ‖ζ‖ = rr → P_all.eval ζ ≠ 0 → g ζ = G ζ / P_all.eval ζ := by
    intro ζ hζ hPζ
    have hζb : ζ ∈ Metric.ball (0:ℂ) (1 + d₁) := by
      rw [Metric.mem_ball, dist_zero_right, hζ]; linarith [hd₁]
    have hfac := hGfacU ζ hζb
    rw [hfac, mul_div_cancel_left₀ _ hPζ]
  have hPhi_rr_bound : ∀ z : ℂ, ‖z‖ ≤ rr → ‖Phi_rr z‖ ≤ M := by
    intro z hz
    have hmono : Metric.ball (0:ℂ) rr ⊆ Metric.ball (0:ℂ) (1 + d₁) :=
      Metric.ball_subset_ball (by linarith [hd₁, hrr_lt_one])
    have hdiff : DiffContOnCl ℂ Phi_rr (Metric.ball (0:ℂ) rr) :=
      DiffContOnCl.mk (hPhi_rr_an.differentiableOn.mono hmono)
        (hPhi_rr_an.continuousOn.mono (by
          rw [closure_ball (0:ℂ) hrr0.ne']
          exact Metric.closedBall_subset_ball (by linarith [hd₁, hrr_lt_one])))
    have hfront : ∀ ζ : ℂ, ζ ∈ frontier (Metric.ball (0:ℂ) rr) → ‖Phi_rr ζ‖ ≤ M := by
      intro ζ hζ
      rw [frontier_ball (0:ℂ) hrr0.ne', Metric.mem_sphere, dist_zero_right] at hζ
      by_cases hPallz : P_all.eval ζ = 0
      · rcases eq_or_ne (P_out.eval ζ) 0 with hPo | hPo
        · rw [hPhirrdef]
          simp only [hPo, zero_mul, zero_div, norm_zero]
          exact hMpos.le
        · have hPr : P_rr.eval ζ = 0 := by
            have h := hPallz
            rw [hPall_eval' ζ] at h
            rcases mul_eq_zero.mp h with h1 | h1
            · exact h1
            · exact absurd h1 hPo
          have hQ := hQrr_zero_of_Prr_zero ζ hζ hPr
          rw [hPhirrdef]
          simp only [hQ, mul_zero, zero_div, norm_zero]
          exact hMpos.le
      · have hPrrζ : P_rr.eval ζ ≠ 0 := by
          intro h0
          exact hPallz (by rw [hPall_eval' ζ, h0, zero_mul])
        have hPoutζ : P_out.eval ζ ≠ 0 := by
          intro h0
          exact hPallz (by rw [hPall_eval' ζ, h0, mul_zero])
        have hval : ‖Phi_rr ζ‖ = ‖G ζ‖ := by
          rw [hPhirrdef, norm_div, norm_mul, norm_mul, hg_on_sphere_rr ζ hζ hPallz, norm_div,
            hQrr_norm ζ hζ, hPall_eval' ζ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by positivity : (0:ℝ) < rr^Nr)]
          rw [div_eq_iff (by positivity : ((rr^Nr : ℝ)) ≠ 0)]
          field_simp
        rw [hval]; exact hMb ζ (by rw [hζ]; exact hrr_lt_one.le)
    have hzcl : z ∈ closure (Metric.ball (0:ℂ) rr) := by
      rw [closure_ball (0:ℂ) hrr0.ne', Metric.mem_closedBall, dist_zero_right]; exact hz
    exact Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdiff hfront hzcl

  -- ============ the Harnack bound on Utilde ============
  set R' : ℝ := (rr + r₁)/2 with hR'def
  have hR'pos : 0 < R' := by rw [hR'def]; linarith
  have hR'lt : R' < rr := by rw [hR'def]; linarith
  have hR'gt : r₁ < R' := by rw [hR'def]; linarith
  have hPhi_rr_ne : ∀ w : ℂ, ‖w‖ < rr → Phi_rr w ≠ 0 := by
    intro w hw
    rw [hPhirrdef]
    apply div_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · rw [hPoutdef, Polynomial.eval_prod]
          rw [Finset.prod_ne_zero_iff]
          intro u hu
          simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
          apply pow_ne_zero
          intro h0
          rw [sub_eq_zero.mp h0] at hw
          exact absurd hw (not_lt.mpr (hSout_ge u hu))
        · exact hgnz w (Metric.ball_subset_closedBall (by
            rw [Metric.mem_ball, dist_zero_right]
            exact lt_trans hw hrr_lt_one))
      · rw [hQrr_eval]
        rw [Finset.prod_ne_zero_iff]
        intro u hu
        apply pow_ne_zero
        intro h0
        have h1 : (starRingEnd ℂ) u * w = ((rr:ℂ))^2 := (sub_eq_zero.mp h0).symm
        have h2 : ‖u‖ * ‖w‖ = rr^2 := by
          have h1' := congrArg norm h1
          rw [norm_mul, norm_conj,
            show ‖((rr:ℂ))^2‖ = rr^2 by
              rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrr0]] at h1'
          exact h1'
        have hu1 : ‖u‖ < rr := hSrr_lt u hu
        have h3 : ‖u‖ * ‖w‖ < rr * rr := by nlinarith [hu1, hw, norm_nonneg u, norm_nonneg w]
        rw [h2] at h3
        nlinarith [h3]
    · rw [Complex.ofReal_ne_zero]; exact ne_of_gt (by positivity)
  have hPhi_rr_an_ball : ∀ w : ℂ, ‖w‖ < rr → AnalyticAt ℂ Phi_rr w := by
    intro w hw
    exact hPhi_rr_an w (by rw [Metric.mem_ball, dist_zero_right]; linarith [hd₁, hrr_lt_one, hw])
  set Ut : ℂ → ℝ := fun w => Real.log M - Real.log ‖Phi_rr w‖ with hUtdef
  have hUt_harm : InnerProductSpace.HarmonicOnNhd Ut (Metric.ball (0:ℂ) rr) := by
    intro w hw
    have hw' : ‖w‖ < rr := by rwa [Metric.mem_ball, dist_zero_right] at hw
    rw [hUtdef]
    exact (InnerProductSpace.harmonicAt_const (Real.log M)).sub
      ((hPhi_rr_an_ball w hw').harmonicAt_log_norm (hPhi_rr_ne w hw'))
  have hUt_nn : ∀ w : ℂ, ‖w‖ ≤ R' → 0 ≤ Ut w := by
    intro w hw
    rw [hUtdef]
    have h1 : ‖Phi_rr w‖ ≤ M := hPhi_rr_bound w (le_trans hw hR'lt.le)
    have h2 : 0 < ‖Phi_rr w‖ := norm_pos_iff.mpr (hPhi_rr_ne w (lt_of_le_of_lt hw hR'lt))
    linarith [Real.log_le_log h2 h1]
  -- |Phi_rr z₀| ≥ ‖G z₀‖
  have hQrr_lb : rr^Nr * ‖P_rr.eval z₀‖ ≤ ‖Qrr.eval z₀‖ := by
    have hterm : ∀ u ∈ Srr, (rr * ‖z₀ - u‖) ^ (Du u).toNat
        ≤ ‖(rr^2 - (starRingEnd ℂ) u * z₀) ^ (Du u).toNat‖ := by
      intro u hu
      rw [norm_pow]
      apply pow_le_pow_left₀ (by positivity)
      have hsq : rr^2 * ‖z₀-u‖^2 ≤ ‖rr^2 - (starRingEnd ℂ) u * z₀‖^2 := by
        have hkey := Commons.Analysis.Complex.Blaschke.normSq_blaschke_key rr u z₀
        have hnn : 0 ≤ (rr^2 - Complex.normSq z₀)*(rr^2 - Complex.normSq u) := by
          have hz : Complex.normSq z₀ ≤ rr^2 := by
            rw [Complex.normSq_eq_norm_sq]
            have h : ‖z₀‖ ≤ rr := le_trans hz₀le (le_trans hρ_lt_r₁.le hr₁_lt_rr.le)
            nlinarith [h, norm_nonneg z₀]
          have hu : Complex.normSq u ≤ rr^2 := by
            rw [Complex.normSq_eq_norm_sq]
            have h : ‖u‖ ≤ rr := (hSrr_lt u hu).le
            nlinarith [h, norm_nonneg u]
          nlinarith [hz, hu]
        have h1 : Complex.normSq ((↑rr:ℂ) * (z₀ - u)) = rr^2 * ‖z₀-u‖^2 := by
          rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]; ring
        have h3 : ‖rr^2 - (starRingEnd ℂ) u * z₀‖^2
            = Complex.normSq ((↑rr:ℂ)^2 - (starRingEnd ℂ) u * z₀) := by
          rw [Complex.normSq_eq_norm_sq]
        rw [h3]
        linarith [hkey, h1, hnn]
      have h1 : (rr * ‖z₀-u‖)^2 ≤ ‖rr^2 - (starRingEnd ℂ) u * z₀‖^2 := by
        rw [mul_pow]; linarith [hsq]
      nlinarith [h1, norm_nonneg (z₀-u), norm_nonneg (rr^2 - (starRingEnd ℂ) u * z₀), hrr0]
    rw [hQrr_eval, hPrr_eval, norm_prod, norm_prod]
    calc rr^Nr * ∏ u ∈ Srr, ‖(z₀ - u) ^ (Du u).toNat‖
        = (∏ u ∈ Srr, rr^(Du u).toNat) * ∏ u ∈ Srr, ‖(z₀ - u) ^ (Du u).toNat‖ := by
            rw [show (∏ u ∈ Srr, rr ^ (Du u).toNat) = rr ^ Nr by
              rw [hNrdef]
              exact Finset.prod_pow_eq_pow_sum _ _ _]
      _ = ∏ u ∈ Srr, (rr * ‖z₀ - u‖) ^ (Du u).toNat := by
            rw [← Finset.prod_mul_distrib]
            apply Finset.prod_congr rfl
            intro u hu
            rw [mul_pow, norm_pow]
      _ ≤ ∏ u ∈ Srr, ‖(rr^2 - (starRingEnd ℂ) u * z₀) ^ (Du u).toNat‖ :=
            Finset.prod_le_prod (fun u _ => by positivity) (fun u hu => hterm u hu)
  have hPhi_rr_ge : ‖G z₀‖ ≤ ‖Phi_rr z₀‖ := by
    have hPz₀' : P_rr.eval z₀ ≠ 0 := by
      intro h0; exact hPz₀ (by rw [hPall_eval' z₀, h0, zero_mul])
    have hrn : (0:ℝ) < rr^Nr := by positivity
    have hfac : ‖P_out.eval z₀ * g z₀‖ = ‖G z₀‖ / ‖P_rr.eval z₀‖ := by
      have hGz₀ : G z₀ = P_rr.eval z₀ * (P_out.eval z₀ * g z₀) := by
        rw [hGfacP z₀ hz₀ball, hPall_eval' z₀]; ring
      have h1 : ‖G z₀‖ = ‖P_rr.eval z₀‖ * ‖P_out.eval z₀ * g z₀‖ := by rw [hGz₀, norm_mul]
      have h2 : ‖P_out.eval z₀ * g z₀‖ = ‖P_out.eval z₀‖ * ‖g z₀‖ := norm_mul _ _
      rw [h1, mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr hPz₀')]
    have hval : ‖Phi_rr z₀‖ = (‖G z₀‖ / ‖P_rr.eval z₀‖) * ‖Qrr.eval z₀‖ / rr^Nr := by
      rw [hPhirrdef, norm_div, norm_mul, hfac, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hrn]
    rw [hval, le_div_iff₀ hrn]
    rw [div_mul_eq_mul_div, le_div_iff₀ (norm_pos_iff.mpr hPz₀')]
    nlinarith [hQrr_lb, norm_nonneg (G z₀), norm_nonneg (P_rr.eval z₀), norm_nonneg (Qrr.eval z₀), hrn]
  have hUt_z₀ : Ut z₀ ≤ A := by
    rw [hUtdef]
    have h2 : Real.log ‖G z₀‖ ≤ Real.log ‖Phi_rr z₀‖ :=
      Real.log_le_log (norm_pos_iff.mpr hGz₀) hPhi_rr_ge
    rw [hAdef]; linarith [hmz₀, h2]
  -- Harnack
  have hHarnack : ∀ w : ℂ, ‖w‖ ≤ r₁ → Ut w ≤ (16/3 : ℝ) * δ⁻¹^2 * A := by
    intro w hw
    have hwR' : ‖w‖ < R' := lt_of_le_of_lt hw hR'gt
    have hz₀R' : ‖z₀‖ < R' := lt_of_le_of_lt hz₀le (by rw [hR'def]; linarith)
    have hharmc : InnerProductSpace.HarmonicOnNhd Ut (Metric.closedBall (0:ℂ) R') := by
      intro z hz
      exact hUt_harm z (by
        rw [Metric.mem_ball, dist_zero_right]
        exact lt_of_le_of_lt (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz) hR'lt)
    have hposc : ∀ z : ℂ, z ∈ Metric.closedBall (0:ℂ) R' → 0 ≤ Ut z :=
      fun z hz => hUt_nn z (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
    obtain ⟨hlo1, hhi1⟩ := Commons.Analysis.Complex.Harmonic.harnack_inequality_ball
      (a := (0:ℂ)) (R := R') hharmc hposc (w := w) (by rw [Metric.mem_ball, dist_zero_right]; exact hwR')
    obtain ⟨hlo2, hhi2⟩ := Commons.Analysis.Complex.Harmonic.harnack_inequality_ball
      (a := (0:ℂ)) (R := R') hharmc hposc (w := z₀) (by rw [Metric.mem_ball, dist_zero_right]; exact hz₀R')
    simp only [sub_zero] at hlo1 hhi1 hlo2 hhi2
    have hU0nn : 0 ≤ Ut 0 := hposc 0 (by simp [Metric.mem_closedBall, hR'pos.le])
    have hU0 : Ut 0 ≤ ((R' + ‖z₀‖)/(R' - ‖z₀‖)) * Ut z₀ := by
      have hp1 : 0 < R' + ‖z₀‖ := by linarith [hR'pos, norm_nonneg z₀]
      have hp2 : 0 < R' - ‖z₀‖ := by linarith [hz₀R']
      rw [div_mul_eq_mul_div, div_le_iff₀ hp1] at hlo2
      rw [div_mul_eq_mul_div, le_div_iff₀ hp2]
      nlinarith [hlo2]
    have hK1 : (R' + ‖w‖)/(R' - ‖w‖) ≤ (R' + r₁)/(R' - r₁) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith [hw, hwR', hR'gt, hR'pos, norm_nonneg w]
    have hK2 : (R' + ‖z₀‖)/(R' - ‖z₀‖) ≤ (R' + ρ)/(R' - ρ) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith [hz₀le, hz₀R', hR'gt, hρ_lt_r₁, hr₁_lt_rr]
    have hK3 : ((R' + r₁)/(R' - r₁)) * ((R' + ρ)/(R' - ρ)) ≤ (16/3 : ℝ) * δ⁻¹^2 := by
      rw [hR'def, hrrdef, hr₁def, hρdef]
      rw [show (16/3 : ℝ) * δ⁻¹^2 = 16/(3*δ^2) by rw [inv_pow]; ring]
      rw [div_mul_div_comm, div_le_div_iff₀ (by nlinarith [hδ0, hδ1]) (by positivity)]
      ring_nf
      have hδpos : 0 < δ^3 := by positivity
      have hle : (189/4:ℝ) * δ^4 ≤ 48 * δ^3 := by
        rw [show δ^4 = δ^3 * δ by ring,
          show (189/4:ℝ) * (δ^3 * δ) = δ^3 * ((189/4)*δ) by ring,
          show (48:ℝ) * δ^3 = δ^3 * 48 by ring]
        apply mul_le_mul_of_nonneg_left _ hδpos.le
        linarith
      linarith
    have hU4 : 0 ≤ Ut z₀ := hUt_nn z₀ (le_of_lt hz₀R')
    have hK1nn : 0 ≤ (R' + r₁)/(R' - r₁) := by apply div_nonneg <;> linarith
    calc Ut w ≤ ((R' + ‖w‖)/(R' - ‖w‖)) * Ut 0 := hhi1
      _ ≤ ((R' + r₁)/(R' - r₁)) * Ut 0 := mul_le_mul_of_nonneg_right hK1 hU0nn
      _ ≤ ((R' + r₁)/(R' - r₁)) * (((R' + ρ)/(R' - ρ)) * Ut z₀) := by
            apply mul_le_mul_of_nonneg_left _ hK1nn
            calc Ut 0 ≤ ((R' + ‖z₀‖)/(R' - ‖z₀‖)) * Ut z₀ := hU0
              _ ≤ ((R' + ρ)/(R' - ρ)) * Ut z₀ := mul_le_mul_of_nonneg_right hK2 hU4
      _ = (((R' + r₁)/(R' - r₁)) * ((R' + ρ)/(R' - ρ))) * Ut z₀ := by ring
      _ ≤ (16/3 : ℝ) * δ⁻¹^2 * A :=
            mul_le_mul hK3 hUt_z₀ hU4 (by positivity)
  -- ============ the logarithmic bound for P_out * g ============
  have hlogPg : ∀ w : ℂ, ‖w‖ ≤ r₁ →
      Real.log M - (Nr:ℝ) * Real.log 2 - (16/3:ℝ)*δ⁻¹^2*A ≤ Real.log ‖P_out.eval w * g w‖ := by
    intro w hw
    have hne1 : P_out.eval w * g w ≠ 0 := by
      apply mul_ne_zero
      · rw [hPoutdef, Polynomial.eval_prod]
        rw [Finset.prod_ne_zero_iff]
        intro u hu
        simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        apply pow_ne_zero
        intro h0
        rw [sub_eq_zero.mp h0] at hw
        have h1 : rr ≤ ‖u‖ := hSout_ge u hu
        have h2 : r₁ < rr := hr₁_lt_rr
        linarith
      · exact hgnz w (Metric.ball_subset_closedBall (by
          rw [Metric.mem_ball, dist_zero_right]
          exact lt_of_le_of_lt hw (lt_trans hr₁_lt_rr hrr_lt_one)))
    have hrew : ((rr:ℂ))^2 = (rr^2 : ℂ) := by push_cast; ring
    have hbase_ne : ∀ u ∈ Srr, rr^2 - (starRingEnd ℂ) u * w ≠ 0 := by
      intro u hu h0
      have h0' : (rr^2 : ℂ) - (starRingEnd ℂ) u * w = 0 := by rw [← hrew]; exact h0
      have h1 : (starRingEnd ℂ) u * w = (rr^2 : ℂ) := (sub_eq_zero.mp h0').symm
      have h2 : ‖u‖ * ‖w‖ = rr^2 := by
        have := congrArg norm h1
        simpa [norm_mul, norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrr0] using this
      have hu1 : ‖u‖ ≤ 1 := hSsub u (hSrrS u hu)
      have hr1 : r₁ < rr^2 := by rw [hr₁def, hrrdef]; nlinarith [hδ0, hδ1]
      nlinarith [h2, hu1, hw, hr1, hrr0, hrr_lt_one, norm_nonneg u, norm_nonneg w]
    have hne2 : Qrr.eval w ≠ 0 := by
      rw [hQrr_eval, Finset.prod_ne_zero_iff]
      intro u hu
      exact pow_ne_zero _ (hbase_ne u (by rw [hSrrdef]; exact hu))
    have hQlog : Real.log ‖Qrr.eval w‖ ≤ (Nr:ℝ) * Real.log (rr*(rr+r₁)) := by
      have hfac : ∀ u ∈ Srr, ‖(rr^2 - (starRingEnd ℂ) u * w) ^ (Du u).toNat‖
          ≤ (rr*(rr+r₁)) ^ (Du u).toNat := by
        intro u hu
        rw [norm_pow]
        apply pow_le_pow_left₀ (by positivity)
        calc ‖rr^2 - (starRingEnd ℂ) u * w‖ ≤ ‖(rr^2:ℂ)‖ + ‖(starRingEnd ℂ) u * w‖ :=
              norm_sub_le _ _
          _ = rr^2 + ‖u‖ * ‖w‖ := by
              rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrr0, norm_mul, norm_conj]
          _ ≤ rr^2 + rr * r₁ := by
              have := mul_le_mul (hSrr_lt u hu).le hw (norm_nonneg w) hrr0.le
              linarith
          _ = rr*(rr+r₁) := by ring
      rw [hQrr_eval, norm_prod, Real.log_prod]
      · calc ∑ u ∈ Srr, Real.log ‖(rr^2 - (starRingEnd ℂ) u * w) ^ (Du u).toNat‖
            ≤ ∑ u ∈ Srr, Real.log ((rr*(rr+r₁)) ^ (Du u).toNat) := by
              apply Finset.sum_le_sum
              intro u hu
              apply Real.log_le_log
              · rw [norm_pos_iff]; exact pow_ne_zero _ (hbase_ne u (by rw [hSrrdef]; exact hu))
              · exact hfac u hu
          _ = ∑ u ∈ Srr, ((Du u).toNat : ℝ) * Real.log (rr*(rr+r₁)) := by
              apply Finset.sum_congr rfl
              intro u hu
              rw [Real.log_pow]
          _ = (Nr:ℝ) * Real.log (rr*(rr+r₁)) := by
              rw [hNrdef, Nat.cast_sum, Finset.sum_mul]
      · intro u hu
        exact norm_ne_zero_iff.mpr (pow_ne_zero _ (hbase_ne u (by rw [hSrrdef]; exact hu)))
    have hUw : Ut w ≤ (16/3:ℝ)*δ⁻¹^2*A := hHarnack w hw
    have hPoutw : P_out.eval w ≠ 0 := by
      rw [hPoutdef, Polynomial.eval_prod]
      rw [Finset.prod_ne_zero_iff]
      intro u hu
      simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      apply pow_ne_zero
      intro h0
      rw [sub_eq_zero.mp h0] at hw
      have h1 : rr ≤ ‖u‖ := hSout_ge u hu
      linarith [hw, h1]
    have hgw : g w ≠ 0 := hgnz w (Metric.ball_subset_closedBall (by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt hw (lt_trans hr₁_lt_rr hrr_lt_one)))
    have hPhi : Real.log ‖Phi_rr w‖
        = Real.log ‖P_out.eval w * g w‖ + Real.log ‖Qrr.eval w‖ - (Nr:ℝ)*Real.log rr := by
      have h1 : ‖Phi_rr w‖ = ‖P_out.eval w * g w‖ * ‖Qrr.eval w‖ / rr^Nr := by
        rw [hPhirrdef]
        simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0:ℝ) < rr^Nr)]
      rw [h1, Real.log_div (by positivity) (by positivity),
        Real.log_mul (norm_ne_zero_iff.mpr hne1) (norm_ne_zero_iff.mpr hne2), Real.log_pow]
    simp only [hUtdef] at hUw
    rw [hPhi] at hUw
    have h2 : Real.log (rr+r₁) ≤ Real.log 2 :=
      Real.log_le_log (by linarith) (by rw [hr₁def, hrrdef]; linarith)
    have h3 : Real.log (rr*(rr+r₁)) = Real.log rr + Real.log (rr+r₁) := by
      rw [Real.log_mul hrr0.ne' (by linarith)]
    rw [h3] at hQlog
    nlinarith [hUw, hQlog, h2, hA0]

  -- ============ arithmetic preamble ============
  have hL1pos : 0 < Real.log ((1 + ρ*rr)/(ρ+rr)) := by linarith [hL1, pow_pos hδ0 2]
  have hNr_le : (Nr:ℝ) ≤ A / Real.log ((1 + ρ*rr)/(ρ+rr)) := by
    rw [le_div_iff₀ hL1pos]; linarith [hmass]
  have hNr_le2 : (Nr:ℝ) ≤ A * δ⁻¹^2 := by
    have h2 : δ⁻¹^2 * δ^2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hδ0.ne', one_pow]
    have h3 : A = A * δ⁻¹^2 * δ^2 := by rw [mul_assoc, h2, mul_one]
    have h4 : A * δ⁻¹^2 * δ^2 ≤ A * δ⁻¹^2 * Real.log ((1+ρ*rr)/(ρ+rr)) :=
      mul_le_mul_of_nonneg_left hL1 (by positivity)
    have h5 : A / Real.log ((1+ρ*rr)/(ρ+rr)) ≤ A * δ⁻¹^2 := by
      rw [div_le_iff₀ hL1pos]
      linarith [h3, h4]
    linarith [hNr_le, h5]
  have hlogH4pos : 0 < H/(4*Real.exp 1) := div_pos hH0 (by positivity)
  have hlogH4neg : Real.log (H/(4*Real.exp 1)) < 0 := by
    rw [Real.log_neg_iff hlogH4pos, div_lt_one (by positivity)]
    have h1 : (1:ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr one_pos
    linarith [hH1]
  have hNrlog : A * (δ⁻¹^2 * Real.log (H/(4*Real.exp 1)))
      ≤ (Nr:ℝ) * Real.log (H/(4*Real.exp 1)) := by
    have h1 := mul_le_mul_of_nonpos_right hNr_le2 (le_of_lt hlogH4neg)
    rwa [mul_assoc] at h1
  have hlogeq : Real.log (H/(2*Real.exp 1)) - Real.log 2 = Real.log (H/(4*Real.exp 1)) := by
    rw [← Real.log_div (by positivity) (by norm_num : (2:ℝ) ≠ 0)]
    congr 1
    rw [div_div, show (2 * Real.exp 1) * 2 = 4 * Real.exp 1 by ring]
  have hlogH2 : Real.log (2*Real.exp 1/H) = -Real.log (H/(2*Real.exp 1)) := by
    rw [← Real.log_inv]
    congr 1
    rw [inv_div]
  have harith : (16/3:ℝ)*δ⁻¹^2 + δ⁻¹^2*Real.log 2 - 1 ≤ 2*δ⁻¹^3*Real.log (2/δ) := by
    have ht : (3:ℝ) ≤ δ⁻¹ := by
      have h3inv : (3:ℝ)⁻¹ = 1/3 := by norm_num
      rw [← le_inv_comm₀ hδ0 (by norm_num : (0:ℝ) < 3), h3inv]
      linarith [hδ3]
    have hlog6 : (16/3 + Real.log 2) ≤ 6 * Real.log 6 := by
      have h3 : (1:ℝ) ≤ Real.log 3 := by
        have h := Real.log_le_log (Real.exp_pos 1) (le_of_lt Real.exp_one_lt_three)
        rwa [Real.log_exp] at h
      have h2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      rw [show (6:ℝ) = 2*3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith
    have hloglt : Real.log 6 ≤ Real.log (2/δ) := by
      apply Real.log_le_log (by norm_num)
      rw [le_div_iff₀ hδ0]; linarith
    have hlog6nn : (0:ℝ) ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    have hkey : (16/3 + Real.log 2) ≤ 2*δ⁻¹ * Real.log (2/δ) := by
      have h1 : 3 * Real.log 6 ≤ δ⁻¹ * Real.log (2/δ) :=
        mul_le_mul ht hloglt hlog6nn (by positivity)
      linarith
    have hsq : (16/3 + Real.log 2) * δ⁻¹^2 ≤ 2*δ⁻¹*Real.log (2/δ) * δ⁻¹^2 :=
      mul_le_mul_of_nonneg_right hkey (by positivity)
    have hstep : (16/3:ℝ)*δ⁻¹^2 + δ⁻¹^2*Real.log 2 - 1
        ≤ (16/3 + Real.log 2) * δ⁻¹^2 := by nlinarith
    calc (16/3:ℝ)*δ⁻¹^2 + δ⁻¹^2*Real.log 2 - 1
        ≤ (16/3 + Real.log 2) * δ⁻¹^2 := hstep
      _ ≤ 2*δ⁻¹*Real.log (2/δ) * δ⁻¹^2 := hsq
      _ = 2*δ⁻¹^3*Real.log (2/δ) := by ring
  -- ============ Cartan disks and final assembly ============
  have hPrr_deg : P_rr.natDegree = Nr := by
    rw [hPrrdef, hNrdef]
    rw [Polynomial.natDegree_prod Srr (fun u => (Polynomial.X - Polynomial.C u) ^ (Du u).toNat)
      (fun u _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero u))]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Polynomial.natDegree_pow (Polynomial.X - Polynomial.C u) (Du u).toNat,
      Polynomial.natDegree_X_sub_C, mul_one]
  obtain ⟨s, r, hspos, hssum, hscov⟩ :=
    cartan_polynomial P_rr hPrr_monic hPrr_root (H := H/2) (by linarith) (by linarith)
  refine ⟨s, r, hspos, by linarith [hssum], ?_⟩
  intro z hz hr
  have hzr₁ : ‖z‖ ≤ r₁ := by rw [hr₁def]; exact hz
  have hz1 : z ∈ Metric.ball (0:ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖z‖ ≤ r₁ := hzr₁
      _ < 1 := by rw [hr₁def]; linarith
  have hbase : (0:ℝ) < H/2 / Real.exp 1 := div_pos (by linarith) (Real.exp_pos 1)
  have hPrz : (H/2 / Real.exp 1) ^ Nr ≤ ‖P_rr.eval z‖ := by
    have h := hscov z hr
    rwa [hPrr_deg] at h
  have hGz : G z = P_rr.eval z * (P_out.eval z * g z) := by
    rw [hGfacP z hz1, hPall_eval' z]; ring
  have hPrz_ne : P_rr.eval z ≠ 0 := by
    intro h0
    have h1 := hPrz
    rw [h0, norm_zero] at h1
    have h2 : (0:ℝ) < (H/2 / Real.exp 1) ^ Nr := pow_pos hbase Nr
    linarith
  have hPoutgz_ne : P_out.eval z * g z ≠ 0 := by
    apply mul_ne_zero
    · rw [hPoutdef, Polynomial.eval_prod]
      rw [Finset.prod_ne_zero_iff]
      intro u hu
      simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      apply pow_ne_zero
      intro h0
      rw [sub_eq_zero.mp h0] at hzr₁
      have h1 : rr ≤ ‖u‖ := hSout_ge u hu
      linarith [hzr₁, h1, hr₁_lt_rr]
    · exact hgnz z (Metric.ball_subset_closedBall hz1)
  have hlogG : Real.log ‖G z‖
      = Real.log ‖P_rr.eval z‖ + Real.log ‖P_out.eval z * g z‖ := by
    rw [hGz, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hPrz_ne)
      (norm_ne_zero_iff.mpr hPoutgz_ne)]
  have hlogPr : (Nr:ℝ) * Real.log (H/(2*Real.exp 1)) ≤ Real.log ‖P_rr.eval z‖ := by
    have h1 := Real.log_le_log (pow_pos hbase Nr) hPrz
    rw [Real.log_pow] at h1
    have h2 : Real.log (H/2 / Real.exp 1) = Real.log (H/(2*Real.exp 1)) := by
      congr 1; ring
    rwa [h2] at h1
  have hlogPg2 : Real.log M - (Nr:ℝ)*Real.log 2 - (16/3:ℝ)*δ⁻¹^2*A
      ≤ Real.log ‖P_out.eval z * g z‖ := hlogPg z hzr₁
  rw [hlogG]
  have hL2eq : Real.log (2 * Real.exp 1 / H)
      = -(Real.log (H/(4*Real.exp 1)) + Real.log 2) := by
    linarith [hlogH2, hlogeq]
  have hlogPr2 : (Nr:ℝ) * Real.log (H/(4*Real.exp 1)) + (Nr:ℝ) * Real.log 2
      ≤ Real.log ‖P_rr.eval z‖ := by
    have h := hlogPr
    have h3 : Real.log (H/(2*Real.exp 1))
        = Real.log (H/(4*Real.exp 1)) + Real.log 2 := by linarith [hlogeq]
    rw [h3] at h
    nlinarith [h]
  have hAd : A * ((16/3:ℝ)*δ⁻¹^2 + δ⁻¹^2*Real.log 2 - 1)
      ≤ A * (2*δ⁻¹^3*Real.log (2/δ)) :=
    mul_le_mul_of_nonneg_left harith hA0
  rw [hL2eq]
  nlinarith [hlogPr2, hlogPg2, hNrlog, hAd, hAdef]

end Commons.Analysis.Complex
