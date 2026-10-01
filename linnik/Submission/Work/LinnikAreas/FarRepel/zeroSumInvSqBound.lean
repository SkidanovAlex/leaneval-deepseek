import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Commons.NumberTheory.Zeta.zeta1_re_two_lower
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
import Submission.Commons.NumberTheory.Zeta.zeta_norm_le_const_of_three_le_re
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity
import Submission.Commons.Analysis.Dyadic.invSq_le_dyadic_layer
import Submission.Work.LinnikAreas.completedRiemannZeta_zero_strip
import Submission.Commons.NumberTheory.DirichletCharacter.far_zero_invSq_sum_uniform_delta
import Submission.Commons.NumberTheory.DirichletCharacter.diskZeroCount_two_half
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultTransfer
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultStripPos

open Complex DirichletCharacter Filter
open scoped Classical BigOperators Topology

namespace Work.LinnikAreas.FarRepel

noncomputable section

set_option maxHeartbeats 1600000

set_option maxHeartbeats 1600000

/-- In the critical strip the vanishing order of `Λ` equals that of `ζ₁ = (s-1)ζ`. -/
lemma ordNat_completedRiemannZeta_eq_zeta1 {u : ℂ} (h0 : 0 < u.re) (h1 : u.re < 1) :
    analyticOrderNatAt completedRiemannZeta u = analyticOrderNatAt riemannZeta₁ u := by
  have hu0 : u ≠ 0 := by intro h; rw [h] at h0; simp at h0
  have hu1 : u ≠ 1 := by intro h; rw [h] at h1; norm_num at h1
  have hGan : AnalyticAt ℂ Complex.Gammaℝ u := by
    have hinv : Differentiable ℂ (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) :=
      Complex.differentiable_Gammaℝ_inv
    have hinvz : (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) u ≠ 0 :=
      inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos h0)
    have han0 : AnalyticAt ℂ (fun s : ℂ => ((Complex.Gammaℝ s)⁻¹)⁻¹) u :=
      (hinv.analyticAt u).inv hinvz
    have heq : (fun s : ℂ => ((Complex.Gammaℝ s)⁻¹)⁻¹) = Complex.Gammaℝ := by
      funext s; rw [inv_inv]
    rwa [heq] at han0
  have hinv : AnalyticAt ℂ (fun s : ℂ => (s - 1)⁻¹) u :=
    (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hu1)
  have hgan : AnalyticAt ℂ (fun s : ℂ => Complex.Gammaℝ s * (s - 1)⁻¹) u := hGan.mul hinv
  have hganne : (fun s : ℂ => Complex.Gammaℝ s * (s - 1)⁻¹) u ≠ 0 :=
    mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos h0) (inv_ne_zero (sub_ne_zero.mpr hu1))
  have hz1an : AnalyticAt ℂ riemannZeta₁ u := differentiable_riemannZeta₁.analyticAt u
  have hEq : completedRiemannZeta =ᶠ[𝓝 u]
      fun s => Complex.Gammaℝ s * (s - 1)⁻¹ * riemannZeta₁ s := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds h0,
      eventually_ne_nhds hu0, eventually_ne_nhds hu1] with s hsre hs0 hs1
    have hGs : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hsre
    have hζ : riemannZeta s = (s - 1)⁻¹ * riemannZeta₁ s := riemannZeta_eq_inv_sub_mul hs1
    have hΛζ : completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
      rw [riemannZeta_def_of_ne_zero hs0]; field_simp
    rw [hΛζ, hζ]; ring
  have h1' : analyticOrderNatAt completedRiemannZeta u
      = analyticOrderNatAt (fun s : ℂ => Complex.Gammaℝ s * (s - 1)⁻¹ * riemannZeta₁ s) u := by
    simp only [analyticOrderNatAt]
    rw [analyticOrderAt_congr hEq]
  have h_or : analyticOrderAt (fun s : ℂ => Complex.Gammaℝ s * (s - 1)⁻¹ * riemannZeta₁ s) u
      = analyticOrderAt (fun s : ℂ => Complex.Gammaℝ s * (s - 1)⁻¹) u
        + analyticOrderAt riemannZeta₁ u := by
    rw [show (fun s : ℂ => Complex.Gammaℝ s * (s - 1)⁻¹ * riemannZeta₁ s)
        = (fun s : ℂ => Complex.Gammaℝ s * (s - 1)⁻¹) * riemannZeta₁ from rfl]
    exact analyticOrderAt_mul hgan hz1an
  have hzero : analyticOrderAt (fun s : ℂ => Complex.Gammaℝ s * (s - 1)⁻¹) u = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hganne)
  have h1'' : analyticOrderNatAt (fun s : ℂ => Complex.Gammaℝ s * (s - 1)⁻¹ * riemannZeta₁ s) u
      = analyticOrderNatAt riemannZeta₁ u := by
    simp only [analyticOrderNatAt]
    rw [h_or, hzero, zero_add]
  rw [h1', h1'']

/-- The vanishing order of `Λ` is at most that of `ζ₁`, everywhere. -/
lemma multZeta_le_order_zeta1 (u : ℂ) :
    analyticOrderNatAt completedRiemannZeta u ≤ analyticOrderNatAt riemannZeta₁ u := by
  by_cases hΛ : completedRiemannZeta u = 0
  · obtain ⟨h0, h1⟩ := Work.LinnikAreas.completedRiemannZeta_zero_strip hΛ
    rw [ordNat_completedRiemannZeta_eq_zeta1 h0 h1]
  · have hz : analyticOrderNatAt completedRiemannZeta u = 0 := by
      have h0 : analyticOrderAt completedRiemannZeta u = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr hΛ)
      simp [analyticOrderNatAt, h0]
    rw [hz]; exact Nat.zero_le _

/-- A uniform bound for `ζ₁` on the fixed disk `‖z‖ ≤ 10`. -/
lemma zeta1_bound_ball_exists :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ z : ℂ, ‖z‖ ≤ 10 → ‖riemannZeta₁ z‖ ≤ B := by
  have hK : IsCompact (Metric.closedBall (0 : ℂ) 10) := isCompact_closedBall _ _
  have hne : (Metric.closedBall (0 : ℂ) 10).Nonempty := ⟨0, by simp⟩
  obtain ⟨x, hx, hxmax⟩ := hK.exists_isMaxOn hne
    (differentiable_riemannZeta₁.continuous.continuousOn.norm)
  refine ⟨max 1 ‖riemannZeta₁ x‖, le_max_left _ _, fun z hz => ?_⟩
  exact le_trans (hxmax (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)) (le_max_right _ _)

/-- The logarithmic ratio appearing in Jensen's inequality is `O(log M)`. -/
lemma jensen_log_bound (M m : ℝ) (hM : 1 ≤ M) (hmlo : (1:ℝ)/4 ≤ m) :
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

/-- **Counting zeros of `ζ` in a unit window.** -/
lemma window1_count :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ t : ℝ, ∀ S : Finset ℂ,
      (∀ u ∈ S, |u.im - t| ≤ 1) →
      ∑ u ∈ S, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
        ≤ C0 * (Real.log (2 + |t|) + 2) := by
  obtain ⟨B0, hB01, hB0⟩ := zeta1_bound_ball_exists
  obtain ⟨Cpg, hCpgpos, hCpg⟩ := Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
  obtain ⟨C3, hC3pos, hC3⟩ := Commons.NumberTheory.Zeta.zeta_norm_le_const_of_three_le_re
  set K1 : ℝ := max Cpg (max C3 1) with hK1def
  have hK11 : 1 ≤ K1 := le_trans (le_max_right C3 1) (le_max_right Cpg (max C3 1))
  have hK1pos : 0 < K1 := lt_of_lt_of_le zero_lt_one hK11
  have hCpgK : Cpg ≤ K1 := le_max_left _ _
  have hC3K : C3 ≤ K1 := le_trans (le_max_left C3 1) (le_max_right Cpg (max C3 1))
  set C0 : ℝ := 12.5 * (15 + Real.log K1 + Real.log 4) + 12.5 * (Real.log B0 + Real.log 4) + 1
    with hC0def
  have hlogK1 : 0 ≤ Real.log K1 := Real.log_nonneg hK11
  have hlogB0 : 0 ≤ Real.log B0 := Real.log_nonneg hB01
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hC0pos : 0 < C0 := by rw [hC0def]; linarith
  refine ⟨C0, hC0pos, ?_⟩
  intro t S hS
  set c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ) with hc
  set S' : Finset ℂ := S.filter (fun u => analyticOrderNatAt completedRiemannZeta u ≠ 0) with hS'
  have hsumS : ∑ u ∈ S, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
      = ∑ u ∈ S', ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) := by
    rw [hS', Finset.sum_filter]
    apply Finset.sum_congr rfl; intro u _
    by_cases h : analyticOrderNatAt completedRiemannZeta u ≠ 0
    · rw [if_pos h]
    · rw [if_neg h, not_not.mp h]; simp
  rw [hsumS]
  have hstripS : ∀ u ∈ S', 0 < u.re ∧ u.re < 1 := by
    intro u hu
    have hne : analyticOrderNatAt completedRiemannZeta u ≠ 0 := (Finset.mem_filter.mp hu).2
    exact Work.LinnikAreas.completedRiemannZeta_zero_strip
      (apply_eq_zero_of_analyticOrderNatAt_ne_zero hne)
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
      ∑ u ∈ S', ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
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
      have hne : analyticOrderNatAt completedRiemannZeta u ≠ 0 := (Finset.mem_filter.mp hu).2
      have hlt : 0 < analyticOrderNatAt riemannZeta₁ u :=
        lt_of_lt_of_le (Nat.pos_of_ne_zero hne) (multZeta_le_order_zeta1 u)
      refine (hmem u).mpr ?_
      rw [hval u (hmem_ball u hu)]
      exact_mod_cast hlt.ne'
    have hle : ∀ u ∈ S', ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
        ≤ (((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c (23/10))) u : ℤ) : ℝ) := by
      intro u hu
      rw [hval u (hmem_ball u hu)]
      exact_mod_cast multZeta_le_order_zeta1 u
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
  have hone : ∀ t : ℝ, (1:ℝ) ≤ Real.log (2 + |t|) + 2 := by
    intro t
    have : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  refine le_trans ?_ (le_refl (C0 * (Real.log (2 + |t|) + 2)))
  by_cases ht5 : |t| ≤ 5
  · have hbd : ∀ z ∈ Metric.sphere c |(5:ℝ)/2|, ‖riemannZeta₁ z‖ ≤ B0 := by
      intro z hz
      have hzn : ‖z - c‖ = 5/2 := by
        have h := hz
        rw [Metric.mem_sphere, dist_eq_norm] at h
        rw [h, abs_of_pos (by norm_num : (0:ℝ) < 5/2)]
      have hcnorm : ‖c‖ ≤ 6 := by
        rw [hc]
        have hsq : ‖(2:ℂ) + Complex.I * (t:ℂ)‖ ^ 2 = 4 + t ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
        have h25 : t ^ 2 ≤ 25 := by
          have hp : (0:ℝ) ≤ (5 - t) * (5 + t) :=
            mul_nonneg (by linarith [(abs_le.mp ht5).2]) (by linarith [(abs_le.mp ht5).1])
          nlinarith [hp]
        nlinarith [hsq, h25, norm_nonneg ((2:ℂ) + Complex.I * (t:ℂ))]
      have hz10 : ‖z‖ ≤ 10 := by
        calc ‖z‖ = ‖(z - c) + c‖ := by rw [show (z - c) + c = z by ring]
          _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
          _ ≤ 5/2 + 6 := by linarith
          _ ≤ 10 := by norm_num
      exact hB0 z hz10
    have h1 := hjensen B0 hB01 hbd
    have h2 := jensen_log_bound B0 ‖riemannZeta₁ c‖ hB01 hΓlower
    have h3 : 12.5 * (Real.log B0 + Real.log 4) ≤ C0 * (Real.log (2 + |t|) + 2) := by
      have h4 : 12.5 * (Real.log B0 + Real.log 4) ≤ C0 := by rw [hC0def]; linarith
      nlinarith [h4, hC0pos, hone t]
    linarith
  · have htabs : (5:ℝ) < |t| := lt_of_not_ge ht5
    have hbd : ∀ z ∈ Metric.sphere c |(5:ℝ)/2|, ‖riemannZeta₁ z‖ ≤ K1 * (|t| + 9) ^ 5 := by
      intro z hz
      have hzn : ‖z - c‖ = 5/2 := by
        have h := hz
        rw [Metric.mem_sphere, dist_eq_norm] at h
        rw [h, abs_of_pos (by norm_num : (0:ℝ) < 5/2)]
      have hre : |z.re - 2| ≤ 5/2 := by
        have h1 : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm (z - c)
        rw [hzn] at h1
        simpa [hc] using h1
      have him : |z.im - t| ≤ 5/2 := by
        have h1 : |(z - c).im| ≤ ‖z - c‖ := Complex.abs_im_le_norm (z - c)
        rw [hzn] at h1
        simpa [hc] using h1
      have hre_lo : -(1:ℝ) ≤ z.re := by linarith [(abs_le.mp hre).1]
      have him1 : (1:ℝ) ≤ |z.im| := by
        have h1 : |t| - |z.im| ≤ |t - z.im| := abs_sub_abs_le_abs_sub t z.im
        have h2 : |t - z.im| = |z.im - t| := abs_sub_comm _ _
        have h3 : |z.im - t| ≤ 5/2 := him
        linarith
      have hz1ne : z ≠ 1 := by
        intro h1
        rw [h1] at him
        simp at him
        linarith
      have hz1eq : riemannZeta₁ z = (z - 1) * riemannZeta z := by
        have h := riemannZeta_eq_inv_sub_mul hz1ne
        rw [h, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hz1ne), one_mul]
      have hgle : (|z.im| + 3) ≤ (|t| + 9) := by
        have h2 : |z.im| ≤ |t| + 5/2 := by
          have h := abs_add_le (z.im - t) t
          rw [show (z.im - t) + t = z.im by ring] at h
          linarith
        linarith
      have hzeta : ‖riemannZeta z‖ ≤ K1 * (|t| + 9) ^ 4 := by
        by_cases h3 : z.re ≤ 3
        · have hb := hCpg z.re z.im hre_lo h3 him1
          have hze : (z.re : ℂ) + Complex.I * (z.im : ℂ) = z := by apply Complex.ext <;> simp
          rw [hze] at hb
          have h4 : (|z.im| + 3)^4 ≤ (|t| + 9)^4 :=
            pow_le_pow_left₀ (by positivity) hgle 4
          calc ‖riemannZeta z‖ ≤ Cpg * (|z.im| + 3)^4 := hb
            _ ≤ K1 * (|t| + 9)^4 := by
                calc Cpg * (|z.im| + 3)^4 ≤ K1 * (|z.im| + 3)^4 :=
                      mul_le_mul_of_nonneg_right hCpgK (by positivity)
                  _ ≤ K1 * (|t| + 9)^4 := mul_le_mul_of_nonneg_left h4 (le_of_lt hK1pos)
        · have h3' : 3 ≤ z.re := le_of_lt (lt_of_not_ge h3)
          have hb := hC3 z h3'
          have h4 : (1:ℝ) ≤ (|t| + 9)^4 := one_le_pow₀ (by linarith [abs_nonneg t])
          calc ‖riemannZeta z‖ ≤ C3 := hb
            _ ≤ K1 * (|t| + 9)^4 := by nlinarith [hC3K, h4, hK1pos]
      have hc1 : ‖c - 1‖ ≤ |t| + 1 := by
        rw [hc]
        have hzz : (2:ℂ) + Complex.I*(t:ℂ) - 1 = (1:ℂ) + Complex.I*(t:ℂ) := by ring
        rw [hzz]
        calc ‖(1:ℂ) + Complex.I*(t:ℂ)‖ ≤ ‖(1:ℂ)‖ + ‖Complex.I*(t:ℂ)‖ := norm_add_le _ _
          _ = |t| + 1 := by
              rw [norm_one]
              rw [norm_mul]
              rw [Complex.norm_I]
              rw [Complex.norm_real]
              rw [Real.norm_eq_abs]
              ring
      have hnorm : ‖(z - 1)‖ ≤ |t| + 5 := by
        have h1 : ‖z - 1‖ ≤ ‖z - c‖ + ‖c - 1‖ := by
          have : z - 1 = (z - c) + (c - 1) := by ring
          rw [this]; exact norm_add_le _ _
        rw [hzn] at h1
        linarith
      have hgle5 : (|t| + 5) * (|t| + 9)^4 ≤ (|t| + 9)^5 := by
        have h1 : (|t| + 5) ≤ (|t| + 9) := by linarith
        nlinarith [h1, pow_pos (by linarith [abs_nonneg t] : (0:ℝ) < |t|+9) 4]
      calc ‖riemannZeta₁ z‖ = ‖(z - 1) * riemannZeta z‖ := by rw [hz1eq]
        _ = ‖z - 1‖ * ‖riemannZeta z‖ := norm_mul _ _
        _ ≤ (|t| + 5) * (K1 * (|t| + 9)^4) := mul_le_mul hnorm hzeta (norm_nonneg _) (by positivity)
        _ = K1 * ((|t| + 5) * (|t| + 9)^4) := by ring
        _ ≤ K1 * (|t| + 9)^5 := mul_le_mul_of_nonneg_left hgle5 (le_of_lt hK1pos)
    have hM1 : 1 ≤ K1 * (|t| + 9)^5 := by
      have h1 : (1:ℝ) ≤ (|t| + 9)^5 := one_le_pow₀ (by linarith [abs_nonneg t])
      nlinarith [hK11, h1, hK1pos]
    have h1 := hjensen (K1 * (|t| + 9)^5) hM1 hbd
    have h2 := jensen_log_bound (K1 * (|t| + 9)^5) ‖riemannZeta₁ c‖ hM1 hΓlower
    have hlogM : Real.log (K1 * (|t| + 9)^5) = Real.log K1 + 5 * Real.log (|t| + 9) := by
      rw [Real.log_mul (ne_of_gt hK1pos) (by positivity), Real.log_pow]
      push_cast; ring
    have hlog93 : Real.log (|t| + 9) ≤ Real.log (2 + |t|) + 2 := by
      have hle : |t| + 9 ≤ (2 + |t|) * 3 := by linarith
      have h1 : Real.log (|t| + 9) ≤ Real.log ((2 + |t|) * 3) :=
        Real.log_le_log (by positivity) hle
      rw [Real.log_mul (by positivity) (by norm_num)] at h1
      have h2 : Real.log 3 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num); linarith
      linarith
    have h3 : 12.5 * (Real.log (K1 * (|t| + 9)^5) + Real.log 4)
        ≤ C0 * (Real.log (2 + |t|) + 2) := by
      rw [hlogM] at *
      have hL0 : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
      have hC0ge : 12.5 * (15 + Real.log K1 + Real.log 4) ≤ C0 := by
        rw [hC0def]; linarith [hlogB0]
      nlinarith [hC0ge, hL0, hlogK1, hlog4, hC0pos, hone t, hlog93]
    linarith

/-- Covering of the window `|Im u − t| ≤ h` by unit windows. -/
lemma window_cover_index {x t h : ℝ} (hx : |x - t| ≤ h) :
    (∃ j : ℕ, (j:ℝ) ≤ h/2 + 1 ∧ |x - (t + 2*(j:ℝ))| ≤ 1) ∨
    (∃ j : ℕ, (j:ℝ) ≤ h/2 + 1 ∧ |x - (t - 2*(j:ℝ))| ≤ 1) := by
  have hle : x - t ≤ h := (abs_le.mp hx).2
  have hge : -h ≤ x - t := (abs_le.mp hx).1
  by_cases htx : t ≤ x
  · left
    refine ⟨⌊(x - t + 1)/2⌋₊, ?_, ?_⟩
    · have hm : (0:ℝ) ≤ (x - t + 1)/2 := by linarith
      have h1 : ((⌊(x - t + 1)/2⌋₊ : ℕ) : ℝ) ≤ (x - t + 1)/2 := Nat.floor_le hm
      linarith
    · have hm : (0:ℝ) ≤ (x - t + 1)/2 := by linarith
      have h1 : ((⌊(x - t + 1)/2⌋₊ : ℕ) : ℝ) ≤ (x - t + 1)/2 := Nat.floor_le hm
      have h2 : (x - t + 1)/2 < ((⌊(x - t + 1)/2⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [abs_le]; constructor <;> linarith
  · right
    push_neg at htx
    refine ⟨⌊(t - x + 1)/2⌋₊, ?_, ?_⟩
    · have hm : (0:ℝ) ≤ (t - x + 1)/2 := by linarith
      have h1 : ((⌊(t - x + 1)/2⌋₊ : ℕ) : ℝ) ≤ (t - x + 1)/2 := Nat.floor_le hm
      linarith
    · have hm : (0:ℝ) ≤ (t - x + 1)/2 := by linarith
      have h1 : ((⌊(t - x + 1)/2⌋₊ : ℕ) : ℝ) ≤ (t - x + 1)/2 := Nat.floor_le hm
      have h2 : (t - x + 1)/2 < ((⌊(t - x + 1)/2⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [abs_le]; constructor <;> linarith

/-- The general window count. -/
theorem lamWindowZeroCount :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ∀ h : ℝ, 1 ≤ h → ∀ S : Finset ℂ,
      (∀ u ∈ S, |u.im - t| ≤ h) →
      ∑ u ∈ S, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
        ≤ C * (h + 1) * (Real.log (2 + |t| + h) + 2) := by
  obtain ⟨C0, hC0pos, hC0⟩ := window1_count
  refine ⟨50 * C0, by positivity, ?_⟩
  intro t h hh S hS
  set m : ℕ := ⌊h/2 + 1⌋₊ + 1 with hm
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by
    rw [hm]
    have h1 : (1:ℕ) ≤ ⌊h/2 + 1⌋₊ + 1 := Nat.succ_le_succ (Nat.zero_le _)
    exact_mod_cast h1
  have hm_le : (m:ℝ) ≤ h + 2 := by
    rw [hm]
    have h1 : ((⌊h/2 + 1⌋₊ : ℕ) : ℝ) ≤ h/2 + 1 :=
      Nat.floor_le (by linarith : (0:ℝ) ≤ h/2 + 1)
    push_cast
    linarith
  have hcover : ∀ u ∈ S, (∑ j ∈ Finset.range m, (if |u.im - (t + 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0))
      + (∑ j ∈ Finset.range m, (if |u.im - (t - 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0)) ≥ 1 := by
    intro u hu
    have hjm : ∀ j : ℕ, (j:ℝ) ≤ h/2 + 1 → j ∈ Finset.range m := by
      intro j hj
      rw [Finset.mem_range, hm]
      have h2 : j ≤ (⌊h/2 + 1⌋₊ : ℕ) := Nat.le_floor hj
      omega
    rcases window_cover_index (hS u hu) with ⟨j, hj, hw⟩ | ⟨j, hj, hw⟩
    · have h1 : (1:ℝ) ≤ ∑ j ∈ Finset.range m,
          (if |u.im - (t + 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0) := by
        have hmem : j ∈ Finset.range m := hjm j hj
        have hsub : ({j} : Finset ℕ) ⊆ Finset.range m := Finset.singleton_subset_iff.mpr hmem
        have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i _ _ => by positivity :
            ∀ i ∈ Finset.range m, i ∉ ({j} : Finset ℕ) →
              0 ≤ (if |u.im - (t + 2*(i:ℝ))| ≤ 1 then (1:ℝ) else 0))
        have h3 : ∑ i ∈ ({j} : Finset ℕ),
            (if |u.im - (t + 2*(i:ℝ))| ≤ 1 then (1:ℝ) else 0) = 1 := by
          rw [Finset.sum_singleton, if_pos hw]
        linarith
      have h2 : 0 ≤ ∑ j ∈ Finset.range m,
          (if |u.im - (t - 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0) :=
        Finset.sum_nonneg (fun i _ => by positivity)
      linarith
    · have h2 : (1:ℝ) ≤ ∑ j ∈ Finset.range m,
          (if |u.im - (t - 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0) := by
        have hmem : j ∈ Finset.range m := hjm j hj
        have hsub : ({j} : Finset ℕ) ⊆ Finset.range m := Finset.singleton_subset_iff.mpr hmem
        have h4 := Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i _ _ => by positivity :
            ∀ i ∈ Finset.range m, i ∉ ({j} : Finset ℕ) →
              0 ≤ (if |u.im - (t - 2*(i:ℝ))| ≤ 1 then (1:ℝ) else 0))
        have h5 : ∑ i ∈ ({j} : Finset ℕ),
            (if |u.im - (t - 2*(i:ℝ))| ≤ 1 then (1:ℝ) else 0) = 1 := by
          rw [Finset.sum_singleton, if_pos hw]
        linarith
      have h1 : 0 ≤ ∑ j ∈ Finset.range m,
          (if |u.im - (t + 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0) :=
        Finset.sum_nonneg (fun i _ => by positivity)
      linarith
  have hdistU : ∀ u : ℂ, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) *
        (∑ j ∈ Finset.range m, (if |u.im - (t + 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0))
      = ∑ j ∈ Finset.range m, (if |u.im - (t + 2*(j:ℝ))| ≤ 1
          then ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) else 0) := by
    intro u
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    by_cases hp : |u.im - (t + 2*(j:ℝ))| ≤ 1
    · rw [if_pos hp, if_pos hp]; ring
    · rw [if_neg hp, if_neg hp]; ring
  have hdistD : ∀ u : ℂ, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) *
        (∑ j ∈ Finset.range m, (if |u.im - (t - 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0))
      = ∑ j ∈ Finset.range m, (if |u.im - (t - 2*(j:ℝ))| ≤ 1
          then ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) else 0) := by
    intro u
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    by_cases hp : |u.im - (t - 2*(j:ℝ))| ≤ 1
    · rw [if_pos hp, if_pos hp]; ring
    · rw [if_neg hp, if_neg hp]; ring
  have hdist : ∑ u ∈ S, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
      ≤ ∑ j ∈ Finset.range m,
          (∑ u ∈ S, (if |u.im - (t + 2*(j:ℝ))| ≤ 1
            then ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) else 0))
        + ∑ j ∈ Finset.range m,
          (∑ u ∈ S, (if |u.im - (t - 2*(j:ℝ))| ≤ 1
            then ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) else 0)) := by
    have h1 : ∑ u ∈ S, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
        ≤ ∑ u ∈ S, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) *
            ((∑ j ∈ Finset.range m, (if |u.im - (t + 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0))
              + (∑ j ∈ Finset.range m, (if |u.im - (t - 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0))) := by
      apply Finset.sum_le_sum; intro u hu
      have hc := hcover u hu
      have hnn : (0:ℝ) ≤ ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) := by positivity
      nlinarith
    calc ∑ u ∈ S, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
        ≤ ∑ u ∈ S, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) *
            ((∑ j ∈ Finset.range m, (if |u.im - (t + 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0))
              + (∑ j ∈ Finset.range m, (if |u.im - (t - 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0))) := h1
      _ = ∑ u ∈ S, (((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) *
              (∑ j ∈ Finset.range m, (if |u.im - (t + 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0))
            + ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) *
              (∑ j ∈ Finset.range m, (if |u.im - (t - 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0))) := by
          apply Finset.sum_congr rfl; intro u _; ring
      _ = (∑ u ∈ S, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) *
              (∑ j ∈ Finset.range m, (if |u.im - (t + 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0)))
            + (∑ u ∈ S, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) *
              (∑ j ∈ Finset.range m, (if |u.im - (t - 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0))) :=
          Finset.sum_add_distrib
      _ = (∑ u ∈ S, ∑ j ∈ Finset.range m, (if |u.im - (t + 2*(j:ℝ))| ≤ 1
              then ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) else 0))
            + (∑ u ∈ S, ∑ j ∈ Finset.range m, (if |u.im - (t - 2*(j:ℝ))| ≤ 1
              then ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) else 0)) := by
          simp only [hdistU, hdistD]
      _ = (∑ j ∈ Finset.range m, ∑ u ∈ S, (if |u.im - (t + 2*(j:ℝ))| ≤ 1
              then ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) else 0))
            + (∑ j ∈ Finset.range m, ∑ u ∈ S, (if |u.im - (t - 2*(j:ℝ))| ≤ 1
              then ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) else 0)) := by
          congr 1
          · exact Finset.sum_comm
          · exact Finset.sum_comm
  have hwinU : ∀ j ∈ Finset.range m,
      (∑ u ∈ S, (if |u.im - (t + 2*(j:ℝ))| ≤ 1
        then ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) else 0))
        ≤ C0 * (Real.log (2 + |t + 2*(j:ℝ)|) + 2) := by
    intro j hj
    have hmem : ∀ u ∈ S.filter (fun u => |u.im - (t + 2*(j:ℝ))| ≤ 1),
        |u.im - (t + 2*(j:ℝ))| ≤ 1 := fun u hu => (Finset.mem_filter.mp hu).2
    have hb := hC0 (t + 2*(j:ℝ)) (S.filter (fun u => |u.im - (t + 2*(j:ℝ))| ≤ 1)) hmem
    rw [Finset.sum_filter] at hb
    simpa using hb
  have hwinD : ∀ j ∈ Finset.range m,
      (∑ u ∈ S, (if |u.im - (t - 2*(j:ℝ))| ≤ 1
        then ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) else 0))
        ≤ C0 * (Real.log (2 + |t - 2*(j:ℝ)|) + 2) := by
    intro j hj
    have hmem : ∀ u ∈ S.filter (fun u => |u.im - (t - 2*(j:ℝ))| ≤ 1),
        |u.im - (t - 2*(j:ℝ))| ≤ 1 := fun u hu => (Finset.mem_filter.mp hu).2
    have hb := hC0 (t - 2*(j:ℝ)) (S.filter (fun u => |u.im - (t - 2*(j:ℝ))| ≤ 1)) hmem
    rw [Finset.sum_filter] at hb
    simpa using hb
  have hlogterm : ∀ j ∈ Finset.range m,
      Real.log (2 + |t + 2*(j:ℝ)|) + 2 ≤ 2 * (Real.log (2 + |t| + h) + 2)
    ∧ Real.log (2 + |t - 2*(j:ℝ)|) + 2 ≤ 2 * (Real.log (2 + |t| + h) + 2) := by
    intro j hj
    have hjle : (j:ℝ) ≤ h/2 + 1 := by
      have hjm : j < m := Finset.mem_range.mp hj
      rw [hm] at hjm
      have h2 : j ≤ (⌊h/2 + 1⌋₊ : ℕ) := by omega
      exact le_trans (by exact_mod_cast h2 : (j:ℝ) ≤ ((⌊h/2 + 1⌋₊ : ℕ) : ℝ))
        (Nat.floor_le (by linarith : (0:ℝ) ≤ h/2 + 1))
    have h2j : 2*(j:ℝ) ≤ h + 2 := by linarith [hjle, hh]
    have hbase : (0:ℝ) < 2 + |t| + h := by linarith [abs_nonneg t]
    have h6 : 0 ≤ Real.log (2 + |t| + h) := Real.log_nonneg (by linarith [abs_nonneg t])
    have h5 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    constructor
    · have hle : |t + 2*(j:ℝ)| ≤ |t| + h + 2 := by
        calc |t + 2*(j:ℝ)| ≤ |t| + |2*(j:ℝ)| := abs_add_le _ _
          _ = |t| + 2*(j:ℝ) := by
              rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (j:ℝ))]; norm_num
          _ ≤ |t| + h + 2 := by linarith
      have h1 : Real.log (2 + |t + 2*(j:ℝ)|) ≤ Real.log (2 + |t| + h + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have h3 : (2 + |t| + h + 2) ≤ (2 + |t| + h) * 2 := by
        linarith [abs_nonneg t, hh]
      have h4 : Real.log (2 + |t| + h + 2) ≤ Real.log (2 + |t| + h) + Real.log 2 := by
        have := Real.log_le_log (by positivity) h3
        rwa [Real.log_mul (ne_of_gt hbase) (by norm_num)] at this
      linarith
    · have hle : |t - 2*(j:ℝ)| ≤ |t| + h + 2 := by
        calc |t - 2*(j:ℝ)| ≤ |t| + |2*(j:ℝ)| := by
              have h := abs_sub_le t 0 (2*(j:ℝ))
              simpa using h
          _ = |t| + 2*(j:ℝ) := by
              rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (j:ℝ))]; norm_num
          _ ≤ |t| + h + 2 := by linarith
      have h1 : Real.log (2 + |t - 2*(j:ℝ)|) ≤ Real.log (2 + |t| + h + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have h3 : (2 + |t| + h + 2) ≤ (2 + |t| + h) * 2 := by
        linarith [abs_nonneg t, hh]
      have h4 : Real.log (2 + |t| + h + 2) ≤ Real.log (2 + |t| + h) + Real.log 2 := by
        have := Real.log_le_log (by positivity) h3
        rwa [Real.log_mul (ne_of_gt hbase) (by norm_num)] at this
      linarith
  have hsumU : ∑ j ∈ Finset.range m,
      (∑ u ∈ S, (if |u.im - (t + 2*(j:ℝ))| ≤ 1
        then ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) else 0))
      ≤ (m:ℝ) * (C0 * (2 * (Real.log (2 + |t| + h) + 2))) := by
    calc ∑ j ∈ Finset.range m,
        (∑ u ∈ S, (if |u.im - (t + 2*(j:ℝ))| ≤ 1
          then ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) else 0))
        ≤ ∑ j ∈ Finset.range m, C0 * (2 * (Real.log (2 + |t| + h) + 2)) := by
          apply Finset.sum_le_sum; intro j hj
          exact le_trans (hwinU j hj)
            (mul_le_mul_of_nonneg_left (hlogterm j hj).1 (le_of_lt hC0pos))
      _ = (m:ℝ) * (C0 * (2 * (Real.log (2 + |t| + h) + 2))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsumD : ∑ j ∈ Finset.range m,
      (∑ u ∈ S, (if |u.im - (t - 2*(j:ℝ))| ≤ 1
        then ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) else 0))
      ≤ (m:ℝ) * (C0 * (2 * (Real.log (2 + |t| + h) + 2))) := by
    calc ∑ j ∈ Finset.range m,
        (∑ u ∈ S, (if |u.im - (t - 2*(j:ℝ))| ≤ 1
          then ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) else 0))
        ≤ ∑ j ∈ Finset.range m, C0 * (2 * (Real.log (2 + |t| + h) + 2)) := by
          apply Finset.sum_le_sum; intro j hj
          exact le_trans (hwinD j hj)
            (mul_le_mul_of_nonneg_left (hlogterm j hj).2 (le_of_lt hC0pos))
      _ = (m:ℝ) * (C0 * (2 * (Real.log (2 + |t| + h) + 2))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h7 : 0 ≤ Real.log (2 + |t| + h) + 2 := by
    have : 0 ≤ Real.log (2 + |t| + h) := Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  calc ∑ u ∈ S, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
      ≤ _ := hdist
    _ ≤ (m:ℝ) * (C0 * (2 * (Real.log (2 + |t| + h) + 2)))
          + (m:ℝ) * (C0 * (2 * (Real.log (2 + |t| + h) + 2))) := add_le_add hsumU hsumD
    _ = 2 * (m:ℝ) * (C0 * (2 * (Real.log (2 + |t| + h) + 2))) := by ring
    _ ≤ 50 * C0 * (h + 1) * (Real.log (2 + |t| + h) + 2) := by
        have hstep1 : 2 * (m:ℝ) * (C0 * (2 * (Real.log (2 + |t| + h) + 2)))
            = 4 * C0 * (Real.log (2 + |t| + h) + 2) * (m:ℝ) := by ring
        rw [hstep1]
        have h3 : 4 * C0 * (Real.log (2 + |t| + h) + 2) * (m:ℝ)
            ≤ 4 * C0 * (Real.log (2 + |t| + h) + 2) * (h + 2) := by
          apply mul_le_mul_of_nonneg_left hm_le
          positivity
        have h4 : 4 * C0 * (Real.log (2 + |t| + h) + 2) * (h + 2)
            ≤ 50 * C0 * (h + 1) * (Real.log (2 + |t| + h) + 2) := by
          have h5 : 4 * (h + 2) ≤ 50 * (h + 1) := by linarith
          have h6 := mul_le_mul_of_nonneg_right h5 (mul_nonneg (le_of_lt hC0pos) h7)
          calc 4 * C0 * (Real.log (2 + |t| + h) + 2) * (h + 2)
              = (4 * (h + 2)) * (C0 * (Real.log (2 + |t| + h) + 2)) := by ring
            _ ≤ (50 * (h + 1)) * (C0 * (Real.log (2 + |t| + h) + 2)) := h6
            _ = 50 * C0 * (h + 1) * (Real.log (2 + |t| + h) + 2) := by ring
        linarith [h3, h4]


theorem dirichletHalfAux :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
      (hprim : χ.IsPrimitive) (w : ℂ) (hw : 1 ≤ w.re),
      Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) / (1 + ‖w - u‖ ^ 2)) ∧
      (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) / (1 + ‖w - u‖ ^ 2))
        ≤ C * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2) := by
  obtain ⟨cfar, hcfarpos, hfar⟩ :=
    Commons.NumberTheory.DirichletCharacter.far_zero_invSq_sum_uniform_delta
  refine ⟨cfar + 12, by linarith, ?_⟩
  intro q hq _inst χ hχ hprim w hw
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψne : χ.primitiveCharacter ≠ 1 :=
    Work.LinnikAreas.OtherCharRepel.primitiveCharacter_ne_one χ hχ
  have hψprim : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hcond : χ.conductor = q := hprim
  have hlogN : Real.log ((χ.conductor : ℕ) : ℝ) = Real.log (q : ℝ) := by rw [hcond]
  set P : ℂ := (1 : ℂ) + (w.im : ℂ) * Complex.I with hPdef
  set ψ : DirichletCharacter ℂ χ.conductor := χ.primitiveCharacter with hψdef
  have hDuniv : ∀ u : ℂ,
      ((MeromorphicOn.divisor (completedLFunction ψ) Set.univ) u : ℤ)
        = (Work.LinnikContract.zeroMult χ u : ℤ) := by
    intro u
    have hdiff : Differentiable ℂ (completedLFunction ψ) :=
      differentiable_completedLFunction hψne
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast
      (fun z _ => hdiff.analyticAt z) (Set.mem_univ u)]
    simp only [Work.LinnikContract.zeroMult]
    rfl
  obtain ⟨hfarSum, hfarBnd⟩ := hfar (χ := ψ) hψne hψprim (s := w) hw
    (by norm_num : (0:ℝ) < 1) le_rfl
  have hfarSum' : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ)
      * (if 1 < ‖P - u‖ then 1 / ‖w - u‖ ^ 2 else 0)) := by
    refine hfarSum.congr ?_
    intro u
    have h := hDuniv u
    simp only [hPdef] at h ⊢
    rw [h]
    push_cast
    rfl
  have hfarBnd' : (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ)
      * (if 1 < ‖P - u‖ then 1 / ‖w - u‖ ^ 2 else 0))
      ≤ cfar * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2) := by
    have h := hfarBnd
    rw [hlogN] at h
    have hR : cfar / 1 ^ 2 * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2)
        = cfar * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2) := by norm_num
    rw [hR] at h
    refine le_trans (le_of_eq ?_) h
    apply tsum_congr
    intro u
    have h2 := hDuniv u
    simp only [hPdef] at h2 ⊢
    rw [h2]
    push_cast
    rfl
  set c₂ : ℂ := (2 : ℂ) + Complex.I * (w.im : ℂ) with hc₂
  have hfin : (Function.support (fun u : ℂ =>
      MeromorphicOn.divisor (completedLFunction ψ) (Metric.closedBall c₂ (5/2)) u)).Finite :=
    (MeromorphicOn.divisor _ _).finiteSupport (isCompact_closedBall c₂ (5/2))
  set S : Finset ℂ := hfin.toFinset with hSdef
  have hSmem : ∀ u : ℂ, u ∈ S ↔
      (MeromorphicOn.divisor (completedLFunction ψ) (Metric.closedBall c₂ (5/2))) u ≠ 0 := by
    intro u; rw [hSdef]; exact Set.Finite.mem_toFinset hfin
  have hDnn : ∀ u : ℂ, 0 ≤ ((MeromorphicOn.divisor (completedLFunction ψ)
      (Metric.closedBall c₂ (5/2))) u : ℤ) := by
    intro u
    by_cases hu : u ∈ Metric.closedBall c₂ (5/2)
    · exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg
        (f := completedLFunction ψ) (U := Metric.closedBall c₂ (5/2))
        (fun z _ => (differentiable_completedLFunction hψne).analyticAt z) u
    · rw [MeromorphicOn.divisor_def, if_neg]
      exact fun hc => hu hc.2
  have hSbound : ∑ u ∈ S, (((MeromorphicOn.divisor (completedLFunction ψ)
      (Metric.closedBall c₂ (5/2))) u : ℤ) : ℝ)
      ≤ (3/2) * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2) + 6 := by
    have h1 : ∑ u ∈ S, (((MeromorphicOn.divisor (completedLFunction ψ)
        (Metric.closedBall c₂ (5/2))) u : ℤ) : ℝ)
        = ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (completedLFunction ψ)
        (Metric.closedBall c₂ (5/2))) u : ℤ) : ℝ) := by
      have hf : (∑ᶠ u : ℂ, (MeromorphicOn.divisor (completedLFunction ψ)
          (Metric.closedBall c₂ (5/2))) u) = ∑ u ∈ S,
          (MeromorphicOn.divisor (completedLFunction ψ) (Metric.closedBall c₂ (5/2))) u := by
        rw [hSdef]
        refine finsum_eq_sum_of_support_subset _ ?_
        intro u hu
        rw [Function.mem_support] at hu
        exact (Set.Finite.mem_toFinset hfin).mpr hu
      have hm := map_sum (Int.castRingHom ℝ) (fun u : ℂ =>
        (MeromorphicOn.divisor (completedLFunction ψ) (Metric.closedBall c₂ (5/2))) u) S
      rw [hf]
      exact hm.symm
    have hd := Commons.NumberTheory.DirichletCharacter.diskZeroCount_two_half
      ψ hψne hψprim w.im
    rw [hlogN] at hd
    rw [show (2:ℂ) + Complex.I * (w.im:ℂ) = c₂ from hc₂.symm] at hd
    have hdmap : ((∑ᶠ u : ℂ, (MeromorphicOn.divisor (completedLFunction ψ)
        (Metric.closedBall c₂ (5/2))) u : ℤ) : ℝ)
        = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (completedLFunction ψ)
        (Metric.closedBall c₂ (5/2))) u : ℤ) : ℝ)) :=
      map_finsum (Int.castRingHom ℝ) hfin
    rw [h1, hdmap]
    have him : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
    have hlog4 : Real.log (2 + |w.im| + 2) ≤ Real.log (2 + ‖w‖) + 2 := by
      have hle : 2 + |w.im| + 2 ≤ (2 + ‖w‖) * 2 := by linarith [him, norm_nonneg w]
      have h1 : Real.log (2 + |w.im| + 2) ≤ Real.log ((2 + ‖w‖) * 2) :=
        Real.log_le_log (by positivity) hle
      rw [Real.log_mul (by positivity) (by norm_num)] at h1
      have h2 : Real.log 2 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
      linarith
    nlinarith [hd, hlog4]
  have hpt : ∀ u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) / (1 + ‖w - u‖ ^ 2)
      ≤ (Work.LinnikContract.zeroMult χ u : ℝ) * (if 1 < ‖P - u‖ then 1 / ‖w - u‖ ^ 2 else 0)
        + (Work.LinnikContract.zeroMult χ u : ℝ) * (if ‖P - u‖ ≤ 1 then 1 else 0) := by
    intro u
    by_cases hx : (Work.LinnikContract.zeroMult χ u : ℝ) = 0
    · rw [hx]; simp
    · have hxpos : 0 < (Work.LinnikContract.zeroMult χ u : ℝ) :=
        lt_of_le_of_ne (by positivity) (Ne.symm hx)
      have hxnn : (0:ℝ) ≤ (Work.LinnikContract.zeroMult χ u : ℝ) := le_of_lt hxpos
      have hzu : Work.LinnikContract.zeroMult χ u ≠ 0 := by
        intro h0; exact hx (by rw [h0]; simp)
      obtain ⟨hre1, hre2, -⟩ :=
        Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq hχ hzu
      have hwpos : 0 < ‖w - u‖ := by
        have h1 : |w.re - u.re| ≤ ‖w - u‖ := by
          simpa using Complex.abs_re_le_norm (w - u)
        have h2 : |w.re - u.re| = w.re - u.re := abs_of_nonneg (by linarith)
        rw [h2] at h1
        linarith
      by_cases hfar' : 1 < ‖P - u‖
      · have h2 : (if ‖P - u‖ ≤ 1 then (1:ℝ) else 0) = 0 := if_neg (not_le.mpr hfar')
        have h3 : (if 1 < ‖P - u‖ then (1:ℝ) / ‖w - u‖ ^ 2 else 0) = 1 / ‖w - u‖ ^ 2 :=
          if_pos hfar'
        have hk : (1:ℝ) / (1 + ‖w - u‖ ^ 2) ≤ 1 / ‖w - u‖ ^ 2 :=
          one_div_le_one_div_of_le (pow_pos hwpos 2) (by nlinarith [norm_nonneg (w - u)])
        calc (Work.LinnikContract.zeroMult χ u : ℝ) / (1 + ‖w - u‖ ^ 2)
            = (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖w - u‖ ^ 2)) :=
              div_eq_mul_one_div _ _
          _ ≤ (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / ‖w - u‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hk hxnn
          _ = (Work.LinnikContract.zeroMult χ u : ℝ) * (if 1 < ‖P - u‖ then 1 / ‖w - u‖ ^ 2 else 0)
                + (Work.LinnikContract.zeroMult χ u : ℝ) * (if ‖P - u‖ ≤ 1 then 1 else 0) := by
              rw [h3, h2, mul_zero, add_zero]
      · have h2 : (if 1 < ‖P - u‖ then (1:ℝ) / ‖w - u‖ ^ 2 else 0) = 0 := if_neg hfar'
        have h3 : (if ‖P - u‖ ≤ 1 then (1:ℝ) else 0) = 1 := if_pos (le_of_not_gt hfar')
        have hk : (1:ℝ) / (1 + ‖w - u‖ ^ 2) ≤ 1 := by
          rw [div_le_one (by positivity)]
          nlinarith [norm_nonneg (w - u)]
        calc (Work.LinnikContract.zeroMult χ u : ℝ) / (1 + ‖w - u‖ ^ 2)
            = (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖w - u‖ ^ 2)) :=
              div_eq_mul_one_div _ _
          _ ≤ (Work.LinnikContract.zeroMult χ u : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left hk hxnn
          _ = (Work.LinnikContract.zeroMult χ u : ℝ) * (if 1 < ‖P - u‖ then 1 / ‖w - u‖ ^ 2 else 0)
                + (Work.LinnikContract.zeroMult χ u : ℝ) * (if ‖P - u‖ ≤ 1 then 1 else 0) := by
              rw [h3, h2, mul_zero, zero_add]
  have hkey : ∀ T : Finset ℂ,
      ∑ u ∈ T, (Work.LinnikContract.zeroMult χ u : ℝ) / (1 + ‖w - u‖ ^ 2)
        ≤ cfar * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2)
          + ((3/2) * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2) + 6) := by
    intro T
    have h1 : ∑ u ∈ T, (Work.LinnikContract.zeroMult χ u : ℝ) / (1 + ‖w - u‖ ^ 2)
        ≤ ∑ u ∈ T, ((Work.LinnikContract.zeroMult χ u : ℝ)
            * (if 1 < ‖P - u‖ then 1 / ‖w - u‖ ^ 2 else 0)
          + (Work.LinnikContract.zeroMult χ u : ℝ) * (if ‖P - u‖ ≤ 1 then 1 else 0)) :=
      Finset.sum_le_sum (fun u _ => hpt u)
    have h2 : ∑ u ∈ T, ((Work.LinnikContract.zeroMult χ u : ℝ)
            * (if 1 < ‖P - u‖ then 1 / ‖w - u‖ ^ 2 else 0)
          + (Work.LinnikContract.zeroMult χ u : ℝ) * (if ‖P - u‖ ≤ 1 then 1 else 0))
        = (∑ u ∈ T, (Work.LinnikContract.zeroMult χ u : ℝ)
            * (if 1 < ‖P - u‖ then 1 / ‖w - u‖ ^ 2 else 0))
          + (∑ u ∈ T, (Work.LinnikContract.zeroMult χ u : ℝ)
            * (if ‖P - u‖ ≤ 1 then 1 else 0)) := Finset.sum_add_distrib
    have h11 : ∑ u ∈ T, (Work.LinnikContract.zeroMult χ u : ℝ)
        * (if 1 < ‖P - u‖ then 1 / ‖w - u‖ ^ 2 else 0)
        ≤ cfar * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2) := by
      exact le_trans (Summable.sum_le_tsum T (fun u _ => by positivity) hfarSum') hfarBnd'
    have h5 : ∑ u ∈ T, (Work.LinnikContract.zeroMult χ u : ℝ)
        * (if ‖P - u‖ ≤ 1 then 1 else 0) ≤ ∑ u ∈ S, (((MeromorphicOn.divisor
          (completedLFunction ψ) (Metric.closedBall c₂ (5/2))) u : ℤ) : ℝ) := by
      have h6 : ∀ u ∈ T, (Work.LinnikContract.zeroMult χ u : ℝ)
          * (if ‖P - u‖ ≤ 1 then 1 else 0) = (if ‖P - u‖ ≤ 1
            then (Work.LinnikContract.zeroMult χ u : ℝ) else 0) := by
        intro u _
        by_cases hh : ‖P - u‖ ≤ 1
        · rw [if_pos hh, if_pos hh, mul_one]
        · rw [if_neg hh, if_neg hh, mul_zero]
      rw [Finset.sum_congr rfl h6, ← Finset.sum_filter]
      have h7 : ∀ u ∈ T.filter (fun u => ‖P - u‖ ≤ 1),
          (Work.LinnikContract.zeroMult χ u : ℝ)
            ≤ (((MeromorphicOn.divisor (completedLFunction ψ)
                (Metric.closedBall c₂ (5/2))) u : ℤ) : ℝ) := by
        intro u hu
        by_cases hz : Work.LinnikContract.zeroMult χ u = 0
        · rw [hz]
          simp only [Nat.cast_zero]
          exact Int.cast_nonneg (hDnn u)
        · have hzero : completedLFunction ψ u = 0 := by
            have h1 : analyticOrderNatAt (completedLFunction ψ) u ≠ 0 := by
              intro hh; exact hz (by rw [Work.LinnikContract.zeroMult]; exact hh)
            exact apply_eq_zero_of_analyticOrderNatAt_ne_zero h1
          have hstrip := Commons.NumberTheory.Linnik.completedL_zero_strip ψ hψne hψprim hzero
          have hmem : u ∈ Metric.closedBall c₂ (5/2) := by
            rw [Metric.mem_closedBall, dist_eq_norm]
            have hsq : ‖u - c₂‖ ^ 2 = (u.re - 2) ^ 2 + (u.im - w.im) ^ 2 := by
              have hre : (u - c₂).re = u.re - 2 := by simp [hc₂]
              have him' : (u - c₂).im = u.im - w.im := by simp [hc₂]
              rw [Complex.sq_norm, Complex.normSq_apply, hre, him']; ring
            have him2 : |u.im - w.im| ≤ 1 := by
              have hP1 : ‖P - u‖ ≤ 1 := (Finset.mem_filter.mp hu).2
              have h1 : |(P - u).im| ≤ ‖P - u‖ := Complex.abs_im_le_norm (P - u)
              have h2 : (P - u).im = w.im - u.im := by simp [hPdef]
              rw [h2] at h1
              rw [abs_sub_comm] at h1
              linarith
            have h2 : ‖u - c₂‖ ^ 2 < (5/2)^2 := by
              rw [hsq]
              have h3 := abs_le.mp him2
              nlinarith [hstrip.1, hstrip.2, h3.1, h3.2]
            nlinarith [norm_nonneg (u - c₂)]
          have hval : ((MeromorphicOn.divisor (completedLFunction ψ)
              (Metric.closedBall c₂ (5/2))) u : ℤ)
              = (Work.LinnikContract.zeroMult χ u : ℤ) := by
            rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast
              (fun z _ => (differentiable_completedLFunction hψne).analyticAt z) hmem]
            simp only [Work.LinnikContract.zeroMult]
            rfl
          rw [hval]
          simp
      have h8 : ∑ u ∈ T.filter (fun u => ‖P - u‖ ≤ 1),
          (Work.LinnikContract.zeroMult χ u : ℝ)
          ≤ ∑ u ∈ T.filter (fun u => ‖P - u‖ ≤ 1),
            (((MeromorphicOn.divisor (completedLFunction ψ)
              (Metric.closedBall c₂ (5/2))) u : ℤ) : ℝ) := Finset.sum_le_sum h7
      have h9 : ∑ u ∈ T.filter (fun u => ‖P - u‖ ≤ 1),
            (((MeromorphicOn.divisor (completedLFunction ψ)
              (Metric.closedBall c₂ (5/2))) u : ℤ) : ℝ)
          ≤ ∑ u ∈ S, (((MeromorphicOn.divisor (completedLFunction ψ)
              (Metric.closedBall c₂ (5/2))) u : ℤ) : ℝ) := by
        have h10 : ∑ u ∈ T.filter (fun u => ‖P - u‖ ≤ 1),
              (((MeromorphicOn.divisor (completedLFunction ψ)
                (Metric.closedBall c₂ (5/2))) u : ℤ) : ℝ)
            = ∑ u ∈ (T.filter (fun u => ‖P - u‖ ≤ 1)).filter
                (fun u => u ∈ S),
              (((MeromorphicOn.divisor (completedLFunction ψ)
                (Metric.closedBall c₂ (5/2))) u : ℤ) : ℝ) := by
          refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
          intro u hu hnot
          have hnu : u ∉ S := fun hc =>
            hnot (Finset.mem_filter.mpr ⟨hu, hc⟩)
          have h0 : ((MeromorphicOn.divisor (completedLFunction ψ)
              (Metric.closedBall c₂ (5/2))) u : ℤ) = 0 := by
            by_contra hne
            exact hnu ((hSmem u).mpr hne)
          rw [h0]; simp
        rw [h10]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun u hu => (Finset.mem_filter.mp hu).2)
          (fun u _ _ => Int.cast_nonneg (hDnn u))
      linarith [h8, h9]
    linarith [h1, h2, h5, hSbound, h11]
  have hnn : ∀ u : ℂ, (0:ℝ) ≤ (Work.LinnikContract.zeroMult χ u : ℝ) / (1 + ‖w - u‖ ^ 2) :=
    fun u => by positivity
  have hCbound : ∀ T : Finset ℂ,
      ∑ u ∈ T, (Work.LinnikContract.zeroMult χ u : ℝ) / (1 + ‖w - u‖ ^ 2)
        ≤ (cfar + 12) * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2) := by
    intro T
    refine le_trans (hkey T) ?_
    have h1 : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
    have h2 : 0 ≤ Real.log (2 + ‖w‖) := Real.log_nonneg (by linarith [norm_nonneg w])
    nlinarith [hcfarpos, h1, h2]
  exact ⟨summable_of_sum_le hnn hCbound, Real.tsum_le_of_sum_le hnn hCbound⟩


/-- `∑_{k ≤ K} (k+2)·(1/2)^k ≤ 6`. -/
lemma sum_kp2_half_le (K : ℕ) :
    ∑ k ∈ Finset.range (K+1), ((k:ℝ) + 2) * ((1/2:ℝ)^k) ≤ 6 := by
  have hsumm1 : Summable (fun k : ℕ => ((k:ℝ) + 1) * ((1/2:ℝ)^k)) := by
    have h := hasSum_choose_mul_geometric_of_norm_lt_one (k := 1) (r := (1/2:ℝ)) (by norm_num)
    simpa [Nat.choose_one_right, mul_comm] using h.summable
  have hval1 : (∑' k : ℕ, ((k:ℝ) + 1) * ((1/2:ℝ)^k)) = 4 := by
    have h := hasSum_choose_mul_geometric_of_norm_lt_one (k := 1) (r := (1/2:ℝ)) (by norm_num)
    rw [show (1:ℝ)/(1-(1/2:ℝ))^(1+1) = 4 by norm_num] at h
    have h' := h.tsum_eq
    simpa [Nat.choose_one_right, mul_comm] using h'
  have hsumm2 : Summable (fun k : ℕ => ((1/2:ℝ)^k)) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hval2 : (∑' k : ℕ, ((1/2:ℝ)^k)) = 2 := tsum_geometric_two
  have hsumm : Summable (fun k : ℕ => ((k:ℝ) + 2) * ((1/2:ℝ)^k)) := by
    have h := hsumm1.add hsumm2
    refine h.congr ?_
    intro k; ring
  have hval : (∑' k : ℕ, ((k:ℝ) + 2) * ((1/2:ℝ)^k)) = 6 := by
    have hcongr : (∑' k : ℕ, ((k:ℝ) + 2) * ((1/2:ℝ)^k))
        = ∑' k : ℕ, (((k:ℝ)+1)*((1/2:ℝ)^k) + ((1/2:ℝ)^k)) := by
      apply tsum_congr; intro k; ring
    rw [hcongr, Summable.tsum_add hsumm1 hsumm2, hval1, hval2]
    norm_num
  exact le_trans (Summable.sum_le_tsum (Finset.range (K+1))
    (f := fun k : ℕ => ((k:ℝ) + 2) * ((1/2:ℝ)^k)) (fun i _ => by positivity) hsumm)
    (le_of_eq hval)

/-- `log(2+a+2^k) + 2 ≤ (k+2)(log(2+a)+2)` for `a ≥ 0`. -/
lemma log_add_pow_le (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    Real.log (2 + a + (2:ℝ)^k) + 2 ≤ ((k:ℝ) + 2) * (Real.log (2 + a) + 2) := by
  have hbase : (0:ℝ) < 2 + a := by linarith
  have hpow : (0:ℝ) < (2:ℝ)^k := by positivity
  have hle : 2 + a + (2:ℝ)^k ≤ (2 + a) * (2 * (2:ℝ)^k) := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0; simp; linarith
    · have h2k : (2:ℝ) ≤ (2:ℝ)^k := by
        calc (2:ℝ) = (2:ℝ)^1 := by ring
          _ ≤ (2:ℝ)^k := pow_le_pow_right₀ (by norm_num) hpos
      nlinarith [ha, h2k]
  have hlog := Real.log_le_log (by positivity) hle
  rw [Real.log_mul (ne_of_gt hbase) (by positivity : (2 * (2:ℝ)^k) ≠ 0),
      Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hpow), Real.log_pow] at hlog
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hka : 0 ≤ Real.log (2 + a) := Real.log_nonneg (by linarith)
  have hk0 : (0:ℝ) ≤ (k:ℝ) := by positivity
  have h1 : Real.log (2 + a + (2:ℝ)^k) ≤ Real.log (2 + a) + (k:ℝ) + 1 := by
    nlinarith [hlog, hlog2, hk0]
  nlinarith [h1, hka, hk0]

/-- The dyadic arithmetic for the ζ half. -/
lemma dyadic_arith (t : ℝ) (Cw : ℝ) (hCw : 0 ≤ Cw) (K : ℕ) :
    ∑ k ∈ Finset.range (K+1),
        (4/(4:ℝ)^k) * (Cw * ((2:ℝ)^k + 1) * (Real.log (2 + |t| + (2:ℝ)^k) + 2))
      ≤ 50 * Cw * (Real.log (2 + |t|) + 2) := by
  set L : ℝ := Real.log (2 + |t|) + 2 with hL
  have hL0 : 0 ≤ L := by
    rw [hL]
    have : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  have hpow : ∀ k : ℕ, (4/(4:ℝ)^k) * ((2:ℝ)^k + 1) = 4 * ((1/2:ℝ)^k + (1/4:ℝ)^k) := by
    intro k
    have h2 : (2:ℝ)^k / (4:ℝ)^k = (1/2:ℝ)^k := by
      rw [← div_pow]; norm_num
    have h4 : (1:ℝ) / (4:ℝ)^k = (1/4:ℝ)^k := by
      rw [show (1:ℝ) = 1^k by simp, ← div_pow]; norm_num
    have h4k : (4:ℝ)^k ≠ 0 := pow_ne_zero k (by norm_num)
    calc (4/(4:ℝ)^k) * ((2:ℝ)^k + 1)
        = 4 * ((2:ℝ)^k/(4:ℝ)^k) + 4 * ((1:ℝ)/(4:ℝ)^k) := by
          field_simp
      _ = 4 * ((1/2:ℝ)^k + (1/4:ℝ)^k) := by rw [h2, h4]; ring
  have hterm : ∀ k : ℕ,
      (4/(4:ℝ)^k) * (Cw * ((2:ℝ)^k + 1) * (Real.log (2 + |t| + (2:ℝ)^k) + 2))
        ≤ Cw * L * ((4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * ((k:ℝ) + 2)) := by
    intro k
    have hlog := log_add_pow_le |t| (abs_nonneg t) k
    have hcoef : (0:ℝ) ≤ Cw * (4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) := by positivity
    calc (4/(4:ℝ)^k) * (Cw * ((2:ℝ)^k + 1) * (Real.log (2 + |t| + (2:ℝ)^k) + 2))
        = Cw * ((4/(4:ℝ)^k) * ((2:ℝ)^k + 1)) * (Real.log (2 + |t| + (2:ℝ)^k) + 2) := by ring
      _ = Cw * (4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * (Real.log (2 + |t| + (2:ℝ)^k) + 2) := by rw [hpow]
      _ ≤ Cw * (4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * (((k:ℝ) + 2) * L) := by
            apply mul_le_mul_of_nonneg_left _ hcoef
            rw [hL]; exact hlog
      _ = Cw * L * ((4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * ((k:ℝ) + 2)) := by ring
  have hsum2 : ∑ k ∈ Finset.range (K+1), (4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * ((k:ℝ) + 2) ≤ 48 := by
    have hsplit : ∑ k ∈ Finset.range (K+1), (4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * ((k:ℝ) + 2)
        = 4 * (∑ k ∈ Finset.range (K+1), ((k:ℝ) + 2) * ((1/2:ℝ)^k))
          + 4 * (∑ k ∈ Finset.range (K+1), ((k:ℝ) + 2) * ((1/4:ℝ)^k)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k _
      ring
    have h14 : ∑ k ∈ Finset.range (K+1), ((k:ℝ) + 2) * ((1/4:ℝ)^k)
        ≤ ∑ k ∈ Finset.range (K+1), ((k:ℝ) + 2) * ((1/2:ℝ)^k) := by
      apply Finset.sum_le_sum; intro k _
      have hle : ((1:ℝ)/4)^k ≤ ((1:ℝ)/2)^k := by
        apply pow_le_pow_left₀ (by norm_num) (by norm_num)
      have h2 : (0:ℝ) ≤ (k:ℝ) + 2 := by positivity
      nlinarith [hle, h2]
    have h12 := sum_kp2_half_le K
    rw [hsplit]
    linarith
  calc ∑ k ∈ Finset.range (K+1),
        (4/(4:ℝ)^k) * (Cw * ((2:ℝ)^k + 1) * (Real.log (2 + |t| + (2:ℝ)^k) + 2))
      ≤ ∑ k ∈ Finset.range (K+1), Cw * L * ((4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * ((k:ℝ) + 2)) :=
        Finset.sum_le_sum (fun k _ => hterm k)
    _ = Cw * L * ∑ k ∈ Finset.range (K+1), (4 * ((1/2:ℝ)^k + (1/4:ℝ)^k)) * ((k:ℝ) + 2) := by
        rw [Finset.mul_sum]
    _ ≤ Cw * L * 48 := by
        apply mul_le_mul_of_nonneg_left hsum2
        positivity
    _ ≤ 50 * Cw * (Real.log (2 + |t|) + 2) := by
        rw [hL] at *
        nlinarith [hL0]

/-- The kernel domination `1/(1+‖w-u‖²) ≤ 1/(1+(Im w - Im u)²)`. -/
lemma inv_one_add_norm_sq_le (w u : ℂ) :
    (1:ℝ) / (1 + ‖w - u‖ ^ 2) ≤ 1 / (1 + (w.im - u.im) ^ 2) := by
  have hsq : ‖w - u‖ ^ 2 = (w.re - u.re) ^ 2 + (w.im - u.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hre : (w - u).re = w.re - u.re := by simp
    have him : (w - u).im = w.im - u.im := by simp
    rw [hre, him]; ring
  apply one_div_le_one_div_of_le
  · positivity
  · rw [hsq]; nlinarith [sq_nonneg (w.re - u.re)]

/-- **Inverse-square kernel bound for the non-trivial zeros of `ζ`.** -/
theorem zetaHalfKernelBound :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ,
      Summable (fun u : ℂ =>
        ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) * (1 / (1 + ‖w - u‖ ^ 2))) ∧
      (∑' u : ℂ, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) * (1 / (1 + ‖w - u‖ ^ 2)))
        ≤ C * (Real.log (2 + ‖w‖) + 2) := by
  obtain ⟨Cw, hCwpos, hCw⟩ := lamWindowZeroCount
  have hCw0 : 0 ≤ Cw := le_of_lt hCwpos
  refine ⟨50 * Cw, by positivity, ?_⟩
  intro w
  set t : ℝ := w.im with ht
  have key : ∀ S : Finset ℂ,
      ∑ u ∈ S, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) * (1 / (1 + ‖w - u‖ ^ 2))
        ≤ 50 * Cw * (Real.log (2 + |t|) + 2) := by
    intro S
    obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ u ∈ S, |u.im - t| ≤ (2:ℝ)^K := by
      rcases S.eq_empty_or_nonempty with h | hne
      · exact ⟨0, by intro u hu; rw [h] at hu; exact absurd hu (Finset.notMem_empty u)⟩
      · obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (∑ u ∈ S, (|u.im - t| + 1)) (by norm_num : (1:ℝ) < 2)
        refine ⟨K, fun u hu => ?_⟩
        have hle : |u.im - t| + 1 ≤ ∑ v ∈ S, (|v.im - t| + 1) :=
          Finset.single_le_sum (f := fun v => |v.im - t| + 1) (fun v _ => by positivity) hu
        linarith
    have hstep : ∑ u ∈ S, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) * (1 / (1 + ‖w - u‖ ^ 2))
        ≤ ∑ u ∈ S, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) *
            (∑ k ∈ Finset.range (K+1), (if |u.im - t| ≤ (2:ℝ)^k then 4/(4:ℝ)^k else 0)) := by
      apply Finset.sum_le_sum; intro u hu
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h2 := inv_one_add_norm_sq_le w u
      have h3 : (1:ℝ) / (1 + (w.im - u.im) ^ 2) = 1 / (1 + |u.im - t| ^ 2) := by
        rw [ht]
        congr 2
        rw [sq_abs]; ring
      rw [h3] at h2
      have hKu : |u.im - t| ≤ (2:ℝ)^K := hK u hu
      exact le_trans h2 (Commons.Analysis.Dyadic.invSq_le_dyadic_layer |u.im - t| (abs_nonneg _) K hKu)
    have h6 : ∑ u ∈ S, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) *
              (∑ k ∈ Finset.range (K+1), (if |u.im - t| ≤ (2:ℝ)^k then 4/(4:ℝ)^k else 0))
          = ∑ k ∈ Finset.range (K+1), (4/(4:ℝ)^k) *
              ∑ u ∈ S, (if |u.im - t| ≤ (2:ℝ)^k
                then ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) else 0) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro u _
      by_cases hp : |u.im - t| ≤ (2:ℝ)^k
      · rw [if_pos hp, if_pos hp]; ring
      · rw [if_neg hp, if_neg hp]; ring
    have hwin : ∀ k ∈ Finset.range (K+1),
        (∑ u ∈ S, (if |u.im - t| ≤ (2:ℝ)^k
            then ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) else 0))
          ≤ Cw * ((2:ℝ)^k + 1) * (Real.log (2 + |t| + (2:ℝ)^k) + 2) := by
      intro k hk
      have hk1 : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
      have hmem : ∀ u ∈ S.filter (fun u => |u.im - t| ≤ (2:ℝ)^k), |u.im - t| ≤ (2:ℝ)^k :=
        fun u hu => (Finset.mem_filter.mp hu).2
      have hb := hCw t ((2:ℝ)^k) hk1 (S.filter (fun u => |u.im - t| ≤ (2:ℝ)^k)) hmem
      rw [Finset.sum_filter] at hb
      simpa using hb
    have h7 : ∑ k ∈ Finset.range (K+1), (4/(4:ℝ)^k) *
            ∑ u ∈ S, (if |u.im - t| ≤ (2:ℝ)^k
              then ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) else 0)
        ≤ ∑ k ∈ Finset.range (K+1), (4/(4:ℝ)^k) *
            (Cw * ((2:ℝ)^k + 1) * (Real.log (2 + |t| + (2:ℝ)^k) + 2)) := by
      apply Finset.sum_le_sum; intro k hk
      apply mul_le_mul_of_nonneg_left (hwin k hk) (by positivity)
    calc ∑ u ∈ S, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) * (1 / (1 + ‖w - u‖ ^ 2))
        ≤ ∑ u ∈ S, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) *
            (∑ k ∈ Finset.range (K+1), (if |u.im - t| ≤ (2:ℝ)^k then 4/(4:ℝ)^k else 0)) := hstep
      _ = ∑ k ∈ Finset.range (K+1), (4/(4:ℝ)^k) *
              ∑ u ∈ S, (if |u.im - t| ≤ (2:ℝ)^k
                then ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) else 0) := h6
      _ ≤ ∑ k ∈ Finset.range (K+1), (4/(4:ℝ)^k) *
            (Cw * ((2:ℝ)^k + 1) * (Real.log (2 + |t| + (2:ℝ)^k) + 2)) := h7
      _ ≤ 50 * Cw * (Real.log (2 + |t|) + 2) := dyadic_arith t Cw hCw0 K
  have hle_t : Real.log (2 + |t|) ≤ Real.log (2 + ‖w‖) := by
    apply Real.log_le_log (by positivity)
    have : |t| ≤ ‖w‖ := by
      have h := Complex.abs_im_le_norm w
      simpa [ht] using h
    linarith
  have hfin : ∀ S : Finset ℂ,
      ∑ u ∈ S, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) * (1 / (1 + ‖w - u‖ ^ 2))
        ≤ 50 * Cw * (Real.log (2 + ‖w‖) + 2) := by
    intro S
    refine le_trans (key S) ?_
    have h2 : 0 ≤ Real.log (2 + ‖w‖) + 2 := by
      have : 0 ≤ Real.log (2 + ‖w‖) := Real.log_nonneg (by linarith [norm_nonneg w])
      linarith
    nlinarith [hle_t, h2, hCw0]
  exact ⟨summable_of_sum_le (f := fun u : ℂ =>
      ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) * (1 / (1 + ‖w - u‖ ^ 2)))
      (fun u => by positivity) hfin,
    Real.tsum_le_of_sum_le (f := fun u : ℂ =>
      ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) * (1 / (1 + ‖w - u‖ ^ 2)))
      (fun u => by positivity) hfin⟩


/-- Assembly test (uses the DEV placeholder for the L half). -/
theorem zeroSumInvSqBound :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
      (hprim : χ.IsPrimitive) (w : ℂ) (hw : (3 / 2 : ℝ) ≤ w.re),
      Summable (fun u : ℂ => (((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
              + (Work.LinnikContract.zeroMult χ u : ℝ)) / ‖w - u‖ ^ 2) ∧
        (∑' u : ℂ, (((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
              + (Work.LinnikContract.zeroMult χ u : ℝ)) / ‖w - u‖ ^ 2)
          ≤ C * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2) := by
  obtain ⟨Cz, hCzpos, hCz⟩ := zetaHalfKernelBound
  obtain ⟨Cl, hClpos, hCl⟩ := dirichletHalfAux
  refine ⟨5 * (Cz + Cl) + 1, by linarith, ?_⟩
  intro q hq _inst χ hχ hprim w hw
  obtain ⟨hsumZ, hbndZ⟩ := hCz w
  obtain ⟨hsumL, hbndL⟩ := hCl q hq χ hχ hprim w (by linarith)
  have hsumL' : Summable (fun u : ℂ =>
      (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖w - u‖ ^ 2))) :=
    hsumL.congr (fun u => by rw [mul_one_div])
  have hbndL' : (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖w - u‖ ^ 2)))
      ≤ Cl * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2) := by
    have heq : (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖w - u‖ ^ 2)))
        = (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) / (1 + ‖w - u‖ ^ 2)) :=
      tsum_congr (fun u => by rw [mul_one_div])
    rw [heq]; exact hbndL
  have hpt : ∀ u : ℂ,
      ((((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) + (Work.LinnikContract.zeroMult χ u : ℝ))
          / ‖w - u‖ ^ 2)
        ≤ 5 * ((((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
            + (Work.LinnikContract.zeroMult χ u : ℝ)) * (1 / (1 + ‖w - u‖ ^ 2))) := by
    intro u
    by_cases h : ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
        + (Work.LinnikContract.zeroMult χ u : ℝ) = 0
    · rw [h]; simp
    · have hpos : 0 < ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
          + (Work.LinnikContract.zeroMult χ u : ℝ) :=
        lt_of_le_of_ne (by positivity) (Ne.symm h)
      have hle1 : u.re ≤ 1 := by
        rcases lt_or_ge 0 ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) with h1 | h1
        · have hz : analyticOrderNatAt completedRiemannZeta u ≠ 0 := by
            intro h0; rw [h0] at h1; simp at h1
          have hΛ : completedRiemannZeta u = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hz
          exact le_of_lt (Work.LinnikAreas.completedRiemannZeta_zero_strip hΛ).2
        · have hb2 : 0 < (Work.LinnikContract.zeroMult χ u : ℝ) := by
            have h2 : 0 ≤ ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) := by positivity
            linarith
          have hz : Work.LinnikContract.zeroMult χ u ≠ 0 := by
            intro h0; rw [h0] at hb2; simp at hb2
          exact le_of_lt (Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq hχ hz).2.1
      have hdist : (1/2:ℝ) ≤ ‖w - u‖ := by
        have h1 : |w.re - u.re| ≤ ‖w - u‖ := by
          simpa using Complex.abs_re_le_norm (w - u)
        have h2 : |w.re - u.re| = w.re - u.re := abs_of_nonneg (by linarith)
        rw [h2] at h1
        linarith
      have h4 : (1:ℝ) ≤ 4 * ‖w - u‖ ^ 2 := by nlinarith [hdist, sq_nonneg ‖w - u‖]
      have hk : (1:ℝ) / ‖w - u‖ ^ 2 ≤ 5 * (1 / (1 + ‖w - u‖ ^ 2)) := by
        rw [show (5:ℝ) * (1 / (1 + ‖w - u‖ ^ 2)) = 5 / (1 + ‖w - u‖ ^ 2) by ring]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h4]
      have h1 : ((((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
            + (Work.LinnikContract.zeroMult χ u : ℝ)) / ‖w - u‖ ^ 2)
          = (((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
            + (Work.LinnikContract.zeroMult χ u : ℝ)) * (1 / ‖w - u‖ ^ 2) :=
        div_eq_mul_one_div _ _
      have h2 : (5:ℝ) * ((((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
            + (Work.LinnikContract.zeroMult χ u : ℝ)) * (1 / (1 + ‖w - u‖ ^ 2)))
          = (((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
            + (Work.LinnikContract.zeroMult χ u : ℝ)) * (5 * (1 / (1 + ‖w - u‖ ^ 2))) := by ring
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_left hk (le_of_lt hpos)
  have hG : Summable (fun u : ℂ =>
      (((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) + (Work.LinnikContract.zeroMult χ u : ℝ))
        * (1 / (1 + ‖w - u‖ ^ 2))) := by
    have h := hsumZ.add hsumL'
    refine h.congr ?_
    intro u; ring
  have hG5 : Summable (fun u : ℂ => 5 *
      ((((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) + (Work.LinnikContract.zeroMult χ u : ℝ))
        * (1 / (1 + ‖w - u‖ ^ 2)))) := hG.mul_left 5
  have hsumTarget : Summable (fun u : ℂ =>
      (((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) + (Work.LinnikContract.zeroMult χ u : ℝ))
        / ‖w - u‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun u => by positivity) (fun u => hpt u) hG5
  refine ⟨hsumTarget, ?_⟩
  have hstep1 : (∑' u : ℂ, (((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
        + (Work.LinnikContract.zeroMult χ u : ℝ)) / ‖w - u‖ ^ 2)
      ≤ ∑' u : ℂ, 5 * ((((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
        + (Work.LinnikContract.zeroMult χ u : ℝ)) * (1 / (1 + ‖w - u‖ ^ 2))) :=
    Summable.tsum_le_tsum (fun u => hpt u) hsumTarget hG5
  have hsplit : (∑' u : ℂ, ((((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
        + (Work.LinnikContract.zeroMult χ u : ℝ)) * (1 / (1 + ‖w - u‖ ^ 2))))
      = (∑' u : ℂ, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ) * (1 / (1 + ‖w - u‖ ^ 2)))
        + (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖w - u‖ ^ 2))) := by
    rw [← Summable.tsum_add hsumZ hsumL']
    apply tsum_congr; intro u; ring
  have hqlog : 0 ≤ Real.log (q:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have h2w : 0 ≤ Real.log (2 + ‖w‖) + 2 := by
    have : 0 ≤ Real.log (2 + ‖w‖) := Real.log_nonneg (by linarith [norm_nonneg w])
    linarith
  calc (∑' u : ℂ, (((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
        + (Work.LinnikContract.zeroMult χ u : ℝ)) / ‖w - u‖ ^ 2)
      ≤ ∑' u : ℂ, 5 * ((((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
        + (Work.LinnikContract.zeroMult χ u : ℝ)) * (1 / (1 + ‖w - u‖ ^ 2))) := hstep1
    _ = 5 * (∑' u : ℂ, ((((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
        + (Work.LinnikContract.zeroMult χ u : ℝ)) * (1 / (1 + ‖w - u‖ ^ 2)))) := tsum_mul_left
    _ = 5 * ((∑' u : ℂ, ((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
          * (1 / (1 + ‖w - u‖ ^ 2)))
        + (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖w - u‖ ^ 2)))) := by
        rw [hsplit]
    _ ≤ 5 * (Cz * (Real.log (2 + ‖w‖) + 2) + Cl * (Real.log (q:ℝ) + Real.log (2 + ‖w‖) + 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith [hbndZ, hbndL']
    _ ≤ (5 * (Cz + Cl) + 1) * (Real.log (q:ℝ) + Real.log (2 + ‖w‖) + 2) := by
        nlinarith [hqlog, h2w, hCzpos, hClpos]



end

end Work.LinnikAreas.FarRepel
