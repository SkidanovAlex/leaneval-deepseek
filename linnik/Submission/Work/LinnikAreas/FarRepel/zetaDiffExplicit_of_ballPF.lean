import Mathlib
import Submission.Work.LinnikAreas.DhK.XiAux
import Submission.Work.LinnikAreas.DhK.ZSBase
import Submission.Work.LinnikAreas.PrincipalZeroCount
import Submission.Work.LinnikAreas.tendsto_finsum_divisor_closedBall_mero
import Submission.Work.LinnikAreas.FarRepel.digammaDerivSeries
import Submission.Work.LinnikAreas.FarRepel.iteratedDeriv_logDeriv_Xi
import Submission.Work.LinnikAreas.xiCZeroInvSqTailBound
import Submission.Commons.Analysis.InfiniteSum.summable_of_finset_tail_bound
import Submission.Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole

open scoped Classical BigOperators Topology
open Filter

namespace Work.LinnikAreas.FarRepel

noncomputable section

/-! ## Helper lemmas -/

/-- `(s/2).re = s.re/2`. -/
private lemma div_two_re (s : ℂ) : (s / 2).re = s.re / 2 := by
  rw [Complex.div_re]; simp [Complex.normSq]; ring

/-- The vanishing multiplicities of the entire completion `Ξ = DhK.Xi` and of
`Λ = completedRiemannZeta` agree everywhere. -/
private lemma analyticOrderNatAt_Xi_eq (u : ℂ) :
    analyticOrderNatAt Work.LinnikAreas.DhK.Xi u
      = analyticOrderNatAt completedRiemannZeta u := by
  by_cases h0 : u = 0
  · subst h0
    have hx : analyticOrderAt Work.LinnikAreas.DhK.Xi 0 = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (by rw [Work.LinnikAreas.DhK.Xi_zero]; norm_num))
    rw [show analyticOrderNatAt Work.LinnikAreas.DhK.Xi 0 = 0 from by
          simp [analyticOrderNatAt, hx],
      analyticOrderNatAt_of_not_analyticAt
        Work.LinnikAreas.not_analyticAt_completedZeta_zero]
  · by_cases h1 : u = 1
    · subst h1
      have hx : analyticOrderAt Work.LinnikAreas.DhK.Xi 1 = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr (by
          rw [show Work.LinnikAreas.DhK.Xi 1 = 1 / 2 by simp [Work.LinnikAreas.DhK.Xi]]
          norm_num))
      rw [show analyticOrderNatAt Work.LinnikAreas.DhK.Xi 1 = 0 from by
            simp [analyticOrderNatAt, hx],
        analyticOrderNatAt_of_not_analyticAt
          Work.LinnikAreas.not_analyticAt_completedZeta_one]
    · exact Work.LinnikAreas.analyticOrderNatAt_xiC_eq u h0 h1

/-- Chain rule: the `k`-th derivative of `z ↦ f (c·z)` at `x` is `c^k` times the `k`-th
derivative of `f` at `c·x`, assuming only that `f` is `C^k` at `c·x`. -/
private lemma iteratedDeriv_comp_mul_left_of_contDiffAt (c : ℂ) (k : ℕ) {f : ℂ → ℂ} {x : ℂ}
    (hf : ContDiffAt ℂ k f (c * x)) :
    iteratedDeriv k (fun z : ℂ => f (c * z)) x = c ^ k * iteratedDeriv k f (c * x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have hcont : Tendsto (fun y : ℂ => c * y) (𝓝 x) (𝓝 (c * x)) :=
      tendsto_const_nhds.mul tendsto_id
    have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℂ (k : ℕ∞) f (c * y) :=
      hcont.eventually ((ContDiffAt.eventually hf (by simp)).mono fun y hy => hy.of_le (by simp))
    have heq : iteratedDeriv k (fun z : ℂ => f (c * z)) =ᶠ[𝓝 x]
        fun y => c ^ k * iteratedDeriv k f (c * y) := by
      filter_upwards [hev] with y hy
      exact ih hy
    rw [heq.deriv_eq, deriv_const_mul_field, deriv_comp_mul_left]
    simp only [smul_eq_mul]
    ring

/-- `Gamma` is analytic at every point of the open right half-plane. -/
private lemma analyticAt_Gamma_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    AnalyticAt ℂ Complex.Gamma w := by
  have hsub : Metric.ball w (w.re / 2) ⊆ {z : ℂ | 0 < z.re} := by
    intro z hz
    change 0 < z.re
    have h1 : ‖z - w‖ < w.re / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have h2 : w.re - z.re ≤ ‖z - w‖ := by
      have h3 : w.re - z.re ≤ ‖w - z‖ := by
        simpa only [Complex.sub_re] using Complex.re_le_norm (w - z)
      rwa [norm_sub_rev] at h3
    linarith only [hw, h1, h2]
  have hdiff : DifferentiableOn ℂ Complex.Gamma (Metric.ball w (w.re / 2)) := by
    intro z hz
    exact (Complex.differentiableAt_Gamma z (by
      intro m h
      have hzre : 0 < z.re := hsub hz
      have hzm : z.re = -((m : ℝ)) := by rw [h]; simp
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith only [hzre, hzm, hm])).differentiableWithinAt
  exact (hdiff.analyticOnNhd Metric.isOpen_ball) w (Metric.mem_ball_self (by positivity))

/-- The `k`-th derivative of `z ↦ digamma (z/2)` is `(1/2)^k` times the `k`-th derivative of
digamma at `z/2`. -/
private lemma iteratedDeriv_digamma_div_two (k : ℕ) {w : ℂ} (hw : 0 < w.re) :
    iteratedDeriv k (fun z : ℂ => Complex.digamma (z / 2)) w
      = (1 / 2 : ℂ) ^ k * iteratedDeriv k Complex.digamma (w / 2) := by
  have hw2 : 0 < (w / 2).re := by rw [div_two_re]; linarith
  have hana : AnalyticAt ℂ Complex.digamma (w / 2) := by
    have hG : AnalyticAt ℂ Complex.Gamma (w / 2) := analyticAt_Gamma_of_re_pos hw2
    have hne : Complex.Gamma (w / 2) ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro m h
      have hre : (w / 2).re = -((m : ℝ)) := by rw [h]; simp
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith only [hre, hm, hw2]
    have h1 : AnalyticAt ℂ (deriv Complex.Gamma / Complex.Gamma) (w / 2) := hG.deriv.div hG hne
    have hfun : Complex.digamma = deriv Complex.Gamma / Complex.Gamma := rfl
    rw [hfun]
    exact h1
  have hfun : (fun z : ℂ => Complex.digamma (z / 2))
      = fun z : ℂ => Complex.digamma ((2 : ℂ)⁻¹ * z) := by
    funext z; congr 1; rw [div_eq_mul_inv, mul_comm]
  have h3 : (2 : ℂ)⁻¹ * w = w / 2 := by ring
  have hdig : ContDiffAt ℂ k Complex.digamma ((2 : ℂ)⁻¹ * w) := by
    rw [h3]; exact hana.contDiffAt
  have h4 : (1 / 2 : ℂ) ^ k = ((2 : ℂ)⁻¹) ^ k := by simp only [one_div]
  have hchain := iteratedDeriv_comp_mul_left_of_contDiffAt (2 : ℂ)⁻¹ k hdig
  rw [h3] at hchain
  rw [hfun, h4]
  exact hchain

/-- **Derivatives of `logDeriv Gammaℝ` as a Hurwitz-zeta type series.** -/
private lemma iteratedDeriv_logDeriv_GammaR (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv k (logDeriv Complex.Gammaℝ) s
      = (-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ)
        * (∑' n : ℕ, (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1)) := by
  have hsre : 0 < s.re := by linarith
  have hk0 : 0 < k := hk
  have hw2 : 0 < (s / 2).re := by rw [div_two_re]; linarith
  have hev : logDeriv Complex.Gammaℝ =ᶠ[𝓝 s]
      fun z : ℂ => (-(Complex.log (Real.pi : ℂ)) / 2) + (1 / 2) * Complex.digamma (z / 2) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hsre] with z hz
    have hz2 : ∀ m : ℕ, z / 2 ≠ -((m : ℕ) : ℂ) := by
      intro m h
      have hre : (z / 2).re = -((m : ℝ)) := by rw [h]; simp
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hzre : 0 < (z / 2).re := by rw [div_two_re]; linarith
      linarith only [hre, hm, hzre]
    rw [Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole z hz2]
    ring
  rw [hev.iteratedDeriv_eq k]
  rw [iteratedDeriv_const_add hk0]
  rw [iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_digamma_div_two k (w := s) hsre]
  have hHas := digammaDerivSeries k hk hw2
  have hterm : ∀ n : ℕ, (1 / (s / 2 + (n : ℂ))) ^ (k + 1)
      = (2 : ℂ) ^ (k + 1) * (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1) := by
    intro n
    have hden : s / 2 + (n : ℂ) = (s + ((2 * n : ℕ) : ℂ)) / 2 := by push_cast; ring
    rw [hden, div_div_eq_mul_div, one_mul,
      show (2 : ℂ) / (s + ((2 * n : ℕ) : ℂ))
        = 2 * (1 / (s + ((2 * n : ℕ) : ℂ))) by ring, mul_pow]
  have hHas' : HasSum (fun n : ℕ =>
      ((-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ) * (2 : ℂ) ^ (k + 1))
        * (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1))
      (iteratedDeriv k Complex.digamma (s / 2)) :=
    hHas.congr_fun fun n => by rw [hterm n]; ring
  have hval : iteratedDeriv k Complex.digamma (s / 2)
      = ((-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ) * (2 : ℂ) ^ (k + 1))
        * (∑' n : ℕ, (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1)) := by
    rw [← hHas'.tsum_eq, tsum_mul_left]
  rw [hval]
  have hpow : (1 / 2 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (k + 1) = 1 := by
    rw [← mul_pow]; norm_num
  have hkey : (1 / 2 : ℂ) * ((1 / 2) ^ k * (((-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ)
        * (2 : ℂ) ^ (k + 1)) * (∑' n : ℕ, (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1))))
      = ((1 / 2 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (k + 1))
          * ((-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ)
              * (∑' n : ℕ, (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1))) := by
    rw [pow_succ]; ring
  rw [hkey, hpow, one_mul]

/-- **Summability of the trivial-zero series and the shift `n ↦ n+1`.** -/
private lemma tsum_inv_add_two_shift (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1)) ∧
      (∑' n : ℕ, (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1))
        = (1 / s) ^ (k + 1)
          + (∑' n : ℕ, (1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ (k + 1)) := by
  have hg : Summable (fun n : ℕ => (1 / (n : ℝ)) ^ (k + 1)) := by
    rw [show (fun n : ℕ => (1 / (n : ℝ)) ^ (k + 1))
        = fun n : ℕ => 1 / (n : ℝ) ^ (k + 1) from funext fun n => one_div_pow _ _]
    exact Real.summable_one_div_nat_pow.mpr (by omega : 1 < k + 1)
  have hsumm : Summable (fun n : ℕ => (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1)) := by
    refine Summable.of_norm_bounded_eventually_nat hg ?_
    filter_upwards [eventually_ge_atTop (⌈‖s‖⌉₊ + 1)] with n hn
    have hsle : ‖s‖ ≤ (n : ℝ) := by
      have h1 : ‖s‖ ≤ (⌈‖s‖⌉₊ : ℝ) := Nat.le_ceil ‖s‖
      have h2 : (⌈‖s‖⌉₊ : ℝ) ≤ (n : ℝ) := by
        have : (⌈‖s‖⌉₊ : ℕ) ≤ n := le_trans (Nat.le_succ _) hn
        exact_mod_cast this
      linarith
    have hnpos : 0 < (n : ℝ) := by
      have h3 : (⌈‖s‖⌉₊ : ℕ) + 1 ≤ n := hn
      have h4 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans (Nat.le_add_left 1 _) h3)
      linarith
    have h2n : (2 : ℝ) * n - ‖s‖ ≤ ‖s + ((2 * n : ℕ) : ℂ)‖ := by
      have h := norm_sub_le (s + ((2 * n : ℕ) : ℂ)) s
      simp only [add_sub_cancel_left] at h
      have hcast : ‖((2 * n : ℕ) : ℂ)‖ = 2 * (n : ℝ) := by
        rw [Complex.norm_natCast]; push_cast; ring
      rw [hcast] at h
      linarith
    have hle : (n : ℝ) ≤ ‖s + ((2 * n : ℕ) : ℂ)‖ := by linarith
    rw [norm_pow, norm_div, norm_one]
    exact pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le hnpos hle) (k + 1)
  refine ⟨hsumm, ?_⟩
  rw [hsumm.tsum_eq_zero_add]
  congr 1
  rw [show ((2 * 0 : ℕ) : ℂ) = 0 by norm_num, add_zero]

/-- **Absolute summability of the zeta zero sum.** -/
private lemma xiZeroSum_summable (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun u : ℂ =>
      (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ) * (1 / (s - u)) ^ (k + 1)) := by
  have hδ : 0 < s.re - 1 := by linarith
  have hfar : ∀ u : ℂ, Work.LinnikAreas.DhK.Xi u = 0 → s.re - 1 ≤ ‖s - u‖ := by
    intro u hu
    have hle : u.re ≤ 1 := Work.LinnikAreas.DhK.Xi_zero_re_le_one hu
    have hre : s.re - 1 ≤ (s - u).re := by simp only [Complex.sub_re]; linarith
    calc s.re - 1 ≤ (s - u).re := hre
      _ ≤ ‖s - u‖ := Complex.re_le_norm _
  have hfin : ({u : ℂ | analyticOrderNatAt Work.LinnikAreas.DhK.Xi u ≠ 0 ∧ ‖u‖ ≤ 2} : Set ℂ).Finite := by
    have h1 : (Function.support (fun u : ℂ =>
        MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall 0 2) u)).Finite :=
      (MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall 0 2)).finiteSupport
        (isCompact_closedBall 0 2)
    refine h1.subset ?_
    intro u hu
    obtain ⟨hord, hnorm⟩ := hu
    rw [Function.mem_support]
    have hmem : u ∈ Metric.closedBall (0 : ℂ) 2 := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hnorm
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast
      (Work.LinnikAreas.DhK.Xi_analyticOnNhd _) hmem]
    exact_mod_cast hord
  obtain ⟨C0, hC0pos, hC0⟩ := Work.LinnikAreas.xiCZeroInvSqTailBound
  let A : ℝ := max ((2 : ℝ) ^ (k + 1)) ((2 * ‖s‖ + 2) ^ 2 / (s.re - 1) ^ (k + 1))
  have hAnn : 0 ≤ A := le_trans (by positivity) (le_max_left _ _)
  set f : ℂ → ℝ := fun u =>
    (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) * ‖(1 / (s - u)) ^ (k + 1)‖ with hfdef
  have hfnn : ∀ u : ℂ, 0 ≤ f u := by intro u; rw [hfdef]; positivity
  have hsmall : ∃ c : ℝ, ∀ t : Finset ℂ, (∀ u ∈ t, ‖u‖ ≤ 2) → ∑ u ∈ t, f u ≤ c := by
    refine ⟨∑ u ∈ hfin.toFinset, f u, ?_⟩
    intro t ht
    calc ∑ u ∈ t, f u ≤ ∑ u ∈ t ∪ hfin.toFinset, f u :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun i _ _ => hfnn i)
      _ = ∑ u ∈ hfin.toFinset, f u := by
          refine (Finset.sum_subset Finset.subset_union_right ?_).symm
          intro u hu hnot
          have hut : u ∈ t := by
            rcases Finset.mem_union.mp hu with h | h
            · exact h
            · exact absurd h hnot
          have h0 : analyticOrderNatAt Work.LinnikAreas.DhK.Xi u = 0 := by
            by_contra hc
            exact hnot (by rw [Set.Finite.mem_toFinset]; exact ⟨hc, ht u hut⟩)
          rw [hfdef]; simp [h0]
  have htail : ∀ t : Finset ℂ, (∀ u ∈ t, 2 < ‖u‖) → ∑ u ∈ t, f u ≤ A * C0 := by
    intro t ht
    have hpt : ∀ u ∈ t, f u ≤ A * ((analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) / ‖u‖ ^ 2) := by
      intro u hu
      by_cases hord : analyticOrderNatAt Work.LinnikAreas.DhK.Xi u = 0
      · rw [hfdef]; simp [hord]
      · have hzu : Work.LinnikAreas.DhK.Xi u = 0 :=
          apply_eq_zero_of_analyticOrderNatAt_ne_zero hord
        have hdist : s.re - 1 ≤ ‖s - u‖ := hfar u hzu
        have h2u : 2 ≤ ‖u‖ := le_of_lt (ht u hu)
        have hupos : 0 < ‖u‖ := by linarith
        have hden : 0 < ‖s - u‖ := lt_of_lt_of_le hδ hdist
        have hb : ‖(1 / (s - u)) ^ (k + 1)‖ ≤ A / ‖u‖ ^ 2 := by
          rw [norm_pow, norm_div, norm_one]
          rcases lt_or_ge (2 * ‖s‖ + 2) ‖u‖ with hlt | hge
          · have htri : ‖u‖ - ‖s‖ ≤ ‖s - u‖ := by
              have h := abs_norm_sub_norm_le u s
              rw [norm_sub_rev u s] at h
              linarith [le_abs_self (‖u‖ - ‖s‖)]
            have hhalf : ‖u‖ / 2 ≤ ‖s - u‖ := by linarith only [htri, hlt]
            have hle1 : (1 : ℝ) / ‖s - u‖ ≤ 2 / ‖u‖ := by
              rw [div_le_div_iff₀ hden hupos]; linarith only [hhalf]
            calc (1 / ‖s - u‖) ^ (k + 1) ≤ (2 / ‖u‖) ^ (k + 1) :=
                  pow_le_pow_left₀ (by positivity) hle1 _
              _ = (2 : ℝ) ^ (k + 1) / ‖u‖ ^ (k + 1) := by rw [div_pow]
              _ ≤ (2 : ℝ) ^ (k + 1) / ‖u‖ ^ 2 :=
                  div_le_div_of_nonneg_left (by positivity) (by positivity)
                    (pow_le_pow_right₀ (by linarith : 1 ≤ ‖u‖) (by omega : 2 ≤ k + 1))
              _ ≤ A / ‖u‖ ^ 2 :=
                  div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
          · have hun : ‖u‖ ^ 2 ≤ A * (s.re - 1) ^ (k + 1) := by
              have h1 : (2 * ‖s‖ + 2) ^ 2 ≤ A * (s.re - 1) ^ (k + 1) := by
                have hA : (2 * ‖s‖ + 2) ^ 2 / (s.re - 1) ^ (k + 1) ≤ A := le_max_right _ _
                exact (div_le_iff₀ (pow_pos hδ _)).mp hA
              have h2 : ‖u‖ ^ 2 ≤ (2 * ‖s‖ + 2) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg u) hge 2
              linarith
            have hfin2 : (1 / (s.re - 1)) ^ (k + 1) ≤ A / ‖u‖ ^ 2 := by
              rw [one_div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
              linarith
            calc (1 / ‖s - u‖) ^ (k + 1) ≤ (1 / (s.re - 1)) ^ (k + 1) :=
                  pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le hδ hdist) _
              _ ≤ A / ‖u‖ ^ 2 := hfin2
        calc (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) * ‖(1 / (s - u)) ^ (k + 1)‖
            ≤ (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) * (A / ‖u‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
          _ = A * ((analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) / ‖u‖ ^ 2) := by ring
    calc ∑ u ∈ t, f u
        ≤ ∑ u ∈ t, A * ((analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) / ‖u‖ ^ 2) :=
          Finset.sum_le_sum hpt
      _ = A * ∑ u ∈ t, ((analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ) / ‖u‖ ^ 2) := by
          rw [Finset.mul_sum]
      _ ≤ A * C0 := mul_le_mul_of_nonneg_left (hC0 t ht) hAnn
  have hsumm_f : Summable f :=
    Commons.Analysis.InfiniteSum.summable_of_finset_tail_bound hfnn hsmall htail
  refine Summable.of_norm ?_
  rw [show (fun u : ℂ => ‖(analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ)
        * (1 / (s - u)) ^ (k + 1)‖) = f from funext fun u => by
      rw [hfdef, norm_mul, Complex.norm_natCast]]
  exact hsumm_f

/-- The elementary algebraic rearrangement closing the proof. -/
private lemma zetaDiff_alg (c : ℂ) (hc : c ≠ 0) (A B T Z : ℂ) :
    -(1 / c) * ((-1 : ℂ) * c * A + (-1 : ℂ) * c * B + c * (A + T) + Z)
      = B - T - (1 / c) * Z := by
  have hcc : (1 / c) * c = 1 := by rw [one_div, inv_mul_cancel₀ hc]
  have hkey : (1 / c) * ((-1 : ℂ) * c * A + (-1 : ℂ) * c * B + c * (A + T) + Z)
      = (T - B) + (1 / c) * Z := by
    rw [show (-1 : ℂ) * c * A + (-1 : ℂ) * c * B + c * (A + T) + Z = c * (T - B) + Z by
      ring]
    rw [mul_add, ← mul_assoc, hcc, one_mul]
  rw [show -(1 / c) * ((-1 : ℂ) * c * A + (-1 : ℂ) * c * B + c * (A + T) + Z)
      = -((1 / c) * ((-1 : ℂ) * c * A + (-1 : ℂ) * c * B + c * (A + T) + Z)) by ring, hkey]
  ring
/-- **Differentiated explicit formula for the Riemann zeta factor, tsum form.** (module `Submission.Work.LinnikAreas.FarRepel.zetaDiffExplicit_of_ballPF`; declare in `namespace Work.LinnikAreas.FarRepel`.)

`Ξ = 1/2 + (1/2)·s(s-1)·Λ₀(s)` is the entire completion of the Riemann zeta function.  Assume the
`k`-th order partial-fraction identity for `Ξ` **as a hypothesis** (ball-limit form, the classical
Hadamard partial fraction; it is proved separately):

`hPF : ∀ s, Ξ s ≠ 0 → Tendsto (fun R => (-1)^k k! · ∑ᶠ_{‖u‖≤R} divisor Ξ (ball R) u · (1/(s-u))^{k+1}) atTop (𝓝 ((logDeriv Ξ)^{(k)} s))`.

Then for `k ≥ 1` odd and `1 < Re s`:

`(∑' u, ord_u(Λ) · (1/(s-u))^{k+1}) + (∑' n, (1/(s+2n+2))^{k+1}) = 1/(s-1)^{k+1} - (1/k!)·((logDeriv ζ)^{(k)})(s)`

(in particular the first family is summable), where `Λ = completedRiemannZeta` and
`ord_u(Λ) = analyticOrderNatAt Λ u` is the multiplicity of `u` as a non-trivial zero of `ζ`.
This is the `ζ`-half of the identity (Lagarias–Montgomery–Odlyzko p. 289; Kadiri–Ng–Wong
arXiv:1902.08640 (2.5)).

PROOF ROUTE: (i) the ball divisor sums of `Ξ` are summable against `Φ u = (1/(s-u))^{k+1}`
(`DhK.Xi_zeroCount_L` + `Commons.Analysis.InfiniteSum.summable_of_finset_tail_bound`, using that
every zero of `Ξ` lies in `0 < Re < 1` — from `Work.LinnikAreas.completedRiemannZeta_zero_strip`
and `DhK.Xi_eq_half_mul` — and that `‖Φ u‖ ≤ A/‖u‖²` for `‖u‖ ≥ 2`), so `hPF` combined with
`Work.LinnikAreas.tendsto_finsum_divisor_closedBall_mero` gives
`∑'_u ord_u(Ξ)·(1/(s-u))^{k+1} = (-1)^k · (1/k!) · ((logDeriv Ξ)^{(k)})(s)`  [for odd `k`, `(-1)^k = -1`];
(ii) `analyticOrderNatAt completedRiemannZeta u = analyticOrderNatAt Ξ u` for every `u` (from
`DhK.Xi_eq_half_mul` off `{0,1}`, `DhK.Xi 0 = DhK.Xi 1 = 1/2 ≠ 0`, and non-vanishing of `(1/2)s(s-1)`
off `{0,1}`);
(iii) `Work.LinnikAreas.DhK.Xi_logDeriv` (`logDeriv Ξ = 1/s + 1/(s-1) + logDeriv Gammaℝ + logDeriv ζ`
on `Re s > 1`) turns the identity for `logDeriv Ξ` into one for `logDeriv ζ`: the `k`-th derivative of
`1/s + 1/(s-1)` is `(-1)^k k!(1/s^{k+1} + 1/(s-1)^{k+1})`, and the `k`-th derivative of
`logDeriv Gammaℝ` is computed from the digamma series
(`Work.LinnikAreas.FarRepel.digammaDerivSeries`, already proved, plus
`Complex.Gammaℝ = fun z => π^{-z/2}Γ(z/2)` and the chain rule) as
`(-1)^{k+1} k! ∑'_n (1/(s+2n))^{k+1} = k!∑'_n (1/(s+2n))^{k+1}` for odd `k`.  Finally
`1/s^{k+1} - ∑'_{n≥0}(1/(s+2n))^{k+1} = -∑'_{n≥1}(1/(s+2n))^{k+1}` gives the stated form. -/
theorem zetaDiffExplicit_of_ballPF (k : ℕ) (hk : 1 ≤ k) (hodd : k % 2 = 1)
    (hPF : ∀ s : ℂ, Work.LinnikAreas.DhK.Xi s ≠ 0 →
      Filter.Tendsto (fun R : ℝ => ((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
          (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
              (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u)) ^ (k + 1)))
        Filter.atTop (nhds (iteratedDeriv k (logDeriv Work.LinnikAreas.DhK.Xi) s)))
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun u : ℂ => (analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ (k + 1)) ∧
    (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ (k + 1))
      + (∑' n : ℕ, (1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ (k + 1))
      = 1 / (s - 1) ^ (k + 1)
        - (1 / (k.factorial : ℂ)) * iteratedDeriv k (logDeriv riemannZeta) s := by
  have hkodd : Odd k := Nat.odd_iff.mpr hodd
  have hsign : (-1 : ℂ) ^ k = -1 := hkodd.neg_one_pow
  have hsign2 : (-1 : ℂ) ^ (k + 1) = 1 := hkodd.add_one.neg_one_pow
  have hfact : ((k.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hsumXi : Summable (fun u : ℂ =>
      (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ) * (1 / (s - u)) ^ (k + 1)) :=
    xiZeroSum_summable k hk hs
  have hsumZeta : Summable (fun u : ℂ =>
      (analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ (k + 1)) := by
    rw [show (fun u : ℂ => (analyticOrderNatAt completedRiemannZeta u : ℂ)
          * (1 / (s - u)) ^ (k + 1))
        = (fun u : ℂ => (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ)
          * (1 / (s - u)) ^ (k + 1))
        from funext fun u => by rw [analyticOrderNatAt_Xi_eq u]]
    exact hsumXi
  have htsumZeta : (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℂ)
        * (1 / (s - u)) ^ (k + 1))
      = ∑' u : ℂ, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ)
        * (1 / (s - u)) ^ (k + 1) :=
    tsum_congr fun u => by rw [analyticOrderNatAt_Xi_eq u]
  have hdivuniv : ∀ u : ℂ, MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi Set.univ u
      = (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℤ) := fun u =>
    Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast
      (Work.LinnikAreas.DhK.Xi_analyticOnNhd Set.univ) (Set.mem_univ u)
  have hsumDiv : Summable (fun u : ℂ =>
      (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi Set.univ) u : ℤ) : ℂ)
        * (1 / (s - u)) ^ (k + 1)) := by
    rw [show (fun u : ℂ => (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi Set.univ) u : ℤ) : ℂ)
          * (1 / (s - u)) ^ (k + 1))
        = (fun u : ℂ => (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ)
          * (1 / (s - u)) ^ (k + 1))
        from funext fun u => by rw [hdivuniv u]; simp]
    exact hsumXi
  have htend := Work.LinnikAreas.tendsto_finsum_divisor_closedBall_mero
    (Work.LinnikAreas.DhK.Xi_meromorphicOn Set.univ) hsumDiv
  have hPF' := hPF s (Work.LinnikAreas.DhK.Xi_ne_zero_of_one_lt_re hs)
  have huniq : ((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
      (∑' u : ℂ, (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi Set.univ) u : ℤ) : ℂ)
        * (1 / (s - u)) ^ (k + 1))
      = iteratedDeriv k (logDeriv Work.LinnikAreas.DhK.Xi) s :=
    tendsto_nhds_unique (htend.const_mul _) hPF'
  have htsumDiv : (∑' u : ℂ, (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi Set.univ) u : ℤ) : ℂ)
        * (1 / (s - u)) ^ (k + 1))
      = ∑' u : ℂ, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ)
        * (1 / (s - u)) ^ (k + 1) :=
    tsum_congr fun u => by rw [hdivuniv u]; simp
  have hSΞ : (∑' u : ℂ, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ)
        * (1 / (s - u)) ^ (k + 1))
      = -(1 / (k.factorial : ℂ)) * iteratedDeriv k (logDeriv Work.LinnikAreas.DhK.Xi) s := by
    have hb := huniq
    rw [htsumDiv] at hb
    have hneg : (-(k.factorial : ℂ)) * (∑' u : ℂ, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ)
          * (1 / (s - u)) ^ (k + 1))
        = iteratedDeriv k (logDeriv Work.LinnikAreas.DhK.Xi) s := by
      simpa only [hsign, neg_one_mul] using hb
    have h1 : -((k.factorial : ℂ) * (∑' u : ℂ, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ)
          * (1 / (s - u)) ^ (k + 1)))
        = iteratedDeriv k (logDeriv Work.LinnikAreas.DhK.Xi) s := by
      rw [← hneg]; ring
    have h2 : (k.factorial : ℂ) * (∑' u : ℂ, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ)
          * (1 / (s - u)) ^ (k + 1))
        = -iteratedDeriv k (logDeriv Work.LinnikAreas.DhK.Xi) s := by
      simpa using congrArg Neg.neg h1
    have h3 : (∑' u : ℂ, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ)
          * (1 / (s - u)) ^ (k + 1))
        = ((k.factorial : ℂ))⁻¹ * (-iteratedDeriv k (logDeriv Work.LinnikAreas.DhK.Xi) s) := by
      have h4 := congrArg (fun x : ℂ => (1 / (k.factorial : ℂ)) * x) h2
      rwa [← mul_assoc, one_div, inv_mul_cancel₀ hfact, one_mul] at h4
    rw [h3]
    ring
  have hderiv := Work.LinnikAreas.FarRepel.iteratedDeriv_logDeriv_Xi k hk hs
  have hG := iteratedDeriv_logDeriv_GammaR k hk hs
  have hshift := tsum_inv_add_two_shift k hk hs
  have hG' : iteratedDeriv k (logDeriv Complex.Gammaℝ) s
      = (k.factorial : ℂ) * (∑' n : ℕ, (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1)) := by
    rw [hG, hsign2, one_mul]
  refine ⟨hsumZeta, ?_⟩
  have hkey : (∑' u : ℂ, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℂ)
        * (1 / (s - u)) ^ (k + 1))
      = (1 / (s - 1)) ^ (k + 1)
        - (∑' n : ℕ, (1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ (k + 1))
        - (1 / (k.factorial : ℂ)) * iteratedDeriv k (logDeriv riemannZeta) s := by
    rw [hSΞ, hderiv, hG', hshift.2, hsign]
    exact zetaDiff_alg (k.factorial : ℂ) hfact _ _ _ _
  rw [htsumZeta, hkey]
  simp only [one_div_pow]
  ring

end

end Work.LinnikAreas.FarRepel
