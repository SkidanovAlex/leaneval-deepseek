import Mathlib
import Submission.Work.EQ.FatouDefs
import Submission.Work.EQ.Fatou.pk_basic
import Submission.Work.EQ.Fatou.cauchy_kernel

/-!
# The near part of the Poisson integral

`Work.EQ.pk r ψ = (1 - r²)/(1 - 2 r cos ψ + r²)` concentrates at `ψ ≡ 0 (mod 2π)` as `r → 1⁻`.
This module proves the quantitative statement needed for the a.e. convergence of Poisson
integrals: if `g ≥ 0` has *bounded running averages* on `(0, δ]`, i.e. `∫₀^s g ≤ 2 ε s` for all
`s ∈ (0, δ]`, then for every `r ∈ [1/2, 1)`

`∫₀^δ pk r ψ · g ψ dψ ≤ 100 ε`.

The proof dominates the kernel by the Cauchy kernel `2(1-r)/((1-r)² + (2/π²)ψ²)` and integrates
by parts against the running integral of `g` (`AbsolutelyContinuousOnInterval`).
-/

set_option maxHeartbeats 1000000

namespace Work.EQ.Fatou

open MeasureTheory Set intervalIntegral Filter

/-- The Poisson kernel is dominated by the Cauchy kernel with the same scale. -/
lemma pk_le_cauchy (r ψ : ℝ) (hr : 1/2 ≤ r) (hr1 : r < 1) (hψ : |ψ| ≤ Real.pi) :
    Work.EQ.pk r ψ ≤ 2 * (1 - r) / ((1 - r) ^ 2 + (2 / Real.pi ^ 2) * ψ ^ 2) := by
  have hr0 : 0 ≤ r := by linarith
  have hcos : Real.cos ψ ≤ 1 - 2 / Real.pi ^ 2 * ψ ^ 2 := Real.cos_le_one_sub_mul_cos_sq hψ
  set a : ℝ := 1 - r with ha
  set c : ℝ := 2 / Real.pi ^ 2 with hc
  have ha0 : 0 < a := by rw [ha]; linarith
  have hc0 : 0 < c := by rw [hc]; positivity
  have hstep : a ^ 2 + c * ψ ^ 2 ≤ 1 - 2 * r * Real.cos ψ + r ^ 2 := by
    have hcos' : Real.cos ψ ≤ 1 - c * ψ ^ 2 := by rw [hc]; exact hcos
    have h6 : 1 - 2 * r * (1 - c * ψ ^ 2) + r ^ 2 = a ^ 2 + 2 * r * c * ψ ^ 2 := by
      rw [ha, hc]; ring
    have h5 : 1 - 2 * r * (1 - c * ψ ^ 2) + r ^ 2 ≤ 1 - 2 * r * Real.cos ψ + r ^ 2 := by
      nlinarith [hcos', hr0]
    have h7 : a ^ 2 + c * ψ ^ 2 ≤ a ^ 2 + 2 * r * c * ψ ^ 2 := by
      have h3 : (1:ℝ) ≤ 2 * r := by linarith
      have h4 : 0 ≤ c * ψ ^ 2 := by positivity
      nlinarith
    calc a ^ 2 + c * ψ ^ 2 ≤ a ^ 2 + 2 * r * c * ψ ^ 2 := h7
      _ = 1 - 2 * r * (1 - c * ψ ^ 2) + r ^ 2 := h6.symm
      _ ≤ 1 - 2 * r * Real.cos ψ + r ^ 2 := h5
  have hnum : 1 - r ^ 2 ≤ 2 * a := by
    have h1 : 1 - r ^ 2 = a * (1 + r) := by rw [ha]; ring
    rw [h1]
    nlinarith [hr0, hr1, ha0]
  have hDpos : 0 < 1 - 2 * r * Real.cos ψ + r ^ 2 := lt_of_lt_of_le (by positivity) hstep
  have hden : 0 < a ^ 2 + c * ψ ^ 2 := by positivity
  have hmain : (1 - r ^ 2) / (1 - 2 * r * Real.cos ψ + r ^ 2) ≤ 2 * a / (a ^ 2 + c * ψ ^ 2) :=
    calc (1 - r ^ 2) / (1 - 2 * r * Real.cos ψ + r ^ 2)
        ≤ (2 * a) / (1 - 2 * r * Real.cos ψ + r ^ 2) :=
          div_le_div_of_nonneg_right hnum hDpos.le
      _ ≤ (2 * a) / (a ^ 2 + c * ψ ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) hden hstep
  simpa only [Work.EQ.pk, ha, hc] using hmain

/-- **The near-part bound.**  If a nonnegative `g` has running integrals bounded by `2εs` on
`(0, δ]` (`δ ≤ π`), then `∫₀^δ pk r ψ g ψ` is at most `100 ε` uniformly in `r ∈ [1/2, 1)`. -/
theorem pk_near_part_bound (δ ε : ℝ) (hδ : 0 < δ) (hδπ : δ ≤ Real.pi) (hε : 0 < ε) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume (0:ℝ) δ)
    (hg0 : ∀ x ∈ Set.Icc (0:ℝ) δ, 0 ≤ g x)
    (havg : ∀ s ∈ Set.Ioc (0:ℝ) δ, ∫ x in (0:ℝ)..s, g x ≤ 2 * ε * s) :
    ∀ r ∈ Set.Ico (1/2 : ℝ) 1,
      ∫ ψ in (0:ℝ)..δ, Work.EQ.pk r ψ * g ψ ≤ 100 * ε := by
  intro r hr
  have hr12 : (1:ℝ)/2 ≤ r := hr.1
  have hr1 : r < 1 := hr.2
  have hr0 : 0 ≤ r := by linarith
  set a : ℝ := 1 - r with ha
  set c : ℝ := 2 / Real.pi ^ 2 with hc
  have ha0 : 0 < a := by rw [ha]; linarith
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hc9 : 1/9 ≤ c := by
    rw [hc, le_div_iff₀ (by positivity)]
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hsqrt_inv : 1 / Real.sqrt c ≤ 3 := by
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hc0)]
    have h : (1:ℝ)/3 ≤ Real.sqrt c := by
      rw [Real.le_sqrt (by norm_num) (le_of_lt hc0)]
      norm_num
      linarith
    linarith
  -- pointwise domination of the kernels
  have hpk_le : ∀ ψ ∈ Set.Icc (0:ℝ) δ, Work.EQ.pk r ψ ≤ cauchyK a c ψ := by
    intro ψ hψ
    have hψπ : |ψ| ≤ Real.pi := by
      rw [abs_le]
      exact ⟨by linarith [hψ.1], le_trans hψ.2 hδπ⟩
    have h := pk_le_cauchy r ψ hr12 hr1 hψπ
    rw [cauchyK, ha, hc]
    exact h
  have hint_pk : IntervalIntegrable (fun ψ : ℝ => Work.EQ.pk r ψ * g ψ) volume (0:ℝ) δ :=
    (hg.mul_continuousOn (continuous_pk r hr0 hr1).continuousOn).congr (fun x _ => by ring)
  have hint_K : IntervalIntegrable (fun ψ : ℝ => cauchyK a c ψ * g ψ) volume (0:ℝ) δ :=
    (hg.mul_continuousOn (cauchyK_continuous ha0 hc0.le).continuousOn).congr
      (fun x _ => by ring)
  have hmono : ∫ ψ in (0:ℝ)..δ, Work.EQ.pk r ψ * g ψ
      ≤ ∫ ψ in (0:ℝ)..δ, cauchyK a c ψ * g ψ :=
    integral_mono_on hδ.le hint_pk hint_K
      (fun x hx => mul_le_mul_of_nonneg_right (hpk_le x hx) (hg0 x hx))
  -- integration by parts
  have hAac : AbsolutelyContinuousOnInterval (fun s : ℝ => ∫ x in (0:ℝ)..s, g x) 0 δ :=
    hg.absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc
  have hKac : AbsolutelyContinuousOnInterval (cauchyK a c) 0 δ := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    have hK : cauchyK a c = fun ψ : ℝ => 2 * a / (a ^ 2 + c * ψ ^ 2) :=
      funext (fun ψ => by rw [cauchyK])
    rw [hK]
    apply ContDiffOn.div
    · fun_prop
    · fun_prop
    · intro x hx
      have : 0 < a ^ 2 + c * x ^ 2 := by positivity
      positivity
  have hIBP := hAac.integral_mul_deriv_eq_deriv_mul hKac
  have hAd : ∀ᵐ x ∂volume, x ∈ Set.uIoc (0:ℝ) δ →
      deriv (fun s : ℝ => ∫ v in (0:ℝ)..s, g v) x = g x := by
    filter_upwards [hg.ae_hasDerivAt_integral] with x hx hxu
    exact (hx (uIoc_subset_uIcc hxu) 0 Set.left_mem_uIcc).deriv
  have hA0 : (∫ v in (0:ℝ)..0, g v) = 0 := by simp
  have h1 : (∫ x in (0:ℝ)..δ, (∫ v in (0:ℝ)..x, g v) * deriv (cauchyK a c) x)
      = - ∫ x in (0:ℝ)..δ, cauchyKq a c x * (∫ v in (0:ℝ)..x, g v) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    show (∫ v in (0:ℝ)..x, g v) * deriv (cauchyK a c) x
      = -(cauchyKq a c x * ∫ v in (0:ℝ)..x, g v)
    rw [deriv_cauchyK ha0 hc0.le, cauchyKderiv_eq_neg_q]
    ring
  have h2 : (∫ x in (0:ℝ)..δ, deriv (fun s : ℝ => ∫ v in (0:ℝ)..s, g v) x * cauchyK a c x)
      = ∫ x in (0:ℝ)..δ, g x * cauchyK a c x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hAd] with x hx hxu
    rw [hx hxu]
  have hmain : (∫ x in (0:ℝ)..δ, cauchyKq a c x * (∫ v in (0:ℝ)..x, g v))
      = (∫ x in (0:ℝ)..δ, g x * cauchyK a c x)
        - (∫ v in (0:ℝ)..δ, g v) * cauchyK a c δ := by
    rw [h1, h2] at hIBP
    rw [hA0] at hIBP
    simp only [mul_zero, sub_zero] at hIBP
    linarith [hIBP]
  -- the two bounds
  have hAδ : (∫ v in (0:ℝ)..δ, g v) ≤ 2 * ε * δ := havg δ ⟨hδ, le_rfl⟩
  have hKδ_pos : 0 < cauchyK a c δ := cauchyK_pos ha0 hc0
  have hPδδ : cauchyK a c δ * δ ≤ 1 / Real.sqrt c := by
    have hD : 2 * a * δ * Real.sqrt c ≤ a ^ 2 + c * δ ^ 2 := by
      have h' : 0 ≤ a ^ 2 - 2 * a * (Real.sqrt c * δ) + (Real.sqrt c * δ) ^ 2 := by
        simpa only [sub_sq] using sq_nonneg (a - Real.sqrt c * δ)
      rw [mul_pow, Real.sq_sqrt hc0.le] at h'
      nlinarith [h']
    have hDpos : 0 < a ^ 2 + c * δ ^ 2 := by positivity
    have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
    rw [cauchyK, div_mul_eq_mul_div, div_le_iff₀ hDpos]
    rw [show (1 / Real.sqrt c) * (a ^ 2 + c * δ ^ 2) = (a ^ 2 + c * δ ^ 2) / Real.sqrt c
      by ring]
    rw [le_div_iff₀ hs]
    linarith [hD]
  have hbd1 : (∫ v in (0:ℝ)..δ, g v) * cauchyK a c δ ≤ 6 * ε := by
    have h2 : cauchyK a c δ * δ ≤ 3 := le_trans hPδδ hsqrt_inv
    calc (∫ v in (0:ℝ)..δ, g v) * cauchyK a c δ ≤ (2 * ε * δ) * cauchyK a c δ :=
          mul_le_mul_of_nonneg_right hAδ (le_of_lt hKδ_pos)
      _ = 2 * ε * (cauchyK a c δ * δ) := by ring
      _ ≤ 2 * ε * 3 := by nlinarith [h2, hε]
      _ = 6 * ε := by ring
  have hkern_bound : ∫ x in (0:ℝ)..δ, cauchyKern a c x ≤ 4 * c + 4 / c := by
    set s0 : ℝ := min δ a with hs0
    have hs0pos : 0 < s0 := by rw [hs0]; exact lt_min hδ ha0
    have hs0a : s0 ≤ a := by rw [hs0]; exact min_le_right _ _
    have hKc : Continuous (cauchyKern a c) := cauchyKern_continuous ha0 hc0.le
    -- first piece: `x ≤ s0 ≤ a`, bound by the constant `4c/a`
    have hpk1 : ∀ x ∈ Set.Icc (0:ℝ) s0, cauchyKern a c x ≤ 4 * c / a := by
      intro x hx
      have hx0 : 0 ≤ x := hx.1
      have hxa : x ≤ a := le_trans hx.2 hs0a
      rw [cauchyKern, div_le_iff₀ (by positivity)]
      rw [div_mul_eq_mul_div, le_div_iff₀ ha0]
      have h1 : x ^ 2 ≤ a ^ 2 := by nlinarith [hx0, hxa]
      have h2 : (a ^ 2) ^ 2 ≤ (a ^ 2 + c * x ^ 2) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        nlinarith [hx0, hc0]
      have h3 : a ^ 2 * x ^ 2 ≤ (a ^ 2 + c * x ^ 2) ^ 2 :=
        le_trans (by nlinarith [h1, ha0]) h2
      nlinarith [h3, hx0, ha0, hc0]
    have hpiece1 : ∫ x in (0:ℝ)..s0, cauchyKern a c x ≤ 4 * c := by
      have hval : (∫ x in (0:ℝ)..s0, 4 * c / a) = (4 * c / a) * s0 := by
        rw [intervalIntegral.integral_const]
        ring
      have hle : (4 * c / a) * s0 ≤ 4 * c := by
        have h1 : (4 * c / a) * s0 ≤ (4 * c / a) * a :=
          mul_le_mul_of_nonneg_left hs0a (by positivity)
        have h2 : (4 * c / a) * a = 4 * c := by
          rw [div_mul_cancel₀ _ (ne_of_gt ha0)]
        linarith
      have hres := integral_mono_on hs0pos.le (hKc.intervalIntegrable _ _)
        (intervalIntegrable_const (μ := volume) (c := 4 * c / a)) hpk1
      rw [hval] at hres
      linarith [hres, hle]
    -- second piece
    have hpiece2 : ∫ x in s0..δ, cauchyKern a c x ≤ 4 / c := by
      by_cases hcase : δ ≤ a
      · have hs0eq : s0 = δ := by rw [hs0]; exact min_eq_left hcase
        have hzero : (∫ x in s0..δ, cauchyKern a c x) = 0 := by
          rw [hs0eq, intervalIntegral.integral_same]
        rw [hzero]
        positivity
      · have hlt : a < δ := lt_of_not_ge hcase
        have hs0eq : s0 = a := by rw [hs0]; exact min_eq_right (le_of_lt hlt)
        rw [hs0eq]
        have hb : ∀ x ∈ Set.Icc a δ, cauchyKern a c x ≤ 4 * a / (c * x ^ 2) := by
          intro x hx
          have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
          rw [cauchyKern, div_le_iff₀ (by positivity)]
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          have h1 : (c * x ^ 2) ^ 2 ≤ (a ^ 2 + c * x ^ 2) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by linarith [sq_nonneg a]) 2
          nlinarith [h1, ha0, hx0, sq_nonneg x]
        have hderiv : ∀ x ∈ Set.uIcc a δ,
            HasDerivAt (fun y : ℝ => -(4 * a / c) / y) (4 * a / (c * x ^ 2)) x := by
          intro x hx
          rw [Set.uIcc_of_le (le_of_lt hlt)] at hx
          have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha0 hx.1)
          have hd := (hasDerivAt_const (x := x) (c := -(4 * a / c))).div
            (hasDerivAt_id x) hx0
          simp only [Pi.div_apply, id_eq] at hd
          have hdval : (0 * x - -(4 * a / c) * 1) / x ^ 2 = 4 * a / (c * x ^ 2) := by
            rw [show 0 * x - -(4 * a / c) * 1 = 4 * a / c by ring]
            rw [div_div]
          rw [hdval] at hd
          exact hd
        have hintd : IntervalIntegrable (fun x : ℝ => 4 * a / (c * x ^ 2)) volume a δ := by
          apply ContinuousOn.intervalIntegrable
          apply ContinuousOn.div continuousOn_const
          · fun_prop
          · intro x hx
            rw [Set.uIcc_of_le (le_of_lt hlt)] at hx
            exact mul_ne_zero (ne_of_gt hc0)
              (pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha0 hx.1)))
        have hval : (∫ x in a..δ, 4 * a / (c * x ^ 2)) = 4 * a / c * (1 / a - 1 / δ) := by
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintd]
          ring
        have hle2 : 4 * a / c * (1 / a - 1 / δ) ≤ 4 / c := by
          have h1 : 1 / a - 1 / δ ≤ 1 / a := by
            have : 0 ≤ 1 / δ := by positivity
            linarith
          have h2 : 0 ≤ 4 * a / c := by positivity
          have h3 : 4 * a / c * (1 / a) = 4 / c := by
            rw [div_mul_eq_mul_div, mul_assoc, one_div, mul_inv_cancel₀ (ne_of_gt ha0),
              mul_one]
          calc 4 * a / c * (1 / a - 1 / δ) ≤ 4 * a / c * (1 / a) :=
                mul_le_mul_of_nonneg_left h1 h2
            _ = 4 / c := h3
        calc ∫ x in a..δ, cauchyKern a c x ≤ ∫ x in a..δ, 4 * a / (c * x ^ 2) :=
              integral_mono_on (le_of_lt hlt) (hKc.intervalIntegrable _ _) hintd hb
          _ = 4 * a / c * (1 / a - 1 / δ) := hval
          _ ≤ 4 / c := hle2
    have hsplit : (∫ x in (0:ℝ)..s0, cauchyKern a c x) + (∫ x in s0..δ, cauchyKern a c x)
        = ∫ x in (0:ℝ)..δ, cauchyKern a c x :=
      intervalIntegral.integral_add_adjacent_intervals (hKc.intervalIntegrable _ _)
        (hKc.intervalIntegrable _ _)
    linarith [hsplit, hpiece1, hpiece2]
  have hqA_bound : ∫ x in (0:ℝ)..δ, cauchyKq a c x * (∫ v in (0:ℝ)..x, g v)
      ≤ 2 * ε * (4 * c + 4 / c) := by
    have hAcont : ContinuousOn (fun s : ℝ => ∫ v in (0:ℝ)..s, g v) (Set.uIcc (0:ℝ) δ) :=
      hAac.continuousOn
    have hint_lhs : IntervalIntegrable (fun x : ℝ => cauchyKq a c x * (∫ v in (0:ℝ)..x, g v))
        volume (0:ℝ) δ :=
      (hAcont.intervalIntegrable.mul_continuousOn
        (cauchyKq_continuous ha0 hc0.le).continuousOn).congr (fun x _ => by ring)
    have hint_rhs : IntervalIntegrable (fun x : ℝ => 2 * ε * cauchyKern a c x) volume (0:ℝ) δ :=
      ((cauchyKern_continuous ha0 hc0.le).const_mul (2 * ε)).intervalIntegrable _ _
    have hpoint : ∀ x ∈ Set.Icc (0:ℝ) δ,
        cauchyKq a c x * (∫ v in (0:ℝ)..x, g v) ≤ 2 * ε * cauchyKern a c x := by
      intro x hx
      rcases eq_or_lt_of_le hx.1 with hx0 | hx0
      · rw [← hx0]
        simp [cauchyKq, cauchyKern]
      · have hAx : (∫ v in (0:ℝ)..x, g v) ≤ 2 * ε * x := havg x ⟨hx0, hx.2⟩
        have hqx : 0 ≤ cauchyKq a c x := cauchyKq_nonneg ha0 hc0 (le_of_lt hx0)
        have hkey : 2 * ε * cauchyKern a c x = cauchyKq a c x * (2 * ε * x) := by
          rw [cauchyKern_eq_q_mul]; ring
        rw [hkey]
        exact mul_le_mul_of_nonneg_left hAx hqx
    have hres := integral_mono_on hδ.le hint_lhs hint_rhs hpoint
    have hconst : (∫ x in (0:ℝ)..δ, 2 * ε * cauchyKern a c x)
        = 2 * ε * ∫ x in (0:ℝ)..δ, cauchyKern a c x :=
      intervalIntegral.integral_const_mul _ _
    rw [hconst] at hres
    have hkern_nonneg' : 0 ≤ ∫ x in (0:ℝ)..δ, cauchyKern a c x :=
      intervalIntegral.integral_nonneg hδ.le (fun x hx => cauchyKern_nonneg ha0 hc0)
    nlinarith [hres, hkern_bound, hε, hkern_nonneg']
  have h40 : 4 * c + 4 / c ≤ 40 := by
    have h1 : 4 / c ≤ 36 := by
      rw [div_le_iff₀ hc0]
      nlinarith [hc9]
    have h2 : 4 * c ≤ 4 := by nlinarith [hc1]
    linarith
  calc ∫ ψ in (0:ℝ)..δ, Work.EQ.pk r ψ * g ψ
      ≤ ∫ ψ in (0:ℝ)..δ, cauchyK a c ψ * g ψ := hmono
    _ = ∫ x in (0:ℝ)..δ, g x * cauchyK a c x :=
        intervalIntegral.integral_congr (fun x _ => by ring)
    _ = (∫ v in (0:ℝ)..δ, g v) * cauchyK a c δ
          + ∫ x in (0:ℝ)..δ, cauchyKq a c x * (∫ v in (0:ℝ)..x, g v) := by
        linarith [hmain]
    _ ≤ 6 * ε + 2 * ε * (4 * c + 4 / c) := add_le_add hbd1 hqA_bound
    _ ≤ 100 * ε := by nlinarith [h40, hε]

end Work.EQ.Fatou

namespace Work.EQ.Fatou

open MeasureTheory Set intervalIntegral Filter

lemma integral_add_symm (h : ℝ → ℝ) (θ s : ℝ) (hs : 0 ≤ s)
    (h1 : IntervalIntegrable (fun ψ : ℝ => h (θ + ψ)) volume (0:ℝ) s)
    (h2 : IntervalIntegrable (fun ψ : ℝ => h (θ - ψ)) volume (0:ℝ) s)
    (h3 : IntervalIntegrable h volume (θ - s) (θ + s)) :
    (∫ ψ in (0:ℝ)..s, (h (θ + ψ) + h (θ - ψ))) = ∫ y in (θ - s)..(θ + s), h y := by
  rw [intervalIntegral.integral_add h1 h2]
  have e1 : (∫ ψ in (0:ℝ)..s, h (θ + ψ)) = ∫ y in θ..θ + s, h y := by
    have hh := intervalIntegral.integral_comp_add_right (f := h) (a := (0:ℝ)) (b := s) θ
    simpa only [zero_add, add_zero, add_comm, add_left_comm, add_assoc] using hh
  have e2 : (∫ ψ in (0:ℝ)..s, h (θ - ψ)) = ∫ y in θ - s..θ, h y := by
    have hh := intervalIntegral.integral_comp_sub_left (f := h) (a := (0:ℝ)) (b := s) θ
    simpa only [sub_zero] using hh
  rw [e1, e2, add_comm]
  have hL : IntervalIntegrable h volume θ (θ + s) := by
    refine h3.mono_set ?_
    rw [uIcc_of_le (show θ - s ≤ θ + s by linarith), uIcc_of_le (show θ ≤ θ + s by linarith)]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hR : IntervalIntegrable h volume (θ - s) θ := by
    refine h3.mono_set ?_
    rw [uIcc_of_le (show θ - s ≤ θ + s by linarith), uIcc_of_le (show θ - s ≤ θ by linarith)]
    exact Icc_subset_Icc le_rfl (by linarith)
  exact intervalIntegral.integral_add_adjacent_intervals hR hL

lemma intervalIntegrable_add_const {h : ℝ → ℝ} {θ a b : ℝ}
    (hint : IntervalIntegrable h volume (a + θ) (b + θ)) :
    IntervalIntegrable (fun ψ : ℝ => h (θ + ψ)) volume a b := by
  have hh := hint.comp_add_right θ (by exact enorm_ne_top)
  rw [add_sub_cancel_right, add_sub_cancel_right] at hh
  exact hh.congr (fun x _ => by rw [add_comm])

lemma intervalIntegrable_sub_const {h : ℝ → ℝ} {θ a b : ℝ}
    (hint : IntervalIntegrable h volume (θ - b) (θ - a)) :
    IntervalIntegrable (fun ψ : ℝ => h (θ - ψ)) volume a b := by
  have hh := hint.comp_sub_left θ (by exact enorm_ne_top)
  rw [sub_sub_cancel, sub_sub_cancel] at hh
  exact hh.symm

/-- **The near-part bound, symmetrized.**  The same estimate as `pk_near_part_bound`, but with
the averaging hypothesis expressed through the integrals over the symmetric intervals
`(θ-s, θ+s)` around the base point `θ`, which is the form in which the Lebesgue-point condition
provides it. -/
theorem pk_near_part_shifted (θ δ ε : ℝ) (hδ : 0 < δ) (hδπ : δ ≤ Real.pi) (hε : 0 < ε)
    (h : ℝ → ℝ) (hh0 : ∀ φ, 0 ≤ h φ) (hhint : IntervalIntegrable h volume (θ - δ) (θ + δ))
    (havg : ∀ s ∈ Set.Ioc (0:ℝ) δ, ∫ φ in (θ - s)..(θ + s), h φ ≤ 2 * ε * s) :
    ∀ r ∈ Set.Ico (1/2 : ℝ) 1,
      ∫ φ in (θ - δ)..(θ + δ), Work.EQ.pk r (θ - φ) * h φ ≤ 100 * ε := by
  intro r hr
  have hr0 : 0 ≤ r := by linarith [hr.1]
  have hr1 : r < 1 := hr.2
  have hs0δ : (0:ℝ) ≤ δ := le_of_lt hδ
  have hpkcont : Continuous (fun φ : ℝ => Work.EQ.pk r (θ - φ)) :=
    (continuous_pk r hr0 hr1).comp (by fun_prop)
  have h1 : IntervalIntegrable (fun φ : ℝ => Work.EQ.pk r (θ-φ) * h φ) volume (θ-δ) (θ+δ) :=
    (hhint.mul_continuousOn hpkcont.continuousOn).congr (fun x _ => by ring)
  have hshift := pk_shift_intervalIntegral r θ δ h hs0δ h1
  have hIadd : IntervalIntegrable (fun ψ : ℝ => h (θ + ψ)) volume (0:ℝ) δ := by
    refine intervalIntegrable_add_const (a := (0:ℝ)) (b := δ) ?_
    refine hhint.mono_set ?_
    rw [show (0:ℝ) + θ = θ by ring, show δ + θ = θ + δ by ring,
      uIcc_of_le (show θ - δ ≤ θ + δ by linarith), uIcc_of_le (show θ ≤ θ + δ by linarith)]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hIsub : IntervalIntegrable (fun ψ : ℝ => h (θ - ψ)) volume (0:ℝ) δ := by
    refine intervalIntegrable_sub_const (a := (0:ℝ)) (b := δ) ?_
    refine hhint.mono_set ?_
    rw [show θ - (0:ℝ) = θ by ring, uIcc_of_le (show θ - δ ≤ θ + δ by linarith),
      uIcc_of_le (show θ - δ ≤ θ by linarith)]
    exact Icc_subset_Icc le_rfl (by linarith)
  have hg : IntervalIntegrable (fun ψ : ℝ => h (θ + ψ) + h (θ - ψ)) volume (0:ℝ) δ :=
    hIadd.add hIsub
  have hg0 : ∀ x ∈ Set.Icc (0:ℝ) δ, 0 ≤ h (θ + x) + h (θ - x) :=
    fun x _ => add_nonneg (hh0 _) (hh0 _)
  have hgavg : ∀ s ∈ Set.Ioc (0:ℝ) δ,
      ∫ ψ in (0:ℝ)..s, (h (θ + ψ) + h (θ - ψ)) ≤ 2 * ε * s := by
    intro s hs
    have hs0 : 0 < s := hs.1
    have hsδ : s ≤ δ := hs.2
    have hIs : IntervalIntegrable h volume (θ - s) (θ + s) := by
      refine hhint.mono_set ?_
      rw [uIcc_of_le (show θ - δ ≤ θ + δ by linarith),
        uIcc_of_le (show θ - s ≤ θ + s by linarith)]
      exact Icc_subset_Icc (by linarith) (by linarith)
    have h1s : IntervalIntegrable (fun ψ : ℝ => h (θ + ψ)) volume (0:ℝ) s := by
      refine intervalIntegrable_add_const (a := (0:ℝ)) (b := s) ?_
      refine hhint.mono_set ?_
      rw [show (0:ℝ) + θ = θ by ring, show s + θ = θ + s by ring,
        uIcc_of_le (show θ - δ ≤ θ + δ by linarith), uIcc_of_le (show θ ≤ θ + s by linarith)]
      exact Icc_subset_Icc (by linarith) (by linarith)
    have h2s : IntervalIntegrable (fun ψ : ℝ => h (θ - ψ)) volume (0:ℝ) s := by
      refine intervalIntegrable_sub_const (a := (0:ℝ)) (b := s) ?_
      refine hhint.mono_set ?_
      rw [show θ - (0:ℝ) = θ by ring, uIcc_of_le (show θ - δ ≤ θ + δ by linarith),
        uIcc_of_le (show θ - s ≤ θ by linarith)]
      exact Icc_subset_Icc (by linarith) (by linarith)
    rw [integral_add_symm h θ s (le_of_lt hs0) h1s h2s hIs]
    exact havg s hs
  have hmain := pk_near_part_bound δ ε hδ hδπ hε
    (fun ψ : ℝ => h (θ + ψ) + h (θ - ψ)) hg hg0 hgavg r hr
  rw [hshift]
  exact hmain

end Work.EQ.Fatou
