import Mathlib
import Submission.Work.A14.defs
import Submission.CDT.CintegralCore
import Submission.Work.C17g.pringsheim

namespace Work.A14D

open Complex Metric MeasureTheory
open scoped BigOperators Topology

/-!
# `H = aH_A + bH_B + cH_C` is not holomorphic at `x = 1` when `c = 0`, `b ≠ 0`

Under the absurd relation `a + b·L(2,χ₋₃)/2 + c·ζ(2)/4 = 0` the coefficient of `xⁿ` in
`H = aH_A + bH_B + cH_C` equals `-(b/2)·Jₙ`, where
`Jₙ = ∬_{[0,1]²} 9ⁿsⁿtⁿ(1-s³)ⁿ(1-t³)ⁿ/(1+st+s²t²)^{2n+1} ds dt = cintegralJ n`
is the `(Cintegral)` double integral (`CintegralIdentity`).  All `Jₙ` have the same sign and
do not decay exponentially (the integrand is bounded below by `(1-η)ⁿ/3` on a small box around
`(s,t) = (1/2,1/2)`), so the power series `H` has radius of convergence exactly `1` and, by
Vivanti–Pringsheim (`Work.C17g.pringsheim`), `x = 1` is a singular point of `H`.
-/

/-! ## 0. The two polynomial factors of the `(Cintegral)` kernel -/

/-- `D(s,t) = 1 + st + s²t²`, the denominator of the `(Cintegral)` kernel. -/
private def kernD (s t : ℝ) : ℝ := 1 + s * t + s ^ 2 * t ^ 2

/-- `N(s,t) = 9st(1-s³)(1-t³)`, the numerator of the `(Cintegral)` kernel. -/
private def kernN (s t : ℝ) : ℝ := 9 * s * t * (1 - s ^ 3) * (1 - t ^ 3)

private lemma kernD_pos (s t : ℝ) : 0 < kernD s t := by
  have hu : 0 ≤ (s * t + 1 / 2) ^ 2 := sq_nonneg _
  unfold kernD
  nlinarith

private lemma kernD_one_le {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : 1 ≤ kernD s t := by
  have hu : 0 ≤ s * t := mul_nonneg hs ht
  have hu2 : 0 ≤ s ^ 2 * t ^ 2 := by positivity
  unfold kernD
  linarith

private lemma kernD_le_three {s t : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t)
    (ht1 : t ≤ 1) : kernD s t ≤ 3 := by
  have hst0 : 0 ≤ s * t := mul_nonneg hs ht
  have hst : s * t ≤ 1 := by nlinarith
  have hst2 : (s * t) ^ 2 ≤ 1 := by nlinarith
  have hs2 : s ^ 2 * t ^ 2 = (s * t) ^ 2 := by ring
  unfold kernD
  rw [hs2]
  linarith

/-- `D(1/2,1/2)² = N(1/2,1/2)`: the kernel takes its maximal value `1/D` at the centre. -/
private lemma kernD_sq_sub_kernN_centre : kernD (1 / 2) (1 / 2) ^ 2 - kernN (1 / 2) (1 / 2) = 0 := by
  unfold kernD kernN
  norm_num

/-- **The box bound**: for every `η > 0` there is a box around `(1/2,1/2)` on which
`D² - N ≤ η` (hence on which the kernel is `≥ (1-η)ⁿ/D`). -/
private lemma exists_box (η : ℝ) (hη0 : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ s t : ℝ, |s - 1 / 2| ≤ δ → |t - 1 / 2| ≤ δ →
      kernD s t ^ 2 - kernN s t ≤ η := by
  have hcont : ContinuousAt (fun p : ℝ × ℝ => kernD p.1 p.2 ^ 2 - kernN p.1 p.2)
      ((1 / 2, 1 / 2) : ℝ × ℝ) := by
    have h1 : Continuous (fun p : ℝ × ℝ => kernD p.1 p.2 ^ 2) := by
      unfold kernD; fun_prop
    have h2 : Continuous (fun p : ℝ × ℝ => kernN p.1 p.2) := by
      unfold kernN; fun_prop
    exact (h1.sub h2).continuousAt
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 ((1 / 2, 1 / 2) : ℝ × ℝ),
      kernD p.1 p.2 ^ 2 - kernN p.1 p.2 < η := by
    have hmem : Set.Iio η ∈ 𝓝 (kernD (1 / 2) (1 / 2) ^ 2 - kernN (1 / 2) (1 / 2)) := by
      rw [kernD_sq_sub_kernN_centre]
      exact IsOpen.mem_nhds isOpen_Iio hη0
    exact hcont.eventually hmem
  obtain ⟨ε, hε0, hε⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min (ε / 2) (1 / 2), lt_min (by positivity) (by norm_num), min_le_right _ _, ?_⟩
  intro s t hs ht
  have hε2 : ε / 2 < ε := by linarith
  have hdist : dist ((s, t) : ℝ × ℝ) ((1 / 2, 1 / 2) : ℝ × ℝ) < ε := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    have hs' : |s - 1 / 2| < ε := lt_of_le_of_lt hs (lt_of_le_of_lt (min_le_left _ _) hε2)
    have ht' : |t - 1 / 2| < ε := lt_of_le_of_lt ht (lt_of_le_of_lt (min_le_left _ _) hε2)
    exact max_lt hs' ht'
  exact le_of_lt (hε hdist)

/-! ## 1. Lower bounds for the `(Cintegral)` integrals -/

/-- **Non-exponential decay of the `(Cintegral)` integrals**: for every `η ∈ (0,1)` there is
`C > 0` with `C·(1-η)ⁿ ≤ Jₙ = cintegralJ n` for all `n`.  (The kernel equals
`(N/D²)ⁿ/D` with `N/D² = 1` at `(s,t) = (1/2,1/2)`, so on a small box around the centre it is
`≥ (1-η)ⁿ/3`.) -/
theorem cintegralJ_lower (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, C * (1 - η) ^ n ≤ Submission.CDT.cintegralJ n := by
  obtain ⟨δ, hδ0, hδhalf, hbox⟩ := exists_box η hη0
  refine ⟨(2 * δ) ^ 2 / 3, by positivity, ?_⟩
  intro n
  set a : ℝ := 1 / 2 - δ with ha
  set b : ℝ := 1 / 2 + δ with hb
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hab : a ≤ b := by rw [ha, hb]; linarith
  have hb1 : b ≤ 1 := by rw [hb]; linarith
  have h1η : 0 ≤ 1 - η := by linarith
  -- joint continuity of the kernel
  have hKC : Continuous fun p : ℝ × ℝ => Submission.CDT.cintegralKernel n p.1 p.2 := by
    have h1 : Continuous fun p : ℝ × ℝ => kernN p.1 p.2 ^ n := by
      unfold kernN; fun_prop
    have h2 : Continuous fun p : ℝ × ℝ => kernD p.1 p.2 ^ (2 * n + 1) := by
      unfold kernD; fun_prop
    have hne : ∀ p : ℝ × ℝ, kernD p.1 p.2 ^ (2 * n + 1) ≠ 0 := fun p =>
      pow_ne_zero _ (ne_of_gt (kernD_pos p.1 p.2))
    refine Continuous.congr (h1.div h2 hne) (fun p => ?_)
    simp only [Pi.div_apply, kernN, kernD]
    exact (Submission.CDT.cintegralKernel_eq_pow n p.1 p.2).symm
  -- the pointwise bound on the box
  have hK : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      (1 - η) ^ n / 3 ≤ Submission.CDT.cintegralKernel n s t := by
    intro s hs t ht
    have hs0 : 0 ≤ s := le_trans ha0 hs.1
    have hs1 : s ≤ 1 := le_trans hs.2 hb1
    have ht0 : 0 ≤ t := le_trans ha0 ht.1
    have ht1 : t ≤ 1 := le_trans ht.2 hb1
    have hD1 : 1 ≤ kernD s t := kernD_one_le hs0 ht0
    have hD3 : kernD s t ≤ 3 := kernD_le_three hs0 hs1 ht0 ht1
    have hDpos : 0 < kernD s t := kernD_pos s t
    have hsδ : |s - 1 / 2| ≤ δ := by
      rw [abs_le]
      constructor
      · rw [ha] at hs; linarith [hs.1]
      · rw [hb] at hs; linarith [hs.2]
    have htδ : |t - 1 / 2| ≤ δ := by
      rw [abs_le]
      constructor
      · rw [ha] at ht; linarith [ht.1]
      · rw [hb] at ht; linarith [ht.2]
    have hD1sq : (1 : ℝ) ≤ kernD s t ^ 2 := one_le_pow₀ hD1
    have hgap : kernD s t ^ 2 - kernN s t ≤ η := hbox s t hsδ htδ
    have hηD : η ≤ η * kernD s t ^ 2 := by
      calc η = η * 1 := by ring
        _ ≤ η * kernD s t ^ 2 := mul_le_mul_of_nonneg_left hD1sq hη0.le
    have hN : (1 - η) * kernD s t ^ 2 ≤ kernN s t := by nlinarith
    rw [Submission.CDT.cintegralKernel_eq_pow]
    have hNn : ((1 - η) * kernD s t ^ 2) ^ n ≤ kernN s t ^ n :=
      pow_le_pow_left₀ (mul_nonneg h1η (by positivity)) hN n
    have hstep : ((1 - η) * kernD s t ^ 2) ^ n / kernD s t ^ (2 * n + 1)
        ≤ kernN s t ^ n / kernD s t ^ (2 * n + 1) :=
      div_le_div_of_nonneg_right hNn (by positivity)
    have heq : ((1 - η) * kernD s t ^ 2) ^ n / kernD s t ^ (2 * n + 1)
        = (1 - η) ^ n / kernD s t := by
      rw [mul_pow, ← pow_mul, pow_succ',
        mul_div_mul_right _ _ (pow_ne_zero (2 * n) (ne_of_gt hDpos))]
    calc (1 - η) ^ n / 3 ≤ (1 - η) ^ n / kernD s t :=
          div_le_div_of_nonneg_left (pow_nonneg h1η n) hDpos hD3
      _ = ((1 - η) * kernD s t ^ 2) ^ n / kernD s t ^ (2 * n + 1) := heq.symm
      _ ≤ kernN s t ^ n / kernD s t ^ (2 * n + 1) := hstep
  -- inner integral: the box dominates
  have hinner : ∀ s ∈ Set.Icc a b,
      (b - a) * ((1 - η) ^ n / 3) ≤ ∫ t in (0 : ℝ)..1, Submission.CDT.cintegralKernel n s t := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans ha0 hs.1
    have hs1 : s ≤ 1 := le_trans hs.2 hb1
    have hcont : Continuous fun t : ℝ => Submission.CDT.cintegralKernel n s t :=
      hKC.comp (continuous_const.prodMk continuous_id)
    have e1 := intervalIntegral.integral_add_adjacent_intervals
      (f := fun t : ℝ => Submission.CDT.cintegralKernel n s t)
      (hcont.intervalIntegrable (μ := volume) 0 a) (hcont.intervalIntegrable (μ := volume) a 1)
    have e2 := intervalIntegral.integral_add_adjacent_intervals
      (f := fun t : ℝ => Submission.CDT.cintegralKernel n s t)
      (hcont.intervalIntegrable (μ := volume) a b) (hcont.intervalIntegrable (μ := volume) b 1)
    have n1 : 0 ≤ ∫ t in (0 : ℝ)..a, Submission.CDT.cintegralKernel n s t :=
      intervalIntegral.integral_nonneg ha0
        (fun u hu => Submission.CDT.cintegralKernel_nonneg n hs0 hs1 hu.1 (le_trans hu.2 (le_trans hab hb1)))
    have n2 : 0 ≤ ∫ t in b..(1 : ℝ), Submission.CDT.cintegralKernel n s t :=
      intervalIntegral.integral_nonneg hb1
        (fun u hu => Submission.CDT.cintegralKernel_nonneg n hs0 hs1 (le_trans (le_trans ha0 hab) hu.1) hu.2)
    have step : (b - a) * ((1 - η) ^ n / 3) ≤ ∫ t in a..b, Submission.CDT.cintegralKernel n s t := by
      have hmono := intervalIntegral.integral_mono_on hab intervalIntegrable_const
        (hcont.intervalIntegrable (μ := volume) a b) (fun t ht => hK s hs t ht)
      rwa [intervalIntegral.integral_const, smul_eq_mul] at hmono
    linarith [e1, e2, n1, n2, step]
  have hcontF : Continuous fun s : ℝ =>
      ∫ t in (0 : ℝ)..1, Submission.CDT.cintegralKernel n s t :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hKC 0 1
  -- outer integral
  have houter : (b - a) * ((b - a) * ((1 - η) ^ n / 3)) ≤
      ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, Submission.CDT.cintegralKernel n s t := by
    set F : ℝ → ℝ := fun s => ∫ t in (0 : ℝ)..1, Submission.CDT.cintegralKernel n s t with hF
    have e1 := intervalIntegral.integral_add_adjacent_intervals
      (f := F) (hcontF.intervalIntegrable (μ := volume) 0 a) (hcontF.intervalIntegrable (μ := volume) a 1)
    have e2 := intervalIntegral.integral_add_adjacent_intervals
      (f := F) (hcontF.intervalIntegrable (μ := volume) a b) (hcontF.intervalIntegrable (μ := volume) b 1)
    have n1 : 0 ≤ ∫ s in (0 : ℝ)..a, F s :=
      intervalIntegral.integral_nonneg ha0 (fun u hu =>
        intervalIntegral.integral_nonneg zero_le_one (fun t ht =>
          Submission.CDT.cintegralKernel_nonneg n hu.1 (le_trans hu.2 (le_trans hab hb1)) ht.1 ht.2))
    have n2 : 0 ≤ ∫ s in b..(1 : ℝ), F s :=
      intervalIntegral.integral_nonneg hb1 (fun u hu =>
        intervalIntegral.integral_nonneg zero_le_one (fun t ht =>
          Submission.CDT.cintegralKernel_nonneg n (le_trans (le_trans ha0 hab) hu.1) hu.2 ht.1 ht.2))
    have step : (b - a) * ((b - a) * ((1 - η) ^ n / 3)) ≤ ∫ s in a..b, F s := by
      have hmono := intervalIntegral.integral_mono_on hab intervalIntegrable_const
        (hcontF.intervalIntegrable (μ := volume) a b) (fun s hs => hinner s hs)
      rwa [intervalIntegral.integral_const, smul_eq_mul] at hmono
    linarith [e1, e2, n1, n2, step]
  have hba : b - a = 2 * δ := by rw [ha, hb]; ring
  calc (2 * δ) ^ 2 / 3 * (1 - η) ^ n
      = (b - a) * ((b - a) * ((1 - η) ^ n / 3)) := by rw [hba]; ring
    _ ≤ Submission.CDT.cintegralJ n := by
        rw [Submission.CDT.cintegralJ]
        exact houter

/-! ## 2. The coefficients of `H = aH_A + bH_B + cH_C` are `-(b/2)·Jₙ` -/

/-- Under the absurd relation `a + b·L(2,χ₋₃)/2 + c·ζ(2)/4 = 0` with `c = 0`, the `n`-th
coefficient of `H = aH_A + bH_B + cH_C` equals `-(b/2)·Jₙ` (`(Cintegral)`, paper
eq. `(Cintegral)`). -/
theorem coeff_HZ_eq (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c) (hc : c = 0) (n : ℕ) :
    ((PowerSeries.coeff n (Submission.CDTPlan.HZ a b c) : ℚ) : ℝ)
      = -(b : ℝ) / 2 * Submission.CDT.cintegralJ n := by
  have hcoeff : PowerSeries.coeff n (Submission.CDTPlan.HZ a b c)
      = (a : ℚ) * Submission.CDT.HA_coeff n + (b : ℚ) * Submission.CDT.HB_coeff n
        + (c : ℚ) * Submission.CDT.HC_coeff n := by
    simpa [Submission.CDTPlan.HZ] using
      Submission.CDT.ZagierH_coeff (a : ℚ) (b : ℚ) (c : ℚ) n
  have hrel : (a : ℝ) + (b : ℝ) * (Submission.CDT.L2chi3Real / 2)
      + (c : ℝ) * (Submission.CDT.zeta2Real / 4) = 0 := h
  have hcR : (c : ℝ) = 0 := by rw [hc]; norm_num
  have ha : (a : ℝ) = -(b : ℝ) * (Submission.CDT.L2chi3Real / 2) := by
    rw [hcR, zero_mul, add_zero] at hrel
    linarith
  have hId : Submission.CDT.L2chi3Real * (Submission.CDT.HA_coeff n : ℝ)
      - 2 * (Submission.CDT.HB_coeff n : ℝ) = Submission.CDT.cintegralJ n :=
    Submission.CDT.CintegralIdentity_proved n
  rw [hcoeff]
  push_cast
  rw [ha, hcR]
  linear_combination (-(b : ℝ) / 2) * hId

/-! ## 3. `H` is not holomorphic at `x = 1` -/
theorem H_not_holo_at_one (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c) (hb : b ≠ 0)
    (hc : c = 0) :
    ¬ ∃ (g : ℂ → ℂ) (δ : ℝ), 0 < δ ∧ DifferentiableOn ℂ g (ball 1 δ) ∧
      ∀ z ∈ lens1 δ, g z = Hfun a b c z := by
  rintro ⟨g, δ, hδ0, hgd, hagree⟩
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  -- positivity and boundedness of the `(Cintegral)` integrals
  obtain ⟨C₀, hC₀0, hC₀⟩ := cintegralJ_lower (1 / 2) (by norm_num) (by norm_num)
  have hJpos : ∀ n : ℕ, 0 < Submission.CDT.cintegralJ n := fun n =>
    lt_of_lt_of_le (by positivity) (hC₀ n)
  have hJle : ∀ n : ℕ, Submission.CDT.cintegralJ n ≤ 1 := fun n =>
    le_trans (le_abs_self _) (Submission.CDT.cintegralJ_bound' n)
  set f : ℕ → ℝ := fun n => |(b : ℝ)| / 2 * Submission.CDT.cintegralJ n with hf
  have hfnn : ∀ n, 0 ≤ f n := fun n => mul_nonneg (by positivity) (le_of_lt (hJpos n))
  have hfle : ∀ n, f n ≤ |(b : ℝ)| / 2 := fun n => by
    rw [hf]
    calc |(b : ℝ)| / 2 * Submission.CDT.cintegralJ n ≤ |(b : ℝ)| / 2 * 1 :=
          mul_le_mul_of_nonneg_left (hJle n) (by positivity)
      _ = |(b : ℝ)| / 2 := mul_one _
  have habs : ∀ n, |((PowerSeries.coeff n (Submission.CDTPlan.HZ a b c) : ℚ) : ℝ)| = f n := by
    intro n
    rw [coeff_HZ_eq a b c h hc n, hf, abs_mul, abs_of_pos (hJpos n), abs_div, abs_neg,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  -- the coefficient series is summable on the unit disc, with sum `H`
  have hsummCoeff : ∀ z : ℂ, ‖z‖ < 1 →
      Summable fun n => (((PowerSeries.coeff n (Submission.CDTPlan.HZ a b c) : ℚ)) : ℂ) * z ^ n := by
    intro z hz
    have hg : Summable fun n => (|(b : ℝ)| / 2) * ‖z‖ ^ n :=
      (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left _
    refine Summable.of_norm_bounded hg (fun n => ?_)
    rw [norm_mul, norm_pow, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs,
      habs n]
    exact mul_le_mul_of_nonneg_right (hfle n) (pow_nonneg (norm_nonneg z) n)
  have hasCoeff : ∀ z : ℂ, ‖z‖ < 1 →
      HasSum (fun n => (((PowerSeries.coeff n (Submission.CDTPlan.HZ a b c) : ℚ)) : ℂ) * z ^ n)
        (Hfun a b c z) := fun z hz => by
    simpa only [Hfun] using (hsummCoeff z hz).hasSum
  -- summability of `Σ fₙ rⁿ` for `r < 1`
  have hsum1 : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable fun n => f n * r ^ n := by
    intro r hr0 hr1
    have hg : Summable fun n => (|(b : ℝ)| / 2) * r ^ n :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left _
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hfnn n) (pow_nonneg hr0 n))
      (fun n => mul_le_mul_of_nonneg_right (hfle n) (pow_nonneg hr0 n)) hg
  -- the contradiction from a geometric lower bound
  have finish : ∀ ρ : ℝ, 1 < ρ → Summable (fun n : ℕ => f n * ρ ^ n) → False := by
    intro ρ hρ hsum
    have hρ0 : 0 < ρ := by linarith
    have h1ρ : 1 / ρ < 1 := (div_lt_one hρ0).mpr hρ
    have h1ρ0 : 0 < 1 / ρ := by positivity
    set η : ℝ := (1 - 1 / ρ) / 2 with hη
    have hη0 : 0 < η := by rw [hη]; linarith
    have hη1 : η < 1 := by rw [hη]; linarith
    obtain ⟨C, hC0, hC⟩ := cintegralJ_lower η hη0 hη1
    set C' : ℝ := |(b : ℝ)| / 2 * C with hC'
    have hC'0 : 0 < C' := by rw [hC']; positivity
    set q : ℝ := (1 - η) * ρ with hq
    have hq1 : 1 < q := by
      rw [hq, hη]
      field_simp
      nlinarith
    have hbnd : ∀ n : ℕ, C' * q ^ n ≤ f n * ρ ^ n := by
      intro n
      have h1 := hC n
      have h3 : 0 ≤ ρ ^ n := pow_nonneg (le_of_lt hρ0) n
      have h4 : (|(b : ℝ)| / 2) * (C * (1 - η) ^ n)
          ≤ (|(b : ℝ)| / 2) * Submission.CDT.cintegralJ n :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h5 : C' * q ^ n = (|(b : ℝ)| / 2) * (C * (1 - η) ^ n) * ρ ^ n := by
        rw [hC', hq, mul_pow]
        ring
      rw [h5, hf]
      exact mul_le_mul_of_nonneg_right h4 h3
    have hge : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) ≤ C' * q ^ n := by
      have hpow : ∀ᶠ n : ℕ in Filter.atTop, 1 / C' ≤ q ^ n :=
        (tendsto_pow_atTop_atTop_of_one_lt hq1).eventually
          (Filter.eventually_atTop.mpr ⟨1 / C', fun n hn => hn⟩)
      filter_upwards [hpow] with n hn
      have h6 := mul_le_mul_of_nonneg_left hn (le_of_lt hC'0)
      rwa [mul_one_div_cancel (ne_of_gt hC'0)] at h6
    have hle : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) ≤ f n * ρ ^ n := by
      filter_upwards [hge] with n hn
      exact le_trans hn (hbnd n)
    have htend : Filter.Tendsto (fun n : ℕ => f n * ρ ^ n) Filter.atTop (nhds 0) :=
      hsum.tendsto_atTop_zero
    have hfin := le_of_tendsto_of_tendsto tendsto_const_nhds htend hle
    norm_num at hfin
  have hzn_of : ∀ z : ℂ, z ∈ ball ((1 : ℝ) : ℂ) δ ∩ ball (0 : ℂ) (1 : ℝ) → ‖z‖ < 1 := by
    intro z hz
    have h' := hz.2
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h'
    exact_mod_cast h'
  rcases lt_trichotomy (b : ℝ) 0 with hbneg | hbzero | hbpos
  · -- `b < 0`: the coefficients are `f n`
    have hsign : ∀ n, ((PowerSeries.coeff n (Submission.CDTPlan.HZ a b c) : ℚ) : ℝ) = f n := by
      intro n
      rw [coeff_HZ_eq a b c h hc n, hf, abs_of_neg hbneg]
      try ring
    have hfg : ∀ z ∈ ball ((1 : ℝ) : ℂ) δ ∩ ball (0 : ℂ) (1 : ℝ),
        HasSum (fun n => ((f n : ℝ) : ℂ) * z ^ n) (g z) := by
      intro z hz
      have h2 : HasSum (fun n => ((f n : ℝ) : ℂ) * z ^ n) (Hfun a b c z) := by
        refine (hasCoeff z (hzn_of z hz)).congr_fun (fun n => ?_)
        have hcast : ((f n : ℝ) : ℂ) = (((PowerSeries.coeff n (Submission.CDTPlan.HZ a b c) : ℚ)) : ℂ) := by
          rw [← Complex.ofReal_ratCast, ← hsign n]
        rw [hcast]
      rw [hagree z (by simpa [lens1] using hz)]
      exact h2
    obtain ⟨ρ, hρ, hsum⟩ := Work.C17g.pringsheim f hfnn 1 (by norm_num) hsum1 g δ hδ0
      (by simpa using hgd) hfg
    exact finish ρ hρ hsum
  · exact absurd hbzero hbR
  · -- `b > 0`: the coefficients are `-f n`
    have hsign : ∀ n, ((PowerSeries.coeff n (Submission.CDTPlan.HZ a b c) : ℚ) : ℝ) = -f n := by
      intro n
      rw [coeff_HZ_eq a b c h hc n, hf, abs_of_pos hbpos]
      try ring
    have hfg : ∀ z ∈ ball ((1 : ℝ) : ℂ) δ ∩ ball (0 : ℂ) (1 : ℝ),
        HasSum (fun n => ((f n : ℝ) : ℂ) * z ^ n) (-(g z)) := by
      intro z hz
      have h2 : HasSum (fun n => ((f n : ℝ) : ℂ) * z ^ n) (-(Hfun a b c z)) := by
        refine (hasCoeff z (hzn_of z hz)).neg.congr_fun (fun n => ?_)
        have hcast : (((PowerSeries.coeff n (Submission.CDTPlan.HZ a b c) : ℚ)) : ℂ)
            = -((f n : ℝ) : ℂ) := by
          rw [← Complex.ofReal_ratCast, hsign n]
          push_cast
          try ring
        rw [hcast]
        try ring
      rw [hagree z (by simpa [lens1] using hz)]
      exact h2
    obtain ⟨ρ, hρ, hsum⟩ := Work.C17g.pringsheim f hfnn 1 (by norm_num) hsum1 (fun z => -g z)
      δ hδ0 (by simpa using hgd.neg) hfg
    exact finish ρ hρ hsum

end Work.A14D
