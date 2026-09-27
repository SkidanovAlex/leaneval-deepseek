import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.FatouDefs
import Submission.Work.EQ.Fatou.pk_eq_poissonKernel
import Submission.Work.EQ.Fatou.pk_nonneg
import Submission.Work.EQ.Fatou.pkS_nonneg
import Submission.Work.EQ.Fatou.integral_pk_eq
import Submission.Work.EQ.Fatou.pkS_mass
import Submission.Work.EQ.Fatou.pk_pi_tendsto
import Submission.Work.EQ.Fatou.pkS_tail_tendsto
import Submission.Work.EQ.Fatou.eventually_pk_lt
import Submission.Work.EQ.Fatou.ae_uniform_interval_average
import Submission.Work.EQ.Fatou.integral_normSq_eq_tsum
import Submission.Work.EQ.Fatou.tsum_pow_sub_sq_le
import Submission.Work.EQ.Fatou.log_norm_le_integral
import Submission.Work.EQ.Fatou.exists_factor_order
import Submission.Work.EQ.Fatou.dist_toLp_eq_sqrt
import Submission.Work.EQ.Fatou.tendsto_integral_norm_of_tendsto_Lp
import Submission.Work.EQ.Fatou.pk_mixture
import Submission.Work.EQ.Fatou.poisson_limit
import Submission.Work.EQ.Fatou.ae_radial_limit_of_poisson
import Submission.Work.EQ.Fatou.volume_radial_limit_eq_zero

/-!
# Namespace copy of `Work.EQ.fatou_riesz`

This is a verbatim copy of `Submission/Work/EQ/fatou_riesz.lean` with all declarations moved
into the namespace `Work.EQ.FR`, to avoid the global name clash on `Work.EQ.rhoSeq.eq_1`
between that file and `Submission.Work.EQ.bp_aux` (the two modules cannot be imported into
one environment).  The mathematics and the names inside the new namespace are unchanged.

This file proves `Work.EQ.FR.fatou_riesz`.
-/

namespace Work.EQ.FR

open MeasureTheory Filter _root_.Topology Complex
open scoped ENNReal

/-- Lebesgue measure restricted to a period `(0, 2π]`. -/
noncomputable abbrev circM : Measure ℝ := volume.restrict (Set.Ioc 0 (2 * Real.pi))

lemma integral_circM_eq (f : ℝ → ℂ) : (∫ x, f x ∂circM) = ∫ x in (0 : ℝ)..(2 * Real.pi), f x := by
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]

lemma integral_circM_eq_real (f : ℝ → ℝ) :
    (∫ x, f x ∂circM) = ∫ x in (0 : ℝ)..(2 * Real.pi), f x := by
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]

lemma norm_pt (ρ θ : ℝ) : ‖(ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = |ρ| := by
  rw [norm_mul, Complex.norm_exp]
  have hre : ((θ : ℂ) * Complex.I).re = 0 := by simp
  rw [hre, Real.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs]

lemma discVal_apply (g : ℂ → ℂ) (ρ θ : ℝ) :
    discVal g ρ θ = g ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := rfl

/-- Taylor coefficients of `g` at the origin. -/
noncomputable def tcoeff (g : ℂ → ℂ) (n : ℕ) : ℂ := (n.factorial : ℂ)⁻¹ * iteratedDeriv n g 0

lemma hasSum_tcoeff {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.ball 0 1)) {z : ℂ}
    (hz : z ∈ Metric.ball 0 1) : HasSum (fun n : ℕ => tcoeff g n * z ^ n) (g z) := by
  have h := Complex.hasSum_taylorSeries_on_ball hg hz
  have hfun : (fun n : ℕ => tcoeff g n * z ^ n)
      = fun n : ℕ => (n.factorial : ℂ)⁻¹ • (z - 0) ^ n • iteratedDeriv n g 0 := by
    funext n
    simp only [tcoeff, smul_eq_mul, sub_zero]
    ring
  rw [hfun]
  exact h

lemma norm_discVal_le {g : ℂ → ℂ} {M : ℝ} (hM : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖g z‖ ≤ M)
    {ρ θ : ℝ} (hρ : ρ ∈ Set.Ioo 0 1) : ‖discVal g ρ θ‖ ≤ M := by
  rw [discVal_apply]
  refine hM _ ?_
  rw [Metric.mem_ball, dist_zero_right, norm_pt, abs_of_nonneg hρ.1.le]
  exact hρ.2

lemma continuous_discVal {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.ball 0 1)) (ρ : ℝ)
    (hρ : ρ ∈ Set.Ioo 0 1) : Continuous (discVal g ρ) := by
  have hcont : ContinuousOn g (Metric.ball (0:ℂ) 1) := hg.continuousOn
  have hψ : Continuous fun θ : ℝ => (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    fun_prop
  have hmaps : ∀ θ : ℝ, (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ Metric.ball 0 1 := by
    intro θ
    rw [Metric.mem_ball, dist_zero_right, norm_pt, abs_of_nonneg hρ.1.le]
    exact hρ.2
  exact hcont.comp_continuous hψ hmaps

lemma memLp_discVal {g : ℂ → ℂ} {M : ℝ} (hg : DifferentiableOn ℂ g (Metric.ball 0 1))
    (hM : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖g z‖ ≤ M) {ρ : ℝ} (hρ : ρ ∈ Set.Ioo 0 1) :
    MemLp (discVal g ρ) 2 circM := by
  refine MemLp.of_bound ((continuous_discVal hg ρ hρ).measurable.aestronglyMeasurable) M ?_
  filter_upwards with θ
  exact norm_discVal_le hM hρ

/-- Parseval's formula for the difference of two dilates. -/
lemma integral_normSq_sub {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.ball 0 1))
    {r s : ℝ} (hr : 0 < r) (hr1 : r < 1) (hs : 0 < s) (hs1 : s < 1) :
    ∫ θ in (0:ℝ)..2 * Real.pi, ‖discVal g r θ - discVal g s θ‖ ^ 2
      = 2 * Real.pi * ∑' n : ℕ, ‖tcoeff g n‖ ^ 2 * (r ^ n - s ^ n) ^ 2 := by
  set R : ℝ := (1 + (max r s)⁻¹) / 2 with hRdef
  have hmax1 : max r s < 1 := max_lt hr1 hs1
  have hmaxpos : 0 < max r s := lt_max_of_lt_left hr
  have hR1 : 1 < R := by
    have h2 : 1 < (max r s)⁻¹ := by
      rw [one_lt_inv₀ hmaxpos]; exact hmax1
    simp only [hRdef]; linarith
  have hrR : r * R < 1 := by
    have h1 : r ≤ max r s := le_max_left _ _
    have h2 : r / max r s ≤ 1 := (div_le_one hmaxpos).mpr h1
    have h3 : r * R = (r + r / max r s) / 2 := by
      rw [hRdef]; field_simp
    rw [h3]; linarith
  have hsR : s * R < 1 := by
    have h1 : s ≤ max r s := le_max_right _ _
    have h2 : s / max r s ≤ 1 := (div_le_one hmaxpos).mpr h1
    have h3 : s * R = (s + s / max r s) / 2 := by
      rw [hRdef]; field_simp
    rw [h3]; linarith
  have hsub : ∀ z ∈ Metric.ball (0:ℂ) R,
      HasSum (fun n : ℕ => (tcoeff g n * r ^ n - tcoeff g n * s ^ n) * z ^ n)
        (g (r * z) - g (s * z)) := by
    intro z hz
    have hzR : ‖z‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hz
    have hrz : r * z ∈ Metric.ball (0:ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr]
      calc r * ‖z‖ < r * R := by nlinarith
        _ < 1 := hrR
    have hsz : s * z ∈ Metric.ball (0:ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs]
      calc s * ‖z‖ < s * R := by nlinarith
        _ < 1 := hsR
    have h1 : HasSum (fun n : ℕ => tcoeff g n * (r * z) ^ n) (g (r * z)) := hasSum_tcoeff hg hrz
    have h2 : HasSum (fun n : ℕ => tcoeff g n * (s * z) ^ n) (g (s * z)) := hasSum_tcoeff hg hsz
    have h1' : HasSum (fun n : ℕ => (tcoeff g n * r ^ n) * z ^ n) (g (r * z)) := by
      have hfun : (fun n : ℕ => (tcoeff g n * r ^ n) * z ^ n)
          = fun n : ℕ => tcoeff g n * (r * z) ^ n := by
        funext n; ring
      simpa only [hfun] using h1
    have h2' : HasSum (fun n : ℕ => (tcoeff g n * s ^ n) * z ^ n) (g (s * z)) := by
      have hfun : (fun n : ℕ => (tcoeff g n * s ^ n) * z ^ n)
          = fun n : ℕ => tcoeff g n * (s * z) ^ n := by
        funext n; ring
      simpa only [hfun] using h2
    have h3 := h1'.sub h2'
    have hfun : (fun n : ℕ => (tcoeff g n * r ^ n) * z ^ n - (tcoeff g n * s ^ n) * z ^ n)
        = fun n : ℕ => (tcoeff g n * r ^ n - tcoeff g n * s ^ n) * z ^ n := by
      funext n; ring
    rw [hfun] at h3
    exact h3
  have key := Work.EQ.Fatou.integral_normSq_eq_tsum (h := fun z => g (r * z) - g (s * z))
    (a := fun n : ℕ => tcoeff g n * r ^ n - tcoeff g n * s ^ n) (ρ := 1) (R := R)
    one_pos hR1 hsub
  have key' : (∫ θ in (0:ℝ)..2 * Real.pi, ‖discVal g r θ - discVal g s θ‖ ^ 2)
      = 2 * Real.pi * ∑' n : ℕ, ‖tcoeff g n * r ^ n - tcoeff g n * s ^ n‖ ^ 2 * 1 ^ (2 * n) := by
    simpa only [discVal_apply, Complex.ofReal_one, one_mul] using key
  rw [key']
  congr 1
  refine tsum_congr fun n => ?_
  have h1 : ‖tcoeff g n * r ^ n - tcoeff g n * s ^ n‖ ^ 2
      = ‖tcoeff g n‖ ^ 2 * (r ^ n - s ^ n) ^ 2 := by
    rw [show tcoeff g n * r ^ n - tcoeff g n * s ^ n
        = tcoeff g n * ((r : ℂ) ^ n - (s : ℂ) ^ n) by ring]
    rw [norm_mul, mul_pow]
    congr 1
    rw [show (r : ℂ) ^ n - (s : ℂ) ^ n = ((r ^ n - s ^ n : ℝ) : ℂ) by
      rw [Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_pow]]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [h1]
  simp

/-- For `0 < ρ < 1` the sequence `‖tcoeff g n‖² ρ^{2n}` is summable. -/
lemma summable_normSq_tcoeff_geo {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.ball 0 1))
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Summable (fun n : ℕ => ‖tcoeff g n‖ ^ 2 * ρ ^ (2 * n)) := by
  obtain ⟨ρ', hρρ', hρ'1⟩ : ∃ ρ', ρ < ρ' ∧ ρ' < 1 := ⟨(ρ + 1) / 2, by linarith, by linarith⟩
  have hρ'0 : 0 < ρ' := lt_trans hρ0 hρρ'
  have hz : (ρ' : ℂ) ∈ Metric.ball (0:ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ'0]
    exact hρ'1
  have hsum' := hasSum_tcoeff hg hz
  have hterm : Tendsto (fun n : ℕ => ‖tcoeff g n‖ * ρ' ^ n) atTop (𝓝 0) := by
    have h := hsum'.summable.tendsto_atTop_zero.norm
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ'0] using h
  obtain ⟨C, hC⟩ : ∃ C, ∀ n, ‖tcoeff g n‖ * ρ' ^ n ≤ C := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hterm 1 one_pos
    refine ⟨1 + ∑ n ∈ Finset.range N, ‖tcoeff g n‖ * ρ' ^ n, fun n => ?_⟩
    have hsum_nn : 0 ≤ ∑ m ∈ Finset.range N, ‖tcoeff g m‖ * ρ' ^ m :=
      Finset.sum_nonneg (fun m _ => by positivity)
    by_cases hn : n < N
    · have h1 : ‖tcoeff g n‖ * ρ' ^ n ≤ ∑ m ∈ Finset.range N, ‖tcoeff g m‖ * ρ' ^ m :=
        Finset.single_le_sum (f := fun m => ‖tcoeff g m‖ * ρ' ^ m)
          (fun m _ => by positivity) (Finset.mem_range.mpr hn)
      linarith
    · push_neg at hn
      have h2 : ‖tcoeff g n‖ * ρ' ^ n < 1 := by
        have h3 := hN n hn
        rwa [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h3
      linarith
  have hratio0 : 0 ≤ (ρ / ρ') ^ 2 := sq_nonneg _
  have hratio1 : (ρ / ρ') ^ 2 < 1 := by
    have h1 : 0 ≤ ρ / ρ' := div_nonneg hρ0.le hρ'0.le
    have h2 : ρ / ρ' < 1 := (div_lt_one hρ'0).mpr hρρ'
    nlinarith
  have hdom : Summable (fun n : ℕ => C ^ 2 * (ρ / ρ') ^ (2 * n)) := by
    have hseq : (fun n : ℕ => C ^ 2 * (ρ / ρ') ^ (2 * n))
        = fun n : ℕ => C ^ 2 * ((ρ / ρ') ^ 2) ^ n := by
      funext n
      rw [pow_mul]
    rw [hseq]
    exact Summable.mul_left _ (summable_geometric_of_lt_one hratio0 hratio1)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hdom
  have hρ'ne : ρ' ≠ 0 := ne_of_gt hρ'0
  have hbound : ‖tcoeff g n‖ * ρ ^ n ≤ C * (ρ / ρ') ^ n := by
    have h1 : (‖tcoeff g n‖ * ρ' ^ n) * (ρ / ρ') ^ n = ‖tcoeff g n‖ * ρ ^ n := by
      rw [div_pow]
      field_simp
    rw [← h1]
    exact mul_le_mul_of_nonneg_right (hC n) (by positivity)
  calc ‖tcoeff g n‖ ^ 2 * ρ ^ (2 * n)
      = (‖tcoeff g n‖ * ρ ^ n) ^ 2 := by ring_nf
    _ ≤ (C * (ρ / ρ') ^ n) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) hbound 2
    _ = C ^ 2 * (ρ / ρ') ^ (2 * n) := by ring_nf

/-- The Taylor coefficients of a bounded holomorphic function are in `ℓ²`. -/
lemma summable_normSq_tcoeff {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.ball 0 1)) {M : ℝ}
    (hM : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖g z‖ ≤ M) :
    Summable (fun n : ℕ => ‖tcoeff g n‖ ^ 2) := by
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by simp [Metric.mem_ball]))
  refine summable_of_sum_range_le (c := M ^ 2) (fun n => sq_nonneg _) fun N => ?_
  have htend : Tendsto (fun ρ : ℝ => ∑ n ∈ Finset.range N, ‖tcoeff g n‖ ^ 2 * ρ ^ (2 * n))
      (𝓝[<] 1) (𝓝 (∑ n ∈ Finset.range N, ‖tcoeff g n‖ ^ 2)) := by
    have hρ : Tendsto (fun ρ : ℝ => ρ) (𝓝[<] (1:ℝ)) (𝓝 1) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hpow : ∀ n : ℕ, Tendsto (fun ρ : ℝ => ρ ^ (2 * n)) (𝓝[<] (1:ℝ)) (𝓝 1) := fun n => by
      simpa using hρ.pow (2 * n)
    have h2 : Tendsto (fun ρ : ℝ => ∑ n ∈ Finset.range N, ‖tcoeff g n‖ ^ 2 * ρ ^ (2 * n))
        (𝓝[<] (1:ℝ)) (𝓝 (∑ n ∈ Finset.range N, ‖tcoeff g n‖ ^ 2 * 1)) :=
      tendsto_finset_sum _ fun n hn => tendsto_const_nhds.mul (hpow n)
    simpa using h2
  refine le_of_tendsto htend ?_
  have hI : ∀ᶠ ρ in (𝓝[<] (1:ℝ)), (0:ℝ) < ρ :=
    nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hI] with ρ hρ1 hρ0
  have hparse := Work.EQ.Fatou.integral_normSq_eq_tsum (h := g) (a := tcoeff g) (ρ := ρ)
    (R := 1) hρ0 hρ1 fun z hz => hasSum_tcoeff hg hz
  have hsumm := summable_normSq_tcoeff_geo hg hρ0 hρ1
  have h1 : ∑ n ∈ Finset.range N, ‖tcoeff g n‖ ^ 2 * ρ ^ (2 * n)
      ≤ ∑' n : ℕ, ‖tcoeff g n‖ ^ 2 * ρ ^ (2 * n) :=
    Summable.sum_le_tsum _ (fun n _ => by positivity) hsumm
  have hbd : ∀ θ : ℝ, ‖discVal g ρ θ‖ ^ 2 ≤ M ^ 2 := fun θ => by
    have h := norm_discVal_le hM (θ := θ) ⟨hρ0, hρ1⟩
    nlinarith [norm_nonneg (discVal g ρ θ)]
  have hint : (∫ θ in (0:ℝ)..2 * Real.pi, ‖discVal g ρ θ‖ ^ 2) ≤ 2 * Real.pi * M ^ 2 := by
    calc (∫ θ in (0:ℝ)..2 * Real.pi, ‖discVal g ρ θ‖ ^ 2)
        ≤ ∫ θ in (0:ℝ)..2 * Real.pi, M ^ 2 := by
          refine intervalIntegral.integral_mono_on (by positivity) ?_ ?_ fun θ _ => hbd θ
          · exact ((continuous_discVal hg ρ ⟨hρ0, hρ1⟩).norm.pow 2).intervalIntegrable _ _
          · exact intervalIntegrable_const
      _ = 2 * Real.pi * M ^ 2 := by
          rw [intervalIntegral.integral_const]
          simp
  have h2 : 2 * Real.pi * (∑' n : ℕ, ‖tcoeff g n‖ ^ 2 * ρ ^ (2 * n)) ≤ 2 * Real.pi * M ^ 2 := by
    rw [← hparse]
    exact hint
  have h3 : (∑' n : ℕ, ‖tcoeff g n‖ ^ 2 * ρ ^ (2 * n)) ≤ M ^ 2 :=
    le_of_mul_le_mul_left h2 (by positivity)
  linarith [h1, h3]

/-- The canonical radii `ρ_k = 1 - 1/(k+1) → 1⁻`. -/
noncomputable def rhoSeq (k : ℕ) : ℝ := 1 - 1 / (k + 2)

lemma rhoSeq_eq (k : ℕ) : rhoSeq k = ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) := by
  rw [rhoSeq]
  push_cast
  field_simp
  ring

lemma rhoSeq_pos (k : ℕ) : 0 < rhoSeq k := by
  rw [rhoSeq, sub_pos, div_lt_one (by positivity : (0:ℝ) < (k : ℝ) + 2)]
  linarith

lemma rhoSeq_lt_one (k : ℕ) : rhoSeq k < 1 := by
  rw [rhoSeq, sub_lt_iff_lt_add]
  have h : (0:ℝ) < 1 / ((k : ℝ) + 2) := by positivity
  linarith

lemma rhoSeq_mem (k : ℕ) : rhoSeq k ∈ Set.Ioo (0:ℝ) 1 := ⟨rhoSeq_pos k, rhoSeq_lt_one k⟩

lemma rhoSeq_tendsto : Tendsto rhoSeq atTop (𝓝[<] (1:ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, Eventually.of_forall fun k => rhoSeq_lt_one k⟩
  have h1 : Tendsto (fun k : ℕ => (1:ℝ) / ((k : ℝ) + 2)) atTop (𝓝 0) := by
    have h := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h2 := h.comp (tendsto_add_atTop_nat 2)
    have hfun : (fun k : ℕ => (1:ℝ) / ((k : ℝ) + 2))
        = (fun n : ℕ => 1 / (n : ℝ)) ∘ (fun a : ℕ => a + 2) := by
      funext k
      simp [Nat.cast_add]
    rw [hfun]
    exact h2
  have h2 : Tendsto (fun k : ℕ => (1:ℝ) - 1 / ((k : ℝ) + 2)) atTop (𝓝 (1 - 0)) :=
    h1.const_sub 1
  have hfun : rhoSeq = fun k : ℕ => (fun n : ℕ => (1:ℝ) - 1 / ((n : ℝ))) (k + 2) := by
    funext k
    simp [rhoSeq]
  rw [hfun]
  simpa using h2

/-- **Cauchy estimate.**  For a nonnegative summable `a`, the `ℓ²` distance
`∑ aₙ (rⁿ - sⁿ)²` is small when `r, s → 1⁻`. -/
lemma cauchy_estimate {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a) :
    ∀ ε > 0, ∃ δ > 0, ∀ r ∈ Set.Ioo (1 - δ) 1, ∀ s ∈ Set.Ioo (1 - δ) 1,
      Real.sqrt (2 * Real.pi * ∑' n : ℕ, a n * (r ^ n - s ^ n) ^ 2) < ε := by
  intro ε hε
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have h4 : 0 < ε ^ 2 / (4 * Real.pi) := by positivity
  -- the tail of the series is small
  obtain ⟨N, hN⟩ : ∃ N : ℕ,
      (∑' n : ℕ, a n) - ∑ n ∈ Finset.range N, a n < ε ^ 2 / (4 * Real.pi) := by
    have h1 : Tendsto (fun N : ℕ => (∑' n : ℕ, a n) - ∑ n ∈ Finset.range N, a n)
        atTop (𝓝 0) := by
      have h2 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, a n) atTop (𝓝 (∑' n : ℕ, a n)) :=
        hs.hasSum.tendsto_sum_nat
      simpa using h2.const_sub (∑' n : ℕ, a n)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h1 (ε ^ 2 / (4 * Real.pi)) h4
    refine ⟨N, ?_⟩
    have h3 := hN N le_rfl
    rw [Real.dist_eq, sub_zero, abs_lt] at h3
    exact h3.2
  -- the finite sum is small near `(1,1)`
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ > 0, ∀ r ∈ Set.Ioo (1 - δ) 1, ∀ s ∈ Set.Ioo (1 - δ) 1,
      ∑ n ∈ Finset.range N, a n * (r ^ n - s ^ n) ^ 2 < ε ^ 2 / (4 * Real.pi) := by
    have hlim : Tendsto (fun p : ℝ × ℝ => ∑ n ∈ Finset.range N, a n * (p.1 ^ n - p.2 ^ n) ^ 2)
        (𝓝[<] (1:ℝ) ×ˢ 𝓝[<] (1:ℝ)) (𝓝 0) := by
      have h1 : Tendsto (fun p : ℝ × ℝ => p.1) (𝓝[<] (1:ℝ) ×ˢ 𝓝[<] (1:ℝ)) (𝓝 1) :=
        tendsto_fst.mono_right nhdsWithin_le_nhds
      have h2 : Tendsto (fun p : ℝ × ℝ => p.2) (𝓝[<] (1:ℝ) ×ˢ 𝓝[<] (1:ℝ)) (𝓝 1) :=
        tendsto_snd.mono_right nhdsWithin_le_nhds
      have h3 : Tendsto (fun p : ℝ × ℝ => ∑ n ∈ Finset.range N, a n * (p.1 ^ n - p.2 ^ n) ^ 2)
          (𝓝[<] (1:ℝ) ×ˢ 𝓝[<] (1:ℝ))
          (𝓝 (∑ n ∈ Finset.range N, a n * (1 ^ n - 1 ^ n) ^ 2)) :=
        tendsto_finset_sum _ fun n hn =>
          tendsto_const_nhds.mul (((h1.pow n).sub (h2.pow n)).pow 2)
      have h4' : (∑ n ∈ Finset.range N, a n * (1 ^ n - 1 ^ n) ^ 2) = 0 := by simp
      rw [h4'] at h3
      simpa using h3
    have hev := hlim.eventually (eventually_lt_nhds h4)
    obtain ⟨U, hU, V, hV, hUV⟩ := Filter.eventually_prod_iff.mp hev
    rw [eventually_nhdsWithin_iff] at hU hV
    obtain ⟨δ₁, hδ₁, h1U⟩ := Metric.eventually_nhds_iff.mp hU
    obtain ⟨δ₂, hδ₂, h2V⟩ := Metric.eventually_nhds_iff.mp hV
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun r hr s hss => ?_⟩
    have hdr : dist r 1 < δ₁ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hr.1, hr.2, min_le_left δ₁ δ₂, min_le_right δ₁ δ₂]
    have hds : dist s 1 < δ₂ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hss.1, hss.2, min_le_left δ₁ δ₂, min_le_right δ₁ δ₂]
    exact hUV (h1U hdr hr.2) (h2V hds hss.2)
  refine ⟨min δ 1, lt_min hδ0 one_pos, fun r hr s hss => ?_⟩
  have hr0 : 0 ≤ r := by linarith [hr.1, min_le_right δ 1]
  have hs0 : 0 ≤ s := by linarith [hss.1, min_le_right δ 1]
  have hr1 : r ≤ 1 := le_of_lt hr.2
  have hs1 : s ≤ 1 := le_of_lt hss.2
  have hkey := Work.EQ.Fatou.tsum_pow_sub_sq_le ha hs N hr0 hr1 hs0 hs1
  have hsmall : ∑ n ∈ Finset.range N, a n * (r ^ n - s ^ n) ^ 2 < ε ^ 2 / (4 * Real.pi) :=
    hδ r ⟨by linarith [hr.1, min_le_left δ 1], hr.2⟩
      s ⟨by linarith [hss.1, min_le_left δ 1], hss.2⟩
  have hb : ∑' n : ℕ, a n * (r ^ n - s ^ n) ^ 2 < ε ^ 2 / (2 * Real.pi) := by
    have h2 : ε ^ 2 / (4 * Real.pi) + ε ^ 2 / (4 * Real.pi) = ε ^ 2 / (2 * Real.pi) := by
      field_simp
      ring
    linarith [hkey, hsmall, hN, h2]
  calc Real.sqrt (2 * Real.pi * ∑' n : ℕ, a n * (r ^ n - s ^ n) ^ 2)
      < Real.sqrt (2 * Real.pi * (ε ^ 2 / (2 * Real.pi))) := by
        apply Real.sqrt_lt_sqrt
        · exact mul_nonneg (by positivity) (tsum_nonneg fun n => mul_nonneg (ha n) (sq_nonneg _))
        · exact mul_lt_mul_of_pos_left hb (by positivity)
    _ = ε := by
        rw [mul_div_cancel₀ _ (by positivity : (0:ℝ) < 2 * Real.pi).ne']
        exact Real.sqrt_sq hε.le

/-- The dilates `θ ↦ g (ρ_k e^{iθ})` form a Cauchy sequence in `L²`. -/
lemma cauchySeq_discVal {g : ℂ → ℂ} {M : ℝ} (hg : DifferentiableOn ℂ g (Metric.ball 0 1))
    (hM : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖g z‖ ≤ M) :
    CauchySeq (fun k : ℕ =>
      (memLp_discVal hg hM (rhoSeq_mem k)).toLp (discVal g (rhoSeq k))) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨δ, hδ0, hδ⟩ := cauchy_estimate (fun n => sq_nonneg (‖tcoeff g n‖))
    (summable_normSq_tcoeff hg hM) ε hε
  have hδ1 : (0:ℝ) < min δ 1 := lt_min hδ0 one_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k ≥ N, rhoSeq k ∈ Set.Ioo (1 - min δ 1) 1 := by
    have hlim : Tendsto rhoSeq atTop (𝓝 1) := rhoSeq_tendsto.mono_right nhdsWithin_le_nhds
    have hlt : ∀ᶠ k : ℕ in atTop, rhoSeq k < 1 := Eventually.of_forall rhoSeq_lt_one
    have hgt : ∀ᶠ k : ℕ in atTop, 1 - min δ 1 < rhoSeq k :=
      hlim.eventually (eventually_gt_nhds (by linarith [hδ1] : (1:ℝ) - min δ 1 < 1))
    have hgood : ∀ᶠ k : ℕ in atTop, rhoSeq k ∈ Set.Ioo (1 - min δ 1) 1 := by
      filter_upwards [hlt, hgt] with k hk1 hk2
      exact ⟨hk2, hk1⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp hgood
    exact ⟨N, fun k hk => hN k hk⟩
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [Work.EQ.Fatou.dist_toLp_eq_sqrt (memLp_discVal hg hM (rhoSeq_mem m))
    (memLp_discVal hg hM (rhoSeq_mem n))]
  rw [integral_circM_eq_real
    (fun x : ℝ => ‖discVal g (rhoSeq m) x - discVal g (rhoSeq n) x‖ ^ 2)]
  rw [integral_normSq_sub hg (rhoSeq_pos m) (rhoSeq_lt_one m) (rhoSeq_pos n) (rhoSeq_lt_one n)]
  have hN' : ∀ k ≥ N, rhoSeq k ∈ Set.Ioo (1 - δ) 1 := fun k hk =>
    ⟨by linarith [min_le_left δ 1, (hN k hk).1], (hN k hk).2⟩
  exact hδ _ (hN' m hm) _ (hN' n hn)

/-- The boundary function: the zero extension of an `L²` class on the period. -/
noncomputable def boundExt (F : Lp ℂ 2 circM) : ℝ → ℂ :=
  Set.indicator (Set.Ioc 0 (2 * Real.pi)) (fun x => (F : ℝ → ℂ) x)

lemma integrableOn_coeFn (F : Lp ℂ 2 circM) :
    IntegrableOn (fun x => (F : ℝ → ℂ) x) (Set.Ioc 0 (2 * Real.pi)) volume :=
  (Lp.memLp F).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)

lemma integrable_boundExt (F : Lp ℂ 2 circM) : Integrable (boundExt F) volume := by
  rw [boundExt]
  rw [integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_coeFn F

lemma locallyIntegrable_boundExt (F : Lp ℂ 2 circM) :
    LocallyIntegrable (boundExt F) volume :=
  (integrable_boundExt F).locallyIntegrable

lemma boundExt_of_mem {F : Lp ℂ 2 circM} {φ : ℝ} (hφ : φ ∈ Set.Ioc 0 (2 * Real.pi)) :
    boundExt F φ = (F : ℝ → ℂ) φ := by
  rw [boundExt, Set.indicator_of_mem hφ]

/-- The `L¹` convergence of the dilates to the boundary function. -/
lemma tendsto_L1_boundExt {g : ℂ → ℂ} {M : ℝ} (hg : DifferentiableOn ℂ g (Metric.ball 0 1))
    (hM : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖g z‖ ≤ M) {F : Lp ℂ 2 circM}
    (hF : Tendsto (fun k : ℕ => (memLp_discVal hg hM (rhoSeq_mem k)).toLp (discVal g (rhoSeq k)))
      atTop (𝓝 F)) :
    Tendsto (fun k : ℕ => ∫ x, ‖discVal g (rhoSeq k) x - (F : ℝ → ℂ) x‖ ∂circM) atTop (𝓝 0) :=
  Work.EQ.Fatou.tendsto_integral_norm_of_tendsto_Lp (μ := circM) (u := fun k => discVal g (rhoSeq k))
    (fun k => memLp_discVal hg hM (rhoSeq_mem k)) hF

/-- **Poisson representation of the dilates** in terms of the boundary function. -/
lemma poisson_identity_boundExt {g : ℂ → ℂ} {M : ℝ} (hg : DifferentiableOn ℂ g (Metric.ball 0 1))
    (hM : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖g z‖ ≤ M) {F : Lp ℂ 2 circM}
    (hF : Tendsto (fun k : ℕ => (memLp_discVal hg hM (rhoSeq_mem k)).toLp (discVal g (rhoSeq k)))
      atTop (𝓝 F)) :
    ∀ r ∈ Set.Ioo (0:ℝ) 1, ∀ θ : ℝ,
      discVal g r θ = (2 * Real.pi)⁻¹ *
        (∫ φ in (0:ℝ)..2 * Real.pi, pk r (θ - φ) * boundExt F φ) := by
  have hL1 := tendsto_L1_boundExt hg hM hF
  have hL1' : Tendsto (fun k : ℕ => ∫ θ in (0:ℝ)..2 * Real.pi,
        ‖discVal g (rhoSeq k) θ - (F : ℝ → ℂ) θ‖) atTop (𝓝 0) := by
    refine hL1.congr' ?_
    filter_upwards with k
    exact integral_circM_eq_real (fun x : ℝ => ‖discVal g (rhoSeq k) x - (F : ℝ → ℂ) x‖)
  have hmain := Work.EQ.Fatou.poisson_limit hg hM rhoSeq rhoSeq_tendsto
    ((Lp.memLp F).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)) hL1'
  intro r hr θ
  have hcongr : (∫ φ in (0:ℝ)..2 * Real.pi, ((pk r (θ - φ) : ℝ) : ℂ) * boundExt F φ)
      = ∫ φ in (0:ℝ)..2 * Real.pi, ((pk r (θ - φ) : ℝ) : ℂ) * (F : ℝ → ℂ) φ := by
    rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi),
      intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with φ hφ
    rw [boundExt_of_mem hφ]
  rw [hmain r hr θ, hcongr]


/-- The dilates have an `L²` limit: the boundary function. -/
lemma exists_boundary {g : ℂ → ℂ} {M : ℝ} (hg : DifferentiableOn ℂ g (Metric.ball 0 1))
    (hM : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖g z‖ ≤ M) :
    ∃ F : Lp ℂ 2 circM,
      Tendsto (fun k : ℕ => (memLp_discVal hg hM (rhoSeq_mem k)).toLp (discVal g (rhoSeq k)))
        atTop (𝓝 F) :=
  cauchySeq_tendsto_of_complete (cauchySeq_discVal hg hM)

/-- Almost every point of the period is a point where the radial limit exists. -/
lemma ae_limit_interval {g : ℂ → ℂ} {M : ℝ} (hg : DifferentiableOn ℂ g (Metric.ball 0 1))
    (hM : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖g z‖ ≤ M) :
    ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (2 * Real.pi))),
      ∃ c : ℂ, Tendsto (fun r : ℝ => discVal g r θ) (𝓝[<] 1) (𝓝 c) := by
  obtain ⟨F, hF⟩ := exists_boundary hg hM
  refine (Work.EQ.Fatou.ae_radial_limit_of_poisson (locallyIntegrable_boundExt F)
    (poisson_identity_boundExt hg hM hF)).mono ?_
  intro θ hθ
  exact ⟨_, hθ⟩

lemma discVal_add_period {g : ℂ → ℂ} (θ : ℝ) :
    (fun r : ℝ => discVal g r (θ + 2 * Real.pi)) = fun r : ℝ => discVal g r θ := by
  funext r
  rw [discVal_apply, discVal_apply]
  congr 2
  rw [show (((θ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I
      = (θ : ℂ) * Complex.I + 2 * Real.pi * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

lemma translation_image_null {s : Set ℝ} (hs : volume s = 0) (c : ℝ) :
    volume ((fun x : ℝ => x + c) '' s) = 0 := by
  obtain ⟨t, hst, htmeas, ht0⟩ := exists_measurable_superset_of_null hs
  refine measure_mono_null (Set.image_mono hst) ?_
  have hpre : (fun x : ℝ => x + c) '' t = (fun y : ℝ => y + (-c)) ⁻¹' t := by
    ext y
    simp [sub_eq_add_neg]
  have hmap : (Measure.map (fun y : ℝ => y + (-c)) (volume : Measure ℝ)) t
      = volume ((fun y : ℝ => y + (-c)) ⁻¹' t) :=
    Measure.map_apply (f := fun y : ℝ => y + (-c)) (by fun_prop) htmeas
  rw [hpre, ← hmap, map_add_right_eq_self (volume : Measure ℝ) (-c)]
  exact ht0

/-- Almost everywhere in `ℝ` the radial limit exists. -/
lemma ae_limit_all {g : ℂ → ℂ} {M : ℝ} (hg : DifferentiableOn ℂ g (Metric.ball 0 1))
    (hM : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖g z‖ ≤ M) :
    ∀ᵐ θ : ℝ ∂(volume : Measure ℝ),
      ∃ c : ℂ, Tendsto (fun t : ℝ => g (t * Complex.exp ((θ : ℂ) * Complex.I)))
        (𝓝[<] 1) (𝓝 c) := by
  have h1 := ae_limit_interval hg hM
  rw [ae_restrict_iff' measurableSet_Ioo] at h1
  have hbad : volume {θ : ℝ | θ ∈ Set.Ioo 0 (2 * Real.pi) ∧
      ¬ (∃ c : ℂ, Tendsto (fun r : ℝ => discVal g r θ) (𝓝[<] 1) (𝓝 c))} = 0 := by
    have h1' := h1
    rw [ae_iff] at h1'
    have hS : {θ : ℝ | θ ∈ Set.Ioo 0 (2 * Real.pi) ∧
        ¬ (∃ c : ℂ, Tendsto (fun r : ℝ => discVal g r θ) (𝓝[<] 1) (𝓝 c))}
        = {a : ℝ | ¬(a ∈ Set.Ioo 0 (2 * Real.pi) →
            ∃ c : ℂ, Tendsto (fun r : ℝ => discVal g r a) (𝓝[<] 1) (𝓝 c))} := by
      ext x
      constructor
      · rintro ⟨hxI, hxQ⟩ hx
        exact hxQ (hx hxI)
      · intro h
        by_cases hI : x ∈ Set.Ioo 0 (2 * Real.pi)
        · exact ⟨hI, fun hx => h (fun _ => hx)⟩
        · exact absurd (fun hxI => absurd hxI hI) h
    rw [hS]
    exact h1'
  have hper : Function.Periodic
      (fun θ : ℝ => ∃ c : ℂ, Tendsto (fun r : ℝ => discVal g r θ) (𝓝[<] 1) (𝓝 c))
      (2 * Real.pi) := fun θ => by
    simp only [discVal_add_period θ]
  set A : Set ℝ := {θ : ℝ | θ ∈ Set.Ioo 0 (2 * Real.pi) ∧
      ¬ (∃ c : ℂ, Tendsto (fun r : ℝ => discVal g r θ) (𝓝[<] 1) (𝓝 c))} ∪ {0} with hAdef
  have hA : volume A = 0 := by
    rw [hAdef]
    refine measure_union_null hbad ?_
    simp
  rw [ae_iff]
  refine measure_mono_null (t := ⋃ k : ℤ, (fun x : ℝ => x + k * (2 * Real.pi)) '' A) ?_ ?_
  · intro θ hθ
    rw [Set.mem_iUnion]
    set k : ℤ := ⌊θ / (2 * Real.pi)⌋ with hk
    have h2π : (0:ℝ) < 2 * Real.pi := by positivity
    have hle : 0 ≤ θ - (k : ℝ) * (2 * Real.pi) := Int.sub_floor_div_mul_nonneg θ h2π
    have hlt : θ - (k : ℝ) * (2 * Real.pi) < 2 * Real.pi := Int.sub_floor_div_mul_lt θ h2π
    have hiff := Iff.of_eq (hper.int_mul k (θ - (k : ℝ) * (2 * Real.pi)))
    rw [show (θ - (k : ℝ) * (2 * Real.pi)) + k * (2 * Real.pi) = θ by ring] at hiff
    rcases eq_or_lt_of_le hle with h0 | h0
    · refine ⟨k, 0, Or.inr rfl, ?_⟩
      have : θ - (k : ℝ) * (2 * Real.pi) = 0 := h0.symm
      linarith
    · refine ⟨k, θ - (k : ℝ) * (2 * Real.pi), Or.inl ⟨⟨h0, hlt⟩, ?_⟩, by ring⟩
      exact fun hcon => hθ (hiff.mpr hcon)
  · refine measure_iUnion_null fun k => ?_
    exact translation_image_null hA ((k : ℝ) * (2 * Real.pi))

/-- **Fatou + F. and M. Riesz (Rychlik Appendix A).** A bounded holomorphic function on the
unit disc has radial limits in almost every direction, and unless it is constant equal to `c`,
the set of directions with radial limit `c` is null. -/
theorem fatou_riesz {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.ball 0 1)) {M : ℝ}
    (hM : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖g z‖ ≤ M) :
    (∀ᵐ θ : ℝ, ∃ c : ℂ,
      Tendsto (fun t : ℝ => g (t * exp (θ * I))) (𝓝[<] 1) (𝓝 c)) ∧
    ∀ c : ℂ, (∃ z ∈ Metric.ball (0 : ℂ) 1, g z ≠ c) →
      volume {θ : ℝ | Tendsto (fun t : ℝ => g (t * exp (θ * I))) (𝓝[<] 1) (𝓝 c)} = 0 := by
  refine ⟨?_, fun c hne => ?_⟩
  · simpa only [discVal_apply] using ae_limit_all hg hM
  · have h := Work.EQ.Fatou.volume_radial_limit_eq_zero hg hM hne
    simpa only [discVal_apply] using h

end Work.EQ.FR
