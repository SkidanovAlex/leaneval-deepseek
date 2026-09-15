import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Integral

open MeasureTheory Real Set
open scoped ENNReal

/-- Quantitative sub-polynomial growth of a power of the logarithm, valid for `0 ≤ B`:
there is `K > 0` with `(log x)^B ≤ K · x^ε` for all `x ≥ 1`. -/
private theorem expNegLog_log_pow_le_const_mul_rpow (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 1 ≤ x → (Real.log x) ^ B ≤ K * x ^ ε := by
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    have h1 : (Real.log x) ^ B = 1 := by rw [← hB0, Real.rpow_zero]
    rw [h1, one_mul]
    exact Real.one_le_rpow hx hε.le
  · refine ⟨(B / ε) ^ B, Real.rpow_pos_of_pos (div_pos hBpos hε) B, ?_⟩
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hεB : 0 < ε / B := div_pos hε hBpos
    have hBε : 0 < B / ε := div_pos hBpos hε
    have hlog : Real.log x ≤ x ^ (ε / B) / (ε / B) := Real.log_le_rpow_div (le_of_lt hx0) hεB
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
    have h1 : (Real.log x) ^ B ≤ (x ^ (ε / B) / (ε / B)) ^ B :=
      Real.rpow_le_rpow hlog0 hlog hBpos.le
    have h2 : (x ^ (ε / B) / (ε / B)) ^ B = x ^ ε * (B / ε) ^ B := by
      rw [Real.div_rpow (le_of_lt (Real.rpow_pos_of_pos hx0 _)) (le_of_lt hεB)]
      rw [← Real.rpow_mul (le_of_lt hx0)]
      rw [show ε / B * B = ε by field_simp]
      rw [show ε / B = (B / ε)⁻¹ by field_simp]
      rw [Real.inv_rpow (le_of_lt hBε)]
      rw [div_inv_eq_mul]
    rw [h2] at h1
    linarith [h1]

/-- Monotonicity of the `ℝ≥0∞`-valued integral of `ofReal f` under a pointwise bound. -/
private theorem expNegLog_lintegral_ofReal_le_ofReal_of_le_on {s : Set ℝ} (hs : MeasurableSet s)
    {f g : ℝ → ℝ} (h : ∀ t ∈ s, f t ≤ g t) :
    ∫⁻ t in s, ENNReal.ofReal (f t) ≤ ∫⁻ t in s, ENNReal.ofReal (g t) := by
  refine lintegral_mono_ae ?_
  rw [ae_restrict_iff' hs]
  filter_upwards with t ht
  exact ENNReal.ofReal_le_ofReal (h t ht)

/-- On a bounded interval `[a,b]`, `∫⁻ ofReal f ≤ ofReal (c·(b-a))` when `f ≤ c`. -/
private theorem expNegLog_lintegral_Icc_ofReal_le_const {a b c : ℝ} (hc : 0 ≤ c) (f : ℝ → ℝ)
    (hf : ∀ t ∈ Set.Icc a b, f t ≤ c) :
    ∫⁻ t in Set.Icc a b, ENNReal.ofReal (f t) ≤ ENNReal.ofReal (c * (b - a)) := by
  calc ∫⁻ t in Set.Icc a b, ENNReal.ofReal (f t)
      ≤ ∫⁻ t in Set.Icc a b, ENNReal.ofReal c :=
        expNegLog_lintegral_ofReal_le_ofReal_of_le_on measurableSet_Icc hf
    _ = ENNReal.ofReal c * volume (Set.Icc a b) := setLIntegral_const _ _
    _ = ENNReal.ofReal c * ENNReal.ofReal (b - a) := by rw [Real.volume_Icc]
    _ = ENNReal.ofReal (c * (b - a)) := (ENNReal.ofReal_mul hc).symm

/-- Splitting `∫⁻` over `Ici 0` at a point `T ≥ 0`. -/
private theorem expNegLog_lintegral_Ici_eq_add_Ioi (g : ℝ → ℝ≥0∞) {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ t in Set.Ici (0:ℝ), g t
      = (∫⁻ t in Set.Icc (0:ℝ) T, g t) + (∫⁻ t in Set.Ioi T, g t) := by
  have hset : Set.Icc (0:ℝ) T ∪ Set.Ioi T = Set.Ici (0:ℝ) := by
    ext x; simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ioi, Set.mem_Ici]
    constructor
    · rintro (⟨h,_⟩ | h); exacts [h, le_trans hT h.le]
    · intro h
      by_cases h1 : x ≤ T
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (lt_of_not_ge h1)
  have hdisj : Disjoint (Set.Icc (0:ℝ) T) (Set.Ioi T) := by
    rw [Set.disjoint_left]; intro x hx hy
    exact absurd hx.2 (not_le.mpr hy)
  rw [← hset, Measure.restrict_union hdisj measurableSet_Ioi, lintegral_add_measure]

/-- Region-A integral bound: `∫_0^∞ log(t+2)^B/(t+β)^A` is finite. -/
private theorem expNegLog_exists_lintegral_Ici_log_pow_div_pow_le (A B β : ℝ) (hA : 1 < A)
    (hB : 0 ≤ B) (hβ : 0 < β) :
    ∃ K : ℝ, 0 < K ∧
      ∫⁻ t in Set.Ici (0:ℝ), ENNReal.ofReal ((Real.log (t + 2)) ^ B / (t + β) ^ A)
        ≤ ENNReal.ofReal K := by
  have hε : 0 < (A - 1) / 2 := by linarith
  have hAnn : 0 ≤ A := by linarith
  obtain ⟨Klog, hKlogpos, hKlog⟩ := expNegLog_log_pow_le_const_mul_rpow B ((A-1)/2) hB hε
  have h3pow : 0 < (3:ℝ) ^ ((A-1)/2) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨(Real.log 3) ^ B * β ^ (-A) + Klog * (3:ℝ) ^ ((A-1)/2) / ((A-1)/2), by positivity, ?_⟩
  have hpt1 : ∀ t ∈ Set.Icc (0:ℝ) 1, (Real.log (t+2))^B / (t+β)^A ≤ (Real.log 3)^B * β^(-A) := by
    intro t ht
    have harg0 : 0 < t + 2 := by linarith [ht.1]
    have hlog_nonneg : 0 ≤ Real.log (t+2) := Real.log_nonneg (by linarith [ht.1])
    have hlog_le : Real.log (t+2) ≤ Real.log 3 := Real.log_le_log harg0 (by linarith [ht.2])
    have hpow : (Real.log (t+2))^B ≤ (Real.log 3)^B := Real.rpow_le_rpow hlog_nonneg hlog_le hB
    have hbase : 0 < t + β := by linarith [ht.1]
    have hβA : 0 < β^A := Real.rpow_pos_of_pos hβ A
    have hle : β^A ≤ (t+β)^A := Real.rpow_le_rpow hβ.le (by linarith [ht.1]) hAnn
    have hinv : ((t+β)^A)⁻¹ ≤ (β^A)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hβA hle
    rw [div_eq_mul_inv, Real.rpow_neg hβ.le]
    exact mul_le_mul hpow hinv (by positivity) (by positivity)
  have hpt2 : ∀ t ∈ Set.Ioi (1:ℝ),
      (Real.log (t+2))^B / (t+β)^A ≤ Klog * (3:ℝ)^((A-1)/2) * t^((A-1)/2 - A) := by
    intro t ht
    have ht1 : 1 ≤ t := le_of_lt ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    have harg1 : 1 ≤ t + 2 := by linarith
    have hlogb : (Real.log (t+2))^B ≤ Klog * (t+2)^((A-1)/2) := hKlog (t+2) harg1
    have hargle : (t+2)^((A-1)/2) ≤ ((3:ℝ)*t)^((A-1)/2) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    have hbase : 0 < t + β := by linarith
    have hle : t^A ≤ (t+β)^A := Real.rpow_le_rpow (le_of_lt ht0) (by linarith) hAnn
    have htApos : 0 < t^A := Real.rpow_pos_of_pos ht0 A
    have hinv : ((t+β)^A)⁻¹ ≤ (t^A)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le htApos hle
    have hcomb : (Real.log (t+2))^B * ((t+β)^A)⁻¹
        ≤ Klog * (3:ℝ)^((A-1)/2) * t^((A-1)/2) * (t^A)⁻¹ := by
      have h1 : (Real.log (t+2))^B ≤ Klog * (3:ℝ)^((A-1)/2) * t^((A-1)/2) := by
        calc (Real.log (t+2))^B ≤ Klog * (t+2)^((A-1)/2) := hlogb
          _ ≤ Klog * (((3:ℝ)*t)^((A-1)/2)) :=
              mul_le_mul_of_nonneg_left hargle (le_of_lt hKlogpos)
          _ = Klog * ((3:ℝ)^((A-1)/2) * t^((A-1)/2)) := by
              rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (le_of_lt ht0)]
          _ = Klog * (3:ℝ)^((A-1)/2) * t^((A-1)/2) := by ring
      exact mul_le_mul h1 hinv (by positivity) (by positivity)
    rw [div_eq_mul_inv]
    refine hcomb.trans_eq ?_
    rw [mul_assoc]
    congr 1
    rw [← Real.rpow_neg (le_of_lt ht0), ← Real.rpow_add ht0]
    congr 1
  have hI1 : ∫⁻ t in Set.Icc (0:ℝ) 1, ENNReal.ofReal ((Real.log (t+2))^B / (t+β)^A)
      ≤ ENNReal.ofReal ((Real.log 3)^B * β^(-A)) := by
    have := expNegLog_lintegral_Icc_ofReal_le_const (a := (0:ℝ)) (b := 1)
      (c := (Real.log 3)^B * β^(-A)) (by positivity) (fun t => (Real.log (t+2))^B / (t+β)^A) hpt1
    simpa using this
  have hI2 : ∫⁻ t in Set.Ioi (1:ℝ), ENNReal.ofReal ((Real.log (t+2))^B / (t+β)^A)
      ≤ ENNReal.ofReal (Klog * (3:ℝ)^((A-1)/2) / ((A-1)/2)) := by
    have hstep1 := expNegLog_lintegral_ofReal_le_ofReal_of_le_on measurableSet_Ioi hpt2
    have hconst_nonneg : 0 ≤ Klog * (3:ℝ)^((A-1)/2) := by positivity
    have hstep2 : ∫⁻ t in Set.Ioi (1:ℝ), ENNReal.ofReal (Klog * (3:ℝ)^((A-1)/2) * t^((A-1)/2 - A))
        = ENNReal.ofReal (Klog * (3:ℝ)^((A-1)/2)) * ∫⁻ t in Set.Ioi (1:ℝ), ENNReal.ofReal (t^((A-1)/2 - A)) := by
      have hcongr : ∫⁻ t in Set.Ioi (1:ℝ), ENNReal.ofReal (Klog * (3:ℝ)^((A-1)/2) * t^((A-1)/2 - A))
          = ∫⁻ t in Set.Ioi (1:ℝ), (ENNReal.ofReal (Klog * (3:ℝ)^((A-1)/2)) * ENNReal.ofReal (t^((A-1)/2 - A))) := by
        apply lintegral_congr; intro t
        rw [ENNReal.ofReal_mul hconst_nonneg]
      rw [hcongr, lintegral_const_mul']
      exact ENNReal.ofReal_ne_top
    have hInt : ∫⁻ t in Set.Ioi (1:ℝ), ENNReal.ofReal (t^((A-1)/2 - A))
        = ENNReal.ofReal (1 / ((A-1)/2)) := by
      have hint : IntegrableOn (fun t : ℝ => t^((A-1)/2 - A)) (Set.Ioi (1:ℝ)) := by
        rw [integrableOn_Ioi_rpow_iff (by norm_num : (0:ℝ) < 1)]
        linarith
      have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (1:ℝ))] (fun t : ℝ => t^((A-1)/2 - A)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one ht)) _
      rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
      congr 1
      rw [integral_Ioi_rpow_of_lt (by linarith : (A-1)/2 - A < -1) (by norm_num : (0:ℝ) < 1)]
      rw [show (A-1)/2 - A + 1 = -((A-1)/2) by ring]
      rw [Real.one_rpow, neg_div_neg_eq]
    refine hstep1.trans ?_
    rw [hstep2, hInt, ← ENNReal.ofReal_mul hconst_nonneg]
    rw [mul_one_div]
  calc ∫⁻ t in Set.Ici (0:ℝ), ENNReal.ofReal ((Real.log (t+2))^B / (t+β)^A)
      = (∫⁻ t in Set.Icc (0:ℝ) 1, ENNReal.ofReal ((Real.log (t+2))^B / (t+β)^A))
        + (∫⁻ t in Set.Ioi (1:ℝ), ENNReal.ofReal ((Real.log (t+2))^B / (t+β)^A)) := by
          have hset : Set.Icc (0:ℝ) 1 ∪ Set.Ioi (1:ℝ) = Set.Ici (0:ℝ) := by
            ext x; simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ioi, Set.mem_Ici]
            constructor
            · rintro (⟨h,_⟩ | h); exacts [h, le_trans zero_le_one h.le]
            · intro h
              by_cases h1 : x ≤ 1
              · exact Or.inl ⟨h, h1⟩
              · exact Or.inr (lt_of_not_ge h1)
          have hdisj : Disjoint (Set.Icc (0:ℝ) 1) (Set.Ioi (1:ℝ)) := by
            rw [Set.disjoint_left]; intro x hx hy; exact absurd hx.2 (not_le.mpr hy)
          rw [← hset, Measure.restrict_union hdisj measurableSet_Ioi, lintegral_add_measure]
    _ ≤ ENNReal.ofReal ((Real.log 3)^B * β^(-A))
        + ENNReal.ofReal (Klog * (3:ℝ)^((A-1)/2) / ((A-1)/2)) := add_le_add hI1 hI2
    _ = ENNReal.ofReal ((Real.log 3)^B * β^(-A) + Klog * (3:ℝ)^((A-1)/2) / ((A-1)/2)) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm

/-- Region-B integral bound, uniform in `T ≥ Tm`. -/
private theorem expNegLog_exists_lintegral_Ioi_log_pow_div_pow_le (A B β Tm : ℝ) (hA : 1 < A)
    (hB : 0 ≤ B) (hβ : 0 < β) (hTm : 0 < Tm) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℝ, Tm ≤ T →
      ∫⁻ t in Set.Ioi T, ENNReal.ofReal ((Real.log (t + 2)) ^ B / (t + β) ^ A)
        ≤ ENNReal.ofReal (K * T ^ (-((A - 1) / 2))) := by
  have hε : 0 < (A - 1) / 2 := by linarith
  have hAnn : 0 ≤ A := by linarith
  obtain ⟨Klog, hKlogpos, hKlog⟩ := expNegLog_log_pow_le_const_mul_rpow B ((A-1)/2) hB hε
  have h1Tm : 0 < 1 + 2 / Tm := by positivity
  refine ⟨Klog * (1 + 2/Tm)^((A-1)/2) / ((A-1)/2), by positivity, ?_⟩
  intro T hTmT
  have hT : 0 < T := lt_of_lt_of_le hTm hTmT
  have h1T_le : 1 + 2 / T ≤ 1 + 2 / Tm := by
    have h2 : 2 / T ≤ 2 / Tm := by
      have h3 : 1 / T ≤ 1 / Tm := one_div_le_one_div_of_le hTm hTmT
      calc 2 / T = 2 * (1/T) := by ring
        _ ≤ 2 * (1/Tm) := by linarith
        _ = 2 / Tm := by ring
    linarith
  have hpt : ∀ t ∈ Set.Ioi T,
      (Real.log (t+2))^B / (t+β)^A ≤ Klog * (1 + 2/Tm)^((A-1)/2) * t^((A-1)/2 - A) := by
    intro t ht
    have htT : T < t := ht
    have ht0 : 0 < t := lt_trans hT htT
    have harg1 : 1 ≤ t + 2 := by linarith
    have hlogb : (Real.log (t+2))^B ≤ Klog * (t+2)^((A-1)/2) := hKlog (t+2) harg1
    have h2t : t + 2 ≤ t * (1 + 2/T) := by
      rw [mul_add, mul_one]; field_simp; nlinarith [hT, htT]
    have hargle : (t+2)^((A-1)/2) ≤ (t * (1 + 2/T))^((A-1)/2) :=
      Real.rpow_le_rpow (by linarith) h2t (by linarith)
    have hargle2 : (t * (1 + 2/T))^((A-1)/2) ≤ (t * (1 + 2/Tm))^((A-1)/2) :=
      Real.rpow_le_rpow (by positivity) (by nlinarith) (by linarith)
    have hbase : 0 < t + β := by linarith
    have hle : t^A ≤ (t+β)^A := Real.rpow_le_rpow (le_of_lt ht0) (by linarith) hAnn
    have htApos : 0 < t^A := Real.rpow_pos_of_pos ht0 A
    have hinv : ((t+β)^A)⁻¹ ≤ (t^A)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le htApos hle
    have hcomb : (Real.log (t+2))^B * ((t+β)^A)⁻¹
        ≤ Klog * (1 + 2/Tm)^((A-1)/2) * t^((A-1)/2) * (t^A)⁻¹ := by
      have h1 : (Real.log (t+2))^B ≤ Klog * (1 + 2/Tm)^((A-1)/2) * t^((A-1)/2) := by
        calc (Real.log (t+2))^B ≤ Klog * (t+2)^((A-1)/2) := hlogb
          _ ≤ Klog * ((t * (1 + 2/T))^((A-1)/2)) :=
              mul_le_mul_of_nonneg_left hargle (le_of_lt hKlogpos)
          _ ≤ Klog * ((t * (1 + 2/Tm))^((A-1)/2)) :=
              mul_le_mul_of_nonneg_left hargle2 (le_of_lt hKlogpos)
          _ = Klog * ((1 + 2/Tm)^((A-1)/2) * t^((A-1)/2)) := by
              rw [Real.mul_rpow (le_of_lt ht0) (by positivity)]
              ring
          _ = Klog * (1 + 2/Tm)^((A-1)/2) * t^((A-1)/2) := by ring
      exact mul_le_mul h1 hinv (by positivity) (by positivity)
    rw [div_eq_mul_inv]
    refine hcomb.trans_eq ?_
    rw [mul_assoc]
    congr 1
    rw [← Real.rpow_neg (le_of_lt ht0), ← Real.rpow_add ht0]
    congr 1
  have hstep1 := expNegLog_lintegral_ofReal_le_ofReal_of_le_on measurableSet_Ioi hpt
  have hconst_nonneg : 0 ≤ Klog * (1 + 2/Tm)^((A-1)/2) := by positivity
  have hstep2 : ∫⁻ t in Set.Ioi T, ENNReal.ofReal (Klog * (1 + 2/Tm)^((A-1)/2) * t^((A-1)/2 - A))
      = ENNReal.ofReal (Klog * (1 + 2/Tm)^((A-1)/2)) * ∫⁻ t in Set.Ioi T, ENNReal.ofReal (t^((A-1)/2 - A)) := by
    have hcongr : ∫⁻ t in Set.Ioi T, ENNReal.ofReal (Klog * (1 + 2/Tm)^((A-1)/2) * t^((A-1)/2 - A))
        = ∫⁻ t in Set.Ioi T, (ENNReal.ofReal (Klog * (1 + 2/Tm)^((A-1)/2)) * ENNReal.ofReal (t^((A-1)/2 - A))) := by
      apply lintegral_congr; intro t
      rw [ENNReal.ofReal_mul hconst_nonneg]
    rw [hcongr, lintegral_const_mul']
    exact ENNReal.ofReal_ne_top
  have hInt : ∫⁻ t in Set.Ioi T, ENNReal.ofReal (t^((A-1)/2 - A))
      = ENNReal.ofReal (T ^ (-((A-1)/2)) / ((A-1)/2)) := by
    have hint : IntegrableOn (fun t : ℝ => t^((A-1)/2 - A)) (Set.Ioi T) := by
      rw [integrableOn_Ioi_rpow_iff hT]
      linarith
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi T)] (fun t : ℝ => t^((A-1)/2 - A)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Real.rpow_nonneg (le_of_lt (lt_trans hT ht)) _
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    congr 1
    rw [integral_Ioi_rpow_of_lt (by linarith : (A-1)/2 - A < -1) hT]
    rw [show (A-1)/2 - A + 1 = -((A-1)/2) by ring]
    rw [neg_div_neg_eq]
  refine hstep1.trans ?_
  rw [hstep2, hInt, ← ENNReal.ofReal_mul hconst_nonneg]
  apply ENNReal.ofReal_le_ofReal
  exact le_of_eq (by ring)

/-- **Target lemma.** For `A > 1`, `B ≥ 0`, `β > 0` there are constants `δ, C > 0` with
`∫_0^∞ exp(-(βL)/log(t+2)) · log(t+2)^B / (t+β)^A dt ≤ C · exp(-δ√L)` for all `L ≥ 2`. -/
theorem exp_neg_log_div_log_pow_integral_le (A B β : ℝ) (hA : 1 < A) (hB : 0 ≤ B) (hβ : 0 < β) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ L : ℝ, 2 ≤ L →
      (∫ t in Set.Ici (0 : ℝ),
        Real.exp (-(β * L) / Real.log (t + 2)) * (Real.log (t + 2)) ^ B / (t + β) ^ A)
        ≤ C * Real.exp (-(δ * Real.sqrt L)) := by
  have hε : 0 < (A - 1) / 2 := by linarith
  have hAnn : 0 ≤ A := by linarith
  obtain ⟨K1, hK1pos, hK1⟩ := expNegLog_exists_lintegral_Ici_log_pow_div_pow_le A B β hA hB hβ
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt1 : Real.log 2 < 1 := by
    rw [Real.log_lt_iff_lt_exp (show (0:ℝ) < 2 by norm_num)]; exact Real.exp_one_gt_two
  have hlt_sqrt2 : Real.log 2 < Real.sqrt (Real.log 2) := by
    rw [Real.lt_sqrt hlog2pos.le]; nlinarith [hlog2pos, hlog2lt1]
  set Tm : ℝ := Real.exp (Real.sqrt (Real.log 2)) - 2 with hTmdef
  have hTmpos : 0 < Tm := by
    rw [hTmdef]
    have h2 : (2:ℝ) < Real.exp (Real.sqrt (Real.log 2)) := by
      have h := Real.exp_lt_exp.mpr hlt_sqrt2
      rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at h
    linarith
  obtain ⟨K2, hK2pos, hK2⟩ := expNegLog_exists_lintegral_Ioi_log_pow_div_pow_le A B β Tm hA hB hβ hTmpos
  set L4 : ℝ := Real.log 4 with hL4def
  have hL4pos : 0 < L4 := by rw [hL4def]; exact Real.log_pos (by norm_num)
  set δ : ℝ := min β ((A - 1) / 2) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min hβ hε
  have hδβ : δ ≤ β := by rw [hδdef]; exact min_le_left _ _
  have hδε : δ ≤ (A - 1) / 2 := by rw [hδdef]; exact min_le_right _ _
  set C1 : ℝ := K1 + K2 * (2:ℝ)^((A-1)/2) with hC1def
  set C2 : ℝ := (K1 + K2 * Tm^(-((A-1)/2))) * Real.exp (δ * L4) with hC2def
  have hC1pos : 0 < C1 := by rw [hC1def]; positivity
  have hC2pos : 0 < C2 := by rw [hC2def]; positivity
  refine ⟨δ, C1 + C2, hδpos, by positivity, ?_⟩
  intro L hL
  have hLpos : 0 < L := by linarith
  have hsqrtL_nn : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hL2 : Real.log 2 ≤ L := by linarith [hlog2lt1]
  have hsqrt_le : Real.sqrt (Real.log 2) ≤ Real.sqrt L := Real.sqrt_le_sqrt hL2
  have hlog2_lt_sqrtL : Real.log 2 < Real.sqrt L := lt_of_lt_of_le hlt_sqrt2 hsqrt_le
  have h2_lt_exp : (2:ℝ) < Real.exp (Real.sqrt L) := by
    have h := Real.exp_lt_exp.mpr hlog2_lt_sqrtL
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at h
  set T : ℝ := Real.exp (Real.sqrt L) - 2 with hTdef
  have hTpos : 0 < T := by rw [hTdef]; linarith
  have hTm_le_T : Tm ≤ T := by
    rw [hTmdef, hTdef]
    exact sub_le_sub_right (Real.exp_le_exp.mpr hsqrt_le) 2
  set F : ℝ → ℝ := fun t => Real.exp (-(β * L) / Real.log (t + 2)) * (Real.log (t + 2)) ^ B / (t + β) ^ A
    with hFdef
  have hFmeas : Measurable F := by rw [hFdef]; measurability
  have hFnn : ∀ t ∈ Set.Ici (0:ℝ), 0 ≤ F t := by
    intro t ht
    have ht0 : 0 ≤ t := ht
    have hlog_pos : 0 < Real.log (t+2) := Real.log_pos (by linarith)
    have hnum : 0 ≤ Real.exp (-(β * L) / Real.log (t + 2)) * (Real.log (t + 2)) ^ B :=
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hlog_pos.le _)
    rw [hFdef]
    exact div_nonneg hnum (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ t + β) _)
  have hFae : 0 ≤ᵐ[volume.restrict (Set.Ici (0:ℝ))] F := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact hFnn t ht
  have hApt : ∀ t ∈ Set.Icc (0:ℝ) T,
      F t ≤ Real.exp (-(β * Real.sqrt L)) * ((Real.log (t+2))^B / (t+β)^A) := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have htT : t ≤ T := ht.2
    have harg0 : 0 < t + 2 := by linarith
    have hlog_pos : 0 < Real.log (t+2) := Real.log_pos (by linarith)
    have harg_le : Real.log (t+2) ≤ Real.sqrt L := by
      have h1 : t + 2 ≤ Real.exp (Real.sqrt L) := by rw [hTdef] at htT; linarith
      calc Real.log (t+2) ≤ Real.log (Real.exp (Real.sqrt L)) := Real.log_le_log harg0 h1
        _ = Real.sqrt L := Real.log_exp _
    have hle1 : 1 ≤ Real.sqrt L / Real.log (t+2) := by
      rw [le_div_iff₀ hlog_pos]; simpa using harg_le
    have hkey : β * Real.sqrt L ≤ L * β / Real.log (t+2) := by
      have h1 : β * Real.sqrt L * 1 ≤ β * Real.sqrt L * (Real.sqrt L / Real.log (t+2)) :=
        mul_le_mul_of_nonneg_left hle1 (by positivity)
      rw [mul_one] at h1
      calc β * Real.sqrt L ≤ β * Real.sqrt L * (Real.sqrt L / Real.log (t+2)) := h1
        _ = L * β / Real.log (t+2) := by
              field_simp
              ring_nf
              rw [Real.sq_sqrt hLpos.le]
    have hkey' : -(β * L) / Real.log (t + 2) ≤ -(β * Real.sqrt L) := by
      rw [neg_div, neg_le_neg_iff, mul_comm β L]
      exact hkey
    have hnn : 0 ≤ (Real.log (t+2))^B / (t+β)^A :=
      div_nonneg (Real.rpow_nonneg hlog_pos.le _) (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ t+β) _)
    rw [hFdef]
    calc Real.exp (-(β * L) / Real.log (t + 2)) * (Real.log (t + 2))^B / (t+β)^A
        = Real.exp (-(β * L) / Real.log (t + 2)) * ((Real.log (t + 2))^B / (t+β)^A) := by ring
      _ ≤ Real.exp (-(β * Real.sqrt L)) * ((Real.log (t + 2))^B / (t+β)^A) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hkey') hnn
  have hBpt : ∀ t ∈ Set.Ioi T, F t ≤ (Real.log (t+2))^B / (t+β)^A := by
    intro t ht
    have htT : T < t := ht
    have hlog_pos : 0 < Real.log (t+2) := Real.log_pos (by linarith [hTpos])
    have hnn : 0 ≤ (Real.log (t+2))^B / (t+β)^A :=
      div_nonneg (Real.rpow_nonneg hlog_pos.le _) (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ t+β) _)
    have hexp1 : Real.exp (-(β * L) / Real.log (t + 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div]
      have : 0 ≤ (β * L) / Real.log (t+2) := div_nonneg (by positivity) hlog_pos.le
      linarith
    rw [hFdef]
    calc Real.exp (-(β * L) / Real.log (t + 2)) * (Real.log (t + 2))^B / (t+β)^A
        = Real.exp (-(β * L) / Real.log (t + 2)) * ((Real.log (t+2))^B / (t+β)^A) := by ring
      _ ≤ 1 * ((Real.log (t+2))^B / (t+β)^A) := mul_le_mul_of_nonneg_right hexp1 hnn
      _ = (Real.log (t+2))^B / (t+β)^A := one_mul _
  have hAreg : ∫⁻ t in Set.Icc (0:ℝ) T, ENNReal.ofReal (F t)
      ≤ ENNReal.ofReal (Real.exp (-(β * Real.sqrt L)) * K1) := by
    have h1 := expNegLog_lintegral_ofReal_le_ofReal_of_le_on measurableSet_Icc hApt
    have hcn : 0 ≤ Real.exp (-(β * Real.sqrt L)) := Real.exp_nonneg _
    have h2 : ∫⁻ t in Set.Icc (0:ℝ) T,
          ENNReal.ofReal (Real.exp (-(β * Real.sqrt L)) * ((Real.log (t+2))^B / (t+β)^A))
        = ENNReal.ofReal (Real.exp (-(β * Real.sqrt L)))
          * ∫⁻ t in Set.Icc (0:ℝ) T, ENNReal.ofReal ((Real.log (t+2))^B / (t+β)^A) := by
      rw [show (∫⁻ t in Set.Icc (0:ℝ) T,
            ENNReal.ofReal (Real.exp (-(β * Real.sqrt L)) * ((Real.log (t+2))^B / (t+β)^A)))
          = ∫⁻ t in Set.Icc (0:ℝ) T,
            ENNReal.ofReal (Real.exp (-(β * Real.sqrt L))) * ENNReal.ofReal ((Real.log (t+2))^B / (t+β)^A) from by
            apply lintegral_congr; intro t; rw [ENNReal.ofReal_mul hcn]]
      rw [lintegral_const_mul']
      exact ENNReal.ofReal_ne_top
    have h3 : ∫⁻ t in Set.Icc (0:ℝ) T, ENNReal.ofReal ((Real.log (t+2))^B / (t+β)^A)
        ≤ ENNReal.ofReal K1 :=
      le_trans (lintegral_mono_set Set.Icc_subset_Ici_self) hK1
    calc ∫⁻ t in Set.Icc (0:ℝ) T, ENNReal.ofReal (F t)
        ≤ ∫⁻ t in Set.Icc (0:ℝ) T,
            ENNReal.ofReal (Real.exp (-(β * Real.sqrt L)) * ((Real.log (t+2))^B / (t+β)^A)) := h1
      _ = ENNReal.ofReal (Real.exp (-(β * Real.sqrt L)))
          * ∫⁻ t in Set.Icc (0:ℝ) T, ENNReal.ofReal ((Real.log (t+2))^B / (t+β)^A) := h2
      _ ≤ ENNReal.ofReal (Real.exp (-(β * Real.sqrt L))) * ENNReal.ofReal K1 := by gcongr
      _ = ENNReal.ofReal (Real.exp (-(β * Real.sqrt L)) * K1) := (ENNReal.ofReal_mul hcn).symm
  have hBreg : ∫⁻ t in Set.Ioi T, ENNReal.ofReal (F t)
      ≤ ENNReal.ofReal (K2 * T ^ (-((A-1)/2))) :=
    le_trans (expNegLog_lintegral_ofReal_le_ofReal_of_le_on measurableSet_Ioi hBpt) (hK2 T hTm_le_T)
  have hlin : ∫⁻ t in Set.Ici (0:ℝ), ENNReal.ofReal (F t)
      ≤ ENNReal.ofReal (Real.exp (-(β * Real.sqrt L)) * K1 + K2 * T ^ (-((A-1)/2))) := by
    rw [expNegLog_lintegral_Ici_eq_add_Ioi (fun t => ENNReal.ofReal (F t)) hTpos.le]
    refine (add_le_add hAreg hBreg).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hreal : Real.exp (-(β * Real.sqrt L)) * K1 + K2 * T ^ (-((A-1)/2))
      ≤ (C1 + C2) * Real.exp (-(δ * Real.sqrt L)) := by
    have hexpβ : Real.exp (-(β * Real.sqrt L)) ≤ Real.exp (-(δ * Real.sqrt L)) :=
      Real.exp_le_exp.mpr (by nlinarith [hδβ, hsqrtL_nn])
    have hεexp : Real.exp (-((A-1)/2) * Real.sqrt L) ≤ Real.exp (-(δ * Real.sqrt L)) :=
      Real.exp_le_exp.mpr (by nlinarith [hδε, hsqrtL_nn])
    by_cases hcase : L4 ≤ Real.sqrt L
    · have hTge : Real.exp (Real.sqrt L) / 2 ≤ T := by
        rw [hTdef]
        have h4 : (4:ℝ) ≤ Real.exp (Real.sqrt L) := by
          have h := Real.exp_le_exp.mpr hcase
          rwa [hL4def, Real.exp_log (by norm_num : (0:ℝ) < 4)] at h
        linarith
      have hTexpo : T ^ (-((A-1)/2)) ≤ (2:ℝ)^((A-1)/2) * Real.exp (-((A-1)/2) * Real.sqrt L) := by
        have h1 : T ^ (-((A-1)/2)) ≤ (Real.exp (Real.sqrt L) / 2) ^ (-((A-1)/2)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hTge (by linarith)
        have h2 : (Real.exp (Real.sqrt L) / 2) ^ (-((A-1)/2))
            = (2:ℝ)^((A-1)/2) * Real.exp (-((A-1)/2) * Real.sqrt L) := by
          rw [Real.div_rpow (Real.exp_nonneg _) (by norm_num : (0:ℝ) ≤ 2)]
          rw [show (Real.exp (Real.sqrt L)) ^ (-((A-1)/2)) = Real.exp (-((A-1)/2) * Real.sqrt L) from by
                rw [← Real.exp_mul]; congr 1; ring]
          rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_inv_eq_mul]; ring
        exact h1.trans (le_of_eq h2)
      have h2nn : (0:ℝ) ≤ (2:ℝ)^((A-1)/2) := by positivity
      calc Real.exp (-(β * Real.sqrt L)) * K1 + K2 * T ^ (-((A-1)/2))
          ≤ K1 * Real.exp (-(δ * Real.sqrt L))
            + K2 * ((2:ℝ)^((A-1)/2) * Real.exp (-(δ * Real.sqrt L))) := by
            have h1 : Real.exp (-(β * Real.sqrt L)) * K1 ≤ K1 * Real.exp (-(δ * Real.sqrt L)) := by
              rw [mul_comm]; exact mul_le_mul_of_nonneg_left hexpβ hK1pos.le
            have h2 : K2 * T ^ (-((A-1)/2)) ≤ K2 * ((2:ℝ)^((A-1)/2) * Real.exp (-(δ * Real.sqrt L))) :=
              mul_le_mul_of_nonneg_left (hTexpo.trans (mul_le_mul_of_nonneg_left hεexp h2nn)) hK2pos.le
            linarith
        _ = C1 * Real.exp (-(δ * Real.sqrt L)) := by rw [hC1def]; ring
        _ ≤ (C1 + C2) * Real.exp (-(δ * Real.sqrt L)) :=
            mul_le_mul_of_nonneg_right (by linarith [hC2pos]) (Real.exp_nonneg _)
    · push_neg at hcase
      have hTexpo : T ^ (-((A-1)/2)) ≤ Tm ^ (-((A-1)/2)) :=
        Real.rpow_le_rpow_of_nonpos hTmpos hTm_le_T (by linarith)
      have hβ1 : Real.exp (-(β * Real.sqrt L)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [hβ, hsqrtL_nn]
      have hge1 : 1 ≤ Real.exp (δ * L4) * Real.exp (-(δ * Real.sqrt L)) := by
        rw [← Real.exp_add, show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]
        exact Real.exp_le_exp.mpr (by nlinarith [hδpos, hcase])
      calc Real.exp (-(β * Real.sqrt L)) * K1 + K2 * T ^ (-((A-1)/2))
          ≤ K1 * 1 + K2 * Tm ^ (-((A-1)/2)) := by
            have h1 : Real.exp (-(β * Real.sqrt L)) * K1 ≤ K1 * 1 := by
              rw [mul_comm]; exact mul_le_mul_of_nonneg_left hβ1 hK1pos.le
            have h2 : K2 * T ^ (-((A-1)/2)) ≤ K2 * Tm ^ (-((A-1)/2)) :=
              mul_le_mul_of_nonneg_left hTexpo hK2pos.le
            linarith
        _ = (K1 + K2 * Tm ^ (-((A-1)/2))) * 1 := by ring
        _ ≤ (K1 + K2 * Tm ^ (-((A-1)/2))) * (Real.exp (δ * L4) * Real.exp (-(δ * Real.sqrt L))) :=
            mul_le_mul_of_nonneg_left hge1 (by positivity)
        _ = C2 * Real.exp (-(δ * Real.sqrt L)) := by rw [hC2def]; ring
        _ ≤ (C1 + C2) * Real.exp (-(δ * Real.sqrt L)) :=
            mul_le_mul_of_nonneg_right (by linarith [hC1pos]) (Real.exp_nonneg _)
  rw [integral_eq_lintegral_of_nonneg_ae hFae hFmeas.aestronglyMeasurable.restrict]
  calc (∫⁻ t in Set.Ici (0:ℝ), ENNReal.ofReal (F t)).toReal
      ≤ (ENNReal.ofReal (Real.exp (-(β * Real.sqrt L)) * K1 + K2 * T ^ (-((A-1)/2)))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
    _ = Real.exp (-(β * Real.sqrt L)) * K1 + K2 * T ^ (-((A-1)/2)) :=
        ENNReal.toReal_ofReal (by positivity)
    _ ≤ (C1 + C2) * Real.exp (-(δ * Real.sqrt L)) := hreal

end Commons.Analysis.Integral