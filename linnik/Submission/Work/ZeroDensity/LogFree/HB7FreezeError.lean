import Mathlib
import Submission.Work.ZeroDensity.LogFree.poleLSDefs
import Submission.Work.ZeroDensity.LogFree.FreezeRpowIdentity
import Submission.Work.ZeroDensity.LogFree.IntervalNormSqCauchySchwarz
import Submission.Work.ZeroDensity.LogFree.HB7MvtAny
import Submission.Work.ZeroDensity.LogFree.HB7FreezeIntegrable

open MeasureTheory
open scoped BigOperators

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Work.ZeroDensity.LogFree

/-! ### Auxiliary lemmas for the freeze-error estimate

A bounded measurable function on a compact interval is interval integrable, and a bounded
measurable kernel is integrable on a rectangle, with Fubini for the two interval integrals. -/

lemma hb7_intervalIntegrable_of_bound {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioc a b))) {M : ℝ}
    (hb : ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M) : IntervalIntegrable f volume a b := by
  refine ⟨?_, ?_⟩
  · exact MeasureTheory.IntegrableOn.of_bound (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
      hf M (by
        filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
        exact hb x (Set.Ioc_subset_Icc_self hx))
  · rw [Set.Ioc_eq_empty_iff.mpr (not_lt.mpr hab)]
    exact MeasureTheory.integrableOn_empty

lemma hb7_integrable_uncurry {Y₁ Y B : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Measurable (Function.uncurry F)) {M : ℝ} (hMnn : 0 ≤ M)
    (hM : ∀ b y, b ∈ Set.Icc 0 B → y ∈ Set.Icc Y₁ Y → ‖F b y‖ ≤ M) :
    Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioc 0 B)).prod (volume.restrict (Set.Ioc Y₁ Y))) := by
  refine Integrable.mono (integrable_const M) ?_ ?_
  · rw [Measure.prod_restrict]
    exact hF.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  · rw [Measure.prod_restrict]
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    obtain ⟨h1, h2⟩ := Set.mem_prod.mp hp
    have hF' : ‖F p.1 p.2‖ ≤ M := hM p.1 p.2 (Set.Ioc_subset_Icc_self h1)
      (Set.Ioc_subset_Icc_self h2)
    have hun : Function.uncurry F p = F p.1 p.2 := rfl
    have hc : ‖(fun _ : ℝ × ℝ => M) p‖ = M := by
      simp only [Real.norm_eq_abs, abs_of_nonneg hMnn]
    rw [hun, hc]
    exact hF'

lemma hb7_swap {Y₁ Y B : ℝ} (hY₁Y : Y₁ ≤ Y) (hB : 0 ≤ B) {F : ℝ → ℝ → ℝ}
    (hF : Measurable (Function.uncurry F)) {M : ℝ} (hMnn : 0 ≤ M)
    (hM : ∀ b y, b ∈ Set.Icc 0 B → y ∈ Set.Icc Y₁ Y → ‖F b y‖ ≤ M) :
    (∫ y in Y₁..Y, ∫ b in 0..B, F b y) = ∫ b in 0..B, ∫ y in Y₁..Y, F b y := by
  have hint := hb7_integrable_uncurry hF hMnn hM
  have hsw := MeasureTheory.integral_integral_swap hint
  have hconv1 : (∫ y in Y₁..Y, ∫ b in 0..B, F b y)
      = ∫ y, (∫ b : ℝ, F b y ∂(volume.restrict (Set.Ioc 0 B)))
          ∂(volume.restrict (Set.Ioc Y₁ Y)) := by
    rw [intervalIntegral.integral_of_le hY₁Y]
    congr 1
    funext y
    rw [intervalIntegral.integral_of_le hB]
  have hconv2 : (∫ b in 0..B, ∫ y in Y₁..Y, F b y)
      = ∫ b, (∫ y : ℝ, F b y ∂(volume.restrict (Set.Ioc Y₁ Y)))
          ∂(volume.restrict (Set.Ioc 0 B)) := by
    rw [intervalIntegral.integral_of_le hB]
    congr 1
    funext b
    rw [intervalIntegral.integral_of_le hY₁Y]
  rw [hconv1, hconv2]
  exact hsw.symm

/-- Mean-value bound for the frozen-amplitude family of the freeze error at a fixed freezing
parameter `b`: the family `Σ_{i : b ≤ a i} z i Y^{a i} y^{-i γ i}` has `1/L`-separated
frequencies, so `MvtMul` with `δ = 1/L` on `[Y e^{-L}, Y]` gives
`(log e^L + C L) Σ_{i : b ≤ a i} ‖z i‖² Y^{2 a i} ≤ (1+C) L Σ_i ‖z i‖² Y^{2 a i}`. -/
lemma hb7_freeze_mvt_bound {C : ℝ} (hC : 0 < C) (hMVT : Work.ZeroDensity.LogFree.MvtMul C)
    {ι : Type*} [Fintype ι] (a γ : ι → ℝ) (z : ι → ℂ) {Y L : ℝ} (hY : 0 < Y) (hL : 1 ≤ L)
    (haL : ∀ i, a i ≤ 1 / L) (hsep : ∀ i j, i ≠ j → 1 / L ≤ |γ i - γ j|) (b : ℝ) :
    (∫ y in (Y * Real.exp (-L))..Y,
        ‖∑ i, (if b ≤ a i then z i * ((Y ^ (a i) : ℝ) : ℂ) else 0)
            * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / y)
      ≤ (C + 1) * L * ∑ i, ‖z i‖ ^ 2 * Y ^ (2 * a i) := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hδ : 0 < 1 / L := by positivity
  have hY1pos : 0 < Y * Real.exp (-L) := mul_pos hY (Real.exp_pos _)
  have hY1le : Y * Real.exp (-L) ≤ Y := by
    have hle : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [Real.exp_pos (-L)]
  have hmvt := Work.ZeroDensity.LogFree.HB7MvtAny hMVT (1 / L) hδ γ
    (fun i => if b ≤ a i then z i * ((Y ^ (a i) : ℝ) : ℂ) else 0)
    (Y * Real.exp (-L)) Y hY1pos hY1le hsep
  have hlog : Real.log (Y / (Y * Real.exp (-L))) + C / (1 / L) = (C + 1) * L := by
    have h1 : Y / (Y * Real.exp (-L)) = Real.exp L := by
      rw [div_eq_iff (by positivity : Y * Real.exp (-L) ≠ 0), ← mul_assoc,
        mul_comm (Real.exp L) Y, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
        mul_one]
    rw [h1, Real.log_exp]
    field_simp
    ring
  have hsq : ∀ i : ι, ‖((Y ^ (a i) : ℝ) : ℂ)‖ ^ 2 = Y ^ (2 * a i) := by
    intro i
    have h1 : ‖((Y ^ (a i) : ℝ) : ℂ)‖ ^ 2 = (Y ^ (a i)) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
    rw [h1, ← Real.rpow_mul_natCast hY.le (a i) 2]
    congr 1
    ring
  have hsum : (∑ i, ‖(if b ≤ a i then z i * ((Y ^ (a i) : ℝ) : ℂ) else 0)‖ ^ 2)
      ≤ ∑ i, ‖z i‖ ^ 2 * Y ^ (2 * a i) := by
    apply Finset.sum_le_sum
    intro i _
    by_cases h : b ≤ a i
    · rw [if_pos h, norm_mul, mul_pow, hsq i]
    · rw [if_neg h, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
  calc (∫ y in (Y * Real.exp (-L))..Y,
        ‖∑ i, (if b ≤ a i then z i * ((Y ^ (a i) : ℝ) : ℂ) else 0)
            * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / y)
      ≤ (Real.log (Y / (Y * Real.exp (-L))) + C / (1 / L))
          * ∑ i, ‖(if b ≤ a i then z i * ((Y ^ (a i) : ℝ) : ℂ) else 0)‖ ^ 2 := hmvt
    _ = (C + 1) * L * (∑ i, ‖(if b ≤ a i then z i * ((Y ^ (a i) : ℝ) : ℂ) else 0)‖ ^ 2) := by
        rw [hlog]
    _ ≤ (C + 1) * L * ∑ i, ‖z i‖ ^ 2 * Y ^ (2 * a i) := by
        refine mul_le_mul_of_nonneg_left hsum ?_
        have hpos : (0 : ℝ) < C + 1 := by linarith
        positivity


/-- Pointwise norm bound of the freeze-block: on `Y e^{-L} ≤ y ≤ Y` the freeze error is bounded by
`L` times the interval integral over the freezing parameter of the frozen-amplitude family. -/
lemma hb7_freeze_norm_bound {ι : Type*} [Fintype ι] (a γ : ι → ℝ) (z : ι → ℂ) {Y L y : ℝ}
    (hY : 0 < Y) (hL : 0 < L) (hy1 : Y * Real.exp (-L) ≤ y) (hy2 : y ≤ Y)
    (ha0 : ∀ i, 0 ≤ a i) (haL : ∀ i, a i ≤ 1 / L) :
    ‖∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ) * ((((y / Y) ^ (a i) - 1 : ℝ)) : ℂ)
        * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖
      ≤ L * ∫ b in (0)..(1 / L),
          ‖∑ i, (if b ≤ a i then z i * ((Y ^ (a i) : ℝ) : ℂ) else 0)
              * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ := by
  have hypos : 0 < y := lt_of_lt_of_le (mul_pos hY (Real.exp_pos _)) hy1
  have htpos : 0 < y / Y := div_pos hypos hY
  have htle : y / Y ≤ 1 := (div_le_one hY).mpr hy2
  have hBnn : 0 ≤ 1 / L := by positivity
  have hlog_ub : Real.log (y / Y) ≤ 0 := Real.log_nonpos (le_of_lt htpos) htle
  have hlog_lb : -L ≤ Real.log (y / Y) := by
    have hle : Real.exp (-L) ≤ y / Y := by
      rw [le_div_iff₀ hY]; linarith
    have h' := Real.log_le_log (Real.exp_pos (-L)) hle
    rwa [Real.log_exp] at h'
  have hlog_abs : |Real.log (y / Y)| ≤ L := abs_le.mpr ⟨hlog_lb, le_trans hlog_ub hL.le⟩
  let S : ℝ → ℂ := fun b => ∑ i, (if b ≤ a i then z i * ((Y ^ (a i) : ℝ) : ℂ) else 0)
      * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)
  have hfreeze : (∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ) * ((((y / Y) ^ (a i) - 1 : ℝ)) : ℂ)
        * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I))
      = ∫ b in (0)..(1 / L), ((Real.log (y / Y) : ℝ) : ℂ)
          * (S b * ((((y / Y) ^ b : ℝ)) : ℂ)) := by
    have hmain := FreezeRpowIdentity (ι := ι)
      (fun i => z i * ((Y ^ (a i) : ℝ) : ℂ) * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)) a
      htpos hBnn ha0 haL
    have hLHS : (∑ i, (z i * ((Y ^ (a i) : ℝ) : ℂ) * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I))
          * ((((y / Y) ^ (a i) - 1 : ℝ)) : ℂ))
        = ∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ) * ((((y / Y) ^ (a i) - 1 : ℝ)) : ℂ)
            * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hRHS : (∫ b in (0)..(1 / L), ((Real.log (y / Y) : ℝ) : ℂ)
          * (∑ i, (if b ≤ a i then z i * ((Y ^ (a i) : ℝ) : ℂ)
                * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I) else 0) * ((((y / Y) ^ b : ℝ)) : ℂ)))
        = ∫ b in (0)..(1 / L), ((Real.log (y / Y) : ℝ) : ℂ)
            * (S b * ((((y / Y) ^ b : ℝ)) : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro b _
      beta_reduce
      rw [show S b = ∑ i, (if b ≤ a i then z i * ((Y ^ (a i) : ℝ) : ℂ) else 0)
          * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I) from rfl, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : b ≤ a i
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]; ring
    rw [hLHS, hRHS] at hmain
    exact hmain
  have hT_le : ∀ b ∈ Set.Icc 0 (1 / L), ‖S b * ((((y / Y) ^ b : ℝ)) : ℂ)‖ ≤ ‖S b‖ := by
    intro b hb
    obtain ⟨hb0, _⟩ := Set.mem_Icc.mp hb
    have ht1 : (y / Y) ^ b ≤ 1 := Real.rpow_le_one (le_of_lt htpos) htle hb0
    have ht0 : 0 ≤ (y / Y) ^ b := Real.rpow_nonneg (le_of_lt htpos) b
    rw [show S b * ((((y / Y) ^ b : ℝ)) : ℂ) = ((y / Y) ^ b) • S b from by
      rw [Complex.real_smul]; ring]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc (y / Y) ^ b * ‖S b‖ ≤ 1 * ‖S b‖ := mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
      _ = ‖S b‖ := one_mul _
  have hmeasS : Measurable S := by
    show Measurable (fun b : ℝ => ∑ i, (if b ≤ a i then z i * ((Y ^ (a i) : ℝ) : ℂ) else 0)
        * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I))
    apply Finset.measurable_sum
    intro i _
    exact (Measurable.ite measurableSet_Iic measurable_const measurable_const).mul measurable_const
  have hnorm1 : ∀ i, ‖(y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ = 1 := by
    intro i
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hypos]
    have hre : ((-(γ i : ℂ)) * Complex.I).re = 0 := by simp [Complex.mul_re]
    rw [hre, Real.rpow_zero]
  have hSf_le : ∀ b : ℝ, ‖S b‖ ≤ ∑ i, ‖z i * ((Y ^ (a i) : ℝ) : ℂ)‖ := by
    intro b
    calc ‖S b‖ ≤ ∑ i, ‖(if b ≤ a i then z i * ((Y ^ (a i) : ℝ) : ℂ) else 0)
          * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ := by
          rw [show S b = ∑ i, (if b ≤ a i then z i * ((Y ^ (a i) : ℝ) : ℂ) else 0)
              * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I) from rfl]
          exact norm_sum_le _ _
      _ ≤ ∑ i, ‖z i * ((Y ^ (a i) : ℝ) : ℂ)‖ := by
          apply Finset.sum_le_sum
          intro i _
          by_cases h : b ≤ a i
          · rw [if_pos h, norm_mul, hnorm1 i, mul_one]
          · rw [if_neg h]
            rw [zero_mul, norm_zero]
            positivity
  have hpow_meas : Measurable (fun b : ℝ => (((y / Y) ^ b : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      (Real.continuous_const_rpow (ne_of_gt htpos)).measurable
  have hmeas1 : Measurable (fun b : ℝ =>
      |Real.log (y / Y)| * ‖S b * ((((y / Y) ^ b : ℝ)) : ℂ)‖) :=
    measurable_const.mul ((hmeasS.mul hpow_meas).norm)
  have hmeas2 : Measurable (fun b : ℝ => L * ‖S b‖) := measurable_const.mul hmeasS.norm
  calc ‖∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ) * ((((y / Y) ^ (a i) - 1 : ℝ)) : ℂ)
        * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖
      = ‖∫ b in (0)..(1 / L), ((Real.log (y / Y) : ℝ) : ℂ)
          * (S b * ((((y / Y) ^ b : ℝ)) : ℂ))‖ := by rw [hfreeze]
    _ ≤ ∫ b in (0)..(1 / L), ‖((Real.log (y / Y) : ℝ) : ℂ)
          * (S b * ((((y / Y) ^ b : ℝ)) : ℂ))‖ :=
        intervalIntegral.norm_integral_le_integral_norm hBnn
    _ = ∫ b in (0)..(1 / L), |Real.log (y / Y)| * ‖S b * ((((y / Y) ^ b : ℝ)) : ℂ)‖ := by
        apply intervalIntegral.integral_congr
        intro b _
        beta_reduce
        rw [show ((Real.log (y / Y) : ℝ) : ℂ) * (S b * ((((y / Y) ^ b : ℝ)) : ℂ))
            = (Real.log (y / Y)) • (S b * ((((y / Y) ^ b : ℝ)) : ℂ)) from by
          rw [Complex.real_smul]]
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∫ b in (0)..(1 / L), L * ‖S b‖ := by
        refine intervalIntegral.integral_mono_on hBnn ?_ ?_ ?_
        · exact hb7_intervalIntegrable_of_bound hBnn hmeas1.aestronglyMeasurable
            (M := |Real.log (y / Y)| * (∑ i, ‖z i * ((Y ^ (a i) : ℝ) : ℂ)‖))
            (fun b hb => by
              rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
              exact mul_le_mul_of_nonneg_left ((hT_le b hb).trans (hSf_le b)) (abs_nonneg _))
        · exact hb7_intervalIntegrable_of_bound hBnn hmeas2.aestronglyMeasurable
            (M := L * (∑ i, ‖z i * ((Y ^ (a i) : ℝ) : ℂ)‖))
            (fun b hb => by
              rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hL.le (norm_nonneg _))]
              exact mul_le_mul_of_nonneg_left (hSf_le b) hL.le)
        · intro b hb
          calc |Real.log (y / Y)| * ‖S b * ((((y / Y) ^ b : ℝ)) : ℂ)‖
              ≤ |Real.log (y / Y)| * ‖S b‖ :=
                mul_le_mul_of_nonneg_left (hT_le b hb) (abs_nonneg _)
            _ ≤ L * ‖S b‖ := mul_le_mul_of_nonneg_right hlog_abs (norm_nonneg _)
    _ = L * ∫ b in (0)..(1 / L), ‖S b‖ := by rw [intervalIntegral.integral_const_mul]

/-- Error term of the freeze-block: with the amplitude `y^{a i}` in `y^{a i - i γ i}` replaced by
the frozen amplitude `Y^{a i}` and the error expanded as
`(y/Y)^{a i} - 1 = ∫_0^{a i} log(y/Y)·(y/Y)^b db`, on `y ∈ [Y e^{-L}, Y]` with `0 ≤ a i ≤ 1/L`
this error contributes `≤ K L Σ ‖z i‖² Y^{2 a i}`, the same shape as the main term.
Route: bound `‖·‖ ≤ L ∫_0^{1/L} ‖S_b(y)‖ db` (using `(y/Y)^b ≤ 1` and `|log(y/Y)| ≤ L`),
then Cauchy–Schwarz, then `MvtMul C` with `δ = 1/L` for the frozen-amplitude family
`S_b(y) = Σ_{i : b ≤ a i} z i · Y^{a i} · y^{-i γ i}`, and finally `∫_0^{1/L} 1_{b ≤ a i} db = a i`. -/
theorem HB7FreezeError {C : ℝ} (hC : 0 < C) (hMVT : Work.ZeroDensity.LogFree.MvtMul C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℝ), 1 ≤ L → ∀ {ι : Type*} [Fintype ι]
      (a γ : ι → ℝ) (z : ι → ℂ) (Y : ℝ), 0 < Y →
        (∀ i, 0 ≤ a i) → (∀ i, a i ≤ 1 / L) →
        (∀ i j, i ≠ j → 1 / L ≤ |γ i - γ j|) →
        (∫ y in (Y * Real.exp (-L))..Y,
            ‖∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ) * (((y / Y) ^ (a i) - 1 : ℝ) : ℂ)
                * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / y)
          ≤ K * L * ∑ i, ‖z i‖ ^ 2 * Y ^ (2 * a i) := by
  refine ⟨C + 1, by linarith, ?_⟩
  intro L hL ι _ a γ z Y hY ha0 haL hsep
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hBnn : 0 ≤ 1 / L := by positivity
  have hBpos : 0 < 1 / L := by positivity
  have hexple : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hY1pos : 0 < Y * Real.exp (-L) := mul_pos hY (Real.exp_pos _)
  have hY1le : Y * Real.exp (-L) ≤ Y := by nlinarith [Real.exp_pos (-L)]
  let S : ℝ → ℝ → ℂ := fun b y =>
    ∑ i, (if b ≤ a i then z i * ((Y ^ (a i) : ℝ) : ℂ) else 0)
      * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)
  let G : ℝ → ℂ := fun y =>
    ∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ) * ((((y / Y) ^ (a i) - 1 : ℝ)) : ℂ)
      * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)
  let F : ℝ → ℝ → ℝ := fun b y => ‖S b y‖ ^ 2 / y
  let Wf : ℝ → ℝ := fun y =>
    ∑ i, ‖z i * ((Y ^ (a i) : ℝ) : ℂ)‖ * ‖(y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖
  let Wc : ℝ := ∑ i, ‖z i * ((Y ^ (a i) : ℝ) : ℂ)‖
  let Sg : ℝ := ∑ i, ‖z i‖ ^ 2 * Y ^ (2 * a i)
  let Mrect : ℝ := Wc ^ 2 / (Y * Real.exp (-L))
  have hWc_nn : 0 ≤ Wc := by positivity
  have hSg_nn : 0 ≤ Sg := Finset.sum_nonneg (fun i _ => by positivity)
  have hMrect_nn : 0 ≤ Mrect := by positivity
  have hnorm1 : ∀ (y : ℝ), 0 < y → ∀ i, ‖(y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ = 1 := by
    intro y hy i
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
    have hre : ((-(γ i : ℂ)) * Complex.I).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.rpow_zero]
  have hS_le_Wf : ∀ b y, ‖S b y‖ ≤ Wf y := by
    intro b y
    calc ‖S b y‖
        ≤ ∑ i, ‖(if b ≤ a i then z i * ((Y ^ (a i) : ℝ) : ℂ) else 0)
            * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ := by
          rw [show S b y = ∑ i, (if b ≤ a i then z i * ((Y ^ (a i) : ℝ) : ℂ) else 0)
              * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I) from rfl]
          exact norm_sum_le _ _
      _ ≤ Wf y := by
          rw [show Wf y = ∑ i, ‖z i * ((Y ^ (a i) : ℝ) : ℂ)‖
              * ‖(y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ from rfl]
          apply Finset.sum_le_sum
          intro i _
          by_cases h : b ≤ a i
          · rw [if_pos h, norm_mul]
          · rw [if_neg h]
            rw [zero_mul, norm_zero]
            positivity
  have hS_le_Wc : ∀ b y, 0 < y → ‖S b y‖ ≤ Wc := by
    intro b y hy
    calc ‖S b y‖
        ≤ ∑ i, ‖(if b ≤ a i then z i * ((Y ^ (a i) : ℝ) : ℂ) else 0)
            * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ := by
          rw [show S b y = ∑ i, (if b ≤ a i then z i * ((Y ^ (a i) : ℝ) : ℂ) else 0)
              * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I) from rfl]
          exact norm_sum_le _ _
      _ ≤ Wc := by
          rw [show Wc = ∑ i, ‖z i * ((Y ^ (a i) : ℝ) : ℂ)‖ from rfl]
          apply Finset.sum_le_sum
          intro i _
          by_cases h : b ≤ a i
          · rw [if_pos h, norm_mul, hnorm1 y hy i, mul_one]
          · rw [if_neg h]
            rw [zero_mul, norm_zero]
            positivity
  have hpoint : ∀ y ∈ Set.Icc (Y * Real.exp (-L)) Y,
      ‖G y‖ ^ 2 / y ≤ L * ∫ b in (0)..(1 / L), F b y := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := Set.mem_Icc.mp hy
    have hypos : 0 < y := lt_of_lt_of_le hY1pos hy1
    have h1 : ‖G y‖ ≤ L * ∫ b in (0)..(1 / L), ‖S b y‖ :=
      hb7_freeze_norm_bound a γ z hY hLpos hy1 hy2 ha0 haL
    have h2 : (∫ b in (0)..(1 / L), ‖S b y‖) ^ 2
        ≤ (1 / L) * ∫ b in (0)..(1 / L), ‖S b y‖ ^ 2 := by
      have hmeasS : Measurable (fun b : ℝ => S b y) := by
        show Measurable (fun b : ℝ => ∑ i, (if b ≤ a i then z i * ((Y ^ (a i) : ℝ) : ℂ) else 0)
            * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I))
        apply Finset.measurable_sum
        intro i _
        exact (Measurable.ite measurableSet_Iic measurable_const measurable_const).mul
          measurable_const
      have h := IntervalNormSqCauchySchwarz (a := (0 : ℝ)) (b := 1 / L) hBnn
        (fun b => S b y) (Wf y) hmeasS (fun b => hS_le_Wf b y)
      simpa using h
    have h3 : ‖G y‖ ^ 2 ≤ L * ∫ b in (0)..(1 / L), ‖S b y‖ ^ 2 := by
      have hs : ‖G y‖ ^ 2 ≤ (L * ∫ b in (0)..(1 / L), ‖S b y‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      calc ‖G y‖ ^ 2 ≤ (L * ∫ b in (0)..(1 / L), ‖S b y‖) ^ 2 := hs
        _ = L ^ 2 * (∫ b in (0)..(1 / L), ‖S b y‖) ^ 2 := by rw [mul_pow]
        _ ≤ L ^ 2 * ((1 / L) * ∫ b in (0)..(1 / L), ‖S b y‖ ^ 2) := by
            exact mul_le_mul_of_nonneg_left h2 (sq_nonneg L)
        _ = L * ∫ b in (0)..(1 / L), ‖S b y‖ ^ 2 := by
            field_simp
    have hkey : (∫ b in (0)..(1 / L), F b y)
        = (∫ b in (0)..(1 / L), ‖S b y‖ ^ 2) * (1 / y) := by
      rw [← intervalIntegral.integral_mul_const (1 / y) (fun b => ‖S b y‖ ^ 2)]
      apply intervalIntegral.integral_congr
      intro b _
      change ‖S b y‖ ^ 2 / y = ‖S b y‖ ^ 2 * (1 / y)
      ring
    have h6 : L * (∫ b in (0)..(1 / L), F b y)
        = (L * ∫ b in (0)..(1 / L), ‖S b y‖ ^ 2) / y := by
      rw [hkey]; ring
    rw [h6]
    exact div_le_div_of_nonneg_right h3 hypos.le
  have hFmeas : Measurable (Function.uncurry F) := by
    have hterm : ∀ i : ι, Measurable (fun p : ℝ × ℝ =>
        (if p.1 ≤ a i then z i * ((Y ^ (a i) : ℝ) : ℂ) else 0)
          * (p.2 : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)) := by
      intro i
      refine Measurable.mul ?_ ?_
      · exact (Measurable.ite measurableSet_Iic measurable_const measurable_const).comp
          measurable_fst
      · exact (by fun_prop : Measurable
            (fun y : ℝ => (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I))).comp measurable_snd
    have hsum : Measurable (fun p : ℝ × ℝ =>
        ∑ i, (if p.1 ≤ a i then z i * ((Y ^ (a i) : ℝ) : ℂ) else 0)
          * (p.2 : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)) := by
      apply Finset.measurable_sum
      intro i _
      exact hterm i
    exact (hsum.norm.pow (measurable_const : Measurable (fun _ : ℝ × ℝ => (2 : ℕ)))).div
      measurable_snd
  have hFbound : ∀ b y, b ∈ Set.Icc 0 (1 / L) → y ∈ Set.Icc (Y * Real.exp (-L)) Y →
      ‖F b y‖ ≤ Mrect := by
    intro b y _ hy
    obtain ⟨hy1, hy2⟩ := Set.mem_Icc.mp hy
    have hypos : 0 < y := lt_of_lt_of_le hY1pos hy1
    have hnum : ‖S b y‖ ^ 2 ≤ Wc ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hS_le_Wc b y hypos) 2
    have h1 : ‖S b y‖ ^ 2 / y ≤ Wc ^ 2 / y := div_le_div_of_nonneg_right hnum hypos.le
    have h2 : Wc ^ 2 / y ≤ Wc ^ 2 / (Y * Real.exp (-L)) :=
      div_le_div_of_nonneg_left (sq_nonneg Wc) hY1pos hy1
    have h3 : ‖F b y‖ = ‖S b y‖ ^ 2 / y := by
      rw [show F b y = ‖S b y‖ ^ 2 / y from rfl, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (sq_nonneg _) hypos.le)]
    rw [h3, show Mrect = Wc ^ 2 / (Y * Real.exp (-L)) from rfl]
    exact h1.trans h2
  have hjoint : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioc 0 (1 / L))).prod
        (volume.restrict (Set.Ioc (Y * Real.exp (-L)) Y))) :=
    hb7_integrable_uncurry hFmeas hMrect_nn hFbound
  have hGint := Work.ZeroDensity.LogFree.HB7FreezeIntegrable (ι := ι) a γ z Y L hY
  have hI_G : IntervalIntegrable (fun y : ℝ => ‖G y‖ ^ 2 / y) volume (Y * Real.exp (-L)) Y :=
    hGint.2.2
  have hIntY : Integrable
      (fun y : ℝ => ∫ b : ℝ, F b y ∂(volume.restrict (Set.Ioc 0 (1 / L))))
      (volume.restrict (Set.Ioc (Y * Real.exp (-L)) Y)) := hjoint.integral_prod_right
  have hIntY2 : Integrable (fun y : ℝ => ∫ b in (0)..(1 / L), F b y)
      (volume.restrict (Set.Ioc (Y * Real.exp (-L)) Y)) :=
    hIntY.congr (Filter.Eventually.of_forall (fun y =>
      (intervalIntegral.integral_of_le hBnn).symm))
  have hI_rhs : IntervalIntegrable (fun y : ℝ => L * ∫ b in (0)..(1 / L), F b y)
      volume (Y * Real.exp (-L)) Y := by
    refine ⟨?_, ?_⟩
    · show Integrable (fun y : ℝ => L * ∫ b in (0)..(1 / L), F b y)
        (volume.restrict (Set.Ioc (Y * Real.exp (-L)) Y))
      exact hIntY2.const_mul L
    · rw [Set.Ioc_eq_empty_iff.mpr (not_lt.mpr hY1le)]
      exact MeasureTheory.integrableOn_empty
  have hI_bLHS : IntervalIntegrable
      (fun b : ℝ => ∫ y in (Y * Real.exp (-L))..Y, F b y) volume 0 (1 / L) := by
    refine hb7_intervalIntegrable_of_bound hBnn ?_ (M := Mrect * (Y - (Y * Real.exp (-L))))
      (fun b hb => ?_)
    · have hAE0 : AEStronglyMeasurable
          (fun b : ℝ => ∫ y : ℝ, F b y ∂(volume.restrict (Set.Ioc (Y * Real.exp (-L)) Y)))
          (volume.restrict (Set.Ioc 0 (1 / L))) := by
        have h := hjoint.aestronglyMeasurable.integral_prod_right'
        simpa only [Function.uncurry_apply_pair] using h
      refine hAE0.congr ?_
      filter_upwards with b
      exact (intervalIntegral.integral_of_le hY1le).symm
    · have hbnd : ∀ y ∈ Set.Icc (Y * Real.exp (-L)) Y, ‖F b y‖ ≤ Mrect :=
        fun y hy => hFbound b y hb hy
      calc ‖∫ y in (Y * Real.exp (-L))..Y, F b y‖
          ≤ ∫ y in (Y * Real.exp (-L))..Y, ‖F b y‖ :=
            intervalIntegral.norm_integral_le_integral_norm hY1le
        _ ≤ ∫ y in (Y * Real.exp (-L))..Y, Mrect := by
            refine intervalIntegral.integral_mono_on hY1le ?_ ?_ (fun y hy => hbnd y hy)
            · exact hb7_intervalIntegrable_of_bound hY1le (by fun_prop) (M := Mrect)
                (fun y hy => by
                  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
                  exact hbnd y hy)
            · exact hb7_intervalIntegrable_of_bound hY1le measurable_const.aestronglyMeasurable
                (M := Mrect) (fun y hy => by
                  simp [Real.norm_eq_abs, abs_of_nonneg hMrect_nn])
        _ = Mrect * (Y - (Y * Real.exp (-L))) := by
            rw [intervalIntegral.integral_const]; ring
  have hI_const : IntervalIntegrable (fun _ : ℝ => (C + 1) * L * Sg) volume 0 (1 / L) := by
    refine hb7_intervalIntegrable_of_bound hBnn measurable_const.aestronglyMeasurable
      (M := (C + 1) * L * Sg) (fun x hx => ?_)
    have hnn : 0 ≤ (C + 1) * L * Sg := by
      apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) hSg_nn
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have hstep7 : (∫ b in (0)..(1 / L), ∫ y in (Y * Real.exp (-L))..Y, F b y)
      ≤ ∫ b in (0)..(1 / L), (C + 1) * L * Sg := by
    refine intervalIntegral.integral_mono_on hBnn hI_bLHS hI_const (fun b hb => ?_)
    exact hb7_freeze_mvt_bound hC hMVT a γ z hY hL haL hsep b
  have hstep8 : (∫ b in (0)..(1 / L), (C + 1) * L * Sg) = (1 / L) * ((C + 1) * L * Sg) := by
    rw [intervalIntegral.integral_const]; ring
  have hfinal : (∫ y in (Y * Real.exp (-L))..Y, ‖G y‖ ^ 2 / y) ≤ (C + 1) * L * Sg := by
    calc (∫ y in (Y * Real.exp (-L))..Y, ‖G y‖ ^ 2 / y)
        ≤ ∫ y in (Y * Real.exp (-L))..Y, L * (∫ b in (0)..(1 / L), F b y) :=
          intervalIntegral.integral_mono_on hY1le hI_G hI_rhs hpoint
      _ = L * (∫ y in (Y * Real.exp (-L))..Y, ∫ b in (0)..(1 / L), F b y) :=
          intervalIntegral.integral_const_mul L _
      _ = L * (∫ b in (0)..(1 / L), ∫ y in (Y * Real.exp (-L))..Y, F b y) := by
          rw [hb7_swap hY1le hBnn hFmeas hMrect_nn hFbound]
      _ ≤ L * (∫ b in (0)..(1 / L), (C + 1) * L * Sg) :=
          mul_le_mul_of_nonneg_left hstep7 hLpos.le
      _ = L * ((1 / L) * ((C + 1) * L * Sg)) := by rw [hstep8]
      _ = (C + 1) * L * Sg := by field_simp
  exact hfinal

namespace Work.ZeroDensity.LogFree

/-- Restatement of the freeze-error estimate under the doubly-qualified name that
`HB7FreezeBlock` refers to; identical in content to `Work.ZeroDensity.LogFree.HB7FreezeError`. -/
theorem HB7FreezeError {C : ℝ} (hC : 0 < C) (hMVT : Work.ZeroDensity.LogFree.MvtMul C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℝ), 1 ≤ L → ∀ {ι : Type*} [Fintype ι]
      (a γ : ι → ℝ) (z : ι → ℂ) (Y : ℝ), 0 < Y →
        (∀ i, 0 ≤ a i) → (∀ i, a i ≤ 1 / L) →
        (∀ i j, i ≠ j → 1 / L ≤ |γ i - γ j|) →
        (∫ y in (Y * Real.exp (-L))..Y,
            ‖∑ i, z i * ((Y ^ (a i) : ℝ) : ℂ) * (((y / Y) ^ (a i) - 1 : ℝ) : ℂ)
                * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / y)
          ≤ K * L * ∑ i, ‖z i‖ ^ 2 * Y ^ (2 * a i) :=
  _root_.Work.ZeroDensity.LogFree.HB7FreezeError hC hMVT

end Work.ZeroDensity.LogFree

end Work.ZeroDensity.LogFree
