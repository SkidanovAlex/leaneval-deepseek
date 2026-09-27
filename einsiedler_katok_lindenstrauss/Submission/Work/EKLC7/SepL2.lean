import Mathlib
import Submission.Work.EKLC7.SepL2BorelIntegral
import Submission.Work.EKLC7.SepL2MeasureZeroPos

/-!
# `Work.EKLC7.SepL2`

A separation (annihilation) lemma used in the EKL proof (component C7):

if `β` is a Borel measure on `ℝ × ℝ` which is finite on compact sets and `Ψ` is a bounded
measurable function whose product with every compactly supported continuous function integrates
to `0` against `β`, then `Ψ = 0` `β`-almost everywhere.

Equivalently: a signed measure `Ψ · β` which is finite on compacts and annihilates all of
`C_c(ℝ × ℝ)` is the zero measure.

The proof has four steps.

1. **Compacts.** For every compact `K`, `∫ z in K, Ψ z ∂β = 0`.  Given `δ > 0`, regularity of `β`
   gives an open neighbourhood `V ⊇ K` with `β (V \ K) < ε`, and Urysohn gives
   `f ∈ C_c(ℝ×ℝ,ℝ)` with `1_K ≤ f ≤ 1_V`, `0 ≤ f ≤ 1`.  Then
   `∫_{K} Ψ = ∫ (1_K - f) Ψ + ∫ f Ψ = ∫ (1_K - f) Ψ`, and `|∫ (1_K - f) Ψ| ≤ C · β (V \ K)`.
   As `V` shrinks to `K` this gives `∫_K Ψ = 0`.
2. **Finite-measure Borel sets.** Approximate a Borel set of finite `β`-measure from inside by
   compact sets (`SepL2BorelIntegral`).
3. **Positivity.** If `∫_A Ψ = 0` with `Ψ > 0` on `A` and `β A < ∞`, then `β A = 0`
   (`SepL2MeasureZeroPos`).
4. **Assembly.** `{Ψ ≠ 0} = {Ψ > 0} ∪ {Ψ < 0}`; each piece meets every closed ball in a
   step-3 set, so each piece is null.
-/

open MeasureTheory
open Set

namespace Work.EKLC7

open scoped CompactlySupported

/-- **Step 1.** If `β` is finite on compacts, `Ψ` is measurable with `|Ψ| ≤ C`, and
`∫ z, F z * Ψ z ∂β = 0` for every `F ∈ C_c(ℝ × ℝ, ℝ)`, then the integral of `Ψ` over every
compact set vanishes. -/
theorem SepL2_compact_integral
    (β : Measure (ℝ × ℝ)) [IsFiniteMeasureOnCompacts β]
    (Ψ : ℝ × ℝ → ℝ) (hΨ : Measurable Ψ) (C : ℝ) (hC : ∀ z, |Ψ z| ≤ C)
    (horth : ∀ F : C_c(ℝ × ℝ, ℝ), ∫ z, F z * Ψ z ∂β = 0)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) :
    ∫ z in K, Ψ z ∂β = 0 := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (Ψ 0)) (hC 0)
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  have key : ∀ δ : ℝ, 0 < δ → |∫ z in K, Ψ z ∂β| ≤ δ := by
    intro δ hδ
    set ε : ℝ := δ / (C + 1) with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; positivity
    obtain ⟨V, hKV, hVo, hVlt⟩ :=
      hK.exists_isOpen_lt_add (μ := β) (ε := ENNReal.ofReal ε)
        (by rw [ENNReal.ofReal_ne_zero_iff]; exact hεpos)
    have hVtop : β V < ⊤ :=
      hVlt.trans (ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, ENNReal.ofReal_lt_top⟩)
    obtain ⟨f, hf1, hf2, hf3, hf4⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK hVo hKV
    have horthf : ∫ z, f z * Ψ z ∂β = 0 := by
      have hmem : ∫ z, (⟨f, hasCompactSupport_def.mpr hf2⟩ : C_c(ℝ × ℝ, ℝ)) z * Ψ z ∂β = 0 :=
        horth ⟨f, hasCompactSupport_def.mpr hf2⟩
      simpa using hmem
    have hInd_meas : Measurable (K.indicator (1 : ℝ × ℝ → ℝ)) :=
      measurable_const.indicator hK.measurableSet
    have hInd1 : Integrable (V.indicator (1 : ℝ × ℝ → ℝ)) β := by
      rw [integrable_indicator_iff hVo.measurableSet]
      exact integrableOn_const (μ := β) (s := V) (by simpa using hVtop.ne) (by simp)
    have hIntV : Integrable (fun z => C * (V.indicator (1 : ℝ × ℝ → ℝ)) z) β :=
      hInd1.const_mul C
    have hFbound : ∀ z : ℝ × ℝ, |f z| ≤ (V.indicator (1 : ℝ × ℝ → ℝ)) z := by
      intro z
      by_cases hz : z ∈ tsupport (⇑f)
      · rw [Set.indicator_of_mem (hf3 hz), abs_of_nonneg (hf4 z).1]
        exact (hf4 z).2
      · rw [image_eq_zero_of_notMem_tsupport hz, abs_zero]
        exact indicator_nonneg (fun _ _ => zero_le_one) z
    have hIntF : Integrable (fun z => f z * Ψ z) β := by
      refine hIntV.mono' ?_ ?_
      · exact (f.continuous.measurable.mul hΨ).aestronglyMeasurable
      · filter_upwards with z
        rw [Real.norm_eq_abs, abs_mul]
        calc |f z| * |Ψ z| ≤ (V.indicator (1 : ℝ × ℝ → ℝ)) z * C :=
              mul_le_mul (hFbound z) (hC z) (abs_nonneg _)
                (indicator_nonneg (fun _ _ => zero_le_one) z)
          _ = C * (V.indicator (1 : ℝ × ℝ → ℝ)) z := by ring
    have hIntg : Integrable (fun z => ((K.indicator (1 : ℝ × ℝ → ℝ)) z - f z) * Ψ z) β := by
      refine hIntV.mono' ?_ ?_
      · exact ((hInd_meas.sub f.continuous.measurable).mul hΨ).aestronglyMeasurable
      · filter_upwards with z
        rw [Real.norm_eq_abs, abs_mul]
        have hd : |(K.indicator (1 : ℝ × ℝ → ℝ)) z - f z| ≤
            (V.indicator (1 : ℝ × ℝ → ℝ)) z := by
          by_cases hz : z ∈ K
          · have hz0 : |(K.indicator (1 : ℝ × ℝ → ℝ)) z - f z| = 0 := by
              simp [Set.indicator_of_mem hz, hf1 hz]
            rw [hz0]
            exact indicator_nonneg (fun _ _ => zero_le_one) z
          · by_cases hzV : z ∈ V
            · have hL : |(K.indicator (1 : ℝ × ℝ → ℝ)) z - f z| = f z := by
                simp [Set.indicator_of_notMem hz, abs_of_nonneg (hf4 z).1]
              have hR : (V.indicator (1 : ℝ × ℝ → ℝ)) z = 1 := by
                simp [Set.indicator_of_mem hzV]
              rw [hL, hR]
              exact (hf4 z).2
            · have hfz : f z = 0 := image_eq_zero_of_notMem_tsupport (fun hc => hzV (hf3 hc))
              have hL : |(K.indicator (1 : ℝ × ℝ → ℝ)) z - f z| = 0 := by
                simp [Set.indicator_of_notMem hz, hfz]
              have hR : (V.indicator (1 : ℝ × ℝ → ℝ)) z = 0 := by
                simp [Set.indicator_of_notMem hzV]
              rw [hL, hR]
        calc |(K.indicator (1 : ℝ × ℝ → ℝ)) z - f z| * |Ψ z|
            ≤ (V.indicator (1 : ℝ × ℝ → ℝ)) z * C :=
              mul_le_mul hd (hC z) (abs_nonneg _) (indicator_nonneg (fun _ _ => zero_le_one) z)
          _ = C * (V.indicator (1 : ℝ × ℝ → ℝ)) z := by ring
    have h1 : ∫ z in K, Ψ z ∂β = ∫ z, (K.indicator (1 : ℝ × ℝ → ℝ)) z * Ψ z ∂β := by
      rw [← integral_indicator hK.measurableSet (f := fun z => Ψ z)]
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ K
      · simp [Set.indicator_of_mem hz]
      · simp [Set.indicator_of_notMem hz]
    have h2 : ∫ z, (K.indicator (1 : ℝ × ℝ → ℝ)) z * Ψ z ∂β
        = ∫ z, ((K.indicator (1 : ℝ × ℝ → ℝ)) z - f z) * Ψ z ∂β
          + ∫ z, f z * Ψ z ∂β := by
      rw [← integral_add hIntg hIntF]
      apply integral_congr_ae
      filter_upwards with z
      ring
    have hmeasVK : MeasurableSet (V \ K) := hVo.measurableSet.diff hK.measurableSet
    have hbound : |∫ z in K, Ψ z ∂β| ≤ C * (β (V \ K)).toReal := by
      rw [h1, h2, horthf, add_zero]
      have hIndVK : Integrable (fun z => C * ((V \ K).indicator (1 : ℝ × ℝ → ℝ)) z) β := by
        have h1' : Integrable ((V \ K).indicator (1 : ℝ × ℝ → ℝ)) β := by
          rw [integrable_indicator_iff hmeasVK]
          exact integrableOn_const (μ := β) (s := V \ K)
            (ne_top_of_le_ne_top hVtop.ne (measure_mono sdiff_subset)) (by simp)
        exact h1'.const_mul C
      have hstep : ‖∫ z, ((K.indicator (1 : ℝ × ℝ → ℝ)) z - f z) * Ψ z ∂β‖
          ≤ ∫ z, C * ((V \ K).indicator (1 : ℝ × ℝ → ℝ)) z ∂β := by
        refine norm_integral_le_of_norm_le hIndVK ?_
        filter_upwards with z
        rw [Real.norm_eq_abs, abs_mul]
        have hd : |(K.indicator (1 : ℝ × ℝ → ℝ)) z - f z| ≤
            ((V \ K).indicator (1 : ℝ × ℝ → ℝ)) z := by
          by_cases hz : z ∈ K
          · have hz0 : |(K.indicator (1 : ℝ × ℝ → ℝ)) z - f z| = 0 := by
              simp [Set.indicator_of_mem hz, hf1 hz]
            rw [hz0]
            exact indicator_nonneg (fun _ _ => zero_le_one) z
          · by_cases hzV : z ∈ V
            · have hmem : z ∈ V \ K := ⟨hzV, hz⟩
              have hL : |(K.indicator (1 : ℝ × ℝ → ℝ)) z - f z| = f z := by
                simp [Set.indicator_of_notMem hz, abs_of_nonneg (hf4 z).1]
              have hR : ((V \ K).indicator (1 : ℝ × ℝ → ℝ)) z = 1 := by
                simp [Set.indicator_of_mem hmem]
              rw [hL, hR]
              exact (hf4 z).2
            · have hfz : f z = 0 := image_eq_zero_of_notMem_tsupport (fun hc => hzV (hf3 hc))
              have hL : |(K.indicator (1 : ℝ × ℝ → ℝ)) z - f z| = 0 := by
                simp [Set.indicator_of_notMem hz, hfz]
              have hR : ((V \ K).indicator (1 : ℝ × ℝ → ℝ)) z = 0 := by
                simp [Set.indicator_of_notMem (show z ∉ V \ K from fun h => hzV h.1)]
              rw [hL, hR]
        calc |(K.indicator (1 : ℝ × ℝ → ℝ)) z - f z| * |Ψ z|
            ≤ ((V \ K).indicator (1 : ℝ × ℝ → ℝ)) z * C :=
              mul_le_mul hd (hC z) (abs_nonneg _) (indicator_nonneg (fun _ _ => zero_le_one) z)
          _ = C * ((V \ K).indicator (1 : ℝ × ℝ → ℝ)) z := by ring
      calc |∫ z, ((K.indicator (1 : ℝ × ℝ → ℝ)) z - f z) * Ψ z ∂β|
          = ‖∫ z, ((K.indicator (1 : ℝ × ℝ → ℝ)) z - f z) * Ψ z ∂β‖ := by
            rw [Real.norm_eq_abs]
        _ ≤ ∫ z, C * ((V \ K).indicator (1 : ℝ × ℝ → ℝ)) z ∂β := hstep
        _ = C * (β (V \ K)).toReal := by
              rw [integral_const_mul, integral_indicator_one hmeasVK, Measure.real_def]
    have hVKlt : β (V \ K) < ENNReal.ofReal ε := by
      have h1' : β (V \ K) = β V - β K :=
        measure_sdiff hKV hK.measurableSet.nullMeasurableSet hK.measure_lt_top.ne
      rw [h1']
      exact ENNReal.sub_lt_of_lt_add (measure_mono hKV) (by simpa [add_comm] using hVlt)
    have hVKne : β (V \ K) ≠ ⊤ := ne_top_of_lt hVKlt
    have htoReal : (β (V \ K)).toReal ≤ ε :=
      (ENNReal.le_ofReal_iff_toReal_le hVKne hεpos.le).mp hVKlt.le
    calc |∫ z in K, Ψ z ∂β| ≤ C * (β (V \ K)).toReal := hbound
      _ ≤ C * ε := mul_le_mul_of_nonneg_left htoReal hC0
      _ = δ * (C / (C + 1)) := by rw [hεdef]; ring_nf
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left ((div_le_one hC1).mpr (by linarith)) hδ.le
      _ = δ := by ring
  have hle : |∫ z in K, Ψ z ∂β| ≤ 0 :=
    le_of_forall_pos_le_add (fun δ hδ => by simpa using key δ hδ)
  exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))

theorem SepL2 :
    ∀ (β : MeasureTheory.Measure (ℝ × ℝ)) [MeasureTheory.IsFiniteMeasureOnCompacts β]
      (Ψ : ℝ × ℝ → ℝ),
      Measurable Ψ → (∃ C : ℝ, ∀ z, |Ψ z| ≤ C) →
      (∀ F : CompactlySupportedContinuousMap (ℝ × ℝ) ℝ,
        ∫ z, F z * Ψ z ∂β = 0) →
      ∀ᵐ z ∂β, Ψ z = 0 := by
  intro β inst Ψ hΨ hbdd horth
  obtain ⟨C, hC⟩ := hbdd
  have hcomp : ∀ K : Set (ℝ × ℝ), IsCompact K → ∫ z in K, Ψ z ∂β = 0 :=
    fun K hK => SepL2_compact_integral β Ψ hΨ C hC horth K hK
  have hborel : ∀ A : Set (ℝ × ℝ), MeasurableSet A → β A ≠ ⊤ → ∫ z in A, Ψ z ∂β = 0 :=
    fun A hA hfin => SepL2BorelIntegral hΨ hC hcomp hA hfin
  have hcomp_neg : ∀ K : Set (ℝ × ℝ), IsCompact K → ∫ z in K, -Ψ z ∂β = 0 := by
    intro K hK
    rw [integral_neg, hcomp K hK, neg_zero]
  have hCneg : ∀ z, |(-Ψ) z| ≤ C := fun z => by simpa [Pi.neg_apply] using hC z
  have hnegposnull : ∀ A : Set (ℝ × ℝ), MeasurableSet A → β A ≠ ⊤ →
      (∀ z ∈ A, 0 < -Ψ z) → β A = 0 := by
    intro A hA hfin hpos
    refine SepL2MeasureZeroPos (Ψ := fun z => -Ψ z) (C := C) hΨ.neg hCneg hA hfin hpos ?_
    exact SepL2BorelIntegral (Ψ := fun z => -Ψ z) hΨ.neg hCneg hcomp_neg hA hfin
  have hposnull : ∀ A : Set (ℝ × ℝ), MeasurableSet A → β A ≠ ⊤ →
      (∀ z ∈ A, 0 < Ψ z) → β A = 0 := by
    intro A hA hfin hpos
    exact SepL2MeasureZeroPos hΨ hC hA hfin hpos (hborel A hA hfin)
  have hball_meas : ∀ n : ℕ, MeasurableSet (Metric.closedBall (0 : ℝ × ℝ) n) :=
    fun n => (isCompact_closedBall (0 : ℝ × ℝ) (n : ℝ)).isClosed.measurableSet
  have hball_fin : ∀ n : ℕ, β (Metric.closedBall (0 : ℝ × ℝ) n) < ⊤ :=
    fun n => (isCompact_closedBall (0 : ℝ × ℝ) (n : ℝ)).measure_lt_top
  have hcover : ∀ (s : Set (ℝ × ℝ)), s = ⋃ n : ℕ, (s ∩ Metric.closedBall (0 : ℝ × ℝ) n) := by
    intro s
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_ge (dist z 0)
      exact ⟨n, hz, by simpa [Metric.mem_closedBall] using hn⟩
    · rintro ⟨n, hz, -⟩; exact hz
  have hS1 : β {z : ℝ × ℝ | 0 < Ψ z} = 0 := by
    rw [hcover {z : ℝ × ℝ | 0 < Ψ z}]
    refine measure_iUnion_null (fun n => ?_)
    refine hposnull _ ?_ ?_ ?_
    · exact (hΨ measurableSet_Ioi).inter (hball_meas n)
    · exact ne_top_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right) (hball_fin n))
    · intro z hz; exact hz.1
  have hS2 : β {z : ℝ × ℝ | Ψ z < 0} = 0 := by
    have hsame : {z : ℝ × ℝ | Ψ z < 0} = {z : ℝ × ℝ | 0 < -Ψ z} := by
      ext z; simp
    rw [hsame, hcover {z : ℝ × ℝ | 0 < -Ψ z}]
    refine measure_iUnion_null (fun n => ?_)
    refine hnegposnull _ ?_ ?_ ?_
    · exact (hΨ.neg measurableSet_Ioi).inter (hball_meas n)
    · exact ne_top_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right) (hball_fin n))
    · intro z hz; exact hz.1
  rw [MeasureTheory.ae_iff]
  have heq : {z : ℝ × ℝ | ¬ (Ψ z = 0)} = {z | 0 < Ψ z} ∪ {z | Ψ z < 0} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    exact ⟨fun h => (lt_or_gt_of_ne h).elim Or.inr Or.inl, fun h => h.elim ne_of_gt ne_of_lt⟩
  rw [heq]
  exact le_antisymm ((measure_union_le _ _).trans (by rw [hS1, hS2, add_zero])) (by simp)

end Work.EKLC7
