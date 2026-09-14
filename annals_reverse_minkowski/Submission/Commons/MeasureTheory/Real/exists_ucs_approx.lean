import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Commons.MeasureTheory.Real.staircase_pointwise_bounds

namespace Commons.MeasureTheory.Real

open _root_.MeasureTheory Filter
open Classical
open scoped ENNReal Topology

/-- Sums of constant multiples of indicators equal the constant times the count of the
indices whose set contains `x`. -/
private lemma sum_indicator_const_eq_card {ι α : Type*} (s : Finset ι) (A : ι → Set α)
    (c : ℝ) (x : α) :
    (∑ i ∈ s, (A i).indicator (fun _ => c) x)
      = c * ((s.filter (fun i => x ∈ A i)).card : ℝ) := by
  have hsum : (∑ i ∈ s, (A i).indicator (fun _ => c) x)
      = ∑ i ∈ s, (if x ∈ A i then c else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : x ∈ A i
    · rw [Set.indicator_of_mem h]; simp [h]
    · rw [Set.indicator_of_notMem h]; simp [h]
  have h2 : (∑ i ∈ s, (if x ∈ A i then c else 0))
      = c * ∑ i ∈ s, (if x ∈ A i then (1:ℝ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : x ∈ A i <;> simp [h]
  rw [hsum, h2]
  congr 1
  rw [Finset.card_filter]
  push_cast
  simp

/-- For measurable nonnegative `F ≤ G` with finite `∫⁻ ofReal G`, the difference of the
Bochner integrals equals the `toReal` of the lintegral of the pointwise difference. -/
private lemma integral_sub_eq_toReal_lintegral_ofReal {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) {F G : α → ℝ} (hF : Measurable F) (hG : Measurable G)
    (h0F : ∀ x, 0 ≤ F x) (hFG : ∀ x, F x ≤ G x)
    (hfin : ∫⁻ x, ENNReal.ofReal (G x) ∂μ ≠ ⊤) :
    (∫ x, G x ∂μ) - (∫ x, F x ∂μ)
      = (∫⁻ x, ENNReal.ofReal (G x - F x) ∂μ).toReal := by
  have hFint : (∫ x, F x ∂μ) = (∫⁻ x, ENNReal.ofReal (F x) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all μ h0F) hF.aestronglyMeasurable
  have hGint : (∫ x, G x ∂μ) = (∫⁻ x, ENNReal.ofReal (G x) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all μ (fun x => le_trans (h0F x) (hFG x)))
      hG.aestronglyMeasurable
  have hpt : ∀ x, ENNReal.ofReal (G x)
      = ENNReal.ofReal (F x) + ENNReal.ofReal (G x - F x) := by
    intro x
    rw [← ENNReal.ofReal_add (h0F x) (sub_nonneg.mpr (hFG x))]
    congr 1
    ring
  have hl : ∫⁻ x, ENNReal.ofReal (G x) ∂μ
      = ∫⁻ x, ENNReal.ofReal (F x) ∂μ + ∫⁻ x, ENNReal.ofReal (G x - F x) ∂μ := by
    simp_rw [hpt]
    rw [lintegral_add_left (f := fun x => ENNReal.ofReal (F x))
      (ENNReal.measurable_ofReal.comp hF)]
  have hfinF : ∫⁻ x, ENNReal.ofReal (F x) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hFG x)))
  have hfindiff : ∫⁻ x, ENNReal.ofReal (G x - F x) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top hfin
      (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (sub_le_self _ (h0F x))))
  rw [hGint, hFint, hl, ENNReal.toReal_add hfinF hfindiff]
  ring

/-- Squeezing `ℝ≥0∞`-valued lintegrals against `ENNReal.ofReal` of a null sequence. -/
private lemma tendsto_toReal_of_le_ofReal {x : ℕ → ENNReal} {r : ℕ → ℝ} (hr0 : ∀ n, 0 ≤ r n)
    (h : ∀ n, x n ≤ ENNReal.ofReal (r n))
    (hr : Tendsto r atTop (nhds 0)) :
    Tendsto (fun n => (x n).toReal) atTop (nhds 0) := by
  refine squeeze_zero' (Eventually.of_forall fun n => ENNReal.toReal_nonneg) ?_ hr
  filter_upwards with n
  calc (x n).toReal ≤ (ENNReal.ofReal (r n)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (h n)
    _ = r n := ENNReal.toReal_ofReal (hr0 n)

theorem exists_ucs_approx (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure μ]
    (f : ℝ → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    ∃ F : ℕ → ℝ → ℝ,
      (∀ n, UpperSemicontinuous (F n)) ∧
      (∀ n x, 0 ≤ F n x) ∧
      (∀ n x, F n x ≤ f x) ∧
      (∀ n, IsCompact {x : ℝ | 0 < F n x}) ∧
      (∀ n x, F n x ≤ 1 - 1/((n:ℝ)+1)) ∧
      Filter.Tendsto (fun n => ∫ x, F n x ∂μ) Filter.atTop (nhds (∫ x, f x ∂μ)) := by
  have hcap_nonneg : ∀ n : ℕ, 0 ≤ 1 - 1/((n:ℝ)+1) := by
    intro n
    have h1 : (1:ℝ) ≤ (n:ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have h2 : 1/((n:ℝ)+1) ≤ 1 := by
      rw [div_le_one (show (0:ℝ) < (n:ℝ)+1 by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    linarith
  let G : ℕ → ℝ → ℝ := fun n x => min (f x) (1 - 1/((n:ℝ)+1))
  have hGmeas : ∀ n, Measurable (G n) := fun n => hf.min measurable_const
  have hG0 : ∀ n x, 0 ≤ G n x := fun n x => le_min (hf0 x) (hcap_nonneg n)
  have hG1 : ∀ n x, G n x ≤ 1 := fun n x => le_trans (min_le_left _ _) (hf1 x)
  have hGle_f : ∀ n x, G n x ≤ f x := fun n x => min_le_left _ _
  let A : ℕ → ℕ → Set ℝ := fun n i => {x : ℝ | (i:ℝ)/((n:ℝ)+1) ≤ G n x}
  have hAmeas : ∀ n i, MeasurableSet (A n i) := fun n i =>
    measurableSet_le measurable_const (hGmeas n)
  have hδne : ∀ n : ℕ, ENNReal.ofReal (1/(((n:ℝ)+1))^2) ≠ 0 := by
    intro n
    have hpos : (0:ℝ) < 1/(((n:ℝ)+1))^2 := by
      apply div_pos one_pos
      exact pow_pos (by positivity) 2
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hpos)
  have hex : ∀ n i, ∃ K : Set ℝ, K ⊆ A n i ∧ IsCompact K ∧
      μ (A n i \ K) < ENNReal.ofReal (1/(((n:ℝ)+1))^2) := by
    intro n i
    exact (hAmeas n i).exists_isCompact_sdiff_lt (measure_ne_top μ (A n i)) (hδne n)
  choose K hKsub hKcpt hKsdiff using hex
  let F : ℕ → ℝ → ℝ := fun n x =>
    ∑ i ∈ Finset.Icc 1 n, (K n i).indicator (fun _ : ℝ => (1/((n:ℝ)+1))) x
  let T : ℕ → ℝ → ℝ := fun n x =>
    ∑ i ∈ Finset.Icc 1 n, (A n i).indicator (fun _ : ℝ => (1/((n:ℝ)+1))) x
  have hT_eq : ∀ n x, T n x = (1/((n:ℝ)+1)) *
      (((Finset.Icc 1 n).filter (fun i : ℕ => (i:ℝ)/((n:ℝ)+1) ≤ G n x)).card : ℝ) := by
    intro n x
    have h := sum_indicator_const_eq_card (Finset.Icc 1 n)
      (fun i => {y : ℝ | (i:ℝ)/((n:ℝ)+1) ≤ G n y}) (1/((n:ℝ)+1)) x
    simpa [T, A] using h
  have hF_eq : ∀ n x, F n x = (1/((n:ℝ)+1)) *
      (((Finset.Icc 1 n).filter (fun i => x ∈ K n i)).card : ℝ) := by
    intro n x
    have h := sum_indicator_const_eq_card (Finset.Icc 1 n) (fun i => K n i)
      (1/((n:ℝ)+1)) x
    simpa [F] using h
  have hTle : ∀ n x, T n x ≤ G n x := by
    intro n x
    rw [hT_eq n x]
    have h := (staircase_pointwise_bounds (G n) (hG0 n) (hG1 n) (n+1) (Nat.succ_pos n) x).1
    have hI : Finset.Icc 1 ((n+1) - 1) = Finset.Icc 1 n := rfl
    have hc : ((n+1 : ℕ) : ℝ) = (n:ℝ) + 1 := by push_cast; ring
    rw [hI, hc] at h
    exact h
  have hTge : ∀ n x, G n x ≤ T n x + 1/((n:ℝ)+1) := by
    intro n x
    rw [hT_eq n x]
    have h := (staircase_pointwise_bounds (G n) (hG0 n) (hG1 n) (n+1) (Nat.succ_pos n) x).2
    have hI : Finset.Icc 1 ((n+1) - 1) = Finset.Icc 1 n := rfl
    have hc : ((n+1 : ℕ) : ℝ) = (n:ℝ) + 1 := by push_cast; ring
    rw [hI, hc] at h
    exact h
  have hFTle : ∀ n x, F n x ≤ T n x := by
    intro n x
    rw [hF_eq n x, hT_eq n x]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hsub : (Finset.Icc 1 n).filter (fun i => x ∈ K n i) ⊆
        (Finset.Icc 1 n).filter (fun i : ℕ => (i:ℝ)/((n:ℝ)+1) ≤ G n x) := by
      intro i hi
      simp only [Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, hKsub n i hi.2⟩
    exact_mod_cast Finset.card_le_card hsub
  have hFGle : ∀ n x, F n x ≤ G n x := fun n x => le_trans (hFTle n x) (hTle n x)
  have hFle_f : ∀ n x, F n x ≤ f x := fun n x => le_trans (hFGle n x) (hGle_f n x)
  have hFcap : ∀ n x, F n x ≤ 1 - 1/((n:ℝ)+1) := fun n x =>
    le_trans (hFGle n x) (min_le_right _ _)
  have hF0 : ∀ n x, 0 ≤ F n x := by
    intro n x
    rw [hF_eq n x]
    exact mul_nonneg (by positivity) (by positivity)
  have hTmeas : ∀ n, Measurable (T n) := by
    intro n
    have h : ∀ i ∈ Finset.Icc 1 n,
        Measurable (fun x : ℝ => (A n i).indicator (fun _ : ℝ => (1/((n:ℝ)+1))) x) :=
      fun i _ => measurable_const.indicator (hAmeas n i)
    simpa [T] using Finset.measurable_sum (Finset.Icc 1 n) h
  have hFmeas : ∀ n, Measurable (F n) := by
    intro n
    have h : ∀ i ∈ Finset.Icc 1 n,
        Measurable (fun x : ℝ => (K n i).indicator (fun _ : ℝ => (1/((n:ℝ)+1))) x) :=
      fun i _ => measurable_const.indicator (hKcpt n i).isClosed.measurableSet
    simpa [F] using Finset.measurable_sum (Finset.Icc 1 n) h
  have hFusc : ∀ n, UpperSemicontinuous (F n) := by
    intro n
    have h : ∀ i ∈ Finset.Icc 1 n,
        UpperSemicontinuous (fun x : ℝ => (K n i).indicator (fun _ : ℝ => (1/((n:ℝ)+1))) x) :=
      fun i _ => (hKcpt n i).isClosed.upperSemicontinuous_indicator (by positivity)
    simpa [F] using upperSemicontinuous_sum h
  let Bad : ℕ → Set ℝ := fun n => ⋃ i ∈ Finset.Icc 1 n, (A n i \ K n i)
  have hBadmeas : ∀ n, MeasurableSet (Bad n) := by
    intro n
    have h := Finset.measurableSet_biUnion (Finset.Icc 1 n)
      (f := fun i => A n i \ K n i)
      (fun i _ => (hAmeas n i).diff (hKcpt n i).isClosed.measurableSet)
    simpa [Bad] using h
  have hTFout : ∀ n x, x ∉ Bad n → T n x = F n x := by
    intro n x hx
    simp only [T, F]
    apply Finset.sum_congr rfl
    intro i hi
    have hnot : x ∉ A n i \ K n i := fun h => hx (by
      simp only [Bad, Set.mem_iUnion]
      exact ⟨i, hi, h⟩)
    rw [Set.mem_sdiff] at hnot
    by_cases hxK : x ∈ K n i
    · have hxA : x ∈ A n i := hKsub n i hxK
      rw [Set.indicator_of_mem hxK, Set.indicator_of_mem hxA]
    · have hxA : x ∉ A n i := fun h => hnot ⟨h, hxK⟩
      rw [Set.indicator_of_notMem hxK, Set.indicator_of_notMem hxA]
  have hFsupp : ∀ n, IsCompact {x : ℝ | 0 < F n x} := by
    intro n
    have hset : {x : ℝ | 0 < F n x} = ⋃ i ∈ Finset.Icc 1 n, K n i := by
      ext x
      rw [Set.mem_ofPred_eq, hF_eq n x]
      simp only [Set.mem_iUnion]
      have hc : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
      constructor
      · intro h
        have hk : 0 < ((Finset.Icc 1 n).filter (fun i => x ∈ K n i)).card := by
          have h2 := (mul_pos_iff_of_pos_left hc).mp h
          exact_mod_cast h2
        obtain ⟨i, hi⟩ := Finset.card_pos.mp hk
        rw [Finset.mem_filter] at hi
        exact ⟨i, hi.1, hi.2⟩
      · rintro ⟨i, hi, hxi⟩
        refine (mul_pos_iff_of_pos_left hc).mpr ?_
        have hk : 0 < ((Finset.Icc 1 n).filter (fun i => x ∈ K n i)).card :=
          Finset.card_pos.mpr ⟨i, by rw [Finset.mem_filter]; exact ⟨hi, hxi⟩⟩
        exact_mod_cast hk
    rw [hset]
    exact Finset.isCompact_biUnion (Finset.Icc 1 n) (fun i _ => hKcpt n i)
  have hfg_le : ∀ n x, f x - G n x ≤ 1/((n:ℝ)+1) := by
    intro n x
    have h2 : G n x = min (f x) (1 - 1/((n:ℝ)+1)) := rfl
    rw [h2]
    rcases le_total (f x) (1 - 1/((n:ℝ)+1)) with h | h
    · rw [min_eq_left h, sub_self]; positivity
    · rw [min_eq_right h]; linarith [hf1 x]
  have hBadle : ∀ n, μ (Bad n) ≤ ENNReal.ofReal (1/((n:ℝ)+1)) := by
    intro n
    have h1 : μ (Bad n) ≤ ∑ i ∈ Finset.Icc 1 n, μ (A n i \ K n i) := by
      have h := measure_biUnion_finset_le (μ := μ) (Finset.Icc 1 n)
        (fun i => A n i \ K n i)
      simpa [Bad] using h
    have h2 : ∑ i ∈ Finset.Icc 1 n, μ (A n i \ K n i)
        ≤ ENNReal.ofReal (1/((n:ℝ)+1)) := by
      calc ∑ i ∈ Finset.Icc 1 n, μ (A n i \ K n i)
          ≤ ∑ i ∈ Finset.Icc 1 n, ENNReal.ofReal (1/(((n:ℝ)+1))^2) := by
            apply Finset.sum_le_sum
            intro i hi
            exact le_of_lt (hKsdiff n i)
        _ = (Finset.Icc 1 n).card • ENNReal.ofReal (1/(((n:ℝ)+1))^2) := by
            rw [Finset.sum_const]
        _ = n • ENNReal.ofReal (1/(((n:ℝ)+1))^2) := by
            rw [Nat.card_Icc]; simp
        _ = ENNReal.ofReal ((n:ℝ) * (1/(((n:ℝ)+1))^2)) := by
            rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast n,
              ← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal (1/((n:ℝ)+1)) := by
            apply ENNReal.ofReal_le_ofReal
            rw [show (n:ℝ) * (1/(((n:ℝ)+1))^2) = (n:ℝ)/(((n:ℝ)+1)^2) by ring]
            rw [div_le_iff₀ (pow_pos (show (0:ℝ) < (n:ℝ)+1 by positivity) 2)]
            have hsq : (1/((n:ℝ)+1)) * ((n:ℝ)+1)^2 = (n:ℝ)+1 := by field_simp
            rw [hsq]
            linarith [Nat.cast_nonneg (α := ℝ) n]
    exact le_trans h1 h2
  have hbound : ∀ n, (∫⁻ x, ENNReal.ofReal (f x - F n x) ∂μ)
      ≤ ENNReal.ofReal ((2 * μ.real Set.univ + 1) / ((n:ℝ)+1)) := by
    intro n
    let e1 : ℝ → ENNReal := fun x => ENNReal.ofReal (f x - G n x)
    let e2 : ℝ → ENNReal := fun x => ENNReal.ofReal (G n x - T n x)
    let e3 : ℝ → ENNReal := fun x => ENNReal.ofReal (T n x - F n x)
    have he1 : Measurable e1 := by
      change Measurable (fun x : ℝ => ENNReal.ofReal (f x - G n x))
      exact ENNReal.measurable_ofReal.comp (hf.sub (hGmeas n))
    have he2 : Measurable e2 := by
      change Measurable (fun x : ℝ => ENNReal.ofReal (G n x - T n x))
      exact ENNReal.measurable_ofReal.comp ((hGmeas n).sub (hTmeas n))
    have hpt : ∀ x, ENNReal.ofReal (f x - F n x) = e1 x + (e2 x + e3 x) := by
      intro x
      simp only [e1, e2, e3]
      rw [show f x - F n x = (f x - G n x) + ((G n x - T n x) + (T n x - F n x)) by ring]
      rw [ENNReal.ofReal_add (by linarith [hGle_f n x])
        (by linarith [hTle n x, hFTle n x])]
      rw [ENNReal.ofReal_add (by linarith [hTle n x]) (by linarith [hFTle n x])]
    have I1 : ∫⁻ x, e1 x ∂μ ≤ ENNReal.ofReal (1/((n:ℝ)+1)) * μ Set.univ := by
      calc ∫⁻ x, e1 x ∂μ ≤ ∫⁻ x, ENNReal.ofReal (1/((n:ℝ)+1)) ∂μ := by
            apply lintegral_mono; intro x
            simp only [e1]
            exact ENNReal.ofReal_le_ofReal (hfg_le n x)
        _ = ENNReal.ofReal (1/((n:ℝ)+1)) * μ Set.univ := lintegral_const _
    have I2 : ∫⁻ x, e2 x ∂μ ≤ ENNReal.ofReal (1/((n:ℝ)+1)) * μ Set.univ := by
      calc ∫⁻ x, e2 x ∂μ ≤ ∫⁻ x, ENNReal.ofReal (1/((n:ℝ)+1)) ∂μ := by
            apply lintegral_mono; intro x
            simp only [e2]
            exact ENNReal.ofReal_le_ofReal (by linarith [hTge n x])
        _ = ENNReal.ofReal (1/((n:ℝ)+1)) * μ Set.univ := lintegral_const _
    have I3 : ∫⁻ x, e3 x ∂μ ≤ ENNReal.ofReal (1/((n:ℝ)+1)) := by
      calc ∫⁻ x, e3 x ∂μ ≤ ∫⁻ x, (Bad n).indicator (fun _ => (1:ENNReal)) x ∂μ := by
            apply lintegral_mono; intro x
            simp only [e3]
            by_cases hx : x ∈ Bad n
            · rw [Set.indicator_of_mem hx]
              calc ENNReal.ofReal (T n x - F n x) ≤ ENNReal.ofReal 1 :=
                    ENNReal.ofReal_le_ofReal (by linarith [hTle n x, hG1 n x, hF0 n x])
                _ = 1 := ENNReal.ofReal_one
            · rw [Set.indicator_of_notMem hx]
              have hz : ENNReal.ofReal (T n x - F n x) = 0 := by
                rw [ENNReal.ofReal_eq_zero]
                have heq := hTFout n x hx
                linarith
              rw [hz]
        _ = μ (Bad n) := by
            rw [lintegral_indicator_const (hBadmeas n) (1:ENNReal)]; simp
        _ ≤ ENNReal.ofReal (1/((n:ℝ)+1)) := hBadle n
    calc ∫⁻ x, ENNReal.ofReal (f x - F n x) ∂μ
        = ∫⁻ x, (e1 x + (e2 x + e3 x)) ∂μ := lintegral_congr (fun x => hpt x)
      _ = ∫⁻ x, e1 x ∂μ + (∫⁻ x, e2 x ∂μ + ∫⁻ x, e3 x ∂μ) := by
            rw [lintegral_add_left he1, lintegral_add_left he2]
      _ ≤ ENNReal.ofReal (1/((n:ℝ)+1)) * μ Set.univ
            + (ENNReal.ofReal (1/((n:ℝ)+1)) * μ Set.univ
              + ENNReal.ofReal (1/((n:ℝ)+1))) := by
            gcongr
      _ = ENNReal.ofReal ((2 * μ.real Set.univ + 1) / ((n:ℝ)+1)) := by
            have huniv : μ Set.univ = ENNReal.ofReal (μ.real Set.univ) :=
              (ENNReal.ofReal_toReal (measure_ne_top μ Set.univ)).symm
            have hmul : ENNReal.ofReal (1/((n:ℝ)+1)) * μ Set.univ
                = ENNReal.ofReal ((1/((n:ℝ)+1)) * μ.real Set.univ) := by
              rw [huniv, ← ENNReal.ofReal_mul (by positivity)]
            rw [hmul]
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            field_simp
            ring
  have hfin : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_ne_top μ Set.univ) ?_
    calc ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal 1 ∂μ :=
          lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hf1 x))
      _ = 1 * μ Set.univ := by rw [lintegral_const, ENNReal.ofReal_one]
      _ = μ Set.univ := one_mul _
  have hident : ∀ n, (∫ x, F n x ∂μ)
      = (∫ x, f x ∂μ) - (∫⁻ x, ENNReal.ofReal (f x - F n x) ∂μ).toReal := by
    intro n
    have h := integral_sub_eq_toReal_lintegral_ofReal μ (hFmeas n) hf (hF0 n) (hFle_f n) hfin
    linarith
  have hctend : Tendsto (fun n => (∫⁻ x, ENNReal.ofReal (f x - F n x) ∂μ).toReal)
      Filter.atTop (nhds 0) := by
    apply tendsto_toReal_of_le_ofReal
      (x := fun n => ∫⁻ x, ENNReal.ofReal (f x - F n x) ∂μ)
      (r := fun n => (2 * μ.real Set.univ + 1) / ((n:ℝ)+1))
    · intro n
      apply div_nonneg
      · linarith [measureReal_nonneg (μ := μ) (s := Set.univ)]
      · positivity
    · exact hbound
    · have h1 : Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) Filter.atTop (nhds (0:ℝ)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := h1.const_mul (2 * μ.real Set.univ + 1)
      simpa [div_eq_mul_inv, mul_zero] using h2
  have hmain : Tendsto (fun n => (∫ x, f x ∂μ)
      - (∫⁻ x, ENNReal.ofReal (f x - F n x) ∂μ).toReal) Filter.atTop
      (nhds (∫ x, f x ∂μ)) := by
    simpa using (tendsto_const_nhds.sub hctend)
  refine ⟨F, hFusc, hF0, hFle_f, hFsupp, hFcap, ?_⟩
  refine Filter.Tendsto.congr' ?_ hmain
  filter_upwards with n
  exact (hident n).symm

end Commons.MeasureTheory.Real