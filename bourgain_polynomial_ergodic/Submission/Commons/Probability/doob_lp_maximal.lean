import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Martingale.Basic

/-!
# Doob's L^p maximal inequality (Bourgain's polynomial ergodic theorem, supporting lemma)

For a nonnegative submartingale `f` adapted to a filtration `𝒢` on a finite measure space and
`p > 1`, Doob's `L^p` maximal inequality asserts

  `∫⁻ (sup_n f_n)^p ≤ (p/(p-1))^p * sup_n ∫⁻ f_n^p`.

The proof follows the classical route:
* the weak-type `(1,1)` maximal inequality `λ μ{M_N > λ} ≤ ∫_{M_N > λ} f_N` for the prefix maxima
  `M_N = sup_{n ≤ N} f_n` (proved here by the standard first-crossing decomposition, using
  `Submartingale.setIntegral_le`);
* the layer-cake formula `lintegral_rpow_eq_lintegral_meas_lt_mul`;
* Tonelli's theorem plus the elementary integral `∫_0^c t^{p-2} dt = c^{p-1}/(p-1)`;
* Hölder's inequality and elementary arithmetic;
* monotone convergence to pass from the prefix maxima to the full supremum.
-/
open MeasureTheory
open scoped ENNReal

namespace Commons.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

lemma lintegral_Ioi_Iic_ofReal_rpow {r c : ℝ} (hr : -1 < r) (hc : 0 ≤ c) :
    ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal (t ^ r) * (Set.Iic c).indicator (fun _ => (1 : ℝ≥0∞)) t ∂volume
      = ENNReal.ofReal (c ^ (r + 1) / (r + 1)) := by
  have hIoc : Set.Ioc (0:ℝ) c ⊆ Set.Ioi 0 := fun t ht => ht.1
  have hpoint : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0:ℝ))),
      ENNReal.ofReal (t ^ r) * (Set.Iic c).indicator (fun _ => (1 : ℝ≥0∞)) t
        = (Set.Ioc 0 c).indicator (fun t => ENNReal.ofReal (t ^ r)) t := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    by_cases htc : t ≤ c
    · rw [Set.indicator_of_mem (s := Set.Iic c) (a := t) htc (fun _ => (1:ℝ≥0∞)),
        Set.indicator_of_mem (s := Set.Ioc 0 c) (a := t) ⟨ht, htc⟩ (fun t => ENNReal.ofReal (t ^ r)),
        mul_one]
    · rw [Set.indicator_of_notMem (s := Set.Iic c) (a := t) htc (fun _ => (1:ℝ≥0∞)),
        Set.indicator_of_notMem (s := Set.Ioc 0 c) (a := t) (fun h => htc h.2)
          (fun t => ENNReal.ofReal (t ^ r)), mul_zero]
  rw [lintegral_congr_ae hpoint, lintegral_indicator measurableSet_Ioc,
    Measure.restrict_restrict_of_subset hIoc]
  rw [← ofReal_integral_eq_lintegral_ofReal
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c) hr).1 (by
        filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
        exact Real.rpow_nonneg ht.1.le r)]
  rw [← intervalIntegral.integral_of_le (μ := volume) hc]
  congr 1
  rw [integral_rpow (Or.inl hr), Real.zero_rpow (by linarith : r + 1 ≠ 0)]
  ring

lemma lintegral_Ioi_Iio_ofReal_rpow {r c : ℝ} (hr : -1 < r) (hc : 0 ≤ c) :
    ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal (t ^ r) * (Set.Iio c).indicator (fun _ => (1 : ℝ≥0∞)) t ∂volume
      = ENNReal.ofReal (c ^ (r + 1) / (r + 1)) := by
  rw [← lintegral_Ioi_Iic_ofReal_rpow hr hc]
  apply lintegral_congr_ae
  have hne : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0:ℝ))), t ≠ c := by
    rw [ae_restrict_iff' measurableSet_Ioi, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (fun t ht => ?_) (MeasureTheory.measure_singleton c)
    simp only [Set.mem_singleton_iff]
    by_contra h
    exact ht (fun _ => h)
  filter_upwards [hne] with t ht
  by_cases h : t < c
  · rw [Set.indicator_of_mem (s := Set.Iio c) (a := t) h (fun _ => (1:ℝ≥0∞)),
      Set.indicator_of_mem (s := Set.Iic c) (a := t) (le_of_lt h) (fun _ => (1:ℝ≥0∞))]
  · rw [Set.indicator_of_notMem (s := Set.Iio c) (a := t) h (fun _ => (1:ℝ≥0∞)),
      Set.indicator_of_notMem (s := Set.Iic c) (a := t) (fun hle => h (lt_of_le_of_ne hle ht))
        (fun _ => (1:ℝ≥0∞))]

lemma lintegral_rpow_le_of_weak_type {M g : Ω → ℝ} [SFinite μ]
    (hM_nn : 0 ≤ᵐ[μ] M) (hM_meas : Measurable M)
    (_hg_nn : 0 ≤ᵐ[μ] g) (hg_meas : Measurable g)
    {p : ℝ} (hp : 1 < p)
    (hweak : ∀ t, 0 < t → ENNReal.ofReal t * μ {a | t < M a}
      ≤ ∫⁻ a in {a | t < M a}, ENNReal.ofReal (g a) ∂μ) :
    ∫⁻ ω, (ENNReal.ofReal (M ω))^p ∂μ
      ≤ ENNReal.ofReal (p/(p-1)) * ∫⁻ ω, ENNReal.ofReal (g ω) * (ENNReal.ofReal (M ω))^(p-1) ∂μ := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp1pos : 0 < p - 1 := by linarith
  have hp2 : -1 < p - 2 := by linarith
  have hL : ∫⁻ ω, (ENNReal.ofReal (M ω))^p ∂μ = ∫⁻ ω, ENNReal.ofReal (M ω ^ p) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hM_nn] with ω hω
    exact ENNReal.ofReal_rpow_of_nonneg hω hp0.le
  rw [hL, lintegral_rpow_eq_lintegral_meas_lt_mul μ hM_nn hM_meas.aemeasurable hp0]
  set Y : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (g ω) * (ENNReal.ofReal (M ω))^(p-1) ∂μ with hY
  have hA : ∫⁻ t in Set.Ioi 0, μ {a | t < M a} * ENNReal.ofReal (t ^ (p-1)) ∂volume
      ≤ ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (t ^ (p-2)) *
          (∫⁻ a in {a | t < M a}, ENNReal.ofReal (g a) ∂μ) ∂volume := by
    apply lintegral_mono_ae
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    have hw := hweak t ht
    have hconst : ENNReal.ofReal (t ^ (p-1)) = ENNReal.ofReal (t ^ (p-2)) * ENNReal.ofReal t := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le (p-2)),
        ← Real.rpow_add_one (ne_of_gt ht) (p-2)]
      congr 1
      ring_nf
    calc μ {a | t < M a} * ENNReal.ofReal (t ^ (p-1))
        = (μ {a | t < M a} * ENNReal.ofReal (t ^ (p-2))) * ENNReal.ofReal t := by
          rw [hconst, mul_assoc]
      _ = ENNReal.ofReal (t ^ (p-2)) * (ENNReal.ofReal t * μ {a | t < M a}) := by ring_nf
      _ ≤ ENNReal.ofReal (t ^ (p-2)) * ∫⁻ a in {a | t < M a}, ENNReal.ofReal (g a) ∂μ :=
          mul_le_mul_of_nonneg_left hw (bot_le : (0:ℝ≥0∞) ≤ ENNReal.ofReal (t ^ (p-2)))
  have hK : AEMeasurable (fun q : ℝ × Ω => ENNReal.ofReal (q.1 ^ (p-2)) *
        (ENNReal.ofReal (g q.2) * (Set.Ioi (0:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) (M q.2 - q.1)))
      ((volume.restrict (Set.Ioi (0:ℝ))).prod μ) := by
    apply Measurable.aemeasurable
    have hpow : Measurable (fun x : ℝ => x ^ (p-2)) := by measurability
    have h1 : Measurable (fun q : ℝ × Ω => ENNReal.ofReal (q.1 ^ (p-2))) :=
      ((ENNReal.continuous_ofReal.measurable).comp hpow).comp measurable_fst
    have h2 : Measurable (fun q : ℝ × Ω => ENNReal.ofReal (g q.2)) :=
      ((ENNReal.continuous_ofReal.measurable).comp hg_meas).comp measurable_snd
    have hind : Measurable ((Set.Ioi (0:ℝ)).indicator (fun _ => (1:ℝ≥0∞))) :=
      Measurable.indicator measurable_const measurableSet_Ioi
    have harg : Measurable (fun q : ℝ × Ω => M q.2 - q.1) :=
      (hM_meas.comp measurable_snd).sub measurable_fst
    have h3 : Measurable fun q : ℝ × Ω =>
        (Set.Ioi (0:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) (M q.2 - q.1) :=
      hind.comp harg
    exact h1.mul (h2.mul h3)
  have hB : ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (t ^ (p-2)) *
        (∫⁻ a in {a | t < M a}, ENNReal.ofReal (g a) ∂μ) ∂volume
      = ENNReal.ofReal ((p-1)⁻¹) * Y := by
    have hstep1 : ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (t ^ (p-2)) *
          (∫⁻ a in {a | t < M a}, ENNReal.ofReal (g a) ∂μ) ∂volume
        = ∫⁻ t in Set.Ioi 0, ∫⁻ a, ENNReal.ofReal (t ^ (p-2)) *
            (ENNReal.ofReal (g a) *
              (Set.Ioi (0:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) (M a - t)) ∂μ ∂volume := by
      apply lintegral_congr; intro t
      rw [← lintegral_indicator (measurableSet_lt measurable_const hM_meas)]
      rw [← lintegral_const_mul' (ENNReal.ofReal (t ^ (p-2))) _ ENNReal.ofReal_ne_top]
      apply lintegral_congr; intro a
      have hpt : (Set.ofPred (fun a => t < M a)).indicator (fun a => ENNReal.ofReal (g a)) a
          = ENNReal.ofReal (g a) * (Set.Ioi (0:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) (M a - t) := by
        by_cases h : t < M a
        · rw [Set.indicator_of_mem (s := {a | t < M a}) (a := a) h (fun a => ENNReal.ofReal (g a)),
            Set.indicator_of_mem (s := Set.Ioi (0:ℝ)) (a := M a - t) (by
              simp only [Set.mem_Ioi]; linarith) (fun _ => (1:ℝ≥0∞)), mul_one]
        · rw [Set.indicator_of_notMem (s := {a | t < M a}) (a := a) h (fun a => ENNReal.ofReal (g a)),
            Set.indicator_of_notMem (s := Set.Ioi (0:ℝ)) (a := M a - t) (by
              simp only [Set.mem_Ioi, not_lt]; linarith) (fun _ => (1:ℝ≥0∞)), mul_zero]
      rw [hpt]
    have hstep2 : ∫⁻ t in Set.Ioi 0, ∫⁻ a, ENNReal.ofReal (t ^ (p-2)) *
            (ENNReal.ofReal (g a) *
              (Set.Ioi (0:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) (M a - t)) ∂μ ∂volume
        = ∫⁻ a, ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (t ^ (p-2)) *
            (ENNReal.ofReal (g a) *
              (Set.Ioi (0:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) (M a - t)) ∂volume ∂μ :=
      lintegral_lintegral_swap (μ := volume.restrict (Set.Ioi (0:ℝ))) (ν := μ) hK
    have hstep3 : ∫⁻ a, ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (t ^ (p-2)) *
          (ENNReal.ofReal (g a) *
            (Set.Ioi (0:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) (M a - t)) ∂volume ∂μ
        = ∫⁻ a, ENNReal.ofReal (g a) * ENNReal.ofReal ((M a) ^ (p-1) / (p-1)) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hM_nn] with a ha
      have hind2 : ∀ t : ℝ, (Set.Ioi (0:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) (M a - t)
          = (Set.Iio (M a)).indicator (fun _ => (1:ℝ≥0∞)) t := by
        intro t
        by_cases h : t < M a
        · rw [Set.indicator_of_mem (s := Set.Ioi (0:ℝ)) (a := M a - t) (by
              simp only [Set.mem_Ioi]; linarith) (fun _ => (1:ℝ≥0∞)),
            Set.indicator_of_mem (s := Set.Iio (M a)) (a := t) h (fun _ => (1:ℝ≥0∞))]
        · rw [Set.indicator_of_notMem (s := Set.Ioi (0:ℝ)) (a := M a - t) (by
              simp only [Set.mem_Ioi, not_lt]; linarith) (fun _ => (1:ℝ≥0∞)),
            Set.indicator_of_notMem (s := Set.Iio (M a)) (a := t) h (fun _ => (1:ℝ≥0∞))]
      calc ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (t^(p-2)) * (ENNReal.ofReal (g a) *
              (Set.Ioi (0:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) (M a - t)) ∂volume
          = ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (g a) * (ENNReal.ofReal (t^(p-2)) *
              (Set.Iio (M a)).indicator (fun _ => (1:ℝ≥0∞)) t) ∂volume := by
            apply lintegral_congr; intro t
            rw [hind2 t]; ring
        _ = ENNReal.ofReal (g a) * ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (t^(p-2)) *
              (Set.Iio (M a)).indicator (fun _ => (1:ℝ≥0∞)) t ∂volume := by
            rw [lintegral_const_mul' (ENNReal.ofReal (g a)) _ ENNReal.ofReal_ne_top]
        _ = ENNReal.ofReal (g a) * ENNReal.ofReal ((M a)^(p-1)/(p-1)) := by
            rw [lintegral_Ioi_Iio_ofReal_rpow hp2 ha, show p - 2 + 1 = p - 1 by ring]
    rw [hstep1, hstep2, hstep3]
    rw [show ∫⁻ a, ENNReal.ofReal (g a) * ENNReal.ofReal ((M a) ^ (p-1) / (p-1)) ∂μ
        = ENNReal.ofReal ((p-1)⁻¹) * ∫⁻ ω, ENNReal.ofReal (g ω) * (ENNReal.ofReal (M ω))^(p-1) ∂μ from by
      rw [← lintegral_const_mul' (ENNReal.ofReal ((p-1)⁻¹)) _ ENNReal.ofReal_ne_top]
      apply lintegral_congr_ae
      filter_upwards [hM_nn] with a ha
      rw [div_eq_mul_inv, ENNReal.ofReal_mul (Real.rpow_nonneg ha (p-1)),
        ENNReal.ofReal_rpow_of_nonneg ha hp1pos.le]
      ring]
  calc ENNReal.ofReal p * ∫⁻ t in Set.Ioi 0, μ {a | t < M a} * ENNReal.ofReal (t ^ (p-1)) ∂volume
      ≤ ENNReal.ofReal p * ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (t ^ (p-2)) *
          (∫⁻ a in {a | t < M a}, ENNReal.ofReal (g a) ∂μ) ∂volume :=
        mul_le_mul_of_nonneg_left hA (bot_le : (0:ℝ≥0∞) ≤ ENNReal.ofReal p)
    _ = ENNReal.ofReal p * (ENNReal.ofReal ((p-1)⁻¹) * Y) := by rw [hB]
    _ = ENNReal.ofReal (p/(p-1)) * Y := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hp0.le, div_eq_mul_inv]

lemma ennreal_le_pow_of_le_mul_rpow {X B : ℝ≥0∞} {p : ℝ} (hp : 1 < p) (hX : X < ⊤)
    (h : X ≤ B * X ^ ((p - 1) / p)) : X ≤ B ^ p := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : (0:ℝ) < (p-1)/p := by positivity
  rcases eq_or_ne X 0 with hX0 | hX0
  · rw [hX0]; exact bot_le
  have hsplit : X = X ^ ((p-1)/p) * X ^ (1/p) := by
    rw [← ENNReal.rpow_add_of_nonneg ((p-1)/p) (1/p) hq0.le (by positivity),
      show (p-1)/p + 1/p = 1 by rw [← add_div, sub_add_cancel, div_self (ne_of_gt hp0)],
      ENNReal.rpow_one]
  have hz : X ^ ((p-1)/p) ≠ 0 := fun hc => hX0 ((ENNReal.rpow_eq_zero_iff_of_pos hq0).mp hc)
  have ht : X ^ ((p-1)/p) ≠ ⊤ := ((ENNReal.rpow_lt_top_iff_of_pos hq0).mpr hX).ne
  have h2 : X ^ ((p-1)/p) * X ^ (1/p) ≤ X ^ ((p-1)/p) * B := by
    calc X ^ ((p-1)/p) * X ^ (1/p) = X := hsplit.symm
      _ ≤ B * X ^ ((p-1)/p) := h
      _ = X ^ ((p-1)/p) * B := mul_comm _ _
  have h3 : X ^ (1/p) ≤ B := (ENNReal.mul_le_mul_iff_right hz ht).mp h2
  calc X = X ^ (1:ℝ) := (ENNReal.rpow_one X).symm
    _ = X ^ ((1/p) * p) := by rw [one_div, inv_mul_cancel₀ (ne_of_gt hp0)]
    _ = (X ^ (1/p)) ^ p := ENNReal.rpow_mul X (1/p) p
    _ ≤ B ^ p := ENNReal.rpow_le_rpow h3 hp0.le


lemma measurableSet_prefixMax {f : ℕ → Ω → ℝ} {𝒢 : Filtration ℕ mΩ}
    (hsub : Submartingale f 𝒢 μ) (N : ℕ) (lam : ℝ) :
    MeasurableSet[𝒢 N] {ω | lam < partialSups f N ω} := by
  induction N with
  | zero =>
      simp only [partialSups_zero]
      exact (hsub.stronglyAdapted 0).measurable measurableSet_Ioi
  | succ N ih =>
      have h1 : MeasurableSet[𝒢 (N+1)] {ω | lam < partialSups f N ω} :=
        (𝒢.mono (Nat.le_succ N)) _ ih
      have h2 : MeasurableSet[𝒢 (N+1)] {ω | lam < f (N+1) ω} :=
        (hsub.stronglyAdapted (N+1)).measurable measurableSet_Ioi
      have heq : {ω | lam < partialSups f (N+1) ω}
          = {ω | lam < partialSups f N ω} ∪ {ω | lam < f (N+1) ω} := by
        ext ω
        simp only [Set.mem_union, Set.mem_ofPred_eq]
        rw [show partialSups f (N+1) = partialSups f N ⊔ f (N+1) by
              simp, Pi.sup_apply, lt_max_iff]
      rw [heq]
      exact h1.union h2

theorem submartingale_maximal_weak {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {𝒢 : Filtration ℕ mΩ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    {N : ℕ} {lam : ℝ} (_hlam : 0 < lam) :
    ENNReal.ofReal lam * μ {ω | lam < partialSups f N ω}
      ≤ ∫⁻ ω in {ω | lam < partialSups f N ω}, ENNReal.ofReal (f N ω) ∂μ := by
  induction N with
  | zero =>
      simp only [partialSups_zero]
      have hs : MeasurableSet {ω : Ω | lam < f 0 ω} :=
        (𝒢.le 0) _ ((hsub.stronglyAdapted 0).measurable measurableSet_Ioi)
      calc ENNReal.ofReal lam * μ {ω : Ω | lam < f 0 ω}
          = ∫⁻ ω in {ω : Ω | lam < f 0 ω}, ENNReal.ofReal lam ∂μ := by
            simp [lintegral_const, Measure.restrict_apply]
        _ ≤ ∫⁻ ω in {ω : Ω | lam < f 0 ω}, ENNReal.ofReal (f 0 ω) ∂μ := by
            apply lintegral_mono_ae
            rw [ae_restrict_iff' hs]
            exact Filter.Eventually.of_forall (fun ω hω => ENNReal.ofReal_le_ofReal (le_of_lt hω))
  | succ N ih =>
      set s : Set Ω := {ω | lam < partialSups f N ω} with hs_def
      set D : Set Ω := {ω | lam < f (N+1) ω} \ s with hD_def
      have hs_meas : MeasurableSet[𝒢 N] s := by
        rw [hs_def]; exact measurableSet_prefixMax hsub N lam
      have hs_amb : MeasurableSet s := (𝒢.le N) s hs_meas
      have hf_meas : MeasurableSet {ω : Ω | lam < f (N+1) ω} :=
        (𝒢.le (N+1)) _ ((hsub.stronglyAdapted (N+1)).measurable measurableSet_Ioi)
      have hD_amb : MeasurableSet D := hf_meas.diff hs_amb
      have hdisj : Disjoint s D := by
        rw [hD_def]; exact Set.disjoint_sdiff_right
      have hsu : s ∪ D = {ω | lam < partialSups f (N+1) ω} := by
        rw [hD_def, hs_def]
        ext ω
        simp only [Set.mem_union, Set.mem_sdiff, Set.mem_ofPred_eq]
        rw [show partialSups f (N+1) = partialSups f N ⊔ f (N+1) by
              simp, Pi.sup_apply, lt_max_iff]
        tauto
      rw [← hsu, measure_union hdisj hD_amb, mul_add,
        lintegral_union (A := s) (B := D) hD_amb hdisj]
      apply add_le_add
      · calc ENNReal.ofReal lam * μ s
            ≤ ∫⁻ ω in s, ENNReal.ofReal (f N ω) ∂μ := ih
          _ ≤ ∫⁻ ω in s, ENNReal.ofReal (f (N+1) ω) ∂μ := by
              have h1 : ∫⁻ ω in s, ENNReal.ofReal (f N ω) ∂μ
                  = ENNReal.ofReal (∫ ω in s, f N ω ∂μ) :=
                (ofReal_integral_eq_lintegral_ofReal ((hsub.integrable N).integrableOn (s := s))
                  (Filter.Eventually.of_forall (fun ω => hnonneg N ω))).symm
              have h2 : ∫⁻ ω in s, ENNReal.ofReal (f (N+1) ω) ∂μ
                  = ENNReal.ofReal (∫ ω in s, f (N+1) ω ∂μ) :=
                (ofReal_integral_eq_lintegral_ofReal ((hsub.integrable (N+1)).integrableOn (s := s))
                  (Filter.Eventually.of_forall (fun ω => hnonneg (N+1) ω))).symm
              rw [h1, h2]
              exact ENNReal.ofReal_le_ofReal
                (Submartingale.setIntegral_le hsub (Nat.le_succ N) hs_meas)
      · calc ENNReal.ofReal lam * μ D
            = ∫⁻ ω in D, ENNReal.ofReal lam ∂μ := by
              simp [lintegral_const, Measure.restrict_apply]
          _ ≤ ∫⁻ ω in D, ENNReal.ofReal (f (N+1) ω) ∂μ := by
              apply lintegral_mono_ae
              rw [ae_restrict_iff' hD_amb]
              exact Filter.Eventually.of_forall
                (fun ω hω => ENNReal.ofReal_le_ofReal (le_of_lt hω.1))

lemma measurable_partialSups {f : ℕ → Ω → ℝ} {𝒢 : Filtration ℕ mΩ}
    (hsub : Submartingale f 𝒢 μ) (N : ℕ) :
    Measurable (fun ω => partialSups f N ω) := by
  induction N with
  | zero =>
      simpa using ((hsub.stronglyAdapted 0).mono (𝒢.le 0)).measurable
  | succ N ih =>
      have h2 : Measurable (f (N+1)) := ((hsub.stronglyAdapted (N+1)).mono (𝒢.le (N+1))).measurable
      have hsup := ih.sup h2
      have hps : (fun ω => partialSups f (N+1) ω)
          = ((fun ω => partialSups f N ω) ⊔ f (N+1)) := by
        funext ω
        rw [show partialSups f (N+1) = partialSups f N ⊔ f (N+1) by
              simp, Pi.sup_apply]
      rw [hps]; exact hsup

lemma exists_partialSups_eq (f : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    ∃ k ≤ N, partialSups f N ω = f k ω := by
  obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_Iic (a := N)) (fun k => f k ω)
  refine ⟨k, Finset.mem_Iic.mp hk, ?_⟩
  rw [Pi.partialSups_apply, partialSups_apply]
  exact hkeq

theorem doob_lp_maximal {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {𝒢 : MeasureTheory.Filtration ℕ mΩ}
    (hsub : MeasureTheory.Submartingale f 𝒢 μ) (hnonneg : 0 ≤ f) {p : ℝ} (hp : 1 < p)
    (hint : ∀ n, MeasureTheory.MemLp (f n) (ENNReal.ofReal p) μ) :
    MeasureTheory.lintegral μ (fun ω => (⨆ n : ℕ, ‖f n ω‖ₑ) ^ p)
      ≤ (ENNReal.ofReal (p / (p - 1))) ^ p *
          (⨆ n : ℕ, MeasureTheory.lintegral μ (fun ω => ‖f n ω‖ₑ ^ p)) := by
  have hnn : ∀ n ω, 0 ≤ f n ω := fun n => Pi.le_def.mp (Pi.le_def.mp hnonneg n)
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp1pos : 0 < p - 1 := by linarith
  have hpq : Real.HolderConjugate p (p/(p-1)) := Real.HolderConjugate.conjExponent hp
  have hAn : ∀ n, ∫⁻ ω, ‖f n ω‖ₑ ^ p ∂μ < ∞ := by
    intro n
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := ENNReal.ofReal p) (f := f n) (ne_of_gt (ENNReal.ofReal_pos.mpr hp0))
      ENNReal.ofReal_ne_top (hint n).aestronglyMeasurable).mp (hint n)
    rwa [ENNReal.toReal_ofReal hp0.le] at h
  have hmain : ∀ N, ∫⁻ ω, (ENNReal.ofReal (partialSups f N ω))^p ∂μ
      ≤ (ENNReal.ofReal (p/(p-1)))^p * (⨆ n, ∫⁻ ω, ‖f n ω‖ₑ ^ p ∂μ) := by
    intro N
    have hM_meas : Measurable (fun ω => partialSups f N ω) := measurable_partialSups hsub N
    have hM_nn : 0 ≤ᵐ[μ] (fun ω => partialSups f N ω) :=
      Filter.Eventually.of_forall fun ω => by
        obtain ⟨k, hk, hkeq⟩ := exists_partialSups_eq f N ω
        show (0:ℝ) ≤ partialSups f N ω
        rw [hkeq]; exact hnn k ω
    have hg_meas : Measurable (f N) := ((hsub.stronglyAdapted N).mono (𝒢.le N)).measurable
    have hg_nn : 0 ≤ᵐ[μ] (f N) := Filter.Eventually.of_forall (fun ω => hnn N ω)
    have hweak : ∀ t, 0 < t → ENNReal.ofReal t * μ {a | t < partialSups f N a}
        ≤ ∫⁻ a in {a | t < partialSups f N a}, ENNReal.ofReal (f N a) ∂μ :=
      fun t ht => submartingale_maximal_weak hsub hnn ht
    have hstep1 := lintegral_rpow_le_of_weak_type hM_nn hM_meas hg_nn hg_meas hp hweak
    have hYle : ∫⁻ ω, ENNReal.ofReal (f N ω) * (ENNReal.ofReal (partialSups f N ω))^(p-1) ∂μ
        ≤ (∫⁻ ω, ‖f N ω‖ₑ ^ p ∂μ) ^ (1/p)
          * (∫⁻ ω, (ENNReal.ofReal (partialSups f N ω))^p ∂μ) ^ (1/(p/(p-1))) := by
      have hhol := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
        (f := fun ω => ENNReal.ofReal (f N ω))
        (g := fun ω => (ENNReal.ofReal (partialSups f N ω))^(p-1))
        ((ENNReal.continuous_ofReal.measurable).comp hg_meas).aemeasurable (by measurability)
      have e1 : ∫⁻ ω, (ENNReal.ofReal (f N ω)) ^ p ∂μ = ∫⁻ ω, ‖f N ω‖ₑ ^ p ∂μ := by
        apply lintegral_congr; intro a
        rw [← Real.enorm_eq_ofReal (hnn N a)]
      have e2 : ∫⁻ ω, ((ENNReal.ofReal (partialSups f N ω))^(p-1))^(p/(p-1)) ∂μ
          = ∫⁻ ω, (ENNReal.ofReal (partialSups f N ω))^p ∂μ := by
        apply lintegral_congr; intro a
        rw [← ENNReal.rpow_mul, show (p-1) * (p/(p-1)) = p by field_simp]
      rw [e1, e2] at hhol
      exact hhol
    have hfk_meas : ∀ k, Measurable (fun ω => ‖f k ω‖ₑ ^ p) := by
      intro k
      have hfk : Measurable (f k) := ((hsub.stronglyAdapted k).mono (𝒢.le k)).measurable
      measurability
    have hXfin : ∫⁻ ω, (ENNReal.ofReal (partialSups f N ω))^p ∂μ < ∞ := by
      have hle : ∫⁻ ω, (ENNReal.ofReal (partialSups f N ω))^p ∂μ
          ≤ ∑ k ∈ Finset.range (N+1), ∫⁻ ω, ‖f k ω‖ₑ ^ p ∂μ := by
        calc ∫⁻ ω, (ENNReal.ofReal (partialSups f N ω))^p ∂μ
            ≤ ∫⁻ ω, ∑ k ∈ Finset.range (N+1), ‖f k ω‖ₑ ^ p ∂μ := by
              apply lintegral_mono; intro ω
              obtain ⟨k, hk, hkeq⟩ := exists_partialSups_eq f N ω
              show (ENNReal.ofReal (partialSups f N ω))^p
                ≤ ∑ k ∈ Finset.range (N+1), ‖f k ω‖ₑ ^ p
              rw [hkeq, ← Real.enorm_eq_ofReal (hnn k ω)]
              exact Finset.single_le_sum (f := fun i => ‖f i ω‖ₑ ^ p) (fun i _ => by positivity)
                (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
          _ = ∑ k ∈ Finset.range (N+1), ∫⁻ ω, ‖f k ω‖ₑ ^ p ∂μ :=
              lintegral_finsetSum _ (fun k _ => hfk_meas k)
      exact lt_of_le_of_lt hle (ENNReal.sum_lt_top.mpr (fun k _ => hAn k))
    have hcomb : ∫⁻ ω, (ENNReal.ofReal (partialSups f N ω))^p ∂μ
        ≤ (ENNReal.ofReal (p/(p-1)) * (∫⁻ ω, ‖f N ω‖ₑ ^ p ∂μ) ^ (1/p))
          * (∫⁻ ω, (ENNReal.ofReal (partialSups f N ω))^p ∂μ) ^ ((p-1)/p) := by
      calc ∫⁻ ω, (ENNReal.ofReal (partialSups f N ω))^p ∂μ
          ≤ ENNReal.ofReal (p/(p-1)) * ∫⁻ ω, ENNReal.ofReal (f N ω) * (ENNReal.ofReal (partialSups f N ω))^(p-1) ∂μ := hstep1
        _ ≤ ENNReal.ofReal (p/(p-1)) * ((∫⁻ ω, ‖f N ω‖ₑ ^ p ∂μ) ^ (1/p)
              * (∫⁻ ω, (ENNReal.ofReal (partialSups f N ω))^p ∂μ) ^ (1/(p/(p-1)))) :=
            mul_le_mul_of_nonneg_left hYle bot_le
        _ = (ENNReal.ofReal (p/(p-1)) * (∫⁻ ω, ‖f N ω‖ₑ ^ p ∂μ) ^ (1/p))
              * (∫⁻ ω, (ENNReal.ofReal (partialSups f N ω))^p ∂μ) ^ ((p-1)/p) := by
            rw [mul_assoc, show 1/(p/(p-1)) = (p-1)/p by field_simp]
    calc ∫⁻ ω, (ENNReal.ofReal (partialSups f N ω))^p ∂μ
        ≤ (ENNReal.ofReal (p/(p-1)) * (∫⁻ ω, ‖f N ω‖ₑ ^ p ∂μ) ^ (1/p))^p :=
          ennreal_le_pow_of_le_mul_rpow hp hXfin hcomb
      _ = (ENNReal.ofReal (p/(p-1)))^p * (∫⁻ ω, ‖f N ω‖ₑ ^ p ∂μ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, show (1/p : ℝ) = p⁻¹ from one_div p,
            ENNReal.rpow_inv_rpow (ne_of_gt hp0)]
      _ ≤ (ENNReal.ofReal (p/(p-1)))^p * (⨆ n, ∫⁻ ω, ‖f n ω‖ₑ ^ p ∂μ) :=
          mul_le_mul_of_nonneg_left (le_iSup (fun n => ∫⁻ ω, ‖f n ω‖ₑ ^ p ∂μ) N) bot_le
  have hfun : (fun ω => (⨆ n, ‖f n ω‖ₑ)^p)
      = (fun ω => ⨆ N, (ENNReal.ofReal (partialSups f N ω))^p) := by
    funext ω
    have hsup : (⨆ n, ‖f n ω‖ₑ) = ⨆ N, ENNReal.ofReal (partialSups f N ω) := by
      apply le_antisymm
      · apply iSup_le; intro n
        have h1 : f n ω ≤ partialSups f n ω := (Pi.le_def.mp (Pi.le_def.mp (le_partialSups f) n)) ω
        calc ‖f n ω‖ₑ = ENNReal.ofReal (f n ω) := Real.enorm_eq_ofReal (hnn n ω)
          _ ≤ ENNReal.ofReal (partialSups f n ω) := ENNReal.ofReal_le_ofReal h1
          _ ≤ ⨆ N, ENNReal.ofReal (partialSups f N ω) :=
              le_iSup (fun N => ENNReal.ofReal (partialSups f N ω)) n
      · apply iSup_le; intro N
        obtain ⟨k, hk, hkeq⟩ := exists_partialSups_eq f N ω
        rw [hkeq]
        exact le_trans (le_of_eq (Real.enorm_eq_ofReal (hnn k ω)).symm) (le_iSup (fun n => ‖f n ω‖ₑ) k)
    rw [hsup]
    exact (ENNReal.orderIsoRpow p hp0).map_iSup (fun N => ENNReal.ofReal (partialSups f N ω))
  rw [hfun]
  have hmeasN : ∀ N, AEMeasurable (fun ω => (ENNReal.ofReal (partialSups f N ω))^p) μ := by
    intro N
    have h := measurable_partialSups hsub N
    exact (by measurability : Measurable (fun ω => (ENNReal.ofReal (partialSups f N ω))^p)).aemeasurable
  have hmono : ∀ᵐ ω ∂μ, Monotone fun N => (ENNReal.ofReal (partialSups f N ω))^p := by
    filter_upwards with ω
    intro N M hNM
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
      ((Pi.le_def.mp (partialSups_monotone f hNM)) ω)) hp0.le
  rw [lintegral_iSup' hmeasN hmono]
  exact iSup_le hmain

end Commons.Probability