import Mathlib.Analysis.SpecialFunctions.Pow.Integral

namespace Commons.Analysis.HardyLittlewood

open MeasureTheory Filter Finset
open scoped BigOperators ENNReal Topology

/-- Integral of `t ↦ t ^ r` (`r > -1`) over the interval `(0, c)`. -/
lemma lintegral_Ioo_rpow {r c : ℝ} (hr : -1 < r) (hc : 0 ≤ c) :
    ∫⁻ t in Set.Ioo 0 c, ENNReal.ofReal (t ^ r) ∂volume
      = ENNReal.ofReal (c ^ (r + 1) / (r + 1)) := by
  have hInt : IntegrableOn (fun t : ℝ => t ^ r) (Set.Ioo 0 c) volume := by
    have h1 : IntegrableOn (fun t : ℝ => t ^ r) (Set.Ioc 0 c) volume :=
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c) hr).1
    exact IntegrableOn.mono_set h1 Set.Ioo_subset_Ioc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo 0 c)] fun t : ℝ => t ^ r := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg (le_of_lt ht.1) r
  have key := ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (Set.Ioo 0 c)) hInt hnn
  rw [← key]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le hc]
  rw [integral_rpow (Or.inl hr)]
  rw [Real.zero_rpow (by linarith : r + 1 ≠ 0)]
  ring

/-- The integral over `s` of the indicator of `t` equals the integral over `s ∩ t`. -/
lemma setLIntegral_indicator_eq_inter {s t : Set ℝ} (htm : MeasurableSet t) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x in s, t.indicator f x ∂volume = ∫⁻ x in s ∩ t, f x ∂volume := by
  rw [lintegral_indicator htm]
  rw [Measure.restrict_restrict (μ := volume) (s := t) (t := s) htm]
  rw [Set.inter_comm]

/-- L¹ (`L^p`) bound for the "positive part" kernel `(f m - t)⁺ t ^ (p-2)`. -/
lemma lintegral_max_sub_mul_rpow_le {p : ℝ} (hp : 1 < p) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (s : Finset ℕ) :
    ∫⁻ t in Set.Ioi 0,
        ENNReal.ofReal ((∑ m ∈ s, max (f m - t) 0) * t ^ (p - 2))
        ∂volume
      ≤ ∑ m ∈ s, ENNReal.ofReal (f m ^ p / (p - 1)) := by
  have hp1 : 0 < p - 1 := by linarith
  have hpt : ∀ t ∈ Set.Ioi 0,
      ENNReal.ofReal ((∑ m ∈ s, max (f m - t) 0) * t ^ (p - 2))
        = ∑ m ∈ s, ENNReal.ofReal (max (f m - t) 0 * t ^ (p - 2)) := by
    intro t ht
    rw [Finset.sum_mul]
    exact ENNReal.ofReal_sum_of_nonneg (fun i _ =>
      mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (le_of_lt ht) _))
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
  have hrpow_meas : Measurable (fun t : ℝ => t ^ (p - 2)) := by fun_prop
  have hmeas : ∀ m ∈ s, Measurable (fun t : ℝ => ENNReal.ofReal (max (f m - t) 0 * t ^ (p - 2))) := by
    intro m hm
    exact ((measurable_const.sub measurable_id).max measurable_const).mul hrpow_meas |>.ennreal_ofReal
  rw [lintegral_finsetSum (μ := volume.restrict (Set.Ioi 0))
    (f := fun m t => ENNReal.ofReal (max (f m - t) 0 * t ^ (p - 2))) s hmeas]
  apply Finset.sum_le_sum
  intro m hm
  have hle : ∀ t ∈ Set.Ioi 0,
      ENNReal.ofReal (max (f m - t) 0 * t ^ (p - 2))
        ≤ (Set.Iio (f m)).indicator (fun t => ENNReal.ofReal (f m * t ^ (p - 2))) t := by
    intro t ht
    by_cases h : t < f m
    · have hmax : max (f m - t) 0 = f m - t := max_eq_left (by linarith)
      rw [hmax, Set.indicator_of_mem (by exact h)]
      apply ENNReal.ofReal_le_ofReal
      have htp : 0 ≤ t ^ (p - 2) := Real.rpow_nonneg (le_of_lt ht) _
      have ht0 : (0:ℝ) < t := ht
      exact mul_le_mul_of_nonneg_right (by linarith) htp
    · have hmax : max (f m - t) 0 = 0 := max_eq_right (by linarith [not_lt.mp h])
      rw [hmax, zero_mul, ENNReal.ofReal_zero]
      exact bot_le
  calc ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (max (f m - t) 0 * t ^ (p - 2))
      ≤ ∫⁻ t in Set.Ioi 0,
          (Set.Iio (f m)).indicator (fun t => ENNReal.ofReal (f m * t ^ (p - 2))) t :=
        setLIntegral_mono' measurableSet_Ioi hle
    _ = ∫⁻ t in Set.Ioi 0 ∩ Set.Iio (f m), ENNReal.ofReal (f m * t ^ (p - 2)) :=
        setLIntegral_indicator_eq_inter measurableSet_Iio _
    _ = ENNReal.ofReal (f m) * ∫⁻ t in Set.Ioo 0 (f m), ENNReal.ofReal (t ^ (p - 2)) := by
        rw [show Set.Ioi 0 ∩ Set.Iio (f m) = Set.Ioo 0 (f m) from rfl]
        simp_rw [ENNReal.ofReal_mul (hf m)]
        rw [lintegral_const_mul (ENNReal.ofReal (f m)) (by fun_prop)]
    _ = ENNReal.ofReal (f m) * ENNReal.ofReal ((f m) ^ (p - 1) / (p - 1)) := by
        rw [lintegral_Ioo_rpow (show -1 < p - 2 by linarith) (hf m)]
        congr 2
        ring
    _ = ENNReal.ofReal (f m ^ p / (p - 1)) := by
        rw [← ENNReal.ofReal_mul (hf m)]
        congr 1
        have hkey : f m * f m ^ (p - 1) = f m ^ p := by
          rw [← Real.rpow_one_add' (hf m) (by linarith : 1 + (p - 1) ≠ 0)]
          ring_nf
        rw [← hkey, ← mul_div_assoc]

/-- The supremum defining the "left-tail maximal function" is bounded above. -/
lemma bddAbove_leftTail (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) {N : ℕ}
    (hN : ∀ n, N ≤ n → f n = 0) (τ : ℕ) :
    BddAbove (Set.range (fun c : ℕ => ((c + τ : ℕ) : ℝ)⁻¹ * ∑ m ∈ Finset.range c, f m)) := by
  refine ⟨∑ m ∈ Finset.range N, f m, ?_⟩
  rintro y ⟨c, rfl⟩
  simp only
  have hsum_le : ∑ m ∈ Finset.range c, f m ≤ ∑ m ∈ Finset.range N, f m := by
    have h1 : ∑ m ∈ Finset.range c ∩ Finset.range N, f m = ∑ m ∈ Finset.range c, f m :=
      Finset.sum_subset Finset.inter_subset_left (fun x hx hxn => hN x (by
        exact Nat.le_of_not_lt (fun hlt => hxn (Finset.mem_inter.mpr ⟨hx, Finset.mem_range.mpr hlt⟩))))
    rw [← h1]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun i _ _ => hf i)
  rcases eq_or_ne (c + τ) 0 with h0 | h0
  · have hc0 : (((c + τ : ℕ)) : ℝ) = 0 := by simp [h0]
    rw [hc0, inv_zero, zero_mul]
    exact Finset.sum_nonneg (fun m _ => hf m)
  · have hge1 : (1:ℝ) ≤ ((c + τ : ℕ) : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h0)
    calc ((c + τ : ℕ) : ℝ)⁻¹ * ∑ m ∈ Finset.range c, f m
        ≤ 1 * ∑ m ∈ Finset.range c, f m :=
          mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hge1)
            (Finset.sum_nonneg (fun m _ => hf m))
      _ = ∑ m ∈ Finset.range c, f m := one_mul _
      _ ≤ ∑ m ∈ Finset.range N, f m := hsum_le

/-- Level-set bound for the left-tail maximal function: the level set
`{τ | t < M τ}` has at most `Φ(t)/t + 1` elements, where `Φ(t) = ∑ (f m - t)⁺`. -/
lemma count_levelSet_left_tail (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) {N : ℕ}
    (hN : ∀ n, N ≤ n → f n = 0) {t : ℝ} (ht : 0 < t) :
    Measure.count {τ : ℕ | t < ⨆ (c : ℕ), ((c + τ : ℕ) : ℝ)⁻¹ * ∑ m ∈ Finset.range c, f m}
      ≤ ENNReal.ofReal ((∑ m ∈ Finset.range N, max (f m - t) 0) / t)
        + (if 0 < ∑ m ∈ Finset.range N, max (f m - t) 0 then 1 else 0) := by
  set Φ : ℝ := ∑ m ∈ Finset.range N, max (f m - t) 0 with hΦdef
  have hΦnn : 0 ≤ Φ := by
    rw [hΦdef]; exact Finset.sum_nonneg (fun m _ => le_max_right _ _)
  have hsupp : ∀ m : ℕ, N ≤ m → max (f m - t) 0 = 0 := by
    intro m hm
    rw [hN m hm, zero_sub, max_eq_right (by linarith)]
  have hsum_le' : ∀ c : ℕ, ∑ m ∈ Finset.range c, max (f m - t) 0 ≤ Φ := by
    intro c
    rw [hΦdef]
    have h1 : ∑ m ∈ Finset.range c ∩ Finset.range N, max (f m - t) 0
        = ∑ m ∈ Finset.range c, max (f m - t) 0 :=
      Finset.sum_subset Finset.inter_subset_left (fun x hx hxn => hsupp x (by
        exact Nat.le_of_not_lt (fun hlt => hxn (Finset.mem_inter.mpr ⟨hx, Finset.mem_range.mpr hlt⟩))))
    rw [← h1]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun i _ _ => le_max_right _ _)
  have hkey : ∀ τ : ℕ, t < (⨆ (c : ℕ), ((c + τ : ℕ) : ℝ)⁻¹ * ∑ m ∈ Finset.range c, f m) →
      (τ : ℝ) < Φ / t := by
    intro τ hτ
    obtain ⟨c, hc⟩ := (lt_ciSup_iff (bddAbove_leftTail f hf hN τ)).mp hτ
    have hcpos : (0:ℝ) < ((c + τ : ℕ) : ℝ) := by
      rcases eq_or_ne (c + τ) 0 with h0 | h0
      · exfalso
        have hc0 : (((c + τ : ℕ)) : ℝ) = 0 := by simp [h0]
        rw [hc0, inv_zero, zero_mul] at hc
        linarith
      · exact_mod_cast Nat.pos_of_ne_zero h0
    have h1 : t * ((c + τ : ℕ) : ℝ) < ∑ m ∈ Finset.range c, f m := by
      have hstep := mul_lt_mul_of_pos_left hc hcpos
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcpos), one_mul] at hstep
      rwa [mul_comm] at hstep
    have h2 : t * (τ:ℝ) < ∑ m ∈ Finset.range c, (f m - t) := by
      have hcast : (((c + τ : ℕ)) : ℝ) = (c:ℝ) + (τ:ℝ) := by push_cast; ring
      have h3 : t * ((c:ℝ) + (τ:ℝ)) < ∑ m ∈ Finset.range c, f m := by
        rw [← hcast]; exact h1
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      linarith
    have h4 : t * (τ:ℝ) < Φ :=
      lt_of_lt_of_le h2 (le_trans (Finset.sum_le_sum (fun m _ => le_max_left _ _)) (hsum_le' c))
    rw [lt_div_iff₀ ht, mul_comm]
    exact h4
  by_cases hΦ0 : Φ = 0
  · have hmem : {τ : ℕ | t < ⨆ (c : ℕ), ((c + τ : ℕ) : ℝ)⁻¹ * ∑ m ∈ Finset.range c, f m} = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨τ, hτ⟩
      have h1 := hkey τ hτ
      rw [hΦ0, zero_div] at h1
      exact absurd h1 (not_lt.mpr (Nat.cast_nonneg τ))
    rw [hmem, measure_empty, hΦ0]
    simp
  · have hΦpos : 0 < Φ := lt_of_le_of_ne hΦnn (Ne.symm hΦ0)
    have hsub : {τ : ℕ | t < ⨆ (c : ℕ), ((c + τ : ℕ) : ℝ)⁻¹ * ∑ m ∈ Finset.range c, f m}
        ⊆ (Finset.range (⌊Φ / t⌋₊ + 1) : Set ℕ) := by
      intro τ hτ
      rw [Finset.mem_coe, Finset.mem_range]
      exact Nat.lt_succ_of_le (Nat.le_floor (le_of_lt (hkey τ hτ)))
    calc Measure.count {τ : ℕ | t < ⨆ (c : ℕ), ((c + τ : ℕ) : ℝ)⁻¹ * ∑ m ∈ Finset.range c, f m}
        ≤ Measure.count (Finset.range (⌊Φ / t⌋₊ + 1) : Set ℕ) := measure_mono hsub
      _ = ENNReal.ofReal ((⌊Φ / t⌋₊ : ℝ) + 1) := by
          rw [Measure.count_apply_finset, Finset.card_range, ← ENNReal.ofReal_natCast]
          congr 1
          push_cast
          ring
      _ ≤ ENNReal.ofReal (Φ / t + 1) := ENNReal.ofReal_le_ofReal (by
          have := Nat.floor_le (show (0:ℝ) ≤ Φ / t by positivity); linarith)
      _ = ENNReal.ofReal (Φ / t) + (if 0 < Φ then 1 else 0) := by
          rw [ENNReal.ofReal_add (by positivity) (by norm_num), if_pos hΦpos, ENNReal.ofReal_one]

/-- **Left-tail maximal inequality on `ℕ`** (`p > 1`), with respect to counting measure.

This is the `L^p` (strong type) bound for the "left-tail maximal function"
`M τ = ⨆_c (c + τ)⁻¹ ∑_{m < c} f m` for nonnegative functions `f` with finite support. -/
theorem left_tail_maximal_nat {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℝ), (∀ n, 0 ≤ f n) →
      (∃ M : ℕ, ∀ n, M ≤ n → f n = 0) →
      ∫⁻ τ, ENNReal.ofReal
          ((⨆ (c : ℕ), ((c + τ : ℕ) : ℝ)⁻¹ * ∑ m ∈ Finset.range c, f m) ^ p) ∂Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ τ, ENNReal.ofReal ((f τ) ^ p) ∂Measure.count := by
  have hp1 : (0:ℝ) < p - 1 := by linarith
  have hp0 : (0:ℝ) < p := by linarith
  have hArith : (0:ℝ) < (2 * p - 1) / (p - 1) := by apply div_pos <;> linarith
  refine ⟨((2 * p - 1) / (p - 1)) ^ (1 / p), Real.rpow_pos_of_pos hArith _, ?_⟩
  intro f hf hfin
  obtain ⟨N, hN⟩ := hfin
  set Mx : ℕ → ℝ := fun τ => ⨆ (c : ℕ), ((c + τ : ℕ) : ℝ)⁻¹ * ∑ m ∈ Finset.range c, f m with hMxdef
  set Φ : ℝ → ℝ := fun t => ∑ m ∈ Finset.range N, max (f m - t) 0 with hΦdef
  set S : ℝ := ∑ m ∈ Finset.range N, f m ^ p with hSdef
  have hMx_nn : ∀ τ, 0 ≤ Mx τ := by
    intro τ
    have h0 : ((0 + τ : ℕ) : ℝ)⁻¹ * ∑ m ∈ Finset.range 0, f m = 0 := by simp
    calc (0:ℝ) = ((0 + τ : ℕ) : ℝ)⁻¹ * ∑ m ∈ Finset.range 0, f m := h0.symm
      _ ≤ ⨆ (c : ℕ), ((c + τ : ℕ) : ℝ)⁻¹ * ∑ m ∈ Finset.range c, f m :=
          le_ciSup (bddAbove_leftTail f hf hN τ) 0
      _ = Mx τ := by rw [hMxdef]
  rw [show (∫⁻ τ, ENNReal.ofReal
        ((⨆ (c : ℕ), ((c + τ : ℕ) : ℝ)⁻¹ * ∑ m ∈ Finset.range c, f m) ^ p) ∂Measure.count)
      = ∫⁻ τ, ENNReal.ofReal (Mx τ ^ p) ∂Measure.count from by
        apply lintegral_congr; intro τ; rw [hMxdef]]
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul Measure.count (Eventually.of_forall hMx_nn)
    (measurable_of_countable Mx).aemeasurable hp0]
  have hcount : ∀ t ∈ Set.Ioi 0, Measure.count {a : ℕ | t < Mx a}
      ≤ ENNReal.ofReal (Φ t / t) + (if 0 < Φ t then 1 else 0) := by
    intro t ht
    rw [show {a : ℕ | t < Mx a}
          = {τ : ℕ | t < ⨆ (c : ℕ), ((c + τ : ℕ) : ℝ)⁻¹ * ∑ m ∈ Finset.range c, f m} from by
        ext a; simp only [hMxdef]]
    rw [show Φ t = ∑ m ∈ Finset.range N, max (f m - t) 0 from by rw [hΦdef]]
    exact count_levelSet_left_tail f hf hN ht
  have hΦnn : ∀ t, 0 ≤ Φ t := by
    intro t; rw [hΦdef]; exact Finset.sum_nonneg (fun m _ => le_max_right _ _)
  have hSnn : 0 ≤ S := by
    rw [hSdef]; exact Finset.sum_nonneg (fun m _ => Real.rpow_nonneg (hf m) p)
  have hΦmeas : Measurable Φ := by
    rw [hΦdef]
    exact Finset.measurable_sum (f := fun m t => max (f m - t) 0) (Finset.range N)
      (fun m _ => (measurable_const.sub measurable_id).max measurable_const)
  have hpt : ∀ t ∈ Set.Ioi 0,
      Measure.count {a : ℕ | t < Mx a} * ENNReal.ofReal (t ^ (p - 1))
        ≤ ENNReal.ofReal (Φ t * t ^ (p - 2))
          + ∑ m ∈ Finset.range N,
              (Set.Iio (f m)).indicator (fun t => ENNReal.ofReal (t ^ (p - 1))) t := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    have h1 := hcount t ht
    have h2 : ENNReal.ofReal (Φ t / t) * ENNReal.ofReal (t ^ (p - 1))
        = ENNReal.ofReal (Φ t * t ^ (p - 2)) := by
      rw [← ENNReal.ofReal_mul (div_nonneg (hΦnn t) (le_of_lt ht0))]
      congr 1
      rw [div_eq_mul_inv, mul_assoc, ← Real.rpow_neg_one t, ← Real.rpow_add ht0 (-1) (p - 1),
        show (-1:ℝ) + (p - 1) = p - 2 by ring]
    have h3 : (if 0 < Φ t then (1:ℝ≥0∞) else 0) * ENNReal.ofReal (t ^ (p - 1))
        ≤ ∑ m ∈ Finset.range N,
            (Set.Iio (f m)).indicator (fun t => ENNReal.ofReal (t ^ (p - 1))) t := by
      by_cases hΦ : 0 < Φ t
      · rw [if_pos hΦ, one_mul]
        have hex : ∃ m ∈ Finset.range N, t < f m := by
          by_contra h
          push_neg at h
          have hzero : Φ t = 0 := by
            rw [hΦdef]
            exact Finset.sum_eq_zero (fun m hm => max_eq_right (by linarith [h m hm]))
          linarith
        obtain ⟨m, hm, hlt⟩ := hex
        calc ENNReal.ofReal (t ^ (p - 1))
            = (Set.Iio (f m)).indicator (fun t => ENNReal.ofReal (t ^ (p - 1))) t := by
              rw [Set.indicator_of_mem (by exact hlt)]
          _ ≤ ∑ k ∈ Finset.range N,
                (Set.Iio (f k)).indicator (fun t => ENNReal.ofReal (t ^ (p - 1))) t :=
              Finset.single_le_sum
                (f := fun k => (Set.Iio (f k)).indicator
                  (fun t => ENNReal.ofReal (t ^ (p - 1))) t) (fun i _ => bot_le) hm
      · rw [if_neg hΦ, zero_mul]
        exact bot_le
    calc Measure.count {a : ℕ | t < Mx a} * ENNReal.ofReal (t ^ (p - 1))
        ≤ (ENNReal.ofReal (Φ t / t) + (if 0 < Φ t then 1 else 0)) * ENNReal.ofReal (t ^ (p - 1)) :=
          mul_le_mul_of_nonneg_right h1 bot_le
      _ = ENNReal.ofReal (Φ t / t) * ENNReal.ofReal (t ^ (p - 1))
            + (if 0 < Φ t then 1 else 0) * ENNReal.ofReal (t ^ (p - 1)) := by rw [add_mul]
      _ ≤ ENNReal.ofReal (Φ t * t ^ (p - 2))
            + ∑ m ∈ Finset.range N,
                (Set.Iio (f m)).indicator (fun t => ENNReal.ofReal (t ^ (p - 1))) t :=
          add_le_add (le_of_eq h2) h3
  have hint1 : ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (Φ t * t ^ (p - 2)) ∂volume
      ≤ ∑ m ∈ Finset.range N, ENNReal.ofReal (f m ^ p / (p - 1)) := by
    rw [show (fun t : ℝ => ENNReal.ofReal (Φ t * t ^ (p - 2)))
        = (fun t : ℝ =>
            ENNReal.ofReal ((∑ m ∈ Finset.range N, max (f m - t) 0) * t ^ (p - 2))) from by
        funext t; rw [hΦdef]]
    exact lintegral_max_sub_mul_rpow_le hp f hf (Finset.range N)
  have hint2 : ∫⁻ t in Set.Ioi 0,
        ∑ m ∈ Finset.range N,
          (Set.Iio (f m)).indicator (fun t => ENNReal.ofReal (t ^ (p - 1))) t ∂volume
      ≤ ∑ m ∈ Finset.range N, ENNReal.ofReal (f m ^ p / p) := by
    have hmeas : ∀ m ∈ Finset.range N, Measurable (fun t : ℝ =>
        (Set.Iio (f m)).indicator (fun t => ENNReal.ofReal (t ^ (p - 1))) t) := by
      intro m hm
      exact ((show Measurable (fun t : ℝ => t ^ (p - 1)) by fun_prop).ennreal_ofReal).indicator
        measurableSet_Iio
    rw [lintegral_finsetSum (μ := volume.restrict (Set.Ioi 0))
      (f := fun m t => (Set.Iio (f m)).indicator (fun t => ENNReal.ofReal (t ^ (p - 1))) t)
      (Finset.range N) hmeas]
    apply Finset.sum_le_sum
    intro m hm
    rw [setLIntegral_indicator_eq_inter measurableSet_Iio]
    rw [show Set.Ioi 0 ∩ Set.Iio (f m) = Set.Ioo 0 (f m) from rfl]
    rw [lintegral_Ioo_rpow (show -1 < p - 1 by linarith) (hf m),
      show p - 1 + 1 = p by ring]
  have hmain : ∫⁻ t in Set.Ioi 0, Measure.count {a : ℕ | t < Mx a} * ENNReal.ofReal (t ^ (p - 1))
      ≤ ∑ m ∈ Finset.range N, ENNReal.ofReal (f m ^ p / (p - 1))
        + ∑ m ∈ Finset.range N, ENNReal.ofReal (f m ^ p / p) := by
    calc ∫⁻ t in Set.Ioi 0, Measure.count {a : ℕ | t < Mx a} * ENNReal.ofReal (t ^ (p - 1))
        ≤ ∫⁻ t in Set.Ioi 0, (ENNReal.ofReal (Φ t * t ^ (p - 2))
            + ∑ m ∈ Finset.range N,
                (Set.Iio (f m)).indicator (fun t => ENNReal.ofReal (t ^ (p - 1))) t) :=
          setLIntegral_mono' measurableSet_Ioi hpt
      _ = (∫⁻ t in Set.Ioi 0, ENNReal.ofReal (Φ t * t ^ (p - 2)))
            + (∫⁻ t in Set.Ioi 0, ∑ m ∈ Finset.range N,
                (Set.Iio (f m)).indicator (fun t => ENNReal.ofReal (t ^ (p - 1))) t) := by
          have hA : Measurable (fun t : ℝ => ENNReal.ofReal (Φ t * t ^ (p - 2))) :=
            (hΦmeas.mul (show Measurable (fun t : ℝ => t ^ (p - 2)) by fun_prop)).ennreal_ofReal
          exact lintegral_add_left (μ := volume.restrict (Set.Ioi 0))
            (f := fun t : ℝ => ENNReal.ofReal (Φ t * t ^ (p - 2))) hA _
      _ ≤ (∑ m ∈ Finset.range N, ENNReal.ofReal (f m ^ p / (p - 1)))
            + ∑ m ∈ Finset.range N, ENNReal.ofReal (f m ^ p / p) := add_le_add hint1 hint2
  have hRHS : ∫⁻ τ, ENNReal.ofReal ((f τ) ^ p) ∂Measure.count = ENNReal.ofReal S := by
    rw [hSdef, lintegral_count,
      tsum_eq_sum (s := Finset.range N) (fun b hb => by
        simp only [Finset.mem_range, not_lt] at hb
        rw [hN b hb, Real.zero_rpow (ne_of_gt hp0), ENNReal.ofReal_zero]),
      ENNReal.ofReal_sum_of_nonneg (fun m _ => Real.rpow_nonneg (hf m) p)]
  have hCp : (((2 * p - 1) / (p - 1)) ^ (1 / p)) ^ p = (2 * p - 1) / (p - 1) := by
    rw [← Real.rpow_mul hArith.le (1 / p) p, one_div,
      inv_mul_cancel₀ (ne_of_gt hp0), Real.rpow_one]
  have hCpow_nn : 0 ≤ (((2 * p - 1) / (p - 1)) ^ (1 / p)) ^ p := by
    rw [hCp]; exact hArith.le
  calc ENNReal.ofReal p * ∫⁻ t in Set.Ioi 0,
          Measure.count {a : ℕ | t < Mx a} * ENNReal.ofReal (t ^ (p - 1))
      ≤ ENNReal.ofReal p * (∑ m ∈ Finset.range N, ENNReal.ofReal (f m ^ p / (p - 1))
          + ∑ m ∈ Finset.range N, ENNReal.ofReal (f m ^ p / p)) := mul_le_mul_right hmain _
    _ = ENNReal.ofReal (p * (S / (p - 1) + S / p)) := by
        rw [show (∑ m ∈ Finset.range N, ENNReal.ofReal (f m ^ p / (p - 1)))
              = ENNReal.ofReal (S / (p - 1)) from by
              rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ =>
                div_nonneg (Real.rpow_nonneg (hf m) p) (le_of_lt hp1))]
              congr 1
              rw [← Finset.sum_div, hSdef],
          show (∑ m ∈ Finset.range N, ENNReal.ofReal (f m ^ p / p))
              = ENNReal.ofReal (S / p) from by
              rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ =>
                div_nonneg (Real.rpow_nonneg (hf m) p) (le_of_lt hp0))]
              congr 1
              rw [← Finset.sum_div, hSdef]]
        rw [ENNReal.ofReal_mul (le_of_lt hp0),
          ENNReal.ofReal_add (div_nonneg hSnn (le_of_lt hp1)) (div_nonneg hSnn (le_of_lt hp0))]
    _ = ENNReal.ofReal (S * ((2 * p - 1) / (p - 1))) := by
        congr 1
        field_simp
        ring
    _ = ENNReal.ofReal ((((2 * p - 1) / (p - 1)) ^ (1 / p)) ^ p * S) := by
        rw [hCp]; congr 1; ring
    _ = ENNReal.ofReal ((((2 * p - 1) / (p - 1)) ^ (1 / p)) ^ p) * ENNReal.ofReal S :=
        ENNReal.ofReal_mul hCpow_nn
    _ = ENNReal.ofReal ((((2 * p - 1) / (p - 1)) ^ (1 / p)) ^ p)
          * ∫⁻ τ, ENNReal.ofReal ((f τ) ^ p) ∂Measure.count := by rw [hRHS]

end Commons.Analysis.HardyLittlewood