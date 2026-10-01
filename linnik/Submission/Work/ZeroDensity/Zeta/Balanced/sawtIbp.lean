import Mathlib

namespace Work.ZeroDensity.Zeta.Balanced

open MeasureTheory Filter intervalIntegral
open scoped Topology

noncomputable section

/-- The sawtooth function `{u} - 1/2`, viewed as a complex-valued function. -/
def saw (u : ℝ) : ℂ := ((Int.fract u : ℝ) : ℂ) - 1 / 2

/-- The continuous function `({u}² - {u})/2`, an antiderivative of `saw` away from the
integers. -/
def saw2 (u : ℝ) : ℂ := ((((Int.fract u) ^ 2 - Int.fract u) / 2 : ℝ) : ℂ)

/-- The derivative of `u ↦ saw2 u * u^{-s-1}`, i.e. of `sawF s`. -/
def sawH (s : ℂ) (u : ℝ) : ℂ :=
  saw u * (u : ℂ) ^ (-s - 1) - (s + 1) * (saw2 u * (u : ℂ) ^ (-s - 2))

/-- The function `({u}²-{u})/2 · u^{-s-1}`. -/
def sawF (s : ℂ) (u : ℝ) : ℂ := saw2 u * (u : ℂ) ^ (-s - 1)

lemma norm_ofReal' (x : ℝ) : ‖(x : ℂ)‖ = |x| := by simp

lemma fract_eq_sub_of_mem_Ioo {u : ℝ} {n : ℤ} (h : u ∈ Set.Ioo (n : ℝ) (n + 1)) :
    Int.fract u = u - n := by
  have hfl : ⌊u⌋ = n := (Int.floor_eq_iff).2 ⟨le_of_lt h.1, h.2⟩
  rw [Int.fract, hfl]

lemma measurable_saw : Measurable saw := by unfold saw; fun_prop

lemma measurable_saw2 : Measurable saw2 := by unfold saw2; fun_prop

lemma norm_saw_le (u : ℝ) : ‖saw u‖ ≤ 1 := by
  have h1 : (0 : ℝ) ≤ Int.fract u := Int.fract_nonneg u
  have h2 : Int.fract u < 1 := Int.fract_lt_one u
  have he : saw u = (((Int.fract u - 1 / 2 : ℝ)) : ℂ) := by unfold saw; push_cast; ring
  rw [he, norm_ofReal', abs_le]
  constructor <;> linarith

lemma norm_saw2_le (u : ℝ) : ‖saw2 u‖ ≤ 1 := by
  have h1 : (0 : ℝ) ≤ Int.fract u := Int.fract_nonneg u
  have h2 : Int.fract u < 1 := Int.fract_lt_one u
  have he : saw2 u = ((((Int.fract u) ^ 2 - Int.fract u) / 2 : ℝ) : ℂ) := rfl
  rw [he, norm_ofReal', abs_le]
  constructor <;> nlinarith

/-- Away from the integers the derivative of the quadratic in the fractional part is the
sawtooth. -/
lemma hasDerivAt_G {u : ℝ} (hu : Int.fract u ≠ 0) :
    HasDerivAt (fun x : ℝ => ((Int.fract x) ^ 2 - Int.fract x) / 2) (Int.fract u - 1 / 2) u := by
  set c : ℝ := (⌊u⌋ : ℝ) with hc
  have hle : c ≤ u := by rw [hc]; exact Int.floor_le u
  have hlt : u < c + 1 := by rw [hc]; exact Int.lt_floor_add_one u
  have hne : u ≠ c := by
    rw [hc]; intro h; exact (Int.fract_ne_zero_iff.mp hu) ⟨⌊u⌋, h.symm⟩
  have hlt' : c < u := lt_of_le_of_ne hle hne.symm
  have hfract : Int.fract u = u - c := fract_eq_sub_of_mem_Ioo ⟨hlt', hlt⟩
  have hev : (fun x : ℝ => ((Int.fract x) ^ 2 - Int.fract x) / 2) =ᶠ[𝓝 u]
      (fun x => ((x - c) ^ 2 - (x - c)) / 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hlt', hlt⟩] with x hx
    rw [fract_eq_sub_of_mem_Ioo hx]
  have hpoly : HasDerivAt (fun x : ℝ => ((x - c) ^ 2 - (x - c)) / 2) (Int.fract u - 1 / 2) u := by
    have h1 : HasDerivAt (fun x : ℝ => (x - c) ^ 2) (2 * (u - c)) u := by
      have h : HasDerivAt (fun x : ℝ => x - c) 1 u := (hasDerivAt_id u).sub_const c
      convert! h.pow 2 using 1
      ring
    have h2 : HasDerivAt (fun x : ℝ => x - c) 1 u := (hasDerivAt_id u).sub_const c
    have h3 : HasDerivAt (fun x : ℝ => (x - c) ^ 2 - (x - c)) (2 * (u - c) - 1) u := h1.sub h2
    have h4 : HasDerivAt (fun x : ℝ => ((x - c) ^ 2 - (x - c)) / 2) ((2 * (u - c) - 1) / 2) u :=
      h3.div_const 2
    have heq : (2 * (u - c) - 1) / 2 = Int.fract u - 1 / 2 := by rw [hfract]; ring
    rw [heq] at h4; exact h4
  exact hpoly.congr_of_eventuallyEq hev

lemma hasDerivAt_saw2 {u : ℝ} (hu : Int.fract u ≠ 0) : HasDerivAt saw2 (saw u) u := by
  have h := (hasDerivAt_G hu).ofReal_comp
  have he : (((Int.fract u - 1 / 2 : ℝ)) : ℂ) = saw u := by unfold saw; push_cast; ring
  rw [he] at h
  exact h

lemma saw2_intCast (n : ℤ) : saw2 (n : ℝ) = 0 := by unfold saw2; simp

lemma saw2_natCast (n : ℕ) : saw2 (n : ℝ) = 0 := by unfold saw2; simp

lemma sawF_natCast (s : ℂ) (n : ℕ) : sawF s (n : ℝ) = 0 := by
  unfold sawF; rw [saw2_natCast]; ring

lemma sawF_intCast (s : ℂ) (n : ℤ) : sawF s (n : ℝ) = 0 := by
  unfold sawF; rw [saw2_intCast]; ring

lemma tendsto_saw2_nhdsGT (n : ℤ) : Tendsto saw2 (𝓝[>] (n : ℝ)) (𝓝 0) := by
  have hmem : Set.Ioo (n : ℝ) ((n : ℝ) + 1) ∈ 𝓝[>] (n : ℝ) := by
    refine Filter.inter_mem self_mem_nhdsWithin ?_
    exact nhdsWithin_le_nhds (Iio_mem_nhds (by linarith : (n : ℝ) < (n : ℝ) + 1))
  have hev : saw2 =ᶠ[𝓝[>] (n : ℝ)]
      (fun u : ℝ => ((((u - n) ^ 2 - (u - n)) / 2 : ℝ) : ℂ)) := by
    filter_upwards [hmem] with u hu
    unfold saw2
    rw [fract_eq_sub_of_mem_Ioo hu]
  have hpoly : Tendsto (fun u : ℝ => ((((u - (n : ℝ)) ^ 2 - (u - (n : ℝ))) / 2 : ℝ) : ℂ))
      (𝓝[>] (n : ℝ)) (𝓝 0) := by
    have hc : Continuous (fun u : ℝ => ((((u - (n : ℝ)) ^ 2 - (u - (n : ℝ))) / 2 : ℝ) : ℂ)) := by
      fun_prop
    have ht : Tendsto (fun u : ℝ => ((((u - (n : ℝ)) ^ 2 - (u - (n : ℝ))) / 2 : ℝ) : ℂ))
        (𝓝 (n : ℝ)) (𝓝 0) := by simpa using hc.tendsto (n : ℝ)
    exact ht.mono_left nhdsWithin_le_nhds
  exact Tendsto.congr' hev.symm hpoly

lemma tendsto_saw2_nhdsLT (n : ℤ) : Tendsto saw2 (𝓝[<] (n : ℝ)) (𝓝 0) := by
  have hmem : Set.Ioo ((n : ℝ) - 1) (n : ℝ) ∈ 𝓝[<] (n : ℝ) := by
    refine Filter.inter_mem ?_ self_mem_nhdsWithin
    exact nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith : (n : ℝ) - 1 < (n : ℝ)))
  have hev : saw2 =ᶠ[𝓝[<] (n : ℝ)]
      (fun u : ℝ => ((((u - (((n - 1 : ℤ)) : ℝ)) ^ 2 - (u - (((n - 1 : ℤ)) : ℝ))) / 2 : ℝ) : ℂ)) := by
    filter_upwards [hmem] with u hu
    unfold saw2
    have hu' : u ∈ Set.Ioo ((((n - 1 : ℤ)) : ℝ)) (((((n - 1 : ℤ)) : ℝ)) + 1) := by
      have h1 : (((n - 1 : ℤ)) : ℝ) = (n : ℝ) - 1 := by push_cast; ring
      rw [h1]; exact ⟨hu.1, by linarith [hu.2]⟩
    rw [fract_eq_sub_of_mem_Ioo hu']
  have hpoly : Tendsto
      (fun u : ℝ => ((((u - (((n - 1 : ℤ)) : ℝ)) ^ 2 - (u - (((n - 1 : ℤ)) : ℝ))) / 2 : ℝ) : ℂ))
      (𝓝[<] (n : ℝ)) (𝓝 0) := by
    have hc : Continuous
        (fun u : ℝ => ((((u - (((n - 1 : ℤ)) : ℝ)) ^ 2 - (u - (((n - 1 : ℤ)) : ℝ))) / 2 : ℝ) : ℂ)) := by
      fun_prop
    have ht : Tendsto
        (fun u : ℝ => ((((u - (((n - 1 : ℤ)) : ℝ)) ^ 2 - (u - (((n - 1 : ℤ)) : ℝ))) / 2 : ℝ) : ℂ))
        (𝓝 (n : ℝ)) (𝓝 0) := by
      have hmain := hc.tendsto (n : ℝ)
      have hval : (((((n : ℝ) - (((n - 1 : ℤ)) : ℝ)) ^ 2 - ((n : ℝ) - (((n - 1 : ℤ)) : ℝ))) / 2 : ℝ) : ℂ)
          = 0 := by
        have : (n : ℝ) - (((n - 1 : ℤ)) : ℝ) = 1 := by push_cast; ring
        rw [this]; norm_num
      rw [hval] at hmain; exact hmain
    exact ht.mono_left nhdsWithin_le_nhds
  exact Tendsto.congr' hev.symm hpoly

lemma tendsto_sawF_nhdsGT {s : ℂ} (n : ℤ) (hn : 1 ≤ n) :
    Tendsto (sawF s) (𝓝[>] (n : ℝ)) (𝓝 0) := by
  change Tendsto (fun u : ℝ => saw2 u * (u : ℂ) ^ (-s - 1)) (𝓝[>] (n : ℝ)) (𝓝 0)
  have h1 := tendsto_saw2_nhdsGT n
  have hne : (n : ℝ) ≠ 0 := by
    have : (0 : ℤ) < n := by omega
    exact_mod_cast (ne_of_gt this)
  have hc : Tendsto (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (𝓝 (n : ℝ)) (𝓝 ((n : ℂ) ^ (-s - 1))) :=
    (Complex.continuousAt_ofReal_cpow_const (n : ℝ) (-s - 1) (Or.inr hne)).tendsto
  have h2 : Tendsto (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (𝓝[>] (n : ℝ)) (𝓝 ((n : ℂ) ^ (-s - 1))) :=
    hc.mono_left nhdsWithin_le_nhds
  simpa using h1.mul h2

lemma tendsto_sawF_nhdsLT {s : ℂ} (n : ℤ) (hn : 1 ≤ n) :
    Tendsto (sawF s) (𝓝[<] (n : ℝ)) (𝓝 0) := by
  change Tendsto (fun u : ℝ => saw2 u * (u : ℂ) ^ (-s - 1)) (𝓝[<] (n : ℝ)) (𝓝 0)
  have h1 := tendsto_saw2_nhdsLT n
  have hne : (n : ℝ) ≠ 0 := by
    have : (0 : ℤ) < n := by omega
    exact_mod_cast (ne_of_gt this)
  have hc : Tendsto (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (𝓝 (n : ℝ)) (𝓝 ((n : ℂ) ^ (-s - 1))) :=
    (Complex.continuousAt_ofReal_cpow_const (n : ℝ) (-s - 1) (Or.inr hne)).tendsto
  have h2 : Tendsto (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (𝓝[<] (n : ℝ)) (𝓝 ((n : ℂ) ^ (-s - 1))) :=
    hc.mono_left nhdsWithin_le_nhds
  simpa using h1.mul h2

lemma hasDerivAt_sawF {s : ℂ} (hs : 0 < s.re) {u : ℝ}
    (hu : Int.fract u ≠ 0) (hpos : 0 < u) : HasDerivAt (sawF s) (sawH s u) u := by
  have h1 : HasDerivAt saw2 (saw u) u := hasDerivAt_saw2 hu
  have hr : -s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s - 1)) ((-s - 1) * (u : ℂ) ^ (-s - 2)) u := by
    have h := hasDerivAt_ofReal_cpow_const (ne_of_gt hpos) hr
    have he : (-s - 1) - 1 = -s - 2 := by ring
    rw [he] at h; exact h
  change HasDerivAt (fun x : ℝ => saw2 x * (x : ℂ) ^ (-s - 1)) (sawH s u) u
  have hmul := h1.mul h2
  convert! hmul using 1
  · unfold sawH; ring

lemma integrableOn_sawH {s : ℂ} (hs : 0 < s.re) (N : ℕ) (hN : 1 ≤ N) :
    IntegrableOn (sawH s) (Set.Ioi (N : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h1 : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Set.Ioi (N : ℝ)) := by
    refine integrableOn_Ioi_cpow_of_lt ?_ hNpos
    have : (-s - 1).re = -s.re - 1 := by simp
    linarith [hs]
  have h2 : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 2)) (Set.Ioi (N : ℝ)) := by
    refine integrableOn_Ioi_cpow_of_lt ?_ hNpos
    have : (-s - 2).re = -s.re - 2 := by simp
    linarith [hs]
  have hi1 : IntegrableOn (fun u => saw u * (u : ℂ) ^ (-s - 1)) (Set.Ioi (N : ℝ)) :=
    h1.bdd_mul (measurable_saw.aestronglyMeasurable) (Filter.Eventually.of_forall norm_saw_le)
  have hi2 : IntegrableOn (fun u => saw2 u * (u : ℂ) ^ (-s - 2)) (Set.Ioi (N : ℝ)) :=
    h2.bdd_mul (measurable_saw2.aestronglyMeasurable) (Filter.Eventually.of_forall norm_saw2_le)
  unfold sawH
  exact hi1.sub (hi2.const_mul (s + 1))

theorem sawtIbp {s : ℂ} (hs : 0 < s.re) (N : ℕ) (hN : 1 ≤ N) :
    ∫ u in Set.Ioi (N : ℝ), (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-s - 1)
      = (s + 1) * ∫ u in Set.Ioi (N : ℝ),
          ((((Int.fract u) ^ 2 - Int.fract u) / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2) := by
  change ∫ u in Set.Ioi (N : ℝ), saw u * (u : ℂ) ^ (-s - 1)
      = (s + 1) * ∫ u in Set.Ioi (N : ℝ), saw2 u * (u : ℂ) ^ (-s - 2)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcp1 : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Set.Ioi (N : ℝ)) := by
    refine integrableOn_Ioi_cpow_of_lt ?_ hNpos
    have : (-s - 1).re = -s.re - 1 := by simp
    linarith [hs]
  have hcp2 : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 2)) (Set.Ioi (N : ℝ)) := by
    refine integrableOn_Ioi_cpow_of_lt ?_ hNpos
    have : (-s - 2).re = -s.re - 2 := by simp
    linarith [hs]
  have hi1 : IntegrableOn (fun u => saw u * (u : ℂ) ^ (-s - 1)) (Set.Ioi (N : ℝ)) :=
    hcp1.bdd_mul (measurable_saw.aestronglyMeasurable) (Filter.Eventually.of_forall norm_saw_le)
  have hi2 : IntegrableOn (fun u => saw2 u * (u : ℂ) ^ (-s - 2)) (Set.Ioi (N : ℝ)) :=
    hcp2.bdd_mul (measurable_saw2.aestronglyMeasurable) (Filter.Eventually.of_forall norm_saw2_le)
  have hIoi : IntegrableOn (sawH s) (Set.Ioi (N : ℝ)) := integrableOn_sawH hs N hN
  have hIci : IntegrableOn (sawH s) (Set.Ici (N : ℝ)) :=
    hIoi.congr_set_ae MeasureTheory.Ioi_ae_eq_Ici.symm
  have hIntCf : ∀ a b : ℝ, (N : ℝ) ≤ a → (N : ℝ) ≤ b →
      IntervalIntegrable (sawH s) volume a b := by
    intro a b ha hb
    rw [intervalIntegrable_iff]
    exact hIci.mono_set (by
      intro x hx
      rw [Set.mem_uIoc] at hx
      rcases hx with hx | hx
      · exact le_trans ha hx.1.le
      · exact le_trans hb hx.1.le)
  -- the per-interval fundamental theorem of calculus
  have hper : ∀ n : ℤ, 1 ≤ n → (N : ℤ) ≤ n →
      ∫ u in (n : ℝ)..((n : ℝ) + 1), sawH s u = 0 := by
    intro n hn hnN
    have hnl : (n : ℝ) < (n : ℝ) + 1 := by linarith
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
    have hderiv : ∀ x ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1), HasDerivAt (sawF s) (sawH s x) x := by
      intro x hx
      have hxpos : 0 < x := by linarith [hx.1]
      have hxne : Int.fract x ≠ 0 := by
        intro hfx
        obtain ⟨k, hk⟩ := Int.fract_eq_zero_iff.mp hfx
        rw [← hk] at hx
        have h1 : n < k := by exact_mod_cast hx.1
        have h2 : k < n + 1 := by exact_mod_cast hx.2
        omega
      exact hasDerivAt_sawF hs hxne hxpos
    have hint : IntervalIntegrable (sawH s) volume (n : ℝ) ((n : ℝ) + 1) :=
      hIntCf _ _ hNn (by linarith)
    have ha : Tendsto (sawF s) (𝓝[>] (n : ℝ)) (𝓝 (sawF s (n : ℝ))) := by
      rw [sawF_intCast]
      simpa using tendsto_sawF_nhdsGT n hn
    have hb : Tendsto (sawF s) (𝓝[<] ((n : ℝ) + 1)) (𝓝 (sawF s ((n : ℝ) + 1))) := by
      have he : ((n : ℝ) + 1) = ((n + 1 : ℤ) : ℝ) := by push_cast; ring
      rw [he, sawF_intCast]
      simpa using tendsto_sawF_nhdsLT (n + 1) (by omega)
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hnl hderiv hint ha hb
    rw [h]
    have e1 : sawF s ((n : ℝ) + 1) = 0 := by
      rw [show ((n : ℝ) + 1) = ((n + 1 : ℤ) : ℝ) by push_cast; ring, sawF_intCast]
    rw [e1, sawF_intCast, sub_zero]
  -- telescope over the unit intervals
  have hstep : ∀ m : ℕ, ∫ u in (N : ℝ)..((N : ℝ) + (m : ℝ)), sawH s u = 0 := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      have he : (N : ℝ) + ((k + 1 : ℕ) : ℝ) = ((N : ℝ) + (k : ℝ)) + 1 := by push_cast; ring
      rw [he, ← intervalIntegral.integral_add_adjacent_intervals
        (hIntCf (N : ℝ) ((N : ℝ) + k) le_rfl (by have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith))
        (hIntCf ((N : ℝ) + k) (((N : ℝ) + k) + 1)
          (by have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith)
          (by have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith))]
      rw [ih, zero_add]
      have hperk := hper ((N : ℤ) + k) (by omega) (by omega)
      simpa using hperk
  have hlim := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (μ := volume) (N : ℝ) hIoi
    (b := fun m : ℕ => (N : ℝ) + (m : ℝ))
    (by simpa only [add_comm] using
      tendsto_atTop_add_const_right atTop (N : ℝ) tendsto_natCast_atTop_atTop)
  have hconst : Tendsto (fun m : ℕ => ∫ u in (N : ℝ)..((N : ℝ) + (m : ℝ)), sawH s u) atTop (𝓝 0) :=
    Tendsto.congr' (Filter.Eventually.of_forall (fun m => (hstep m).symm)) tendsto_const_nhds
  have h0 : ∫ u in Set.Ioi (N : ℝ), sawH s u = 0 := tendsto_nhds_unique hlim hconst
  have hH : ∫ u in Set.Ioi (N : ℝ), sawH s u
      = (∫ u in Set.Ioi (N : ℝ), saw u * (u : ℂ) ^ (-s - 1))
        - (s + 1) * ∫ u in Set.Ioi (N : ℝ), saw2 u * (u : ℂ) ^ (-s - 2) := by
    rw [show (∫ u in Set.Ioi (N : ℝ), sawH s u)
        = ∫ u in Set.Ioi (N : ℝ),
            (saw u * (u : ℂ) ^ (-s - 1) - (s + 1) * (saw2 u * (u : ℂ) ^ (-s - 2))) by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      unfold sawH; ring]
    rw [MeasureTheory.integral_sub hi1 (hi2.const_mul (s + 1)), MeasureTheory.integral_const_mul]
  rw [hH, sub_eq_zero] at h0
  exact h0

end

end Work.ZeroDensity.Zeta.Balanced
