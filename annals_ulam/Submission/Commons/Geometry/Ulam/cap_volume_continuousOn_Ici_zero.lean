import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod

namespace Commons.Geometry.Ulam

open Set Filter MeasureTheory
open scoped Topology Interval

/-! ### A measurability lemma for interval integrals with measurable moving endpoints -/

lemma aeStronglyMeasurable_intervalIntegral_param
    {L U : ℝ → ℝ} (hL : Measurable L) (hU : Measurable U)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) :
    AEStronglyMeasurable (fun t => ∫ z in L t..U t, g t z) volume := by
  let S1 : Set (ℝ × ℝ) := {p | p.2 ∈ Ioc (L p.1) (U p.1)}
  let S2 : Set (ℝ × ℝ) := {p | p.2 ∈ Ioc (U p.1) (L p.1)}
  have hS1eq : S1 = {p : ℝ × ℝ | L p.1 < p.2 ∧ p.2 ≤ U p.1} := by
    ext p; simp [S1, mem_Ioc]
  have hS2eq : S2 = {p : ℝ × ℝ | U p.1 < p.2 ∧ p.2 ≤ L p.1} := by
    ext p; simp [S2, mem_Ioc]
  have hS1 : MeasurableSet S1 := by
    rw [hS1eq]
    exact (measurableSet_lt (hL.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hU.comp measurable_fst))
  have hS2 : MeasurableSet S2 := by
    rw [hS2eq]
    exact (measurableSet_lt (hU.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hL.comp measurable_fst))
  have h1 : AEStronglyMeasurable
      (fun t => ∫ z, S1.indicator (Function.uncurry g) (t, z)) volume := by
    exact ((hg.indicator hS1).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable)
  have h2 : AEStronglyMeasurable
      (fun t => ∫ z, S2.indicator (Function.uncurry g) (t, z)) volume := by
    exact ((hg.indicator hS2).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable)
  have h_eq :
      (fun t =>
          (∫ z, S1.indicator (Function.uncurry g) (t, z)) -
            ∫ z, S2.indicator (Function.uncurry g) (t, z)) =
        fun t => ∫ z in L t..U t, g t z := by
    funext t
    rw [intervalIntegral]
    have hleft : (∫ z, S1.indicator (Function.uncurry g) (t, z)) =
        ∫ z, (Ioc (L t) (U t)).indicator (g t) z := by
      apply integral_congr_ae
      filter_upwards [] with z
      by_cases hz : z ∈ Ioc (L t) (U t)
      · have hcond : L t < z ∧ z ≤ U t := by simpa [mem_Ioc] using hz
        simp [S1, hcond]
      · have hcond : ¬ (L t < z ∧ z ≤ U t) := by simpa [mem_Ioc] using hz
        simp [S1, hcond]
    have hright : (∫ z, S2.indicator (Function.uncurry g) (t, z)) =
        ∫ z, (Ioc (U t) (L t)).indicator (g t) z := by
      apply integral_congr_ae
      filter_upwards [] with z
      by_cases hz : z ∈ Ioc (U t) (L t)
      · have hcond : U t < z ∧ z ≤ L t := by simpa [mem_Ioc] using hz
        simp [S2, hcond]
      · have hcond : ¬ (U t < z ∧ z ≤ L t) := by simpa [mem_Ioc] using hz
        simp [S2, hcond]
    rw [hleft, hright]
    rw [← integral_indicator (μ := volume) (s := Ioc (L t) (U t)) (f := g t)
      measurableSet_Ioc]
    rw [← integral_indicator (μ := volume) (s := Ioc (U t) (L t)) (f := g t)
      measurableSet_Ioc]
  exact (h1.sub h2).congr (Eventually.of_forall (congrFun h_eq))

/-! ### Continuity of a primitive with continuous integrand -/

lemma continuousOn_intervalIntegral_primitive_const_lower
    {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b)) :
    ContinuousOn (fun u => ∫ z in a..u, g z) (Icc a b) := by
  intro u hu
  have h_int : IntervalIntegrable g volume a b :=
    hg.intervalIntegrable_of_Icc hab
  have h := intervalIntegral.continuousWithinAt_primitive (μ := volume) (f := g) (a := a)
      (b₁ := a) (b₂ := b) (b₀ := u) (measure_singleton u) ?_
  · simpa [hab, min_eq_left hab, max_eq_right hab] using h
  · simpa [hab, min_eq_left hab, max_eq_right hab] using h_int

/-! ### Continuity of the clamp function -/

lemma continuousOn_clamp_affine {t a b : ℝ} (_hab : a ≤ b)
    {h : ℝ → ℝ} (hh : ContinuousOn h (Set.Ici 0)) :
    ContinuousOn (fun r : ℝ => max a (min b (r * t + h r))) (Set.Ici 0) := by
  fun_prop

lemma mapsTo_clamp_affine_Icc {t a b : ℝ} (hab : a ≤ b)
    {h : ℝ → ℝ} :
    MapsTo (fun r : ℝ => max a (min b (r * t + h r))) (Set.Ici 0) (Set.Icc a b) := by
  intro r _hr
  rw [Set.mem_Icc]
  constructor
  · exact le_max_left _ _
  · exact max_le hab (min_le_left _ _)

/-! ### Pointwise continuity of the inner cap integral -/

lemma continuousOn_cap_slice_integral {n : ℕ} {t : ℝ} {f h : ℝ → ℝ}
    (_ht : t ∈ Set.Icc (-1 : ℝ) 1) (hft_nonneg : 0 ≤ f t)
    (hh : ContinuousOn h (Set.Ici 0)) :
    ContinuousOn
      (fun r : ℝ =>
        ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
          (f t ^ 2 - z ^ 2) ^ (n - 1))
      (Set.Ici 0) := by
  let a : ℝ := -f t
  let b : ℝ := f t
  let u : ℝ → ℝ := fun r => max a (min b (r * t + h r))
  let g : ℝ → ℝ := fun z => (f t ^ 2 - z ^ 2) ^ (n - 1)
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith
  have hg_cont : ContinuousOn g (Icc a b) := by
    dsimp [g]
    fun_prop
  have hu_cont : ContinuousOn u (Set.Ici 0) := by
    dsimp [u, a, b]
    exact continuousOn_clamp_affine hab hh
  have hu_mem : MapsTo u (Set.Ici 0) (Set.Icc a b) := by
    dsimp [u, a, b]
    exact mapsTo_clamp_affine_Icc hab
  have hP_cont : ContinuousOn (fun y => ∫ z in a..y, g z) (Icc a b) :=
    continuousOn_intervalIntegral_primitive_const_lower hab hg_cont
  exact hP_cont.comp hu_cont hu_mem

/-! ### A uniform bound for the inner cap integral -/

lemma norm_cap_slice_integral_le {n : ℕ} {f h : ℝ → ℝ} {M : ℝ}
    (hf_le_M : ∀ t ∈ Set.Icc (-1 : ℝ) 1, f t ≤ M)
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t) :
    ∀ r : ℝ, ∀ᵐ t ∂volume, t ∈ Ι (-1 : ℝ) 1 →
      ‖(∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
          (f t ^ 2 - z ^ 2) ^ (n - 1))‖ ≤
        (2 * M) * (2 * M ^ 2) ^ (n - 1) := by
  intro r
  filter_upwards [] with t ht
  have htIoc : t ∈ Ioc (-1 : ℝ) 1 := by
    simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
  have htcc : t ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioc_subset_Icc_self htIoc
  have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
  have hft_le : f t ≤ M := hf_le_M t htcc
  let a : ℝ := -f t
  let b : ℝ := f t
  let U : ℝ := max a (min b (r * t + h r))
  let g : ℝ → ℝ := fun z => (f t ^ 2 - z ^ 2) ^ (n - 1)
  have ha_le_b : a ≤ b := by dsimp [a, b]; linarith
  have hU_mem : U ∈ Set.Icc a b := by
    dsimp [U]
    rw [Set.mem_Icc]
    constructor
    · exact le_max_left _ _
    · exact max_le ha_le_b (min_le_left _ _)
  have hUa : a ≤ U := hU_mem.1
  have hUb : U ≤ b := hU_mem.2
  have hg_bound : ∀ z ∈ Ι a U, ‖g z‖ ≤ (2 * M ^ 2) ^ (n - 1) := by
    intro z hz
    have hzIoc : z ∈ Ioc a U := by
      simpa [Set.uIoc_of_le hUa] using hz
    have hz_lower : -M ≤ z := by
      have ha_lower : -M ≤ a := by dsimp [a]; linarith
      exact le_trans ha_lower (le_of_lt hzIoc.1)
    have hz_upper : z ≤ M := by
      have hb_upper : b ≤ M := by dsimp [b]; linarith
      exact le_trans (le_trans hzIoc.2 hUb) hb_upper
    have hz_abs : |z| ≤ M := abs_le.mpr ⟨hz_lower, hz_upper⟩
    have hsq_le : |f t ^ 2 - z ^ 2| ≤ 2 * M ^ 2 := by
      have h1 : |f t ^ 2 - z ^ 2| ≤ f t ^ 2 + z ^ 2 := by
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg (f t), sq_nonneg z]
      have hftsq : f t ^ 2 ≤ M ^ 2 := by
        exact pow_le_pow_left₀ hft_nonneg hft_le 2
      have hzsq : z ^ 2 ≤ M ^ 2 := by
        calc z ^ 2 = |z| ^ 2 := by simp [sq_abs]
          _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg z) hz_abs 2
      have hsum : f t ^ 2 + z ^ 2 ≤ 2 * M ^ 2 := by nlinarith
      exact le_trans h1 hsum
    have hpow : |(f t ^ 2 - z ^ 2) ^ (n - 1)| ≤ (2 * M ^ 2) ^ (n - 1) := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hsq_le (n - 1)
    dsimp [g]
    simpa [Real.norm_eq_abs] using hpow
  have hlen : |U - a| ≤ 2 * M := by
    rw [abs_of_nonneg (sub_nonneg.mpr hUa)]
    calc U - a ≤ b - a := sub_le_sub hUb le_rfl
      _ = 2 * f t := by dsimp [a, b]; ring
      _ ≤ 2 * M := mul_le_mul_of_nonneg_left hft_le (by norm_num)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := U)
      (C := (2 * M ^ 2) ^ (n - 1)) (f := g) hg_bound
  calc ‖∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
        (f t ^ 2 - z ^ 2) ^ (n - 1)‖
      = ‖∫ z in a..U, g z‖ := by simp [a, b, U, g]
    _ ≤ (2 * M ^ 2) ^ (n - 1) * |U - a| := hnorm
    _ ≤ (2 * M ^ 2) ^ (n - 1) * (2 * M) := by
        exact mul_le_mul_of_nonneg_left hlen (pow_nonneg (by nlinarith [sq_nonneg M]) _)
    _ = (2 * M) * (2 * M ^ 2) ^ (n - 1) := by ring

/-! ### The requested continuity -/

lemma cap_volume_continuousOn_Ici_zero {n : ℕ} {f h : ℝ → ℝ}
    (hn : 1 ≤ n)
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    (hf_meas : Measurable f)
    (hf_bdd : Bornology.IsBounded (f '' Set.Icc (-1 : ℝ) 1))
    (hh_cont : ContinuousOn h (Set.Ici 0)) :
    ContinuousOn
      (fun r : ℝ =>
        ∫ t in (-1 : ℝ)..1,
          ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
            (f t ^ 2 - z ^ 2) ^ (n - 1))
      (Set.Ici 0) := by
  rcases hf_bdd.exists_pos_norm_le with ⟨M, hMpos, hM⟩
  have _hn_pos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hf_abs_le : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |f t| ≤ M := by
    intro t ht
    exact hM (f t) ⟨t, ht, rfl⟩
  have hf_le_M : ∀ t ∈ Set.Icc (-1 : ℝ) 1, f t ≤ M := by
    intro t ht
    have hnonneg : 0 ≤ f t := hf_nonneg t ht
    simpa [abs_of_nonneg hnonneg] using hf_abs_le t ht
  let B : ℝ := (2 * M) * (2 * M ^ 2) ^ (n - 1)
  have hF_meas : ∀ r : ℝ,
      AEStronglyMeasurable
        (fun t : ℝ =>
          ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
            (f t ^ 2 - z ^ 2) ^ (n - 1))
        (volume.restrict (Ι (-1 : ℝ) 1)) := by
    intro r
    have hL : Measurable (fun t : ℝ => -f t) := by fun_prop
    have hU : Measurable (fun t : ℝ => max (-f t) (min (f t) (r * t + h r))) := by
      fun_prop
    have hg : Measurable (Function.uncurry (fun t z : ℝ => (f t ^ 2 - z ^ 2) ^ (n - 1))) := by
      fun_prop
    exact (aeStronglyMeasurable_intervalIntegral_param hL hU hg).restrict
  have h_bound_all : ∀ r : ℝ, ∀ᵐ t ∂volume, t ∈ Ι (-1 : ℝ) 1 →
      ‖(∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
          (f t ^ 2 - z ^ 2) ^ (n - 1))‖ ≤ B := by
    intro r
    have := norm_cap_slice_integral_le (n := n) (f := f) (h := h) (M := M)
      hf_le_M hf_nonneg r
    simpa [B] using this
  intro r0 hr0
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (F := fun r t =>
      ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
        (f t ^ 2 - z ^ 2) ^ (n - 1))
    (bound := fun _ => B) (s := Set.Ici 0) (x₀ := r0) (a := -1) (b := 1)
    ?_ ?_ ?_ ?_
  · exact Eventually.of_forall hF_meas
  · exact Eventually.of_forall h_bound_all
  · exact intervalIntegrable_const
  · filter_upwards [] with t ht
    have htIoc : t ∈ Ioc (-1 : ℝ) 1 := by
      simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    have htcc : t ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioc_subset_Icc_self htIoc
    have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
    exact (continuousOn_cap_slice_integral (n := n) (f := f) (h := h) htcc hft_nonneg
      hh_cont).continuousWithinAt hr0

end Commons.Geometry.Ulam