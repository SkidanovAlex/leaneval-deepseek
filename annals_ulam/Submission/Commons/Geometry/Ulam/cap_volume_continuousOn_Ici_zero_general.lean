import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib
import Submission.Commons.Geometry.Ulam.cap_volume_continuousOn_Ici_zero

namespace Commons.Geometry.Ulam

open Set Filter MeasureTheory
open scoped Topology Interval

/-! ### Pointwise continuity of the inner cap integral (general interval) -/

private lemma continuousOn_cap_slice_integral_general {n : ℕ} {t a b : ℝ} {f h : ℝ → ℝ}
    (_ht : t ∈ Set.Icc a b) (hft_nonneg : 0 ≤ f t)
    (hh : ContinuousOn h (Set.Ici 0)) :
    ContinuousOn
      (fun r : ℝ =>
        ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
          (f t ^ 2 - z ^ 2) ^ (n - 1))
      (Set.Ici 0) := by
  let c : ℝ := -f t
  let d : ℝ := f t
  let u : ℝ → ℝ := fun r => max c (min d (r * t + h r))
  let g : ℝ → ℝ := fun z => (f t ^ 2 - z ^ 2) ^ (n - 1)
  have hcd : c ≤ d := by
    dsimp [c, d]
    linarith
  have hg_cont : ContinuousOn g (Icc c d) := by
    dsimp [g]
    fun_prop
  have hu_cont : ContinuousOn u (Set.Ici 0) := by
    dsimp [u, c, d]
    exact continuousOn_clamp_affine hcd hh
  have hu_mem : MapsTo u (Set.Ici 0) (Set.Icc c d) := by
    dsimp [u, c, d]
    exact mapsTo_clamp_affine_Icc hcd
  have hP_cont : ContinuousOn (fun y => ∫ z in c..y, g z) (Icc c d) :=
    continuousOn_intervalIntegral_primitive_const_lower hcd hg_cont
  exact hP_cont.comp hu_cont hu_mem

/-! ### A uniform bound for the inner cap integral (general interval) -/

private lemma norm_cap_slice_integral_le_general {n : ℕ} {f h : ℝ → ℝ} {M a b : ℝ}
    (hab : a ≤ b)
    (hf_le_M : ∀ t ∈ Set.Icc a b, f t ≤ M)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t) :
    ∀ r : ℝ, ∀ᵐ t ∂volume, t ∈ Ι a b →
      ‖(∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
          (f t ^ 2 - z ^ 2) ^ (n - 1))‖ ≤
        (2 * M) * (2 * M ^ 2) ^ (n - 1) := by
  intro r
  filter_upwards [] with t ht
  have htIoc : t ∈ Ioc a b := by
    simpa [Set.uIoc_of_le hab] using ht
  have htcc : t ∈ Set.Icc a b := Set.Ioc_subset_Icc_self htIoc
  have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
  have hft_le : f t ≤ M := hf_le_M t htcc
  let c : ℝ := -f t
  let d : ℝ := f t
  let U : ℝ := max c (min d (r * t + h r))
  let g : ℝ → ℝ := fun z => (f t ^ 2 - z ^ 2) ^ (n - 1)
  have hc_le_d : c ≤ d := by dsimp [c, d]; linarith
  have hU_mem : U ∈ Set.Icc c d := by
    dsimp [U]
    rw [Set.mem_Icc]
    constructor
    · exact le_max_left _ _
    · exact max_le hc_le_d (min_le_left _ _)
  have hUc : c ≤ U := hU_mem.1
  have hUd : U ≤ d := hU_mem.2
  have hg_bound : ∀ z ∈ Ι c U, ‖g z‖ ≤ (2 * M ^ 2) ^ (n - 1) := by
    intro z hz
    have hzIoc : z ∈ Ioc c U := by
      simpa [Set.uIoc_of_le hUc] using hz
    have hz_lower : -M ≤ z := by
      have hc_lower : -M ≤ c := by dsimp [c]; linarith
      exact le_trans hc_lower (le_of_lt hzIoc.1)
    have hz_upper : z ≤ M := by
      have hd_upper : d ≤ M := by dsimp [d]; linarith
      exact le_trans (le_trans hzIoc.2 hUd) hd_upper
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
  have hlen : |U - c| ≤ 2 * M := by
    rw [abs_of_nonneg (sub_nonneg.mpr hUc)]
    calc U - c ≤ d - c := sub_le_sub hUd le_rfl
      _ = 2 * f t := by dsimp [c, d]; ring
      _ ≤ 2 * M := mul_le_mul_of_nonneg_left hft_le (by norm_num)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := U)
      (C := (2 * M ^ 2) ^ (n - 1)) (f := g) hg_bound
  calc ‖∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
        (f t ^ 2 - z ^ 2) ^ (n - 1)‖
      = ‖∫ z in c..U, g z‖ := by simp [c, d, U, g]
    _ ≤ (2 * M ^ 2) ^ (n - 1) * |U - c| := hnorm
    _ ≤ (2 * M ^ 2) ^ (n - 1) * (2 * M) := by
        exact mul_le_mul_of_nonneg_left hlen (pow_nonneg (by nlinarith [sq_nonneg M]) _)
    _ = (2 * M) * (2 * M ^ 2) ^ (n - 1) := by ring

/-! ### The requested continuity on a general interval -/

lemma cap_volume_continuousOn_Ici_zero_general {n : ℕ} {f h : ℝ → ℝ} {a b : ℝ}
    (hn : 1 ≤ n) (hab : a ≤ b)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t)
    (hf_meas : Measurable f)
    (hf_bdd : Bornology.IsBounded (f '' Set.Icc a b))
    (hh_cont : ContinuousOn h (Set.Ici 0)) :
    ContinuousOn
      (fun r : ℝ =>
        ∫ t in a..b,
          ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
            (f t ^ 2 - z ^ 2) ^ (n - 1))
      (Set.Ici 0) := by
  rcases hf_bdd.exists_pos_norm_le with ⟨M, hMpos, hM⟩
  have _hn_pos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hf_abs_le : ∀ t ∈ Set.Icc a b, |f t| ≤ M := by
    intro t ht
    exact hM (f t) ⟨t, ht, rfl⟩
  have hf_le_M : ∀ t ∈ Set.Icc a b, f t ≤ M := by
    intro t ht
    have hnonneg : 0 ≤ f t := hf_nonneg t ht
    simpa [abs_of_nonneg hnonneg] using hf_abs_le t ht
  let B : ℝ := (2 * M) * (2 * M ^ 2) ^ (n - 1)
  have hF_meas : ∀ r : ℝ,
      AEStronglyMeasurable
        (fun t : ℝ =>
          ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
            (f t ^ 2 - z ^ 2) ^ (n - 1))
        (volume.restrict (Ι a b)) := by
    intro r
    have hL : Measurable (fun t : ℝ => -f t) := by fun_prop
    have hU : Measurable (fun t : ℝ => max (-f t) (min (f t) (r * t + h r))) := by
      fun_prop
    have hg : Measurable (Function.uncurry (fun t z : ℝ => (f t ^ 2 - z ^ 2) ^ (n - 1))) := by
      fun_prop
    exact (aeStronglyMeasurable_intervalIntegral_param hL hU hg).restrict
  have h_bound_all : ∀ r : ℝ, ∀ᵐ t ∂volume, t ∈ Ι a b →
      ‖(∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
          (f t ^ 2 - z ^ 2) ^ (n - 1))‖ ≤ B := by
    intro r
    have := norm_cap_slice_integral_le_general (n := n) (f := f) (h := h) (M := M)
      hab hf_le_M hf_nonneg r
    simpa [B] using this
  intro r0 hr0
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (F := fun r t =>
      ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))),
        (f t ^ 2 - z ^ 2) ^ (n - 1))
    (bound := fun _ => B) (s := Set.Ici 0) (x₀ := r0) (a := a) (b := b)
    ?_ ?_ ?_ ?_
  · exact Eventually.of_forall hF_meas
  · exact Eventually.of_forall h_bound_all
  · exact intervalIntegrable_const
  · filter_upwards [] with t ht
    have htIoc : t ∈ Ioc a b := by
      simpa [Set.uIoc_of_le hab] using ht
    have htcc : t ∈ Set.Icc a b := Set.Ioc_subset_Icc_self htIoc
    have hft_nonneg : 0 ≤ f t := hf_nonneg t htcc
    exact (continuousOn_cap_slice_integral_general (n := n) (f := f) (h := h) htcc hft_nonneg
      hh_cont).continuousWithinAt hr0

end Commons.Geometry.Ulam
