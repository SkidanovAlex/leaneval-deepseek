import Mathlib
import Submission.Commons.Analysis.Integral.integrableOn_abs_sub_rpow_Icc

namespace Commons.Analysis.Integral

open MeasureTheory Set Real
open scoped Topology

/-- For `x ≥ 0`, `(√x)⁻¹ = x^(-1/2)`. -/
private lemma inv_sqrt_eq_rpow_neg_half' {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹ = x ^ (-(1:ℝ)/2) := by
  rw [show (-(1:ℝ)/2) = -(1/2) by norm_num]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx]

/-- If `f` grows at least at linear rate `m` on `[a,b]` and vanishes at `c`, then
`m * |x - c| ≤ |f x|` on `[a,b]`. -/
private lemma abs_le_abs_of_slope_ge' {f : ℝ → ℝ} {m a b c x : ℝ}
    (hslope : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v → m * (v - u) ≤ f v - f u)
    (hc : c ∈ Icc a b) (hfc : f c = 0) (hx : x ∈ Icc a b) :
    m * |x - c| ≤ |f x| := by
  rcases le_total x c with h | h
  · have hsl := hslope x hx c hc h
    have h1 : m * (c - x) ≤ |f x| := by
      calc m * (c - x) ≤ f c - f x := hsl
        _ = - f x := by rw [hfc]; ring
        _ ≤ |f x| := neg_le_abs (f x)
    rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    exact h1
  · have hsl := hslope c hc x hx h
    have h1 : m * (x - c) ≤ |f x| := by
      calc m * (x - c) ≤ f x - f c := hsl
        _ = f x := by rw [hfc]; ring
        _ ≤ |f x| := le_abs_self (f x)
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact h1

/-- The pointwise comparison bound for the parabolic-ramp integrand. -/
private lemma key_bound {c T ρ z : ℝ} (hc : 0 < c) (hT : 0 < T) (hρ : 0 < ρ)
    (hρT : ρ ≤ T) (hz : 0 < z) :
    ∃ t0 ∈ Ioo (0:ℝ) T, ∃ K : ℝ, 0 < K ∧
      ∀ t ∈ Ioc (0:ℝ) T,
        (Real.sqrt |(c * z * t ^ ((2:ℝ)/3)) ^ 2 - (min ρ (max 0 (T - t))) ^ 2|)⁻¹
          ≤ K * (Real.sqrt |t - t0|)⁻¹ := by
  have ha : 0 < c * z := mul_pos hc hz
  set rr : ℝ → ℝ := fun t => min ρ (max 0 (T - t)) with hrr
  set A : ℝ → ℝ := fun t => (c * z) * t ^ ((2:ℝ)/3) - rr t with hA
  set Br : ℝ → ℝ := fun t => (c * z) * t ^ ((2:ℝ)/3) + rr t with hBr
  have hrr_apply : ∀ t : ℝ, rr t = min ρ (max 0 (T - t)) := fun t => rfl
  have hA_apply : ∀ t : ℝ, A t = (c * z) * t ^ ((2:ℝ)/3) - rr t := fun t => rfl
  have hBr_apply : ∀ t : ℝ, Br t = (c * z) * t ^ ((2:ℝ)/3) + rr t := fun t => rfl
  -- continuity of `rr`
  have hrr_cont : Continuous rr := by
    rw [hrr]
    fun_prop
  -- continuity of `A`
  have hAcont : ContinuousOn A (Icc 0 T) := by
    have h1 : Continuous (fun t : ℝ => (c * z) * t ^ ((2:ℝ)/3)) :=
      continuous_const.mul (Real.continuous_rpow_const (by norm_num))
    rw [hA]
    exact (h1.sub hrr_cont).continuousOn
  -- values at the endpoints
  have hA0 : A 0 = -ρ := by
    rw [hA_apply, hrr_apply]
    rw [show (0:ℝ) ^ ((2:ℝ)/3) = 0 from Real.zero_rpow (by norm_num)]
    rw [mul_zero, zero_sub]
    rw [show T - 0 = T by ring, max_eq_right hT.le, min_eq_left hρT]
  have hAT : 0 < A T := by
    rw [hA_apply, hrr_apply]
    rw [show T - T = (0:ℝ) by ring, max_eq_left le_rfl, min_eq_right hρ.le, sub_zero]
    exact mul_pos ha (Real.rpow_pos_of_pos hT _)
  -- IVT: `A` vanishes somewhere in `(0,T)`
  have h0mem : (0:ℝ) ∈ Icc (A 0) (A T) := by
    rw [hA0]
    exact ⟨by linarith, hAT.le⟩
  obtain ⟨t0, ht0Icc, ht0eq⟩ := (intermediate_value_Icc hT.le hAcont) h0mem
  have ht0pos : 0 < t0 := by
    rcases lt_or_eq_of_le ht0Icc.1 with h | h
    · exact h
    · exfalso
      have hz0 : A 0 = 0 := h.symm ▸ ht0eq
      rw [hA0] at hz0
      linarith
  have ht0ltT : t0 < T := by
    rcases lt_or_eq_of_le ht0Icc.2 with h | h
    · exact h
    · exfalso
      have hz0 : A T = 0 := h ▸ ht0eq
      linarith [hAT]
  -- constants
  set m1 : ℝ := (2/3) * (c * z) * T ^ (-(1/3:ℝ)) with hm1
  have hm1pos : 0 < m1 := by
    rw [hm1]
    have : 0 < T ^ (-(1/3:ℝ)) := Real.rpow_pos_of_pos hT _
    positivity
  set δ : ℝ := min ((c * z) * (T/2) ^ ((2:ℝ)/3)) (min ρ (T/2)) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    refine lt_min ?_ ?_
    · exact mul_pos ha (Real.rpow_pos_of_pos (by positivity : (0:ℝ) < T/2) _)
    · exact lt_min hρ (by positivity)
  set K : ℝ := (m1 * δ) ^ (-(1:ℝ)/2) with hK
  have hKpos : 0 < K := by
    rw [hK]
    exact Real.rpow_pos_of_pos (by positivity : 0 < m1 * δ) _
  -- slope of the pure power part
  have hslope1 : ∀ u ∈ Icc (0:ℝ) T, ∀ v ∈ Icc (0:ℝ) T, u ≤ v →
      m1 * (v - u) ≤ (c * z) * v ^ ((2:ℝ)/3) - (c * z) * u ^ ((2:ℝ)/3) := by
    have hconv : Convex ℝ (Icc (0:ℝ) T) := convex_Icc 0 T
    have hcont : ContinuousOn (fun s : ℝ => (c * z) * s ^ ((2:ℝ)/3)) (Icc 0 T) :=
      (continuous_const.mul (Real.continuous_rpow_const (by norm_num))).continuousOn
    have hdiff : DifferentiableOn ℝ (fun s : ℝ => (c * z) * s ^ ((2:ℝ)/3))
        (interior (Icc (0:ℝ) T)) := by
      intro s hs
      rw [interior_Icc] at hs
      exact ((Real.hasDerivAt_rpow_const (p := (2:ℝ)/3)
        (Or.inl (ne_of_gt hs.1))).const_mul (c * z)).differentiableAt.differentiableWithinAt
    have hderiv_ge : ∀ s ∈ interior (Icc (0:ℝ) T),
        m1 ≤ deriv (fun s : ℝ => (c * z) * s ^ ((2:ℝ)/3)) s := by
      intro s hs
      rw [interior_Icc] at hs
      have hspos : 0 < s := hs.1
      have hsT : s ≤ T := hs.2.le
      have hrpow : T ^ (-(1/3:ℝ)) ≤ s ^ (-(1/3:ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hspos hsT (by norm_num)
      have hd : HasDerivAt (fun s : ℝ => (c * z) * s ^ ((2:ℝ)/3))
          ((c * z) * ((2/3) * s ^ ((2:ℝ)/3 - 1))) s :=
        (Real.hasDerivAt_rpow_const (p := (2:ℝ)/3) (Or.inl (ne_of_gt hspos))).const_mul (c * z)
      rw [hd.deriv, hm1]
      have hexp : (2:ℝ)/3 - 1 = -(1/3:ℝ) := by norm_num
      rw [hexp]
      calc (2/3) * (c * z) * T ^ (-(1/3:ℝ))
          = (c * z) * ((2/3) * T ^ (-(1/3:ℝ))) := by ring
        _ ≤ (c * z) * ((2/3) * s ^ (-(1/3:ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ ha.le
            exact mul_le_mul_of_nonneg_left hrpow (by norm_num)
    intro u hu v hv huv
    exact Convex.mul_sub_le_image_sub_of_le_deriv hconv hcont hdiff hderiv_ge u hu v hv huv
  -- the ramp is antitone
  have hrr_anti : ∀ u v : ℝ, u ≤ v → rr v ≤ rr u := by
    intro u v huv
    rw [hrr_apply, hrr_apply]
    exact min_le_min le_rfl (max_le_max le_rfl (by linarith))
  -- slope of `A`
  have hslopeA : ∀ u ∈ Icc (0:ℝ) T, ∀ v ∈ Icc (0:ℝ) T, u ≤ v → m1 * (v - u) ≤ A v - A u := by
    intro u hu v hv huv
    have h1 := hslope1 u hu v hv huv
    have h2 : 0 ≤ rr u - rr v := by
      have := hrr_anti u v huv
      linarith
    rw [hA_apply, hA_apply]
    linarith
  have hAbsA : ∀ t ∈ Icc (0:ℝ) T, m1 * |t - t0| ≤ |A t| :=
    fun t ht => abs_le_abs_of_slope_ge' hslopeA ht0Icc ht0eq ht
  -- lower bound for the second factor
  have hB_lb : ∀ t ∈ Ioc (0:ℝ) T, δ ≤ Br t := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have htT : t ≤ T := ht.2
    have hleft_nonneg : 0 ≤ (c * z) * t ^ ((2:ℝ)/3) :=
      mul_nonneg ha.le (Real.rpow_nonneg ht0.le _)
    rw [hBr_apply]
    rcases le_total t (T/2) with h | h
    · have hmax : max 0 (T - t) = T - t := max_eq_right (by linarith)
      have hmin : min ρ (T/2) ≤ min ρ (T - t) := min_le_min le_rfl (by linarith)
      have hδle : δ ≤ min ρ (T/2) := by rw [hδ]; exact min_le_right _ _
      have hrr_lb : δ ≤ rr t := by
        rw [hrr_apply, hmax]
        exact le_trans hδle hmin
      linarith
    · have hδle : δ ≤ (c * z) * (T/2) ^ ((2:ℝ)/3) := by rw [hδ]; exact min_le_left _ _
      have hrpow : (T/2) ^ ((2:ℝ)/3) ≤ t ^ ((2:ℝ)/3) :=
        Real.rpow_le_rpow (by positivity) h (by norm_num)
      have hge : (c * z) * (T/2) ^ ((2:ℝ)/3) ≤ (c * z) * t ^ ((2:ℝ)/3) :=
        mul_le_mul_of_nonneg_left hrpow ha.le
      have hnn : 0 ≤ rr t := by
        rw [hrr_apply]
        exact le_min hρ.le (le_max_left 0 (T - t))
      linarith
  -- the algebraic identity
  have hident : ∀ t, 0 < t →
      (c * z * t ^ ((2:ℝ)/3)) ^ 2 - (min ρ (max 0 (T - t))) ^ 2 = A t * Br t := by
    intro t ht
    rw [hA_apply, hBr_apply, hrr_apply]
    ring
  refine ⟨t0, ⟨ht0pos, ht0ltT⟩, K, hKpos, ?_⟩
  intro t ht
  have htIcc : t ∈ Icc (0:ℝ) T := ⟨ht.1.le, ht.2⟩
  have hA_lb : m1 * |t - t0| ≤ |A t| := hAbsA t htIcc
  have hB_lb' : δ ≤ Br t := hB_lb t ht
  have hBpos : 0 < Br t := lt_of_lt_of_le hδpos hB_lb'
  have hid := hident t ht.1
  have hX : m1 * δ * |t - t0| ≤
      |(c * z * t ^ ((2:ℝ)/3)) ^ 2 - (min ρ (max 0 (T - t))) ^ 2| := by
    rw [hid, abs_mul, abs_of_pos hBpos]
    calc m1 * δ * |t - t0| = (m1 * |t - t0|) * δ := by ring
      _ ≤ |A t| * δ := mul_le_mul_of_nonneg_right hA_lb hδpos.le
      _ ≤ |A t| * Br t := mul_le_mul_of_nonneg_left hB_lb' (abs_nonneg _)
  rcases eq_or_ne (|t - t0|) 0 with h0 | h0
  · have ht_eq : t = t0 := sub_eq_zero.mp (abs_eq_zero.mp h0)
    have hid0 : (c * z * t ^ ((2:ℝ)/3)) ^ 2 - (min ρ (max 0 (T - t))) ^ 2 = 0 := by
      rw [ht_eq, hident t0 ht0pos, ht0eq, zero_mul]
    rw [hid0, abs_zero, h0]
    simp
  · have hsub : t - t0 ≠ 0 := fun h => h0 (by rw [h, abs_zero])
    have h0pos : 0 < |t - t0| := abs_pos.mpr hsub
    have hYpos : 0 < m1 * δ * |t - t0| := by
      have h1 : 0 < m1 * δ := mul_pos hm1pos hδpos
      positivity
    calc (Real.sqrt |(c * z * t ^ ((2:ℝ)/3)) ^ 2 - (min ρ (max 0 (T - t))) ^ 2|)⁻¹
        = |(c * z * t ^ ((2:ℝ)/3)) ^ 2 - (min ρ (max 0 (T - t))) ^ 2| ^ (-(1:ℝ)/2) :=
          inv_sqrt_eq_rpow_neg_half' (abs_nonneg _)
      _ ≤ (m1 * δ * |t - t0|) ^ (-(1:ℝ)/2) :=
          Real.rpow_le_rpow_of_nonpos hYpos hX (by norm_num)
      _ = (m1 * δ) ^ (-(1:ℝ)/2) * |t - t0| ^ (-(1:ℝ)/2) :=
          Real.mul_rpow (by positivity) (abs_nonneg _)
      _ = K * |t - t0| ^ (-(1:ℝ)/2) := by rw [hK]
      _ = K * (Real.sqrt |t - t0|)⁻¹ := by
          rw [inv_sqrt_eq_rpow_neg_half' (abs_nonneg _)]

theorem integrableOn_inv_sqrt_abs_parabolic_ramp_sub {c T ρ z : ℝ}
    (hc : 0 < c) (hT : 0 < T) (hρ : 0 < ρ) (hρT : ρ ≤ T) (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (Real.sqrt |(c * z * t ^ ((2:ℝ)/3)) ^ 2 - (min ρ (max 0 (T - t))) ^ 2|)⁻¹)
      (Set.uIoc 0 T) := by
  obtain ⟨t0, _ht0, K, hKpos, hbound⟩ := key_bound hc hT hρ hρT hz
  have hbase : IntegrableOn (fun t : ℝ => |t - t0| ^ (-(1:ℝ)/2)) (Set.Icc 0 T) :=
    integrableOn_abs_sub_rpow_Icc (a := (0:ℝ)) (b := T) (c := t0) (s := -(1:ℝ)/2) hT.le
      (by norm_num)
  have hbase' : IntegrableOn (fun t : ℝ => (Real.sqrt |t - t0|)⁻¹) (Set.uIoc 0 T) := by
    have h1 : IntegrableOn (fun t : ℝ => |t - t0| ^ (-(1:ℝ)/2)) (Set.uIoc 0 T) :=
      hbase.mono_set (by rw [Set.uIoc_of_le hT.le]; exact Ioc_subset_Icc_self)
    refine h1.congr_fun ?_ measurableSet_uIoc
    intro t ht
    exact (inv_sqrt_eq_rpow_neg_half' (abs_nonneg (t - t0))).symm
  have hdom : IntegrableOn (fun t : ℝ => K * (Real.sqrt |t - t0|)⁻¹) (Set.uIoc 0 T) :=
    hbase'.const_mul K
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (Real.sqrt |(c * z * t ^ ((2:ℝ)/3)) ^ 2 - (min ρ (max 0 (T - t))) ^ 2|)⁻¹)
      (volume.restrict (Set.uIoc 0 T)) := by
    have hcont : Continuous
        (fun t : ℝ => (c * z * t ^ ((2:ℝ)/3)) ^ 2 - (min ρ (max 0 (T - t))) ^ 2) := by
      have h1 : Continuous (fun t : ℝ => (c * z) * t ^ ((2:ℝ)/3)) :=
        continuous_const.mul (Real.continuous_rpow_const (by norm_num))
      have h2 : Continuous (fun t : ℝ => min ρ (max 0 (T - t))) := by fun_prop
      exact (h1.pow 2).sub (h2.pow 2)
    have h3 : Measurable (fun x : ℝ => (Real.sqrt |x|)⁻¹) := by fun_prop
    exact (h3.comp hcont.measurable).aestronglyMeasurable
  rw [IntegrableOn]
  refine Integrable.mono' hdom hmeas ?_
  rw [ae_restrict_iff' measurableSet_uIoc]
  filter_upwards with t ht
  have ht' : t ∈ Ioc (0:ℝ) T := by rwa [Set.uIoc_of_le hT.le] at ht
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact hbound t ht'

end Commons.Analysis.Integral
