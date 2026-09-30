import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.casdiv.yr_L2
import Submission.Work.BMF.casdiv.wdb_support
import Submission.Work.BMF.mrlas.norm_Kf_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Cauchy--Schwarz consequence of the `L²` bound (own copy)

Same statement and proof as `Work.BMF.casdiv.b_bound`, but consuming the unconditional
`Work.BMF.casdiv.yr_L2_Kf_bound` instead of `series_tau`.
-/

namespace Work.BMF.casdiv

open MeasureTheory intervalIntegral
open scoped BigOperators

/-- Cauchy--Schwarz for the integral over an interval, for nonnegative bounded measurable functions. -/
private lemma cs_interval {a b : ℝ} (hab : a ≤ b) {F G : ℝ → ℝ}
    (hFm : Measurable F) (hGm : Measurable G)
    (hFnn : ∀ t ∈ Set.Icc a b, 0 ≤ F t) (hGnn : ∀ t ∈ Set.Icc a b, 0 ≤ G t)
    (hFb : ∃ C, ∀ t ∈ Set.Icc a b, F t ≤ C) (hGb : ∃ C, ∀ t ∈ Set.Icc a b, G t ≤ C) :
    (∫ t in a..b, F t * G t) ≤
      Real.sqrt (∫ t in a..b, F t ^ 2) * Real.sqrt (∫ t in a..b, G t ^ 2) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_of_le hab]
  obtain ⟨C, hC⟩ := hFb
  obtain ⟨D, hD⟩ := hGb
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]; exact measure_Ioc_lt_top⟩
  have hFmem : MemLp F (ENNReal.ofReal 2) (volume.restrict (Set.Ioc a b)) :=
    MemLp.of_bound hFm.aestronglyMeasurable (max C 0) (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
      have hxI : x ∈ Set.Icc a b := Set.Ioc_subset_Icc_self hx
      rw [Real.norm_of_nonneg (hFnn x hxI)]
      exact le_max_of_le_left (hC x hxI))
  have hGmem : MemLp G (ENNReal.ofReal 2) (volume.restrict (Set.Ioc a b)) :=
    MemLp.of_bound hGm.aestronglyMeasurable (max D 0) (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
      have hxI : x ∈ Set.Icc a b := Set.Ioc_subset_Icc_self hx
      rw [Real.norm_of_nonneg (hGnn x hxI)]
      exact le_max_of_le_left (hD x hxI))
  have hFae : 0 ≤ᵐ[volume.restrict (Set.Ioc a b)] F := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
    exact hFnn x (Set.Ioc_subset_Icc_self hx)
  have hGae : 0 ≤ᵐ[volume.restrict (Set.Ioc a b)] G := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
    exact hGnn x (Set.Ioc_subset_Icc_self hx)
  have h2 : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hhold := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Set.Ioc a b)) h2 hFae hGae hFmem hGmem
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa [Real.rpow_natCast, Real.rpow_two] using hhold

/-- `√(X+Y) ≤ √X + √Y` for nonnegative `X,Y`. -/
private lemma sqrt_add_le_sqrt_add_sqrt {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    Real.sqrt (X + Y) ≤ Real.sqrt X + Real.sqrt Y := by
  have hnn : 0 ≤ Real.sqrt X + Real.sqrt Y := by positivity
  have hsq : X + Y ≤ (Real.sqrt X + Real.sqrt Y) ^ 2 := by
    nlinarith [Real.sq_sqrt hX, Real.sq_sqrt hY, Real.sqrt_nonneg X, Real.sqrt_nonneg Y]
  calc Real.sqrt (X + Y) ≤ Real.sqrt ((Real.sqrt X + Real.sqrt Y) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt X + Real.sqrt Y := Real.sqrt_sq hnn

/-- `√(e^{2w}) = e^w`. -/
private lemma sqrt_exp_two_mul (w : ℝ) : Real.sqrt (Real.exp (2 * w)) = Real.exp w := by
  have h : Real.exp (2 * w) = (Real.exp w) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  rw [h, Real.sqrt_sq (Real.exp_nonneg w)]

/-- **Cauchy--Schwarz at the exponent `α`.**  For `1 ≤ y`, `0 < α ≤ 1`,
`∫_1^y ‖Kf f t‖/t² dt ≤ √(∫_1^y ‖Kf f t‖²/t^{3+2α}) · √(∫_1^y t^{2α-1})`. -/
private lemma cs_kf (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {y α : ℝ}
    (hy1 : 1 ≤ y) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∫ t in (1 : ℝ)..y, ‖Kf f t‖ / t ^ 2) ≤
      Real.sqrt (∫ t in (1 : ℝ)..y, ‖Kf f t‖ ^ 2 / t ^ (3 + 2 * α)) *
      Real.sqrt (∫ t in (1 : ℝ)..y, t ^ (2 * α - 1)) := by
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
  set F : ℝ → ℝ := fun t => ‖Kf f t‖ / t ^ (3 / 2 + α) with hFdef
  set G : ℝ → ℝ := fun t => t ^ (α - 1 / 2) with hGdef
  have hmeasKf : Measurable (fun t : ℝ => Kf f t) := by
    have hA : Measurable (fun n : ℕ => ∑ m ∈ Finset.Icc 1 n, f m * (Real.log m : ℂ)) :=
      measurable_of_countable _
    exact hA.comp Nat.measurable_floor
  have hFm : Measurable F := hmeasKf.norm.div (measurable_id.pow_const _)
  have hGm : Measurable G := measurable_id.pow_const _
  have hFnn : ∀ t ∈ Set.Icc 1 y, 0 ≤ F t := by
    intro t ht
    show 0 ≤ ‖Kf f t‖ / t ^ (3 / 2 + α)
    exact div_nonneg (norm_nonneg _)
      (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos ht.1) _).le
  have hGnn : ∀ t ∈ Set.Icc 1 y, 0 ≤ G t := by
    intro t ht
    show 0 ≤ t ^ (α - 1 / 2)
    exact Real.rpow_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t) _
  have hFb : ∃ C, ∀ t ∈ Set.Icc 1 y, F t ≤ C := by
    refine ⟨y * Real.log y + 1, ?_⟩
    intro t ht
    have ht1 : 1 ≤ t := ht.1
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht1
    have hA : ‖Kf f t‖ ≤ t * Real.log t := Work.BMF.mrlas.norm_Kf_le f hb ht1
    have hlog : Real.log t ≤ Real.log y := Real.log_le_log ht0 ht.2
    have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht1
    have htlog : t * Real.log t ≤ y * Real.log y := mul_le_mul ht.2 hlog hlogt hy0.le
    have hden : (1 : ℝ) ≤ t ^ (3 / 2 + α) := Real.one_le_rpow ht1 (by linarith)
    have hden0 : (0 : ℝ) < t ^ (3 / 2 + α) := lt_of_lt_of_le one_pos hden
    show ‖Kf f t‖ / t ^ (3 / 2 + α) ≤ y * Real.log y + 1
    calc ‖Kf f t‖ / t ^ (3 / 2 + α) ≤ (y * Real.log y) / t ^ (3 / 2 + α) :=
          div_le_div_of_nonneg_right (le_trans hA htlog) hden0.le
      _ ≤ (y * Real.log y) / 1 :=
          div_le_div_of_nonneg_left (mul_nonneg hy0.le (Real.log_nonneg hy1)) one_pos hden
      _ ≤ y * Real.log y + 1 := by rw [div_one]; linarith
  have hGb : ∃ C, ∀ t ∈ Set.Icc 1 y, G t ≤ C := by
    refine ⟨max 1 (y ^ ((1 : ℝ) / 2)), ?_⟩
    intro t ht
    have ht1 : 1 ≤ t := ht.1
    show t ^ (α - 1 / 2) ≤ max 1 (y ^ ((1 : ℝ) / 2))
    rcases le_total (1 / 2) α with h | h
    · have h1 : t ^ (α - 1 / 2) ≤ t ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le ht1 (show α - 1 / 2 ≤ 1 / 2 by linarith)
      have h2 : t ^ ((1 : ℝ) / 2) ≤ y ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (le_of_lt (lt_of_lt_of_le one_pos ht1)) ht.2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      exact le_trans (le_trans h1 h2) (le_max_right _ _)
    · have h1 : t ^ (α - 1 / 2) ≤ t ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le ht1 (show α - 1 / 2 ≤ 0 by linarith)
      rw [Real.rpow_zero] at h1
      exact le_trans h1 (le_max_left _ _)
  have hcs := cs_interval (a := 1) (b := y) hy1 hFm hGm hFnn hGnn hFb hGb
  have hFG : (∫ t in (1 : ℝ)..y, F t * G t) = ∫ t in (1 : ℝ)..y, ‖Kf f t‖ / t ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hy1] at ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht.1
    have h3 : t ^ (α - 1 / 2) * t ^ 2 = t ^ (3 / 2 + α) := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht0]
      congr 1; ring
    show ‖Kf f t‖ / t ^ (3 / 2 + α) * t ^ (α - 1 / 2) = ‖Kf f t‖ / t ^ 2
    rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity), mul_assoc, h3]
  have hF2 : (∫ t in (1 : ℝ)..y, F t ^ 2) = ∫ t in (1 : ℝ)..y, ‖Kf f t‖ ^ 2 / t ^ (3 + 2 * α) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hy1] at ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht.1
    have ha : (t ^ (3 / 2 + α)) ^ 2 = t ^ (3 + 2 * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; congr 1; ring
    show (‖Kf f t‖ / t ^ (3 / 2 + α)) ^ 2 = ‖Kf f t‖ ^ 2 / t ^ (3 + 2 * α)
    rw [div_pow, ha]
  have hG2 : (∫ t in (1 : ℝ)..y, G t ^ 2) = ∫ t in (1 : ℝ)..y, t ^ (2 * α - 1) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hy1] at ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht.1
    show (t ^ (α - 1 / 2)) ^ 2 = t ^ (2 * α - 1)
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; congr 1; ring
  rw [hFG, hF2, hG2] at hcs
  exact hcs

theorem yr_Kf_L1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x y T : ℝ, 11 ≤ x → 3 ≤ y → y ≤ x → 2 ≤ T →
        (∫ t in (1 : ℝ)..y, ‖Kf f t‖ / t ^ 2) ≤
          C * (Real.log y * Real.exp (Wsup f x (1 / Real.log y) (T + 1)) +
               Real.exp (Zrcp y) * Real.log y / Real.sqrt T) := by
  obtain ⟨Cs, hCs, hser⟩ := yr_L2_Kf_bound
  obtain ⟨Cw, hCw, hw⟩ := Wsup_scale
  refine ⟨Real.sqrt (Cs * max (Real.exp (2 * Cw)) 1) * Real.exp 1 + 1, by positivity, ?_⟩
  intro f hf1 hmul hb x y T hx hy hyx hT
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogy1 : (1 : ℝ) ≤ Real.log y := by
    have hlog3 : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
    exact le_trans hlog3.le (Real.log_le_log (by norm_num) hy)
  set α : ℝ := 1 / Real.log y with hαdef
  have hα : 0 < α := by rw [hαdef]; positivity
  have hα1 : α ≤ 1 := by rw [hαdef, div_le_one hlogy]; exact hlogy1
  have hαy : α * Real.log y = 1 := by rw [hαdef]; field_simp
  have h1α : (1 : ℝ) / α = Real.log y := by rw [hαdef, one_div_one_div]
  have hexpα : Real.exp (1 / α) = y := by rw [h1α]; exact Real.exp_log hy0
  -- `yr_L2_Kf_bound` at scale `y`
  have hseries := hser f hf1 hmul hb y α T (by linarith) hα hα1 (by linarith) (le_of_eq hexpα)
  -- `Wsup_scale`: promote `Wsup f y` to `Wsup f x`
  have hsc := hw f hb y x α (T + 1) (by linarith) hyx hx hα hα1 (by rw [hαy]) (by linarith)
  have hWexp : Real.exp (2 * Wsup f y α (T + 1))
      ≤ Real.exp (2 * Cw) * Real.exp (2 * Wsup f x α (T + 1)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [hsc])
  set K1 : ℝ := Cs * max (Real.exp (2 * Cw)) 1 with hK1
  have hK1pos : 0 < K1 := by rw [hK1]; positivity
  -- the `L²` bound at exponent `α`
  have hP : (∫ t in (1 : ℝ)..y, ‖Kf f t‖ ^ 2 / t ^ (3 + 2 * α))
      ≤ K1 * (Real.log y * Real.exp (2 * Wsup f x α (T + 1))
          + Real.exp (2 * Zrcp y) * Real.log y / T) := by
    refine le_trans hseries ?_
    have hmax1 : (1 : ℝ) ≤ max (Real.exp (2 * Cw)) 1 := le_max_right _ _
    have hmaxe : Real.exp (2 * Cw) ≤ max (Real.exp (2 * Cw)) 1 := le_max_left _ _
    have hX0 : 0 ≤ Real.log y * Real.exp (2 * Wsup f x α (T + 1)) :=
      mul_nonneg hlogy.le (Real.exp_nonneg _)
    have hY0 : 0 ≤ Real.exp (2 * Zrcp y) * Real.log y / T :=
      div_nonneg (mul_nonneg (Real.exp_nonneg _) hlogy.le) hT0.le
    have hA : (1 / α) * Real.exp (2 * Wsup f y α (T + 1))
        ≤ max (Real.exp (2 * Cw)) 1 * (Real.log y * Real.exp (2 * Wsup f x α (T + 1))) := by
      rw [h1α]
      refine le_trans (mul_le_mul_of_nonneg_left hWexp hlogy.le) ?_
      rw [show Real.log y * (Real.exp (2 * Cw) * Real.exp (2 * Wsup f x α (T + 1)))
          = Real.exp (2 * Cw) * (Real.log y * Real.exp (2 * Wsup f x α (T + 1))) by ring]
      exact mul_le_mul_of_nonneg_right hmaxe hX0
    have hB : Real.exp (2 * Zrcp y) / (α * T)
        ≤ max (Real.exp (2 * Cw)) 1 * (Real.exp (2 * Zrcp y) * Real.log y / T) := by
      have h : Real.exp (2 * Zrcp y) / (α * T) = Real.exp (2 * Zrcp y) * (1 / α) / T := by
        field_simp
      rw [h, h1α]
      calc Real.exp (2 * Zrcp y) * Real.log y / T
          = 1 * (Real.exp (2 * Zrcp y) * Real.log y / T) := (one_mul _).symm
        _ ≤ max (Real.exp (2 * Cw)) 1 * (Real.exp (2 * Zrcp y) * Real.log y / T) :=
            mul_le_mul_of_nonneg_right hmax1 hY0
    have hsum : (1 / α) * Real.exp (2 * Wsup f y α (T + 1)) + Real.exp (2 * Zrcp y) / (α * T)
        ≤ max (Real.exp (2 * Cw)) 1 *
            (Real.log y * Real.exp (2 * Wsup f x α (T + 1))
              + Real.exp (2 * Zrcp y) * Real.log y / T) := by
      nlinarith [hA, hB]
    rw [hK1]
    calc Cs * ((1 / α) * Real.exp (2 * Wsup f y α (T + 1)) + Real.exp (2 * Zrcp y) / (α * T))
        ≤ Cs * (max (Real.exp (2 * Cw)) 1 *
            (Real.log y * Real.exp (2 * Wsup f x α (T + 1))
              + Real.exp (2 * Zrcp y) * Real.log y / T)) :=
          mul_le_mul_of_nonneg_left hsum hCs.le
      _ = (Cs * max (Real.exp (2 * Cw)) 1) *
            (Real.log y * Real.exp (2 * Wsup f x α (T + 1))
              + Real.exp (2 * Zrcp y) * Real.log y / T) := by ring
  -- the Cauchy--Schwarz step
  have hcs := cs_kf f hb (y := y) (α := α) hy1 hα hα1
  -- the elementary integral
  have hQ : (∫ t in (1 : ℝ)..y, t ^ (2 * α - 1)) ≤ Real.exp 2 * Real.log y := by
    rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < 2 * α - 1))]
    rw [show (2 * α - 1) + 1 = 2 * α by ring, Real.one_rpow]
    rw [Real.rpow_def_of_pos hy0, show Real.log y * (2 * α) = 2 by nlinarith [hαy]]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.exp_pos 2, hαy]
  refine le_trans hcs ?_
  refine le_trans (mul_le_mul (Real.sqrt_le_sqrt hP) (Real.sqrt_le_sqrt hQ)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) ?_
  -- final assembly
  have e1 : Real.sqrt (Real.log y * Real.exp (2 * Wsup f x α (T + 1)))
        * Real.sqrt (Real.exp 2 * Real.log y)
      = Real.exp 1 * (Real.log y * Real.exp (Wsup f x α (T + 1))) := by
    rw [Real.sqrt_mul hlogy.le, sqrt_exp_two_mul, Real.sqrt_mul (Real.exp_pos 2).le,
        show Real.sqrt (Real.exp 2) = Real.exp 1 from by simpa using sqrt_exp_two_mul (1 : ℝ)]
    rw [show (Real.sqrt (Real.log y) * Real.exp (Wsup f x α (T + 1)))
          * (Real.exp 1 * Real.sqrt (Real.log y))
        = Real.exp 1 * (Real.exp (Wsup f x α (T + 1))
            * (Real.sqrt (Real.log y) * Real.sqrt (Real.log y))) by ring,
      Real.mul_self_sqrt hlogy.le]
    ring
  have e2 : Real.sqrt (Real.exp (2 * Zrcp y) * Real.log y / T) * Real.sqrt (Real.exp 2 * Real.log y)
      = Real.exp 1 * (Real.exp (Zrcp y) * Real.log y / Real.sqrt T) := by
    rw [show Real.exp (2 * Zrcp y) * Real.log y / T = Real.exp (2 * Zrcp y) * (Real.log y / T)
        by ring]
    rw [Real.sqrt_mul (Real.exp_pos _).le, sqrt_exp_two_mul, Real.sqrt_div hlogy.le,
        Real.sqrt_mul (Real.exp_pos 2).le,
        show Real.sqrt (Real.exp 2) = Real.exp 1 from by simpa using sqrt_exp_two_mul (1 : ℝ)]
    rw [show (Real.exp (Zrcp y) * (Real.sqrt (Real.log y) / Real.sqrt T))
          * (Real.exp 1 * Real.sqrt (Real.log y))
        = Real.exp 1 * (Real.exp (Zrcp y)
            * ((Real.sqrt (Real.log y) * Real.sqrt (Real.log y)) / Real.sqrt T)) by ring,
      Real.mul_self_sqrt hlogy.le]
    ring
  have hstep : Real.sqrt (K1 * (Real.log y * Real.exp (2 * Wsup f x α (T + 1))
          + Real.exp (2 * Zrcp y) * Real.log y / T)) * Real.sqrt (Real.exp 2 * Real.log y)
      ≤ (Real.sqrt K1 * Real.exp 1) * (Real.log y * Real.exp (Wsup f x α (T + 1))
          + Real.exp (Zrcp y) * Real.log y / Real.sqrt T) := by
    have hX0 : 0 ≤ Real.log y * Real.exp (2 * Wsup f x α (T + 1)) :=
      mul_nonneg hlogy.le (Real.exp_nonneg _)
    have hY0 : 0 ≤ Real.exp (2 * Zrcp y) * Real.log y / T :=
      div_nonneg (mul_nonneg (Real.exp_nonneg _) hlogy.le) hT0.le
    have hXY := sqrt_add_le_sqrt_add_sqrt hX0 hY0
    have hq0 : 0 ≤ Real.sqrt (Real.exp 2 * Real.log y) := Real.sqrt_nonneg _
    rw [Real.sqrt_mul hK1pos.le]
    calc Real.sqrt K1 * Real.sqrt (Real.log y * Real.exp (2 * Wsup f x α (T + 1))
            + Real.exp (2 * Zrcp y) * Real.log y / T) * Real.sqrt (Real.exp 2 * Real.log y)
        = Real.sqrt K1 * (Real.sqrt (Real.log y * Real.exp (2 * Wsup f x α (T + 1))
            + Real.exp (2 * Zrcp y) * Real.log y / T) * Real.sqrt (Real.exp 2 * Real.log y)) := by
          ring
      _ ≤ Real.sqrt K1 * ((Real.sqrt (Real.log y * Real.exp (2 * Wsup f x α (T + 1)))
            + Real.sqrt (Real.exp (2 * Zrcp y) * Real.log y / T))
            * Real.sqrt (Real.exp 2 * Real.log y)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hXY hq0) (Real.sqrt_nonneg K1)
      _ = Real.sqrt K1 * (Real.exp 1 * (Real.log y * Real.exp (Wsup f x α (T + 1)))
            + Real.exp 1 * (Real.exp (Zrcp y) * Real.log y / Real.sqrt T)) := by
          rw [show (Real.sqrt (Real.log y * Real.exp (2 * Wsup f x α (T + 1)))
                + Real.sqrt (Real.exp (2 * Zrcp y) * Real.log y / T))
                * Real.sqrt (Real.exp 2 * Real.log y)
              = Real.sqrt (Real.log y * Real.exp (2 * Wsup f x α (T + 1)))
                  * Real.sqrt (Real.exp 2 * Real.log y)
                + Real.sqrt (Real.exp (2 * Zrcp y) * Real.log y / T)
                  * Real.sqrt (Real.exp 2 * Real.log y) by ring,
            e1, e2]
      _ = (Real.sqrt K1 * Real.exp 1) * (Real.log y * Real.exp (Wsup f x α (T + 1))
            + Real.exp (Zrcp y) * Real.log y / Real.sqrt T) := by ring
  refine le_trans hstep ?_
  have hA' : 0 ≤ Real.log y * Real.exp (Wsup f x α (T + 1)) :=
    mul_nonneg hlogy.le (Real.exp_nonneg _)
  have hB' : 0 ≤ Real.exp (Zrcp y) * Real.log y / Real.sqrt T :=
    div_nonneg (mul_nonneg (Real.exp_nonneg _) hlogy.le) (Real.sqrt_nonneg _)
  have hbr : 0 ≤ Real.log y * Real.exp (Wsup f x α (T + 1))
      + Real.exp (Zrcp y) * Real.log y / Real.sqrt T := add_nonneg hA' hB'
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hbr

end Work.BMF.casdiv
