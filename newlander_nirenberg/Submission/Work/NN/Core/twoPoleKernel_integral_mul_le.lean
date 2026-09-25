import Mathlib
import Submission.Work.NN.Core.fiberBeurling
import Submission.Work.CR.Flat.Cauchy.integral_norm_rpow_ball
import Submission.Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball

namespace Work.NN.Core

open MeasureTheory Metric

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- **Pointwise two-pole bound.**  For `0 < α < 1`, `d > 0`, `0 ≤ u`, `0 ≤ v`, `d ≤ u + v` and
`|u - v| ≤ d`:
`(u * v)⁻¹ ≤ 4 * 3^α * d^(α-1) * (u^(-1-α) + v^(-1-α))`.

Route: case `u ≤ 2d`: use `(uv)⁻¹ ≤ (2/d)(u⁻¹ + v⁻¹)` (equivalent to `d ≤ 2(u+v)`), then
`u⁻¹ ≤ (2d)^α * u^(-1-α)` and `v⁻¹ ≤ (3d)^α * v^(-1-α)` (from `u ≤ 2d` and `v ≤ u + d ≤ 3d`),
and `2·2^α ≤ 4·3^α`, `2·3^α ≤ 4·3^α`.  Case `u > 2d`: `v ≥ u - d > u/2` so `(uv)⁻¹ ≤ 2/u²`, and
`2u^{-2} ≤ 2^α d^{α-1} u^{-1-α}` (from `u ≥ 2d`, `α-1<0`), and `2^α ≤ 4·3^α`.  Edge cases
`u = 0` or `v = 0` give left side `0`, so they are immediate from nonnegativity of the rpow terms. -/
private lemma twoPole_pointwise_le {α d u v : ℝ} (hα : 0 < α) (hα1 : α < 1) (hd : 0 < d)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : d ≤ u + v) (huvd : |u - v| ≤ d) :
    (u * v)⁻¹ ≤ 4 * (3 : ℝ) ^ α * d ^ (α - 1) * (u ^ (-1 - α) + v ^ (-1 - α)) := by
  have hdpos : (0:ℝ) < d ^ (α - 1) := Real.rpow_pos_of_pos hd _
  have hCnn : (0:ℝ) ≤ 4 * 3 ^ α * d ^ (α - 1) := by positivity
  by_cases huz : u = 0
  · rw [huz, zero_mul, inv_zero]
    exact mul_nonneg hCnn (add_nonneg (Real.rpow_nonneg le_rfl _) (Real.rpow_nonneg hv _))
  by_cases hvz : v = 0
  · rw [hvz, mul_zero, inv_zero]
    exact mul_nonneg hCnn (add_nonneg (Real.rpow_nonneg hu _) (Real.rpow_nonneg le_rfl _))
  have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm huz)
  have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hvz)
  have hstepA : (u * v)⁻¹ ≤ (2 / d) * (u⁻¹ + v⁻¹) := by
    have h2u : d ≤ 2 * (u + v) := by linarith
    have huvpos : 0 < u * v := mul_pos hupos hvpos
    have hkey : (u * v)⁻¹ * (d * (u * v)) ≤ ((2 / d) * (u⁻¹ + v⁻¹)) * (d * (u * v)) := by
      have hleft : (u * v)⁻¹ * (d * (u * v)) = d := by
        rw [mul_comm ((u*v)⁻¹) (d*(u*v)), mul_assoc, mul_inv_cancel₀ (ne_of_gt huvpos), mul_one]
      have hright : ((2 / d) * (u⁻¹ + v⁻¹)) * (d * (u * v)) = 2 * (u + v) := by
        field_simp
        ring
      rw [hleft, hright]
      linarith
    exact (mul_le_mul_iff_left₀ (by positivity : (0:ℝ) < d * (u * v))).mp hkey
  by_cases hu2 : u ≤ 2 * d
  · have hv3 : v ≤ 3 * d := by
      have h := (abs_le.mp huvd).1
      linarith
    have key : ∀ x : ℝ, 0 < x → x ≤ 3 * d → (2 / d) * x ^ α ≤ 4 * 3 ^ α * d ^ (α - 1) := by
      intro x hx hxle
      have e : (2 / d) * (3 * d) ^ α = 2 * 3 ^ α * d ^ (α - 1) := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ (3:ℝ)) (le_of_lt hd)]
        rw [Real.rpow_sub hd α 1, Real.rpow_one]
        field_simp
      have h1 : (2 / d) * x ^ α ≤ (2 / d) * (3 * d) ^ α :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_of_lt hx) hxle (le_of_lt hα)) (by positivity)
      rw [e] at h1
      have h2 : 2 * 3 ^ α * d ^ (α - 1) ≤ 4 * 3 ^ α * d ^ (α - 1) := by
        have h3α : (0:ℝ) ≤ 3 ^ α := Real.rpow_nonneg (by norm_num) α
        have h23 : (2:ℝ) * 3^α ≤ 4 * 3^α := by linarith
        exact mul_le_mul_of_nonneg_right h23 (le_of_lt hdpos)
      linarith
    have hu_bound : u⁻¹ ≤ (2 * d) ^ α * u ^ (-1 - α) := by
      have h1 : u ^ (-1:ℝ) = u ^ α * u ^ (-1 - α) := by
        rw [← Real.rpow_add hupos, show (α + (-1 - α)) = (-1:ℝ) by ring]
      rw [← Real.rpow_neg_one u, h1]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (le_of_lt hupos) hu2 (le_of_lt hα))
        (Real.rpow_nonneg (le_of_lt hupos) _)
    have hv_bound : v⁻¹ ≤ (3 * d) ^ α * v ^ (-1 - α) := by
      have h1 : v ^ (-1:ℝ) = v ^ α * v ^ (-1 - α) := by
        rw [← Real.rpow_add hvpos, show (α + (-1 - α)) = (-1:ℝ) by ring]
      rw [← Real.rpow_neg_one v, h1]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (le_of_lt hvpos) hv3 (le_of_lt hα))
        (Real.rpow_nonneg (le_of_lt hvpos) _)
    calc (u * v)⁻¹ ≤ (2 / d) * (u⁻¹ + v⁻¹) := hstepA
      _ ≤ (2 / d) * ((2 * d) ^ α * u ^ (-1 - α) + (3 * d) ^ α * v ^ (-1 - α)) :=
            mul_le_mul_of_nonneg_left (add_le_add hu_bound hv_bound) (by positivity)
      _ = ((2 / d) * (2 * d) ^ α) * u ^ (-1 - α) + ((2 / d) * (3 * d) ^ α) * v ^ (-1 - α) := by ring
      _ ≤ (4 * 3 ^ α * d ^ (α - 1)) * u ^ (-1 - α) + (4 * 3 ^ α * d ^ (α - 1)) * v ^ (-1 - α) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right (key (2 * d) (by positivity) (by linarith))
                (Real.rpow_nonneg (le_of_lt hupos) _)
            · exact mul_le_mul_of_nonneg_right (key (3 * d) (by positivity) (le_refl _))
                (Real.rpow_nonneg (le_of_lt hvpos) _)
      _ = 4 * 3 ^ α * d ^ (α - 1) * (u ^ (-1 - α) + v ^ (-1 - α)) := by ring
  · have hu2' : 2 * d < u := not_le.mp hu2
    have hv_gt : u / 2 < v := by
      have h : u - v ≤ d := (abs_le.mp huvd).2
      linarith
    have hstepB : (u * v)⁻¹ ≤ 2 / u ^ 2 := by
      have huvpos : 0 < u * v := mul_pos hupos hvpos
      rw [← sub_nonneg]
      have hcalc : 2 / u ^ 2 - (u * v)⁻¹ = (2 * v - u) / (u ^ 2 * v) := by
        field_simp
      rw [hcalc]
      exact div_nonneg (by linarith) (by positivity)
    have hle : u ^ (α - 1) ≤ (2 * d) ^ (α - 1) := by
      have h1 : u ^ (α - 1) = (u ^ (1 - α))⁻¹ := by
        rw [show α - 1 = -(1 - α) by ring, Real.rpow_neg (le_of_lt hupos)]
      have h2 : (2 * d) ^ (α - 1) = ((2 * d) ^ (1 - α))⁻¹ := by
        rw [show α - 1 = -(1 - α) by ring, Real.rpow_neg (by positivity : (0:ℝ) ≤ 2 * d)]
      rw [h1, h2]
      exact (inv_le_inv₀ (Real.rpow_pos_of_pos hupos _)
        (Real.rpow_pos_of_pos (by positivity : (0:ℝ) < 2 * d) _)).mpr
        (Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 2 * d) hu2'.le (by linarith : (0:ℝ) ≤ 1 - α))
    have e2 : 2 / u ^ 2 = 2 * (u ^ (-1 - α) * u ^ (α - 1)) := by
      have h1 : u ^ (-1 - α) * u ^ (α - 1) = u ^ (-2:ℝ) := by
        rw [← Real.rpow_add hupos, show (-1 - α) + (α - 1) = (-2:ℝ) by ring]
      have h2 : u ^ (-2:ℝ) = (u ^ 2)⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hupos) (2:ℝ)]
        congr 1
        exact Real.rpow_natCast u 2
      rw [div_eq_mul_inv, ← h2, ← h1]
    have h2α : (2:ℝ) ^ α ≤ 4 * 3 ^ α := by
      have h1 : (2:ℝ)^α ≤ 2 := by
        have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hα1.le
        rwa [Real.rpow_one] at this
      have h2 : (1:ℝ) ≤ 3^α := Real.one_le_rpow (by norm_num) hα.le
      nlinarith
    calc (u * v)⁻¹ ≤ 2 / u ^ 2 := hstepB
      _ = 2 * (u ^ (-1 - α) * u ^ (α - 1)) := e2
      _ ≤ 2 * (u ^ (-1 - α) * (2 * d) ^ (α - 1)) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg (le_of_lt hupos) _)
      _ = 2 ^ α * d ^ (α - 1) * u ^ (-1 - α) := by
            rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ (2:ℝ)) (le_of_lt hd)]
            have h2 : (2:ℝ) * 2 ^ (α - 1) = 2 ^ α := by
              conv_rhs => rw [show α = 1 + (α - 1) by ring]
              rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one]
            rw [show 2 * (u ^ (-1 - α) * (2 ^ (α - 1) * d ^ (α - 1)))
                = (2 * 2 ^ (α - 1)) * d ^ (α - 1) * u ^ (-1 - α) by ring, h2]
      _ ≤ 4 * 3 ^ α * d ^ (α - 1) * (u ^ (-1 - α) + v ^ (-1 - α)) := by
            have hdnn : (0:ℝ) ≤ d ^ (α - 1) := le_of_lt hdpos
            have h1 : 2 ^ α * d ^ (α - 1) * u ^ (-1 - α)
                ≤ 4 * 3 ^ α * d ^ (α - 1) * u ^ (-1 - α) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2α hdnn)
                (Real.rpow_nonneg (le_of_lt hupos) _)
            have h3 : 4 * 3 ^ α * d ^ (α - 1) * u ^ (-1 - α)
                ≤ 4 * 3 ^ α * d ^ (α - 1) * (u ^ (-1 - α) + v ^ (-1 - α)) :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg (le_of_lt hvpos) _))
                (by positivity)
            linarith

/-- Local integrability of a shifted power of the norm on a disc.  For `-2 < s` and any
`a c : ℂ`, `R : ℝ`, the function `w ↦ ‖w - a‖ ^ s` is integrable on `Metric.ball c R`. -/
private lemma integrableOn_norm_sub_rpow_ball (a c : ℂ) {R s : ℝ} (hs : -2 < s) :
    IntegrableOn (fun w : ℂ => ‖w - a‖ ^ s) (Metric.ball c R) := by
  have hmp : MeasurePreserving (fun z : ℂ => z - a) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right volume (-a)
  have hemb : MeasurableEmbedding (fun z : ℂ => z - a) := by
    simpa only [MeasurableEquiv.coe_addRight, sub_eq_add_neg] using
      (MeasurableEquiv.addRight (-a)).measurableEmbedding
  have himg : (fun z : ℂ => z - a) '' Metric.ball c R = Metric.ball (c - a) R := by
    ext w
    simp only [Set.mem_image, Metric.mem_ball, dist_eq_norm]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rwa [show (z - a) - (c - a) = z - c by ring]
    · intro hw
      refine ⟨w + a, ?_, by ring⟩
      rwa [show w + a - c = w - (c - a) by ring]
  have h1 : IntegrableOn (fun z : ℂ => ‖z‖ ^ s) (Metric.ball (c - a) R) := by
    refine (Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball (ρ := R + ‖c - a‖) hs).mono_set ?_
    intro z hz
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero] at hz ⊢
    calc ‖z‖ = ‖(z - (c - a)) + (c - a)‖ := by rw [show (z - (c - a)) + (c - a) = z by ring]
      _ ≤ ‖z - (c - a)‖ + ‖c - a‖ := norm_add_le _ _
      _ < R + ‖c - a‖ := by linarith
  exact (hmp.integrableOn_image hemb (f := fun z : ℂ => ‖z‖ ^ s)
      (s := Metric.ball c R)).mp (by rw [himg]; exact h1)

/-- Translation invariance moves the pole to the centre of the disc: for `a : ℂ`, `ρ s : ℝ`,
`∫_{w ∈ Metric.ball a ρ} ‖w - a‖^s = ∫_{z ∈ Metric.ball 0 ρ} ‖z‖^s`. -/
private lemma setIntegral_norm_sub_rpow_ball (a : ℂ) {ρ s : ℝ} :
    ∫ w in Metric.ball a ρ, ‖w - a‖ ^ s = ∫ z in Metric.ball (0:ℂ) ρ, ‖z‖ ^ s := by
  have hmp : MeasurePreserving (fun z : ℂ => z + a) volume volume :=
    measurePreserving_add_right volume a
  have hemb : MeasurableEmbedding (fun z : ℂ => z + a) :=
    (MeasurableEquiv.addRight a).measurableEmbedding
  have hpre : (fun z : ℂ => z + a) ⁻¹' Metric.ball a ρ = Metric.ball (0:ℂ) ρ := by
    ext z
    simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero]
    rw [show z + a - a = z by ring]
  have h := hmp.setIntegral_preimage_emb hemb (fun w : ℂ => ‖w - a‖ ^ s) (Metric.ball a ρ)
  rw [hpre] at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_ball
  intro z _
  show ‖z + a - a‖ ^ s = ‖z‖ ^ s
  rw [show z + a - a = z by ring]

/-- Two-pole kernel bound: for `0 < α < 1`, `R > 0`, `0 ≤ r0 < R` there is `K > 0` with, for all
`a b : ℂ` of norm `≤ r0`,
`‖a - b‖ * ∫_{‖w‖<R} (‖w-a‖‖w-b‖)⁻¹ ≤ K ‖a-b‖^α`. -/
lemma twoPoleKernel_integral_mul_le {R α r0 : ℝ} (hR : 0 < R) (hr0 : 0 ≤ r0) (hr0R : r0 < R)
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ a b : ℂ, ‖a‖ ≤ r0 → ‖b‖ ≤ r0 →
      ‖a - b‖ * (∫ w in Metric.ball (0:ℂ) R, (‖w - a‖ * ‖w - b‖)⁻¹) ≤ K * ‖a - b‖ ^ α := by
  set S : ℝ := R + r0 with hS
  have hSpos : 0 < S := by rw [hS]; linarith
  refine ⟨16 * Real.pi * 3 ^ α * S ^ (1 - α) / (1 - α), by positivity, ?_⟩
  intro a b ha hb
  by_cases hd0 : ‖a - b‖ = 0
  · rw [hd0, Real.zero_rpow (ne_of_gt hα), zero_mul, mul_zero]
  · have hdpos : 0 < ‖a - b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd0)
    set d : ℝ := ‖a - b‖ with hd
    have hpt : ∀ w : ℂ, (‖w - a‖ * ‖w - b‖)⁻¹ ≤
        4 * 3 ^ α * d ^ (α - 1) * (‖w - a‖ ^ (-1 - α) + ‖w - b‖ ^ (-1 - α)) := by
      intro w
      refine twoPole_pointwise_le hα hα1 hdpos (norm_nonneg _) (norm_nonneg _) ?_ ?_
      · rw [hd]
        calc ‖a - b‖ = ‖(w - b) - (w - a)‖ := by ring_nf
          _ ≤ ‖w - b‖ + ‖w - a‖ := norm_sub_le _ _
          _ = ‖w - a‖ + ‖w - b‖ := by ring
      · rw [hd]
        have h := abs_norm_sub_norm_le (w - a) (w - b)
        rwa [show (w - a) - (w - b) = b - a by ring, norm_sub_rev b a] at h
    have hgi1 : IntegrableOn (fun w : ℂ => ‖w - a‖ ^ (-1 - α)) (Metric.ball (0:ℂ) R) :=
      integrableOn_norm_sub_rpow_ball a 0 (by linarith : (-2:ℝ) < -1 - α)
    have hgi2 : IntegrableOn (fun w : ℂ => ‖w - b‖ ^ (-1 - α)) (Metric.ball (0:ℂ) R) :=
      integrableOn_norm_sub_rpow_ball b 0 (by linarith : (-2:ℝ) < -1 - α)
    have hgint : Integrable (fun w : ℂ => 4 * 3 ^ α * d ^ (α - 1) *
        (‖w - a‖ ^ (-1 - α) + ‖w - b‖ ^ (-1 - α)))
        (volume.restrict (Metric.ball (0:ℂ) R)) :=
      (hgi1.add hgi2).const_mul _
    have hle := integral_mono_of_nonneg
      (μ := volume.restrict (Metric.ball (0:ℂ) R))
      (f := fun w : ℂ => (‖w - a‖ * ‖w - b‖)⁻¹)
      (g := fun w : ℂ => 4 * 3 ^ α * d ^ (α - 1) *
        (‖w - a‖ ^ (-1 - α) + ‖w - b‖ ^ (-1 - α)))
      (Filter.Eventually.of_forall
        (fun w => inv_nonneg.mpr (mul_nonneg (norm_nonneg _) (norm_nonneg _))))
      hgint
      (Filter.Eventually.of_forall hpt)
    have hgval : (∫ w in Metric.ball (0:ℂ) R, 4 * 3 ^ α * d ^ (α - 1) *
        (‖w - a‖ ^ (-1 - α) + ‖w - b‖ ^ (-1 - α)))
        = 4 * 3 ^ α * d ^ (α - 1) *
          ((∫ w in Metric.ball (0:ℂ) R, ‖w - a‖ ^ (-1 - α))
           + (∫ w in Metric.ball (0:ℂ) R, ‖w - b‖ ^ (-1 - α))) := by
      rw [integral_const_mul, integral_add hgi1 hgi2]
    have hbound_a : (∫ w in Metric.ball (0:ℂ) R, ‖w - a‖ ^ (-1 - α))
        ≤ 2 * Real.pi * S ^ (1 - α) / (1 - α) := by
      have hsub : Metric.ball (0:ℂ) R ⊆ Metric.ball a S := by
        intro w hw
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hw
        rw [Metric.mem_ball, dist_eq_norm]
        calc ‖w - a‖ ≤ ‖w‖ + ‖a‖ := norm_sub_le _ _
          _ < R + r0 := by linarith
      have hintbig : IntegrableOn (fun w : ℂ => ‖w - a‖ ^ (-1 - α)) (Metric.ball a S) :=
        integrableOn_norm_sub_rpow_ball a a (by linarith : (-2:ℝ) < -1 - α)
      calc (∫ w in Metric.ball (0:ℂ) R, ‖w - a‖ ^ (-1 - α))
          ≤ ∫ w in Metric.ball a S, ‖w - a‖ ^ (-1 - α) :=
            setIntegral_mono_set hintbig
              (Filter.Eventually.of_forall (fun w => Real.rpow_nonneg (norm_nonneg _) _))
              (Filter.Eventually.of_forall (fun w hw => hsub hw))
        _ = ∫ z in Metric.ball (0:ℂ) S, ‖z‖ ^ (-1 - α) := setIntegral_norm_sub_rpow_ball a
        _ = 2 * Real.pi * S ^ (1 - α) / (1 - α) := by
            rw [Work.CR.Flat.Cauchy.integral_norm_rpow_ball hSpos (by linarith : (-2:ℝ) < -1 - α),
              show (-1 - α) + 2 = 1 - α by ring]
    have hbound_b : (∫ w in Metric.ball (0:ℂ) R, ‖w - b‖ ^ (-1 - α))
        ≤ 2 * Real.pi * S ^ (1 - α) / (1 - α) := by
      have hsub : Metric.ball (0:ℂ) R ⊆ Metric.ball b S := by
        intro w hw
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hw
        rw [Metric.mem_ball, dist_eq_norm]
        calc ‖w - b‖ ≤ ‖w‖ + ‖b‖ := norm_sub_le _ _
          _ < R + r0 := by linarith
      have hintbig : IntegrableOn (fun w : ℂ => ‖w - b‖ ^ (-1 - α)) (Metric.ball b S) :=
        integrableOn_norm_sub_rpow_ball b b (by linarith : (-2:ℝ) < -1 - α)
      calc (∫ w in Metric.ball (0:ℂ) R, ‖w - b‖ ^ (-1 - α))
          ≤ ∫ w in Metric.ball b S, ‖w - b‖ ^ (-1 - α) :=
            setIntegral_mono_set hintbig
              (Filter.Eventually.of_forall (fun w => Real.rpow_nonneg (norm_nonneg _) _))
              (Filter.Eventually.of_forall (fun w hw => hsub hw))
        _ = ∫ z in Metric.ball (0:ℂ) S, ‖z‖ ^ (-1 - α) := setIntegral_norm_sub_rpow_ball b
        _ = 2 * Real.pi * S ^ (1 - α) / (1 - α) := by
            rw [Work.CR.Flat.Cauchy.integral_norm_rpow_ball hSpos (by linarith : (-2:ℝ) < -1 - α),
              show (-1 - α) + 2 = 1 - α by ring]
    have hbound : (∫ w in Metric.ball (0:ℂ) R, (‖w - a‖ * ‖w - b‖)⁻¹)
        ≤ 16 * Real.pi * 3 ^ α * S ^ (1 - α) / (1 - α) * d ^ (α - 1) := by
      calc (∫ w in Metric.ball (0:ℂ) R, (‖w - a‖ * ‖w - b‖)⁻¹)
          ≤ ∫ w in Metric.ball (0:ℂ) R, 4 * 3 ^ α * d ^ (α - 1) *
              (‖w - a‖ ^ (-1 - α) + ‖w - b‖ ^ (-1 - α)) := hle
        _ = 4 * 3 ^ α * d ^ (α - 1) *
              ((∫ w in Metric.ball (0:ℂ) R, ‖w - a‖ ^ (-1 - α))
               + (∫ w in Metric.ball (0:ℂ) R, ‖w - b‖ ^ (-1 - α))) := hgval
        _ ≤ 4 * 3 ^ α * d ^ (α - 1) *
              ((2 * Real.pi * S ^ (1 - α) / (1 - α)) + (2 * Real.pi * S ^ (1 - α) / (1 - α))) :=
              mul_le_mul_of_nonneg_left (add_le_add hbound_a hbound_b) (by positivity)
        _ = 16 * Real.pi * 3 ^ α * S ^ (1 - α) / (1 - α) * d ^ (α - 1) := by ring
    have hdd : d * d ^ (α - 1) = d ^ α := by
      have hx : d ^ ((1:ℝ) + (α - 1)) = d ^ (1:ℝ) * d ^ (α - 1) :=
        Real.rpow_add hdpos 1 (α - 1)
      rw [Real.rpow_one] at hx
      rw [show (1:ℝ) + (α - 1) = α by ring] at hx
      exact hx.symm
    calc d * (∫ w in Metric.ball (0:ℂ) R, (‖w - a‖ * ‖w - b‖)⁻¹)
        ≤ d * (16 * Real.pi * 3 ^ α * S ^ (1 - α) / (1 - α) * d ^ (α - 1)) :=
            mul_le_mul_of_nonneg_left hbound (le_of_lt hdpos)
      _ = 16 * Real.pi * 3 ^ α * S ^ (1 - α) / (1 - α) * d ^ α := by
            rw [show d * (16 * Real.pi * 3 ^ α * S ^ (1 - α) / (1 - α) * d ^ (α - 1))
                = (16 * Real.pi * 3 ^ α * S ^ (1 - α) / (1 - α)) * (d * d ^ (α - 1)) by ring,
              hdd]

end Work.NN.Core
