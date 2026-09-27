import Mathlib
import Submission.Mostow.Interfaces

/-!
# Infrastructure for `Work.Mostow.natMapSurj`

The Poincaré-ball chart `kappa : E n → E n`, `kappa u = u/(1 + tpart u)`, its inverse on the
open unit ball, and elementary lemmas about them.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Metric

noncomputable section

/-- The Poincaré-ball chart `u ↦ u / (1 + tpart u)`, a bijection from `E n = ℍⁿ` onto the
open unit ball of `E n`. -/
def kappa {n : ℕ} (u : E n) : E n := (1 + tpart u)⁻¹ • u

/-- The inverse of the Poincaré-ball chart, `b ↦ 2b/(1 - ‖b‖²)`. -/
def kappaInv {n : ℕ} (b : E n) : E n := (2 / (1 - ‖b‖ ^ 2)) • b

/-- The open unit ball of `E n`. -/
def ball1 (n : ℕ) : Set (E n) := Metric.ball 0 1

/-- The closed unit ball of `E n`. -/
def closedBall1 (n : ℕ) : Set (E n) := Metric.closedBall 0 1

variable {n : ℕ}

lemma tpart_pos (u : E n) : 0 < tpart u := Real.sqrt_pos.2 (by positivity)

lemma one_add_tpart_pos (u : E n) : 0 < 1 + tpart u := by linarith [tpart_pos u]

lemma tpart_sq (u : E n) : tpart u ^ 2 = 1 + ‖u‖ ^ 2 := Real.sq_sqrt (by positivity)

lemma one_le_tpart_surjDefs (u : E n) : 1 ≤ tpart u := by
  have h := tpart_sq u
  nlinarith [norm_nonneg u, tpart_pos u, sq_nonneg (tpart u)]

lemma norm_kappa (u : E n) : ‖kappa u‖ = ‖u‖ / (1 + tpart u) := by
  rw [kappa, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (one_add_tpart_pos u),
    div_eq_inv_mul]

lemma norm_kappa_lt_one (u : E n) : ‖kappa u‖ < 1 := by
  rw [norm_kappa, div_lt_one (one_add_tpart_pos u)]
  have h := tpart_sq u
  nlinarith [norm_nonneg u, one_le_tpart_surjDefs u, sq_nonneg (tpart u)]

lemma kappa_mem_ball1 (u : E n) : kappa u ∈ ball1 n := by
  rw [ball1, Metric.mem_ball, dist_zero_right]
  exact norm_kappa_lt_one u

lemma norm_kappa_sq (u : E n) : ‖kappa u‖ ^ 2 = (tpart u - 1) / (1 + tpart u) := by
  have hsq : ‖u‖ ^ 2 = tpart u ^ 2 - 1 := by rw [tpart_sq]; ring
  have h2 : tpart u ^ 2 - 1 = (tpart u - 1) * (1 + tpart u) := by ring
  rw [norm_kappa, div_pow, hsq, h2,
    div_eq_div_iff (pow_ne_zero 2 (ne_of_gt (one_add_tpart_pos u)))
      (ne_of_gt (one_add_tpart_pos u))]
  ring

lemma one_sub_norm_kappa_sq (u : E n) : 1 - ‖kappa u‖ ^ 2 = 2 / (1 + tpart u) := by
  have h : (0:ℝ) < 1 + tpart u := one_add_tpart_pos u
  rw [norm_kappa_sq, eq_div_iff (ne_of_gt h), sub_mul,
    div_mul_cancel₀ _ (ne_of_gt h)]
  ring

lemma kappaInv_kappa (u : E n) : kappaInv (kappa u) = u := by
  have h : (0:ℝ) < 1 + tpart u := one_add_tpart_pos u
  have h1 : (2:ℝ) / (2 / (1 + tpart u)) = 1 + tpart u := by
    rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)]
  have h2 : (1 + tpart u) * (1 + tpart u)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt h)
  rw [kappaInv, one_sub_norm_kappa_sq, kappa, smul_smul, h1, h2, one_smul]

lemma norm_kappaInv (b : E n) (h : ‖b‖ < 1) : ‖kappaInv b‖ = 2 * ‖b‖ / (1 - ‖b‖ ^ 2) := by
  have hb : (0:ℝ) < 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
  rw [kappaInv, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hb)]
  ring

lemma tpart_kappaInv (b : E n) (h : ‖b‖ < 1) :
    tpart (kappaInv b) = (1 + ‖b‖ ^ 2) / (1 - ‖b‖ ^ 2) := by
  have hb : (0:ℝ) < 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
  have h2 : ‖kappaInv b‖ = 2 * ‖b‖ / (1 - ‖b‖ ^ 2) := norm_kappaInv b h
  have key : 1 + ‖kappaInv b‖ ^ 2 = ((1 + ‖b‖ ^ 2) / (1 - ‖b‖ ^ 2)) ^ 2 := by
    rw [h2, div_pow]
    field_simp
    ring
  rw [tpart, key, Real.sqrt_sq (by positivity)]

lemma one_add_tpart_kappaInv (b : E n) (h : ‖b‖ < 1) :
    1 + tpart (kappaInv b) = 2 / (1 - ‖b‖ ^ 2) := by
  have hb : (0:ℝ) < 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
  rw [tpart_kappaInv b h]
  field_simp
  ring

lemma kappa_kappaInv (b : E n) (h : ‖b‖ < 1) : kappa (kappaInv b) = b := by
  have hb : (0:ℝ) < 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
  have ht : 1 + tpart (kappaInv b) = 2 / (1 - ‖b‖ ^ 2) := one_add_tpart_kappaInv b h
  have hc : (2 / (1 - ‖b‖ ^ 2))⁻¹ * (2 / (1 - ‖b‖ ^ 2)) = 1 :=
    inv_mul_cancel₀ (ne_of_gt (div_pos (by norm_num) hb))
  rw [kappa, ht, kappaInv, smul_smul, hc, one_smul]

lemma norm_sub_sphere (b ξ : E n) (hξ : ξ ∈ Sph n) : ‖b - ξ‖ ^ 2 = ‖b‖ ^ 2 - 2 * inner ℝ b ξ + 1 := by
  have hnormξ : ‖ξ‖ = 1 := by
    rw [Sph, Metric.mem_sphere, dist_eq_norm] at hξ; simpa using hξ
  rw [norm_sub_sq_real, hnormξ]
  ring

lemma busemann_kappaInv (b ξ : E n) (h : ‖b‖ < 1) (hξ : ξ ∈ Sph n) :
    busemann ξ (kappaInv b) = 2 * Real.log ‖b - ξ‖ - Real.log (1 - ‖b‖ ^ 2) := by
  have hb : (0:ℝ) < 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
  have ht : tpart (kappaInv b) = (1 + ‖b‖ ^ 2) / (1 - ‖b‖ ^ 2) := tpart_kappaInv b h
  have hi : inner ℝ (kappaInv b) ξ = (2 / (1 - ‖b‖ ^ 2)) * inner ℝ b ξ := by
    rw [kappaInv, real_inner_smul_left]
  have hkey : tpart (kappaInv b) - inner ℝ (kappaInv b) ξ = ‖b - ξ‖ ^ 2 / (1 - ‖b‖ ^ 2) := by
    rw [ht, hi, norm_sub_sphere b ξ hξ]
    field_simp
    ring
  have hsp : (0:ℝ) < ‖b - ξ‖ := by
    have hnormξ : ‖ξ‖ = 1 := by
      rw [Sph, Metric.mem_sphere, dist_eq_norm] at hξ; simpa using hξ
    have hne : b ≠ ξ := by
      intro e; rw [e, hnormξ] at h; exact lt_irrefl _ h
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  rw [busemann, hkey, Real.log_div (by positivity) (ne_of_gt hb), Real.log_pow]
  push_cast
  ring

/-- The chart identity: `tpart u - ⟪u,ξ⟫ = ‖κ u - ξ‖²/(1 - ‖κ u‖²)` for `ξ` on the unit sphere. -/
lemma chart_id (u ξ : E n) (hξ : ξ ∈ Sph n) :
    tpart u - inner ℝ u ξ = ‖kappa u - ξ‖ ^ 2 / (1 - ‖kappa u‖ ^ 2) := by
  have hb : ‖kappa u‖ < 1 := norm_kappa_lt_one u
  have hpos : (0:ℝ) < 1 - ‖kappa u‖ ^ 2 := by nlinarith [norm_nonneg (kappa u)]
  have hu : kappaInv (kappa u) = u := kappaInv_kappa u
  have h1 : tpart u = (1 + ‖kappa u‖ ^ 2) / (1 - ‖kappa u‖ ^ 2) := by
    have h := tpart_kappaInv (kappa u) hb
    rwa [hu] at h
  have h2 : inner ℝ u ξ = (2 / (1 - ‖kappa u‖ ^ 2)) * inner ℝ (kappa u) ξ := by
    conv_lhs => rw [← hu]
    rw [kappaInv, real_inner_smul_left]
  rw [h1, h2, norm_sub_sphere (kappa u) ξ hξ]
  field_simp
  ring

lemma norm_eq_one_of_mem_Sph {x : E n} (hx : x ∈ Sph n) : ‖x‖ = 1 := by
  rw [Sph, Metric.mem_sphere, dist_eq_norm, sub_zero] at hx; exact hx

lemma mem_Sph_of_norm_eq_one {x : E n} (hx : ‖x‖ = 1) : x ∈ Sph n := by
  rw [Sph, Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hx

lemma kappa_injective : Function.Injective (kappa : E n → E n) :=
  fun a b h => by rw [← kappaInv_kappa a, ← kappaInv_kappa b, h]

lemma continuous_tpart_surjDefs : Continuous (fun u : E n => tpart u) := by
  unfold tpart
  exact Real.continuous_sqrt.comp (by fun_prop)

lemma continuous_kappa : Continuous (fun u : E n => kappa u) := by
  have h1 : Continuous (fun u : E n => (1 + tpart u)⁻¹) :=
    Continuous.inv₀ (continuous_const.add continuous_tpart_surjDefs)
      (fun u => ne_of_gt (one_add_tpart_pos u))
  exact h1.smul continuous_id

lemma continuousOn_kappaInv : ContinuousOn (fun b : E n => kappaInv b) (ball1 n) := by
  rw [ball1]
  have hne : ∀ b ∈ Metric.ball (0 : E n) 1, (1 - ‖b‖ ^ 2 : ℝ) ≠ 0 := by
    intro b hb
    rw [Metric.mem_ball, dist_zero_right] at hb
    intro h
    have h2 : ‖b‖ ^ 2 = 1 := by linarith
    nlinarith [norm_nonneg b, hb, h2]
  have h1 : ContinuousOn (fun b : E n => (1 - ‖b‖ ^ 2)⁻¹) (Metric.ball (0 : E n) 1) :=
    ContinuousOn.inv₀ (continuous_const.sub (continuous_norm.pow 2)).continuousOn hne
  have h2 : ContinuousOn (fun b : E n => (2 * (1 - ‖b‖ ^ 2)⁻¹)) (Metric.ball (0 : E n) 1) :=
    continuousOn_const.mul h1
  refine (h2.smul continuousOn_id).congr ?_
  intro b _
  show (2 / (1 - ‖b‖ ^ 2)) • b = (2 * (1 - ‖b‖ ^ 2)⁻¹) • b
  rw [div_eq_mul_inv]

/-- The Busemann function at a point given in the Poincaré-ball chart. -/
lemma busemann_chart (z ξ : E n) (hξ : ξ ∈ Sph n) :
    busemann ξ z = 2 * Real.log ‖kappa z - ξ‖ - Real.log (1 - ‖kappa z‖ ^ 2) := by
  have h := busemann_kappaInv (kappa z) ξ (norm_kappa_lt_one z) hξ
  rwa [kappaInv_kappa z] at h

/-- `ξ ↦ log ‖b - ξ‖` is integrable against any finite measure supported on the sphere, for `b`
inside the open unit ball. -/
lemma integrable_log_dist (ν : Measure (E n)) [IsFiniteMeasure ν] (hsupp : ν (Sph n)ᶜ = 0)
    {b : E n} (hb : ‖b‖ < 1) : Integrable (fun ξ => Real.log ‖b - ξ‖) ν := by
  have hInt : IntegrableOn (fun ξ : E n => Real.log ‖b - ξ‖) (Sph n) ν := by
    refine ContinuousOn.integrableOn_compact (isCompact_sphere (0 : E n) 1) ?_
    refine ContinuousOn.log ?_ ?_
    · exact (continuous_const.sub continuous_id).continuousOn.norm
    · intro ξ hξ h
      have hξ1 : ‖ξ‖ = 1 := norm_eq_one_of_mem_Sph hξ
      have h2 : b - ξ = 0 := norm_eq_zero.mp h
      have h1 : b = ξ := sub_eq_zero.mp h2
      rw [h1, hξ1] at hb
      exact lt_irrefl _ hb
  have hνeq : ν.restrict (Sph n) = ν := Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupp)
  change Integrable (fun ξ => Real.log ‖b - ξ‖) (ν.restrict (Sph n)) at hInt
  rwa [hνeq] at hInt

/-- The barycentre functional computed in the Poincaré-ball chart. -/
lemma baryFun_chart (ν : Measure (E n)) [IsFiniteMeasure ν] (hν : ν Set.univ = 1)
    (hsupp : ν (Sph n)ᶜ = 0) (y : E n) :
    baryFun ν y = 2 * ∫ ξ, Real.log ‖kappa y - ξ‖ ∂ν - Real.log (1 - ‖kappa y‖ ^ 2) := by
  have hb : ‖kappa y‖ < 1 := norm_kappa_lt_one y
  have hInt : Integrable (fun ξ => Real.log ‖kappa y - ξ‖) ν := integrable_log_dist ν hsupp hb
  have hae : (fun ξ => busemann ξ y) =ᵐ[ν]
      (fun ξ => 2 * Real.log ‖kappa y - ξ‖ - Real.log (1 - ‖kappa y‖ ^ 2)) := by
    filter_upwards [ae_iff.mpr hsupp] with ξ hξ
    exact busemann_chart y ξ hξ
  rw [baryFun, integral_congr_ae hae,
    integral_sub (hInt.const_mul 2) (integrable_const _),
    integral_const_mul, integral_const]
  simp [Measure.real, hν]

end

end Work.Mostow
