/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weighted endpoint-value estimate at the right endpoint

The target of this file is the *weighted* (by `thEta θ = sin(2θ)^{-η}`, `η = 99/100`)
endpoint-value bound

  `F² ≤ 2 t^{3+η} ∫_{Iθ} (f'')² thEta + 100 t^{η-1} ∫_{Iθ} f² thEta`

for `F = lim_{x → (π/2)⁻} f x`, `f` of class `C²` on `(0, π/2)`, `(f'')² thEta` and `f² thEta`
integrable there, and every `t ∈ (0, π/2)`.

Proof: the *left*-endpoint version `endpointParamLeftW_aux` (proved below with the same
constants) is transported across the measure preserving involution `θ ↦ π/2 - θ`, which leaves
`thEta` invariant (`sin(2(π/2-x)) = sin(2x)`) and turns the limit at `(π/2)⁻` into a limit at
`0⁺` (all the reflection facts are bundled in `EndpointValues.reflectFacts`), exactly as in
`EndpointValues.endpointParamRight`.

The left-endpoint proof is the weighted version of `EndpointValues.endpointParamLeft`:

* the reproducing formula `F = ∫_0^t η f'' - ∫_0^t η'' f` of `EndpointValues.twoIbpEtaT`
  (test function `η_t(x) = x (1 - x/t)³`) is combined with the *weighted* Cauchy–Schwarz
  inequality `weighted_cs_integral` (a genuine Mathlib gap), applied to
  `η = (η/√thEta)·√thEta` and to `f'' = (f''·√thEta)/√thEta`;
* the two integral bounds against the weight (`1/thEta = sin(2x)^η` on `(0, π/2)`) are
  `∫_0^t η²/thEta ≤ t^{3+η}` and `∫_0^t (η'')²/thEta ≤ 50 t^{η-1}`;
* `2|AB| ≤ 2A² + 2B²` then produces exactly the constants `2` and `100` of the statement.

The file also exports, for the sibling tasks of this directory, the general weighted
Cauchy–Schwarz `weighted_cs_integral`, the reflection invariance `thEta_pi_div_two_sub`, the
pointwise/integral bounds `etaT_sq_div_thEta_le`, `etaT''_sq_div_thEta_le`,
`integral_etaT_sq_div_thEta_le`, `integral_etaT''_sq_div_thEta_le`, the `MemLp` infrastructures
`continuousOn_*`, `integrableOn_etaT_sq_div_thEta`, `integrableOn_etaT''_sq_div_thEta`, and the
**left-endpoint** version `endpointParamLeftW_aux` (which turns `endpointParamRightW` into a
one-line reflection argument, and which is also the statement of the sibling task
`TVRed/endpointParamLeftW`, up to the name).
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.EllipticEst.Core.thEtaFacts
import Submission.Work.EllipticEst.Core.i0Aux.EndpointDefs
import Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.twoIbpEtaT
import Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.etaTFacts
import Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.derivBoundedNearLeft
import Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.reflectFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 0. Elementary facts about the weight `thEta` -/

/-- The weight `thEta` is invariant under the reflection `x ↦ π/2 - x`. -/
theorem thEta_pi_div_two_sub (x : ℝ) :
    Work.FTS.EllipticEst.thEta (Real.pi / 2 - x) = Work.FTS.EllipticEst.thEta x := by
  simp only [Work.FTS.EllipticEst.thEta]
  rw [show 2 * (Real.pi / 2 - x) = Real.pi - 2 * x by ring, Real.sin_pi_sub]

/-- `thEta` is positive on `(0, t)` for `t < π/2`. -/
theorem thEta_pos_of_mem {t x : ℝ} (hta : t < Real.pi / 2) (hx : x ∈ Set.Ioo 0 t) :
    0 < Work.FTS.EllipticEst.thEta x :=
  Work.EllipticEst.Core.thEtaFacts.1 x ⟨hx.1, lt_trans hx.2 hta⟩

/-- On `(0, t)`, `t < π/2`, the inverse of the weight is the power `sin(2x)^η`. -/
theorem inv_thEta_of_mem {t x : ℝ} (hta : t < Real.pi / 2) (hx : x ∈ Set.Ioo 0 t) :
    (Work.FTS.EllipticEst.thEta x)⁻¹ = (Real.sin (2 * x)) ^ Work.Spaces.eta :=
  Work.EllipticEst.Core.thEtaFacts.2.2.1 x ⟨hx.1, lt_trans hx.2 hta⟩

/-- `thEta` is nonnegative on the open angular interval. -/
theorem thEta_nonneg_of_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 ≤ Work.FTS.EllipticEst.thEta x :=
  (Work.EllipticEst.Core.thEtaFacts.1 x hx).le

/-! ## 1. Continuity of the pieces entering the weighted Cauchy–Schwarz -/

theorem continuous_etaT (t : ℝ) : Continuous (etaT t) := by
  unfold etaT; fun_prop

theorem continuous_etaT'' (t : ℝ) : Continuous (etaT'' t) := by
  unfold etaT''; fun_prop

/-- `√thEta` is continuous on `(0, t)`, `t < π/2`. -/
theorem continuousOn_sqrt_thEta {t : ℝ} (hta : t < Real.pi / 2) :
    ContinuousOn (fun x : ℝ => Real.sqrt (Work.FTS.EllipticEst.thEta x)) (Set.Ioo 0 t) :=
  (Work.EllipticEst.Core.thEtaFacts.2.2.2.mono
    (fun _ hx => ⟨hx.1, lt_trans hx.2 hta⟩)).sqrt

/-- `1/√thEta` is continuous on `(0, t)`, `t < π/2`. -/
theorem continuousOn_inv_sqrt_thEta {t : ℝ} (hta : t < Real.pi / 2) :
    ContinuousOn (fun x : ℝ => (Real.sqrt (Work.FTS.EllipticEst.thEta x))⁻¹) (Set.Ioo 0 t) := by
  refine ContinuousOn.inv₀ (continuousOn_sqrt_thEta hta) ?_
  intro x hx
  exact ne_of_gt (Real.sqrt_pos_of_pos (thEta_pos_of_mem hta hx))

/-- `η/√thEta` is continuous on `(0, t)`. -/
theorem continuousOn_etaT_div_sqrt_thEta (t : ℝ) (hta : t < Real.pi / 2) :
    ContinuousOn (fun x : ℝ => etaT t x / Real.sqrt (Work.FTS.EllipticEst.thEta x))
      (Set.Ioo 0 t) := by
  refine ContinuousOn.div ((continuous_etaT t).continuousOn) (continuousOn_sqrt_thEta hta) ?_
  intro x hx
  exact ne_of_gt (Real.sqrt_pos_of_pos (thEta_pos_of_mem hta hx))

/-- `η''/√thEta` is continuous on `(0, t)`. -/
theorem continuousOn_etaT''_div_sqrt_thEta (t : ℝ) (hta : t < Real.pi / 2) :
    ContinuousOn (fun x : ℝ => etaT'' t x / Real.sqrt (Work.FTS.EllipticEst.thEta x))
      (Set.Ioo 0 t) := by
  refine ContinuousOn.div ((continuous_etaT'' t).continuousOn) (continuousOn_sqrt_thEta hta) ?_
  intro x hx
  exact ne_of_gt (Real.sqrt_pos_of_pos (thEta_pos_of_mem hta hx))

/-! ## 2. Pointwise bounds for the test function against the weight -/

/-- `η_t(x)²/thEta x ≤ 2^η t^η x²` on `(0, t)`.  The two factors are `η_t(x)² ≤ x²` and
`1/thEta x = sin(2x)^η ≤ (2x)^η = 2^η x^η ≤ 2^η t^η`. -/
theorem etaT_sq_div_thEta_le (t x : ℝ) (ht : 0 < t) (hta : t < Real.pi / 2)
    (hx : x ∈ Set.Ioo 0 t) :
    (etaT t x) ^ 2 / Work.FTS.EllipticEst.thEta x
      ≤ 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta * x ^ 2 := by
  have hxpi : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hx.1, lt_trans hx.2 hta⟩
  have hsin_pos : 0 < Real.sin (2 * x) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, hta])
  have hsinle : Real.sin (2 * x) ≤ 2 * x := Real.sin_le (by linarith [hx.1])
  have hinv : (Work.FTS.EllipticEst.thEta x)⁻¹
      = (Real.sin (2 * x)) ^ Work.Spaces.eta := inv_thEta_of_mem hta hx
  have hthpos : 0 < Work.FTS.EllipticEst.thEta x := thEta_pos_of_mem hta hx
  have h1 : (etaT t x) ^ 2 ≤ x ^ 2 := by
    have hsq : (etaT t x) ^ 2 = x ^ 2 * (1 - x / t) ^ 6 := by
      simp only [etaT]; ring
    have hu0 : 0 ≤ 1 - x / t := by
      have : x / t ≤ 1 := (div_le_one ht).mpr hx.2.le
      linarith
    have hu1 : 1 - x / t ≤ 1 := by
      have : 0 ≤ x / t := div_nonneg hx.1.le ht.le
      linarith
    have hu6 : (1 - x / t) ^ 6 ≤ 1 := pow_le_one₀ hu0 hu1
    calc (etaT t x) ^ 2 = x ^ 2 * (1 - x / t) ^ 6 := hsq
      _ ≤ x ^ 2 * 1 := mul_le_mul_of_nonneg_left hu6 (sq_nonneg x)
      _ = x ^ 2 := by ring
  have h2 : (Work.FTS.EllipticEst.thEta x)⁻¹
      ≤ 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta := by
    rw [hinv]
    calc (Real.sin (2 * x)) ^ Work.Spaces.eta ≤ (2 * x) ^ Work.Spaces.eta :=
          Real.rpow_le_rpow hsin_pos.le hsinle Work.Spaces.eta_pos.le
      _ = 2 ^ Work.Spaces.eta * x ^ Work.Spaces.eta :=
          Real.mul_rpow (by norm_num) hx.1.le
      _ ≤ 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
          exact Real.rpow_le_rpow hx.1.le hx.2.le Work.Spaces.eta_pos.le
  rw [div_eq_mul_inv]
  calc (etaT t x) ^ 2 * (Work.FTS.EllipticEst.thEta x)⁻¹
      ≤ x ^ 2 * (2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta) :=
        mul_le_mul h1 h2 (inv_nonneg.mpr hthpos.le) (sq_nonneg x)
    _ = 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta * x ^ 2 := by ring

/-- `η_t''(x)²/thEta x ≤ (36/t²)(2x)^η` on `(0, t)`: `(η_t'')² ≤ 36/t²` and
`1/thEta x = sin(2x)^η ≤ (2x)^η`. -/
theorem etaT''_sq_div_thEta_le (t x : ℝ) (ht : 0 < t) (hta : t < Real.pi / 2)
    (hx : x ∈ Set.Ioo 0 t) :
    (etaT'' t x) ^ 2 / Work.FTS.EllipticEst.thEta x
      ≤ (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta := by
  have hsin_pos : 0 < Real.sin (2 * x) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, hta])
  have hsinle : Real.sin (2 * x) ≤ 2 * x := Real.sin_le (by linarith [hx.1])
  have hinv : (Work.FTS.EllipticEst.thEta x)⁻¹
      = (Real.sin (2 * x)) ^ Work.Spaces.eta := inv_thEta_of_mem hta hx
  have hthpos : 0 < Work.FTS.EllipticEst.thEta x := thEta_pos_of_mem hta hx
  have h1 : (etaT'' t x) ^ 2 ≤ 36 / t ^ 2 := by
    have hsq : (etaT'' t x) ^ 2
        = (36 / t ^ 2) * ((1 - x / t) ^ 2 * (2 * (x / t) - 1) ^ 2) := by
      simp only [etaT'']; ring
    have hu0 : 0 ≤ 1 - x / t := by
      have hxt : x / t ≤ 1 := (div_le_one ht).mpr hx.2.le
      linarith
    have hu1 : 1 - x / t ≤ 1 := by
      have : 0 ≤ x / t := div_nonneg hx.1.le ht.le
      linarith
    have hu2 : (1 - x / t) ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one _).mpr (abs_le.mpr ⟨by linarith, hu1⟩)
    have hv0 : -1 ≤ 2 * (x / t) - 1 := by
      have : 0 ≤ x / t := div_nonneg hx.1.le ht.le
      linarith
    have hv1 : 2 * (x / t) - 1 ≤ 1 := by
      have : x / t ≤ 1 := (div_le_one ht).mpr hx.2.le
      linarith
    have hv2 : (2 * (x / t) - 1) ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one _).mpr (abs_le.mpr ⟨hv0, hv1⟩)
    have hprod : (1 - x / t) ^ 2 * (2 * (x / t) - 1) ^ 2 ≤ 1 :=
      calc (1 - x / t) ^ 2 * (2 * (x / t) - 1) ^ 2 ≤ 1 * 1 :=
            mul_le_mul hu2 hv2 (sq_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    calc (etaT'' t x) ^ 2
        = (36 / t ^ 2) * ((1 - x / t) ^ 2 * (2 * (x / t) - 1) ^ 2) := hsq
      _ ≤ (36 / t ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left hprod (div_nonneg (by norm_num) (sq_nonneg t))
      _ = 36 / t ^ 2 := by ring
  have h2 : (Work.FTS.EllipticEst.thEta x)⁻¹ ≤ (2 * x) ^ Work.Spaces.eta := by
    rw [hinv]
    exact Real.rpow_le_rpow hsin_pos.le hsinle Work.Spaces.eta_pos.le
  rw [div_eq_mul_inv]
  calc (etaT'' t x) ^ 2 * (Work.FTS.EllipticEst.thEta x)⁻¹
      ≤ (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta :=
        mul_le_mul h1 h2 (inv_nonneg.mpr hthpos.le) (by positivity)

/-! ## 3. Weighted Cauchy–Schwarz -/

/-- **Weighted Cauchy–Schwarz.**  For `w > 0` on `s`, if `u/√w` and `v·√w` are square
integrable on `s`, then `(∫_s u v)² ≤ (∫_s u²/w)·(∫_s v² w)`. -/
theorem weighted_cs_integral {u v w : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hw : ∀ x ∈ s, 0 < w x)
    (hu : MemLp (fun x : ℝ => u x / Real.sqrt (w x)) 2 (volume.restrict s))
    (hv : MemLp (fun x : ℝ => v x * Real.sqrt (w x)) 2 (volume.restrict s)) :
    (∫ x in s, u x * v x) ^ 2
      ≤ (∫ x in s, (u x) ^ 2 / w x) * (∫ x in s, (v x) ^ 2 * w x) := by
  have hcs := Work.Spaces.cs_integral hu hv
  have e1 : (∫ x in s, (u x / Real.sqrt (w x)) * (v x * Real.sqrt (w x)))
      = ∫ x in s, u x * v x := by
    refine setIntegral_congr_fun hs (fun x hx => ?_)
    have hne : Real.sqrt (w x) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos (hw x hx))
    field_simp
  have e2 : (∫ x in s, (u x / Real.sqrt (w x)) ^ 2) = ∫ x in s, (u x) ^ 2 / w x := by
    refine setIntegral_congr_fun hs (fun x hx => ?_)
    rw [div_pow, Real.sq_sqrt (le_of_lt (hw x hx))]
  have e3 : (∫ x in s, (v x * Real.sqrt (w x)) ^ 2) = ∫ x in s, (v x) ^ 2 * w x := by
    refine setIntegral_congr_fun hs (fun x hx => ?_)
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hw x hx))]
  rwa [e1, e2, e3] at hcs

/-! ## 4. Integrability of the test function against the weight -/

/-- `η_t²/thEta` is integrable on `(0, t)`. -/
theorem integrableOn_etaT_sq_div_thEta (t : ℝ) (ht : 0 < t) (hta : t < Real.pi / 2) :
    IntegrableOn (fun x : ℝ => (etaT t x) ^ 2 / Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 t) := by
  have hcont : ContinuousOn (fun x : ℝ => (etaT t x) ^ 2 / Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 t) := by
    refine ContinuousOn.div (((continuous_etaT t).pow 2).continuousOn)
      (Work.EllipticEst.Core.thEtaFacts.2.2.2.mono
        (fun x hx => ⟨hx.1, lt_trans hx.2 hta⟩)) ?_
    intro x hx
    exact ne_of_gt (thEta_pos_of_mem hta hx)
  have hgint : IntegrableOn (fun x : ℝ => 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta * x ^ 2)
      (Set.Ioo 0 t) := by
    have h2 : IntegrableOn (fun x : ℝ => x ^ 2) (Set.Ioo 0 t) :=
      ((continuous_id.pow 2).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    exact (show Integrable (fun x : ℝ => x ^ 2) (volume.restrict (Set.Ioo 0 t)) from
      h2).const_mul _
  refine Integrable.mono' hgint (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (thEta_pos_of_mem hta hx).le)]
  exact etaT_sq_div_thEta_le t x ht hta hx

/-- `η_t''²/thEta` is integrable on `(0, t)`. -/
theorem integrableOn_etaT''_sq_div_thEta (t : ℝ) (ht : 0 < t) (hta : t < Real.pi / 2) :
    IntegrableOn (fun x : ℝ => (etaT'' t x) ^ 2 / Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 t) := by
  have hcont : ContinuousOn (fun x : ℝ => (etaT'' t x) ^ 2 / Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 t) := by
    refine ContinuousOn.div (((continuous_etaT'' t).pow 2).continuousOn)
      (Work.EllipticEst.Core.thEtaFacts.2.2.2.mono
        (fun x hx => ⟨hx.1, lt_trans hx.2 hta⟩)) ?_
    intro x hx
    exact ne_of_gt (thEta_pos_of_mem hta hx)
  have hgcont : ContinuousOn (fun x : ℝ => (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta)
      (Set.Icc 0 t) := by
    refine ContinuousOn.const_mul ?_ _
    refine ContinuousOn.rpow_const (by fun_prop) ?_
    intro x _
    exact Or.inr Work.Spaces.eta_pos.le
  have hgint : IntegrableOn (fun x : ℝ => (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta)
      (Set.Ioo 0 t) := (hgcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  refine Integrable.mono' hgint (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (thEta_pos_of_mem hta hx).le)]
  exact etaT''_sq_div_thEta_le t x ht hta hx

/-! ## 5. The two integral bounds against the weight -/

/-- `∫_0^t η_t²/thEta ≤ t^{3+η}`. -/
theorem integral_etaT_sq_div_thEta_le (t : ℝ) (ht : 0 < t) (hta : t < Real.pi / 2) :
    ∫ x in Set.Ioo 0 t, (etaT t x) ^ 2 / Work.FTS.EllipticEst.thEta x
      ≤ t ^ (3 + Work.Spaces.eta) := by
  have hgint : IntegrableOn (fun x : ℝ => 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta * x ^ 2)
      (Set.Ioo 0 t) := by
    have h2 : IntegrableOn (fun x : ℝ => x ^ 2) (Set.Ioo 0 t) :=
      ((continuous_id.pow 2).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    exact (show Integrable (fun x : ℝ => x ^ 2) (volume.restrict (Set.Ioo 0 t)) from
      h2).const_mul _
  have hmono : ∫ x in Set.Ioo 0 t, (etaT t x) ^ 2 / Work.FTS.EllipticEst.thEta x
      ≤ ∫ x in Set.Ioo 0 t, 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta * x ^ 2 :=
    integral_mono_ae (integrableOn_etaT_sq_div_thEta t ht hta) hgint (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact etaT_sq_div_thEta_le t x ht hta hx)
  have hgval : ∫ x in Set.Ioo 0 t, 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta * x ^ 2
      = 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta * (t ^ 3 / 3) := by
    rw [MeasureTheory.integral_const_mul,
      EndpointValues.setIntegral_Ioo_eq_intervalIntegral (fun x : ℝ => x ^ 2) ht.le, integral_pow]
    norm_num
  rw [hgval] at hmono
  refine hmono.trans ?_
  have hexp : t ^ (3 + Work.Spaces.eta) = t ^ Work.Spaces.eta * t ^ 3 := by
    rw [show (3 : ℝ) + Work.Spaces.eta = Work.Spaces.eta + 3 by ring,
      Real.rpow_add ht (Work.Spaces.eta) (3 : ℝ)]
    norm_num [Real.rpow_natCast]
  rw [hexp]
  have h3 : (2 : ℝ) ^ Work.Spaces.eta / 3 ≤ 1 := by
    have h' : (2 : ℝ) ^ Work.Spaces.eta ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) Work.Spaces.eta_lt_one.le
    rw [Real.rpow_one] at h'
    exact le_trans (div_le_div_of_nonneg_right h' (by norm_num)) (by norm_num)
  have hp : 0 ≤ t ^ Work.Spaces.eta * t ^ 3 :=
    mul_nonneg (Real.rpow_nonneg ht.le _) (by positivity)
  calc (2 : ℝ) ^ Work.Spaces.eta * t ^ Work.Spaces.eta * (t ^ 3 / 3)
      = ((2 : ℝ) ^ Work.Spaces.eta / 3) * (t ^ Work.Spaces.eta * t ^ 3) := by ring
    _ ≤ 1 * (t ^ Work.Spaces.eta * t ^ 3) := mul_le_mul_of_nonneg_right h3 hp
    _ = t ^ Work.Spaces.eta * t ^ 3 := one_mul _

/-- `∫_0^t η_t''²/thEta ≤ 50 t^{η-1}`. -/
theorem integral_etaT''_sq_div_thEta_le (t : ℝ) (ht : 0 < t) (hta : t < Real.pi / 2) :
    ∫ x in Set.Ioo 0 t, (etaT'' t x) ^ 2 / Work.FTS.EllipticEst.thEta x
      ≤ 50 * t ^ (Work.Spaces.eta - 1) := by
  have hgcont : ContinuousOn (fun x : ℝ => (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta)
      (Set.Icc 0 t) := by
    refine ContinuousOn.const_mul ?_ _
    refine ContinuousOn.rpow_const (by fun_prop) ?_
    intro x _
    exact Or.inr Work.Spaces.eta_pos.le
  have hgint : IntegrableOn (fun x : ℝ => (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta)
      (Set.Ioo 0 t) := (hgcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  have hmono : ∫ x in Set.Ioo 0 t, (etaT'' t x) ^ 2 / Work.FTS.EllipticEst.thEta x
      ≤ ∫ x in Set.Ioo 0 t, (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta :=
    integral_mono_ae (integrableOn_etaT''_sq_div_thEta t ht hta) hgint (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact etaT''_sq_div_thEta_le t x ht hta hx)
  have hxpow : ∫ x in Set.Ioo 0 t, x ^ Work.Spaces.eta
      = t ^ (Work.Spaces.eta + 1) / (Work.Spaces.eta + 1) := by
    rw [EndpointValues.setIntegral_Ioo_eq_intervalIntegral (fun x : ℝ => x ^ Work.Spaces.eta) ht.le,
      integral_rpow (Or.inl (by linarith [Work.Spaces.eta_pos]))]
    rw [Real.zero_rpow (by linarith [Work.Spaces.eta_pos] : Work.Spaces.eta + 1 ≠ 0), sub_zero]
  have hmul : ∫ x in Set.Ioo 0 t, (2 * x) ^ Work.Spaces.eta
      = 2 ^ Work.Spaces.eta * ∫ x in Set.Ioo 0 t, x ^ Work.Spaces.eta := by
    rw [← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioo
      (fun x hx => Real.mul_rpow (by norm_num) hx.1.le)
  have hgval : ∫ x in Set.Ioo 0 t, (36 / t ^ 2) * (2 * x) ^ Work.Spaces.eta
      = 36 * 2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta) * t ^ (Work.Spaces.eta - 1) := by
    rw [MeasureTheory.integral_const_mul, hmul, hxpow]
    have ht2 : t ^ (Work.Spaces.eta + 1) = t ^ (Work.Spaces.eta - 1) * t ^ 2 := by
      rw [show Work.Spaces.eta + 1 = (Work.Spaces.eta - 1) + 2 by ring,
        Real.rpow_add ht (Work.Spaces.eta - 1) (2 : ℝ)]
      norm_num [Real.rpow_natCast]
    rw [ht2]
    field_simp
    ring
  rw [hgval] at hmono
  refine hmono.trans ?_
  have hcoef : (36 : ℝ) * (2 : ℝ) ^ Work.Spaces.eta / (1 + Work.Spaces.eta) ≤ 50 := by
    have h2 : (2 : ℝ) ^ Work.Spaces.eta ≤ 2 := by
      have h' : (2 : ℝ) ^ Work.Spaces.eta ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) Work.Spaces.eta_lt_one.le
      rwa [Real.rpow_one] at h'
    have hden : (1 : ℝ) + Work.Spaces.eta = 199 / 100 := by
      rw [Work.Spaces.eta]; norm_num
    rw [hden]
    calc (36 : ℝ) * (2 : ℝ) ^ Work.Spaces.eta / (199 / 100)
          ≤ (36 : ℝ) * 2 / (199 / 100) := by
          refine div_le_div_of_nonneg_right ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 50 := by norm_num
  have ht0 : 0 ≤ t ^ (Work.Spaces.eta - 1) := Real.rpow_nonneg ht.le _
  calc (36 : ℝ) * (2 : ℝ) ^ Work.Spaces.eta / (1 + Work.Spaces.eta) * t ^ (Work.Spaces.eta - 1)
      ≤ 50 * t ^ (Work.Spaces.eta - 1) := mul_le_mul_of_nonneg_right hcoef ht0

/-! ## 6. The weighted endpoint-value estimate at the left endpoint -/

/-- **The weighted endpoint-value estimate at the left endpoint.**  For `F = lim_{x → 0⁺} f x`,
`f` of class `C²` on `(0, π/2)` with `(f'')² thEta` and `f² thEta` integrable there, and every
`t ∈ (0, π/2)`:

  `F² ≤ 2 t^{3+η} ∫_{Iθ} (f'')² thEta + 100 t^{η-1} ∫_{Iθ} f² thEta`. -/
theorem endpointParamLeftW_aux (f : ℝ → ℝ) (F t : ℝ) (ht : 0 < t) (hta : t < Real.pi / 2)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hlim : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F))
    (h2 : MeasureTheory.IntegrableOn
      (fun x : ℝ => (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 (Real.pi / 2)))
    (h1 : MeasureTheory.IntegrableOn
      (fun x : ℝ => (f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 (Real.pi / 2))) :
    F ^ 2 ≤ 2 * t ^ (3 + Work.Spaces.eta) *
        (∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      + 100 * t ^ (Work.Spaces.eta - 1) *
        (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * Work.FTS.EllipticEst.thEta x) := by
  have hsub : Set.Ioo (0 : ℝ) t ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨hx.1, lt_trans hx.2 hta⟩
  have h2t := h2.mono_set hsub
  have h1t := h1.mono_set hsub
  -- continuity of the two integrands on `(0, t)`
  have hcont2 : ContinuousOn (deriv (deriv f)) (Set.Ioo 0 t) := by
    have h1' : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
      hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact (h1'.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsub
  have hcont0 : ContinuousOn f (Set.Ioo 0 t) := (hf.continuousOn).mono hsub
  -- the squares are integrable (the weight is `≥ 1`)
  have h2sq : IntegrableOn (fun x : ℝ => (deriv (deriv f) x) ^ 2) (Set.Ioo 0 t) := by
    refine Integrable.mono' h2t ((hcont2.pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (deriv (deriv f) x) ^ 2 = (deriv (deriv f) x) ^ 2 * 1 := by ring
      _ ≤ (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x :=
          mul_le_mul_of_nonneg_left
            (Work.EllipticEst.Core.thEtaFacts.2.1 x (hsub hx)) (sq_nonneg _)
  have h1sq : IntegrableOn (fun x : ℝ => (f x) ^ 2) (Set.Ioo 0 t) := by
    refine Integrable.mono' h1t ((hcont0.pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (f x) ^ 2 = (f x) ^ 2 * 1 := by ring
      _ ≤ (f x) ^ 2 * Work.FTS.EllipticEst.thEta x :=
          mul_le_mul_of_nonneg_left
            (Work.EllipticEst.Core.thEtaFacts.2.1 x (hsub hx)) (sq_nonneg _)
  -- `L¹` integrability from `L²` integrability
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 t) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hf2L1 : IntegrableOn (deriv (deriv f)) (Set.Ioo 0 t) := by
    refine Integrable.mono' (h2sq.add hconst) (hcont2.aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x _
    show |deriv (deriv f) x| ≤ (deriv (deriv f) x) ^ 2 + 1
    exact EndpointValues.abs_le_sq_add_one_aux _
  have hfL1 : IntegrableOn f (Set.Ioo 0 t) := by
    refine Integrable.mono' (h1sq.add hconst) (hcont0.aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x _
    show |f x| ≤ (f x) ^ 2 + 1
    exact EndpointValues.abs_le_sq_add_one_aux _
  -- `f'` is bounded near `0⁺`
  obtain ⟨M, hM⟩ := EndpointValues.derivBoundedNearLeft ht hta.le hf h2sq
  -- the reproducing formula
  have hid : F = (∫ x in Set.Ioo 0 t, etaT t x * deriv (deriv f) x)
      - ∫ x in Set.Ioo 0 t, etaT'' t x * f x :=
    EndpointValues.twoIbpEtaT f F t ht hta hf hlim ⟨M, hM⟩ hfL1 hf2L1
  -- positivity of the weight and nonnegativity of the two energies
  have hEtapos : ∀ x ∈ Set.Ioo (0 : ℝ) t, 0 < Work.FTS.EllipticEst.thEta x :=
    fun x hx => thEta_pos_of_mem hta hx
  set Jt := ∫ x in Set.Ioo 0 t, (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x
    with hJt
  set Xt := ∫ x in Set.Ioo 0 t, (f x) ^ 2 * Work.FTS.EllipticEst.thEta x with hXt
  have hJt0 : 0 ≤ Jt := by
    rw [hJt]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun x hx => mul_nonneg (sq_nonneg _) (hEtapos x hx).le)
  have hXt0 : 0 ≤ Xt := by
    rw [hXt]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun x hx => mul_nonneg (sq_nonneg _) (hEtapos x hx).le)
  -- the weighted Cauchy–Schwarz inputs, first piece
  have hmemA : MemLp (fun x : ℝ => etaT t x / Real.sqrt (Work.FTS.EllipticEst.thEta x)) 2
      (volume.restrict (Set.Ioo 0 t)) := by
    have hmeas : AEStronglyMeasurable
        (fun x : ℝ => etaT t x / Real.sqrt (Work.FTS.EllipticEst.thEta x))
        (volume.restrict (Set.Ioo 0 t)) :=
      (continuousOn_etaT_div_sqrt_thEta t hta).aestronglyMeasurable measurableSet_Ioo
    refine (MeasureTheory.memLp_two_iff_integrable_sq hmeas).mpr ?_
    refine (integrableOn_etaT_sq_div_thEta t ht hta).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    rw [div_pow, Real.sq_sqrt (le_of_lt (hEtapos x hx))]
  have hmemA' : MemLp (fun x : ℝ => etaT'' t x / Real.sqrt (Work.FTS.EllipticEst.thEta x)) 2
      (volume.restrict (Set.Ioo 0 t)) := by
    have hmeas : AEStronglyMeasurable
        (fun x : ℝ => etaT'' t x / Real.sqrt (Work.FTS.EllipticEst.thEta x))
        (volume.restrict (Set.Ioo 0 t)) :=
      (continuousOn_etaT''_div_sqrt_thEta t hta).aestronglyMeasurable measurableSet_Ioo
    refine (MeasureTheory.memLp_two_iff_integrable_sq hmeas).mpr ?_
    refine (integrableOn_etaT''_sq_div_thEta t ht hta).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    rw [div_pow, Real.sq_sqrt (le_of_lt (hEtapos x hx))]
  -- second pieces
  have hmemB : MemLp (fun x : ℝ => deriv (deriv f) x * Real.sqrt (Work.FTS.EllipticEst.thEta x))
      2 (volume.restrict (Set.Ioo 0 t)) := by
    have hmeas : AEStronglyMeasurable
        (fun x : ℝ => deriv (deriv f) x * Real.sqrt (Work.FTS.EllipticEst.thEta x))
        (volume.restrict (Set.Ioo 0 t)) :=
      (hcont2.mul (continuousOn_sqrt_thEta hta)).aestronglyMeasurable measurableSet_Ioo
    refine (MeasureTheory.memLp_two_iff_integrable_sq hmeas).mpr ?_
    refine h2t.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hEtapos x hx))]
  have hmemB' : MemLp (fun x : ℝ => f x * Real.sqrt (Work.FTS.EllipticEst.thEta x)) 2
      (volume.restrict (Set.Ioo 0 t)) := by
    have hmeas : AEStronglyMeasurable
        (fun x : ℝ => f x * Real.sqrt (Work.FTS.EllipticEst.thEta x))
        (volume.restrict (Set.Ioo 0 t)) :=
      (hcont0.mul (continuousOn_sqrt_thEta hta)).aestronglyMeasurable measurableSet_Ioo
    refine (MeasureTheory.memLp_two_iff_integrable_sq hmeas).mpr ?_
    refine h1t.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hEtapos x hx))]
  -- the two weighted Cauchy–Schwarz inequalities
  have hcsA := weighted_cs_integral measurableSet_Ioo hEtapos hmemA hmemB
  have hcsB := weighted_cs_integral measurableSet_Ioo hEtapos hmemA' hmemB'
  have hA2 : (∫ x in Set.Ioo 0 t, etaT t x * deriv (deriv f) x) ^ 2
      ≤ t ^ (3 + Work.Spaces.eta) * Jt := by
    refine hcsA.trans ?_
    rw [hJt]
    exact mul_le_mul_of_nonneg_right (integral_etaT_sq_div_thEta_le t ht hta) hJt0
  have hB2 : (∫ x in Set.Ioo 0 t, etaT'' t x * f x) ^ 2
      ≤ 50 * t ^ (Work.Spaces.eta - 1) * Xt := by
    refine hcsB.trans ?_
    rw [hXt]
    exact mul_le_mul_of_nonneg_right (integral_etaT''_sq_div_thEta_le t ht hta) hXt0
  -- assembly
  have hF : F ^ 2 ≤ 2 * (t ^ (3 + Work.Spaces.eta) * Jt)
      + 2 * (50 * t ^ (Work.Spaces.eta - 1) * Xt) := by
    rw [hid]
    nlinarith [hA2, hB2,
      sq_nonneg ((∫ x in Set.Ioo 0 t, etaT t x * deriv (deriv f) x)
        + (∫ x in Set.Ioo 0 t, etaT'' t x * f x))]
  set J := ∫ x in Set.Ioo 0 (Real.pi / 2),
    (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x with hJ
  set X := ∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * Work.FTS.EllipticEst.thEta x with hX
  have hJs : Jt ≤ J := by
    rw [hJt, hJ]
    refine MeasureTheory.setIntegral_mono_set h2 ?_ (ae_of_all _ (fun x hx => hsub hx))
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    exact mul_nonneg (sq_nonneg _) (thEta_nonneg_of_mem_Ioo hx)
  have hXs : Xt ≤ X := by
    rw [hXt, hX]
    refine MeasureTheory.setIntegral_mono_set h1 ?_ (ae_of_all _ (fun x hx => hsub hx))
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    exact mul_nonneg (sq_nonneg _) (thEta_nonneg_of_mem_Ioo hx)
  have htpow0 : 0 ≤ t ^ (3 + Work.Spaces.eta) := Real.rpow_nonneg ht.le _
  have hEtpow0 : 0 ≤ t ^ (Work.Spaces.eta - 1) := Real.rpow_nonneg ht.le _
  calc F ^ 2 ≤ 2 * (t ^ (3 + Work.Spaces.eta) * Jt)
        + 2 * (50 * t ^ (Work.Spaces.eta - 1) * Xt) := hF
    _ ≤ 2 * (t ^ (3 + Work.Spaces.eta) * J)
        + 2 * (50 * t ^ (Work.Spaces.eta - 1) * X) := by
        have h1' : 2 * (t ^ (3 + Work.Spaces.eta) * Jt) ≤ 2 * (t ^ (3 + Work.Spaces.eta) * J) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJs htpow0) (by norm_num)
        have h2' : 2 * (50 * t ^ (Work.Spaces.eta - 1) * Xt)
            ≤ 2 * (50 * t ^ (Work.Spaces.eta - 1) * X) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hXs (mul_nonneg (by norm_num) hEtpow0)) (by norm_num)
        linarith
    _ = 2 * t ^ (3 + Work.Spaces.eta) * J
        + 100 * t ^ (Work.Spaces.eta - 1) * X := by ring

theorem endpointParamRightW (f : ℝ → ℝ) (F t : ℝ) (ht : 0 < t) (hta : t < Real.pi / 2)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hlim : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F))
    (h2 : MeasureTheory.IntegrableOn
      (fun x : ℝ => (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 (Real.pi / 2)))
    (h1 : MeasureTheory.IntegrableOn
      (fun x : ℝ => (f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 (Real.pi / 2))) :
    F ^ 2 ≤ 2 * t ^ (3 + Work.Spaces.eta) *
        (∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      + 100 * t ^ (Work.Spaces.eta - 1) *
        (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * Work.FTS.EllipticEst.thEta x) := by
  obtain ⟨hintR, hintIR, hcdR, _hd1R, hd2R, hlimR⟩ := EndpointValues.reflectFacts
  set g : ℝ → ℝ := fun x => f (Real.pi / 2 - x) with hg_eq
  have hg_cd : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)) := by
    simpa only [hg_eq] using hcdR f hf
  have hg_lim : Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F) := by
    simpa only [hg_eq] using hlimR f F hlim
  -- pointwise identification of the two integrands with the reflected ones
  have hpt2 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (deriv (deriv g) x) ^ 2 * Work.FTS.EllipticEst.thEta x
        = (fun y : ℝ => (deriv (deriv f) y) ^ 2 * Work.FTS.EllipticEst.thEta y)
            (Real.pi / 2 - x) := by
    intro x hx
    have h1 : deriv (deriv g) x = deriv (deriv f) (Real.pi / 2 - x) := by
      simpa only [hg_eq] using hd2R f hf x hx
    rw [h1]
    simp only [thEta_pi_div_two_sub]
  have hpt1 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (g x) ^ 2 * Work.FTS.EllipticEst.thEta x
        = (fun y : ℝ => (f y) ^ 2 * Work.FTS.EllipticEst.thEta y) (Real.pi / 2 - x) := by
    intro x _
    simp only [hg_eq]
    rw [thEta_pi_div_two_sub]
  -- transfer of the two integrability hypotheses
  have hg_2 : IntegrableOn (fun x : ℝ => (deriv (deriv g) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 (Real.pi / 2)) :=
    (hintIR (fun y : ℝ => (deriv (deriv f) y) ^ 2 * Work.FTS.EllipticEst.thEta y) h2).congr_fun
      (fun x hx => (hpt2 x hx).symm) measurableSet_Ioo
  have hg_1 : IntegrableOn (fun x : ℝ => (g x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 (Real.pi / 2)) :=
    (hintIR (fun y : ℝ => (f y) ^ 2 * Work.FTS.EllipticEst.thEta y) h1).congr_fun
      (fun x hx => (hpt1 x hx).symm) measurableSet_Ioo
  -- the weighted left-endpoint estimate for the reflected function
  have hmain := endpointParamLeftW_aux g F t ht hta hg_cd hg_lim hg_2 hg_1
  -- the two integrals are invariant under the reflection
  have hIg : (∫ x in Set.Ioo 0 (Real.pi / 2),
        (deriv (deriv g) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      = ∫ x in Set.Ioo 0 (Real.pi / 2),
        (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x := by
    calc (∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv (deriv g) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
        = ∫ x in Set.Ioo 0 (Real.pi / 2),
            (fun y : ℝ => (deriv (deriv f) y) ^ 2 * Work.FTS.EllipticEst.thEta y)
              (Real.pi / 2 - x) :=
          setIntegral_congr_fun measurableSet_Ioo hpt2
      _ = ∫ x in Set.Ioo 0 (Real.pi / 2),
            (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x := by
          simpa using hintR (fun y : ℝ => (deriv (deriv f) y) ^ 2 * Work.FTS.EllipticEst.thEta y)
  have hIf : (∫ x in Set.Ioo 0 (Real.pi / 2), (g x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      = ∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * Work.FTS.EllipticEst.thEta x := by
    calc (∫ x in Set.Ioo 0 (Real.pi / 2), (g x) ^ 2 * Work.FTS.EllipticEst.thEta x)
        = ∫ x in Set.Ioo 0 (Real.pi / 2),
            (fun y : ℝ => (f y) ^ 2 * Work.FTS.EllipticEst.thEta y) (Real.pi / 2 - x) :=
          setIntegral_congr_fun measurableSet_Ioo hpt1
      _ = ∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * Work.FTS.EllipticEst.thEta x := by
          simpa using hintR (fun y : ℝ => (f y) ^ 2 * Work.FTS.EllipticEst.thEta y)
  rwa [hIg, hIf] at hmain

end Work.EllipticEst.Core.i0Aux.TVRed
