/-
Copyright: work module for the Elgindi finite-time singularity project.

# The endpoint-value estimate, at one scale

`endpointParamLeft` is the heart of `Work.EllipticEst.Core.i0Aux.endpointValuesCore`: if
`F = lim_{x → 0⁺} f x` and `f` is `C²` on `(0, π/2)` with `f, f'' ∈ L²` there, then for every
scale `t ∈ (0, π/2)`

  `F² ≤ (2/3) t³ ∫_{Iθ} (f'')² + 72 t⁻¹ ∫_{Iθ} f²`.

The two distinct powers of the scale (`t³` against `t⁻¹`) are exactly what makes the subsequent
one-dimensional optimisation produce the two-term bound `F² ≤ C (∫f² + √(∫f² ∫(f'')²))`.

Proof: the reproducing formula `F = ∫_0^t η f'' - ∫_0^t η'' f` of
`EndpointValues.twoIbpEtaT`, with the test function `η x = x (1-x/t)³` whose `L²(0,t)` norm is
`≤ t^{3/2}/√3` and whose second derivative has `L²(0,t)` norm `≤ 6/√t`
(`EndpointValues.etaTFacts`), together with Cauchy–Schwarz.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.cs_integral
import Submission.Work.EllipticEst.Core.derivIntegrableOfEnergy
import Submission.Work.EllipticEst.Core.i0Aux.EndpointDefs
import Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.etaTFacts
import Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.twoIbpEtaT
import Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.derivBoundedNearLeft

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.EndpointValues

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- Auxiliary: on `(0,t)` the test function `η_t` is bounded by `t` (both in absolute value and
after squaring). -/
private lemma etaT_abs_le {t x : ℝ} (hx : x ∈ Set.Ioo 0 t) : |etaT t x| ≤ t := by
  have hx0 : 0 ≤ x := hx.1.le
  have hxt : x ≤ t := hx.2.le
  have ht0 : 0 < t := lt_trans hx.1 hx.2
  have h1 : 0 ≤ 1 - x / t := by
    have : x / t ≤ 1 := (div_le_one ht0).mpr hxt
    linarith
  have h2 : 1 - x / t ≤ 1 := by
    have : 0 ≤ x / t := div_nonneg hx0 ht0.le
    linarith
  have h3 : (1 - x / t) ^ 3 ≤ 1 := by
    have := pow_le_pow_left₀ h1 h2 3
    simpa using this
  have h4 : 0 ≤ (1 - x / t) ^ 3 := pow_nonneg h1 3
  have h5 : etaT t x ≤ t := by
    simp only [etaT]
    calc x * (1 - x / t) ^ 3 ≤ x * 1 := mul_le_mul_of_nonneg_left h3 hx0
      _ = x := mul_one x
      _ ≤ t := hxt
  have h6 : 0 ≤ etaT t x := by
    simp only [etaT]
    exact mul_nonneg hx0 h4
  rw [abs_of_nonneg h6]
  exact h5

/-- Auxiliary: on `(0,t)` the second derivative of the test function is bounded by `6/t`. -/
private lemma etaT''_abs_le {t x : ℝ} (hx : x ∈ Set.Ioo 0 t) : |etaT'' t x| ≤ 6 / t := by
  have ht0 : 0 < t := lt_trans hx.1 hx.2
  have hx0 : 0 ≤ x := hx.1.le
  have hxt : x ≤ t := hx.2.le
  have h1 : |1 - x / t| ≤ 1 := by
    have h0 : 0 ≤ 1 - x / t := by
      have : x / t ≤ 1 := (div_le_one ht0).mpr hxt
      linarith
    rw [abs_of_nonneg h0]
    have : 0 ≤ x / t := div_nonneg hx0 ht0.le
    linarith
  have h2 : |2 * x / t - 1| ≤ 1 := by
    have h0 : 0 ≤ x / t := div_nonneg hx0 ht0.le
    have h1' : x / t ≤ 1 := (div_le_one ht0).mpr hxt
    have h2' : 2 * x / t = 2 * (x / t) := by ring
    rw [h2', abs_le]
    constructor <;> linarith
  have h3 : (0:ℝ) ≤ 6 / t := div_nonneg (by norm_num) ht0.le
  calc |etaT'' t x| = |6 / t| * |1 - x / t| * |2 * x / t - 1| := by
        simp only [etaT'', abs_mul]
    _ ≤ (6 / t) * 1 * 1 := by
        refine mul_le_mul (mul_le_mul (le_of_eq (abs_of_nonneg h3)) h1 (abs_nonneg _)
          h3) h2 (abs_nonneg _) (mul_nonneg h3 (by norm_num)) 
    _ = 6 / t := by ring

/-- Auxiliary: the test function is continuous. -/
private lemma continuousOn_etaT (t : ℝ) :
    ContinuousOn (etaT t) (Set.Ioo 0 t) := by
  unfold etaT
  fun_prop

/-- Auxiliary: the second derivative of the test function is continuous. -/
private lemma continuousOn_etaT'' (t : ℝ) :
    ContinuousOn (etaT'' t) (Set.Ioo 0 t) := by
  unfold etaT''
  fun_prop

/-- **The endpoint-value estimate at one scale.**  If `f` is `C²` on `(0, π/2)` with
`F = lim_{x → 0⁺} f x` and if `f` and `f''` are square-integrable on `(0, π/2)`, then for every
`t ∈ (0, π/2)`,

  `F² ≤ (2/3) t³ ∫_{Iθ} (f'')² + 72 t⁻¹ ∫_{Iθ} f²`. -/
theorem endpointParamLeft (f : ℝ → ℝ) (F t : ℝ)
    (ht : 0 < t) (hta : t < Real.pi / 2)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hlim : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F))
    (h2 : MeasureTheory.IntegrableOn (fun x : ℝ => (deriv (deriv f) x) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)))
    (h1 : MeasureTheory.IntegrableOn (fun x : ℝ => (f x) ^ 2)
      (Set.Ioo 0 (Real.pi / 2))) :
    F ^ 2 ≤ (2 / 3) * t ^ 3 * (∫ x in Set.Ioo 0 (Real.pi / 2), (deriv (deriv f) x) ^ 2)
      + 72 * t⁻¹ * (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2) := by
  have ht0 : 0 < t := ht
  have hsub : Set.Ioo (0 : ℝ) t ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨hx.1, lt_trans hx.2 hta⟩
  have h2t : IntegrableOn (fun x : ℝ => (deriv (deriv f) x) ^ 2) (Set.Ioo 0 t) := h2.mono_set hsub
  have h1t : IntegrableOn (fun x : ℝ => (f x) ^ 2) (Set.Ioo 0 t) := h1.mono_set hsub
  -- continuity of the second derivative on `(0,t)`
  have hcon2 : ContinuousOn (deriv (deriv f)) (Set.Ioo 0 t) := by
    have h1' : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
      hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact (h1'.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsub
  have hcon0 : ContinuousOn f (Set.Ioo 0 t) := (hf.continuousOn).mono hsub
  -- `f''` and `f` are `L¹(0,t)`
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 t) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hf2L1 : IntegrableOn (deriv (deriv f)) (Set.Ioo 0 t) := by
    refine Integrable.mono' (h2t.add hconst)
      (hcon2.aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x _
    show |deriv (deriv f) x| ≤ (deriv (deriv f) x) ^ 2 + 1
    exact Work.EllipticEst.Core.abs_le_sq_add_one _
  have hfL1 : IntegrableOn f (Set.Ioo 0 t) := by
    refine Integrable.mono' (h1t.add hconst)
      (hcon0.aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x _
    show |f x| ≤ (f x) ^ 2 + 1
    exact Work.EllipticEst.Core.abs_le_sq_add_one _
  -- the reproducing formula
  obtain ⟨M, hM⟩ := derivBoundedNearLeft (f := f) ht hta.le hf h2t
  have hid : F = (∫ x in Set.Ioo 0 t, etaT t x * deriv (deriv f) x)
      - ∫ x in Set.Ioo 0 t, etaT'' t x * f x :=
    twoIbpEtaT f F t ht hta hf hlim ⟨M, hM⟩ hfL1 hf2L1
  -- the elementary facts about the test function
  obtain ⟨hηd, hη'd, hη0, hη'0, hηt, hη't, hηsq, hη''sq⟩ := etaTFacts ht
  have hηsq' : (∫ x in Set.Ioo (0 : ℝ) t, (etaT t x) ^ 2) ≤ t ^ 3 / 3 := by
    have heq : (∫ x in (0 : ℝ)..t, (etaT t x) ^ 2) = ∫ x in Set.Ioo (0 : ℝ) t, (etaT t x) ^ 2 := by
      rw [intervalIntegral.integral_of_le ht.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [← heq]
    exact hηsq
  have hη''sq' : (∫ x in Set.Ioo (0 : ℝ) t, (etaT'' t x) ^ 2) ≤ 36 / t := by
    have heq : (∫ x in (0 : ℝ)..t, (etaT'' t x) ^ 2)
        = ∫ x in Set.Ioo (0 : ℝ) t, (etaT'' t x) ^ 2 := by
      rw [intervalIntegral.integral_of_le ht.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [← heq]
    exact hη''sq
  have hmemη : MemLp (etaT t) 2 (volume.restrict (Set.Ioo 0 t)) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq]
    · refine Integrable.mono' (integrableOn_const (C := t ^ 2) ?_)
        (((continuousOn_etaT t).pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
      · rw [Real.volume_Ioo]
        exact ENNReal.ofReal_ne_top
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h := etaT_abs_le (t := t) (x := x) hx
        have h2 : (etaT t x) ^ 2 ≤ t ^ 2 := by
          simpa [abs_sq] using pow_le_pow_left₀ (abs_nonneg (etaT t x)) h 2
        exact h2
    · exact (continuousOn_etaT t).aestronglyMeasurable measurableSet_Ioo
  have hmemf2 : MemLp (deriv (deriv f)) 2 (volume.restrict (Set.Ioo 0 t)) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq]
    · exact h2t
    · exact hcon2.aestronglyMeasurable measurableSet_Ioo
  have hmemη'' : MemLp (etaT'' t) 2 (volume.restrict (Set.Ioo 0 t)) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq]
    · refine Integrable.mono' (integrableOn_const (C := (6 / t) ^ 2) ?_)
        (((continuousOn_etaT'' t).pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
      · rw [Real.volume_Ioo]
        exact ENNReal.ofReal_ne_top
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        have h := etaT''_abs_le (t := t) (x := x) hx
        have h2 : (etaT'' t x) ^ 2 ≤ (6 / t) ^ 2 := by
          simpa [abs_sq] using pow_le_pow_left₀ (abs_nonneg (etaT'' t x)) h 2
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact h2
    · exact (continuousOn_etaT'' t).aestronglyMeasurable measurableSet_Ioo
  have hmemf : MemLp f 2 (volume.restrict (Set.Ioo 0 t)) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq]
    · exact h1t
    · exact hcon0.aestronglyMeasurable measurableSet_Ioo
  have hcs1 := Work.Spaces.cs_integral hmemη hmemf2
  have hcs2 := Work.Spaces.cs_integral hmemη'' hmemf
  -- monotonicity of the two energies
  have hJ0 : 0 ≤ ∫ x in Set.Ioo 0 t, (deriv (deriv f) x) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioo
      (fun x _ => sq_nonneg (deriv (deriv f) x))
  have hX0 : 0 ≤ ∫ x in Set.Ioo 0 t, (f x) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioo (fun x _ => sq_nonneg (f x))
  have hJs : (∫ x in Set.Ioo 0 t, (deriv (deriv f) x) ^ 2)
      ≤ ∫ x in Set.Ioo 0 (Real.pi / 2), (deriv (deriv f) x) ^ 2 :=
    setIntegral_mono_set h2 (ae_of_all _ (fun x => sq_nonneg _)) (ae_of_all _ (fun x hx => hsub hx))
  have hXs : (∫ x in Set.Ioo 0 t, (f x) ^ 2)
      ≤ ∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 :=
    setIntegral_mono_set h1 (ae_of_all _ (fun x => sq_nonneg _)) (ae_of_all _ (fun x hx => hsub hx))
  -- assemble
  set J := ∫ x in Set.Ioo 0 (Real.pi / 2), (deriv (deriv f) x) ^ 2 with hJ
  set X := ∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 with hX
  set Jt := ∫ x in Set.Ioo 0 t, (deriv (deriv f) x) ^ 2 with hJt
  set Xt := ∫ x in Set.Ioo 0 t, (f x) ^ 2 with hXt
  have hA1 : (∫ x in Set.Ioo 0 t, etaT t x * deriv (deriv f) x) ^ 2
      ≤ (t ^ 3 / 3) * Jt := by
    refine le_trans hcs1 ?_
    exact mul_le_mul_of_nonneg_right hηsq' hJ0
  have hA2 : (∫ x in Set.Ioo 0 t, etaT'' t x * f x) ^ 2 ≤ (36 / t) * Xt := by
    refine le_trans hcs2 ?_
    exact mul_le_mul_of_nonneg_right hη''sq' hX0
  have hJs' : Jt ≤ J := hJs
  have hXs' : Xt ≤ X := hXs
  have hmain : F ^ 2 ≤ 2 * ((t ^ 3 / 3) * Jt) + 2 * ((36 / t) * Xt) := by
    rw [hid]
    nlinarith [hA1, hA2, sq_nonneg ((∫ x in Set.Ioo 0 t, etaT t x * deriv (deriv f) x)
      + (∫ x in Set.Ioo 0 t, etaT'' t x * f x))]
  have hcoef1 : (0:ℝ) ≤ t ^ 3 / 3 := by positivity
  have hcoef2 : (0:ℝ) ≤ 36 / t := by positivity
  calc F ^ 2 ≤ 2 * ((t ^ 3 / 3) * Jt) + 2 * ((36 / t) * Xt) := hmain
    _ ≤ 2 * ((t ^ 3 / 3) * J) + 2 * ((36 / t) * X) := by
        have h1' : (t ^ 3 / 3) * Jt ≤ (t ^ 3 / 3) * J :=
          mul_le_mul_of_nonneg_left hJs' hcoef1
        have h2' : (36 / t) * Xt ≤ (36 / t) * X :=
          mul_le_mul_of_nonneg_left hXs' hcoef2
        linarith
    _ = (2 / 3) * t ^ 3 * (∫ x in Set.Ioo 0 (Real.pi / 2), (deriv (deriv f) x) ^ 2)
        + 72 * t⁻¹ * (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2) := by
        rw [hJ, hX]
        field_simp
        ring

end Work.EllipticEst.Core.i0Aux.EndpointValues
