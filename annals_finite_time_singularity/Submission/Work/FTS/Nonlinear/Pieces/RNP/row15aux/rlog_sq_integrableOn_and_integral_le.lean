import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `z`-integral of the row-15 bookkeeping weight

`∫_0^∞ ((1 + log(1+z))/(1+z))² dz ≤ 100`.  The true value is `5` (substitute `u = 1+z`,
then `u = e^t`: `∫_0^∞ (1+t)²e^{-t} dt = 5`), but for the row-15 bookkeeping any explicit
constant suffices, and a majorant with an elementary `rpow` antiderivative is cheaper to
formalise: for `z ≥ 0`,

`((1 + log(1+z))/(1+z))² ≤ 25 (1+z)^{-3/2}`

(because `log u ≤ 4(u^{1/4} - 1)` for `u ≥ 1` by `Real.log_le_sub_one_of_pos` applied to
`u^{1/4}`), and `∫_0^∞ (1+z)^{-3/2} dz = 2` by the fundamental theorem of calculus, with
antiderivative `-2(1+z)^{-1/2}`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false

/-- The antiderivative `-2(1+z)^{-1/2}` of the majorant `(1+z)^{-3/2}`. -/
private theorem hasDerivAt_maj (x : ℝ) (_hx : 0 ≤ x) :
    HasDerivAt (fun t : ℝ => -2 * (1 + t) ^ (-(1 / 2 : ℝ))) ((1 + x) ^ (-(3 / 2 : ℝ))) x := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
    simpa using (hasDerivAt_id x).const_add (1 : ℝ)
  have hne : (1 + x) ≠ 0 := by positivity
  have h2 : HasDerivAt (fun t : ℝ => (1 + t) ^ (-(1 / 2 : ℝ)))
      (-(1 / 2 : ℝ) * (1 + x) ^ (-(1 / 2 : ℝ) - 1)) x := by
    have hraw :=
      (Real.hasDerivAt_rpow_const (x := 1 + x) (p := -(1 / 2 : ℝ)) (Or.inl hne)).comp x h1
    convert hraw using 1
    · funext t
      rfl
    · ring_nf
  rw [show (-(1 / 2 : ℝ)) - 1 = -(3 / 2 : ℝ) by norm_num] at h2
  have h3 := h2.const_mul (-2 : ℝ)
  have hval : (-2 : ℝ) * (-(1 / 2 : ℝ) * (1 + x) ^ (-(3 / 2 : ℝ)))
      = (1 + x) ^ (-(3 / 2 : ℝ)) := by ring
  rwa [hval] at h3

private theorem tendsto_maj :
    Tendsto (fun t : ℝ => -2 * (1 + t) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => (1 : ℝ) + t) atTop atTop :=
    tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id
  have h2 : Tendsto (fun t : ℝ => ((1 : ℝ) + t) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp h1
  simpa using h2.const_mul (-2)

/-- The majorant `z ↦ (1+z)^{-3/2}` is integrable on `[0,∞)`. -/
theorem maj_integrableOn_Ici :
    IntegrableOn (fun z : ℝ => (1 + z) ^ (-(3 / 2 : ℝ))) (Set.Ici (0 : ℝ)) := by
  have key := MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
    (a := (0 : ℝ)) (l := (0 : ℝ))
    (g := fun t : ℝ => -2 * (1 + t) ^ (-(1 / 2 : ℝ)))
    (g' := fun x : ℝ => (1 + x) ^ (-(3 / 2 : ℝ)))
    (fun x hx => hasDerivAt_maj x hx)
    (fun x hx => by
      have hx' : (0 : ℝ) < x := hx
      exact Real.rpow_nonneg (by linarith) _)
    tendsto_maj
  change Integrable (fun z : ℝ => (1 + z) ^ (-(3 / 2 : ℝ))) (volume.restrict (Set.Ici 0))
  rw [← Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))]
  exact key

/-- `∫_0^∞ (1+z)^{-3/2} dz = 2`. -/
theorem integral_maj_Ici :
    ∫ z in Set.Ici (0 : ℝ), (1 + z) ^ (-(3 / 2 : ℝ)) = 2 := by
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0 : ℝ)) (l := (0 : ℝ))
    (g := fun t : ℝ => -2 * (1 + t) ^ (-(1 / 2 : ℝ)))
    (g' := fun x : ℝ => (1 + x) ^ (-(3 / 2 : ℝ)))
    (fun x hx => hasDerivAt_maj x hx)
    (fun x hx => by
      have hx' : (0 : ℝ) < x := hx
      exact Real.rpow_nonneg (by linarith) _)
    tendsto_maj
  rw [key]
  rw [show (1 : ℝ) + 0 = 1 by ring, Real.one_rpow]
  norm_num

/-- `1 + log u ≤ 5 u^{1/4}` for `u ≥ 1`. -/
private theorem one_add_log_le {u : ℝ} (hu : 1 ≤ u) : 1 + Real.log u ≤ 5 * u ^ (1 / 4 : ℝ) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hq : (0 : ℝ) < u ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hu0 _
  have h1 : Real.log (u ^ (1 / 4 : ℝ)) ≤ u ^ (1 / 4 : ℝ) - 1 := Real.log_le_sub_one_of_pos hq
  have h2 : Real.log (u ^ (1 / 4 : ℝ)) = (1 / 4) * Real.log u := Real.log_rpow hu0 (1 / 4)
  have h3 : (1 : ℝ) ≤ u ^ (1 / 4 : ℝ) := Real.one_le_rpow hu (by norm_num)
  linarith

/-- The pointwise majorant: `rlog z² ≤ 25 (1+z)^{-3/2}` for `z ≥ 0`. -/
theorem rlog_sq_le_maj {z : ℝ} (hz : 0 ≤ z) :
    (rlog z) ^ 2 ≤ 25 * (1 + z) ^ (-(3 / 2 : ℝ)) := by
  have hu : (1 : ℝ) ≤ 1 + z := by linarith
  have hu0 : (0 : ℝ) < 1 + z := lt_of_lt_of_le one_pos hu
  have hlog : 1 + Real.log (1 + z) ≤ 5 * (1 + z) ^ (1 / 4 : ℝ) := one_add_log_le hu
  have hlog0 : 0 ≤ 1 + Real.log (1 + z) := by
    have := Real.log_nonneg hu
    linarith
  have hsq : (1 + Real.log (1 + z)) ^ 2 ≤ 25 * (1 + z) ^ (1 / 2 : ℝ) := by
    have hpow : ((1 + z) ^ (1 / 4 : ℝ)) ^ 2 = (1 + z) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast ((1 + z) ^ (1 / 4 : ℝ)) 2,
        ← Real.rpow_mul (le_of_lt hu0) (1 / 4) ((2 : ℕ) : ℝ),
        show (1 / 4) * ((2 : ℕ) : ℝ) = 1 / 2 by push_cast; norm_num]
    have h6 := pow_le_pow_left₀ hlog0 hlog 2
    rw [mul_pow, hpow] at h6
    norm_num at h6
    exact h6
  have hkey : (1 + z) ^ (1 / 2 : ℝ) / (1 + z) ^ 2 = (1 + z) ^ (-(3 / 2 : ℝ)) := by
    have h2r : (1 + z) ^ 2 = (1 + z) ^ (2 : ℝ) := (Real.rpow_natCast (1 + z) 2).symm
    rw [h2r, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hu0) 2,
      ← Real.rpow_add hu0 (1 / 2) (-(2 : ℝ)),
      show (1 / 2 : ℝ) + -(2 : ℝ) = -(3 / 2 : ℝ) by norm_num]
  have hnn : (0 : ℝ) ≤ (1 + z) ^ 2 := by positivity
  calc (rlog z) ^ 2
      = (1 + Real.log (1 + z)) ^ 2 / (1 + z) ^ 2 := by rw [rlog_def, div_pow]
    _ ≤ 25 * (1 + z) ^ (1 / 2 : ℝ) / (1 + z) ^ 2 :=
        div_le_div_of_nonneg_right hsq hnn
    _ = 25 * ((1 + z) ^ (1 / 2 : ℝ) / (1 + z) ^ 2) := by ring
    _ = 25 * (1 + z) ^ (-(3 / 2 : ℝ)) := by rw [hkey]

theorem rlog_sq_integrableOn_and_integral_le :
    MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.FTS.Nonlinear.Pieces.RNP.row15aux.rlog z) ^ 2) (Set.Ici (0 : ℝ)) ∧
      ∫ z in Set.Ici (0 : ℝ), (Work.FTS.Nonlinear.Pieces.RNP.row15aux.rlog z) ^ 2 ≤ 100 := by
  have hmaj := maj_integrableOn_Ici
  have hmeas : Measurable (fun z : ℝ => (rlog z) ^ 2) := by
    simp only [rlog]
    fun_prop
  have hInt : IntegrableOn (fun z : ℝ => (rlog z) ^ 2) (Set.Ici (0 : ℝ)) := by
    rw [IntegrableOn] at hmaj ⊢
    refine Integrable.mono' (hmaj.const_mul (25 : ℝ)) hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact rlog_sq_le_maj hz
  refine ⟨hInt, ?_⟩
  have hle : ∀ᵐ z ∂(volume.restrict (Set.Ici (0 : ℝ))),
      (rlog z) ^ 2 ≤ 25 * (1 + z) ^ (-(3 / 2 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    exact rlog_sq_le_maj hz
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ici (0 : ℝ))] (fun z : ℝ => (rlog z) ^ 2) :=
    Eventually.of_forall fun z => sq_nonneg _
  calc ∫ z in Set.Ici (0 : ℝ), (rlog z) ^ 2
      ≤ ∫ z in Set.Ici (0 : ℝ), 25 * (1 + z) ^ (-(3 / 2 : ℝ)) :=
        integral_mono_of_nonneg hnn (hmaj.const_mul 25) hle
    _ = 25 * ∫ z in Set.Ici (0 : ℝ), (1 + z) ^ (-(3 / 2 : ℝ)) := integral_const_mul _ _
    _ = 25 * 2 := by rw [integral_maj_Ici]
    _ ≤ 100 := by norm_num

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
