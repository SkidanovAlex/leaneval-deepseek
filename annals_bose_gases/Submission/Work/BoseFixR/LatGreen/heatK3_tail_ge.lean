import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.LatGreen.MadelungDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Green's-function tail bound `heatK3_tail_ge`

For `a ≥ 0` and `η > 0` the heat-kernel tail
`∫_{η}^{∞} (4πt)^{-3/2} e^{-a/t} dt`
is at least its two-term expansion about `a = 0`
`1/(4π^{3/2}√η) − a/(12π^{3/2}η^{3/2})`.

**Proof.**  On `t > 0` the pointwise inequality `e^{-x} ≥ 1 - x` for `x = a/t ≥ 0` gives
`(4πt)^{-3/2} e^{-a/t} ≥ (4πt)^{-3/2}(1 - a/t)`
`= (4π)^{-3/2}(t^{-3/2} - a t^{-5/2})`,
and the right-hand side is exactly the linear combination whose integral over `(η, ∞)` can be
evaluated with `integral_Ioi_rpow_of_lt`:
`∫_η^∞ t^{-3/2} = 2η^{-1/2}`, `∫_η^∞ t^{-5/2} = (2/3)η^{-3/2}`.
The arithmetic normalisation `(4π)^{-3/2}·2 = 1/(4π^{3/2})` and `(4π)^{-3/2}·(2/3) = 1/(12π^{3/2})`
finishes.  Integrability of the heat-kernel integrand on `(η, ∞)` is by domination with
`(4π)^{-3/2} t^{-3/2}` (integrable since `-3/2 < -1`).
-/

namespace Work.BoseFixR.LatGreen

open MeasureTheory Set

/-- Integrability of the heat-kernel tail integrand on `(η, ∞)`: it is dominated by
`(4π)^{-3/2} t^{-3/2}`, which is integrable on `(η, ∞)` since `η > 0` and `-3/2 < -1`. -/
lemma heatK3_tail_integrable {a η : ℝ} (ha : 0 ≤ a) (hη : 0 < η) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(a / t))) (Set.Ioi η) := by
  have h3 : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) (Set.Ioi η) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hη
  have hdom : MeasureTheory.IntegrableOn
      (fun t : ℝ => (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * t ^ (-(3 / 2 : ℝ))) (Set.Ioi η) :=
    h3.const_mul _
  refine hdom.mono' ?_ ?_
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := hη.trans ht
    have h4π : (0 : ℝ) < 4 * Real.pi := by positivity
    rw [Real.norm_of_nonneg (by positivity), Real.mul_rpow h4π.le ht0.le]
    have hexp : Real.exp (-(a / t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have h1 : 0 ≤ a / t := div_nonneg ha ht0.le
      linarith
    calc (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * t ^ (-(3 / 2 : ℝ)) * Real.exp (-(a / t))
        ≤ (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * t ^ (-(3 / 2 : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * t ^ (-(3 / 2 : ℝ)) := by ring

/-- The integral of the linear comparison function
`(4π)^{-3/2}(t^{-3/2} - a t^{-5/2})` over `(η, ∞)`:
it evaluates to `(4π)^{-3/2}(2η^{-1/2} - (2/3)aη^{-3/2})`. -/
lemma integral_Ioi_rpow_lower {a η : ℝ} (hη : 0 < η) :
    ∫ t in Set.Ioi η,
        (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * (t ^ (-(3 / 2 : ℝ)) - a * t ^ (-(5 / 2 : ℝ)))
      = (4 * Real.pi) ^ (-(3 / 2 : ℝ))
          * (2 * η ^ (-(1 / 2 : ℝ)) - a * (2 / 3) * η ^ (-(3 / 2 : ℝ))) := by
  have h3 : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) (Set.Ioi η) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hη
  have h5 : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-(5 / 2 : ℝ))) (Set.Ioi η) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hη
  rw [integral_const_mul, integral_sub h3 (h5.const_mul a), integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num) hη, integral_Ioi_rpow_of_lt (by norm_num) hη]
  ring_nf

/-- The arithmetic normalisation `(4π)^{-3/2}·2 = 1/(4π^{3/2})` and
`(4π)^{-3/2}·(2/3) = 1/(12π^{3/2})`, together with `η^{-1/2} = 1/√η`. -/
lemma arith_lower {a η : ℝ} (hη : 0 < η) :
    (4 * Real.pi) ^ (-(3 / 2 : ℝ))
        * (2 * η ^ (-(1 / 2 : ℝ)) - a * (2 / 3) * η ^ (-(3 / 2 : ℝ)))
      = 1 / (4 * Real.pi ^ (3 / 2 : ℝ) * Real.sqrt η)
          - a / (12 * Real.pi ^ (3 / 2 : ℝ) * η ^ (3 / 2 : ℝ)) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h4rp : (4 : ℝ) ^ (3 / 2 : ℝ) = 8 := by
    rw [Real.rpow_div_two_eq_sqrt 3 (by norm_num : (0 : ℝ) ≤ 4),
      show Real.sqrt 4 = 2 by norm_num]
    norm_num
  have h4πrp : (4 * Real.pi) ^ (3 / 2 : ℝ) = 8 * Real.pi ^ (3 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hπ.le, h4rp]
  have hc : (4 * Real.pi) ^ (-(3 / 2 : ℝ)) = 1 / (8 * Real.pi ^ (3 / 2 : ℝ)) := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 4 * Real.pi), h4πrp, one_div]
  rw [hc]
  have e1 : η ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt η := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hη.le]
    norm_num
  have e2 : η ^ (-(3 / 2 : ℝ)) = 1 / η ^ (3 / 2 : ℝ) := by
    rw [Real.rpow_neg hη.le]
    norm_num
  rw [e1, e2]
  have hx : (0 : ℝ) < Real.pi ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hπ _
  have hy : (0 : ℝ) < η ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hη _
  have hs : (0 : ℝ) < Real.sqrt η := Real.sqrt_pos.mpr hη
  field_simp
  ring

/-- Pointwise comparison: on `t > η > 0`,
`(4π)^{-3/2}(t^{-3/2} - a t^{-5/2}) ≤ (4πt)^{-3/2} e^{-a/t}`, from `e^{-x} ≥ 1 - x`. -/
lemma lower_le_heatK3 {a η : ℝ} (hη : 0 < η) :
    ∀ t ∈ Set.Ioi η,
      (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * (t ^ (-(3 / 2 : ℝ)) - a * t ^ (-(5 / 2 : ℝ)))
        ≤ (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(a / t)) := by
  intro t ht
  have ht0 : 0 < t := hη.trans ht
  have h4π : (0 : ℝ) < 4 * Real.pi := by positivity
  have h4πt : (0 : ℝ) < 4 * Real.pi * t := by positivity
  have hsplit : (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) = (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * t ^ (-(3 / 2 : ℝ)) :=
    Real.mul_rpow h4π.le ht0.le
  have hpow : t ^ (-(5 / 2 : ℝ)) = t ^ (-(3 / 2 : ℝ)) * t ^ (-1 : ℝ) := by
    rw [← Real.rpow_add ht0, show -(5 / 2 : ℝ) = -(3 / 2 : ℝ) + (-1 : ℝ) by norm_num]
  rw [hpow, Real.rpow_neg_one]
  calc (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * (t ^ (-(3 / 2 : ℝ)) - a * (t ^ (-(3 / 2 : ℝ)) * t⁻¹))
      = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (1 - a / t) := by rw [hsplit]; ring
    _ ≤ (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(a / t)) :=
        mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg (a / t))
          (Real.rpow_nonneg h4πt.le _)

theorem heatK3_tail_ge {a η : ℝ} (ha : 0 ≤ a) (hη : 0 < η) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(a / t)))
      (Set.Ioi η) ∧
    1 / (4 * Real.pi ^ (3 / 2 : ℝ) * Real.sqrt η)
        - a / (12 * Real.pi ^ (3 / 2 : ℝ) * η ^ (3 / 2 : ℝ))
      ≤ ∫ t in Set.Ioi η, (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(a / t)) := by
  have hf_int := heatK3_tail_integrable ha hη
  have h3 : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) (Set.Ioi η) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hη
  have h5 : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-(5 / 2 : ℝ))) (Set.Ioi η) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hη
  have hg_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * (t ^ (-(3 / 2 : ℝ)) - a * t ^ (-(5 / 2 : ℝ))))
      (Set.Ioi η) := (h3.sub (h5.const_mul a)).const_mul _
  have hle : ∫ t in Set.Ioi η,
        (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * (t ^ (-(3 / 2 : ℝ)) - a * t ^ (-(5 / 2 : ℝ)))
      ≤ ∫ t in Set.Ioi η, (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(a / t)) := by
    refine integral_mono_ae hg_int hf_int ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact lower_le_heatK3 hη t ht
  have hval : ∫ t in Set.Ioi η,
        (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * (t ^ (-(3 / 2 : ℝ)) - a * t ^ (-(5 / 2 : ℝ)))
      = 1 / (4 * Real.pi ^ (3 / 2 : ℝ) * Real.sqrt η)
          - a / (12 * Real.pi ^ (3 / 2 : ℝ) * η ^ (3 / 2 : ℝ)) :=
    (integral_Ioi_rpow_lower (a := a) hη).trans (arith_lower (a := a) hη)
  exact ⟨hf_int, hval ▸ hle⟩

end Work.BoseFixR.LatGreen
