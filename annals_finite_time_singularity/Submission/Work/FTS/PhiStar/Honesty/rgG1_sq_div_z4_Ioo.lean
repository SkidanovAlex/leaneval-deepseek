import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Honesty.lintegral_Ioo_triangle
import Submission.Work.FTS.PhiStar.Honesty.lintegral_ofReal_rpow_Ioo_left
import Submission.Work.FTS.PhiStar.Honesty.sq_integral_le_mul_integral_sq
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_mul_rpow_ae
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_mul_rpow_ae
import Submission.Work.FTS.PhiStar.Honesty.lintegral_rpow_prim_weighted_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.PhiStar.Honesty

/-- Weighted Hardy-type estimate behind the singular Green branch: for `r > -2`, if
`(c t)²/t⁴` is integrable on `(0,1)` and `c` is a.e. measurable, then
`z ↦ (z^{-(r+1)} ∫₀^z c t · t^r)²/z⁴` is integrable on `(0,1)`.

The proof combines

* `(∫₀^z f)² ≤ z ∫₀^z f²` (`sq_integral_le_mul_integral_sq`), giving the pointwise bound
  `(z^{-(r+1)} ∫₀^z c tᵣ)²/z⁴ ≤ z^{-(2r+5)} ∫₀^z c² t^{2r}` on `(0,1)`;
* integration of the resulting `ENNReal`-valued bound against the weight `z^{-(2r+5)}`,
  where Tonelli on the triangle `0 < t < z < 1` and the elementary primitive
  `∫_t^1 z^{-(2r+5)} dz = (t^{-(2r+4)} - 1)/(2r+4) ≤ t^{-(2r+4)}/(2r+4)` cancel the `t^{2r}`
  factor and leave `≤ (2r+4)^{-1} ∫₀^1 c²/t⁴`
  (`lintegral_rpow_prim_weighted_le`);
* the equivalence between finiteness of that `lintegral` and integrability of the
  nonnegative target (`hasFiniteIntegral_iff_ofReal`), with a.e. strong measurability
  supplied by the continuity of the primitive of `t ↦ c t · t^r`. -/
theorem integrableOn_prim_rpow_sq_div_z4 {r : ℝ} (hr : -2 < r) {c : ℝ → ℝ} (hc : AEMeasurable c)
    (hint : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1)) :
    IntegrableOn
      (fun z : ℝ => (z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4)
      (Set.Ioo 0 1) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hfIcc : IntegrableOn (fun t : ℝ => c t * t ^ r) (Set.Icc 0 1) :=
    integrableOn_mul_rpow_ae (by linarith : (-2 : ℝ) ≤ r) hc hint
  have hf2Icc : IntegrableOn (fun t : ℝ => (c t) ^ 2 * t ^ (2 * r)) (Set.Icc 0 1) :=
    integrableOn_sq_mul_rpow_ae (by linarith : (-4 : ℝ) ≤ 2 * r) hc hint
  have hf2Ioo : IntegrableOn (fun t : ℝ => (c t) ^ 2 * t ^ (2 * r)) (Set.Ioo 0 1) :=
    hf2Icc.mono_set fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  -- the pointwise rewriting of the square
  have hpow : ∀ t : ℝ, 0 ≤ t → (c t * t ^ r) ^ 2 = (c t) ^ 2 * t ^ (2 * r) := by
    intro t ht
    have htr : (t ^ r) ^ 2 = t ^ (2 * r) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
      congr 1
      ring
    rw [mul_pow, htr]
  -- Cauchy-Schwarz with the constant function `1` on `0..z`
  have hcs : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      (∫ t in (0 : ℝ)..z, c t * t ^ r) ^ 2
        ≤ z * ∫ t in (0 : ℝ)..z, (c t) ^ 2 * t ^ (2 * r) := by
    intro z hz
    have hz0 : (0 : ℝ) ≤ z := le_of_lt hz.1
    have hz1 : z ≤ 1 := le_of_lt hz.2
    have hsub : Set.Icc 0 z ⊆ Set.Icc 0 1 := fun x hx => ⟨hx.1, le_trans hx.2 hz1⟩
    have h1 : IntervalIntegrable (fun t : ℝ => c t * t ^ r) volume 0 z :=
      IntegrableOn.intervalIntegrable (by rw [uIcc_of_le hz0]; exact hfIcc.mono_set hsub)
    have h2' : IntervalIntegrable (fun t : ℝ => (c t) ^ 2 * t ^ (2 * r)) volume 0 z :=
      IntegrableOn.intervalIntegrable (by rw [uIcc_of_le hz0]; exact hf2Icc.mono_set hsub)
    have h2 : IntervalIntegrable (fun t : ℝ => (c t * t ^ r) ^ 2) volume 0 z :=
      IntervalIntegrable.congr (fun t ht => by
        rw [uIoc_of_le hz0] at ht
        exact (hpow t (le_of_lt ht.1)).symm) h2'
    have h3 := sq_integral_le_mul_integral_sq hz0 h1 h2
    have h4 : (∫ t in (0 : ℝ)..z, (c t * t ^ r) ^ 2)
        = ∫ t in (0 : ℝ)..z, (c t) ^ 2 * t ^ (2 * r) :=
      intervalIntegral.integral_congr fun t ht => by
        rw [uIcc_of_le hz0] at ht
        exact hpow t ht.1
    rw [h4] at h3
    exact h3
  -- the bound `G z ≤ z^{-(2r+5)} * ∫₀^z (c t)² t^{2r}`
  have hGbound : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      (z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4
        ≤ z ^ (-(2 * r + 5)) * ∫ t in (0 : ℝ)..z, (c t) ^ 2 * t ^ (2 * r) := by
    intro z hz
    have hz0 : 0 < z := hz.1
    have hz0' : (0 : ℝ) ≤ z := le_of_lt hz0
    have hA : (z ^ (-(r + 1))) ^ 2 = z ^ (-(2 * r + 2)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hz0']
      congr 1
      ring
    have hB : z ^ (-(2 * r + 2)) * z ^ (-((4 : ℕ) : ℝ)) = z ^ (-(2 * r + 6)) := by
      rw [← Real.rpow_add hz0]
      congr 1
      ring
    have hC : (z ^ 4)⁻¹ = z ^ (-((4 : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast z 4]
      exact (Real.rpow_neg hz0' ((4 : ℕ) : ℝ)).symm
    have he : (z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4
        = z ^ (-(2 * r + 6)) * (∫ t in (0 : ℝ)..z, c t * t ^ r) ^ 2 := by
      calc (z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4
          = ((z ^ (-(r + 1))) ^ 2 * (∫ t in (0 : ℝ)..z, c t * t ^ r) ^ 2)
              * (z ^ 4)⁻¹ := by
            rw [div_eq_mul_inv, mul_pow]
        _ = (z ^ (-(2 * r + 2)) * (∫ t in (0 : ℝ)..z, c t * t ^ r) ^ 2)
              * z ^ (-((4 : ℕ) : ℝ)) := by
            rw [hA, hC]
        _ = (z ^ (-(2 * r + 2)) * z ^ (-((4 : ℕ) : ℝ)))
              * (∫ t in (0 : ℝ)..z, c t * t ^ r) ^ 2 := by ring
        _ = z ^ (-(2 * r + 6)) * (∫ t in (0 : ℝ)..z, c t * t ^ r) ^ 2 := by rw [hB]
    rw [he]
    calc z ^ (-(2 * r + 6)) * (∫ t in (0 : ℝ)..z, c t * t ^ r) ^ 2
        ≤ z ^ (-(2 * r + 6)) * (z * ∫ t in (0 : ℝ)..z, (c t) ^ 2 * t ^ (2 * r)) :=
          mul_le_mul_of_nonneg_left (hcs z hz) (Real.rpow_nonneg hz0' _)
      _ = z ^ (-(2 * r + 5)) * ∫ t in (0 : ℝ)..z, (c t) ^ 2 * t ^ (2 * r) := by
          have hstep2 : z ^ (-(2 * r + 6)) * z = z ^ (-(2 * r + 5)) := by
            have h1 : z ^ (-(2 * r + 6)) * z = z ^ (-(2 * r + 6)) * z ^ (1 : ℝ) := by
              rw [Real.rpow_one]
            rw [h1, ← Real.rpow_add hz0]
            congr 1
            ring
          rw [← mul_assoc, hstep2]
  -- the a.e. pointwise bound in `ofReal` form
  have hstep : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal ((z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4)
        ≤ ENNReal.ofReal (z ^ (-(2 * r + 5)))
            * ∫⁻ t in Set.Ioo (0 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)) := by
    intro z hz
    have hz0 : 0 < z := hz.1
    have hzle : z ≤ 1 := le_of_lt hz.2
    have hint2 : IntegrableOn (fun t : ℝ => (c t) ^ 2 * t ^ (2 * r)) (Set.Ioo (0 : ℝ) z) :=
      hf2Ioo.mono_set fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hzle⟩
    have hnn2 : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) z)]
        (fun t : ℝ => (c t) ^ 2 * t ^ (2 * r)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt ht.1) _)
    have hconv : ENNReal.ofReal (∫ t in (0 : ℝ)..z, (c t) ^ 2 * t ^ (2 * r))
        = ∫⁻ t in Set.Ioo (0 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)) := by
      rw [intervalIntegral.integral_of_le hz0.le, integral_Ioc_eq_integral_Ioo]
      exact ofReal_integral_eq_lintegral_ofReal hint2 hnn2
    calc ENNReal.ofReal ((z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4)
        ≤ ENNReal.ofReal
            (z ^ (-(2 * r + 5)) * ∫ t in (0 : ℝ)..z, (c t) ^ 2 * t ^ (2 * r)) :=
          ENNReal.ofReal_le_ofReal (hGbound z hz)
      _ = ENNReal.ofReal (z ^ (-(2 * r + 5)))
            * ∫⁻ t in Set.Ioo (0 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hz0) _), hconv]
  have hlin1 : (∫⁻ z in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4))
      ≤ ∫⁻ z in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (z ^ (-(2 * r + 5)))
          * ∫⁻ t in Set.Ioo (0 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact hstep z hz
  -- Tonelli on the triangle, plus the elementary `z`-integral
  have hmain : (∫⁻ z in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4))
      ≤ (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
          * (ENNReal.ofReal (2 * r + 4))⁻¹ :=
    hlin1.trans (lintegral_rpow_prim_weighted_le hr hc hint)
  have hfin : (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4)) < ∞ := by
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] (fun t : ℝ => (c t) ^ 2 / t ^ 4) :=
      Eventually.of_forall fun t => div_nonneg (sq_nonneg _) (by positivity)
    exact (hasFiniteIntegral_iff_ofReal hnn).mp hint.hasFiniteIntegral
  have hlt : (∫⁻ z in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4)) < ∞ :=
    lt_of_le_of_lt hmain (ENNReal.mul_lt_top hfin
      (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (by linarith : (0 : ℝ) < 2 * r + 4))))
  -- measurability of the target function and conclusion
  have hPcont : ContinuousOn (fun z : ℝ => ∫ t in (0 : ℝ)..z, c t * t ^ r)
      (Set.Ioo (0 : ℝ) 1) :=
    (intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := 1)
      (by rw [uIcc_of_le h01]; exact hfIcc)).mono fun x hx => by
        rw [uIcc_of_le h01]
        exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hpowcont : ContinuousOn (fun z : ℝ => z ^ (-(r + 1))) (Set.Ioo (0 : ℝ) 1) :=
    fun z hz => (Real.continuousAt_rpow_const z (-(r + 1))
      (Or.inl (ne_of_gt hz.1))).continuousWithinAt
  have hcont : ContinuousOn
      (fun z : ℝ => (z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4)
      (Set.Ioo (0 : ℝ) 1) :=
    ((hpowcont.mul hPcont).pow 2).div (continuousOn_id.pow 4)
      fun z hz => pow_ne_zero 4 (ne_of_gt hz.1)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
      (fun z : ℝ => (z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact div_nonneg (sq_nonneg _) (pow_nonneg (le_of_lt hz.1) 4)
  exact ⟨hcont.aestronglyMeasurable measurableSet_Ioo,
    (hasFiniteIntegral_iff_ofReal hnn).mpr (by simpa only using hlt)⟩

/-- **Near-zero weighted square bound for the singular Green branch.**

With `q = rgQ α m ≥ 28` and `rgG1 α m c z = z^{-q} * ∫_0^z c t * t^{q-1} dt`, the function
`z ↦ (rgG1 α m c z)² / z⁴` is integrable on `(0,1)`.

HINT (verified by two reviewers).  For `z ∈ (0,1)` write `A z = ∫ t in (0)..z, rgF1 α m c t` so
that `rgG1 α m c z = z^{-(rgQ α m)} * A z` by definition.  Split
`c t * t^{q-1} = (c t * t^{-3/2}) * t^{q+1/2}`, so Cauchy–Schwarz on `0..z` gives
`(A z)² ≤ (∫ t in 0..z, (c t)² * t^{-3}) * (∫ t in 0..z, t^{2q+1})` and
`∫ t in 0..z, t^{2q+1} = z^{2q+2}/(2q+2)` (`2q+1 > -1`).  Hence
`(rgG1 z / z²)² = (rgG1 z)²/z⁴ ≤ (1/(2q+2)) * z^{-2} * ∫ t in 0..z, (c t)² t^{-3}`
`≤ (1/(2q+2)) * z^{-2} * ∫ t in 0..z, (c t)² t^{-4}` (since `t ≤ 1`).
Tonelli on the triangle `0 < t < z < 1` (`Work.FTS.PhiStar.Honesty.lintegral_Ioo_triangle`)
gives `∫_0^1 z^{-2} ∫_0^z (c t)²t^{-4} dt dz = ∫_0^1 (c t)² t^{-4} (1/t - 1) dt ≤ ∫_0^1 (c t)²/t⁴ dt < ∞`.

USEFUL FACTS (already in the workspace, or 2 lines): `rgQ_ge : 28 ≤ rgQ α m`
(`Submission.Work.FTS.EllExist.RadGreenDefs`); `Work.FTS.PhiStar.Honesty.sq_integral_le_mul_integral_sq`
(Cauchy–Schwarz `(∫_0^z f)² ≤ z ∫_0^z f²`, but you will want the weighted form above);
`Work.FTS.PhiStar.Honesty.integrableOn_mul_rpow` gives `c t * t^r ∈ L¹(0,1)` for `r ≥ -2` from
`hnear` and `hc : AEMeasurable c` (adapt: its proof only uses `hc` for measurability);
`intervalIntegral.continuousOn_primitive_interval` gives continuity (hence
`AEStronglyMeasurable`) of the primitive of an interval-integrable function — you need
`AEStronglyMeasurable` of the target integrand to apply `Integrable.mono'`.
Recover `(rgG1 z)²/z⁴` from an `IntegrableOn` statement about an a.e.-equal/nonneg dominating
function with `Integrable.mono'` (or `IntegrableOn.congr_fun_ae` after a pointwise identity). -/
theorem rgG1_sq_div_z4_Ioo {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.EllExist.rgG1 α m c z) ^ 2 / z ^ 4) (Set.Ioo 0 1) := by
  -- `hfar` is not needed: the statement only concerns the behaviour near `0`.
  have hq : (-2 : ℝ) < Work.FTS.EllExist.rgQ α m - 1 := by
    have hge := Work.FTS.EllExist.rgQ_ge hα hα4 hm
    linarith
  have hkey := integrableOn_prim_rpow_sq_div_z4 (r := Work.FTS.EllExist.rgQ α m - 1) hq hc hnear
  refine hkey.congr_fun ?_ measurableSet_Ioo
  intro z hz
  have hexp : -((Work.FTS.EllExist.rgQ α m - 1) + 1) = -(Work.FTS.EllExist.rgQ α m) := by ring
  simp only [Work.FTS.EllExist.rgG1, Work.FTS.EllExist.rgA, Work.FTS.EllExist.rgF1, hexp]

end Work.FTS.PhiStar.Honesty
