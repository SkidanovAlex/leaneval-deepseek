/-
# The Cauchy–Schwarz bound for the inner integral `G1A` of the singular Green term

`G1A α m c x = ∫_0^x c t · t^{a-1} dt` with `a = G1a α m = (2m+5)/α > 0`.  Writing the integrand
as

  `c t · t^{a-1} = (c t / t²) · t^{a+1}`   (`t > 0`),

the Cauchy–Schwarz inequality on `(0,x)`, `x < 1`, for the pair `u t = c t / t²`, `v t = t^{a+1}`
gives

  `(G1A x)² ≤ (∫_0^x c t²/t⁴ dt) · (∫_0^x t^{2a+2} dt) ≤ M0 · x^{2a+3}/(2a+3)`,

where `M0 = G1M0 c = ∫_{(0,1)} c z²/z⁴ dz` and `∫_0^x t^{2a+2} = x^{2a+3}/(2a+3)`.

This is the endpoint (`z → 0`) estimate `|G1A x| ≤ x^{(3+2a)/2} √(M0/(2a+3))` in squared form; it
is the input of `G1_sq_div_cube_le`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.EllExist.Honesty.G1Aux
import Submission.Work.Blocks.IMC.cs_integral_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty.G1Endpoint

open MeasureTheory Set Filter

theorem g1A_sq_le {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1)) :
    ∀ x : ℝ, 0 < x → x < 1 →
      Work.FTS.EllExist.Honesty.G1A α m c x ^ 2
        ≤ Work.FTS.EllExist.Honesty.G1M0 c
            * (x ^ (2 * Work.FTS.EllExist.Honesty.G1a α m + 3)
                / (2 * Work.FTS.EllExist.Honesty.G1a α m + 3)) := by
  intro x hx0 hx1
  have ha : 0 < G1a α m := G1a_pos hα m
  have hsmeas : MeasurableSet (Ioo (0 : ℝ) x) := measurableSet_Ioo
  -- ### Continuity of the two Cauchy–Schwarz factors on `(0,x)`
  have hfc : ContinuousOn (fun t : ℝ => c t / t ^ 2) (Ioo (0 : ℝ) x) :=
    (hc.mono (fun t ht => ht.1)).div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (ne_of_gt ht.1))
  have hgc : ContinuousOn (fun t : ℝ => t ^ (G1a α m + 1)) (Ioo (0 : ℝ) x) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht.1))
  -- ### Integrability of the squares on `(0,x)`
  have hf2 : Integrable (fun t : ℝ => (c t / t ^ 2) ^ 2)
      (volume.restrict (Ioo (0 : ℝ) x)) := by
    have hInt1 : IntegrableOn (fun z : ℝ => c z ^ 2 / z ^ 4) (Ioo (0 : ℝ) x) :=
      h0.mono_set (fun z hz => ⟨hz.1, lt_trans hz.2 hx1⟩)
    refine hInt1.congr_fun ?_ hsmeas
    intro t _
    change c t ^ 2 / t ^ 4 = (c t / t ^ 2) ^ 2
    rw [div_pow, ← pow_mul]
  have hg2 : Integrable (fun t : ℝ => (t ^ (G1a α m + 1)) ^ 2)
      (volume.restrict (Ioo (0 : ℝ) x)) := by
    have hr : IntegrableOn (fun t : ℝ => t ^ (2 * G1a α m + 2)) (Ioo (0 : ℝ) x) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hx0).mpr (by linarith)
    refine hr.congr_fun ?_ hsmeas
    intro t ht
    change t ^ (2 * G1a α m + 2) = (t ^ (G1a α m + 1)) ^ 2
    rw [pow_two, ← Real.rpow_add ht.1 (G1a α m + 1) (G1a α m + 1)]
    congr 1
    ring
  -- ### Cauchy–Schwarz
  have hcs : |∫ t in Ioo (0 : ℝ) x, (c t / t ^ 2) * t ^ (G1a α m + 1)|
      ≤ Real.sqrt (∫ t in Ioo (0 : ℝ) x, (c t / t ^ 2) ^ 2)
        * Real.sqrt (∫ t in Ioo (0 : ℝ) x, (t ^ (G1a α m + 1)) ^ 2) :=
    Work.Blocks.IMC.cs_integral_mul_le (volume.restrict (Ioo (0 : ℝ) x))
      (hfc.aestronglyMeasurable hsmeas) (hgc.aestronglyMeasurable hsmeas) hf2 hg2
  -- ### The `D_z`-factor: `∫_0^x c t²/t⁴ ≤ M0`
  have hA : ∫ t in Ioo (0 : ℝ) x, (c t / t ^ 2) ^ 2 ≤ G1M0 c := by
    have h1 : ∫ t in Ioo (0 : ℝ) x, (c t / t ^ 2) ^ 2
        = ∫ t in Ioo (0 : ℝ) x, c t ^ 2 / t ^ 4 := by
      refine setIntegral_congr_fun hsmeas ?_
      intro t _
      change (c t / t ^ 2) ^ 2 = c t ^ 2 / t ^ 4
      rw [div_pow, ← pow_mul]
    rw [h1, G1M0]
    exact setIntegral_mono_set h0
      (Eventually.of_forall (fun t : ℝ => div_nonneg (sq_nonneg _) (by positivity)))
      (Eventually.of_forall (fun t ht => ⟨ht.1, lt_trans ht.2 hx1⟩))
  -- ### The power factor: `∫_0^x t^{2a+2} = x^{2a+3}/(2a+3)`
  have hC : ∫ t in Ioo (0 : ℝ) x, (t ^ (G1a α m + 1)) ^ 2
      = x ^ (2 * G1a α m + 3) / (2 * G1a α m + 3) := by
    have h1 : ∫ t in Ioo (0 : ℝ) x, (t ^ (G1a α m + 1)) ^ 2
        = ∫ t in Ioo (0 : ℝ) x, t ^ (2 * G1a α m + 2) := by
      refine setIntegral_congr_fun hsmeas ?_
      intro t ht
      change (t ^ (G1a α m + 1)) ^ 2 = t ^ (2 * G1a α m + 2)
      rw [pow_two, ← Real.rpow_add ht.1 (G1a α m + 1) (G1a α m + 1)]
      congr 1
      ring
    rw [h1, setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := x)),
      ← intervalIntegral.integral_of_le hx0.le,
      integral_rpow (Or.inl (by linarith : (-1 : ℝ) < 2 * G1a α m + 2)),
      Real.zero_rpow (x := (2 * G1a α m + 2) + 1) (by intro hz; linarith [ha, hz]),
      sub_zero]
    have hexp : (2 * G1a α m + 2) + 1 = 2 * G1a α m + 3 := by ring
    rw [hexp]
  -- ### `G1A x` as a set integral of the product
  have hG1A : G1A α m c x
      = ∫ t in Ioo (0 : ℝ) x, (c t / t ^ 2) * t ^ (G1a α m + 1) := by
    rw [G1A, intervalIntegral.integral_of_le hx0.le,
      ← setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := x))]
    refine setIntegral_congr_fun hsmeas ?_
    intro t ht
    have ht0 : 0 < t := ht.1
    change c t * t ^ (G1a α m - 1) = c t / t ^ 2 * t ^ (G1a α m + 1)
    have key : t ^ (G1a α m - 1) * t ^ 2 = t ^ (G1a α m + 1) := by
      have h2 : t ^ 2 = t ^ (2 : ℝ) := (Real.rpow_two t).symm
      rw [h2, ← Real.rpow_add ht0 (G1a α m - 1) (2 : ℝ)]
      congr 1
      ring
    have hdiv : t ^ (G1a α m + 1) / t ^ 2 = t ^ (G1a α m - 1) := by
      rw [div_eq_iff (pow_ne_zero 2 (ne_of_gt ht0))]
      exact key.symm
    rw [div_mul_eq_mul_div, mul_div_assoc, hdiv]
  -- ### Assembly
  have hAnn : 0 ≤ ∫ t in Ioo (0 : ℝ) x, (c t / t ^ 2) ^ 2 :=
    setIntegral_nonneg hsmeas (fun t _ => sq_nonneg _)
  have hCnn : 0 ≤ ∫ t in Ioo (0 : ℝ) x, (t ^ (G1a α m + 1)) ^ 2 :=
    setIntegral_nonneg hsmeas (fun t _ => sq_nonneg _)
  calc G1A α m c x ^ 2
      = (∫ t in Ioo (0 : ℝ) x, (c t / t ^ 2) * t ^ (G1a α m + 1)) ^ 2 := by rw [hG1A]
    _ = |∫ t in Ioo (0 : ℝ) x, (c t / t ^ 2) * t ^ (G1a α m + 1)| ^ 2 := by rw [sq_abs]
    _ ≤ (Real.sqrt (∫ t in Ioo (0 : ℝ) x, (c t / t ^ 2) ^ 2)
          * Real.sqrt (∫ t in Ioo (0 : ℝ) x, (t ^ (G1a α m + 1)) ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hcs 2
    _ = (∫ t in Ioo (0 : ℝ) x, (c t / t ^ 2) ^ 2)
          * (∫ t in Ioo (0 : ℝ) x, (t ^ (G1a α m + 1)) ^ 2) := by
        rw [mul_pow, Real.sq_sqrt hAnn, Real.sq_sqrt hCnn]
    _ ≤ G1M0 c * (∫ t in Ioo (0 : ℝ) x, (t ^ (G1a α m + 1)) ^ 2) :=
        mul_le_mul_of_nonneg_right hA hCnn
    _ = G1M0 c * (x ^ (2 * G1a α m + 3) / (2 * G1a α m + 3)) := by rw [hC]

end Work.FTS.EllExist.Honesty.G1Endpoint
