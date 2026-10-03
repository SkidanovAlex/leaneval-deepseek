import Mathlib

namespace Work.FatouL1

open MeasureTheory Real Filter

/-!
# The integral of `sech²` along the real line

`∫ y, 1 / cosh (π (y - a)) ^ 2 dy = 2 / π`, together with the integrability of the integrand.
The antiderivative is `tanh (π (y - a)) / π` (whose derivative is exactly the integrand), with
limits `±1/π` at `±∞`; integrability is obtained by dominating the integrand with `4 e^{-2t}`
resp. `4 e^{2t}` on the two half lines.
-/

/-- `deriv tanh = 1 / cosh²`. -/
lemma hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have h1 : HasDerivAt (fun x => Real.sinh x / Real.cosh x)
      ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2) x :=
    (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (ne_of_gt (Real.cosh_pos x))
  have hnum : Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x = 1 := by
    rw [← sq, ← sq, Real.cosh_sq_sub_sinh_sq]
  rw [hnum] at h1
  have h2 : Real.tanh = fun x => Real.sinh x / Real.cosh x := funext Real.tanh_eq_sinh_div_cosh
  rw [h2]
  exact h1

/-- `deriv (tanh (π (y - a)) / π) = 1 / cosh (π (y - a))²`. -/
lemma hasDerivAt_sechSqShift (a y : ℝ) :
    HasDerivAt (fun y : ℝ => Real.tanh (Real.pi * (y - a)) / Real.pi)
      (1 / Real.cosh (Real.pi * (y - a)) ^ 2) y := by
  have hcomp : HasDerivAt (fun y : ℝ => Real.tanh (Real.pi * (y - a)))
      (1 / Real.cosh (Real.pi * (y - a)) ^ 2 * Real.pi) y := by
    have hinner : HasDerivAt (fun y : ℝ => Real.pi * (y - a)) Real.pi y := by
      simpa using ((hasDerivAt_id y).sub_const a).const_mul Real.pi
    change HasDerivAt ((fun x => Real.tanh x) ∘ fun y : ℝ => Real.pi * (y - a)) _ y
    exact (hasDerivAt_tanh (Real.pi * (y - a))).comp y hinner
  have hdiv := hcomp.div_const Real.pi
  convert hdiv using 1
  field_simp

/-- `tanh` in terms of `exp (-2x)`. -/
lemma tanh_eq_ratio (x : ℝ) : Real.tanh x = (1 - Real.exp (-(2*x))) / (1 + Real.exp (-(2*x))) := by
  rw [Real.tanh_eq]
  have h2 : Real.exp (-(2*x)) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]; ring_nf
  have h1 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  rw [h2]
  have hp : Real.exp x + Real.exp (-x) ≠ 0 := by positivity
  have hq : 1 + Real.exp (-x) * Real.exp (-x) ≠ 0 := by positivity
  field_simp
  linear_combination (2 * Real.exp (-x)) * h1

lemma tendsto_tanh_atTop : Tendsto (fun x : ℝ => Real.tanh x) atTop (nhds 1) := by
  have hg : Tendsto (fun x : ℝ => 2 * x) atTop atTop := by
    simpa using tendsto_id.const_mul_atTop (show (0:ℝ) < 2 by norm_num)
  have hExp : Tendsto (fun x : ℝ => Real.exp (-(2*x))) atTop (nhds 0) := by
    simpa only [Function.comp_def] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hg
  have hnum : Tendsto (fun x : ℝ => 1 - Real.exp (-(2*x))) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hExp
  have hden : Tendsto (fun x : ℝ => 1 + Real.exp (-(2*x))) atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add hExp
  have hdiv : Tendsto ((fun x : ℝ => 1 - Real.exp (-(2*x))) / (fun x : ℝ => 1 + Real.exp (-(2*x)))) atTop (nhds ((1-0)/(1+0))) :=
    hnum.div hden (by norm_num)
  have hfin : Tendsto (fun x : ℝ => (1 - Real.exp (-(2*x))) / (1 + Real.exp (-(2*x)))) atTop (nhds ((1-0)/(1+0))) := by
    refine Tendsto.congr (fun x => ?_) hdiv
    simp [Pi.div_apply]
  have hres := Tendsto.congr (fun x => (tanh_eq_ratio x).symm) hfin
  simpa using hres

lemma tendsto_tanh_atBot : Tendsto (fun x : ℝ => Real.tanh x) atBot (nhds (-1)) := by
  have hneg : Tendsto (fun x : ℝ => Real.tanh (-x)) atTop (nhds (-1)) := by
    have := tendsto_tanh_atTop.neg
    simpa using this
  have := hneg.comp tendsto_neg_atBot_atTop
  simpa [Function.comp_def] using this

lemma tendsto_sechSqShift_atTop (a : ℝ) :
    Tendsto (fun y : ℝ => Real.tanh (Real.pi * (y - a)) / Real.pi) atTop (nhds (1 / Real.pi)) := by
  have hmap : Tendsto (fun y : ℝ => Real.pi * (y - a)) atTop atTop := by
    have h1 : Tendsto (fun y : ℝ => y + (-a)) atTop atTop := tendsto_atTop_add_const_right _ (-a) tendsto_id
    have h2 : Tendsto (fun y : ℝ => Real.pi * (y + (-a))) atTop atTop :=
      h1.const_mul_atTop (show (0:ℝ) < Real.pi by positivity)
    simpa [sub_eq_add_neg] using h2
  have hcomp : Tendsto (fun y : ℝ => Real.tanh (Real.pi * (y - a))) atTop (nhds 1) := by
    have := tendsto_tanh_atTop.comp hmap
    simpa [Function.comp_def] using this
  have hdiv := hcomp.div_const Real.pi
  simpa [Pi.div_apply] using hdiv

lemma tendsto_sechSqShift_atBot (a : ℝ) :
    Tendsto (fun y : ℝ => Real.tanh (Real.pi * (y - a)) / Real.pi) atBot (nhds (-(1 / Real.pi))) := by
  have hmap : Tendsto (fun y : ℝ => Real.pi * (y - a)) atBot atBot := by
    have h1 : Tendsto (fun y : ℝ => y + (-a)) atBot atBot := tendsto_atBot_add_const_right _ (-a) tendsto_id
    have h2 : Tendsto (fun y : ℝ => Real.pi * (y + (-a))) atBot atBot :=
      Tendsto.const_mul_atBot (show (0:ℝ) < Real.pi by positivity) h1
    simpa [sub_eq_add_neg] using h2
  have hcomp : Tendsto (fun y : ℝ => Real.tanh (Real.pi * (y - a))) atBot (nhds (-1)) := by
    have := tendsto_tanh_atBot.comp hmap
    simpa [Function.comp_def] using this
  have hdiv := hcomp.div_const Real.pi
  simpa [Pi.div_apply, neg_div] using hdiv

/-- Domination of `sech²` by `4 e^{-2t}` on the right. -/
lemma sechSq_le_exp_neg (t : ℝ) : 1 / Real.cosh t ^ 2 ≤ 4 * Real.exp (-(2*t)) := by
  have hcosh : Real.exp t / 2 ≤ Real.cosh t := by
    rw [Real.cosh_eq]; have h := Real.exp_pos (-t); linarith
  have hcosh2 : (Real.exp t / 2)^2 ≤ Real.cosh t ^ 2 := pow_le_pow_left₀ (by positivity) hcosh 2
  have hsquare : Real.exp (2*t) = (Real.exp t)^2 := by rw [sq, ← Real.exp_add]; ring_nf
  have hexpmul : Real.exp (2*t) * Real.exp (-(2*t)) = 1 := by rw [← Real.exp_add]; ring_nf; simp
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hcosh2, Real.exp_pos (2*t), Real.exp_pos (-(2*t))]

/-- Domination of `sech²` by `4 e^{2t}` on the left. -/
lemma sechSq_le_exp_pos (t : ℝ) : 1 / Real.cosh t ^ 2 ≤ 4 * Real.exp (2*t) := by
  have hcosh : Real.exp (-t) / 2 ≤ Real.cosh t := by
    rw [Real.cosh_eq]; have h := Real.exp_pos t; linarith
  have hcosh2 : (Real.exp (-t) / 2)^2 ≤ Real.cosh t ^ 2 := pow_le_pow_left₀ (by positivity) hcosh 2
  have hsquare : Real.exp (-(2*t)) = (Real.exp (-t))^2 := by rw [sq, ← Real.exp_add]; ring_nf
  have hexpmul : Real.exp (-(2*t)) * Real.exp (2*t) = 1 := by rw [← Real.exp_add]; ring_nf; simp
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hcosh2, Real.exp_pos (-(2*t)), Real.exp_pos (2*t)]

/-- `1 / cosh (π (y - a))²` is integrable on the real line. -/
lemma integrable_sechSq (a : ℝ) : Integrable (fun y : ℝ => 1 / Real.cosh (Real.pi * (y - a)) ^ 2) := by
  have hcont : Continuous (fun y : ℝ => 1 / Real.cosh (Real.pi * (y - a)) ^ 2) := by
    apply Continuous.div
    · exact continuous_const
    · exact (Real.continuous_cosh.comp ((continuous_const.mul (continuous_id.sub continuous_const)))).pow 2
    · intro y; positivity
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := a)]
  apply IntegrableOn.union
  · have hbase : IntegrableOn (fun y : ℝ => Real.exp ((2*Real.pi) * y)) (Set.Iic a) :=
      integrableOn_exp_mul_Iic (by linarith [Real.pi_pos]) a
    have hg : IntegrableOn (fun y : ℝ => 4 * Real.exp ((2*Real.pi)*(y - a))) (Set.Iic a) := by
      have h2 : IntegrableOn (fun y : ℝ => (4 * Real.exp (-(2*Real.pi*a))) * Real.exp ((2*Real.pi) * y)) (Set.Iic a) :=
        hbase.const_mul _
      refine h2.congr_fun (fun y _ => ?_) measurableSet_Iic
      have he : Real.exp ((2*Real.pi)*(y - a)) = Real.exp (-(2*Real.pi*a)) * Real.exp ((2*Real.pi)*y) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [he]; ring
    refine hg.mono' (hcont.aestronglyMeasurable.restrict) ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h := sechSq_le_exp_pos (Real.pi * (y - a))
    convert h using 2
    ring_nf
  · have hbase : IntegrableOn (fun y : ℝ => Real.exp ((-(2*Real.pi)) * y)) (Set.Ioi a) :=
      integrableOn_exp_mul_Ioi (by linarith [Real.pi_pos]) a
    have hg : IntegrableOn (fun y : ℝ => 4 * Real.exp (-(2*Real.pi)*(y - a))) (Set.Ioi a) := by
      have h2 : IntegrableOn (fun y : ℝ => (4 * Real.exp (2*Real.pi*a)) * Real.exp ((-(2*Real.pi)) * y)) (Set.Ioi a) :=
        hbase.const_mul _
      refine h2.congr_fun (fun y _ => ?_) measurableSet_Ioi
      have he : Real.exp (-(2*Real.pi)*(y - a)) = Real.exp (2*Real.pi*a) * Real.exp ((-(2*Real.pi))*y) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [he]; ring
    refine hg.mono' (hcont.aestronglyMeasurable.restrict) ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h := sechSq_le_exp_neg (Real.pi * (y - a))
    convert h using 2
    ring_nf

theorem hcIntegralSechSq (a : ℝ) :
    MeasureTheory.Integrable (fun y : ℝ => 1 / Real.cosh (Real.pi * (y - a)) ^ 2) ∧
      ∫ y : ℝ, 1 / Real.cosh (Real.pi * (y - a)) ^ 2 = 2 / Real.pi := by
  refine ⟨integrable_sechSq a, ?_⟩
  have hderiv : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Real.tanh (Real.pi * (y - a)) / Real.pi)
      (1 / Real.cosh (Real.pi * (y - a)) ^ 2) y := fun y => hasDerivAt_sechSqShift a y
  have h := integral_of_hasDerivAt_of_tendsto hderiv (integrable_sechSq a)
    (tendsto_sechSqShift_atBot a) (tendsto_sechSqShift_atTop a)
  rw [h]
  ring_nf

end Work.FatouL1
