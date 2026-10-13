/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS/ClassC/modeWeightedEnergy` — the per-mode weighted energy inequality

`modeWeightedEnergy` integrates the *pointwise* per-mode weighted energy identity
`hasDerivAt_flux` of `ModeEnergyWeighted.lean` (there: along the mode ODE,
`(flux α a)' = enInt α lam a c`) over `(0,∞)`, using the two boundary hypotheses on `flux`
(continuity from the right at `0` and decay at `+∞`):

  `α²∫_0^∞ (z a')² w²  +  (λ - 3α² - 3α(5+α)/2) ∫_0^∞ a² w²  ≤  ∫_0^∞ c a w²`,

where `w(z) = (1+z)²/z²` is the paper's radial weight.  The coercive content is the pair of
`w²`-derivative bounds of `ModeEnergyDefs.lean`, `|(z²w²)''| ≤ 6w²` and `|(z w²)'| ≤ 3w²`
(proved there), which turn the indefinite quadratic form of `enInt` into the definite one of
the displayed inequality:

* the fundamental theorem of calculus on `(0,∞)`
  (`MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto`) gives `∫_0^∞ enInt = 0` from the two
  boundary conditions (this is where `hcont` and `hdec` are used; `flux α a 0 = 0` by
  `flux_zero`);
* the pointwise domination of `enInt` by the quadratic form of the statement is
  `mweAux.enIntGeRHS` (from the two `w²`-bounds above);
* the integral of `enInt` is dominated by the integral of that quadratic form
  (`setIntegral_mono_on`), whose value is computed by linearity (`integral_rhs`).

Everything here is proved.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FTS.ClassC.ModeEnergyDefs
import Submission.Work.FTS.ClassC.ModeEnergyWeighted
import Submission.Work.FTS.ClassC.mweAux.enIntGeRHS

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-! ## Measurability of the two weight coefficients -/

private lemma measurable_rwbb_aux : Measurable rwbb := by
  rw [show rwbb = fun z : ℝ => (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4 from rfl]
  measurability

private lemma measurable_rwc_aux : Measurable rwc := by
  rw [show rwc = fun z : ℝ => (1 + z) ^ 3 * (z - 3) / z ^ 4 from rfl]
  measurability

/-! ## Integrability of `enInt` on `(0,∞)`

Every one of the five terms of `enInt α lam a c` is integrable on `(0,∞)`: the first, fourth
and fifth are (multiples of) the three integrands of the hypotheses, while the middle two are
dominated by `6·(a z)²w(z)²` and `3·(a z)²w(z)²` by the two `w²`-bounds of `ModeEnergyDefs`.
-/

lemma integrableOn_enInt {α lam : ℝ} {a c : ℝ → ℝ}
    (hac : ContinuousOn a (Set.Ioi 0))
    (hint1 : MeasureTheory.IntegrableOn
      (fun z => (z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint2 : MeasureTheory.IntegrableOn
      (fun z => (a z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint3 : MeasureTheory.IntegrableOn
      (fun z => c z * a z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn (enInt α lam a c) (Set.Ioi 0) := by
  have hbb : MeasureTheory.IntegrableOn (fun z => rwbb z * (a z) ^ 2) (Set.Ioi 0) := by
    refine (hint2.const_mul (6:ℝ)).mono' ?_ ?_
    · exact measurable_rwbb_aux.aestronglyMeasurable.mul
        ((hac.pow 2).aestronglyMeasurable measurableSet_Ioi)
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with z hz
      have h1 : |rwbb z| ≤ 6 * (Work.Spaces.w z) ^ 2 := abs_rwbb_le hz
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (a z))]
      calc |rwbb z| * a z ^ 2 ≤ (6 * (Work.Spaces.w z) ^ 2) * a z ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ = 6 * (a z ^ 2 * (Work.Spaces.w z) ^ 2) := by ring
  have hcc : MeasureTheory.IntegrableOn (fun z => rwc z * (a z) ^ 2) (Set.Ioi 0) := by
    refine (hint2.const_mul (3:ℝ)).mono' ?_ ?_
    · exact measurable_rwc_aux.aestronglyMeasurable.mul
        ((hac.pow 2).aestronglyMeasurable measurableSet_Ioi)
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with z hz
      have h1 : |rwc z| ≤ 3 * (Work.Spaces.w z) ^ 2 := abs_rwc_le hz
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (a z))]
      calc |rwc z| * a z ^ 2 ≤ (3 * (Work.Spaces.w z) ^ 2) * a z ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ = 3 * (a z ^ 2 * (Work.Spaces.w z) ^ 2) := by ring
  have h1 : MeasureTheory.IntegrableOn (fun z => α ^ 2 * (rw z * (deriv a z) ^ 2))
      (Set.Ioi 0) := by
    refine hint1.const_mul (α ^ 2) |>.congr (Filter.Eventually.of_forall fun z => ?_)
    show α ^ 2 * ((z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = α ^ 2 * (rw z * (deriv a z) ^ 2)
    rw [rw_eq_w]; ring
  have h2 : MeasureTheory.IntegrableOn (fun z => (α ^ 2 / 2) * (rwbb z * (a z) ^ 2))
      (Set.Ioi 0) := hbb.const_mul _
  have h3 : MeasureTheory.IntegrableOn (fun z => ((α * (5 + α)) / 2) * (rwc z * (a z) ^ 2))
      (Set.Ioi 0) := hcc.const_mul _
  have h4 : MeasureTheory.IntegrableOn (fun z => lam * ((a z) ^ 2 * (Work.Spaces.w z) ^ 2))
      (Set.Ioi 0) := hint2.const_mul _
  refine ((((h1.sub h2).add h3).add h4).sub hint3).congr ?_
  filter_upwards with z
  simp only [Pi.sub_apply, Pi.add_apply, enInt]
  ring

/-! ## The quadratic form on the right-hand side -/

/-- Integrability of the quadratic form appearing in the statement. -/
lemma integrableOn_rhs {α lam : ℝ} {a c : ℝ → ℝ}
    (hint1 : MeasureTheory.IntegrableOn
      (fun z => (z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint2 : MeasureTheory.IntegrableOn
      (fun z => (a z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint3 : MeasureTheory.IntegrableOn
      (fun z => c z * a z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn
      (fun z => α ^ 2 * ((z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (lam - 3 * α ^ 2 - 3 * α * (5 + α) / 2) * ((a z) ^ 2 * (Work.Spaces.w z) ^ 2)
        - c z * a z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have h1 : MeasureTheory.IntegrableOn
      (fun z => α ^ 2 * ((z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2)) (Set.Ioi 0) :=
    hint1.const_mul _
  have h2 : MeasureTheory.IntegrableOn
      (fun z => (lam - 3 * α ^ 2 - 3 * α * (5 + α) / 2)
        * ((a z) ^ 2 * (Work.Spaces.w z) ^ 2)) (Set.Ioi 0) := hint2.const_mul _
  exact ((h1.add h2).sub hint3).congr
    (Filter.Eventually.of_forall fun z => by
      simp only [Pi.add_apply, Pi.sub_apply]
      try ring)

/-- The value of the integral of that quadratic form. -/
lemma integral_rhs {α lam : ℝ} {a c : ℝ → ℝ}
    (hint1 : MeasureTheory.IntegrableOn
      (fun z => (z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint2 : MeasureTheory.IntegrableOn
      (fun z => (a z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint3 : MeasureTheory.IntegrableOn
      (fun z => c z * a z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0)) :
    (∫ z in Set.Ioi 0, (α ^ 2 * ((z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (lam - 3 * α ^ 2 - 3 * α * (5 + α) / 2) * ((a z) ^ 2 * (Work.Spaces.w z) ^ 2)
        - c z * a z * (Work.Spaces.w z) ^ 2))
      = α ^ 2 * (∫ z in Set.Ioi 0, (z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (lam - 3 * α ^ 2 - 3 * α * (5 + α) / 2)
          * (∫ z in Set.Ioi 0, (a z) ^ 2 * (Work.Spaces.w z) ^ 2)
        - ∫ z in Set.Ioi 0, c z * a z * (Work.Spaces.w z) ^ 2 := by
  have h1 : MeasureTheory.IntegrableOn
      (fun z => α ^ 2 * ((z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2)) (Set.Ioi 0) :=
    hint1.const_mul _
  have h2 : MeasureTheory.IntegrableOn
      (fun z => (lam - 3 * α ^ 2 - 3 * α * (5 + α) / 2)
        * ((a z) ^ 2 * (Work.Spaces.w z) ^ 2)) (Set.Ioi 0) := hint2.const_mul _
  have h12 : MeasureTheory.IntegrableOn
      (fun z => α ^ 2 * ((z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (lam - 3 * α ^ 2 - 3 * α * (5 + α) / 2) * ((a z) ^ 2 * (Work.Spaces.w z) ^ 2))
      (Set.Ioi 0) := h1.add h2
  rw [show (fun z => α ^ 2 * ((z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (lam - 3 * α ^ 2 - 3 * α * (5 + α) / 2) * ((a z) ^ 2 * (Work.Spaces.w z) ^ 2)
        - c z * a z * (Work.Spaces.w z) ^ 2)
      = (fun z => (α ^ 2 * ((z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (lam - 3 * α ^ 2 - 3 * α * (5 + α) / 2) * ((a z) ^ 2 * (Work.Spaces.w z) ^ 2))
        - (c z * a z * (Work.Spaces.w z) ^ 2)) from rfl]
  rw [MeasureTheory.integral_sub h12 hint3, MeasureTheory.integral_add h1 h2,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-! ## The per-mode weighted energy inequality -/

theorem modeWeightedEnergy {α lam : ℝ} (hα : 0 < α) {a c : ℝ → ℝ}
    (hac : ContinuousOn a (Set.Ioi 0))
    (ha : ∀ z, 0 < z → HasDerivAt a (deriv a z) z)
    (ha' : ∀ z, 0 < z → HasDerivAt (deriv a) (deriv (deriv a) z) z)
    (hode : ∀ z, 0 < z → α ^ 2 * z ^ 2 * deriv (deriv a) z + α * (5 + α) * z * deriv a z
        = lam * a z - c z)
    (hint1 : MeasureTheory.IntegrableOn
      (fun z => (z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint2 : MeasureTheory.IntegrableOn
      (fun z => (a z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint3 : MeasureTheory.IntegrableOn
      (fun z => c z * a z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hcont : ContinuousWithinAt (Work.FTS.ClassC.flux α a) (Set.Ici 0) 0)
    (hdec : Filter.Tendsto (Work.FTS.ClassC.flux α a) Filter.atTop (nhds 0)) :
    α ^ 2 * (∫ z in Set.Ioi 0, (z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2)
      + (lam - 3 * α ^ 2 - 3 * α * (5 + α) / 2)
          * (∫ z in Set.Ioi 0, (a z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Set.Ioi 0, c z * a z * (Work.Spaces.w z) ^ 2 := by
  -- `enInt` is integrable and `flux` is its primitive along the mode ODE
  have hInt : MeasureTheory.IntegrableOn (enInt α lam a c) (Set.Ioi 0) :=
    integrableOn_enInt hac hint1 hint2 hint3
  have hderiv : ∀ z ∈ Set.Ioi (0:ℝ), HasDerivAt (flux α a) (enInt α lam a c z) z :=
    fun z hz => hasDerivAt_flux hα hz (ha z hz) (ha' z hz) (hode z hz)
  -- the fundamental theorem of calculus on `(0,∞)`: both boundary terms vanish
  have hFTC : ∫ z in Set.Ioi 0, enInt α lam a c z = 0 := by
    have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto (a := (0:ℝ)) hcont hderiv hInt
      hdec
    rw [flux_zero, sub_zero] at h
    exact h
  -- the pointwise domination, integrated
  have hIntRHS := integrableOn_rhs (α := α) (lam := lam) hint1 hint2 hint3
  have hmono : (∫ z in Set.Ioi 0, (α ^ 2 * ((z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (lam - 3 * α ^ 2 - 3 * α * (5 + α) / 2) * ((a z) ^ 2 * (Work.Spaces.w z) ^ 2)
        - c z * a z * (Work.Spaces.w z) ^ 2))
      ≤ ∫ z in Set.Ioi 0, enInt α lam a c z :=
    setIntegral_mono_on hIntRHS hInt measurableSet_Ioi fun z hz => mweAux.enIntGeRHS hα z hz
  have hval := integral_rhs (α := α) (lam := lam) hint1 hint2 hint3
  rw [hFTC] at hmono
  rw [hval] at hmono
  linarith

end Work.FTS.ClassC
