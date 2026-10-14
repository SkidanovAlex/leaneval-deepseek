import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.Have
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.ClassC.modeWeightedEnergy =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.moment_eq_deriv_cos3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The antiderivative of `sinCos2 θ = sin θ cos²θ` that vanishes at `θ = π/2`:
`g θ = -(1/3) cos³θ`. -/
def cosCube (θ : ℝ) : ℝ := -(1 / 3) * Real.cos θ ^ 3

theorem hasDerivAt_cosCube (θ : ℝ) : HasDerivAt cosCube (Work.Elliptic.sinCos2 θ) θ := by
  have h : HasDerivAt (fun θ : ℝ => Real.cos θ ^ 3)
      (3 * Real.cos θ ^ (3 - 1) * (-Real.sin θ)) θ := (Real.hasDerivAt_cos θ).pow 3
  have h2 : HasDerivAt (fun θ : ℝ => -(1 / 3) * Real.cos θ ^ 3)
      (-(1 / 3) * (3 * Real.cos θ ^ (3 - 1) * (-Real.sin θ))) θ := h.const_mul (-(1 / 3))
  show HasDerivAt (fun θ : ℝ => -(1 / 3) * Real.cos θ ^ 3) (Work.Elliptic.sinCos2 θ) θ
  convert h2 using 1
  simp only [Work.Elliptic.sinCos2]
  ring



theorem cosCube_zero : cosCube 0 = -(1 / 3) := by
  simp [cosCube]

/-- `deriv f` is continuous on the open interval `(0, π/2)` when `f` is `C¹` on the closed
interval: at interior points the two-sided derivative agrees with the one-sided one, and the
latter is continuous on the compact interval. -/
theorem continuousOn_deriv_Ioo_of_contDiffOn {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (π / 2))) :
    ContinuousOn (deriv f) (Set.Ioo 0 (π / 2)) := by
  have hpos : (0 : ℝ) < π / 2 := by positivity
  have hUniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) (π / 2)) := uniqueDiffOn_Icc hpos
  have hcont : ContinuousOn (derivWithin f (Set.Icc (0 : ℝ) (π / 2)))
      (Set.Icc (0 : ℝ) (π / 2)) := hf.continuousOn_derivWithin hUniq le_rfl
  refine (hcont.mono Set.Ioo_subset_Icc_self).congr ?_
  intro x hx
  exact (derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)).symm


/-- `deriv f` is interval integrable on `[0, π/2]` for `f` of class `C¹` there: it is
continuous on the open interval and bounded there by the bound of
`Work.Elliptic.contDiffOn_one_bounds`. -/
theorem intervalIntegrable_deriv_of_contDiffOn {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (π / 2))) (h0 : f 0 = 0) (hπ : f (π / 2) = 0) :
    IntervalIntegrable (deriv f) volume (0 : ℝ) (π / 2) := by
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  obtain ⟨C, -, -, hbound⟩ := Work.Elliptic.contDiffOn_one_bounds hf h0 hπ
  exact Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hpi
    (continuousOn_deriv_Ioo_of_contDiffOn hf) C (fun x hx => by
      simpa [Real.norm_eq_abs] using hbound x hx)



end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.WDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The integrands

`PsiEta`/`PsiGam m` are the *honest angular data* (`θ`-integrals), `SubEta`/`SubGam m`/`HonGam m`
their pullbacks under `x = sin(2θ)` (with the Jacobian `1/(2κ x)`), `Wide l` the `x`-weighted
square of the `(l+1)`-st derivative of the slice, and `Dom`/`AccDom` the dominating functions
produced by the triangular inversion. -/

/-- `(∂_θh)² sin(2θ)^{-η}`. -/
def PsiEta (h : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- `(D_θ^m(∂_θh))² sin(2θ)^{-γ}`. -/
def PsiGam (α : ℝ) (h : ℝ → ℝ) (m : ℕ) : ℝ → ℝ :=
  fun θ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

/-- The `x`-pullback of `PsiEta`. -/
def SubEta (h : ℝ → ℝ) : ℝ → ℝ :=
  fun x => PsiEta h (thetaOf x) * (1 / (2 * kappa x))

/-- The `x`-pullback of `PsiGam m`. -/
def SubGam (α : ℝ) (h : ℝ → ℝ) (m : ℕ) : ℝ → ℝ :=
  fun x => PsiGam α h m (thetaOf x) * (1 / (2 * kappa x))

/-- The `x`-pullback of `PsiGam m` with `sin(2θ(x))` evaluated as `x`. -/
def HonGam (α : ℝ) (h : ℝ → ℝ) (m : ℕ) : ℝ → ℝ :=
  fun x => (Work.Elliptic.Dth1Iter m (deriv h) (thetaOf x)) ^ 2
    * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))

/-- The integrand `x ↦ x^{2l-γ}(∂_x^{l+1}(sliceX h) x)²` of `B_l`. -/
def Wide (α : ℝ) (h : ℝ → ℝ) (l : ℕ) : ℝ → ℝ :=
  fun x => x ^ (2 * (l : ℝ) - Work.Spaces.gam α)
    * (iteratedDeriv (l + 1) (sliceX h) x) ^ 2

/-- The off-diagonal part of the level-`j` expansion. -/
def Restn (h : ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  fun x => ∑ l ∈ Finset.range j,
    aCoeff j l x * (x ^ l * iteratedDeriv (l + 1) (sliceX h) x)

/-- The full `j`-th expansion of `D_θ^j(∂_θh)(θ x)`. -/
def Expn (h : ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  fun x => ∑ l ∈ Finset.range (j + 1),
    aCoeff j l x * (x ^ l * iteratedDeriv (l + 1) (sliceX h) x)

/-- The joint recursion producing the dominating functions `Dom` and their partial sums
`AccDom`. -/
def domSeq (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) : ℕ → (ℝ → ℝ) × (ℝ → ℝ)
  | 0 => (SubEta h, fun _ => 0)
  | (l + 1) =>
      (fun x => 2 * HonGam α h (l + 1) x
          + 2 * (((l + 1 : ℕ) : ℝ)) * Cm ^ 2
              * ((domSeq α h Cm l).2 x + (domSeq α h Cm l).1 x),
        fun x => (domSeq α h Cm l).2 x + (domSeq α h Cm l).1 x)

/-- An integrable dominating function for the level-`l` quantity. -/
def Dom (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (l : ℕ) : ℝ → ℝ := (domSeq α h Cm l).1

/-- The partial sum `Σ_{m < l} Dom m`. -/
def AccDom (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (l : ℕ) : ℝ → ℝ := (domSeq α h Cm l).2

/-! ## Elementary substitution facts -/

private lemma xNear_sq : xNear ^ 2 = 1 / 2 := by
  rw [xNear, Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- `sin (2 θ(x)) = x` for `x ∈ [-1,1]`. -/
lemma sin_two_thetaOf {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Real.sin (2 * thetaOf x) = x := by
  have h2 : 2 * thetaOf x = Real.arcsin x := by simp only [thetaOf]; ring
  rw [h2, Real.sin_arcsin hx.1 hx.2]

/-- `sin (2 θ(x)) = x` on the near interval. -/
lemma sin_two_thetaOf_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) xNear) :
    Real.sin (2 * thetaOf x) = x :=
  sin_two_thetaOf ⟨by linarith [hx.1], by linarith [hx.2, xNear_lt]⟩

/-- On the near interval `(0,x₁)`, `θ(x)` lands in the angular interval `(0,π/2)`. -/
lemma thetaOf_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo 0 xNear) :
    thetaOf x ∈ Set.Ioo 0 (Real.pi / 2) := by
  have ha0 : 0 < Real.arcsin x := Real.arcsin_pos.mpr hx.1
  have ha2 : Real.arcsin x ≤ Real.pi / 2 := (Real.arcsin_mem_Icc x).2
  constructor <;> simp only [thetaOf] <;> linarith

/-- `θ(x₁) = π/8`. -/
lemma thetaOf_xNear : thetaOf xNear = Real.pi / 8 := by
  rw [thetaOf, xNear, Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  ring

lemma thetaOf_zero : thetaOf 0 = 0 := by simp [thetaOf]

/-- `θ` is differentiable with derivative the Jacobian `1/(2κ x)`. -/
lemma hasDerivAt_thetaOf' {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt thetaOf (1 / (2 * kappa x)) x := by
  have h1 : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x :=
    Real.hasDerivAt_arcsin (ne_of_gt hx.1) (ne_of_lt hx.2)
  have h2 : HasDerivAt (fun y => Real.arcsin y / 2) ((1 / Real.sqrt (1 - x ^ 2)) / 2) x :=
    h1.div_const 2
  have hval : (1 / Real.sqrt (1 - x ^ 2)) / 2 = 1 / (2 * kappa x) := by
    rw [kappa_eq_sqrt]; ring
  exact h2.congr_deriv hval

/-- `1/√2 ≤ κ x` on `[0,x₁]`. -/
lemma kappa_ge {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) xNear) :
    1 / Real.sqrt 2 ≤ kappa x := by
  have hxnn : 0 ≤ x := hx.1
  have hxsq : x ^ 2 ≤ 1 / 2 := by
    have h1 : x * x ≤ xNear * xNear :=
      mul_le_mul hx.2 hx.2 hxnn (le_trans hxnn hx.2)
    have h2 : xNear * xNear = 1 / 2 := by simpa [pow_two] using xNear_sq
    nlinarith [h1, h2]
  have hsqrt : Real.sqrt (1 / 2) ≤ Real.sqrt (1 - x ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have h2 : Real.sqrt (1 / 2) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1) 2, Real.sqrt_one]
  rw [kappa_eq_sqrt]
  linarith [hsqrt, h2]

/-- `1 ≤ 2 κ x` on `[0,x₁]`. -/
lemma two_kappa_ge_one {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) xNear) :
    1 ≤ 2 * kappa x := by
  have h := kappa_ge hx
  have h2 : (2:ℝ) * (1 / Real.sqrt 2) = Real.sqrt 2 := by
    rw [mul_one_div, div_eq_iff (by positivity : (Real.sqrt 2) ≠ 0)]
    rw [← pow_two, Real.sq_sqrt (by norm_num)]
  have h3 : (1:ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  linarith [h, h2, h3]

/-- `γ < 4 + η` for `α ≤ 1`. -/
lemma gam_lt_four {α : ℝ} (hα : α ≤ 1) : Work.Spaces.gam α < 4 + Work.Spaces.eta := by
  unfold Work.Spaces.gam Work.Spaces.eta; linarith

lemma psiEta_nonneg (h : ℝ → ℝ) :
    ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ PsiEta h θ := by
  intro θ hθ
  have hs : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;>
      simp only [Work.Spaces.Iθ, Set.mem_Icc] at hθ <;> linarith
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)

lemma psiGam_nonneg (α : ℝ) (h : ℝ → ℝ) (m : ℕ) :
    ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ PsiGam α h m θ := by
  intro θ hθ
  have hs : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;>
      simp only [Work.Spaces.Iθ, Set.mem_Icc] at hθ <;> linarith
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)

/-- The chain rule for `sliceX h = h ∘ θ` on the near interval. -/
lemma deriv_sliceX_eq {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 xNear) :
    deriv (sliceX h) x = deriv h (thetaOf x) * (1 / (2 * kappa x)) := by
  have hyI : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2, xNear_lt]⟩
  have hmem : thetaOf x ∈ Set.Ioo 0 (Real.pi / 2) := thetaOf_mem_Ioo hx
  have hdh : DifferentiableAt ℝ h (thetaOf x) :=
    ((hsm.contDiffAt (isOpen_Ioo.mem_nhds hmem)).differentiableAt (by simp))
  exact (hdh.hasDerivAt.comp x (hasDerivAt_thetaOf' hyI)).deriv

/-- `sliceX h = h ∘ θ` is `C^∞` on the near interval. -/
lemma contDiffOn_sliceX {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sliceX h) (Set.Ioo 0 xNear) := by
  have hθ : ContDiffOn ℝ (⊤ : ℕ∞) thetaOf (Set.Ioo 0 xNear) := by
    intro x hx
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) Real.arcsin x :=
      Real.contDiffAt_arcsin (by linarith [hx.1]) (by linarith [hx.2, xNear_lt])
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) thetaOf x := h1.div_const 2
    exact h2.contDiffWithinAt
  exact hsm.comp hθ (fun x hx => thetaOf_mem_Ioo hx)

/-- Every iterated `x`-derivative of `sliceX h` is `C^∞` on the near interval. -/
lemma contDiffOn_iteratedDeriv_sliceX {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv n (sliceX h)) (Set.Ioo 0 xNear) := by
  induction n with
  | zero => simpa using contDiffOn_sliceX hsm
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv_of_isOpen isOpen_Ioo (by simp)

/-- The auxiliary `x^{-η}(∂_x(sliceX h))²` of the `l = 0` slot is dominated by `SubEta`. -/
lemma etaPiece_le_subEta {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 xNear) :
    x ^ (-(Work.Spaces.eta)) * (deriv (sliceX h) x) ^ 2 ≤ SubEta h x := by
  have hxnn : (0:ℝ) ≤ x := le_of_lt hx.1
  have hk1 : (1:ℝ) ≤ 2 * kappa x := two_kappa_ge_one ⟨hxnn, le_of_lt hx.2⟩
  have hkpos : (0:ℝ) < 2 * kappa x := lt_of_lt_of_le one_pos hk1
  have hs : Real.sin (2 * thetaOf x) = x := sin_two_thetaOf_Ioo hx
  have hd : deriv (sliceX h) x = deriv h (thetaOf x) * (1 / (2 * kappa x)) :=
    deriv_sliceX_eq hsm hx
  have h1 : (1:ℝ) / (2 * kappa x) ≤ 1 := by
    rw [div_le_one hkpos]; linarith
  have h2 : (0:ℝ) ≤ (deriv h (thetaOf x)) ^ 2 * x ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hxnn _)
  simp only [SubEta, PsiEta, hs]
  rw [hd]
  have hrw : x ^ (-(Work.Spaces.eta))
        * (deriv h (thetaOf x) * (1 / (2 * kappa x))) ^ 2
      = (deriv h (thetaOf x)) ^ 2 * x ^ (-(Work.Spaces.eta))
          * (1 / (2 * kappa x)) ^ 2 := by
    ring
  rw [hrw]
  have h3 : (1 / (2 * kappa x)) ^ 2 ≤ 1 / (2 * kappa x) := by
    have hnn : (0:ℝ) ≤ 1 / (2 * kappa x) := by positivity
    nlinarith [h1, hnn]
  calc (deriv h (thetaOf x)) ^ 2 * x ^ (-(Work.Spaces.eta)) * (1 / (2 * kappa x)) ^ 2
      ≤ (deriv h (thetaOf x)) ^ 2 * x ^ (-(Work.Spaces.eta)) * (1 / (2 * kappa x)) :=
        mul_le_mul_of_nonneg_left h3 h2
    _ = (deriv h (thetaOf x)) ^ 2 * x ^ (-(Work.Spaces.eta)) * (1 / (2 * kappa x)) := rfl

/-! ## Integrability of the two building blocks -/

/-- The `η`-pullback of the honest `η`-data is integrable on `(0,x₁)`. -/
lemma subEta_integrable {h : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (PsiEta h) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (SubEta h) (Set.Ioo 0 xNear) := by
  have h1 : MeasureTheory.IntegrableOn (SubEta h) (Set.Ioc 0 xNear) :=
    (thetaOfSubst (Ψ := PsiEta h) hint (psiEta_nonneg h)).1
  rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
  exact h1

/-- The `x`-pullback of the honest `γ`-data at order `m` is integrable on `(0,x₁)`. -/
lemma subGam_integrable {α : ℝ} {h : ℝ → ℝ} {m : ℕ}
    (hint : MeasureTheory.IntegrableOn (PsiGam α h m) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (SubGam α h m) (Set.Ioo 0 xNear) := by
  have h1 : MeasureTheory.IntegrableOn (SubGam α h m) (Set.Ioc 0 xNear) :=
    (thetaOfSubst (Ψ := PsiGam α h m) hint (psiGam_nonneg α h m)).1
  rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
  exact h1

/-- The same, with `sin(2θ(x))` evaluated as `x`. -/
lemma honGam_integrable {α : ℝ} {h : ℝ → ℝ} {m : ℕ}
    (hint : MeasureTheory.IntegrableOn (PsiGam α h m) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (HonGam α h m) (Set.Ioo 0 xNear) := by
  refine (subGam_integrable hint).congr_fun (fun x hx => ?_) measurableSet_Ioo
  simp only [HonGam, SubGam, PsiGam, sin_two_thetaOf_Ioo hx]

/-! ## Elementary algebra of the weights -/

/-- `(x^m)² x^{c} = x^{2m+c}` for `x > 0`. -/
lemma pow_sq_mul_rpow {x : ℝ} (hx : 0 < x) (m : ℕ) (c : ℝ) :
    (x ^ m) ^ 2 * x ^ c = x ^ (2 * (m : ℝ) + c) := by
  rw [← pow_mul, show m * 2 = 2 * m by ring, ← Real.rpow_natCast x (2 * m),
    show ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) by push_cast; ring, ← Real.rpow_add hx]

/-- The Young inequality `A² ≤ 2(A+R)² + 2R²`. -/
lemma young (A R : ℝ) : A ^ 2 ≤ 2 * (A + R) ^ 2 + 2 * R ^ 2 := by
  nlinarith [sq_nonneg (A + 2 * R)]

lemma Wide_nonneg (α : ℝ) (h : ℝ → ℝ) (l : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ Wide α h l x :=
  mul_nonneg (Real.rpow_nonneg hx _) (sq_nonneg _)

/-! ## The recursion and its elementary properties -/

lemma AccDom_succ (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (l : ℕ) :
    AccDom α h Cm (l + 1) = fun x => AccDom α h Cm l x + Dom α h Cm l x := by
  funext x
  simp only [AccDom, Dom, domSeq]

lemma Dom_succ (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (l : ℕ) :
    Dom α h Cm (l + 1) = fun x => 2 * HonGam α h (l + 1) x
        + 2 * (((l + 1 : ℕ) : ℝ)) * Cm ^ 2 * AccDom α h Cm (l + 1) x := by
  funext x
  simp only [AccDom, Dom, domSeq]

lemma Dom_zero (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) :
    Dom α h Cm 0 = SubEta h := by
  funext x
  simp only [Dom, domSeq]

lemma AccDom_zero (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) :
    AccDom α h Cm 0 = fun _ => 0 := by
  funext x
  simp only [AccDom, domSeq]

lemma Dom_succ_eq (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (k : ℕ) (x : ℝ) :
    Dom α h Cm (k + 1) x = 2 * HonGam α h (k + 1) x
      + 2 * (((k + 1 : ℕ) : ℝ)) * Cm ^ 2 * AccDom α h Cm (k + 1) x := by
  rw [Dom_succ]

lemma accDom_eq_sum (α : ℝ) (h : ℝ → ℝ) (Cm : ℝ) (l : ℕ) (x : ℝ) :
    AccDom α h Cm l x = ∑ m ∈ Finset.range l, Dom α h Cm m x := by
  induction l with
  | zero => rw [AccDom_zero]; simp
  | succ l ih =>
      rw [AccDom_succ]
      show AccDom α h Cm l x + Dom α h Cm l x = _
      rw [ih, Finset.sum_range_succ]


end Work.FTS.H2.DivQ
end
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.aCoeff_diag =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open scoped Real Topology

set_option autoImplicit false

/-- **The diagonal coefficient.**  For every `i`, the top coefficient of the expansion of
`G^i (2κ ∂_x f)` is `a i i = (2κ)^{i+1}`.  This is the fact that makes the inversion of
`Submission/Work/FTS/H2/DivQ/NOTES.md` §4 work: `a i i` does not vanish on the near region
`[0,x₁]` (`κ ≥ 1/√2` there), so the top term of the expansion *dominates* the whole sum by the
pointwise Young inequality.

Proof: both `aCoeff` and `bCoeff` are instances of the general recursion `genCoeff` of
`Submission/Work/FTS/H2/DivQ/aCoeff_bounds.lean` (`aCoeff_eq_genCoeff` with initial datum `2κ`);
above the diagonal `genCoeff` vanishes (`genCoeff_zero`), so the recursion
`genCoeff_succ_succ` collapses at the diagonal to `genCoeff init (i+1) (i+1) = 2κ · genCoeff init i i`. -/
theorem aCoeff_diag (i : ℕ) : aCoeff i i = fun x => (2 * kappa x) ^ (i + 1) := by
  have key : ∀ i : ℕ, genCoeff (fun x : ℝ => 2 * kappa x) i i
      = fun x => (2 * kappa x) ^ (i + 1) := by
    intro i
    induction i with
    | zero =>
        rw [genCoeff_init_zero]
        funext x
        simp
    | succ i ih =>
        rw [genCoeff_succ_succ]
        have hzero : genCoeff (fun x : ℝ => 2 * kappa x) i (i + 1) = 0 :=
          genCoeff_zero _ i (i + 1) (Nat.lt_succ_self i)
        rw [hzero, ih]
        funext x
        have hd0 : deriv (0 : ℝ → ℝ) x = 0 := by
          simpa using (hasDerivAt_const (x := x) (c := (0 : ℝ))).deriv
        simp only [Pi.zero_apply, hd0, mul_zero, zero_mul, add_zero, zero_add, pow_succ]
        ring
  rw [show aCoeff i i = genCoeff (fun x : ℝ => 2 * kappa x) i i from aCoeff_eq_genCoeff i i]
  exact key i

end Work.FTS.H2.DivQ
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.exists_Cm_aCoeffBnd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

/-! ### A single uniform constant for the finitely many coefficients `aCoeff n m`, `1 ≤ n ≤ 4`

`aCoeff_bounds n` (proved in the sibling file) supplies, for each *fixed* `n`, a constant bounding
all `|aCoeff n m|` with `m ≤ n` on `[0,xNear]`, and (for `n ≥ 1`) a constant with
`|aCoeff n 0 x| ≤ C x²`.  The present statement asks for a *single* constant that works for all
`n ∈ {1,2,3,4}` at once, which is a finite maximum — taken here as a sum of nonnegative
witnesses (so that all the comparisons are `linarith`-linear and no `max`-bookkeeping is needed). -/

theorem exists_Cm_aCoeffBnd :
    ∃ Cm : ℝ, 0 ≤ Cm ∧
      (∀ (n m : ℕ), 1 ≤ n → n ≤ 4 → m ≤ n →
        ∀ x ∈ Set.Icc (0 : ℝ) xNear, |aCoeff n m x| ≤ Cm) ∧
      (∀ (n : ℕ), 1 ≤ n → n ≤ 4 →
        ∀ x ∈ Set.Icc (0 : ℝ) xNear, |aCoeff n 0 x| ≤ Cm * x ^ 2) := by
  obtain ⟨c1, hc1nn, hc1⟩ := (aCoeff_bounds 1).2.1
  obtain ⟨c2, hc2nn, hc2⟩ := (aCoeff_bounds 2).2.1
  obtain ⟨c3, hc3nn, hc3⟩ := (aCoeff_bounds 3).2.1
  obtain ⟨c4, hc4nn, hc4⟩ := (aCoeff_bounds 4).2.1
  obtain ⟨d1, hd1nn, hd1⟩ := (aCoeff_bounds 1).2.2 le_rfl
  obtain ⟨d2, hd2nn, hd2⟩ := (aCoeff_bounds 2).2.2 (by norm_num)
  obtain ⟨d3, hd3nn, hd3⟩ := (aCoeff_bounds 3).2.2 (by norm_num)
  obtain ⟨d4, hd4nn, hd4⟩ := (aCoeff_bounds 4).2.2 (by norm_num)
  set Cm : ℝ := c1 + c2 + c3 + c4 + d1 + d2 + d3 + d4 with hCm
  have hCmnn : 0 ≤ Cm := by rw [hCm]; linarith
  have hc1le : c1 ≤ Cm := by rw [hCm]; linarith
  have hc2le : c2 ≤ Cm := by rw [hCm]; linarith
  have hc3le : c3 ≤ Cm := by rw [hCm]; linarith
  have hc4le : c4 ≤ Cm := by rw [hCm]; linarith
  have hd1le : d1 ≤ Cm := by rw [hCm]; linarith
  have hd2le : d2 ≤ Cm := by rw [hCm]; linarith
  have hd3le : d3 ≤ Cm := by rw [hCm]; linarith
  have hd4le : d4 ≤ Cm := by rw [hCm]; linarith
  refine ⟨Cm, hCmnn, ?_, ?_⟩
  · intro n m hn1 hn4 hmn x hx
    interval_cases n
    · exact le_trans (hc1 m hmn x hx) hc1le
    · exact le_trans (hc2 m hmn x hx) hc2le
    · exact le_trans (hc3 m hmn x hx) hc3le
    · exact le_trans (hc4 m hmn x hx) hc4le
  · intro n hn1 hn4 x hx
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    interval_cases n
    · exact le_trans (hd1 x hx) (mul_le_mul_of_nonneg_right hd1le hx2)
    · exact le_trans (hd2 x hx) (mul_le_mul_of_nonneg_right hd2le hx2)
    · exact le_trans (hd3 x hx) (mul_le_mul_of_nonneg_right hd3le hx2)
    · exact le_trans (hd4 x hx) (mul_le_mul_of_nonneg_right hd4le hx2)

end Work.FTS.H2.DivQ
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgNearSetup =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

open Work.FTS.EllExist

set_option autoImplicit false














end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.RadGreenActA =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

theorem RadGreenActA {α : ℝ} (m : ℕ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) (hm : 1 ≤ m) {c : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A) (hc : ContDiffOn ℝ 2 c (Set.Ioi 0)) (hb : ∀ k : ℕ, k ≤ 2 → ∀ t : ℝ, 0 < t → |iteratedDeriv k c t| ≤ A / (1 + t ^ (k + 1))) : ∀ z : ℝ, 0 < z → Work.FTS.PhiStar.Radial.radGreen α m (fun t => α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t) z = α * z ^ 2 * iteratedDeriv 2 (Work.FTS.PhiStar.Radial.radGreen α m c) z + (5 + α) * z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z := by
  intro z hz
  -- ### 1. the hypotheses of the ODE for `radGreen α m c`
  have hcont : ContinuousOn c (Set.Ioi 0) := hc.continuousOn
  obtain ⟨h0, hinf⟩ := RadGreenSupport.src_integrable hα m hA hc hb
  have hode := RadGreenSupport.radGreen_ode_weak hα m hcont h0 hinf z hz
  -- ### 2. the right-hand side is `(λ_m · radGreen α m c z - c z)/α`
  have hI2 : iteratedDeriv 2 (Radial.radGreen α m c) z
      = deriv (deriv (Radial.radGreen α m c)) z := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hI2]
  have hαne : α ≠ 0 := ne_of_gt hα
  have hR : α * z ^ 2 * deriv (deriv (Radial.radGreen α m c)) z
      + (5 + α) * z * deriv (Radial.radGreen α m c) z
      = (Radial.lamR m * Radial.radGreen α m c z - c z) / α := by
    rw [eq_div_iff hαne]
    linear_combination (-1) * hode
  rw [hR]
  -- ### 3. unfold the Green formula and integrate by parts in both integrals
  simp only [Radial.radGreen, neg_div]
  rw [RadGreenSupport.ibp_lower hα m hA hc hb hz,
    RadGreenSupport.ibp_upper hα m hA hc hb hz]
  -- ### 4. abstract the six powers, the two integrals, `K`, `c z` and `(deriv c) z`
  set Ac : ℝ := ∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1) with hAc
  set Bc : ℝ := ∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1) with hBc
  set q : ℝ := (2 * (m : ℝ) + 5) / α with hq
  set p : ℝ := 2 * (m : ℝ) / α with hp
  set Zq : ℝ := z ^ (-q) with hZq
  set Zq1 : ℝ := z ^ (q + 1) with hZq1
  set Zq0 : ℝ := z ^ q with hZq0
  set Zp : ℝ := z ^ p with hZp
  set Zp1 : ℝ := z ^ (1 - p) with hZp1
  set Zp0 : ℝ := z ^ (-p) with hZp0
  set K : ℝ := 1 / (α * (4 * (m : ℝ) + 5)) with hK
  set cc : ℝ := c z with hcc
  set cd : ℝ := deriv c z with hcd
  -- ### 5. the four `rpow` products
  have hZqZq1 : Zq * Zq1 = z := by
    rw [hZq, hZq1, ← Real.rpow_add hz, show -q + (q + 1) = 1 from by ring, Real.rpow_one]
  have hZqZq0 : Zq * Zq0 = 1 := by
    rw [hZq, hZq0, ← Real.rpow_add hz, show -q + q = 0 from by ring, Real.rpow_zero]
  have hZpZp1 : Zp * Zp1 = z := by
    rw [hZp, hZp1, ← Real.rpow_add hz, show p + (1 - p) = 1 from by ring, Real.rpow_one]
  have hZpZp0 : Zp * Zp0 = 1 := by
    rw [hZp, hZp0, ← Real.rpow_add hz, show p + -p = 0 from by ring, Real.rpow_zero]
  -- ### 6. the two IBP results, cleaned up
  have hA1 : Zq * (α * Zq1 * cd - 2 * (m : ℝ) * Zq0 * cc + 2 * (m : ℝ) * q * Ac)
      = α * z * cd - 2 * (m : ℝ) * cc + 2 * (m : ℝ) * q * (Zq * Ac) := by
    rw [show Zq * (α * Zq1 * cd - 2 * (m : ℝ) * Zq0 * cc + 2 * (m : ℝ) * q * Ac)
        = α * cd * (Zq * Zq1) - 2 * (m : ℝ) * cc * (Zq * Zq0)
          + 2 * (m : ℝ) * q * (Zq * Ac) from by ring]
    rw [hZqZq1, hZqZq0]
    ring
  have hB1 : Zp * (-α * Zp1 * cd - (2 * (m : ℝ) + 5) * Zp0 * cc + (2 * (m : ℝ) + 5) * p * Bc)
      = -α * z * cd - (2 * (m : ℝ) + 5) * cc + (2 * (m : ℝ) + 5) * p * (Zp * Bc) := by
    rw [show Zp * (-α * Zp1 * cd - (2 * (m : ℝ) + 5) * Zp0 * cc + (2 * (m : ℝ) + 5) * p * Bc)
        = -α * cd * (Zp * Zp1) - (2 * (m : ℝ) + 5) * cc * (Zp * Zp0)
          + (2 * (m : ℝ) + 5) * p * (Zp * Bc) from by ring]
    rw [hZpZp1, hZpZp0]
    ring
  -- ### 7. the final arithmetic
  rw [eq_div_iff hαne]
  rw [hA1, hB1]
  have h45 : (4 * (m : ℝ) + 5) ≠ 0 := ne_of_gt (by positivity)
  have h5 : α * (4 * (m : ℝ) + 5) ≠ 0 := mul_ne_zero hαne h45
  simp only [hq, hp, hK, Radial.lamR]
  field_simp
  ring

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.radGreenSolvesNoH0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Deleg

set_option autoImplicit false

open Work.FTS.PhiStar.Series (rgiK rgiSn rgiSp rgiF1 rgiF2 rgiA rgiB rgiD1 rgiA_hasDerivAt
  rgiB_hasDerivAt hasDerivAt_radGreenI radGreenI_eq_rgi)

/-!
# `radGreenSolvesNoH0` — the mode-`m` radial Green's function solves the Euler equation

`Work.FTS.PhiStar.Radial.radGreen α m c` is the explicit decaying solution of the mode-`m`
radial Euler equation

  `-α² z² a'' - α(5+α) z a' + λ_m a = c`,      `λ_m = lamR m = 2m(2m+5)`,

written as a Green's function with the two indicial exponents `s⁻ = -(2m+5)/α` (decaying at
`∞`) and `s⁺ = 2m/α`, normalisation `K = 1/(α(4m+5))`.

The sibling `Work.FTS.PhiStar.Radial.radGreen_solves` proves this identity under the *extra*
hypothesis that `t ↦ c t · t^{-1-s⁺}` is integrable on `(0,1)`.  That hypothesis is **not
needed** for the pointwise identity: the tail integral `∫_z^∞` only ever needs local
integrability of `c t t^{-1-s⁺}` near `z`, which continuity of `c` on the compact interval
`[z/2, 1]` supplies (together with the global integrability on `(1,∞)` — precisely what the
public lemmas `Work.FTS.PhiStar.Series.rgiB_hasDerivAt` / `rgiA_hasDerivAt` use).

The computation is the standard one: with `A z = ∫_0^z c t t^{-1-s⁻} dt` and
`B z = ∫_z^∞ c t t^{-1-s⁺} dt`, the `c`-terms of `a'` cancel
(`z^{s⁻} · c z · z^{-1-s⁻} = c z / z = z^{s⁺} · c z · z^{-1-s⁺}`), and the indicial relations
`-α²s(s-1) - α(5+α)s + λ_m = 0` for `s = s⁻, s⁺` together with `α²K(s⁺-s⁻) = 1` leave `c z`.
-/

/-- **The second derivative of `radGreenI`.**  The explicit formula for
`deriv (deriv (radGreenI α m c)) z`: the `y`-differentiated version of
`Work.FTS.PhiStar.Series.rgiD1`. -/
def rgiD2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (y : ℝ) : ℝ :=
  rgiK α m * (((rgiSn α m * ((rgiSn α m - 1) * y ^ (rgiSn α m - 2))) * rgiA α m c y
            + (rgiSn α m * y ^ (rgiSn α m - 1)) * rgiF1 α m c y)
          + ((rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y
            + (rgiSp α m * y ^ (rgiSp α m - 1)) * (-(rgiF2 α m c y))))

/-- `rgiD1` is differentiable on `(0,∞)`, with the explicit second derivative `rgiD2`. -/
theorem hasDerivAt_rgiD1 {α : ℝ} (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (rgiD1 α m c) (rgiD2 α m c z) z := by
  intro z hz
  have hA := rgiA_hasDerivAt (α := α) (m := m) (c := c) hc h0 z hz
  have hB := rgiB_hasDerivAt (α := α) (m := m) (c := c) hc hinf z hz
  have h := hasDerivAt_pairGreen (K := rgiK α m) (sn := rgiSn α m) (sp := rgiSp α m)
    (A := rgiA α m c) (B := rgiB α m c) (F1 := rgiF1 α m c) (F2 := rgiF2 α m c)
    hA hB (ne_of_gt hz)
  exact h.congr_deriv (by simp only [rgiD2])

/-- The six clearing identities at `z > 0`: the four elementary `rpow` identities for the two
indicial exponents and the two `c`-clearing identities `z² z^{s-1} · (c z z^{-1-s}) = c z`. -/
theorem rpow_clear {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {z : ℝ} (hz : 0 < z) :
    z * z ^ (rgiSn α m - 1) = z ^ (rgiSn α m) ∧
    z ^ 2 * z ^ (rgiSn α m - 2) = z ^ (rgiSn α m) ∧
    z * z ^ (rgiSp α m - 1) = z ^ (rgiSp α m) ∧
    z ^ 2 * z ^ (rgiSp α m - 2) = z ^ (rgiSp α m) ∧
    z ^ 2 * z ^ (rgiSn α m - 1) * rgiF1 α m c z = c z ∧
    z ^ 2 * z ^ (rgiSp α m - 1) * rgiF2 α m c z = c z := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := rgiClearing α m c
  exact ⟨h1 z hz, h2 z hz, h3 z hz, h4 z hz, h5 z hz, h6 z hz⟩

theorem radGreenSolvesNoH0 (α : ℝ) (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z, 0 < z →
      -α ^ 2 * z ^ 2 * deriv (deriv (Work.FTS.PhiStar.Radial.radGreen α m c)) z
        - α * (5 + α) * z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
        + Work.FTS.PhiStar.Radial.lamR m * Work.FTS.PhiStar.Radial.radGreen α m c z
        = c z := by
  have hmain : ∀ z, 0 < z →
      -α ^ 2 * z ^ 2 * deriv (deriv (Work.FTS.PhiStar.Radial.radGreenI α m c)) z
        - α * (5 + α) * z * deriv (Work.FTS.PhiStar.Radial.radGreenI α m c) z
        + Work.FTS.PhiStar.Radial.lamR m * Work.FTS.PhiStar.Radial.radGreenI α m c z
        = c z := by
    intro z hz
    have hGreen1 : ∀ y ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (Work.FTS.PhiStar.Radial.radGreenI α m c) (rgiD1 α m c y) y :=
      fun y hy => hasDerivAt_radGreenI (α := α) (m := m) (c := c) hc h0 hinf y hy
    have hD2 : HasDerivAt (rgiD1 α m c) (rgiD2 α m c z) z :=
      hasDerivAt_rgiD1 m hc h0 hinf z hz
    have hderivEq : deriv (Work.FTS.PhiStar.Radial.radGreenI α m c) =ᶠ[𝓝 z] rgiD1 α m c :=
      eventually_of_mem (Ioi_mem_nhds hz) (fun y hy => (hGreen1 y hy).deriv)
    have hdd : deriv (deriv (Work.FTS.PhiStar.Radial.radGreenI α m c)) z = rgiD2 α m c z := by
      rw [hderivEq.deriv_eq, hD2.deriv]
    have hd1z : deriv (Work.FTS.PhiStar.Radial.radGreenI α m c) z = rgiD1 α m c z :=
      (hGreen1 z hz).deriv
    have hgz : Work.FTS.PhiStar.Radial.radGreenI α m c z
        = rgiK α m * (z ^ rgiSn α m * rgiA α m c z + z ^ rgiSp α m * rgiB α m c z) :=
      congrFun (radGreenI_eq_rgi α m c) z
    rw [hdd, hd1z, hgz]
    obtain ⟨hzs1, hzs2, hzp1, hzp2, hc1, hc2⟩ := rpow_clear (α := α) (m := m) (c := c) hz
    -- first derivative: `z * rgiD1 = K (s⁻ z^{s⁻} A + s⁺ z^{s⁺} B)`
    have hzA1 : z * rgiD1 α m c z
        = rgiK α m * (rgiSn α m * (z ^ rgiSn α m * rgiA α m c z)
          + rgiSp α m * (z ^ rgiSp α m * rgiB α m c z)) := by
      simp only [rgiD1]
      linear_combination (rgiK α m * rgiSn α m * rgiA α m c z) * hzs1
        + (rgiK α m * rgiSp α m * rgiB α m c z) * hzp1
    -- second derivative:
    -- `z² * rgiD2 = K (s⁻(s⁻-1) z^{s⁻} A + s⁺(s⁺-1) z^{s⁺} B + (s⁻-s⁺) c)`
    have hzA2 : z ^ 2 * rgiD2 α m c z
        = rgiK α m * (rgiSn α m * (rgiSn α m - 1) * (z ^ rgiSn α m * rgiA α m c z)
          + rgiSp α m * (rgiSp α m - 1) * (z ^ rgiSp α m * rgiB α m c z)
          + (rgiSn α m - rgiSp α m) * c z) := by
      simp only [rgiD2]
      linear_combination (rgiK α m * rgiSn α m * (rgiSn α m - 1) * rgiA α m c z) * hzs2
        + (rgiK α m * rgiSp α m * (rgiSp α m - 1) * rgiB α m c z) * hzp2
        + (rgiK α m * rgiSn α m) * hc1 - (rgiK α m * rgiSp α m) * hc2
    obtain ⟨hind1, hind2, hK⟩ := rgiIndicial α hα m
    have hEC := eulerCombination (α := α) (lam := Work.FTS.PhiStar.Radial.lamR m)
      (K := rgiK α m) (sn := rgiSn α m) (sp := rgiSp α m)
      (P := z ^ rgiSn α m * rgiA α m c z) (Q := z ^ rgiSp α m * rgiB α m c z)
      (cz := c z) (W1 := z * rgiD1 α m c z) (W2 := z ^ 2 * rgiD2 α m c z)
      hzA1 hzA2 hind1 hind2 hK
    linear_combination hEC
  intro z hz
  have hfun : Work.FTS.PhiStar.Radial.radGreen α m c
      = Work.FTS.PhiStar.Radial.radGreenI α m c := rfl
  simpa only [hfun] using hmain z hz

end Work.FTS.PhiStar.Series.Deleg
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.eFam_growth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Filter Set SignType

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

open Work.FTS.PhiStar.Gegenbauer
/-! ## The constraint `sec²θ₀ ≤ M` at a maximum of `|eFam m|` -/

/-- **The second-order constraint.**  If `θ₀` is an interior point where `|eFam m|` is maximal,
`eFam m θ₀ ≠ 0` and `(eFam m)' θ₀ = 0`, then `1 ≤ eM m · cos²θ₀` (i.e. `sec²θ₀ ≤ M`). -/
lemma eM_mul_cos_sq_ge_one (m : ℕ) {θ₀ : ℝ} (hint : θ₀ ∈ Set.Ioo 0 (Real.pi/2))
    (hnz : eFam m θ₀ ≠ 0) (hder : deriv (eFam m) θ₀ = 0)
    (hmax : ∀ θ ∈ Set.Icc (0:ℝ) (Real.pi/2), |eFam m θ| ≤ |eFam m θ₀|) :
    1 ≤ eM m * (Real.cos θ₀)^2 := by
  by_contra hcon
  rw [not_le] at hcon
  have hcos_pos : 0 < Real.cos θ₀ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hint.1, Real.pi_pos], by linarith [hint.2, Real.pi_pos]⟩
  have hcos_ne : Real.cos θ₀ ≠ 0 := ne_of_gt hcos_pos
  have hπ : 0 < Real.pi/2 - θ₀ := by linarith [hint.2]
  have hc : 0 < 1 / Real.cos θ₀ - eM m * Real.cos θ₀ := by
    have h2 : eM m * Real.cos θ₀ < 1 / Real.cos θ₀ := by
      rw [lt_div_iff₀ hcos_pos]; linarith [hcon]
    linarith
  have hdphi : deriv (fun θ' => Real.cos θ' * deriv (eFam m) θ') θ₀
      = (1 / Real.cos θ₀ - eM m * Real.cos θ₀) * eFam m θ₀ := eFam_ode m θ₀ hcos_ne
  have hphi0 : (fun θ' => Real.cos θ' * deriv (eFam m) θ') θ₀ = 0 := by
    simp [hder]
  rcases lt_trichotomy (eFam m θ₀) 0 with hlt | heq | hgt
  · -- `f θ₀ < 0`: `φ` is negative just to the right of `θ₀`, so `f` decreases strictly there
    have hd : deriv (fun θ' => Real.cos θ' * deriv (eFam m) θ') θ₀ < 0 := by
      rw [hdphi]; exact mul_neg_of_pos_of_neg hc hlt
    have hsign := eventually_nhdsWithin_sign_eq_of_deriv_neg hd hphi0
    have hneg : ∀ᶠ x in 𝓝[>] θ₀,
        (fun θ' => Real.cos θ' * deriv (eFam m) θ') x < 0 := by
      filter_upwards [hsign.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hx'
      have h1 : sign (θ₀ - x) = -1 := sign_eq_neg_one_iff.mpr (sub_neg.mpr hx')
      rw [h1] at hx
      exact sign_eq_neg_one_iff.mp hx
    obtain ⟨δ, hδpos, hδsub⟩ :=
      (nhdsGT_basis_of_exists_gt (show ∃ b : ℝ, θ₀ < b from ⟨θ₀ + 1, by linarith⟩)).mem_iff.mp hneg
    set δ₁ : ℝ := min (δ - θ₀) (Real.pi/2 - θ₀) / 2 with hδ₁def
    have hδ₁pos : 0 < δ₁ := by
      rw [hδ₁def]
      have h := lt_min (show (0:ℝ) < δ - θ₀ by linarith) hπ
      linarith
    have hδ₁δ : θ₀ + δ₁ < δ := by
      rw [hδ₁def]; nlinarith [min_le_left (δ - θ₀) (Real.pi/2 - θ₀)]
    have hδ₁π : θ₀ + δ₁ < Real.pi/2 := by
      rw [hδ₁def]; nlinarith [min_le_right (δ - θ₀) (Real.pi/2 - θ₀)]
    have hderneg : ∀ x ∈ Set.Ioo θ₀ (θ₀ + δ₁), deriv (eFam m) x < 0 := by
      intro x hx
      have hxmem : x ∈ Set.Ioo θ₀ δ := ⟨hx.1, by linarith [hx.2, hδ₁δ]⟩
      have hxφ : Real.cos x * deriv (eFam m) x < 0 := hδsub hxmem
      have hcx : 0 < Real.cos x := by
        refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
        · linarith [hx.1, hint.1, Real.pi_pos]
        · linarith [hx.2, hδ₁π]
      nlinarith [hxφ, hcx]
    have hanti : StrictAntiOn (eFam m) (Set.Icc θ₀ (θ₀ + δ₁)) :=
      strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuous_eFam m).continuousOn
        (fun x hx => by rw [interior_Icc] at hx; exact hderneg x hx)
    have hcmp : eFam m (θ₀ + δ₁) < eFam m θ₀ :=
      hanti (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith)) (by linarith)
    have habs : |eFam m θ₀| < |eFam m (θ₀ + δ₁)| := by
      rw [abs_of_neg hlt, abs_of_neg (by linarith [hcmp, hlt])]
      linarith
    have := hmax (θ₀ + δ₁) ⟨by linarith [hint.1, hδ₁pos], by linarith [hδ₁π]⟩
    linarith
  · exact absurd heq hnz
  · -- `f θ₀ > 0`: `φ` is positive just to the right of `θ₀`, so `f` increases strictly there
    have hd : 0 < deriv (fun θ' => Real.cos θ' * deriv (eFam m) θ') θ₀ := by
      rw [hdphi]; exact mul_pos hc hgt
    have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos hd hphi0
    have hpos : ∀ᶠ x in 𝓝[>] θ₀,
        0 < (fun θ' => Real.cos θ' * deriv (eFam m) θ') x := by
      filter_upwards [hsign.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hx'
      have h1 : sign (x - θ₀) = 1 := sign_eq_one_iff.mpr (sub_pos.mpr hx')
      rw [h1] at hx
      exact sign_eq_one_iff.mp hx
    obtain ⟨δ, hδpos, hδsub⟩ :=
      (nhdsGT_basis_of_exists_gt (show ∃ b : ℝ, θ₀ < b from ⟨θ₀ + 1, by linarith⟩)).mem_iff.mp hpos
    set δ₁ : ℝ := min (δ - θ₀) (Real.pi/2 - θ₀) / 2 with hδ₁def
    have hδ₁pos : 0 < δ₁ := by
      rw [hδ₁def]
      have h := lt_min (show (0:ℝ) < δ - θ₀ by linarith) hπ
      linarith
    have hδ₁δ : θ₀ + δ₁ < δ := by
      rw [hδ₁def]; nlinarith [min_le_left (δ - θ₀) (Real.pi/2 - θ₀)]
    have hδ₁π : θ₀ + δ₁ < Real.pi/2 := by
      rw [hδ₁def]; nlinarith [min_le_right (δ - θ₀) (Real.pi/2 - θ₀)]
    have hderpos : ∀ x ∈ Set.Ioo θ₀ (θ₀ + δ₁), 0 < deriv (eFam m) x := by
      intro x hx
      have hxmem : x ∈ Set.Ioo θ₀ δ := ⟨hx.1, by linarith [hx.2, hδ₁δ]⟩
      have hxφ : 0 < Real.cos x * deriv (eFam m) x := hδsub hxmem
      have hcx : 0 < Real.cos x := by
        refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
        · linarith [hx.1, hint.1, Real.pi_pos]
        · linarith [hx.2, hδ₁π]
      nlinarith [hxφ, hcx]
    have hmono : StrictMonoOn (eFam m) (Set.Icc θ₀ (θ₀ + δ₁)) :=
      strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_eFam m).continuousOn
        (fun x hx => by rw [interior_Icc] at hx; exact hderpos x hx)
    have hcmp : eFam m θ₀ < eFam m (θ₀ + δ₁) :=
      hmono (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith)) (by linarith)
    have habs : |eFam m θ₀| < |eFam m (θ₀ + δ₁)| := by
      rw [abs_of_pos hgt, abs_of_pos (by linarith [hcmp, hgt])]
      linarith
    have := hmax (θ₀ + δ₁) ⟨by linarith [hint.1, hδ₁pos], by linarith [hδ₁π]⟩
    linarith

/-! ## The pointwise bound `|eFam m θ| ≤ √2 |(eFam m)'(0)|` -/

/-- **The pointwise bound.**  `|eFam m|` is bounded by `√2 |(eFam m)'(0)|` on `Iθ`; this is the
maximum principle for the Sturm–Liouville equation of `eFam m`. -/
lemma eFam_sq_le (m : ℕ) : ∀ θ ∈ Work.Spaces.Iθ,
    (eFam m θ)^2 ≤ 2 * (deriv (eFam m) 0)^2 := by
  intro θ hθ
  have hmemθ : θ ∈ Set.Icc (0:ℝ) (Real.pi/2) := hθ
  obtain ⟨θ₀, hθ₀mem, hθ₀max⟩ :=
    isCompact_Icc.exists_isMaxOn (s := Set.Icc (0:ℝ) (Real.pi/2))
      ⟨0, ⟨le_rfl, by linarith [Real.pi_pos]⟩⟩ (((continuous_eFam m).abs).continuousOn)
  by_cases hzero : eFam m θ₀ = 0
  · have h1 : |eFam m θ| ≤ 0 := by simpa [hzero] using hθ₀max hmemθ
    have h2 : eFam m θ = 0 := abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    rw [h2]; nlinarith [sq_nonneg (deriv (eFam m) 0)]
  · have hnz : eFam m θ₀ ≠ 0 := hzero
    have hint : θ₀ ∈ Set.Ioo 0 (Real.pi/2) := by
      rcases lt_or_eq_of_le hθ₀mem.1 with h | h
      · rcases lt_or_eq_of_le hθ₀mem.2 with h2 | h2
        · exact ⟨h, h2⟩
        · exact absurd (by rw [h2, eFam_pi_half m]) hzero
      · exact absurd (by rw [h.symm, eFam_zero m]) hzero
    have hder : deriv (eFam m) θ₀ = 0 := by
      have hnb : Set.Icc (0:ℝ) (Real.pi/2) ∈ 𝓝 θ₀ :=
        mem_of_superset (Ioo_mem_nhds hint.1 hint.2) fun x hx => ⟨hx.1.le, hx.2.le⟩
      have hmaxabs : IsLocalMax (fun x => |eFam m x|) θ₀ := hθ₀max.isLocalMax hnb
      rcases lt_trichotomy (eFam m θ₀) 0 with hlt | heq | hgt
      · have heq' : (fun x => |eFam m x|) =ᶠ[𝓝 θ₀] fun x => -eFam m x := by
          filter_upwards [(continuous_eFam m).continuousAt.eventually
            (isOpen_Iio.mem_nhds hlt)] with x hx
          exact abs_of_neg hx
        have hlmax : IsLocalMax (fun x => -eFam m x) θ₀ := heq'.isLocalMax_iff.mp hmaxabs
        have h0 := hlmax.deriv_eq_zero
        have h0' : deriv (fun x => -eFam m x) θ₀ = -deriv (eFam m) θ₀ := by
          simpa using deriv.neg (f := eFam m) (x := θ₀)
        linarith
      · exact absurd heq hzero
      · have heq' : (fun x => |eFam m x|) =ᶠ[𝓝 θ₀] eFam m := by
          filter_upwards [(continuous_eFam m).continuousAt.eventually
            (isOpen_Ioi.mem_nhds hgt)] with x hx
          exact abs_of_pos hx
        have hlmax : IsLocalMax (eFam m) θ₀ := heq'.isLocalMax_iff.mp hmaxabs
        exact hlmax.deriv_eq_zero
    have hcon := eM_mul_cos_sq_ge_one m hint hnz hder (fun θ hθ => hθ₀max hθ)
    have hcrit := eEne_at_critical m hder
    have hle := eEne_le_eEne_zero m hθ₀mem
    have hcoef : (1:ℝ)/2 ≤ eM m * Real.cos θ₀ - 1 / (2 * Real.cos θ₀) := by
      have h1 : 1 ≤ 2 * (eM m * Real.cos θ₀ ^ 2) - 1 := by linarith
      have h2 : Real.cos θ₀ ≤ 1 := Real.cos_le_one θ₀
      have hcp : 0 < Real.cos θ₀ := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hint.1, Real.pi_pos], by linarith [hint.2, Real.pi_pos]⟩
      have h3 : eM m * Real.cos θ₀ - 1 / (2 * Real.cos θ₀)
          = (2 * (eM m * Real.cos θ₀ ^ 2) - 1) / (2 * Real.cos θ₀) := by
        field_simp
      rw [h3, le_div_iff₀ (by positivity)]
      linarith
    have hf2 : (eFam m θ₀)^2 ≤ 2 * eEne m θ₀ := by
      rw [hcrit]
      nlinarith [hcoef, sq_nonneg (eFam m θ₀)]
    calc (eFam m θ)^2 = |eFam m θ|^2 := by rw [sq_abs]
      _ ≤ |eFam m θ₀|^2 := pow_le_pow_left₀ (abs_nonneg _) (hθ₀max hmemθ) 2
      _ = (eFam m θ₀)^2 := by rw [sq_abs]
      _ ≤ 2 * eEne m θ₀ := hf2
      _ ≤ 2 * eEne m 0 := by linarith
      _ = 2 * (deriv (eFam m) 0)^2 := by rw [eEne_at_zero m]

/-! ## The size of `(eFam m)'(0)` -/

/-- The ladder relation at `x = 0`: `(gC (k+1))'(0) = (k+2) gC k 0`. -/
lemma deriv_gC_succ_zero (k : ℕ) : deriv (gC (k + 1)) 0 = ((k : ℝ) + 3) * gC k 0 := by
  have h := Erel_all k 0
  simp only [Erel, Drel, Nat.add_sub_cancel] at h
  push_cast at h
  norm_num at h
  linarith

/-- `(gC (2j) 0)² ≤ 4j+3`, by the three-term recurrence at `x = 0`. -/
lemma gC_even_zero_sq_le (j : ℕ) : (gC (2 * j) 0)^2 ≤ 4 * (j : ℝ) + 3 := by
  induction j with
  | zero => rw [show gC (2 * 0) = gC 0 from rfl,
      show gC 0 = (fun _ : ℝ => 1) from rfl]; norm_num
  | succ j ih =>
    have hrec := gC_rec (2 * j) 0
    have h2j : ((2 * j : ℕ) : ℝ) = 2 * (j : ℝ) := by push_cast; ring
    rw [h2j] at hrec
    have hval : gC (2 * j + 2) 0 = -((2 * (j:ℝ) + 3) / (2 * (j:ℝ) + 2)) * gC (2 * j) 0 := by
      field_simp
      linarith [hrec]
    have hsq : (gC (2 * (j + 1)) 0)^2
        = ((2 * (j:ℝ) + 3) / (2 * (j:ℝ) + 2))^2 * (gC (2 * j) 0)^2 := by
      have h2 : (2 * (j + 1) : ℕ) = 2 * j + 2 := by ring
      rw [h2, hval]; ring
    have hA : ((2 * (j:ℝ) + 3) / (2 * (j:ℝ) + 2))^2 * (4 * (j:ℝ) + 3) ≤ 4 * (j:ℝ) + 7 := by
      rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (2 * (j:ℝ) + 2)]
    rw [hsq]
    have hstep : ((2 * (j:ℝ) + 3) / (2 * (j:ℝ) + 2))^2 * (gC (2 * j) 0)^2
        ≤ 4 * ((j:ℝ) + 1) + 3 :=
      calc ((2 * (j:ℝ) + 3) / (2 * (j:ℝ) + 2))^2 * (gC (2 * j) 0)^2
          ≤ ((2 * (j:ℝ) + 3) / (2 * (j:ℝ) + 2))^2 * (4 * (j:ℝ) + 3) :=
            mul_le_mul_of_nonneg_left ih (sq_nonneg _)
        _ ≤ 4 * (j:ℝ) + 7 := hA
        _ = 4 * ((j:ℝ) + 1) + 3 := by ring
    simpa only [Nat.cast_add, Nat.cast_one] using hstep

/-- The initial-data bound: `|(eFam m)'(0)| ≤ 6 (m+1)^{3/2}`. -/
lemma deriv_eFam_zero_bound (m : ℕ) :
    |deriv (eFam m) 0| ≤ 6 * ((m : ℝ) + 1) ^ ((3 : ℝ) / 2) := by
  have hlad : deriv (eFam m) 0 = (2 * (m:ℝ) + 3) * gC (2 * m) 0 := by
    rw [deriv_eFam_zero m, deriv_gC_succ_zero (2 * m)]
    push_cast; ring
  have hsq := gC_even_zero_sq_le m
  have hg : |gC (2 * m) 0| ≤ Real.sqrt (4 * (m:ℝ) + 3) := by
    have h5 : Real.sqrt ((gC (2 * m) 0)^2) ≤ Real.sqrt ((Real.sqrt (4 * (m:ℝ) + 3))^2) := by
      refine Real.sqrt_le_sqrt ?_
      rw [Real.sq_sqrt (show (0:ℝ) ≤ 4 * (m:ℝ) + 3 by positivity)]
      exact hsq
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (by positivity)] at h5
  have hsqrt : Real.sqrt (4 * (m:ℝ) + 3) ≤ 2 * Real.sqrt ((m:ℝ) + 1) := by
    have h1 : Real.sqrt (4 * (m:ℝ) + 3) ≤ Real.sqrt (4 * ((m:ℝ) + 1)) :=
      Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt (4 * ((m:ℝ) + 1)) = 2 * Real.sqrt ((m:ℝ) + 1) := by
      rw [show (4:ℝ) * ((m:ℝ) + 1) = (2 * Real.sqrt ((m:ℝ) + 1))^2 by
        rw [mul_pow, Real.sq_sqrt (by positivity)]; ring]
      exact Real.sqrt_sq (by positivity)
    rwa [h2] at h1
  have hrpow : ((m : ℝ) + 1) ^ ((3:ℝ)/2) = ((m:ℝ) + 1) * Real.sqrt ((m:ℝ) + 1) := by
    rw [show ((3:ℝ)/2) = 1 + 1/2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  rw [hlad, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (m:ℝ) + 3), hrpow]
  have hs : 0 ≤ Real.sqrt ((m:ℝ) + 1) := Real.sqrt_nonneg _
  calc (2 * (m:ℝ) + 3) * |gC (2 * m) 0|
      ≤ (2 * (m:ℝ) + 3) * (2 * Real.sqrt ((m:ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (hg.trans hsqrt) (by positivity)
    _ ≤ 6 * (((m:ℝ) + 1) * Real.sqrt ((m:ℝ) + 1)) := by nlinarith

/-! ## The main statement -/

theorem eFam_growth :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
        |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)) := by
  refine ⟨9, by norm_num, fun m θ hθ => ?_⟩
  have h1 : (eFam m θ)^2 ≤ 2 * (deriv (eFam m) 0)^2 := eFam_sq_le m θ hθ
  have h2 : (deriv (eFam m) 0)^2 ≤ (6 * ((m:ℝ) + 1)^((3:ℝ)/2))^2 := by
    have hsq : |deriv (eFam m) 0|^2 ≤ (6 * ((m:ℝ) + 1)^((3:ℝ)/2))^2 :=
      pow_le_pow_left₀ (abs_nonneg _) (deriv_eFam_zero_bound m) 2
    rwa [sq_abs] at hsq
  have h3 : |eFam m θ|^2 ≤ (Real.sqrt 2 * 6 * ((m:ℝ) + 1)^((3:ℝ)/2))^2 := by
    have he : (Real.sqrt 2 * 6 * ((m:ℝ) + 1)^((3:ℝ)/2))^2
        = 2 * (6 * ((m:ℝ) + 1)^((3:ℝ)/2))^2 := by
      rw [mul_assoc, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [he, sq_abs]
    linarith
  have h4 : |eFam m θ| ≤ Real.sqrt 2 * 6 * ((m:ℝ) + 1)^((3:ℝ)/2) := by
    have hB : 0 ≤ Real.sqrt 2 * 6 * ((m:ℝ) + 1)^((3:ℝ)/2) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (by norm_num))
        (Real.rpow_nonneg (by positivity) ((3:ℝ)/2))
    have h5 : Real.sqrt ((eFam m θ)^2)
        ≤ Real.sqrt ((Real.sqrt 2 * 6 * ((m:ℝ) + 1)^((3:ℝ)/2))^2) := by
      refine Real.sqrt_le_sqrt ?_
      rw [show (eFam m θ)^2 = |eFam m θ|^2 from (sq_abs _).symm]
      exact h3
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hB] at h5
  have h6 : Real.sqrt 2 * 6 * ((m:ℝ) + 1)^((3:ℝ)/2)
      ≤ 9 * ((m:ℝ) + 1)^((3:ℝ)/2) := by
    have hx : 0 ≤ ((m:ℝ) + 1)^((3:ℝ)/2) := Real.rpow_nonneg (by positivity) _
    have hsq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    have hr : Real.sqrt 2 * 6 ≤ 9 := by
      nlinarith [sq_nonneg ((3/2 : ℝ) - Real.sqrt 2)]
    nlinarith [hr, hx]
  linarith
end Work.FTS.PhiStar.Series
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.hardySinGam_weak =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weak-range angular `sin (2θ)`-weighted Hardy inequality

The target `Work.FTS.StrongEps.EpsSqTools.hardySinGam_weak` is the `sin (2θ)`-weighted Hardy
inequality

  `∫_{Iθ} sin(2θ)^{-c} u² ≤ C/(c-1)² ∫_{Iθ} sin(2θ)^{2-c} (u')²`,

for `1 < c ≤ 3/2`, i.e. for the *weak-weight* range where the exponent `2 - c` on the derivative
side is `≥ 0` (all of `Work.FTS.EllSol.hardySinTwoFin`, `hardySinAll`,
`Work.FTS.ClassC.NormPieces.hardy_sinOpen` need the derivative exponent `≤ 0`).

## Route

* Split `(0, π/2)` at `π/4` (`lintegral_split_Ioo_fts`).
* On the left half `(0, π/4)`, `sin(2θ)` is comparable with `θ` in the favourable direction, so
  `Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.sinHardyGamLeft` (Jordan's inequality
  `θ ≤ (π/4) sin(2θ)` together with the sharp power-weight Hardy
  `TT.SinHardy.NarrowAlt.powerHardy_open` at the exponent `η = c - 2 ∈ (-1, 0]`) gives the bound
  with the sharp constant `4/(c-1)²`, requiring only `u → 0` at `0⁺`.
* The right half is transported to the left one by the reflection `θ ↦ π/2 - θ`, which preserves
  `sin(2θ)` and turns `deriv` into `-deriv`, and which turns the `(π/2)⁻` limit into a `0⁺` limit
  (`T6CoefAux.lintegral_Ioo_reflect`).
* The `∫⁻` (Lebesgue) inequality on `Iθ`, together with the integrability of the *right* hand
  side, yields integrability of `sin(2θ)^{-c} u²` together with the Bochner-integral inequality
  (`Work.FTS.EllipticEst.remov.integrable_of_lintegral_ofReal_le'`).

The constant produced is `C = 4`.
-/

namespace Work.FTS.StrongEps.EpsSqTools

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-! ## Auxiliary lemmas -/

/-- `sin (2θ) > 0` on `(0, π/2)`. -/
private lemma sin2_pos_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- Splitting an `∫⁻`-integral on `(0, π/2)` at the midpoint `π/4` (the two halves are disjoint
and their union differs from `(0, π/2)` by the null set `{π/4}`). -/
private theorem lintegral_split_Ioo_fts (F : ℝ → ENNReal) :
    (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), F θ)
      = (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), F θ)
        + (∫⁻ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), F θ) := by
  have h1 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), F θ)
      = ∫⁻ θ in Set.Ioc (0 : ℝ) (Real.pi / 2), F θ :=
    setLIntegral_congr (MeasureTheory.Ioo_ae_eq_Ioc)
  rw [h1, ← Set.Ioc_union_Ioc_eq_Ioc (a := (0 : ℝ)) (b := Real.pi / 4) (c := Real.pi / 2)
    (by positivity) (by linarith [Real.pi_pos])]
  rw [lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc_of_le le_rfl)]
  rw [setLIntegral_congr (MeasureTheory.Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := Real.pi / 4)).symm,
      setLIntegral_congr (MeasureTheory.Ioo_ae_eq_Ioc (a := Real.pi / 4) (b := Real.pi / 2)).symm]

/-- **The `∫⁻` form of the weighted Hardy inequality on the open interval `(0, π/2)`**, for
`1 < c ≤ 3/2` and `u` of class `C¹` on `(0, π/2)` with `u → 0` at both endpoints: the form in
which no integrability hypothesis is needed. -/
private theorem lin_hardy_Ioo_fts {c : ℝ} {u : ℝ → ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2)
    (hu : ContDiffOn ℝ 1 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hu0 : Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hupi : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      ≤ ENNReal.ofReal (4 / (c - 1) ^ 2) *
        (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := by
  have hc2' : c ≤ 2 := by linarith
  -- the left half for `u`
  have hu4 : ContDiffOn ℝ 1 u (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
    hu.mono (fun x hx => ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩)
  have hleft := Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.sinHardyGamLeft c hc1 hc2' hu4 hu0
  -- the reflected function `g θ = u (π/2 - θ)`
  set g : ℝ → ℝ := fun φ => u (Real.pi / 2 - φ) with hgdef
  have hgcont : ContDiffOn ℝ 1 g (Set.Ioo (0 : ℝ) (Real.pi / 4)) := by
    have hf : ContDiffOn ℝ 1 (fun φ : ℝ => Real.pi / 2 - φ) (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
      (contDiffOn_const (c := Real.pi / 2)).sub contDiffOn_id
    have hcomp := hu.comp hf
      (fun φ hφ => ⟨by linarith [hφ.2, Real.pi_pos], by linarith [hφ.1]⟩)
    rw [hgdef]
    exact hcomp
  have hg0 : Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hmap : Filter.Tendsto (fun φ : ℝ => Real.pi / 2 - φ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h : Filter.Tendsto (fun φ : ℝ => Real.pi / 2 - φ) (nhds (0 : ℝ))
            (nhds (Real.pi / 2 - 0)) := tendsto_const_nhds.sub tendsto_id
        simpa using h.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      · filter_upwards [self_mem_nhdsWithin] with φ hφ
        exact sub_lt_self (Real.pi / 2) hφ
    have h := hupi.comp hmap
    simpa only [hgdef, Function.comp_def] using h
  have hright :=
    Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.sinHardyGamLeft c hc1 hc2' hgcont hg0
  -- the split and the reflection transport
  have hL1 := lintegral_split_Ioo_fts
    (fun θ : ℝ => ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
  have hR1 := lintegral_split_Ioo_fts
    (fun θ : ℝ => ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
  have hL2 : (∫⁻ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      = ∫⁻ φ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ENNReal.ofReal ((Real.sin (2 * φ)) ^ (-c) * (g φ) ^ 2) := by
    rw [Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.lintegral_Ioo_reflect
        (fun θ : ℝ => ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
        (Real.pi / 4) (Real.pi / 2),
      show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 from by ring]
    refine setLIntegral_congr_fun measurableSet_Ioo (fun φ _ => ?_)
    congr 1
    rw [hgdef]
    have hs : Real.sin (2 * (Real.pi / 2 - φ)) = Real.sin (2 * φ) := by
      rw [show 2 * (Real.pi / 2 - φ) = Real.pi - 2 * φ from by ring, Real.sin_pi_sub]
    rw [hs]
  have hR2 : (∫⁻ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
      = ∫⁻ φ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ENNReal.ofReal ((Real.sin (2 * φ)) ^ (2 - c) * (deriv g φ) ^ 2) := by
    rw [Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.lintegral_Ioo_reflect
        (fun θ : ℝ => ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
        (Real.pi / 4) (Real.pi / 2),
      show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 from by ring]
    rw [hgdef]
    refine setLIntegral_congr_fun measurableSet_Ioo (fun φ _ => ?_)
    congr 1
    rw [deriv_comp_const_sub]
    have hs : Real.sin (2 * (Real.pi / 2 - φ)) = Real.sin (2 * φ) := by
      rw [show 2 * (Real.pi / 2 - φ) = Real.pi - 2 * φ from by ring, Real.sin_pi_sub]
    rw [hs, neg_sq]
  have hLR : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      = (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
        + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (g θ) ^ 2)) :=
    hL1.trans (congrArg (fun t => (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
      ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2)) + t) hL2)
  have hRR : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
      = (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
        + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv g θ) ^ 2)) :=
    hR1.trans (congrArg (fun t => (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
      ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) + t) hR2)
  rw [hLR, hRR]
  calc (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
        + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (g θ) ^ 2))
      ≤ ENNReal.ofReal (4 / (c - 1) ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
        + ENNReal.ofReal (4 / (c - 1) ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv g θ) ^ 2)) :=
        add_le_add hleft hright
    _ = ENNReal.ofReal (4 / (c - 1) ^ 2) * ((∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
        + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv g θ) ^ 2))) :=
        (mul_add _ _ _).symm

/-! ## The main theorem -/

/-- **The angular weighted Hardy inequality with the `sin (2θ)`-weight and an exponent
`c ∈ (1,3/2]`, i.e. `c - 2 ∈ (-1,-1/2]` — the weak-weight range** (all of
`Work.FTS.EllSol.hardySinTwoFin`, `hardySinAll`, `Work.FTS.ClassC.NormPieces.hardy_sinOpen`
require the exponent on the *right* to be `≥ 0`):

for `1 < c ≤ 3/2` and `u` of class `C¹` on `(0,π/2)` with `u → 0` at both endpoints
(`0⁺` and `(π/2)⁻`) whose `sin(2θ)^{2-c}`-weighted squared derivative is integrable on
`Iθ = [0,π/2]`, the function `θ ↦ sin(2θ)^{-c} u(θ)²` is integrable on `Iθ` and
`∫_{Iθ} sin(2θ)^{-c} u² ≤ C/(c-1)² ∫_{Iθ} sin(2θ)^{2-c} (u')²`.

`C = 4` is enough.  Route: split `Iθ` at `π/4`; on each half `sin (2θ)` is comparable with the
distance to the corresponding endpoint (`(4/π)θ ≤ sin(2θ) ≤ 2θ` on `[0,π/4]`, and
`sin (2θ) = sin (2(π/2-θ))`), so both comparisons go in the *favourable* direction:
`sin(2θ)^{-c} ≤ θ^{-c}` and `θ^{2-c} ≤ sin(2θ)^{2-c}` (the exponent `2-c > 0` here);
hence the sin-weight inequality on `(0,π/4)` follows from the power-weight Hardy
`Work.FTS.StrongEps.EpsSqTools.powerHardy_negGlobal` with `η = c - 2 ∈ (-1,0)` (being proved in
parallel in a sibling file of the same directory: import it if it is built, otherwise prove the
power statement inside this file — the sharp local form
`Work.FTS.EllipticEst.Cores.powerHardy_at_gen` on `[ε,A]`, valid for every `η > -1`, plus the
truncation/limit argument suffices).  The right half is the reflection `θ ↦ π/2 - θ`, which
preserves both weights and turns the `(π/2)⁻` limit into a `0⁺` limit. -/
theorem hardySinGam_weak : ∃ C : ℝ, 0 < C ∧ ∀ (c : ℝ) (u : ℝ → ℝ),
    1 < c → c ≤ 3 / 2 →
    ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)) →
    Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 0) →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2)
      ≤ C / (c - 1) ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2 := by
  refine ⟨4, by norm_num, ?_⟩
  intro c u hc1 hc2 hu hu0 hupi hG2int
  have hKnn : (0 : ℝ) ≤ 4 / (c - 1) ^ 2 := by positivity
  -- the `∫⁻`-inequality on `(0, π/2)`, transferred to `Iθ = [0, π/2]`
  have hlin2 := lin_hardy_Ioo_fts hc1 hc2 hu hu0 hupi
  have hIθ1 : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      = (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2)) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
    exact (setLIntegral_congr (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ))
      (b := Real.pi / 2))).symm
  have hIθ2 : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
      = (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
    exact (setLIntegral_congr (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ))
      (b := Real.pi / 2))).symm
  have hlinIθ : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      ≤ ENNReal.ofReal (4 / (c - 1) ^ 2) *
        (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := by
    rw [hIθ1, hIθ2]
    exact hlin2
  -- the two weights are nonnegative on `Iθ`
  have hG2ae : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2) := by
    refine (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall (fun θ hθ => ?_))
    exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc (x := 2 * θ)
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _) (sq_nonneg _)
  have hG2lin : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2))
      = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hG2int hG2ae).symm
  have hK : (0 : ℝ) ≤ 4 / (c - 1) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2) :=
    mul_nonneg hKnn (integral_nonneg_of_ae hG2ae)
  have hbound : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      ≤ ENNReal.ofReal (4 / (c - 1) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := by
    rw [hG2lin] at hlinIθ
    refine hlinIθ.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hKnn]
  -- strong measurability and nonnegativity of the left-hand weight
  have hcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-c))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun θ hθ => Or.inl (ne_of_gt (sin2_pos_of_Ioo hθ)))
    exact h1.mul (hu.continuousOn.pow 2)
  have haesm : AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
      ← Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ))
        (b := Real.pi / 2))]
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  have hnn : ∀ x ∈ Work.Spaces.Iθ, 0 ≤ (Real.sin (2 * x)) ^ (-c) * (u x) ^ 2 := by
    intro x hx
    exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc (x := 2 * x)
      ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩) _) (sq_nonneg _)
  exact Work.FTS.EllipticEst.remov.integrable_of_lintegral_ofReal_le'
    measurableSet_Icc hK haesm hnn hbound

end

end Work.FTS.StrongEps.EpsSqTools
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.ThetaBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option maxHeartbeats 1000000

/-- The uniform bound for the `θ`-direction backward difference quotient: for every `e > 0`,
eventually in `j`, the weighted `L¹`-norm of the difference quotient of `V n` at scale
`hq j = 1 / (j+1)` is bounded by `(1 + e/m0)^2` times the weighted `L¹`-norm of `∂_θ V n`. -/
theorem backwardDiffQuot_theta_bound {a b c c' d' d : ℝ} (hcc' : c < c') (hd'd : d' < d)
    (hab : a < b) {ι : Type*} [Fintype ι] {ρ : ι → ℝ → ℝ → ℝ}
    (hρc : ∀ k, ContinuousOn (Function.uncurry (ρ k)) (Set.Icc a b ×ˢ Set.Icc c d))
    (hρp : ∀ k, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < ρ k z θ)
    {V : ℕ → ι → ℝ → ℝ → ℝ}
    (hVsm : ∀ n k, ContDiffOn ℝ 1 (Function.uncurry (V n k)) (Set.Ioo a b ×ˢ Set.Ioo c d))
    (hVc : ∀ n k, ContinuousOn (Function.uncurry (V n k)) (Set.Icc a b ×ˢ Set.Icc c d))
    {hq : ℕ → ℝ} (hq_eq : ∀ j : ℕ, hq j = 1 / ((j : ℝ) + 1))
    {m0 : ℝ} (hm0_pos : 0 < m0)
    (hm0_le : ∀ (k : ι) (z θ : ℝ), z ∈ Set.Icc a b → θ ∈ Set.Icc c d → m0 ≤ ρ k z θ)
    (hunif : ∀ ε > 0, ∃ δ > 0, ∀ k : ι, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
        ∀ y ∈ Set.Icc c d, |θ - y| < δ → |ρ k z θ - ρ k z y| < ε)
    (hq_lt : ∀ᶠ j : ℕ in Filter.atTop, hq j < c' - c)
    (e : ℝ) (he : 0 < e) :
    ∀ᶠ j : ℕ in Filter.atTop, ∀ n : ℕ,
      ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d', ENNReal.ofReal
        (∑ k : ι, ((V n k p.1 p.2 - V n k p.1 (p.2 - hq j)) * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2)
      ≤ ENNReal.ofReal ((1 + e / m0) ^ 2) *
        ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d, ENNReal.ofReal
          (∑ k : ι, (deriv (fun θ' => V n k p.1 θ') p.2 * ρ k p.1 p.2) ^ 2) := by
  have hq_pos : ∀ j : ℕ, 0 < hq j := fun j => by rw [hq_eq j]; positivity
  have hq_tendsto : Filter.Tendsto hq Filter.atTop (nhds 0) := by
    rw [show hq = fun j : ℕ => 1 / ((j : ℝ) + 1) from funext hq_eq]
    exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  obtain ⟨δ, hδpos, hδspec⟩ := hunif e he
  refine ((hq_tendsto.eventually (Iio_mem_nhds hδpos)).and hq_lt).mono fun j hh n => ?_
  obtain ⟨hj, hjlt⟩ := hh
  have hshift : ∀ q ∈ Set.Icc a b ×ˢ Set.Icc c' d',
      (q.1, q.2 - hq j) ∈ Set.Icc a b ×ˢ Set.Icc c d := by
    intro q hqS
    obtain ⟨h1, h2⟩ := hqS
    exact ⟨h1, ⟨by linarith [h2.1, hjlt], by linarith [h2.2, hd'd, hq_pos j]⟩⟩
  have hC : 1 ≤ (1 + e / m0) ^ 2 := by
    have h1 : 0 ≤ e / m0 := le_of_lt (div_pos he hm0_pos)
    nlinarith
  have hratio : ∀ (k : ι) (z y θ : ℝ), z ∈ Set.Icc a b → y ∈ Set.Icc c d →
      θ ∈ Set.Icc c d → |θ - y| ≤ hq j →
      (ρ k z θ) ^ 2 ≤ (1 + e / m0) ^ 2 * (ρ k z y) ^ 2 := by
    intro k z y θ hz hy hθ hyθ
    have h1 : |ρ k z θ - ρ k z y| < e :=
      hδspec k z hz θ hθ y hy (lt_of_le_of_lt hyθ hj)
    have hlt : ρ k z θ < ρ k z y * (1 + e / m0) := by
      have h2 : ρ k z θ < ρ k z y + e := by linarith [(abs_lt.mp h1).2]
      have h3 : e ≤ e * ρ k z y / m0 := by
        have h4 : 1 ≤ ρ k z y / m0 := by
          rw [le_div_iff₀ hm0_pos]; linarith [hm0_le k z y hz hy]
        calc e = e * 1 := by ring
          _ ≤ e * (ρ k z y / m0) := mul_le_mul_of_nonneg_left h4 (le_of_lt he)
          _ = e * ρ k z y / m0 := by ring
      have h5 : ρ k z y * (1 + e / m0) = ρ k z y + e * ρ k z y / m0 := by ring
      rw [h5]; linarith
    have h5 : 0 ≤ ρ k z θ := le_of_lt (hρp k z hz θ hθ)
    have h6 : (ρ k z θ) ^ 2 ≤ (ρ k z y * (1 + e / m0)) ^ 2 := by nlinarith [h5, hlt]
    calc (ρ k z θ) ^ 2 ≤ (ρ k z y * (1 + e / m0)) ^ 2 := h6
      _ = (1 + e / m0) ^ 2 * (ρ k z y) ^ 2 := by ring
  have hper_meas : ∀ k : ι, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
      (((V n k p.1 p.2 - V n k p.1 (p.2 - hq j)) * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) := by
    intro k
    have hcont : ContinuousOn (fun p : ℝ × ℝ => ((V n k p.1 p.2 - V n k p.1 (p.2 - hq j))
        * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2) (Set.Icc a b ×ˢ Set.Icc c' d') := by
      have hcs : ContinuousOn (fun p : ℝ × ℝ => (p.1, p.2 - hq j))
          (Set.Icc a b ×ˢ Set.Icc c' d') :=
        (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousOn
      have h1 : ContinuousOn (fun p : ℝ × ℝ => V n k p.1 p.2)
          (Set.Icc a b ×ˢ Set.Icc c' d') :=
        (hVc n k).mono (fun p hp => ⟨hp.1, ⟨le_trans (le_of_lt hcc') hp.2.1,
          le_trans hp.2.2 (le_of_lt hd'd)⟩⟩)
      have h2 : ContinuousOn (fun p : ℝ × ℝ => V n k p.1 (p.2 - hq j))
          (Set.Icc a b ×ˢ Set.Icc c' d') := (hVc n k).comp hcs hshift
      have h3 : ContinuousOn (fun p : ℝ × ℝ => ρ k p.1 p.2)
          (Set.Icc a b ×ˢ Set.Icc c' d') :=
        (hρc k).mono (fun p hp => ⟨hp.1, ⟨le_trans (le_of_lt hcc') hp.2.1,
          le_trans hp.2.2 (le_of_lt hd'd)⟩⟩)
      exact (((h1.sub h2).mul_const ((j : ℝ) + 1)).mul h3).pow 2
    have h4a : AEMeasurable (fun p : ℝ × ℝ => ‖((V n k p.1 p.2 - V n k p.1 (p.2 - hq j))
        * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2‖ₑ)
        (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c' d')) :=
      AEStronglyMeasurable.enorm (hcont.aestronglyMeasurable (measurableSet_Icc.prod measurableSet_Icc))
    refine AEMeasurable.congr h4a (Eventually.of_forall fun p => ?_)
    exact Real.enorm_eq_ofReal (by positivity)
  have hper : ∀ k : ι, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
        ENNReal.ofReal (((V n k p.1 p.2 - V n k p.1 (p.2 - hq j))
          * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2)
      ≤ ENNReal.ofReal ((1 + e / m0) ^ 2) * ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
          ENNReal.ofReal ((deriv (fun θ' => V n k p.1 θ') p.2) ^ 2 * (ρ k p.1 p.2) ^ 2) := by
    intro k
    by_cases hcd' : c' < d'
    · -- the interior sub-box exhaustion of the difference-quotient region
      rw [lintegral_subbox_eq_iSup hab hcd' (hper_meas k)]
      refine iSup_le fun l => ?_
      set al : ℝ := a + (b - a) / ((l : ℝ) + 2) with haldef
      set bl : ℝ := b - (b - a) / ((l : ℝ) + 2) with hbldef
      set cl : ℝ := c' + (d' - c') / ((l : ℝ) + 2) with hcldef
      set dl : ℝ := d' - (d' - c') / ((l : ℝ) + 2) with hdldef
      have hposb : 0 < (b - a) / ((l : ℝ) + 2) := div_pos (by linarith) (by positivity)
      have hposd : 0 < (d' - c') / ((l : ℝ) + 2) := div_pos (by linarith) (by positivity)
      have hal : a < al := by rw [haldef]; linarith
      have hbl : bl < b := by rw [hbldef]; linarith
      have hcl : c' < cl := by rw [hcldef]; linarith
      have hdl : dl < d' := by rw [hdldef]; linarith
      have hreg : (Set.Icc (a + (b - a) / ((l : ℝ) + 2)) (b - (b - a) / ((l : ℝ) + 2))
            ×ˢ Set.Icc (c' + (d' - c') / ((l : ℝ) + 2)) (d' - (d' - c') / ((l : ℝ) + 2))
            : Set (ℝ × ℝ)) = (Set.Icc al bl ×ˢ Set.Icc cl dl) := by
        rw [haldef, hbldef, hcldef, hdldef]
      rw [hreg]
      have hsm_sub : ∀ z ∈ Set.Icc al bl, ContDiffOn ℝ 1 (fun θ => V n k z θ) (Set.Ioo c d) := by
        intro z hz
        have hzab : z ∈ Set.Ioo a b := ⟨by linarith [hz.1, hal], by linarith [hz.2, hbl]⟩
        have hlin : ContDiffOn ℝ 1 (fun θ : ℝ => (z, θ)) (Set.Ioo c d) := by
          have h1 : ContDiff ℝ 1 (fun θ : ℝ => (z, θ)) := by fun_prop
          exact h1.contDiffOn
        exact (hVsm n k).comp hlin fun θ hθ => ⟨hzab, hθ⟩
      have hc_sub : ∀ z ∈ Set.Icc al bl, ContinuousOn (fun θ => V n k z θ) (Set.Icc c d) := by
        intro z hz
        exact (hVc n k).comp (continuous_const.prodMk continuous_id).continuousOn
          (fun θ hθ => ⟨⟨by linarith [hz.1, hal], by linarith [hz.2, hbl]⟩, hθ⟩)
      have hmeas_sub : AEMeasurable (fun p : ℝ × ℝ =>
          ENNReal.ofReal ((deriv (fun θ' => V n k p.1 θ') p.2) ^ 2 * (ρ k p.1 p.2) ^ 2))
          (MeasureTheory.volume.restrict (Set.Icc al bl ×ˢ Set.Icc c d)) := by
        have hsubst : Set.Icc al bl ×ˢ Set.Icc c d ⊆ Set.Icc a b ×ˢ Set.Icc c d := by
          intro p hp
          exact ⟨⟨by linarith [hp.1.1, hal], by linarith [hp.1.2, hbl]⟩, hp.2⟩
        exact AEMeasurable.mono_set hsubst (aemeasurable_pth_sq_mul (hVsm n k) (hρc k))
      have hDQ := diffQuot_backward_lintegral_le_theta (a := al) (b := bl) (c := c) (d := d)
        (c' := cl) (d' := dl) (h := hq j) (C := (1 + e / m0) ^ 2) (w := ρ k) (u := V n k)
        (by linarith) (by linarith) (hq_pos j) (by linarith [hjlt, hcl]) hC
        (fun z hz θ hθ => hρp k z ⟨by linarith [hz.1, hal], by linarith [hz.2, hbl]⟩ θ hθ)
        (fun z hz y hy θ hθ hzy =>
          hratio k z y θ ⟨by linarith [hz.1, hal], by linarith [hz.2, hbl]⟩ hy hθ hzy)
        hsm_sub hc_sub hmeas_sub
      refine le_trans (le_of_eq ?_) (le_trans hDQ ?_)
      · -- identify the difference-quotient integrands
        refine lintegral_congr fun p => ?_
        congr 1
        rw [← mul_pow]
        congr 1
        have hh : (V n k p.1 p.2 - V n k p.1 (p.2 - hq j)) / hq j
            = (V n k p.1 p.2 - V n k p.1 (p.2 - hq j)) * ((j : ℝ) + 1) := by
          rw [hq_eq j]
          field_simp
        rw [hh]
      · -- enlarge the integration region `Icc al bl ×ˢ Icc c d ⊆ Icc a b ×ˢ Icc c d`
        refine mul_le_mul' le_rfl (setLIntegral_mono_subset
          (measurableSet_Icc.prod measurableSet_Icc) (measurableSet_Icc.prod measurableSet_Icc) ?_)
        intro p hp
        exact ⟨⟨le_trans (le_of_lt hal) hp.1.1, le_trans hp.1.2 (le_of_lt hbl)⟩, hp.2⟩
    · -- degenerate `θ`-box: the region is null
      have h0 : (MeasureTheory.volume (Set.Icc c' d') : ℝ≥0∞) = 0 := by
        rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]
        linarith [not_lt.mp hcd']
      have hSnull : (MeasureTheory.volume : Measure (ℝ × ℝ)) (Set.Icc a b ×ˢ Set.Icc c' d') = 0 := by
        rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, h0, mul_zero]
      rw [MeasureTheory.Measure.restrict_eq_zero.mpr hSnull, MeasureTheory.lintegral_zero_measure]
      exact bot_le
  have hd_meas : ∀ k : ι, AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((deriv (fun θ' => V n k p.1 θ') p.2) ^ 2 * (ρ k p.1 p.2) ^ 2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    fun k => aemeasurable_pth_sq_mul (hVsm n k) (hρc k)
  calc ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d', ENNReal.ofReal
        (∑ k : ι, ((V n k p.1 p.2 - V n k p.1 (p.2 - hq j)) * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2)
      = ∑ k : ι, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d', ENNReal.ofReal
          (((V n k p.1 p.2 - V n k p.1 (p.2 - hq j)) * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2) := by
        rw [show (fun p : ℝ × ℝ => ENNReal.ofReal
            (∑ k : ι, ((V n k p.1 p.2 - V n k p.1 (p.2 - hq j)) * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2))
            = fun p : ℝ × ℝ => ∑ k : ι, ENNReal.ofReal
              (((V n k p.1 p.2 - V n k p.1 (p.2 - hq j)) * ((j : ℝ) + 1) * ρ k p.1 p.2) ^ 2) from by
          funext p
          exact ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
        exact lintegral_finsetSum' Finset.univ fun k _ => hper_meas k
    _ ≤ ∑ k : ι, ENNReal.ofReal ((1 + e / m0) ^ 2) * ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
          ENNReal.ofReal ((deriv (fun θ' => V n k p.1 θ') p.2) ^ 2 * (ρ k p.1 p.2) ^ 2) :=
        Finset.sum_le_sum fun k _ => hper k
    _ = ENNReal.ofReal ((1 + e / m0) ^ 2) * (∑ k : ι, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
          ENNReal.ofReal ((deriv (fun θ' => V n k p.1 θ') p.2) ^ 2 * (ρ k p.1 p.2) ^ 2)) :=
        (Finset.mul_sum _ _ _).symm
    _ = ENNReal.ofReal ((1 + e / m0) ^ 2) * ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
          ENNReal.ofReal (∑ k : ι, (deriv (fun θ' => V n k p.1 θ') p.2 * ρ k p.1 p.2) ^ 2) := by
        congr 1
        rw [show (fun p : ℝ × ℝ => ENNReal.ofReal
            (∑ k : ι, (deriv (fun θ' => V n k p.1 θ') p.2 * ρ k p.1 p.2) ^ 2))
            = fun p : ℝ × ℝ => ∑ k : ι, ENNReal.ofReal
              ((deriv (fun θ' => V n k p.1 θ') p.2) ^ 2 * (ρ k p.1 p.2) ^ 2) from by
          funext p
          rw [show (∑ k : ι, (deriv (fun θ' => V n k p.1 θ') p.2 * ρ k p.1 p.2) ^ 2)
              = ∑ k : ι, (deriv (fun θ' => V n k p.1 θ') p.2) ^ 2 * (ρ k p.1 p.2) ^ 2 from
            Finset.sum_congr rfl fun k _ => mul_pow _ _ 2]
          exact ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        exact (lintegral_finsetSum' Finset.univ fun k _ => hd_meas k).symm

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.lintegral_backwardDiffQuot_majorant_le_liminf_z =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The majorant bound for the backward difference quotient of `W` (z-direction)

The `z`-direction instance of the assembly of
`Submission/Work/FTS/StrongEps/LocUnif/NOTES_assembly_final.md`, item 2: if `W` is the a.e.
pointwise limit of a family `V n` that is `C^1` in `z` on the open rectangle, and `ρ` is a
positive continuous weight on the closed rectangle, then the weighted `L²`-norm of the backward
difference quotients of `W` over the inner rectangle is bounded by the `liminf` of the weighted
`L²`-norms of the `z`-derivatives of `V n` over the outer rectangle — with no loss of constant
(the weight is compared inside the sliding window, where it converges to itself).

The proof applies Fatou's lemma three times: once to exchange the outer `liminf` over `j` with the
integral, once to pass from the difference quotients of `W` to those of `V n` (pointwise a.e.
convergence), and once to bound each difference quotient of `V n` by the mean of `∂_z V n` over
the sliding window (fundamental theorem of calculus plus Cauchy–Schwarz).  The finitely many
indices with `1/(j+1) ≥ a' - a`, for which the window would leave the outer rectangle, are
discarded at the start.
-/

noncomputable section

namespace Work.FTS.StrongEps.LocUnif

open MeasureTheory Set Filter
open scoped ENNReal

set_option maxHeartbeats 1000000

/-! ## Helper lemmas. -/

/-- For a box `[c,d]`, almost every point of it lies in the open interval `(c,d)`. -/
theorem lz_ae_mem_Ioo {c d : ℝ} :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc c d)), θ ∈ Set.Ioo c d := by
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
  refine measure_mono_null (t := ({c} ∪ {d} : Set ℝ)) (fun θ hθ => ?_) ?_
  swap
  · rw [measure_union_null_iff]
    exact ⟨measure_singleton c, measure_singleton d⟩
  have h1 : θ ∈ Set.Icc c d := by
    by_contra h
    exact hθ fun hh => absurd hh h
  have h2 : θ ∉ Set.Ioo c d := fun hh => hθ fun _ => hh
  simp only [Set.mem_Icc] at h1
  simp only [Set.mem_Ioo] at h2
  simp only [Set.mem_union, Set.mem_singleton_iff]
  rcases lt_or_eq_of_le h1.1 with h | h
  · right
    by_contra hne
    exact h2 ⟨h, lt_of_le_of_ne h1.2 hne⟩
  · left; exact h.symm

/-- The `z`-slice of a function that is `C¹` on the open rectangle is `C¹`. -/
theorem lz_slice_sm {a b c d : ℝ} {u : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 (Function.uncurry u) (Set.Ioo a b ×ˢ Set.Ioo c d)) :
    ∀ θ ∈ Set.Ioo c d, ContDiffOn ℝ 1 (fun z => u z θ) (Set.Ioo a b) := by
  intro θ hθ
  have hlin : ContDiffOn ℝ 1 (fun z : ℝ => (z, θ)) (Set.Ioo a b) := by
    have h1 : ContDiff ℝ 1 (fun z : ℝ => (z, θ)) := by fun_prop
    exact h1.contDiffOn
  exact hsm.comp hlin (fun z hz => ⟨hz, hθ⟩)

/-- Restrictions of a.e. measurability to a smaller set. -/
theorem lz_aemeasurable_restrict_of_subset {A B : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hAB : A ⊆ B) (hf : AEMeasurable f (MeasureTheory.volume.restrict B)) :
    AEMeasurable f (MeasureTheory.volume.restrict A) := by
  obtain ⟨g, hgm, hgae⟩ := hf
  exact ⟨g, hgm, (MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hAB le_rfl)) hgae⟩

theorem lintegral_backwardDiffQuot_majorant_le_liminf_z {a a' b' b c d : ℝ}
    (haa' : a < a') (hb'b : b' < b) (hcd : c < d)
    {ι : Type*} [Fintype ι] {ρ : ι → ℝ → ℝ → ℝ}
    (hρc : ∀ k, ContinuousOn (Function.uncurry (ρ k)) (Set.Icc a b ×ˢ Set.Icc c d))
    (hρp : ∀ k, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < ρ k z θ)
    {V : ℕ → ι → ℝ → ℝ → ℝ} {W : ι → ℝ → ℝ → ℝ}
    (hVsm : ∀ n k, ContDiffOn ℝ 1 (Function.uncurry (V n k)) (Set.Ioo a b ×ˢ Set.Ioo c d))
    (hVc : ∀ n k, ContinuousOn (Function.uncurry (V n k)) (Set.Icc a b ×ˢ Set.Icc c d))
    (hWmeas : ∀ k, MeasureTheory.AEStronglyMeasurable (Function.uncurry (W k))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)))
    (hconv : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)), ∀ k,
      Filter.Tendsto (fun n => V n k p.1 p.2) Filter.atTop (nhds (W k p.1 p.2))) :
    ∫⁻ p in (Set.Icc a' b' ×ˢ Set.Icc c d),
        Filter.liminf (fun j : ℕ => ∑ k, ENNReal.ofReal
          (((W k p.1 p.2 - W k (p.1 - 1 / ((j : ℝ) + 1)) p.2) * ((j : ℝ) + 1)
            * ρ k p.1 p.2) ^ 2)) Filter.atTop
      ≤ Filter.liminf (fun n : ℕ => ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c d),
          ENNReal.ofReal (∑ k, (deriv (fun z' => V n k z' p.2) p.1 * ρ k p.1 p.2) ^ 2))
          Filter.atTop := by
  classical
  set S : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc c d with hS
  set S' : Set (ℝ × ℝ) := Set.Icc a' b' ×ˢ Set.Icc c d with hS'
  have hSmeas : MeasurableSet S := by
    rw [hS]; exact measurableSet_Icc.prod measurableSet_Icc
  have hS'meas : MeasurableSet S' := by
    rw [hS']; exact measurableSet_Icc.prod measurableSet_Icc
  have hS'sub : S' ⊆ S := by
    rw [hS, hS']
    intro p hp
    simp only [Set.mem_prod, Set.mem_Icc] at hp ⊢
    exact ⟨⟨by linarith [hp.1.1, haa'], by linarith [hp.1.2, hb'b]⟩, hp.2⟩
  set hh : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with hhh
  have hhpos : ∀ j, 0 < hh j := by intro j; rw [hhh]; positivity
  have hhtend : Tendsto hh Filter.atTop (nhds 0) := by
    rw [hhh]; simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  by_cases hne : Nonempty ι
  · by_cases hbox : a' ≤ b'
    swap
    · rw [hS', show (Set.Icc a' b' : Set ℝ) = ∅ from Set.Icc_eq_empty_iff.mpr hbox,
        Set.empty_prod]
      simp
    obtain ⟨C, hC1, hCratio, hCtend⟩ :=
        exists_scaling_const_seq (by linarith) hcd hne hρc hρp
    obtain ⟨J₀, hJ₀⟩ := Filter.eventually_atTop.mp
      (hhtend.eventually (Iio_mem_nhds (show (0 : ℝ) < a' - a by linarith)))
    set Y : ℕ → ℝ≥0∞ := fun n => ∫⁻ p in S,
      ENNReal.ofReal (∑ k, (deriv (fun z' => V n k z' p.2) p.1 * ρ k p.1 p.2) ^ 2) with hY
    set L : ℝ≥0∞ := Filter.liminf Y Filter.atTop with hL
    set Aw : ℕ → ℝ × ℝ → ℝ≥0∞ := fun j' p => ∑ k, ENNReal.ofReal
      (((W k p.1 p.2 - W k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2) ^ 2) with hAw
    set Av : ℕ → ℕ → ℝ × ℝ → ℝ≥0∞ := fun j' n p => ∑ k, ENNReal.ofReal
      (((V n k p.1 p.2 - V n k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2) ^ 2) with hAv
    -- ### 0. basic facts
    have hshift : ∀ j' ≥ J₀, ∀ p, p ∈ S' → (p.1 - hh j', p.2) ∈ S := by
      intro j' hj' p hp
      simp only [hS, hS'] at hp ⊢
      simp only [Set.mem_prod, Set.mem_Icc] at hp ⊢
      exact ⟨⟨by linarith [hp.1.1, hJ₀ j' hj'], by linarith [hp.1.2, hhpos j']⟩, hp.2⟩
    have hhu : ∀ j' ≥ J₀, hh j' ≤ a' - a := fun j' hj' => le_of_lt (hJ₀ j' hj')
    -- ### 1. slice smoothness in `θ` (a.e.)
    have hslice : ∀ n k, ∀ θ ∈ Set.Ioo c d,
        ContDiffOn ℝ 1 (fun z => V n k z θ) (Set.Ioo a b) :=
      fun n k => lz_slice_sm (hVsm n k)
    have hu_sm : ∀ n k, ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc c d)),
        ContDiffOn ℝ 1 (fun z => V n k z θ) (Set.Ioo a b) :=
      fun n k => (lz_ae_mem_Ioo (c := c) (d := d)).mono fun θ hθ => hslice n k θ hθ
    -- ### 2. measurability of the `y`-integrands
    have hYsum : ∀ n k, AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal ((deriv (fun z' => V n k z' p.2) p.1 * ρ k p.1 p.2) ^ 2))
        (MeasureTheory.volume.restrict S) := by
      intro n k
      refine (aemeasurable_deriv_slice_of_contDiffOn (hVsm n k) (hρc k)).congr ?_
      filter_upwards with p
      congr 1
      ring
    have hY_eq : ∀ n, Y n = ∑ k, ∫⁻ p in S,
        ENNReal.ofReal ((deriv (fun z' => V n k z' p.2) p.1 * ρ k p.1 p.2) ^ 2) := by
      intro n
      have h1 : Y n = ∫⁻ p in S, ∑ k,
          ENNReal.ofReal ((deriv (fun z' => V n k z' p.2) p.1 * ρ k p.1 p.2) ^ 2) := by
        rw [hY]
        exact MeasureTheory.lintegral_congr
          (fun p => ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _))
      rw [h1]
      exact MeasureTheory.lintegral_finsetSum' Finset.univ fun k _ => hYsum n k
    -- ### 3. the left-hand side rewritten
    have hLHS : ∫⁻ p in S',
        Filter.liminf (fun j : ℕ => ∑ k, ENNReal.ofReal
          (((W k p.1 p.2 - W k (p.1 - 1 / ((j : ℝ) + 1)) p.2) * ((j : ℝ) + 1)
            * ρ k p.1 p.2) ^ 2)) Filter.atTop
        = ∫⁻ p in S', Filter.liminf (fun j => Aw j p) Filter.atTop := by
      refine lintegral_congr fun p => ?_
      refine Filter.liminf_congr (Filter.Eventually.of_forall fun j => ?_)
      rw [hAw]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hhh]
      have h1 : 1 / (1 / ((j : ℝ) + 1)) = (j : ℝ) + 1 := by simp only [one_div, inv_inv]
      rw [h1]
    -- ### 4. dropping the finitely many bad indices ``j < J₀``
    have hstep1 : ∫⁻ p in S', Filter.liminf (fun j => Aw j p) Filter.atTop
        ≤ ∫⁻ p in S', Filter.liminf (fun j => Aw (j + J₀) p) Filter.atTop := by
      refine lintegral_mono fun p => ?_
      rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat]
      refine iSup_le fun m => ?_
      refine le_trans ?_ (le_iSup (fun i => ⨅ j, ⨅ (_ : j ≥ i), Aw (j + J₀) p) m)
      refine le_iInf fun j => le_iInf fun hj => ?_
      exact (iInf_le (fun i => ⨅ (_ : i ≥ m), Aw i p) (j + J₀)).trans (iInf_le _ (by omega))
    -- ### 5. measurability of the `W`-integrands
    have hAw_sum : ∀ j' ≥ J₀, ∀ k, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (((W k p.1 p.2 - W k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2) ^ 2))
        (MeasureTheory.volume.restrict S') := by
      intro j' hj' k
      have hW1 : AEMeasurable (fun p : ℝ × ℝ => W k p.1 p.2)
          (MeasureTheory.volume.restrict S') :=
        lz_aemeasurable_restrict_of_subset hS'sub ((hWmeas k).aemeasurable)
      have hW2 : AEMeasurable (fun p : ℝ × ℝ => W k (p.1 - hh j') p.2)
          (MeasureTheory.volume.restrict S') :=
        aemeasurable_comp_sub_of_aemeasurable hSmeas hS'meas (hshift j' hj')
          (hWmeas k).aemeasurable
      have hρ' : AEMeasurable (fun p : ℝ × ℝ => ρ k p.1 p.2)
          (MeasureTheory.volume.restrict S') :=
        ((hρc k).mono hS'sub).aestronglyMeasurable hS'meas |>.aemeasurable
      have hnum : AEMeasurable (fun p : ℝ × ℝ =>
          (W k p.1 p.2 - W k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2)
          (MeasureTheory.volume.restrict S') :=
        ((hW1.sub hW2).mul aemeasurable_const).mul hρ'
      have hsq : AEMeasurable (fun p : ℝ × ℝ =>
          ((W k p.1 p.2 - W k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2) ^ 2)
          (MeasureTheory.volume.restrict S') :=
        hnum.pow (aemeasurable_const : AEMeasurable (fun _ : ℝ × ℝ => (2 : ℕ)) _)
      exact ENNReal.measurable_ofReal.comp_aemeasurable hsq
    have hAw_meas : ∀ j' ≥ J₀, AEMeasurable (Aw j')
        (MeasureTheory.volume.restrict S') := by
      intro j' hj'
      rw [hAw]
      refine (Finset.aemeasurable_sum Finset.univ (fun k _ => hAw_sum j' hj' k)).congr ?_
      filter_upwards with p
      simp only [Finset.sum_apply]
    have hstep2 : ∫⁻ p in S', Filter.liminf (fun j => Aw (j + J₀) p) Filter.atTop
        ≤ Filter.liminf (fun j => ∫⁻ p in S', Aw (j + J₀) p) Filter.atTop :=
      MeasureTheory.lintegral_liminf_le' fun j => hAw_meas (j + J₀) (by omega)
    -- ### 6. measurability of the `V`-integrands
    have hAv_sum : ∀ j' n k, j' ≥ J₀ → AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (((V n k p.1 p.2 - V n k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2) ^ 2))
        (MeasureTheory.volume.restrict S') := by
      intro j' n k hj'
      have hV1 : AEMeasurable (fun p : ℝ × ℝ => V n k p.1 p.2)
          (MeasureTheory.volume.restrict S') :=
        ((hVc n k).mono hS'sub).aestronglyMeasurable hS'meas |>.aemeasurable
      have hV2 : AEMeasurable (fun p : ℝ × ℝ => V n k (p.1 - hh j') p.2)
          (MeasureTheory.volume.restrict S') :=
        ((hVc n k).comp (((continuous_fst.sub continuous_const).prodMk continuous_snd).continuousOn)
          (hshift j' hj')).aestronglyMeasurable hS'meas |>.aemeasurable
      have hρ' : AEMeasurable (fun p : ℝ × ℝ => ρ k p.1 p.2)
          (MeasureTheory.volume.restrict S') :=
        ((hρc k).mono hS'sub).aestronglyMeasurable hS'meas |>.aemeasurable
      have hnum : AEMeasurable (fun p : ℝ × ℝ =>
          (V n k p.1 p.2 - V n k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2)
          (MeasureTheory.volume.restrict S') :=
        ((hV1.sub hV2).mul aemeasurable_const).mul hρ'
      have hsq : AEMeasurable (fun p : ℝ × ℝ =>
          ((V n k p.1 p.2 - V n k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2) ^ 2)
          (MeasureTheory.volume.restrict S') :=
        hnum.pow (aemeasurable_const : AEMeasurable (fun _ : ℝ × ℝ => (2 : ℕ)) _)
      exact ENNReal.measurable_ofReal.comp_aemeasurable hsq
    have hAv_meas : ∀ j' n, j' ≥ J₀ → AEMeasurable (Av j' n)
        (MeasureTheory.volume.restrict S') := by
      intro j' n hj'
      rw [hAv]
      refine (Finset.aemeasurable_sum Finset.univ (fun k _ => hAv_sum j' n k hj')).congr ?_
      filter_upwards with p
      simp only [Finset.sum_apply]
    -- ### 7. a.e. convergence and Fatou in `n`
    have hae_conv : ∀ j' ≥ J₀, ∀ᵐ p ∂(MeasureTheory.volume.restrict S'),
        ∀ k, (Tendsto (fun n => V n k p.1 p.2) Filter.atTop (nhds (W k p.1 p.2)) ∧
              Tendsto (fun n => V n k (p.1 - hh j') p.2) Filter.atTop
                (nhds (W k (p.1 - hh j') p.2))) := by
      intro j' hj'
      filter_upwards [MeasureTheory.ae_restrict_of_ae_restrict_of_subset hS'sub hconv,
        ae_shift_preimage_sub hSmeas hS'meas hconv (hshift j' hj')] with p hp1 hp2
      exact fun k => ⟨hp1 k, hp2 k⟩
    have hAw_eq : ∀ j' ≥ J₀, ∀ᵐ p ∂(MeasureTheory.volume.restrict S'),
        Aw j' p = Filter.liminf (fun n => Av j' n p) Filter.atTop := by
      intro j' hj'
      filter_upwards [hae_conv j' hj'] with p hp
      have hten : Tendsto (fun n => Av j' n p) Filter.atTop (nhds (Aw j' p)) := by
        rw [hAw, hAv]
        refine tendsto_finsetSum Finset.univ fun k _ => ?_
        have h1 : Tendsto (fun n => (V n k p.1 p.2 - V n k (p.1 - hh j') p.2)
            * (1 / hh j') * ρ k p.1 p.2) Filter.atTop
            (nhds ((W k p.1 p.2 - W k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2)) :=
          (((hp k).1.sub (hp k).2).mul_const (1 / hh j')).mul_const (ρ k p.1 p.2)
        exact ENNReal.tendsto_ofReal (h1.pow 2)
      exact hten.liminf_eq.symm
    have hFatou2 : ∀ j' ≥ J₀, ∫⁻ p in S', Aw j' p
        ≤ Filter.liminf (fun n => ∫⁻ p in S', Av j' n p) Filter.atTop := by
      intro j' hj'
      rw [MeasureTheory.lintegral_congr_ae (hAw_eq j' hj')]
      exact MeasureTheory.lintegral_liminf_le' fun n => hAv_meas j' n hj'
    -- ### 8. the per-`(j,n)` bound
    have hterm : ∀ j' ≥ J₀, ∀ n,
        ∫⁻ p in S', Av j' n p ≤ ENNReal.ofReal (C j') * Y n := by
      intro j' hj' n
      have hsplit : ∫⁻ p in S', Av j' n p = ∑ k, ∫⁻ p in S', ENNReal.ofReal
          (((V n k p.1 p.2 - V n k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2) ^ 2) := by
        rw [hAv]
        exact MeasureTheory.lintegral_finsetSum' Finset.univ fun k _ => hAv_sum j' n k hj'
      have hk : ∀ k, ∫⁻ p in S', ENNReal.ofReal
          (((V n k p.1 p.2 - V n k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2) ^ 2)
          ≤ ENNReal.ofReal (C j') * ∫⁻ p in S,
              ENNReal.ofReal ((deriv (fun z' => V n k z' p.2) p.1 * ρ k p.1 p.2) ^ 2) := by
        intro k
        refine (le_of_eq ?_).trans ((lz_diffQuot_backward_lintegral_le_ioo (a := a) (b := b)
          (a' := a') (b' := b') (c := c) (d := d) (h := hh j') (C := C j') (w := ρ k)
          (u := V n k)
          haa' hb'b (hhpos j') (hJ₀ j' hj') (hC1 j')
          (fun z hz θ hθ => hρp k z hz θ hθ)
          (fun z hz y hy θ hθ hzy => hCratio j' k z y θ hz hy hθ hzy)
          (hu_sm n k) (aemeasurable_deriv_slice_of_contDiffOn (hVsm n k) (hρc k))).trans
          (le_of_eq ?_))
        · refine lintegral_congr fun p => ?_
          congr 1
          ring
        · congr 1
          refine lintegral_congr fun p => ?_
          congr 1
          ring
      calc ∫⁻ p in S', Av j' n p
          = ∑ k, ∫⁻ p in S', ENNReal.ofReal
              (((V n k p.1 p.2 - V n k (p.1 - hh j') p.2) * (1 / hh j') * ρ k p.1 p.2) ^ 2) :=
            hsplit
        _ ≤ ∑ k, ENNReal.ofReal (C j') * ∫⁻ p in S,
              ENNReal.ofReal ((deriv (fun z' => V n k z' p.2) p.1 * ρ k p.1 p.2) ^ 2) :=
            Finset.sum_le_sum fun k _ => hk k
        _ = ENNReal.ofReal (C j') * ∑ k, ∫⁻ p in S,
              ENNReal.ofReal ((deriv (fun z' => V n k z' p.2) p.1 * ρ k p.1 p.2) ^ 2) := by
            rw [Finset.mul_sum]
        _ = ENNReal.ofReal (C j') * Y n := by rw [← hY_eq n]
    -- ### 9. assembly
    have hA_le : ∀ j, ∫⁻ p in S', Aw (j + J₀) p ≤ ENNReal.ofReal (C (j + J₀)) * L := by
      intro j
      refine (hFatou2 (j + J₀) (by omega)).trans ?_
      have h1 : Filter.liminf (fun n => ∫⁻ p in S', Av (j + J₀) n p) Filter.atTop
          ≤ Filter.liminf (fun n => ENNReal.ofReal (C (j + J₀)) * Y n) Filter.atTop := by
        rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat]
        refine iSup_le fun m => ?_
        refine le_trans ?_ (le_iSup (fun m => ⨅ i, ⨅ (_ : i ≥ m),
          ENNReal.ofReal (C (j + J₀)) * Y i) m)
        refine le_iInf fun n => le_iInf fun hn => ?_
        exact (iInf_le (fun i => ⨅ (_ : i ≥ m), ∫⁻ p in S', Av (j + J₀) i p) n).trans
          ((iInf_le _ hn).trans (hterm (j + J₀) (by omega) n))
      have h2 : Filter.liminf (fun n => ENNReal.ofReal (C (j + J₀)) * Y n) Filter.atTop
          = ENNReal.ofReal (C (j + J₀)) * L := by
        rw [hL]
        exact ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top
      exact h1.trans (le_of_eq h2)
    have hstep3 : Filter.liminf (fun j => ∫⁻ p in S', Aw (j + J₀) p) Filter.atTop
        ≤ Filter.liminf (fun j => ENNReal.ofReal (C (j + J₀)) * L) Filter.atTop := by
      rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat]
      refine iSup_le fun m => ?_
      refine le_trans ?_ (le_iSup (fun i => ⨅ j, ⨅ (_ : j ≥ i),
        ENNReal.ofReal (C (j + J₀)) * L) m)
      refine le_iInf fun j => le_iInf fun hj => ?_
      exact (iInf_le (fun i => ⨅ (_ : i ≥ m), ∫⁻ p in S', Aw (i + J₀) p) j).trans
        ((iInf_le _ hj).trans (hA_le j))
    have hstep4 : Filter.liminf (fun j => ENNReal.ofReal (C (j + J₀)) * L) Filter.atTop = L := by
      have hctend : Tendsto (fun j => C (j + J₀)) Filter.atTop (nhds 1) :=
        hCtend.comp (tendsto_add_atTop_nat J₀)
      rcases eq_or_ne L ⊤ with hLtop | hLtop
      · rw [hLtop]
        have hconst : (fun j => ENNReal.ofReal (C (j + J₀)) * (⊤ : ℝ≥0∞)) = fun _ => ⊤ := by
          funext j
          exact ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (by linarith [hC1 (j + J₀)]))
        rw [hconst, Filter.liminf_const]
      · have h2 : Tendsto (fun j => C (j + J₀) * L.toReal) Filter.atTop (nhds (1 * L.toReal)) :=
          hctend.mul_const L.toReal
        have h3 : Tendsto (fun j => ENNReal.ofReal (C (j + J₀)) * L) Filter.atTop (nhds L) := by
          have h4 := ENNReal.tendsto_ofReal h2
          rw [one_mul, ENNReal.ofReal_toReal hLtop] at h4
          refine h4.congr' ?_
          filter_upwards with j
          have hCpos : (0 : ℝ) ≤ C (j + J₀) := by linarith [hC1 (j + J₀)]
          rw [ENNReal.ofReal_mul hCpos, ENNReal.ofReal_toReal hLtop]
        rw [h3.liminf_eq]
    -- ### 10. the chain
    have hfinal : ∫⁻ p in S', Filter.liminf (fun j => Aw j p) Filter.atTop
        ≤ Filter.liminf (fun n => Y n) Filter.atTop :=
      calc ∫⁻ p in S', Filter.liminf (fun j => Aw j p) Filter.atTop
          ≤ ∫⁻ p in S', Filter.liminf (fun j => Aw (j + J₀) p) Filter.atTop := hstep1
        _ ≤ Filter.liminf (fun j => ∫⁻ p in S', Aw (j + J₀) p) Filter.atTop := hstep2
        _ ≤ Filter.liminf (fun j => ENNReal.ofReal (C (j + J₀)) * L) Filter.atTop := hstep3
        _ = L := hstep4
        _ = Filter.liminf (fun n => Y n) Filter.atTop := by rw [hL]
    rw [hLHS, hL]
    exact hfinal
  · haveI : IsEmpty ι := not_nonempty_iff.mp hne
    simp

end Work.FTS.StrongEps.LocUnif
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.cosTailB =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set



end Work.FTS_EllLimOK.PkgJets
end
