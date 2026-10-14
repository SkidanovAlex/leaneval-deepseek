import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Order.IsLocallyClosed
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.Psi0Aux.dthU_iter_elementary_bounds_repaired
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.scoef_sum_shift
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.thD_reindex
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.ClassC.mweAux.enIntGeRHS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.mweAux

theorem enIntGeRHS {α lam : ℝ} (hα : 0 < α) {a c : ℝ → ℝ} :
    ∀ z ∈ Set.Ioi (0:ℝ),
      α ^ 2 * ((z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (lam - 3 * α ^ 2 - 3 * α * (5 + α) / 2) * ((a z) ^ 2 * (Work.Spaces.w z) ^ 2)
        - c z * a z * (Work.Spaces.w z) ^ 2
      ≤ Work.FTS.ClassC.enInt α lam a c z := by
  intro z hz
  have hz0 : 0 < z := hz
  have hA : (0:ℝ) ≤ (a z) ^ 2 := sq_nonneg _
  have hW : (0:ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hαpos : (0:ℝ) ≤ α := le_of_lt hα
  have hα5 : (0:ℝ) ≤ α * (5 + α) := mul_nonneg hαpos (by linarith)
  have hα2 : (0:ℝ) ≤ α ^ 2 := sq_nonneg α
  -- the two `w²`-derivative bounds of `ModeEnergyDefs`
  have hbb : rwbb z ≤ 6 * (Work.Spaces.w z) ^ 2 :=
    le_trans (le_abs_self _) (abs_rwbb_le hz0)
  have hcc : -rwc z ≤ 3 * (Work.Spaces.w z) ^ 2 := by
    have h1 := abs_rwc_le hz0
    have h2 := neg_le_abs (rwc z)
    linarith
  -- multiply the two bounds by the nonnegative prefactors
  have hB : (α ^ 2 / 2) * rwbb z * (a z) ^ 2
      ≤ (α ^ 2 / 2) * (6 * (Work.Spaces.w z) ^ 2) * (a z) ^ 2 := by
    have h : rwbb z * (a z) ^ 2 ≤ (6 * (Work.Spaces.w z) ^ 2) * (a z) ^ 2 :=
      mul_le_mul_of_nonneg_right hbb hA
    have hα2' : (0:ℝ) ≤ α ^ 2 / 2 := by positivity
    calc (α ^ 2 / 2) * rwbb z * (a z) ^ 2
        = (α ^ 2 / 2) * (rwbb z * (a z) ^ 2) := by ring
      _ ≤ (α ^ 2 / 2) * ((6 * (Work.Spaces.w z) ^ 2) * (a z) ^ 2) :=
          mul_le_mul_of_nonneg_left h hα2'
      _ = (α ^ 2 / 2) * (6 * (Work.Spaces.w z) ^ 2) * (a z) ^ 2 := by ring
  have hC : -((α * (5 + α)) / 2) * rwc z * (a z) ^ 2
      ≤ ((α * (5 + α)) / 2) * (3 * (Work.Spaces.w z) ^ 2) * (a z) ^ 2 := by
    have h : (-rwc z) * (a z) ^ 2 ≤ (3 * (Work.Spaces.w z) ^ 2) * (a z) ^ 2 :=
      mul_le_mul_of_nonneg_right hcc hA
    have h5' : (0:ℝ) ≤ (α * (5 + α)) / 2 := by linarith
    calc -((α * (5 + α)) / 2) * rwc z * (a z) ^ 2
        = ((α * (5 + α)) / 2) * ((-rwc z) * (a z) ^ 2) := by ring
      _ ≤ ((α * (5 + α)) / 2) * ((3 * (Work.Spaces.w z) ^ 2) * (a z) ^ 2) :=
          mul_le_mul_of_nonneg_left h h5'
      _ = ((α * (5 + α)) / 2) * (3 * (Work.Spaces.w z) ^ 2) * (a z) ^ 2 := by ring
  -- `rw z = (z w z)²` identifies the first term with `α² rw z (∂_z a)²`
  have hkey : α ^ 2 * rw z * (deriv a z) ^ 2
      = α ^ 2 * ((z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    rw [rw_eq_w]; ring
  rw [enInt, ← hkey]
  nlinarith [hB, hC, hA, hW, hα5, hα2]

end Work.FTS.ClassC.mweAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.coerc.slice_limit_at_right_eq_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.coerc

open MeasureTheory Set Filter
open scoped Real Topology Interval

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The substitution `h = u' - tan θ · u`

Everything below is proved from scratch; the only inputs are `ContDiffOn` of `u` and the three
`L²` statements among the target theorem's hypotheses. -/

/-- The substitution `h θ = deriv u θ - tan θ · u θ` of the endpoint analysis: `h` is the
first-order quantity made `L²` by `Lzero1`. -/
def hslice (u : ℝ → ℝ) : ℝ → ℝ := fun θ => deriv u θ - Real.tan θ * u θ

/-- `hsliceDeriv u = -(Lzero1 u) - 6 u` is the derivative of `hslice u`:
`h' = u'' - (tan θ · u)'` and `Lzero1 u = -u'' + (tan θ · u)' - 6u`. -/
def hsliceDeriv (u : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => -(Work.FTS.EllipticEst.Lzero1 u θ) - 6 * u θ

/-- `hslice u` is `C¹` on the strip and its derivative is `hsliceDeriv u`. -/
theorem hslice_deriv_eq {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ 1 (hslice u) (Set.Ioo 0 (Real.pi / 2)) ∧
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), deriv (hslice u) θ = hsliceDeriv u θ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcos : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos x ≠ 0 := fun x hx =>
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, hpi], hx.2⟩)
  have hdu : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have htan : ContDiffOn ℝ 1 Real.tan (Set.Ioo 0 (Real.pi / 2)) := by
    intro x hx
    rw [contDiffWithinAt_iff_contDiffAt (isOpen_Ioo.mem_nhds hx)]
    exact Real.contDiffAt_tan.2 (hcos x hx)
  constructor
  · show ContDiffOn ℝ 1 (fun t => deriv u t - Real.tan t * u t) (Set.Ioo 0 (Real.pi / 2))
    exact hdu.sub (htan.mul (hu.of_le (by norm_num)))
  · intro θ hθ
    have hnhds : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
    have hdu' : DifferentiableAt ℝ (deriv u) θ :=
      (hdu.differentiableOn (by norm_num)).differentiableAt hnhds
    have hu' : DifferentiableAt ℝ u θ :=
      (hu.differentiableOn (by norm_num)).differentiableAt hnhds
    have htan' : DifferentiableAt ℝ Real.tan θ :=
      (Real.hasDerivAt_tan (hcos θ hθ)).differentiableAt
    have h1 : deriv (fun t => deriv u t - Real.tan t * u t) θ
        = deriv (fun t => deriv u t) θ - deriv (fun t => Real.tan t * u t) θ :=
      deriv_sub hdu' (htan'.mul hu')
    have h2 : hsliceDeriv u θ
        = deriv (fun t => deriv u t) θ - deriv (fun t => Real.tan t * u t) θ := by
      simp only [hsliceDeriv, Work.FTS.EllipticEst.Lzero1]
      ring
    exact h1.trans h2.symm

/-- Near `π/2` the tangent dominates `1 / (2 (π/2 - θ))`: `cos θ = sin (π/2 - θ) ≤ π/2 - θ`
and `sin θ ≥ 1/2` for `θ ≥ π/4`. -/
theorem inv_two_mul_pi_div_two_sub_le_tan {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    1 / (2 * (Real.pi / 2 - θ)) ≤ Real.tan θ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have hθle : θ ≤ Real.pi / 2 := le_of_lt hθ.2
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hpi], hθ.2⟩
  have hsin : (1 : ℝ) / 2 ≤ Real.sin θ := by
    have h1 : 2 / Real.pi * θ ≤ Real.sin θ := Real.mul_le_sin hθ0.le hθle
    have h2 : (1 : ℝ) / 2 ≤ 2 / Real.pi * θ := by
      have h3 : 2 / Real.pi * (Real.pi / 4) ≤ 2 / Real.pi * θ :=
        mul_le_mul_of_nonneg_left hθ.1.le (by positivity)
      have h4 : 2 / Real.pi * (Real.pi / 4) = 1 / 2 := by field_simp; ring
      linarith
    linarith
  have hcos_le : Real.cos θ ≤ Real.pi / 2 - θ := by
    have h : Real.sin (Real.pi / 2 - θ) < Real.pi / 2 - θ :=
      Real.sin_lt (by linarith [hθ.2])
    rw [Real.sin_pi_div_two_sub] at h
    exact le_of_lt h
  have h1 : 1 / (2 * (Real.pi / 2 - θ)) ≤ 1 / (2 * Real.cos θ) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    linarith
  have h2 : 1 / (2 * Real.cos θ) ≤ Real.tan θ := by
    rw [Real.tan_eq_sin_div_cos, div_le_div_iff₀ (by positivity) hcos]
    nlinarith [hsin, hcos]
  linarith

/-- The antiderivative of `θ ↦ (π/2 - θ)⁻²` is `θ ↦ (π/2 - θ)⁻¹`. -/
theorem integral_pi_div_two_sub_inv_sq (a b : ℝ) (hab : a ≤ b) (hb : b < Real.pi / 2) :
    ∫ θ in a..b, ((Real.pi / 2 - θ)⁻¹) ^ 2 = (Real.pi / 2 - b)⁻¹ - (Real.pi / 2 - a)⁻¹ := by
  have hcongr : Set.EqOn (fun θ : ℝ => ((Real.pi / 2 - θ)⁻¹) ^ 2)
      (fun θ : ℝ => (Real.pi / 2 - θ) ^ (-2 : ℝ)) (Set.uIcc a b) := by
    intro θ hθ
    rw [Set.uIcc_of_le hab] at hθ
    have hθb : θ < Real.pi / 2 := lt_of_le_of_lt hθ.2 hb
    have hle : 0 ≤ Real.pi / 2 - θ := by linarith
    change ((Real.pi / 2 - θ)⁻¹) ^ 2 = (Real.pi / 2 - θ) ^ (-2 : ℝ)
    have h2 : (Real.pi / 2 - θ) ^ (-2 : ℝ) = ((Real.pi / 2 - θ) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hle (2 : ℝ), Real.rpow_two]
    rw [h2, inv_pow]
  rw [intervalIntegral.integral_congr hcongr,
    Work.FTS.EllipticEst.remov.integral_sub_rpow_neg (b := Real.pi / 2) (p := 2) (t := b) (θ := a)
      hab hb (by norm_num : (1 : ℝ) < 2)]
  rw [show (1 : ℝ) - 2 = -1 by norm_num, show (2 : ℝ) - 1 = 1 by norm_num, div_one]
  simp only [Real.rpow_neg_one]

/-- A non-zero limit at `π/2` from the left keeps `|u|` away from `0` on a left neighbourhood. -/
theorem abs_lower_of_tendsto_nhdsWithin {u : ℝ → ℝ} {ν : ℝ} (hν : ν ≠ 0)
    (hlim : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds ν)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ θ ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), |ν| / 2 ≤ |u θ| := by
  have hνpos : 0 < |ν| := abs_pos.mpr hν
  have hε : 0 < |ν| / 2 := by linarith
  have h1 : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      |u θ - ν| < |ν| / 2 := by
    have h2 := Metric.tendsto_nhds.mp hlim (|ν| / 2) hε
    filter_upwards [h2] with θ hθ
    rwa [Real.dist_eq] at hθ
  rw [eventually_nhdsWithin_iff] at h1
  rw [Metric.eventually_nhds_iff] at h1
  obtain ⟨δ, hδpos, hδ⟩ := h1
  refine ⟨δ, hδpos, fun θ hθ => ?_⟩
  have hdist : dist θ (Real.pi / 2) < δ := by
    rw [Real.dist_eq, abs_of_neg (by linarith [hθ.2])]
    linarith [hθ.1]
  have hlt : |u θ - ν| < |ν| / 2 := hδ hdist hθ.2
  have h2 : |ν| ≤ |u θ| + |ν - u θ| := by
    calc |ν| = |u θ + (ν - u θ)| := by ring_nf
      _ ≤ |u θ| + |ν - u θ| := abs_add_le _ _
  rw [abs_sub_comm] at h2
  linarith

/-- `hslice u` is bounded on a left neighbourhood of `π/2`.  The derivative
`hsliceDeriv u = -(Lzero1 u) - 6u` is square-integrable on `Iθ` by hypothesis, so it is
integrable, and the fundamental theorem of calculus together with `|z| ≤ (1 + z²)/2` bounds the
increment of `hslice u` uniformly. -/
theorem hslice_bdd_near_pi_div_two {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hu0 : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ)
    (hg : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2) Work.Spaces.Iθ) :
    ∃ M δ : ℝ, 0 < M ∧ 0 < δ ∧ δ < Real.pi / 2 ∧
      ∀ θ ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), |hslice u θ| ≤ M := by
  have hpi : 0 < Real.pi := Real.pi_pos
  obtain ⟨hHC1, hHeq⟩ := hslice_deriv_eq hu
  -- the dominating function
  set G : ℝ → ℝ := fun t => 7 / 2 + (1 / 2) * (Work.FTS.EllipticEst.Lzero1 u t) ^ 2
    + 3 * (u t) ^ 2 with hGdef
  have hGnn : ∀ t : ℝ, 0 ≤ G t := by
    intro t
    rw [hGdef]
    have h1 : 0 ≤ (Work.FTS.EllipticEst.Lzero1 u t) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ (u t) ^ 2 := sq_nonneg _
    linarith
  have hIθfin : (volume : MeasureTheory.Measure ℝ) Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hGint : MeasureTheory.IntegrableOn G Work.Spaces.Iθ := by
    rw [hGdef]
    exact ((MeasureTheory.integrableOn_const hIθfin).add (hg.const_mul (1 / 2))).add
      (hu0.const_mul 3)
  have hdom : ∀ t : ℝ, |hsliceDeriv u t| ≤ G t := by
    intro t
    have h1 : |Work.FTS.EllipticEst.Lzero1 u t|
        ≤ (1 + (Work.FTS.EllipticEst.Lzero1 u t) ^ 2) / 2 := by
      nlinarith [abs_nonneg (Work.FTS.EllipticEst.Lzero1 u t),
        sq_abs (Work.FTS.EllipticEst.Lzero1 u t),
        sq_nonneg (|Work.FTS.EllipticEst.Lzero1 u t| - 1)]
    have h2 : |u t| ≤ (1 + (u t) ^ 2) / 2 := by
      nlinarith [abs_nonneg (u t), sq_abs (u t), sq_nonneg (|u t| - 1)]
    have h3 : |-(Work.FTS.EllipticEst.Lzero1 u t) - 6 * u t|
        ≤ |Work.FTS.EllipticEst.Lzero1 u t| + 6 * |u t| := by
      have h6 : |(6 : ℝ) * u t| = 6 * |u t| := by rw [abs_mul]; norm_num
      have h := abs_add_le (-(Work.FTS.EllipticEst.Lzero1 u t)) (-(6 * u t))
      rw [abs_neg, abs_neg, h6] at h
      exact h
    rw [hGdef]
    simp only [hsliceDeriv]
    linarith
  set K : ℝ := ∫ t in Work.Spaces.Iθ, G t with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    exact MeasureTheory.integral_nonneg hGnn
  set θ₀ : ℝ := 3 * Real.pi / 8 with hθ₀def
  have hθ₀mem : θ₀ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [hθ₀def]
    exact ⟨by linarith [hpi], by linarith [hpi]⟩
  have hderivH : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (hslice u) (hsliceDeriv u x) x := by
    intro x hx
    have hd : DifferentiableAt ℝ (hslice u) x :=
      (hHC1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hx)
    have h1 : HasDerivAt (hslice u) (deriv (hslice u) x) x := hd.hasDerivAt
    rw [hHeq x hx] at h1
    exact h1
  refine ⟨|hslice u θ₀| + K + 1, Real.pi / 8, ?_, ?_, ?_, ?_⟩
  · have := abs_nonneg (hslice u θ₀); linarith
  · positivity
  · linarith [hpi]
  · intro θ hθ
    have hπ8 : Real.pi / 2 - Real.pi / 8 = 3 * Real.pi / 8 := by ring
    have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hθ.1, hπ8, hpi], hθ.2⟩
    have hle : θ₀ ≤ θ := by
      rw [hθ₀def]
      linarith [hθ.1, hπ8]
    have hsub : Set.Ioc θ₀ θ ⊆ Work.Spaces.Iθ := fun x hx =>
      ⟨le_trans hθ₀mem.1.le hx.1.le, le_trans hx.2 hθmem.2.le⟩
    have hsub' : Set.Ioc θ₀ θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
      ⟨lt_trans hθ₀mem.1 hx.1, lt_of_le_of_lt hx.2 hθmem.2⟩
    have hsub'' : Set.Ioo θ₀ θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
      ⟨lt_of_lt_of_le hθ₀mem.1 hx.1.le, lt_of_le_of_lt hx.2.le hθmem.2⟩
    have hGsub : MeasureTheory.IntegrableOn G (Set.Ioc θ₀ θ) := hGint.mono_set hsub
    have haesm : MeasureTheory.AEStronglyMeasurable (hsliceDeriv u)
        (volume.restrict (Set.Ioc θ₀ θ)) := by
      refine (aestronglyMeasurable_deriv (hslice u) volume).restrict.congr ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => ?_)
      exact (hderivH x (hsub' hx)).deriv
    have hInt' : MeasureTheory.IntegrableOn (hsliceDeriv u) (Set.Ioc θ₀ θ) :=
      MeasureTheory.Integrable.mono' hGsub haesm
        (Filter.Eventually.of_forall (fun x => by
          rw [Real.norm_eq_abs]
          exact hdom x))
    have hInt : IntervalIntegrable (hsliceDeriv u) volume θ₀ θ :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr hInt'
    have hcont : ContinuousOn (hslice u) (Set.Icc θ₀ θ) :=
      hHC1.continuousOn.mono (fun x hx =>
        ⟨lt_of_lt_of_le hθ₀mem.1 hx.1, lt_of_le_of_lt hx.2 hθmem.2⟩)
    have hftc : ∫ x in θ₀..θ, hsliceDeriv u x = hslice u θ - hslice u θ₀ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont
        (fun x hx => hderivH x (hsub'' hx)) hInt
    have e1 : hslice u θ = hslice u θ₀ + ∫ x in θ₀..θ, hsliceDeriv u x := by
      rw [hftc]; ring
    have e2 : |∫ x in θ₀..θ, hsliceDeriv u x| ≤ ∫ x in θ₀..θ, |hsliceDeriv u x| :=
      intervalIntegral.abs_integral_le_integral_abs hle
    have e3 : (∫ x in θ₀..θ, |hsliceDeriv u x|)
        = ∫ x in Set.Ioc θ₀ θ, |hsliceDeriv u x| := intervalIntegral.integral_of_le hle
    have e4 : (∫ x in Set.Ioc θ₀ θ, |hsliceDeriv u x|) ≤ ∫ x in Set.Ioc θ₀ θ, G x :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun x => abs_nonneg (hsliceDeriv u x)))
        hGsub (Filter.Eventually.of_forall hdom)
    have e5 : (∫ x in Set.Ioc θ₀ θ, G x) ≤ K := by
      rw [hKdef]
      exact MeasureTheory.setIntegral_mono_set hGint
        (Filter.Eventually.of_forall hGnn)
        (Filter.Eventually.of_forall (fun x hx => hsub hx))
    calc |hslice u θ| = |hslice u θ₀ + ∫ x in θ₀..θ, hsliceDeriv u x| := by rw [e1]
      _ ≤ |hslice u θ₀| + |∫ x in θ₀..θ, hsliceDeriv u x| := abs_add_le _ _
      _ ≤ |hslice u θ₀| + ∫ x in θ₀..θ, |hsliceDeriv u x| := by linarith [e2]
      _ = |hslice u θ₀| + ∫ x in Set.Ioc θ₀ θ, |hsliceDeriv u x| := by rw [e3]
      _ ≤ |hslice u θ₀| + ∫ x in Set.Ioc θ₀ θ, G x := by linarith [e4]
      _ ≤ |hslice u θ₀| + K + 1 := by linarith [e5]

/-! ## The endpoint limit -/

/-! Note the hypothesis `hg`: `u ≡ 1` is NOT admissible, since `Lzero1 1 = 1/cos²θ - 6` is not
square-integrable near `π/2`.  Route: `h := u' - tan θ · u` satisfies `h' = -(Lzero1 u) - 6u`, so
`h' ∈ L²` and `h` is bounded near `π/2`; hence `∫ (tan θ)²u² ≤ 2∫(u')² + 2∫h² < ∞` on
`(π/2 - δ, π/2)`.  If `ν ≠ 0` then `|u| ≥ |ν|/2` near `π/2` and `(tan θ)² ≥ c/(π/2 - θ)²` there,
contradicting `¬IntegrableOn (fun z => c / z ^ 2) (Ioi 0)`
(`Work.FTS.EllipticEst.AxisIntegral.not_integrableOn_of_le_div_pow`, after `z = π/2 - θ`). -/
theorem slice_limit_at_right_eq_zero {u : ℝ → ℝ} {ν : ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hu0 : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ)
    (hu1 : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ)
    (hg : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2) Work.Spaces.Iθ)
    (hlim : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds ν)) :
    ν = 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  by_contra hν
  have hνne : ν ≠ 0 := hν
  have hν2 : 0 < ν ^ 2 := sq_pos_of_ne_zero hνne
  obtain ⟨M, δ₁, hMpos, hδ₁pos, _hδ₁lt, hbdd⟩ := hslice_bdd_near_pi_div_two hu hu0 hg
  obtain ⟨δ₂, hδ₂pos, hlow⟩ := abs_lower_of_tendsto_nhdsWithin hνne hlim
  set δ : ℝ := min δ₁ (min δ₂ (Real.pi / 8)) with hδdef
  have hδpos : 0 < δ := lt_min hδ₁pos (lt_min hδ₂pos (by linarith [hpi]))
  have hδ₁ : δ ≤ δ₁ := min_le_left _ _
  have hδ₂ : δ ≤ δ₂ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδπ : δ ≤ Real.pi / 8 := le_trans (min_le_right _ _) (min_le_right _ _)
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact MeasureTheory.integral_nonneg (fun θ => sq_nonneg (deriv u θ))
  set K : ℝ := 2 * B + 2 * M ^ 2 * δ with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    have h1 : 0 ≤ 2 * B := by linarith
    have h2 : 0 ≤ 2 * M ^ 2 * δ := by positivity
    linarith
  set C : ℝ := 16 * K / ν ^ 2 + 2 / δ with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    have h1 : 0 ≤ 16 * K / ν ^ 2 := div_nonneg (by linarith) hν2.le
    have h2 : 0 < 2 / δ := div_pos (by norm_num) hδpos
    linarith
  set ε : ℝ := 1 / C with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; exact div_pos one_pos hCpos
  have h2δ : 0 < 2 / δ := div_pos (by norm_num) hδpos
  have h2δC : 2 / δ ≤ C := by
    rw [hCdef]
    have h1 : 0 ≤ 16 * K / ν ^ 2 := div_nonneg (by linarith) hν2.le
    linarith
  have hεle : ε ≤ δ / 2 := by
    rw [hεdef]
    have h1 : (2 / δ)⁻¹ = δ / 2 := by rw [inv_div]
    simpa only [one_div, h1] using one_div_le_one_div_of_le h2δ h2δC
  have hεltδ : ε < δ := by linarith [hεle, hδpos]
  set a : ℝ := Real.pi / 2 - δ with hadef
  set b : ℝ := Real.pi / 2 - ε with hbdef
  have hle_ab : a ≤ b := by rw [hadef, hbdef]; linarith
  have ha0 : 0 ≤ a := by rw [hadef]; linarith [hδπ, hpi]
  have hbpi : b < Real.pi / 2 := by rw [hbdef]; linarith [hεpos]
  have hbaeq : b - a = δ - ε := by rw [hadef, hbdef]; ring
  have hsubIθ : Set.Ioc a b ⊆ Work.Spaces.Iθ := fun x hx =>
    ⟨le_trans ha0 hx.1.le, le_trans hx.2 hbpi.le⟩
  -- the pointwise comparison on `(a,b)`
  have hpt : ∀ x ∈ Set.Ioo a b,
      (ν ^ 2 / 16) * ((Real.pi / 2 - x)⁻¹) ^ 2
        ≤ 2 * (deriv u x) ^ 2 + 2 * M ^ 2 := by
    intro x hx
    have hxδ : Real.pi / 2 - δ < x := by simpa [hadef] using hx.1
    have hxε : x < Real.pi / 2 - ε := by simpa [hbdef] using hx.2
    have hxπ : x < Real.pi / 2 := by linarith [hxε, hεpos]
    have hx4 : Real.pi / 4 < x := by linarith [hxδ, hδπ, hpi]
    have hxne : Real.pi / 2 - x ≠ 0 := by linarith
    have htan_low : 1 / (2 * (Real.pi / 2 - x)) ≤ Real.tan x :=
      inv_two_mul_pi_div_two_sub_le_tan ⟨hx4, hxπ⟩
    have htan_sq : (1 / (2 * (Real.pi / 2 - x))) ^ 2 ≤ (Real.tan x) ^ 2 :=
      pow_le_pow_left₀ (by positivity) htan_low 2
    have hbddmem : x ∈ Set.Ioo (Real.pi / 2 - δ₁) (Real.pi / 2) :=
      ⟨by linarith [hxδ, hδ₁], hxπ⟩
    have hhlow : |deriv u x - Real.tan x * u x| ≤ M := by
      have h := hbdd x hbddmem
      simpa only [hslice] using h
    have hl2mem : x ∈ Set.Ioo (Real.pi / 2 - δ₂) (Real.pi / 2) :=
      ⟨by linarith [hxδ, hδ₂], hxπ⟩
    have hulow : |ν| / 2 ≤ |u x| := hlow x hl2mem
    have hu2 : (|ν| / 2) ^ 2 ≤ (u x) ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ |ν| / 2) hulow 2
      rwa [sq_abs] at h
    have step1 : (ν ^ 2 / 16) * ((Real.pi / 2 - x)⁻¹) ^ 2
        ≤ (u x) ^ 2 * (Real.tan x) ^ 2 := by
      have hsq : (|ν| / 2) ^ 2 = ν ^ 2 / 4 := by rw [div_pow, sq_abs]; norm_num
      have h2sq : (1 / (2 * (Real.pi / 2 - x))) ^ 2 = 1 / (4 * (Real.pi / 2 - x) ^ 2) := by
        rw [div_pow]; ring
      have heq : (ν ^ 2 / 16) * ((Real.pi / 2 - x)⁻¹) ^ 2
          = (|ν| / 2) ^ 2 * (1 / (2 * (Real.pi / 2 - x))) ^ 2 := by
        rw [hsq, h2sq, inv_pow]
        field_simp
        ring
      rw [heq]
      exact mul_le_mul hu2 htan_sq (by positivity) (by positivity)
    have step2 : (Real.tan x * u x) ^ 2 ≤ 2 * (deriv u x) ^ 2 + 2 * M ^ 2 := by
      have hsplit : Real.tan x * u x = deriv u x - (deriv u x - Real.tan x * u x) := by ring
      rw [hsplit]
      have hz2 : (deriv u x - Real.tan x * u x) ^ 2 ≤ M ^ 2 := by
        nlinarith [hhlow, abs_nonneg (deriv u x - Real.tan x * u x),
          sq_abs (deriv u x - Real.tan x * u x), abs_nonneg M, sq_abs M, hMpos.le]
      nlinarith [sq_nonneg (deriv u x + (deriv u x - Real.tan x * u x)), hz2,
        sq_nonneg (deriv u x)]
    calc (ν ^ 2 / 16) * ((Real.pi / 2 - x)⁻¹) ^ 2
        ≤ (u x) ^ 2 * (Real.tan x) ^ 2 := step1
      _ = (Real.tan x * u x) ^ 2 := by ring
      _ ≤ 2 * (deriv u x) ^ 2 + 2 * M ^ 2 := step2
  -- integrability on the interval
  have hIntf1 : IntervalIntegrable
      (fun x : ℝ => (ν ^ 2 / 16) * ((Real.pi / 2 - x)⁻¹) ^ 2) volume a b := by
    have hcont_inv : ContinuousOn (fun x : ℝ => (Real.pi / 2 - x)⁻¹) (Set.Icc a b) := by
      refine ContinuousOn.inv₀ (continuous_const.sub continuous_id).continuousOn ?_
      intro x hx
      exact sub_ne_zero.mpr (by linarith [hx.2, hbpi])
    have hc : ContinuousOn (fun x : ℝ => ((Real.pi / 2 - x)⁻¹) ^ 2) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hle_ab]
      exact hcont_inv.pow 2
    exact (hc.const_mul (ν ^ 2 / 16)).intervalIntegrable
  have hInt2 : IntervalIntegrable (fun x : ℝ => 2 * (deriv u x) ^ 2) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle_ab]
    exact (hu1.mono_set hsubIθ).const_mul 2
  have hIntc : IntervalIntegrable (fun _ : ℝ => 2 * M ^ 2) volume a b :=
    intervalIntegrable_const
  have hIntf2 : IntervalIntegrable (fun x : ℝ => 2 * (deriv u x) ^ 2 + 2 * M ^ 2)
      volume a b := hInt2.add hIntc
  have hmono : (∫ x in a..b, (ν ^ 2 / 16) * ((Real.pi / 2 - x)⁻¹) ^ 2)
      ≤ ∫ x in a..b, (2 * (deriv u x) ^ 2 + 2 * M ^ 2) :=
    intervalIntegral.integral_mono_on_of_le_Ioo hle_ab hIntf1 hIntf2 hpt
  have hLHS : (∫ x in a..b, (ν ^ 2 / 16) * ((Real.pi / 2 - x)⁻¹) ^ 2)
      = (ν ^ 2 / 16) * ((Real.pi / 2 - b)⁻¹ - (Real.pi / 2 - a)⁻¹) := by
    rw [intervalIntegral.integral_const_mul, integral_pi_div_two_sub_inv_sq a b hle_ab hbpi]
  have hRHS : (∫ x in a..b, (2 * (deriv u x) ^ 2 + 2 * M ^ 2))
      = 2 * (∫ x in a..b, (deriv u x) ^ 2) + 2 * M ^ 2 * (b - a) := by
    rw [intervalIntegral.integral_add hInt2 hIntc, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hsubint : (∫ x in a..b, (deriv u x) ^ 2) ≤ B := by
    rw [intervalIntegral.integral_of_le hle_ab, hBdef]
    exact MeasureTheory.setIntegral_mono_set hu1
      (Filter.Eventually.of_forall (fun x => sq_nonneg (deriv u x)))
      (Filter.Eventually.of_forall (fun x hx => hsubIθ hx))
  have hkey : (ν ^ 2 / 16) * ((Real.pi / 2 - b)⁻¹ - (Real.pi / 2 - a)⁻¹)
      ≤ 2 * B + 2 * M ^ 2 * δ := by
    calc (ν ^ 2 / 16) * ((Real.pi / 2 - b)⁻¹ - (Real.pi / 2 - a)⁻¹)
        = (∫ x in a..b, (ν ^ 2 / 16) * ((Real.pi / 2 - x)⁻¹) ^ 2) := hLHS.symm
      _ ≤ ∫ x in a..b, (2 * (deriv u x) ^ 2 + 2 * M ^ 2) := hmono
      _ = 2 * (∫ x in a..b, (deriv u x) ^ 2) + 2 * M ^ 2 * (b - a) := hRHS
      _ ≤ 2 * B + 2 * M ^ 2 * δ := by
          have h1 : 2 * (∫ x in a..b, (deriv u x) ^ 2) ≤ 2 * B :=
            mul_le_mul_of_nonneg_left hsubint (by norm_num)
          have h2 : 2 * M ^ 2 * (b - a) ≤ 2 * M ^ 2 * δ := by
            have h3 : 0 ≤ 2 * M ^ 2 := by positivity
            rw [hbaeq]
            exact mul_le_mul_of_nonneg_left (by linarith) h3
          linarith
  have hb_inv : (Real.pi / 2 - b)⁻¹ = C := by
    have h1 : Real.pi / 2 - b = ε := by rw [hbdef]; ring
    rw [h1, hεdef]
    simp
  have ha_inv : (Real.pi / 2 - a)⁻¹ = δ⁻¹ := by
    have h1 : Real.pi / 2 - a = δ := by rw [hadef]; ring
    rw [h1]
  rw [hb_inv, ha_inv] at hkey
  have hval : (ν ^ 2 / 16) * (C - δ⁻¹) = K + ν ^ 2 / (16 * δ) := by
    rw [hCdef, hKdef]
    field_simp
    ring
  rw [hval] at hkey
  rw [hKdef] at hkey
  have hpos : 0 < ν ^ 2 / (16 * δ) := div_pos hν2 (by positivity)
  linarith

end

end Work.FTS.EllipticEst.remov.coerc
end
-- ===== merged: Submission.Work.FTS.GalBasis.exists_mixed_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis

open scoped Real Topology ContDiff
open Set Filter

open Work.FTS.EllipticEst.remov.selfdth (dthCoef DthIter_expansion_of_contDiffOn
  DthCoef_sin_pow_bound)

noncomputable section

set_option autoImplicit false

/-! ## Smoothness of the curried partial derivatives, at a finite order

The `ℋ^k`-machinery of the project uses `ContDiffOn ℝ ⊤` on the fixed sets of
`Work.Spaces`; here the data is only `C⁶` on an arbitrary rectangle, so the
partial-derivative calculus is re-stated at a finite order on an arbitrary open set.
-/

/-- The `z`-partial derivative lowers the order of differentiability by one. -/
theorem contDiffOn_uncurry_pz_le {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (h : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V) :
    ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (by simp)
  have hcomp : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply
      (contDiffOn_const : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun _ : ℝ × ℝ => ((1, 0) : ℝ × ℝ)) V)
  exact hcomp.congr hchain

/-- The `θ`-partial derivative lowers the order of differentiability by one. -/
theorem contDiffOn_uncurry_pth_le {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (h : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V) :
    ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (by simp)
  have hcomp : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply
      (contDiffOn_const : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun _ : ℝ × ℝ => ((0, 1) : ℝ × ℝ)) V)
  exact hcomp.congr hchain

/-- The iterated `z`-partial `∂_z^i` costs `i` orders of differentiability. -/
theorem contDiffOn_uncurry_pzIter_le {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry G) V) :
    ∀ i k : ℕ, i + k ≤ N →
      ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pzIter i G)) V := by
  intro i
  induction i with
  | zero => intro k hk; simpa using h.of_le (Nat.cast_le.mpr (show k ≤ N by omega))
  | succ i ih =>
      intro k hik
      have h2 : ContDiffOn ℝ (((k + 1 : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.pzIter i G)) V := ih (k + 1) (by omega)
      simpa [Work.Spaces.pzIter_succ] using contDiffOn_uncurry_pz_le hV h2

/-- The iterated `θ`-partial `∂_θ^i` costs `i` orders of differentiability. -/
theorem contDiffOn_uncurry_pthIter_le {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry G) V) :
    ∀ i k : ℕ, i + k ≤ N →
      ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pthIter i G)) V := by
  intro i
  induction i with
  | zero => intro k hk; simpa using h.of_le (Nat.cast_le.mpr (show k ≤ N by omega))
  | succ i ih =>
      intro k hik
      have h2 : ContDiffOn ℝ (((k + 1 : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.pthIter i G)) V := ih (k + 1) (by omega)
      simpa [Work.Spaces.pthIter_succ] using contDiffOn_uncurry_pth_le hV h2

/-- The `z`-slice of a function that is `C^N` on an open set is `C^N` at the point. -/
theorem contDiffAt_slice_fst_of_uncurry {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {N : ℕ} (h : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry G) V)
    {z θ : ℝ} (hz : (z, θ) ∈ V) :
    ContDiffAt ℝ ((N : ℕ) : WithTop ℕ∞) (fun z' => G z' θ) z := by
  have hc : ContDiffAt ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry G) (z, θ) :=
    h.contDiffAt (hV.mem_nhds hz)
  have hlin : ContDiffAt ℝ ((N : ℕ) : WithTop ℕ∞) (fun z' : ℝ => (z', θ)) z := by fun_prop
  simpa [Function.comp_def, Function.uncurry] using hc.comp z hlin

/-- Differentiability of the `z`-slice of an iterated `z`-partial, at a point of an open
set where the function is smooth enough. -/
theorem differentiableAt_slice_pzIter {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {N : ℕ} (h : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry G) V)
    {i : ℕ} (hi : i + 1 ≤ N) {z θ : ℝ} (hz : (z, θ) ∈ V) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter i G z' θ) z := by
  have h1 : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞)
      (Function.uncurry (Work.Spaces.pzIter i G)) V :=
    contDiffOn_uncurry_pzIter_le hV h i 1 (by omega)
  have h2 : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞)
      (fun z' => Work.Spaces.pzIter i G z' θ) z :=
    contDiffAt_slice_fst_of_uncurry hV h1 hz
  exact h2.differentiableAt (by simp)

/-- Smoothness of the `z`-slice of an iterated `θ`-partial. -/
theorem contDiffAt_slice_pthIter {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry G) V)
    {i k : ℕ} (hi : i + k ≤ N) {z θ : ℝ} (hz : (z, θ) ∈ V) :
    ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) (fun z' => Work.Spaces.pthIter i G z' θ) z :=
  contDiffAt_slice_fst_of_uncurry hV (contDiffOn_uncurry_pthIter_le hV h i k hi) hz

/-! ## The expansion of `D_z^n = (z∂_z)^n` in Stirling numbers -/

/-- The derivative of `z ↦ z^k`. -/
private theorem deriv_zpow (k : ℕ) (z : ℝ) :
    deriv (fun z' : ℝ => z' ^ k) z = (k : ℝ) * z ^ (k - 1) := by
  have h := deriv_pow (f := fun z' : ℝ => z') (x := z) differentiableAt_id k
  rw [show (fun z' : ℝ => z') ^ k = (fun z' : ℝ => z' ^ k) from rfl] at h
  have h1 : deriv (fun z' : ℝ => z') z = 1 := deriv_id z
  rw [h, h1]
  ring

/-- The elementary algebra of one term of the induction step. -/
private theorem z_mul_term (k : ℕ) (z A B : ℝ) :
    z * ((k : ℝ) * z ^ (k - 1) * A + z ^ k * B) = (k : ℝ) * z ^ k * A + z ^ (k + 1) * B := by
  rcases k with _ | m
  · ring
  · rw [pow_succ]; push_cast; ring

/-- **The Stirling expansion of `D_z^n`**, at a point where the `z`-slice of `h` is
`C^{n+1}` on an open set contained in the domain:
`D_z^n h = ∑_{k ≤ n} S(n,k) z^k ∂_z^k h`. -/
theorem DzIter_eq_sum_scoef_of_contDiffOn (h : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (hU : IsOpen U) :
    ∀ n : ℕ, ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry h) U →
      ∀ z θ, (z, θ) ∈ U →
        Work.Spaces.DzIter n h z θ =
          ∑ k ∈ Finset.range (n + 1), (Work.Spaces.scoef n k : ℝ) * (z ^ k * Work.Spaces.pzIter k h z θ) := by
  intro n
  induction n with
  | zero =>
      intro hsm z θ hzθ
      rw [Finset.sum_range_one, show Work.Spaces.scoef 0 0 = 1 from rfl]
      norm_num
  | succ n ih =>
      intro hsm z θ hzθ
      have hsm' : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry h) U :=
        hsm.of_le (Nat.cast_le.mpr (show n + 1 ≤ n + 2 by omega))
      have hdiff : ∀ k : ℕ, k ≤ n →
          DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter k h z' θ) z := fun k hk =>
        differentiableAt_slice_pzIter hU hsm (i := k) (by omega) hzθ
      have hd1 : ∀ k : ℕ, DifferentiableAt ℝ (fun z' : ℝ => z' ^ k) z := fun k =>
        differentiableAt_pow k
      have hd3 : ∀ k ∈ Finset.range (n + 1),
          DifferentiableAt ℝ (fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ) z :=
        fun k hk => (hd1 k).mul (hdiff k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
      have hsl : {z' : ℝ | (z', θ) ∈ U} ∈ 𝓝 z := by
        have hopen : IsOpen {z' : ℝ | (z', θ) ∈ U} :=
          hU.preimage (by fun_prop : Continuous fun z' : ℝ => (z', θ))
        exact hopen.mem_nhds hzθ
      have hev : (fun z' => Work.Spaces.DzIter n h z' θ)
          =ᶠ[𝓝 z] (fun z' => ∑ k ∈ Finset.range (n + 1),
              (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ)) := by
        filter_upwards [hsl] with z' hz'
        exact ih hsm' z' θ hz'
      have hterm : ∀ k : ℕ, k ≤ n →
          deriv (fun z' : ℝ => (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ)) z
            = (Work.Spaces.scoef n k : ℝ)
                * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                    + z ^ k * Work.Spaces.pzIter (k + 1) h z θ) := by
        intro k hk
        rw [deriv_const_mul (d := fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ)
          (Work.Spaces.scoef n k : ℝ) ((hd1 k).mul (hdiff k hk))]
        congr 1
        rw [show (fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ)
              = (fun z' : ℝ => z' ^ k) * (fun z' : ℝ => Work.Spaces.pzIter k h z' θ) from rfl,
          deriv_mul (hd1 k) (hdiff k hk), deriv_zpow]
        rfl
      have hderiv : deriv (fun z' => Work.Spaces.DzIter n h z' θ) z
          = ∑ k ∈ Finset.range (n + 1), (Work.Spaces.scoef n k : ℝ)
              * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                  + z ^ k * Work.Spaces.pzIter (k + 1) h z θ) := by
        rw [hev.deriv_eq]
        have hsumfun : (fun z' => ∑ k ∈ Finset.range (n + 1),
              (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ))
            = (∑ k ∈ Finset.range (n + 1),
                fun z' => (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ)) := by
          funext z'
          simp [Finset.sum_apply]
        rw [hsumfun, deriv_sum (fun k hk => (hd3 k hk).const_mul (Work.Spaces.scoef n k : ℝ))]
        exact Finset.sum_congr rfl fun k hk =>
          hterm k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
      calc Work.Spaces.DzIter (n + 1) h z θ
          = z * deriv (fun z' => Work.Spaces.DzIter n h z' θ) z := by
            simp [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
        _ = z * (∑ k ∈ Finset.range (n + 1), (Work.Spaces.scoef n k : ℝ)
              * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                  + z ^ k * Work.Spaces.pzIter (k + 1) h z θ)) := by rw [hderiv]
        _ = ∑ k ∈ Finset.range (n + 1), (Work.Spaces.scoef n k : ℝ)
              * ((k : ℝ) * z ^ k * Work.Spaces.pzIter k h z θ
                  + z ^ (k + 1) * Work.Spaces.pzIter (k + 1) h z θ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [show z * ((Work.Spaces.scoef n k : ℝ)
                  * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                      + z ^ k * Work.Spaces.pzIter (k + 1) h z θ))
                = (Work.Spaces.scoef n k : ℝ)
                  * (z * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                      + z ^ k * Work.Spaces.pzIter (k + 1) h z θ)) from by ring,
              z_mul_term]
        _ = ∑ j ∈ Finset.range (n + 2),
              (Work.Spaces.scoef (n + 1) j : ℝ) * (z ^ j * Work.Spaces.pzIter j h z θ) :=
            Work.Spaces.scoef_sum_shift n (fun k => Work.Spaces.pzIter k h z θ) z

/-- **The angular expansion commutes with `∂_z^k`**: on an open set where `F` is smooth
enough, the `k`-th `z`-derivative of the exact expansion of `D_θ^b` is the expansion of the
`k`-th `z`-derivative. -/
theorem pzIter_DthIter_expansion {F : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {N : ℕ}
    (hF : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry F) U)
    {b k : ℕ} (hb1 : b + 1 ≤ N) (hbk : b + k ≤ N) {z θ : ℝ} (hzθ : (z, θ) ∈ U) :
    Work.Spaces.pzIter k (Work.Spaces.DthIter b F) z θ
      = ∑ r ∈ Finset.range (b + 1), dthCoef b r θ * Work.Spaces.pzIter k (Work.Spaces.pthIter r F) z θ := by
  have hexp : ∀ z' θ' : ℝ, (z', θ') ∈ U →
      Work.Spaces.DthIter b F z' θ'
        = ∑ r ∈ Finset.range (b + 1), dthCoef b r θ' * Work.Spaces.pthIter r F z' θ' :=
    fun z' θ' h => DthIter_expansion_of_contDiffOn b F U hU
      (hF.of_le (Nat.cast_le.mpr hb1)) z' θ' h
  have hsl : {z' : ℝ | (z', θ) ∈ U} ∈ 𝓝 z := by
    have hopen : IsOpen {z' : ℝ | (z', θ) ∈ U} :=
      hU.preimage (by fun_prop : Continuous fun z' : ℝ => (z', θ))
    exact hopen.mem_nhds hzθ
  have hev : (fun z' => Work.Spaces.DthIter b F z' θ)
      =ᶠ[𝓝 z] (fun z' => ∑ r ∈ Finset.range (b + 1),
          dthCoef b r θ * Work.Spaces.pthIter r F z' θ) := by
    filter_upwards [hsl] with z' hz'
    exact hexp z' θ hz'
  calc Work.Spaces.pzIter k (Work.Spaces.DthIter b F) z θ
      = iteratedDeriv k (fun z' => Work.Spaces.DthIter b F z' θ) z :=
        Work.Spaces.pzIter_eq_iteratedDeriv k _ z θ
    _ = iteratedDeriv k (fun z' => ∑ r ∈ Finset.range (b + 1),
          dthCoef b r θ * Work.Spaces.pthIter r F z' θ) z := hev.iteratedDeriv_eq k
    _ = ∑ r ∈ Finset.range (b + 1),
          dthCoef b r θ * iteratedDeriv k (fun z' => Work.Spaces.pthIter r F z' θ) z :=
        Work.Spaces.iteratedDeriv_sum_const_mul _ (fun r => dthCoef b r θ)
          (fun r z' => Work.Spaces.pthIter r F z' θ) k z
          (fun r hr => contDiffAt_slice_pthIter hU hF
            (i := r) (k := k) (by
              have hr' : r ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
              omega) hzθ)
    _ = ∑ r ∈ Finset.range (b + 1),
          dthCoef b r θ * Work.Spaces.pzIter k (Work.Spaces.pthIter r F) z θ := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Work.Spaces.pzIter_eq_iteratedDeriv]

/-! ## The main bound

`D_z^a D_θ^b F` is a *finite linear combination*, with coefficients bounded on the box, of the
plain derivatives `∂_z^k ∂_θ^r F = pzIter k (pthIter r F)` with `k ≤ a`, `r ≤ b`:

* `D_z^a = ∑_{k≤a} S(a,k) z^k ∂_z^k` (Stirling numbers of the second kind,
  `DzIter_eq_sum_scoef_of_contDiffOn`);
* `∂_z^k (D_θ^b F) = ∑_{r≤b} a_{b,r}(θ) · ∂_z^k∂_θ^r F` (`pzIter_DthIter_expansion`, from the
  exact expansion `D_θ^b = ∑_r a_{b,r} ∂_θ^r` of `DthIter_expansion_of_contDiffOn` and the fact
  that the coefficients `a_{b,r}` do not depend on `z`),
* and `|a_{b,r}(θ)| ≤ K_{b,r} |sin 2θ|^r ≤ K_{b,r}` (`DthCoef_sin_pow_bound`), while
  `|z| ≤ max |A| |B|` on `[A,B]`.

Every `pzIter k (pthIter r F)` occurring has `k + r ≤ a + b ≤ 4`, so the hypothesis bounds it by
`M`, giving `|D_z^a D_θ^b F| ≤ K M` with
`K = (∑_{k≤a} S(a,k) (max |A| |B|)^k) · (∑_{r≤b} K_{b,r})`. -/


end

end Work.FTS.GalBasis
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.aCoeff_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ### Elementary facts about `κ` on `[0, xNear]` -/


lemma kappa_abs_le_one {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) xNear) : |kappa x| ≤ 1 := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2, xNear_lt]
  rw [kappa_eq_sqrt, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg x])

lemma kappa_pos_of_mem {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) xNear) : 0 < kappa x := by
  have hx2 : x ^ 2 < 1 := by nlinarith [hx.1, hx.2, xNear_lt]
  rw [kappa_eq_sqrt]
  exact Real.sqrt_pos.mpr (by linarith)

/-- `1/κ` is bounded on `[0,xNear]`. -/
lemma exists_inv_kappa_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc (0 : ℝ) xNear, 1 / kappa x ≤ C := by
  have hpos : ∀ x ∈ Set.Icc (0 : ℝ) xNear, kappa x ≠ 0 :=
    fun x hx => ne_of_gt (kappa_pos_of_mem hx)
  have hcont : ContinuousOn (fun x => 1 / kappa x) (Set.Icc (0 : ℝ) xNear) :=
    continuousOn_const.div (contDiffOn_kappa.continuousOn.mono Icc_subset_U) hpos
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have hk : 0 < kappa x := kappa_pos_of_mem hx
  have h1 : 1 / kappa x = ‖1 / kappa x‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [h1]
  exact le_trans (hC x hx) (le_max_left _ _)

lemma hasDerivAt_kappa {x : ℝ} (hx : x ∈ U) : HasDerivAt kappa (-(x / kappa x)) x := by
  have hx2 : x ^ 2 < 1 := by
    have h1 : |x| < 3 / 4 := abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    nlinarith [abs_nonneg x, sq_abs x]
  have hne : (1 : ℝ) - x ^ 2 ≠ 0 := by nlinarith
  have h1 : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
    have h := (hasDerivAt_const (x := x) (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)
    have hf : ((fun _ : ℝ => (1 : ℝ)) - (id : ℝ → ℝ) ^ 2) = fun y : ℝ => 1 - y ^ 2 := by
      funext y; simp
    rw [hf] at h
    convert h using 1
    simp
  have h2 : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      (-(2 * x) / (2 * Real.sqrt (1 - x ^ 2))) x := h1.sqrt hne
  rw [show kappa = fun y : ℝ => Real.sqrt (1 - y ^ 2) from funext fun y => kappa_eq_sqrt y]
  have hval : -(2 * x) / (2 * Real.sqrt (1 - x ^ 2))
      = -(x / (fun y : ℝ => Real.sqrt (1 - y ^ 2)) x) := by
    change -(2 * x) / (2 * Real.sqrt (1 - x ^ 2)) = -(x / Real.sqrt (1 - x ^ 2))
    ring
  rw [hval] at h2
  exact h2

lemma deriv_two_kappa_eq {x : ℝ} (hx : x ∈ U) :
    deriv (fun y : ℝ => 2 * kappa y) x = -(2 * x / kappa x) := by
  have h : deriv (fun y : ℝ => (2 : ℝ) * kappa y) x = 2 * deriv kappa x :=
    deriv_const_mul 2 (hasDerivAt_kappa hx).differentiableAt
  rw [show (fun y : ℝ => 2 * kappa y) = (fun y : ℝ => (2 : ℝ) * kappa y) from rfl, h,
    (hasDerivAt_kappa hx).deriv]
  ring

lemma contDiffOn_two_kappa : ContDiffOn ℝ ⊤ (fun x : ℝ => 2 * kappa x) U :=
  contDiffOn_const.mul contDiffOn_kappa

lemma exists_jetBdd_two_kappa (K : ℕ) :
    ∃ M : ℝ, JetBdd K (fun x : ℝ => 2 * kappa x) M :=
  exists_jetBdd_of_contDiffOn K contDiffOn_two_kappa

/-! ### The recursion `genCoeff`: equation lemmas and truncation -/

lemma genCoeff_zero_eq (init : ℝ → ℝ) (j : ℕ) :
    genCoeff init 0 j = fun x => if j = 0 then init x else 0 := rfl

lemma genCoeff_succ_eq (init : ℝ → ℝ) (i j : ℕ) :
    genCoeff init i.succ j = fun x =>
      2 * kappa x * (x * deriv (genCoeff init i j) x + (j : ℝ) * genCoeff init i j x)
        + (if j = 0 then 0 else 2 * kappa x * genCoeff init i (j - 1) x) := rfl

lemma genCoeff_init_zero (init : ℝ → ℝ) : genCoeff init 0 0 = init := by
  rw [genCoeff_zero_eq]
  funext x
  simp

lemma genCoeff_succ_zero (init : ℝ → ℝ) (i : ℕ) :
    genCoeff init i.succ 0 = fun x => 2 * kappa x * (x * deriv (genCoeff init i 0) x) := by
  rw [genCoeff_succ_eq]
  funext x
  simp

lemma genCoeff_succ_succ (init : ℝ → ℝ) (i j : ℕ) :
    genCoeff init i.succ j.succ = fun x =>
      2 * kappa x * (x * deriv (genCoeff init i j.succ) x
        + ((j.succ : ℕ) : ℝ) * genCoeff init i j.succ x)
        + 2 * kappa x * genCoeff init i j x := by
  rw [genCoeff_succ_eq]
  funext x
  simp

/-- For `j > i` the coefficient `genCoeff init i j` vanishes identically. -/
lemma genCoeff_zero (init : ℝ → ℝ) : ∀ i j : ℕ, i < j → genCoeff init i j = 0 := by
  intro i
  induction i with
  | zero =>
      intro j hj
      rw [genCoeff_zero_eq]
      funext x
      simp [Nat.pos_iff_ne_zero.mp hj]
  | succ i ih =>
      intro j hj
      rw [genCoeff_succ_eq, ih j (by omega), ih (j - 1) (by omega)]
      funext x
      have hj0 : j ≠ 0 := by omega
      simp [hj0]

lemma bCoeff_eq_genCoeff : ∀ i j : ℕ, bCoeff i j = genCoeff (fun _ : ℝ => 1) i j := by
  intro i
  induction i with
  | zero =>
      intro j
      rw [show bCoeff 0 j = fun _ => (if j = 0 then (1 : ℝ) else 0) from rfl, genCoeff_zero_eq]
  | succ i ih =>
      intro j
      rw [show bCoeff i.succ j = fun x =>
          2 * kappa x * (x * deriv (bCoeff i j) x + (j : ℝ) * bCoeff i j x)
            + (if j = 0 then 0 else 2 * kappa x * bCoeff i (j - 1) x) from rfl,
        genCoeff_succ_eq, ih j, ih (j - 1)]

lemma aCoeff_eq_genCoeff : ∀ i j : ℕ, aCoeff i j = genCoeff (fun x : ℝ => 2 * kappa x) i j := by
  intro i
  induction i with
  | zero =>
      intro j
      rw [show aCoeff 0 j = fun x => (if j = 0 then 2 * kappa x else 0) from rfl, genCoeff_zero_eq]
  | succ i ih =>
      intro j
      rw [show aCoeff i.succ j = fun x =>
          2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x)
            + (if j = 0 then 0 else 2 * kappa x * aCoeff i (j - 1) x) from rfl,
        genCoeff_succ_eq, ih j, ih (j - 1)]

/-! ### The constant recursion and the main `JetBdd` induction -/

/-- One step of the constant recursion of the `JetBdd` induction. -/
noncomputable def levStep (M : ℝ) (n : ℕ) (C : ℝ) : ℝ :=
  (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n * C * ((n : ℝ) + 2) + (2 : ℝ) ^ n + ((n : ℝ) + 2) * C + 1)
    + 2 * C + 1

/-- The constant of the `JetBdd` induction at level `i`: `levBound M0 M n i` bounds the first
`n - i` derivatives of the level-`i` coefficients. -/
noncomputable def levBound (M0 M : ℝ) (n : ℕ) : ℕ → ℝ
  | 0 => M0 + 1
  | (i + 1) => levStep M n (levBound M0 M n i)

lemma levBound_succ (M0 M : ℝ) (n i : ℕ) :
    levBound M0 M n i.succ = levStep M n (levBound M0 M n i) := rfl

lemma levBound_nonneg {M0 M : ℝ} (h0 : 0 ≤ M0) (hM : 0 ≤ M) (n : ℕ) :
    ∀ i, 0 ≤ levBound M0 M n i := by
  intro i
  induction i with
  | zero => rw [levBound]; linarith
  | succ i ih =>
      rw [levBound_succ]
      simp only [levStep]
      positivity

private lemma lev_zero_case {M C : ℝ} {K n : ℕ} (hKn : K ≤ n) (hM : 0 ≤ M) (hC : 0 ≤ C) :
    (2 : ℝ) ^ K * M * ((2 : ℝ) ^ K * 1 * C) ≤ levStep M n C := by
  have hA : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hKn
  have hA0 : (0 : ℝ) ≤ (2 : ℝ) ^ K := by positivity
  have hAn : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn2 : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith
  have hMC : (0 : ℝ) ≤ M * C := mul_nonneg hM hC
  have hAA : (2 : ℝ) ^ K * (2 : ℝ) ^ K ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n := mul_le_mul hA hA hA0 hAn
  have key : (2 : ℝ) ^ K * M * ((2 : ℝ) ^ K * 1 * C) ≤ (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n * C * ((n : ℝ) + 2)) := by
    have h1 : (2 : ℝ) ^ K * (2 : ℝ) ^ K * (M * C) ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) :=
      mul_le_mul_of_nonneg_right hAA hMC
    have h2 : (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) * ((n : ℝ) + 2) := by
      have := mul_le_mul_of_nonneg_left hn2 (mul_nonneg (mul_nonneg hAn hAn) hMC)
      simpa using this
    calc (2 : ℝ) ^ K * M * ((2 : ℝ) ^ K * 1 * C) = (2 : ℝ) ^ K * (2 : ℝ) ^ K * (M * C) := by ring
      _ ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) := h1
      _ ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) * ((n : ℝ) + 2) := h2
      _ = (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n * C * ((n : ℝ) + 2)) := by ring
  have hfin : (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n * C * ((n : ℝ) + 2)) ≤ levStep M n C := by
    simp only [levStep]
    have hX : (0 : ℝ) ≤ (2 : ℝ) ^ n + ((n : ℝ) + 2) * C + 1 := by positivity
    have hle : (2 : ℝ) ^ n * C * ((n : ℝ) + 2)
        ≤ (2 : ℝ) ^ n * C * ((n : ℝ) + 2) + (2 : ℝ) ^ n + ((n : ℝ) + 2) * C + 1 := by linarith
    have := mul_le_mul_of_nonneg_left hle (mul_nonneg hAn hM)
    linarith [this, hC]
  exact key.trans hfin

private lemma lev_succ_case {M C : ℝ} {K n : ℕ} (hKn : K ≤ n) (hM : 0 ≤ M) (hC : 0 ≤ C) :
    (2 : ℝ) ^ K * M * ((2 : ℝ) ^ K * 1 * C + (2 : ℝ) ^ K * (n : ℝ) * C)
      + (2 : ℝ) ^ K * M * C ≤ levStep M n C := by
  have hA : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hKn
  have hA0 : (0 : ℝ) ≤ (2 : ℝ) ^ K := by positivity
  have hAn : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn2 : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hAn1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hMC : (0 : ℝ) ≤ M * C := mul_nonneg hM hC
  have hAA : (2 : ℝ) ^ K * (2 : ℝ) ^ K ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n := mul_le_mul hA hA hA0 hAn
  have hpart1 : (2 : ℝ) ^ K * M * ((2 : ℝ) ^ K * 1 * C + (2 : ℝ) ^ K * (n : ℝ) * C)
      ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) * ((n : ℝ) + 2) := by
    have heq : (2 : ℝ) ^ K * M * ((2 : ℝ) ^ K * 1 * C + (2 : ℝ) ^ K * (n : ℝ) * C)
        = (2 : ℝ) ^ K * (2 : ℝ) ^ K * (M * C) * ((n : ℝ) + 1) := by ring
    rw [heq]
    have h1 : (2 : ℝ) ^ K * (2 : ℝ) ^ K * (M * C) ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) :=
      mul_le_mul_of_nonneg_right hAA hMC
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
    have h3 : (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) * ((n : ℝ) + 1)
        ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) * ((n : ℝ) + 2) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact h2.trans h3
  have hpart2 : (2 : ℝ) ^ K * M * C
      ≤ (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n + ((n : ℝ) + 2) * C + 1) := by
    have h1 : (2 : ℝ) ^ K * M * C ≤ (2 : ℝ) ^ n * M * C :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hM) hC
    have h2 : (2 : ℝ) ^ n * M * C ≤ (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n + ((n : ℝ) + 2) * C + 1) := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hAn hM)
      have hX : (0 : ℝ) ≤ (2 : ℝ) ^ n + (n : ℝ) * C + 1 := by positivity
      linarith
    exact h1.trans h2
  have hsum : (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) * ((n : ℝ) + 2)
      + (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n + ((n : ℝ) + 2) * C + 1) ≤ levStep M n C := by
    simp only [levStep]
    have hAM : (0 : ℝ) ≤ (2 : ℝ) ^ n * M := by positivity
    have e1 : (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) * ((n : ℝ) + 2)
        = (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n * C * ((n : ℝ) + 2)) := by ring
    have e2 : (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n * C * ((n : ℝ) + 2))
        + (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n + ((n : ℝ) + 2) * C + 1)
        = (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n * C * ((n : ℝ) + 2)
            + ((2 : ℝ) ^ n + ((n : ℝ) + 2) * C + 1)) := by ring
    rw [e1, e2]
    have hY : (0 : ℝ) ≤ (2 : ℝ) ^ n + ((n : ℝ) + 2) * C + 1 := by positivity
    have hle : (2 : ℝ) ^ n * C * ((n : ℝ) + 2)
        ≤ (2 : ℝ) ^ n * C * ((n : ℝ) + 2) + (2 : ℝ) ^ n + ((n : ℝ) + 2) * C + 1 := by linarith
    have := mul_le_mul_of_nonneg_left hle hAM
    linarith [this, hC]
  linarith [hpart1, hpart2, hsum]

/-- **The main induction.**  For `i + K ≤ n`, the first `K + 1` derivatives of every level-`i`
coefficient `genCoeff init i j` with `j ≤ i` are bounded by `levBound Minit Mκ n i` on
`[0, xNear]`; `Minit` bounds the jets of the initial datum, `Mκ` those of `2κ`. -/
theorem genCoeff_jetBdd (n : ℕ) {init : ℝ → ℝ} {Minit Mκ : ℝ}
    (hinit : JetBdd n init Minit) (hκ : JetBdd n (fun x : ℝ => 2 * kappa x) Mκ) :
    ∀ i K : ℕ, i + K ≤ n → ∀ j ≤ i, JetBdd K (genCoeff init i j) (levBound Minit Mκ n i) := by
  intro i
  induction i with
  | zero =>
      intro K hK j hj
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      subst hj0
      rw [genCoeff_init_zero]
      have hle : JetBdd K init Minit := hinit.jet_mono (by omega)
      refine hle.jet_le ?_
      rw [levBound]
      linarith [hinit.jet_nonneg]
  | succ i ih =>
      intro K hK j hj
      have hM0 : 0 ≤ Minit := hinit.jet_nonneg
      have hMκ0 : 0 ≤ Mκ := hκ.jet_nonneg
      have hC : 0 ≤ levBound Minit Mκ n i := levBound_nonneg hM0 hMκ0 n i
      have ihK : ∀ j ≤ i, JetBdd (K + 1) (genCoeff init i j) (levBound Minit Mκ n i) :=
        ih (K + 1) (by omega)
      have hk : JetBdd K (fun x : ℝ => 2 * kappa x) Mκ := hκ.jet_mono (by omega)
      have hKn : K ≤ n := by omega
      rw [levBound_succ]
      rcases j with _ | j
      · rw [genCoeff_succ_zero]
        have hd : JetBdd K (deriv (genCoeff init i 0)) (levBound Minit Mκ n i) :=
          (ihK 0 (by omega)).jet_deriv
        have h1 : JetBdd K ((fun x : ℝ => x) * deriv (genCoeff init i 0))
            ((2 : ℝ) ^ K * 1 * levBound Minit Mκ n i) := JetBdd.jet_mul (JetBdd.jet_id K) hd
        have h2 : JetBdd K ((fun x : ℝ => 2 * kappa x) * ((fun x : ℝ => x) * deriv (genCoeff init i 0)))
            ((2 : ℝ) ^ K * Mκ * ((2 : ℝ) ^ K * 1 * levBound Minit Mκ n i)) :=
          JetBdd.jet_mul hk h1
        exact h2.jet_le (lev_zero_case hKn hMκ0 hC)
      · rw [genCoeff_succ_succ]
        have hb1 : JetBdd (K + 1) (genCoeff init i j.succ) (levBound Minit Mκ n i) := by
          by_cases hji : j.succ ≤ i
          · exact ihK j.succ hji
          · have heq : j.succ = i.succ := by omega
            rw [heq, genCoeff_zero init i i.succ (by omega)]
            exact (JetBdd.jet_zero (K + 1)).jet_le hC
        have hd1 : JetBdd K (deriv (genCoeff init i j.succ)) (levBound Minit Mκ n i) := hb1.jet_deriv
        have hx1 : JetBdd K ((fun x : ℝ => x) * deriv (genCoeff init i j.succ))
            ((2 : ℝ) ^ K * 1 * levBound Minit Mκ n i) :=
          JetBdd.jet_mul (JetBdd.jet_id K) hd1
        have hjc : JetBdd K ((fun _ : ℝ => ((j.succ : ℕ) : ℝ)) * genCoeff init i j.succ)
            ((2 : ℝ) ^ K * |((j.succ : ℕ) : ℝ)| * levBound Minit Mκ n i) :=
          JetBdd.jet_mul (JetBdd.jet_const K ((j.succ : ℕ) : ℝ)) (hb1.jet_mono (Nat.le_succ K))
        have hjcn : JetBdd K ((fun _ : ℝ => ((j.succ : ℕ) : ℝ)) * genCoeff init i j.succ)
            ((2 : ℝ) ^ K * (n : ℝ) * levBound Minit Mκ n i) := by
          refine hjc.jet_le ?_
          have hle : |((j.succ : ℕ) : ℝ)| ≤ (n : ℝ) := by
            rw [abs_of_nonneg (by positivity)]
            exact_mod_cast (by omega : j.succ ≤ n)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by positivity)) hC
        have hs : JetBdd K ((fun x : ℝ => x) * deriv (genCoeff init i j.succ)
              + (fun _ : ℝ => ((j.succ : ℕ) : ℝ)) * genCoeff init i j.succ)
            ((2 : ℝ) ^ K * 1 * levBound Minit Mκ n i
              + (2 : ℝ) ^ K * (n : ℝ) * levBound Minit Mκ n i) := hx1.jet_add hjcn
        have hm1 : JetBdd K ((fun x : ℝ => 2 * kappa x)
              * ((fun x : ℝ => x) * deriv (genCoeff init i j.succ)
                + (fun _ : ℝ => ((j.succ : ℕ) : ℝ)) * genCoeff init i j.succ))
            ((2 : ℝ) ^ K * Mκ * ((2 : ℝ) ^ K * 1 * levBound Minit Mκ n i
              + (2 : ℝ) ^ K * (n : ℝ) * levBound Minit Mκ n i)) := JetBdd.jet_mul hk hs
        have hm2 : JetBdd K ((fun x : ℝ => 2 * kappa x) * genCoeff init i j)
            ((2 : ℝ) ^ K * Mκ * levBound Minit Mκ n i) :=
          JetBdd.jet_mul hk ((ihK j (by omega)).jet_mono (Nat.le_succ K))
        exact (hm1.jet_add hm2).jet_le (lev_succ_case hKn hMκ0 hC)

/-! ### The vanishing of the first derivative of the `j = 0` coefficients -/

/-- For the `a`-family (`init = 2κ`) the derivative of the `j = 0` coefficient vanishes at `0`
like `x`: `|(genCoeff (2κ) i 0)'| ≤ C x` on `[0,xNear]`. -/
lemma genCoeff_a0_deriv_le : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ x ∈ Set.Icc (0 : ℝ) xNear,
      |deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x| ≤ C * x := by
  intro i
  induction i with
  | zero =>
      obtain ⟨C0, hC0nn, hC0bd⟩ := exists_inv_kappa_bound
      refine ⟨2 * C0 + 1, by linarith, ?_⟩
      intro x hx
      have hxU : x ∈ U := Icc_subset_U hx
      have hxnn : 0 ≤ x := hx.1
      have hkpos : 0 < kappa x := kappa_pos_of_mem hx
      have hκnn : 0 ≤ kappa x := le_of_lt hkpos
      rw [genCoeff_init_zero, deriv_two_kappa_eq hxU, abs_neg, abs_div,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * x), abs_of_pos hkpos]
      have h2 : 1 ≤ C0 * kappa x := by
        have h1 : 1 / kappa x ≤ C0 := hC0bd x hx
        rwa [div_le_iff₀ hkpos] at h1
      rw [div_le_iff₀ hkpos]
      nlinarith [h2, hxnn, hκnn]
  | succ i ih =>
      obtain ⟨C, hCnn, hCbd⟩ := ih
      obtain ⟨C0, hC0nn, hC0bd⟩ := exists_inv_kappa_bound
      obtain ⟨E, hE⟩ := exists_jetBdd_two_kappa (i + 2)
      have hb : JetBdd 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) (levBound E E (i + 2) i) :=
        genCoeff_jetBdd (n := i + 2) (init := fun y : ℝ => 2 * kappa y) (Minit := E) (Mκ := E)
          hE hE i 2 (by omega) 0 (by omega)
      have hEnn : 0 ≤ levBound E E (i + 2) i :=
        levBound_nonneg hE.jet_nonneg hE.jet_nonneg (i + 2) i
      refine ⟨2 * C0 * C + 2 * C + 2 * levBound E E (i + 2) i + 1,
        by nlinarith [hCnn, hC0nn, hEnn, mul_nonneg hC0nn hCnn], ?_⟩
      intro x hx
      have hxU : x ∈ U := Icc_subset_U hx
      have hxnn : 0 ≤ x := hx.1
      have hx1 : x ≤ 1 := le_trans hx.2 xNear_le_one
      have hkpos : 0 < kappa x := kappa_pos_of_mem hx
      have hκnn : 0 ≤ kappa x := le_of_lt hkpos
      have hsm : ContDiffOn ℝ ⊤ (genCoeff (fun y : ℝ => 2 * kappa y) i 0) U := hb.jet_smooth
      have hdd_smooth : ContDiffOn ℝ ⊤ (deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0)) U := by
        simpa [Function.iterate_one] using contDiffOn_iterate_deriv hsm 1
      have hDdiff : DifferentiableAt ℝ (deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0)) x :=
        (hdd_smooth.contDiffAt (U_isOpen.mem_nhds hxU)).differentiableAt (by norm_num)
      have hdd : deriv (deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0)) x
          = iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x := by
        rw [show deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0)
            = iteratedDeriv 1 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) from
              (iteratedDeriv_one).symm,
          ← iteratedDeriv_succ (n := 1) (f := genCoeff (fun y : ℝ => 2 * kappa y) i 0)]
      have hval : deriv (fun y : ℝ => 2 * kappa y * (y * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) y)) x
          = (-(2 * x / kappa x)) * (x * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x)
            + (2 * kappa x) * (deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x
              + x * iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x) := by
        have hf : HasDerivAt (fun y : ℝ => 2 * kappa y) (-(2 * x / kappa x)) x := by
          have h := (hasDerivAt_kappa hxU).const_mul (2 : ℝ)
          have hv : (2 : ℝ) * (-(x / kappa x)) = -(2 * x / kappa x) := by ring
          rwa [hv] at h
        have hD : HasDerivAt (deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0))
            (iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x) x := by
          have h := hDdiff.hasDerivAt
          rwa [hdd] at h
        have hg : HasDerivAt (fun y : ℝ => y * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) y)
            (deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x
              + x * iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x) x := by
          have h := (hasDerivAt_id x).mul hD
          have hfun : (fun y : ℝ => y * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) y)
              = (id : ℝ → ℝ) * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) := rfl
          rw [← hfun] at h
          simpa using h
        have hfin : HasDerivAt (fun y : ℝ => 2 * kappa y * (y * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) y))
            ((-(2 * x / kappa x)) * (x * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x)
              + (2 * kappa x) * (deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x
                + x * iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x)) x := by
          have h := hf.mul hg
          have hfun : (fun y : ℝ => 2 * kappa y * (y * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) y))
              = (fun y : ℝ => 2 * kappa y)
                * (fun y : ℝ => y * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) y) := rfl
          rw [← hfun] at h
          simpa using h
        exact hfin.deriv
      rw [genCoeff_succ_zero, hval]
      have hE2 : |iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x|
          ≤ levBound E E (i + 2) i := hb.jet_bound 2 (by omega) x hx
      have hDx : |deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x| ≤ C * x := hCbd x hx
      have hk1 : |kappa x| ≤ 1 := kappa_abs_le_one hx
      have hA : |-(2 * x / kappa x)| ≤ 2 * C0 * x := by
        rw [abs_neg, abs_of_nonneg (div_nonneg (by positivity) hκnn)]
        have h2 : x / kappa x ≤ C0 * x := by
          have h1 : 1 / kappa x ≤ C0 := hC0bd x hx
          rw [div_le_iff₀ hkpos] at h1 ⊢
          nlinarith [h1, hC0nn, hxnn, hκnn]
        have h3 : 2 * x / kappa x = 2 * (x / kappa x) := by ring
        rw [h3]
        linarith
      have hDxn : |x * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x| ≤ C * x ^ 2 := by
        rw [abs_mul, abs_of_nonneg hxnn]
        nlinarith [hDx, hCnn, hxnn]
      have hinside : |deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x
          + x * iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x|
          ≤ (C + levBound E E (i + 2) i) * x := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hxnn]
        have h3 : x * |iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x|
            ≤ x * levBound E E (i + 2) i := mul_le_mul_of_nonneg_left hE2 hxnn
        nlinarith [hDx, h3, hxnn, hEnn, hCnn]
      have hkk : |2 * kappa x| ≤ 2 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        linarith [hk1]
      have t1 : |(-(2 * x / kappa x)) * (x * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x)|
          ≤ 2 * C0 * C * x := by
        rw [abs_mul]
        calc |-(2 * x / kappa x)| * |x * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x|
            ≤ (2 * C0 * x) * (C * x ^ 2) := mul_le_mul hA hDxn (abs_nonneg _) (by positivity)
          _ ≤ 2 * C0 * C * x := by
            have hxx : x ^ 3 ≤ x := by nlinarith [hx1, hxnn]
            nlinarith [hxx, hC0nn, hCnn, hxnn, mul_nonneg hC0nn hCnn]
      have t2 : |2 * kappa x * (deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x
            + x * iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x)|
          ≤ 2 * (C + levBound E E (i + 2) i) * x := by
        rw [abs_mul]
        calc |2 * kappa x| * |deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x
              + x * iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x|
            ≤ 2 * ((C + levBound E E (i + 2) i) * x) :=
              mul_le_mul hkk hinside (abs_nonneg _) (by norm_num)
          _ = 2 * (C + levBound E E (i + 2) i) * x := by ring
      have hsum := (abs_add_le
        ((-(2 * x / kappa x)) * (x * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x))
        (2 * kappa x * (deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x
          + x * iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x)))
      nlinarith [hsum, t1, t2, hxnn]

/-- **Size and vanishing order of the expansion coefficients.**  On `[0, x₁]` (`x₁ = xNear = sin(π/4)`):

* each `b i j` with `j ≤ i` is bounded;
* each `a i l` with `l ≤ i` is bounded;
* for `i ≥ 1` the `l = 0` coefficient vanishes like `x²`: `∃ C ≥ 0, ∀ x ∈ [0,x₁], |a i 0 x| ≤ C x²`.

ROUTE.  Inductions on `i`, using that `κ x = √(1-x²)` is smooth on `[0,x₁]` with `κ ≥ 1/√2` there,
so `κ` and `κ' = -x/κ` are bounded; the finite set of sup norms is handled with the induction
hypotheses (the induction must be strengthened to also bound the first derivatives of the
coefficients, since the recursion differentiates them).  The `x²`-vanishing uses
`a (i+1) 0 = 2κ · x · (a i 0)'` (the `j = 0` branch of the recursion has no second term): if
`a i 0 = x² w i` with `w i` bounded then `2κx(x² w)' = 2κx²(2 w + x w')` is `x²` times the bounded
function `2κ(2w + xw')`.  The base case is `a 1 0 = 2κ·x·(2κ)' = 2κx(-2x/κ) = -4x²` using
`(√(1-x²))' = -x/√(1-x²)` on `(-1,1)`.  (Note the statement excludes `i = 0`, where `a 0 0 = 2κ`
is not `O(x²)`.) -/
theorem aCoeff_bounds (i : ℕ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ i, ∀ x ∈ Set.Icc 0 xNear, |bCoeff i j x| ≤ C) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ i, ∀ x ∈ Set.Icc 0 xNear, |aCoeff i j x| ≤ C) ∧
        (1 ≤ i → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc 0 xNear, |aCoeff i 0 x| ≤ C * x ^ 2) := by
  obtain ⟨Mκ, hMκ⟩ := exists_jetBdd_two_kappa i
  have hM0 : 0 ≤ Mκ := hMκ.jet_nonneg
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨levBound 1 Mκ i i, levBound_nonneg (by norm_num) hM0 i i, ?_⟩
    intro j hj x hx
    have hinit : JetBdd i (fun _ : ℝ => 1) 1 := by
      simpa using (JetBdd.jet_const i (1 : ℝ))
    have h := genCoeff_jetBdd (n := i) (init := fun _ : ℝ => 1) (Minit := 1) (Mκ := Mκ)
      hinit hMκ i 0 (by omega) j hj
    rw [bCoeff_eq_genCoeff]
    simpa using h.jet_bound 0 (Nat.zero_le 0) x hx
  · refine ⟨levBound Mκ Mκ i i, levBound_nonneg hM0 hM0 i i, ?_⟩
    intro j hj x hx
    have h := genCoeff_jetBdd (n := i) (init := fun y : ℝ => 2 * kappa y) (Minit := Mκ)
      (Mκ := Mκ) hMκ hMκ i 0 (by omega) j hj
    rw [aCoeff_eq_genCoeff]
    simpa using h.jet_bound 0 (Nat.zero_le 0) x hx
  · intro hi
    have hpred : (i - 1).succ = i := Nat.succ_pred_eq_of_pos hi
    obtain ⟨C₁, hC₁0, hC₁⟩ := genCoeff_a0_deriv_le (i - 1)
    have hgen : genCoeff (fun y : ℝ => 2 * kappa y) i 0
        = fun y => 2 * kappa y * (y * deriv (genCoeff (fun y : ℝ => 2 * kappa y) (i - 1) 0) y) := by
      conv_lhs => rw [← hpred]
      exact genCoeff_succ_zero (fun y : ℝ => 2 * kappa y) (i - 1)
    refine ⟨2 * C₁, by linarith, ?_⟩
    intro x hx
    have hxnn : 0 ≤ x := hx.1
    have hk1 : |kappa x| ≤ 1 := kappa_abs_le_one hx
    have hD : |deriv (genCoeff (fun y : ℝ => 2 * kappa y) (i - 1) 0) x| ≤ C₁ * x := hC₁ x hx
    rw [aCoeff_eq_genCoeff, hgen, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hxnn]
    have h1 : x * |deriv (genCoeff (fun y : ℝ => 2 * kappa y) (i - 1) 0) x| ≤ C₁ * x ^ 2 := by
      nlinarith [hD, hC₁0, hxnn]
    have h2 : (2 : ℝ) * |kappa x| ≤ 2 * 1 := by linarith [hk1]
    calc (2 : ℝ) * |kappa x| * (x * |deriv (genCoeff (fun y : ℝ => 2 * kappa y) (i - 1) 0) x|)
        ≤ 2 * 1 * (C₁ * x ^ 2) :=
          mul_le_mul h2 h1 (by positivity) (by norm_num)
      _ = (2 * C₁) * x ^ 2 := by ring

end Work.FTS.H2.DivQ
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgB_step_claim =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.PhiStar.Honesty










end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgG1_sq_div_z4_Ioo =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.rgiClearing =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

/-- For `z > 0`: `z * z ^ (s - 1) = z ^ s` (`z = z ^ 1` and `Real.rpow_add`). -/
private lemma mul_rpow_sub_one {z s : ℝ} (hz : 0 < z) : z * z ^ (s - 1) = z ^ s := by
  calc z * z ^ (s - 1) = z ^ (1 : ℝ) * z ^ (s - 1) := by rw [Real.rpow_one]
    _ = z ^ ((1 : ℝ) + (s - 1)) := (Real.rpow_add hz 1 (s - 1)).symm
    _ = z ^ s := by congr 1; ring

/-- For `z > 0`: `z ^ 2 * z ^ (s - 2) = z ^ s` (`z ^ 2 = z ^ (2 : ℝ)` and `Real.rpow_add`). -/
private lemma sq_mul_rpow_sub_two {z s : ℝ} (hz : 0 < z) : z ^ 2 * z ^ (s - 2) = z ^ s := by
  calc z ^ 2 * z ^ (s - 2) = z ^ (2 : ℝ) * z ^ (s - 2) := by rw [(Real.rpow_two z).symm]
    _ = z ^ ((2 : ℝ) + (s - 2)) := (Real.rpow_add hz 2 (s - 2)).symm
    _ = z ^ s := by congr 1; ring

/-- For `z > 0` and `s + t = -1`: `z ^ 2 * z ^ (s - 1) * z ^ t = 1`.  Here
`z ^ 2 * z ^ (s - 1) = z ^ (s + 1)`, so the total exponent is `s + 1 + t = 0`.  This is the
exact cancellation behind the two `rgiF`-conjuncts, with `s = rgiSn α m` or `s = rgiSp α m`
and `t` the exponent of the corresponding integrand. -/
private lemma sq_mul_rpow_sub_one_mul {z s t : ℝ} (hz : 0 < z) (hst : s + t = -1) :
    z ^ 2 * z ^ (s - 1) * z ^ t = 1 := by
  have h2 : z ^ 2 * z ^ (s - 1) = z ^ (s + 1) := by
    have h := sq_mul_rpow_sub_two (z := z) (s := s + 1) hz
    have he : s + 1 - 2 = s - 1 := by ring
    rwa [he] at h
  have h3 : z ^ (s + 1) * z ^ t = 1 := by
    have he : s + 1 + t = 0 := by linarith only [hst]
    calc z ^ (s + 1) * z ^ t = z ^ ((s + 1) + t) := (Real.rpow_add hz (s + 1) t).symm
      _ = z ^ (0 : ℝ) := by rw [he]
      _ = 1 := Real.rpow_zero z
  rw [h2, h3]

theorem rgiClearing (α : ℝ) (m : ℕ) (c : ℝ → ℝ) :
    (∀ z : ℝ, 0 < z → z * z ^ (Work.FTS.PhiStar.Series.rgiSn α m - 1)
        = z ^ (Work.FTS.PhiStar.Series.rgiSn α m)) ∧
    (∀ z : ℝ, 0 < z → z ^ 2 * z ^ (Work.FTS.PhiStar.Series.rgiSn α m - 2)
        = z ^ (Work.FTS.PhiStar.Series.rgiSn α m)) ∧
    (∀ z : ℝ, 0 < z → z * z ^ (Work.FTS.PhiStar.Series.rgiSp α m - 1)
        = z ^ (Work.FTS.PhiStar.Series.rgiSp α m)) ∧
    (∀ z : ℝ, 0 < z → z ^ 2 * z ^ (Work.FTS.PhiStar.Series.rgiSp α m - 2)
        = z ^ (Work.FTS.PhiStar.Series.rgiSp α m)) ∧
    (∀ z : ℝ, 0 < z → z ^ 2 * z ^ (Work.FTS.PhiStar.Series.rgiSn α m - 1)
        * Work.FTS.PhiStar.Series.rgiF1 α m c z = c z) ∧
    (∀ z : ℝ, 0 < z → z ^ 2 * z ^ (Work.FTS.PhiStar.Series.rgiSp α m - 1)
        * Work.FTS.PhiStar.Series.rgiF2 α m c z = c z) := by
  have hSn : ∀ z : ℝ, 0 < z → z ^ 2 * z ^ (rgiSn α m - 1)
      * z ^ ((2 * (m : ℝ) + 5) / α - 1) = 1 := by
    intro z hz
    have hst : rgiSn α m + ((2 * (m : ℝ) + 5) / α - 1) = -1 := by
      simp only [rgiSn]; ring
    exact sq_mul_rpow_sub_one_mul hz hst
  have hSp : ∀ z : ℝ, 0 < z → z ^ 2 * z ^ (rgiSp α m - 1)
      * z ^ (-(2 * (m : ℝ) / α) - 1) = 1 := by
    intro z hz
    have hst : rgiSp α m + (-(2 * (m : ℝ) / α) - 1) = -1 := by
      simp only [rgiSp]; ring
    exact sq_mul_rpow_sub_one_mul hz hst
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz; exact mul_rpow_sub_one hz
  · intro z hz; exact sq_mul_rpow_sub_two hz
  · intro z hz; exact mul_rpow_sub_one hz
  · intro z hz; exact sq_mul_rpow_sub_two hz
  · intro z hz
    simp only [rgiF1]
    calc z ^ 2 * z ^ (rgiSn α m - 1) * (c z * z ^ ((2 * (m : ℝ) + 5) / α - 1))
        = c z * (z ^ 2 * z ^ (rgiSn α m - 1) * z ^ ((2 * (m : ℝ) + 5) / α - 1)) := by
          ring
      _ = c z * 1 := by rw [hSn z hz]
      _ = c z := by ring
  · intro z hz
    simp only [rgiF2]
    calc z ^ 2 * z ^ (rgiSp α m - 1) * (c z * z ^ (-(2 * (m : ℝ) / α) - 1))
        = c z * (z ^ 2 * z ^ (rgiSp α m - 1) * z ^ (-(2 * (m : ℝ) / α) - 1)) := by
          ring
      _ = c z * 1 := by rw [hSp z hz]
      _ = c z := by ring

end Work.FTS.PhiStar.Series.Deleg
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.rgiIndicial =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

theorem rgiIndicial (α : ℝ) (hα : 0 < α) (m : ℕ) :
    (-α ^ 2 * Work.FTS.PhiStar.Series.rgiSn α m * (Work.FTS.PhiStar.Series.rgiSn α m - 1)
        - α * (5 + α) * Work.FTS.PhiStar.Series.rgiSn α m
        + Work.FTS.PhiStar.Radial.lamR m = 0) ∧
    (-α ^ 2 * Work.FTS.PhiStar.Series.rgiSp α m * (Work.FTS.PhiStar.Series.rgiSp α m - 1)
        - α * (5 + α) * Work.FTS.PhiStar.Series.rgiSp α m
        + Work.FTS.PhiStar.Radial.lamR m = 0) ∧
    (α ^ 2 * Work.FTS.PhiStar.Series.rgiK α m
        * (Work.FTS.PhiStar.Series.rgiSp α m - Work.FTS.PhiStar.Series.rgiSn α m) = 1) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have h4m : (4 * (m : ℝ) + 5) ≠ 0 := by positivity
  -- the indicial exponents satisfy `s⁺ - s⁻ = (4m+5)/α`
  have hsp_sub : Work.FTS.PhiStar.Series.rgiSp α m - Work.FTS.PhiStar.Series.rgiSn α m
      = (4 * (m : ℝ) + 5) / α := by
    simp only [Work.FTS.PhiStar.Series.rgiSp, Work.FTS.PhiStar.Series.rgiSn]
    field_simp
    ring
  refine ⟨?_, ?_, ?_⟩
  · -- `s⁻` solves the indicial equation `-α²s(s-1) - α(5+α)s + λ_m = 0`
    simp only [Work.FTS.PhiStar.Series.rgiSn, Work.FTS.PhiStar.Radial.lamR]
    field_simp
    ring
  · simp only [Work.FTS.PhiStar.Series.rgiSp, Work.FTS.PhiStar.Radial.lamR]
    field_simp
    ring
  · -- the Wronskian normalisation: `α²·K·(s⁺-s⁻) = 1`
    rw [hsp_sub]
    simp only [Work.FTS.PhiStar.Series.rgiK]
    field_simp

end Work.FTS.PhiStar.Series.Deleg
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.EneAux.eFamOdeDerivAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.Series.EneAux

set_option autoImplicit false



end Work.FTS.PhiStar.Series.EneAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.eFamEneAux =====
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

/-! ## The `θ`-form of the Gegenbauer equation -/

/-- **The Sturm–Liouville form of the Gegenbauer equation.**  If `q` solves the Gegenbauer
equation of index `n` then `f = cos θ · q(sin θ)` satisfies
`(cos θ · f')' = (1/cos θ - (n+1)(n+2) cos θ) · f` wherever `cos θ ≠ 0`. -/
lemma ode_of_gC {q : ℝ → ℝ} {n : ℕ} (hq : ContDiff ℝ 3 q)
    (hode : ∀ x : ℝ, (1 - x^2) * deriv (deriv q) x - 4 * x * deriv q x
      + (n:ℝ) * ((n:ℝ)+3) * q x = 0)
    (θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    deriv (fun θ' => Real.cos θ' * deriv (fun θ' : ℝ => Real.cos θ' * q (Real.sin θ')) θ') θ
      = (1 / Real.cos θ - (((n:ℝ)+1) * ((n:ℝ)+2)) * Real.cos θ)
          * (Real.cos θ * q (Real.sin θ)) := by
  have hdiffq : Differentiable ℝ q := hq.differentiable (by norm_num)
  have hddiffq : Differentiable ℝ (deriv q) :=
    (ContDiff.deriv' (n := 2) hq).differentiable (by norm_num)
  have hfun : (fun θ' => Real.cos θ' * deriv (fun θ' : ℝ => Real.cos θ' * q (Real.sin θ')) θ')
      = fun θ' => Real.cos θ' ^ 3 * deriv q (Real.sin θ')
          - Real.cos θ' * Real.sin θ' * q (Real.sin θ') := by
    funext θ'
    rw [deriv_cos_comp_sin q hq]
    ring
  rw [hfun]
  have hcos : HasDerivAt Real.cos (-Real.sin θ) θ := Real.hasDerivAt_cos θ
  have hsin : HasDerivAt Real.sin (Real.cos θ) θ := Real.hasDerivAt_sin θ
  have hqs : HasDerivAt (fun θ' : ℝ => q (Real.sin θ')) (deriv q (Real.sin θ) * Real.cos θ) θ :=
    ((hdiffq.differentiableAt).hasDerivAt).comp θ hsin
  have hdqs : HasDerivAt (fun θ' : ℝ => deriv q (Real.sin θ'))
      (deriv (deriv q) (Real.sin θ) * Real.cos θ) θ :=
    ((hddiffq.differentiableAt).hasDerivAt).comp θ hsin
  have hA : HasDerivAt (fun θ' => Real.cos θ' * Real.sin θ' * q (Real.sin θ'))
      ((-Real.sin θ * Real.sin θ + Real.cos θ * Real.cos θ) * q (Real.sin θ)
        + (Real.cos θ * Real.sin θ) * (deriv q (Real.sin θ) * Real.cos θ)) θ :=
    (hcos.mul hsin).mul hqs
  have hB : HasDerivAt (fun θ' => Real.cos θ' ^ 3 * deriv q (Real.sin θ'))
      ((3 * Real.cos θ ^ 2 * (-Real.sin θ)) * deriv q (Real.sin θ)
        + Real.cos θ ^ 3 * (deriv (deriv q) (Real.sin θ) * Real.cos θ)) θ :=
    (hcos.pow 3).mul hdqs
  have htot : HasDerivAt (fun θ' => Real.cos θ' ^ 3 * deriv q (Real.sin θ')
        - Real.cos θ' * Real.sin θ' * q (Real.sin θ')) _ θ := hB.sub hA
  rw [htot.deriv]
  have ho := hode (Real.sin θ)
  have hs' : Real.sin θ ^ 2 + Real.cos θ ^ 2 - 1 = 0 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  field_simp
  linear_combination (Real.cos θ^2) * ho
    + (q (Real.sin θ) + Real.cos θ^2 * deriv (deriv q) (Real.sin θ)) * hs'

/-- The `θ`-form of the Gegenbauer equation for `eFam m`. -/
lemma eFam_ode (m : ℕ) (θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    deriv (fun θ' => Real.cos θ' * deriv (eFam m) θ') θ
      = (1 / Real.cos θ - eM m * Real.cos θ) * eFam m θ := by
  have h := ode_of_gC (q := gC (2 * m + 1)) (n := 2 * m + 1) (contDiff_gC (2 * m + 1))
    (fun x => (gC_ode (2 * m + 1)).2 x) θ hθ
  have harith : ((((2 * m + 1 : ℕ) : ℝ) + 1) * (((2 * m + 1 : ℕ) : ℝ) + 2)) = eM m := by
    unfold eM; push_cast; ring
  rw [harith] at h
  exact h

/-- At `θ = 0` the `cos` prefactor contributes nothing to the derivative, so
`(eFam m)'(0) = (gC (2m+1))'(0)`. -/
lemma deriv_eFam_zero (m : ℕ) : deriv (eFam m) 0 = deriv (gC (2 * m + 1)) 0 := by
  change deriv (Real.cos * fun θ : ℝ => gC (2 * m + 1) (Real.sin θ)) 0 = _
  have hB : HasDerivAt (gC (2 * m + 1)) (deriv (gC (2 * m + 1)) (Real.sin 0)) (Real.sin 0) :=
    (((contDiff_gC (2 * m + 1)).differentiable (by norm_num)).differentiableAt).hasDerivAt
  have hcomp : HasDerivAt (fun θ : ℝ => gC (2 * m + 1) (Real.sin θ))
      (deriv (gC (2 * m + 1)) (Real.sin 0) * Real.cos 0) 0 :=
    hB.comp 0 (Real.hasDerivAt_sin 0)
  have h := ((Real.hasDerivAt_cos 0).mul hcomp).deriv
  simpa using h

/-- The derivative of `eFam m` is differentiable everywhere. -/
lemma differentiableAt_deriv_eFam (m : ℕ) (θ : ℝ) :
    DifferentiableAt ℝ (deriv (eFam m)) θ := by
  have hq : Differentiable ℝ (gC (2 * m + 1)) :=
    (contDiff_gC (2 * m + 1)).differentiable (by norm_num)
  have hdq : Differentiable ℝ (deriv (gC (2 * m + 1))) :=
    ((ContDiff.deriv' (n := 2) (contDiff_gC (2 * m + 1))).differentiable (by norm_num))
  have hform : deriv (eFam m)
      = fun θ : ℝ => -Real.sin θ * gC (2 * m + 1) (Real.sin θ)
          + Real.cos θ ^ 2 * deriv (gC (2 * m + 1)) (Real.sin θ) := by
    change deriv (fun θ : ℝ => Real.cos θ * gC (2 * m + 1) (Real.sin θ)) = _
    exact deriv_cos_comp_sin (gC (2 * m + 1)) (contDiff_gC (2 * m + 1))
  rw [hform]
  exact (((Real.differentiableAt_sin).neg).mul
      (hq.differentiableAt.comp θ (Real.differentiableAt_sin))).add
    ((Real.differentiableAt_cos.pow 2).mul
      (hdq.differentiableAt.comp θ (Real.differentiableAt_sin)))

/-- The second derivative of `eFam m`, in reduced (first-order) form. -/
lemma eFam_deriv2_eq (m : ℕ) (θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    deriv (deriv (eFam m)) θ
      = Real.tan θ * deriv (eFam m) θ + (1 / (Real.cos θ)^2 - eM m) * eFam m θ := by
  have hmul : deriv (fun θ' => Real.cos θ' * deriv (eFam m) θ') θ
      = deriv Real.cos θ * deriv (eFam m) θ + Real.cos θ * deriv (deriv (eFam m)) θ :=
    deriv_mul Real.differentiableAt_cos (differentiableAt_deriv_eFam m θ)
  rw [eFam_ode m θ hθ, Real.deriv_cos] at hmul
  have h2 : Real.cos θ * deriv (deriv (eFam m)) θ
      = Real.cos θ * (Real.tan θ * deriv (eFam m) θ
          + (1 / (Real.cos θ)^2 - eM m) * eFam m θ) := by
    have h3 : Real.cos θ * (Real.tan θ * deriv (eFam m) θ
          + (1 / (Real.cos θ)^2 - eM m) * eFam m θ)
        = (1 / Real.cos θ - eM m * Real.cos θ) * eFam m θ
          + Real.sin θ * deriv (eFam m) θ := by
      rw [Real.tan_eq_sin_div_cos]; field_simp; ring
    rw [h3, hmul]; ring
  exact mul_left_cancel₀ hθ h2

/-! ## The energy `eEne` -/

/-- `eEne m 0 = (eFam m)'(0)²`. -/
lemma eEne_at_zero (m : ℕ) : eEne m 0 = (deriv (eFam m) 0)^2 := by
  unfold eEne
  rw [eFam_zero m]
  simp

/-- `eEne m (π/2) = 0`. -/
lemma eEne_at_pi_half (m : ℕ) : eEne m (Real.pi / 2) = 0 := by
  unfold eEne
  rw [eFam_pi_half m]
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- Differentiability of the energy where `cos θ ≠ 0`. -/
lemma differentiableAt_eEne (m : ℕ) {θ : ℝ} (hθ : Real.cos θ ≠ 0) :
    DifferentiableAt ℝ (eEne m) θ := by
  have hf : DifferentiableAt ℝ (eFam m) θ := (differentiable_eFam m).differentiableAt
  have hg : DifferentiableAt ℝ (deriv (eFam m)) θ := differentiableAt_deriv_eFam m θ
  have hcos : DifferentiableAt ℝ Real.cos θ := Real.differentiableAt_cos
  have hsin : DifferentiableAt ℝ Real.sin θ := Real.differentiableAt_sin
  have hinv : DifferentiableAt ℝ (fun x : ℝ => 1 / (2 * Real.cos x)) θ := by
    have h2 : DifferentiableAt ℝ (fun x : ℝ => 2 * Real.cos x) θ :=
      (differentiableAt_const 2).mul hcos
    have h3 := h2.inv (by simpa using hθ)
    have heq : (fun x : ℝ => 1 / (2 * Real.cos x)) = fun x : ℝ => (2 * Real.cos x)⁻¹ := by
      funext x; rw [div_eq_mul_inv, one_mul]
    rw [heq]; exact h3
  unfold eEne
  exact ((hcos.mul (hg.pow 2)).sub ((hsin.mul hf).mul hg)).add
    ((((differentiableAt_const (eM m)).mul hcos).sub hinv).mul (hf.pow 2))

/-- **The derivative of the energy.** `eEne m' = -(3 sin θ/(2 cos²θ)) f²`. -/
lemma eEne_deriv (m : ℕ) (θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    deriv (eEne m) θ
      = -(3 * Real.sin θ / (2 * (Real.cos θ)^2)) * (eFam m θ)^2 := by
  have hf : HasDerivAt (eFam m) (deriv (eFam m) θ) θ :=
    ((differentiable_eFam m).differentiableAt).hasDerivAt
  have hg : HasDerivAt (deriv (eFam m)) (deriv (deriv (eFam m)) θ) θ :=
    (differentiableAt_deriv_eFam m θ).hasDerivAt
  have hcos : HasDerivAt Real.cos (-Real.sin θ) θ := Real.hasDerivAt_cos θ
  have hsin : HasDerivAt Real.sin (Real.cos θ) θ := Real.hasDerivAt_sin θ
  have hcinv : HasDerivAt (fun x : ℝ => (Real.cos x)⁻¹) (- -Real.sin θ / Real.cos θ ^ 2) θ :=
    hcos.inv hθ
  have hhalf : HasDerivAt (fun x : ℝ => (1/2:ℝ) * (Real.cos x)⁻¹)
      ((1/2:ℝ) * (- -Real.sin θ / Real.cos θ ^ 2)) θ := hcinv.const_mul _
  have hpoint : ∀ x : ℝ, 1 / (2 * Real.cos x) = (1/2:ℝ) * (Real.cos x)⁻¹ := by
    intro x
    have key : (2 * Real.cos x)⁻¹ = (1/2:ℝ) * (Real.cos x)⁻¹ := by
      rw [show (1/2:ℝ) = (2:ℝ)⁻¹ from by norm_num, mul_inv_rev, mul_comm]
    rwa [div_eq_mul_inv, one_mul]
  have hfun : (fun x : ℝ => 1 / (2 * Real.cos x)) =ᶠ[𝓝 θ]
      fun x => (1/2:ℝ) * (Real.cos x)⁻¹ := Filter.Eventually.of_forall hpoint
  have hinv : HasDerivAt (fun x : ℝ => 1 / (2 * Real.cos x))
      (Real.sin θ / (2 * Real.cos θ^2)) θ := by
    have h := hhalf.congr_of_eventuallyEq hfun
    have hval : (1/2:ℝ) * (- -Real.sin θ / Real.cos θ ^ 2)
        = Real.sin θ / (2 * Real.cos θ ^ 2) := by
      field_simp
    rwa [hval] at h
  have hE : HasDerivAt (fun θ' => Real.cos θ' * deriv (eFam m) θ' ^ 2
        - Real.sin θ' * eFam m θ' * deriv (eFam m) θ'
        + (eM m * Real.cos θ' - 1 / (2 * Real.cos θ')) * eFam m θ' ^ 2) _ θ :=
    (((hcos.mul (hg.pow 2)).sub ((hsin.mul hf).mul hg)).add
      (((hcos.const_mul (eM m)).sub hinv).mul (hf.pow 2)))
  change deriv (fun θ' => Real.cos θ' * deriv (eFam m) θ' ^ 2
        - Real.sin θ' * eFam m θ' * deriv (eFam m) θ'
        + (eM m * Real.cos θ' - 1 / (2 * Real.cos θ')) * eFam m θ' ^ 2) θ = _
  rw [hE.deriv]
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, show (2:ℕ) - 1 = 1 from rfl, pow_one]
  rw [eFam_deriv2_eq m θ hθ, Real.tan_eq_sin_div_cos]
  have hs' : Real.sin θ ^ 2 + Real.cos θ ^ 2 - 1 = 0 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  field_simp
  ring_nf
  linear_combination
    (-2 * deriv (eFam m) θ * Real.cos θ * eFam m θ) * hs'

/-- The energy is non-increasing on `(0, π/2)`. -/
lemma eEne_deriv_nonpos (m : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi/2)) :
    deriv (eEne m) x ≤ 0 := by
  have hcos : Real.cos x ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩)
  rw [eEne_deriv m x hcos]
  have h1 : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have h3 : 0 ≤ 3 * Real.sin x / (2 * (Real.cos x)^2) :=
    div_nonneg (by linarith) (by positivity)
  nlinarith [sq_nonneg (eFam m x)]

/-- **Energy monotonicity**: `eEne m θ ≤ eEne m 0` for `θ ∈ [0, π/2]`. -/
lemma eEne_le_eEne_zero (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Icc (0:ℝ) (Real.pi/2)) :
    eEne m θ ≤ eEne m 0 := by
  rcases lt_or_eq_of_le hθ.2 with hlt | heq
  · rcases eq_or_lt_of_le hθ.1 with h0 | hpos
    · rw [h0]
    · have hcos_ne : ∀ x ∈ Set.Icc (0:ℝ) θ, Real.cos x ≠ 0 := by
        intro x hx
        exact ne_of_gt (Real.cos_pos_of_mem_Ioo
          ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, hlt]⟩)
      have hcont : ContinuousOn (eEne m) (Set.Icc 0 θ) := by
        have hgd : Differentiable ℝ (deriv (eFam m)) :=
          fun x => differentiableAt_deriv_eFam m x
        have hg : ContinuousOn (fun x : ℝ => deriv (eFam m) x) (Set.Icc 0 θ) :=
          hgd.continuous.continuousOn
        have hf : ContinuousOn (fun x : ℝ => eFam m x) (Set.Icc 0 θ) :=
          (continuous_eFam m).continuousOn
        have hinv : ContinuousOn (fun x : ℝ => 1 / (2 * Real.cos x)) (Set.Icc 0 θ) := by
          refine ContinuousOn.div continuousOn_const ?_ ?_
          · exact (continuous_const.mul Real.continuous_cos).continuousOn
          · intro x hx; exact mul_ne_zero two_ne_zero (hcos_ne x hx)
        change ContinuousOn (fun x : ℝ => Real.cos x * deriv (eFam m) x ^ 2
            - Real.sin x * eFam m x * deriv (eFam m) x
            + (eM m * Real.cos x - 1 / (2 * Real.cos x)) * eFam m x ^ 2) (Set.Icc 0 θ)
        exact (((Real.continuous_cos.continuousOn.mul (hg.pow 2)).sub
              (((Real.continuous_sin.continuousOn).mul hf).mul hg)).add
            (((continuous_const.mul Real.continuous_cos).continuousOn.sub hinv).mul (hf.pow 2)))
      have hdiff : DifferentiableOn ℝ (eEne m) (Set.Ioo 0 θ) := fun x hx =>
        (differentiableAt_eEne m (hcos_ne x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)).differentiableWithinAt
      obtain ⟨c, hc, hcd⟩ :=
        exists_deriv_eq_slope (f := eEne m) (a := 0) (b := θ) hpos hcont hdiff
      have hle : deriv (eEne m) c ≤ 0 :=
        eEne_deriv_nonpos m ⟨hc.1, by linarith [hc.2, hlt]⟩
      have hkey : eEne m θ - eEne m 0 = θ * deriv (eEne m) c := by
        rw [hcd, sub_zero]; field_simp
      nlinarith [hkey, hle, hθ.1]
  · rw [heq, eEne_at_pi_half, eEne_at_zero]; positivity

/-- At a critical point of `f = eFam m`, `eEne m` is the height of `f` times the bracket. -/
lemma eEne_at_critical (m : ℕ) {θ : ℝ} (hθ : deriv (eFam m) θ = 0) :
    eEne m θ = (eM m * Real.cos θ - 1 / (2 * Real.cos θ)) * (eFam m θ)^2 := by
  unfold eEne
  rw [hθ]; ring
end Work.FTS.PhiStar.Series
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.exists_eFam_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

/-! ## Auxiliary bounds on the compact interval `[-1,1]` -/

/-- A continuous real function on `[-1,1]` is bounded there in absolute value. -/
lemma exists_abs_le_on_Icc {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (-1) 1)) :
    ∃ C : ℝ, ∀ x ∈ Set.Icc (-1 : ℝ) 1, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := f) hf
  exact ⟨C, fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩

/-- The value and the derivative of the Gegenbauer polynomial `gC (2m+1)` are both bounded on
the interval `[-1,1]` (the two constants `M`, `D` are nonnegative). -/
lemma exists_gC_bound_and_deriv_bound (m : ℕ) : ∃ M D : ℝ, 0 ≤ M ∧ 0 ≤ D ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) x| ≤ M) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) x| ≤ D) := by
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1))).continuous).continuousOn
  obtain ⟨D, hD⟩ := exists_abs_le_on_Icc
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1))).continuous_deriv
      (by norm_num)).continuousOn
  exact ⟨M, D, le_trans (abs_nonneg _) (hM 0 (by norm_num)),
    le_trans (abs_nonneg _) (hD 0 (by norm_num)), hM, hD⟩

/-- Mean value bound for the odd Gegenbauer polynomial: for `θ ∈ Iθ`,
`|gC (2m+1) (sin θ)| ≤ D · sin θ`, where `D` bounds `|deriv (gC (2m+1))|` on `[-1,1]`. -/
lemma abs_gC_sin_le (m : ℕ) {D : ℝ}
    (hD : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) x| ≤ D) :
    ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)| ≤ D * Real.sin θ := by
  intro θ hθ
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) (s := Set.Icc (0 : ℝ) 1) (C := D)
    (x := (0 : ℝ)) (y := Real.sin θ)
    (fun x _ => ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).differentiable
      (by norm_num)).differentiableAt)
    (fun x hx => hD x ⟨by linarith [hx.1], hx.2⟩)
    (convex_Icc (0 : ℝ) 1) ⟨le_rfl, zero_le_one⟩ ⟨hsin0, hsin1⟩
  rw [gC_odd_zero m] at h
  simpa [Real.norm_eq_abs, abs_of_nonneg hsin0] using h

/-! ## The derivative of `eFam m · cos` -/

/-- Explicit form of the derivative of `θ ↦ eFam m θ · cos θ`: since
`eFam m t · cos t = (1 - sin²t) · gC (2m+1) (sin t)` (as `cos² = 1 - sin²`), the product and
chain rules give the displayed combination of `gC (2m+1)` and its derivative at `sin θ`. -/
lemma deriv_eFam_mul_cos (m : ℕ) (θ : ℝ) :
    deriv (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m t * Real.cos t) θ
      = (0 - 2 * Real.sin θ * Real.cos θ)
          * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)
        + (1 - Real.sin θ ^ 2)
          * (deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) (Real.sin θ) * Real.cos θ) := by
  have hgc : HasDerivAt (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1))
      (deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) (Real.sin θ)) (Real.sin θ) :=
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).differentiable
      (by norm_num)).differentiableAt).hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin t))
      (deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) (Real.sin θ) * Real.cos θ) θ :=
    hgc.comp θ (Real.hasDerivAt_sin θ)
  have h1 : HasDerivAt (fun t : ℝ => 1 - Real.sin t ^ 2)
      (0 - 2 * Real.sin θ * Real.cos θ) θ := by
    have hs : HasDerivAt (fun t : ℝ => Real.sin t ^ 2)
        (2 * Real.sin θ ^ (2 - 1) * Real.cos θ) θ := (Real.hasDerivAt_sin θ).pow 2
    have h := (hasDerivAt_const (x := θ) (c := (1 : ℝ))).sub hs
    convert h using 1
    ring
  have hprod := h1.mul h2
  rw [show (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m t * Real.cos t)
      = fun t : ℝ => (1 - Real.sin t ^ 2)
          * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin t) from ?_]
  · exact hprod.deriv
  · funext t
    rw [Work.FTS.PhiStar.Gegenbauer.eFam]
    rw [show Real.cos t * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin t) * Real.cos t
        = Real.cos t ^ 2 * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin t) from by ring]
    rw [Real.cos_sq']

/-! ## The main bounds -/

theorem exists_eFam_bounds (m : ℕ) : ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
    (∀ θ ∈ Work.Spaces.Iθ, |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ A * Real.cos θ) ∧
    (∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| ≤ A * Real.sin θ * Real.cos θ ^ 2) ∧
    (∀ θ : ℝ,
      |deriv (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m t * Real.cos t) θ| ≤ B) := by
  obtain ⟨M, D, hMnn, hDnn, hM, hD⟩ := exists_gC_bound_and_deriv_bound m
  have hmvt := abs_gC_sin_le m hD
  refine ⟨D + 1, 2 * M + D + 1, by linarith, by linarith, ?_, ?_, ?_⟩
  · intro θ hθ
    have hcos : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hsin0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
    calc |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        = Real.cos θ * |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)| := by
          rw [Work.FTS.PhiStar.Gegenbauer.eFam, abs_mul, abs_of_nonneg hcos]
      _ ≤ Real.cos θ * (D * Real.sin θ) := mul_le_mul_of_nonneg_left (hmvt θ hθ) hcos
      _ = D * Real.cos θ * Real.sin θ := by ring
      _ ≤ D * Real.cos θ * 1 := mul_le_mul_of_nonneg_left hsin1 (mul_nonneg hDnn hcos)
      _ = D * Real.cos θ := by ring
      _ ≤ (D + 1) * Real.cos θ := mul_le_mul_of_nonneg_right (by linarith) hcos
  · intro θ hθ
    have hcos : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hsin0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    calc |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ|
        = Real.cos θ ^ 2 * |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)| := by
          rw [Work.FTS.PhiStar.Gegenbauer.eFam, abs_mul, abs_mul, abs_of_nonneg hcos]
          ring
      _ ≤ Real.cos θ ^ 2 * (D * Real.sin θ) :=
          mul_le_mul_of_nonneg_left (hmvt θ hθ) (by positivity)
      _ = (D * Real.sin θ) * Real.cos θ ^ 2 := by ring
      _ ≤ ((D + 1) * Real.sin θ) * Real.cos θ ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hsin0)
            (by positivity)
      _ = (D + 1) * Real.sin θ * Real.cos θ ^ 2 := by ring
  · intro θ
    have hsin_abs : |Real.sin θ| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
    have hcos_abs : |Real.cos θ| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
    have hsin_mem : Real.sin θ ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
    have hP : |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)| ≤ M := hM _ hsin_mem
    have hP' : |deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) (Real.sin θ)| ≤ D :=
      hD _ hsin_mem
    have hsq_abs : |1 - Real.sin θ ^ 2| ≤ 1 := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · nlinarith [sq_nonneg (Real.sin θ), Real.sin_le_one θ, Real.neg_one_le_sin θ]
      · nlinarith [sq_nonneg (Real.sin θ)]
    have hfirst : |0 - 2 * Real.sin θ * Real.cos θ| ≤ 2 := by
      have hprod : |Real.sin θ| * |Real.cos θ| ≤ 1 := by
        have h := mul_le_mul hsin_abs hcos_abs (abs_nonneg (Real.cos θ))
          (by norm_num : (0 : ℝ) ≤ 1)
        simpa using h
      have h1 : |0 - 2 * Real.sin θ * Real.cos θ| = 2 * (|Real.sin θ| * |Real.cos θ|) := by
        rw [show (0 : ℝ) - 2 * Real.sin θ * Real.cos θ = -(2 * Real.sin θ * Real.cos θ) from
            by ring,
          abs_neg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      rw [h1]
      linarith
    rw [deriv_eFam_mul_cos m θ]
    calc |(0 - 2 * Real.sin θ * Real.cos θ)
            * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)
          + (1 - Real.sin θ ^ 2)
            * (deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) (Real.sin θ) * Real.cos θ)|
        ≤ |(0 - 2 * Real.sin θ * Real.cos θ)
            * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)|
          + |(1 - Real.sin θ ^ 2)
            * (deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) (Real.sin θ) * Real.cos θ)| :=
          abs_add_le _ _
      _ ≤ 2 * M + 1 * (D * 1) := by
          rw [abs_mul, abs_mul, abs_mul]
          have hA : |0 - 2 * Real.sin θ * Real.cos θ|
              * |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)| ≤ 2 * M :=
            mul_le_mul hfirst hP (abs_nonneg _) (by norm_num)
          have hB : |1 - Real.sin θ ^ 2|
              * (|deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) (Real.sin θ)|
                * |Real.cos θ|) ≤ 1 * (D * 1) := by
            have hbd : |deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) (Real.sin θ)|
                * |Real.cos θ| ≤ D * 1 :=
              mul_le_mul hP' hcos_abs (abs_nonneg _) hDnn
            exact mul_le_mul hsq_abs hbd (by positivity) (by norm_num)
          linarith
      _ = 2 * M + D := by ring
      _ ≤ 2 * M + D + 1 := by linarith

end Work.FTS.PhiStar.Series
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.L12dens_transport_abs_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

theorem L12dens_transport_abs_le {f : ℝ → ℝ → ℝ} {Maj : ℝ → ℝ} {z : ℝ}
    (hMaj0 : ∀ r : ℝ, 0 ≤ Maj r)
    (hslot : ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, ∀ j i : ℕ, j + i ≤ 1 →
      |Work.Spaces.mixed j i f r θ| ≤ Maj r)
    (hz : 0 < z) :
    |Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Transport f) z| ≤ 6 * Maj z / z := by
  have h1z : 0 < 1 + z := by linarith
  have hM : 0 ≤ Maj z := hMaj0 z
  -- `D_θ f = sin(2θ) ∂_θ f` is the `(j,i) = (0,1)` slot of the hypothesis.
  have hD : ∀ θ : ℝ, |Work.Spaces.Dth f z θ| ≤ Maj z := fun θ => by
    have h := hslot z hz θ 0 1 (by norm_num)
    simpa [Work.Spaces.mixed, Work.Spaces.Dth] using h
  have hA : 0 ≤ 6 * Maj z := mul_nonneg (by norm_num) hM
  -- Angular domination: `K θ = 3 sinθ cos²θ ≤ 2 cos θ`, and
  -- `|Transport f z θ| = 3 |D_θ f z θ| / (1+z) ≤ 3 Maj z / (1+z) ≤ 3 Maj z`.
  have hdom : ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.K θ * |Work.Coercivity.Transport f z θ|
      ≤ (6 * Maj z) * Real.cos θ := by
    intro θ hθ
    have hc : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
    have hK : Work.Spaces.K θ ≤ 2 * Real.cos θ := by
      rw [Work.Spaces.K]
      have hs := Real.sin_le_one (2 * θ)
      have hs2 := Real.sin_two_mul θ
      nlinarith [hc, hs, hs2]
    have htr : |Work.Coercivity.Transport f z θ| ≤ 3 * Maj z / (1 + z) := by
      rw [Work.Coercivity.Transport, abs_div, abs_mul, abs_of_pos h1z,
        show |(3 : ℝ)| = 3 by norm_num]
      exact div_le_div_of_nonneg_right (by linarith [hD θ]) h1z.le
    calc Work.Spaces.K θ * |Work.Coercivity.Transport f z θ|
        ≤ (2 * Real.cos θ) * (3 * Maj z / (1 + z)) :=
          mul_le_mul hK htr (abs_nonneg _) (by linarith [hc])
      _ = (6 * Maj z / (1 + z)) * Real.cos θ := by ring
      _ ≤ (6 * Maj z) * Real.cos θ :=
          mul_le_mul_of_nonneg_right
            (div_le_self (mul_nonneg (by norm_num) hM) (by linarith)) hc
  exact AbsL12densLe (Y := Work.Coercivity.Transport f) (s := z) (A := 6 * Maj z)
    hz hA hdom

end Work.FTS.StrongEps.E5Aux2
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.Psivar0_slots_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.E5Aux2

/-! ## The model profile `δ` and its derivatives -/

/-- The model profile `δ(z,θ) = sin(2θ)/(2(1+z))` (the singular part `Theta α (Fstar α)` of
the stream function of the reference profile). -/
private noncomputable def delta (z θ : ℝ) : ℝ := Real.sin (2 * θ) / (2 * (1 + z))

lemma hasDerivAt_delta_z (θ z : ℝ) (hz : (0 : ℝ) < 1 + z) :
    HasDerivAt (fun z' : ℝ => delta z' θ) (- Real.sin (2 * θ) / (2 * (1 + z) ^ 2)) z := by
  have h2 : HasDerivAt (fun z' : ℝ => 2 * (1 + z')) 2 z := by
    simpa using ((hasDerivAt_id z).const_add 1).const_mul 2
  have h1 : HasDerivAt (fun z' : ℝ => (2 * (1 + z'))⁻¹) (-2 / (2 * (1 + z)) ^ 2) z :=
    h2.inv (by positivity)
  have h3 := h1.const_mul (Real.sin (2 * θ))
  have hfun : (fun z' : ℝ => Real.sin (2 * θ) * (2 * (1 + z'))⁻¹)
      = fun z' : ℝ => delta z' θ := by
    funext z'; simp only [delta]; ring
  rw [hfun] at h3
  have hval : Real.sin (2 * θ) * (-2 / (2 * (1 + z)) ^ 2)
      = - Real.sin (2 * θ) / (2 * (1 + z) ^ 2) := by
    field_simp
  rwa [hval] at h3

lemma hasDerivAt_delta_th (z θ : ℝ) (hz : (0 : ℝ) < 1 + z) :
    HasDerivAt (fun θ' : ℝ => delta z θ') (Real.cos (2 * θ) / (1 + z)) θ := by
  have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have h1 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h2
  have h3 := h1.div_const (2 * (1 + z))
  have hfun : (fun θ' : ℝ => Real.sin (2 * θ') / (2 * (1 + z)))
      = fun θ' : ℝ => delta z θ' := by
    funext θ'; simp only [delta]
  rw [hfun] at h3
  have hval : Real.cos (2 * θ) * 2 / (2 * (1 + z)) = Real.cos (2 * θ) / (1 + z) := by
    field_simp
  rwa [hval] at h3

/-- The totalised derivative is bounded in terms of the derivative of the subtracted
profile: quantitatively, "`deriv (f - g) x - deriv f x` is either `-deriv g x` or `0`". -/
lemma abs_deriv_sub_sub_le {f g : ℝ → ℝ} {x : ℝ} (hg : DifferentiableAt ℝ g x) :
    |deriv (f - g) x - deriv f x| ≤ |deriv g x| := by
  by_cases hf : DifferentiableAt ℝ f x
  · have hfg : DifferentiableAt ℝ (f - g) x := hf.sub hg
    rw [deriv_sub hf hg]
    have : deriv f x - deriv g x - deriv f x = -deriv g x := by ring
    rw [this, abs_neg]
  · have hnm : ¬ DifferentiableAt ℝ (f - g) x := by
      intro h
      have h' : DifferentiableAt ℝ (fun y => (f y - g y) + g y) x := h.add hg
      have heq : (fun y => (f y - g y) + g y) = f := by funext y; ring
      exact hf (heq ▸ h')
    rw [deriv_zero_of_not_differentiableAt hnm, deriv_zero_of_not_differentiableAt hf]
    simp

/-- The `pz`-form of `abs_deriv_sub_sub_le`. -/
lemma abs_pz_sub_le {F G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hG : DifferentiableAt ℝ (fun z' => G z' θ) z) :
    |Work.Spaces.pz (F - G) z θ - Work.Spaces.pz F z θ| ≤ |Work.Spaces.pz G z θ| := by
  have h := abs_deriv_sub_sub_le (f := fun z' : ℝ => F z' θ)
    (g := fun z' : ℝ => G z' θ) hG
  have key : (fun z' : ℝ => (F - G) z' θ)
      = ((fun z' : ℝ => F z' θ) - fun z' : ℝ => G z' θ) := by
    funext z'; rfl
  have h1 : Work.Spaces.pz (F - G) z θ
      = deriv ((fun z' : ℝ => F z' θ) - fun z' : ℝ => G z' θ) z := by
    simp only [Work.Spaces.pz, key]
  have h2 : Work.Spaces.pz F z θ = deriv (fun z' : ℝ => F z' θ) z := rfl
  have h3 : Work.Spaces.pz G z θ = deriv (fun z' : ℝ => G z' θ) z := rfl
  rw [h1, h2, h3]
  exact h

/-- The `pth`-form of `abs_deriv_sub_sub_le`. -/
lemma abs_pth_sub_le {F G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hG : DifferentiableAt ℝ (fun θ' => G z θ') θ) :
    |Work.Spaces.pth (F - G) z θ - Work.Spaces.pth F z θ| ≤ |Work.Spaces.pth G z θ| := by
  have h := abs_deriv_sub_sub_le (f := fun θ' : ℝ => F z θ')
    (g := fun θ' : ℝ => G z θ') hG
  have key : (fun θ' : ℝ => (F - G) z θ')
      = ((fun θ' : ℝ => F z θ') - fun θ' : ℝ => G z θ') := by
    funext θ'; rfl
  have h1 : Work.Spaces.pth (F - G) z θ
      = deriv ((fun θ' : ℝ => F z θ') - fun θ' : ℝ => G z θ') θ := by
    simp only [Work.Spaces.pth, key]
  have h2 : Work.Spaces.pth F z θ = deriv (fun θ' : ℝ => F z θ') θ := rfl
  have h3 : Work.Spaces.pth G z θ = deriv (fun θ' : ℝ => G z θ') θ := rfl
  rw [h1, h2, h3]
  exact h

/-- The `z`-error for the model profile `δ`. -/
lemma abs_pz_sub_le_delta {F : ℝ → ℝ → ℝ} {z θ : ℝ} (h1z : (0 : ℝ) < 1 + z)
    (hs2nn : 0 ≤ Real.sin (2 * θ)) :
    |Work.Spaces.pz (F - delta) z θ - Work.Spaces.pz F z θ|
      ≤ Real.sin (2 * θ) / (2 * (1 + z) ^ 2) := by
  have hG : DifferentiableAt ℝ (fun z' : ℝ => delta z' θ) z :=
    (hasDerivAt_delta_z θ z h1z).differentiableAt
  have h := abs_pz_sub_le (F := F) (G := delta) hG
  have hd : Work.Spaces.pz delta z θ = - Real.sin (2 * θ) / (2 * (1 + z) ^ 2) := by
    simp only [Work.Spaces.pz]
    exact (hasDerivAt_delta_z θ z h1z).deriv
  rw [hd] at h
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (1 + z) ^ 2), abs_neg,
    abs_of_nonneg hs2nn] at h
  exact h

/-- The `θ`-error for the model profile `δ`. -/
lemma abs_pth_sub_le_delta {F : ℝ → ℝ → ℝ} {z θ : ℝ} (h1z : (0 : ℝ) < 1 + z) :
    |Work.Spaces.pth (F - delta) z θ - Work.Spaces.pth F z θ|
      ≤ |Real.cos (2 * θ)| / (1 + z) := by
  have hG : DifferentiableAt ℝ (fun θ' : ℝ => delta z θ') θ :=
    (hasDerivAt_delta_th z θ h1z).differentiableAt
  have h := abs_pth_sub_le (F := F) (G := delta) hG
  have hd : Work.Spaces.pth delta z θ = Real.cos (2 * θ) / (1 + z) := by
    simp only [Work.Spaces.pth]
    exact (hasDerivAt_delta_th z θ h1z).deriv
  rw [hd] at h
  rwa [abs_div, abs_of_nonneg h1z.le] at h

/-! ## The exact algebraic relation between the slots at `F - δ` and at `F` -/

lemma Rop_sub_eq (F G : ℝ → ℝ → ℝ) (α z θ : ℝ) :
    Work.Construction.Rop α (F - G) z θ = Work.Construction.Rop α F z θ
      + (-(2 * Real.sin θ * G z θ)
          + α * Real.sin θ * z * (Work.Spaces.pz (F - G) z θ - Work.Spaces.pz F z θ)
          + Real.cos θ * (Work.Spaces.pth (F - G) z θ - Work.Spaces.pth F z θ))
        / Real.cos θ := by
  simp only [Work.Construction.Rop, Pi.sub_apply]
  rw [← add_div]
  congr 1
  ring

lemma Uop_sub_eq (F G : ℝ → ℝ → ℝ) (α z θ : ℝ) :
    Work.Construction.Uop α (F - G) z θ = Work.Construction.Uop α F z θ
      + (3 * G z θ - α * z * (Work.Spaces.pz (F - G) z θ - Work.Spaces.pz F z θ)) := by
  simp only [Work.Construction.Uop, Pi.sub_apply]
  ring

lemma Vop_sub_eq (F G : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Construction.Vop (F - G) z θ = Work.Construction.Vop F z θ
      + ((Work.Spaces.pth (F - G) z θ - Work.Spaces.pth F z θ) + Real.tan θ * G z θ) := by
  simp only [Work.Construction.Vop, Pi.sub_apply]
  ring

/-- `z/(1+z)² ≤ 1/4` for `z > 0`. -/
lemma div_sq_le_quarter {z : ℝ} (hz : 0 < z) : z / (1 + z) ^ 2 ≤ 1 / 4 := by
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  nlinarith [sq_nonneg (1 - z)]

/-! ## The three slot bounds -/

lemma Rop_delta_bd {α z θ : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hz : 0 < z)
    (hθ1 : 0 < θ) (hθ2 : θ < π / 2) (F : ℝ → ℝ → ℝ) :
    |Work.Construction.Rop α (F - delta) z θ| ≤ |Work.Construction.Rop α F z θ| + 10 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hcosne : Real.cos θ ≠ 0 := ne_of_gt hcos
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ1 (by linarith [hθ2, Real.pi_pos])
  have hs2nn : 0 ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]
    exact mul_nonneg (mul_nonneg (by norm_num) hsin.le) hcos.le
  have hez := abs_pz_sub_le_delta (F := F) h1z hs2nn
  have heth := abs_pth_sub_le_delta (F := F) (z := z) (θ := θ) h1z
  rw [Rop_sub_eq (F := F) (G := delta)]
  set ez : ℝ := Work.Spaces.pz (F - delta) z θ - Work.Spaces.pz F z θ with hezdef
  set eth : ℝ := Work.Spaces.pth (F - delta) z θ - Work.Spaces.pth F z θ with hethdef
  have hez' : |ez| ≤ Real.sin (2 * θ) / (2 * (1 + z) ^ 2) := by rw [hezdef]; exact hez
  have heth' : |eth| ≤ |Real.cos (2 * θ)| / (1 + z) := by rw [hethdef]; exact heth
  rw [show delta z θ = Real.sin (2 * θ) / (2 * (1 + z)) from rfl]
  have hE : |(-(2 * Real.sin θ * (Real.sin (2 * θ) / (2 * (1 + z))))
        + α * Real.sin θ * z * ez + Real.cos θ * eth) / Real.cos θ| ≤ 3 + α / 4 := by
    have hN : |-(2 * Real.sin θ * (Real.sin (2 * θ) / (2 * (1 + z))))
          + α * Real.sin θ * z * ez + Real.cos θ * eth|
        ≤ 2 * Real.sin θ * |Real.sin (2 * θ) / (2 * (1 + z))|
          + α * Real.sin θ * z * |ez| + Real.cos θ * |eth| := by
      have h2 : |-(2 * Real.sin θ * (Real.sin (2 * θ) / (2 * (1 + z))))
            + α * Real.sin θ * z * ez|
          ≤ |-(2 * Real.sin θ * (Real.sin (2 * θ) / (2 * (1 + z))))|
            + |α * Real.sin θ * z * ez| := abs_add_le _ _
      have h3 : |-(2 * Real.sin θ * (Real.sin (2 * θ) / (2 * (1 + z))))
            + α * Real.sin θ * z * ez + Real.cos θ * eth|
          ≤ |-(2 * Real.sin θ * (Real.sin (2 * θ) / (2 * (1 + z))))
              + α * Real.sin θ * z * ez| + |Real.cos θ * eth| := abs_add_le _ _
      have h4 : |-(2 * Real.sin θ * (Real.sin (2 * θ) / (2 * (1 + z))))|
          = 2 * Real.sin θ * |Real.sin (2 * θ) / (2 * (1 + z))| := by
        rw [abs_neg, abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hsin.le]
      have h5 : |α * Real.sin θ * z * ez| = α * Real.sin θ * z * |ez| := by
        rw [abs_mul, abs_mul, abs_mul,
          abs_of_nonneg hα0, abs_of_nonneg hsin.le, abs_of_nonneg hz.le]
      have h6 : |Real.cos θ * eth| = Real.cos θ * |eth| := by
        rw [abs_mul, abs_of_nonneg hcos.le]
      linarith
    have hstep : |(-(2 * Real.sin θ * (Real.sin (2 * θ) / (2 * (1 + z))))
          + α * Real.sin θ * z * ez + Real.cos θ * eth) / Real.cos θ|
        ≤ (2 * Real.sin θ * |Real.sin (2 * θ) / (2 * (1 + z))|
            + α * Real.sin θ * z * |ez| + Real.cos θ * |eth|) / Real.cos θ := by
      rw [abs_div, abs_of_nonneg hcos.le]
      exact div_le_div_of_nonneg_right hN hcos.le
    have hsplit : (2 * Real.sin θ * |Real.sin (2 * θ) / (2 * (1 + z))|
          + α * Real.sin θ * z * |ez| + Real.cos θ * |eth|) / Real.cos θ
        = 2 * Real.sin θ * |Real.sin (2 * θ) / (2 * (1 + z))| / Real.cos θ
          + α * Real.sin θ * z * |ez| / Real.cos θ + |eth| := by
      field_simp
    rw [hsplit] at hstep
    have hA : 2 * Real.sin θ * |Real.sin (2 * θ) / (2 * (1 + z))| / Real.cos θ ≤ 2 := by
      have hkey : 2 * Real.sin θ * |Real.sin (2 * θ) / (2 * (1 + z))| / Real.cos θ
          = 2 * Real.sin θ ^ 2 / (1 + z) := by
        rw [abs_of_nonneg (div_nonneg hs2nn (by positivity)), Real.sin_two_mul]
        field_simp
      rw [hkey, div_le_iff₀ h1z]
      nlinarith [Real.sin_sq_le_one θ, hz]
    have hB : α * Real.sin θ * z * |ez| / Real.cos θ ≤ α / 4 := by
      have hkey : α * Real.sin θ * z * |ez| / Real.cos θ
          ≤ α * Real.sin θ * z * (Real.sin (2 * θ) / (2 * (1 + z) ^ 2)) / Real.cos θ := by
        apply div_le_div_of_nonneg_right _ hcos.le
        exact mul_le_mul_of_nonneg_left hez' (by positivity)
      refine le_trans hkey ?_
      have hkey2 : α * Real.sin θ * z * (Real.sin (2 * θ) / (2 * (1 + z) ^ 2)) / Real.cos θ
          = α * (z / (1 + z) ^ 2) * Real.sin θ ^ 2 := by
        rw [Real.sin_two_mul]
        field_simp
      rw [hkey2]
      have h1 : α * (z / (1 + z) ^ 2) ≤ α * (1 / 4) :=
        mul_le_mul_of_nonneg_left (div_sq_le_quarter hz) hα0
      have h2 : (0 : ℝ) ≤ Real.sin θ ^ 2 := sq_nonneg _
      have h3 : (0 : ℝ) ≤ α * (1 / 4) := by positivity
      have h4 := mul_le_mul h1 (Real.sin_sq_le_one θ) h2 h3
      linarith
    have hC : |eth| ≤ 1 := by
      have h1 : |Real.cos (2 * θ)| / (1 + z) ≤ 1 / (1 + z) :=
        div_le_div_of_nonneg_right (Real.abs_cos_le_one (2 * θ)) h1z.le
      have h2 : (1 : ℝ) / (1 + z) ≤ 1 := by
        rw [div_le_one h1z]; linarith
      linarith
    linarith
  linarith [abs_add_le (Work.Construction.Rop α F z θ)
    ((-(2 * Real.sin θ * (Real.sin (2 * θ) / (2 * (1 + z))))
      + α * Real.sin θ * z * ez + Real.cos θ * eth) / Real.cos θ), hE, hα1]

lemma Uop_div_s2_delta_bd {α z θ : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hz : 0 < z)
    (hθ1 : 0 < θ) (hθ2 : θ < π / 2) (F : ℝ → ℝ → ℝ) :
    |Work.Construction.Uop α (F - delta) z θ / Work.Construction.s2 θ|
      ≤ |Work.Construction.Uop α F z θ / Work.Construction.s2 θ| + 10 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ1 (by linarith [hθ2, Real.pi_pos])
  have hs2pos : 0 < Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]
    exact mul_pos (mul_pos (by norm_num) hsin) hcos
  have hs2ne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hs2pos
  have hez := abs_pz_sub_le_delta (F := F) h1z hs2pos.le
  simp only [Work.Construction.s2]
  rw [Uop_sub_eq (F := F) (G := delta), add_div]
  set ez : ℝ := Work.Spaces.pz (F - delta) z θ - Work.Spaces.pz F z θ with hezdef
  have hez' : |ez| ≤ Real.sin (2 * θ) / (2 * (1 + z) ^ 2) := by rw [hezdef]; exact hez
  rw [show delta z θ = Real.sin (2 * θ) / (2 * (1 + z)) from rfl]
  have hE : |(3 * (Real.sin (2 * θ) / (2 * (1 + z))) - α * z * ez) / Real.sin (2 * θ)|
      ≤ 3 / 2 + α / 8 := by
    have hN : |3 * (Real.sin (2 * θ) / (2 * (1 + z))) - α * z * ez|
        ≤ 3 * |Real.sin (2 * θ) / (2 * (1 + z))| + α * z * |ez| := by
      have h2 : |3 * (Real.sin (2 * θ) / (2 * (1 + z))) - α * z * ez|
          ≤ |3 * (Real.sin (2 * θ) / (2 * (1 + z)))| + |α * z * ez| := by
        calc |3 * (Real.sin (2 * θ) / (2 * (1 + z))) - α * z * ez|
            = |3 * (Real.sin (2 * θ) / (2 * (1 + z))) + (-(α * z * ez))| := by rw [sub_eq_add_neg]
          _ ≤ |3 * (Real.sin (2 * θ) / (2 * (1 + z)))| + |-(α * z * ez)| := abs_add_le _ _
          _ = |3 * (Real.sin (2 * θ) / (2 * (1 + z)))| + |α * z * ez| := by rw [abs_neg]
      have h3 : |3 * (Real.sin (2 * θ) / (2 * (1 + z)))| = 3 * |Real.sin (2 * θ) / (2 * (1 + z))| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      have h4 : |α * z * ez| = α * z * |ez| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hα0, abs_of_nonneg hz.le]
      linarith
    have hstep : |(3 * (Real.sin (2 * θ) / (2 * (1 + z))) - α * z * ez) / Real.sin (2 * θ)|
        ≤ (3 * |Real.sin (2 * θ) / (2 * (1 + z))| + α * z * |ez|) / Real.sin (2 * θ) := by
      rw [abs_div, abs_of_nonneg hs2pos.le]
      exact div_le_div_of_nonneg_right hN hs2pos.le
    have hsplit : (3 * |Real.sin (2 * θ) / (2 * (1 + z))| + α * z * |ez|) / Real.sin (2 * θ)
        = 3 * |Real.sin (2 * θ) / (2 * (1 + z))| / Real.sin (2 * θ)
          + α * z * |ez| / Real.sin (2 * θ) := by
      rw [add_div]
    rw [hsplit] at hstep
    have hA : 3 * |Real.sin (2 * θ) / (2 * (1 + z))| / Real.sin (2 * θ) ≤ 3 / 2 := by
      have hkey : 3 * |Real.sin (2 * θ) / (2 * (1 + z))| / Real.sin (2 * θ)
          = 3 / (2 * (1 + z)) := by
        rw [abs_of_nonneg (div_nonneg hs2pos.le (by positivity))]
        field_simp
      rw [hkey, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (1 + z))]
      linarith
    have hB : α * z * |ez| / Real.sin (2 * θ) ≤ α / 8 := by
      have hkey : α * z * |ez| / Real.sin (2 * θ)
          ≤ α * z * (Real.sin (2 * θ) / (2 * (1 + z) ^ 2)) / Real.sin (2 * θ) := by
        apply div_le_div_of_nonneg_right _ hs2pos.le
        exact mul_le_mul_of_nonneg_left hez' (by positivity)
      refine le_trans hkey ?_
      have hkey2 : α * z * (Real.sin (2 * θ) / (2 * (1 + z) ^ 2)) / Real.sin (2 * θ)
          = α * z / (2 * (1 + z) ^ 2) := by
        field_simp
      rw [hkey2]
      have hz4 : z / (1 + z) ^ 2 ≤ 1 / 4 := div_sq_le_quarter hz
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (1 + z) ^ 2)]
      have hz4' : z ≤ (1 + z) ^ 2 / 4 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)] at hz4
        linarith
      have h6 : α * z ≤ α * ((1 + z) ^ 2 / 4) := mul_le_mul_of_nonneg_left hz4' hα0
      have h7 : α / 8 * (2 * (1 + z) ^ 2) = α * ((1 + z) ^ 2 / 4) := by ring
      linarith
    linarith
  linarith [abs_add_le (Work.Construction.Uop α F z θ / Real.sin (2 * θ))
    ((3 * (Real.sin (2 * θ) / (2 * (1 + z))) - α * z * ez) / Real.sin (2 * θ)), hE, hα1]

lemma Vop_delta_bd {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < π / 2)
    (F : ℝ → ℝ → ℝ) :
    |Work.Construction.Vop (F - delta) z θ| ≤ |Work.Construction.Vop F z θ| + 10 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ1 (by linarith [hθ2, Real.pi_pos])
  have hs2nn : 0 ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]
    exact mul_nonneg (mul_nonneg (by norm_num) hsin.le) hcos.le
  have heth := abs_pth_sub_le_delta (F := F) (z := z) (θ := θ) h1z
  rw [Vop_sub_eq (F := F) (G := delta)]
  set eth : ℝ := Work.Spaces.pth (F - delta) z θ - Work.Spaces.pth F z θ with hethdef
  have heth' : |eth| ≤ |Real.cos (2 * θ)| / (1 + z) := by rw [hethdef]; exact heth
  rw [show delta z θ = Real.sin (2 * θ) / (2 * (1 + z)) from rfl]
  have hE : |eth + Real.tan θ * (Real.sin (2 * θ) / (2 * (1 + z)))| ≤ 2 := by
    have htanval : Real.tan θ * (Real.sin (2 * θ) / (2 * (1 + z)))
        = Real.sin θ ^ 2 / (1 + z) := by
      rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul]
      field_simp
    have htanabs : |Real.tan θ * (Real.sin (2 * θ) / (2 * (1 + z)))|
        = Real.sin θ ^ 2 / (1 + z) := by
      rw [htanval, abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity))]
    have h1 : |eth + Real.tan θ * (Real.sin (2 * θ) / (2 * (1 + z)))|
        ≤ |eth| + |Real.tan θ * (Real.sin (2 * θ) / (2 * (1 + z)))| := abs_add_le _ _
    rw [htanabs] at h1
    have h2 : |eth| ≤ 1 / (1 + z) := by
      refine le_trans heth' ?_
      exact div_le_div_of_nonneg_right (Real.abs_cos_le_one (2 * θ)) h1z.le
    have h3 : Real.sin θ ^ 2 / (1 + z) ≤ 1 / (1 + z) :=
      div_le_div_of_nonneg_right (Real.sin_sq_le_one θ) h1z.le
    have h4 : (1 : ℝ) / (1 + z) ≤ 1 := by
      rw [div_le_one h1z]; linarith
    linarith
  linarith [abs_add_le (Work.Construction.Vop F z θ)
    (eth + Real.tan θ * (Real.sin (2 * θ) / (2 * (1 + z)))), hE]

/-- Auxiliary fact for `N0_N_Transport_pt_le`: subtracting the explicit profile
`δ(z,θ) = sin(2θ)/(2(1+z))` (which is `Theta α (Fstar α)`, the singular part of the
stream function of the reference profile) changes each of the three slots `Rop`, `Uop/s2`,
`Vop` by at most `10`.

Hint for the proof.  `Rop α Ψ z θ = (2 sinθ·Ψ + α sinθ·z·pz Ψ + cosθ·pth Ψ)/cosθ`,
`Uop α Ψ z θ = -3Ψ - α z·pz Ψ`, `Vop Ψ z θ = pth Ψ - tanθ·Ψ`; `δ` is smooth for `z ≠ -1`,
with `pz δ z θ = -sin(2θ)/(2(1+z)^2)` and `pth δ z θ = cos(2θ)/(1+z)`.  The obstruction is
that `pz`/`pth` are totalised `deriv`s and are *not* additive in general: if
`f := fun z' => Ψ1 z' θ` is not `DifferentiableAt ℝ · z` then neither is `f - δ`, and both
differentials are `0` (`deriv_zero_of_not_differentiableAt`); if it is differentiable then
`deriv_sub` applies.  In both cases the signed error
`deriv (f - δ) z - deriv f z + deriv δ z` is bounded in absolute value by `|deriv δ z|`
(and likewise in `θ`), which gives the claim with the three explicit bounds
`|Rop α δ| ≤ 2 + α/4 + 1`, `|Uop α δ / s2 θ| ≤ 3/2 + α/8`, `|Vop δ| ≤ 2` (using
`Real.sin_two_mul`, `Real.tan_eq_sin_div_cos`, `0 < cos θ`, `sin(2θ) ≠ 0`). -/
theorem Psivar0_slots_sub : ∀ {α z θ : ℝ}, α ∈ Set.Ioc 0 1 → z ∈ Set.Ioi (0 : ℝ) →
    θ ∈ Set.Ioo (0 : ℝ) (π / 2) → ∀ {Ψ1 : ℝ → ℝ → ℝ},
      |Work.Construction.Rop α (fun z θ => Ψ1 z θ - Real.sin (2 * θ) / (2 * (1 + z))) z θ|
          ≤ |Work.Construction.Rop α Ψ1 z θ| + 10 ∧
      |Work.Construction.Uop α (fun z θ => Ψ1 z θ - Real.sin (2 * θ) / (2 * (1 + z))) z θ
          / Work.Construction.s2 θ|
          ≤ |Work.Construction.Uop α Ψ1 z θ / Work.Construction.s2 θ| + 10 ∧
      |Work.Construction.Vop (fun z θ => Ψ1 z θ - Real.sin (2 * θ) / (2 * (1 + z))) z θ|
          ≤ |Work.Construction.Vop Ψ1 z θ| + 10 := by
  intro α z θ hα hz hθ Ψ1
  obtain ⟨hα0, hα1⟩ := hα
  refine ⟨?_, ?_, ?_⟩
  · exact Rop_delta_bd hα0.le hα1 hz hθ.1 hθ.2 Ψ1
  · exact Uop_div_s2_delta_bd hα0.le hα1 hz hθ.1 hθ.2 Ψ1
  · exact Vop_delta_bd hz hθ.1 hθ.2 Ψ1

end Work.FTS.StrongEps.E5Aux2
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.EulerWeakZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

/-!
# Rigidity of the weak Euler self-similar equation (`EulerWeakZero`)

The auxiliary lemmas below assemble the proof of `EulerWeakZero`:

* `affine_eq_of_ae_eq` -- two affine functions agreeing a.e. on a non degenerate interval agree.
* `exists_affine_of_forall_local` -- a function which is a.e. affine on every `(a,b) ⊆ (0,b)`
  is a.e. affine on `(0,b)` (consistency of the local affine data + countable cover).
* `exists_global_ode_solution` -- local classical solutions of the (Euler-type, second order)
  ODE on the intervals `(0,b)` glue to a global one on `(0,∞)`.
-/

/-- Two affine functions agreeing almost everywhere on a nondegenerate interval coincide. -/
lemma affine_eq_of_ae_eq {a b c₁ c₂ d₁ d₂ : ℝ} (hab : a < b)
    (h : ∀ᵐ t ∂(volume.restrict (Ioo a b)), c₁ + c₂ * t = d₁ + d₂ * t) :
    c₁ = d₁ ∧ c₂ = d₂ := by
  have hcont₁ : ContinuousOn (fun t : ℝ => c₁ + c₂ * t) (Ioo a b) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
  have hcont₂ : ContinuousOn (fun t : ℝ => d₁ + d₂ * t) (Ioo a b) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
  have heq : EqOn (fun t : ℝ => c₁ + c₂ * t) (fun t : ℝ => d₁ + d₂ * t) (Ioo a b) :=
    MeasureTheory.Measure.eqOn_Ioo_of_ae_eq volume h hcont₁ hcont₂
  have h1 : (2 * a + b) / 3 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have h2 : (a + 2 * b) / 3 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have e1 : c₁ + c₂ * ((2 * a + b) / 3) = d₁ + d₂ * ((2 * a + b) / 3) := heq h1
  have e2 : c₁ + c₂ * ((a + 2 * b) / 3) = d₁ + d₂ * ((a + 2 * b) / 3) := heq h2
  have ht : ((2 * a + b) / 3) - ((a + 2 * b) / 3) ≠ 0 := by
    intro hh; linarith
  have hc2 : c₂ = d₂ := by
    have hd : (c₂ - d₂) * (((2 * a + b) / 3) - ((a + 2 * b) / 3)) = 0 := by
      linear_combination e1 - e2
    rcases mul_eq_zero.mp hd with h | h
    · linarith
    · exact absurd h ht
  have hc1 : c₁ = d₁ := by linear_combination e1 - hc2 * ((2 * a + b) / 3)
  exact ⟨hc1, hc2⟩

/-- If a function is a.e. affine on every subinterval `(a,b) ⊆ (0,b)` (with the same ambient `b`),
then the affine representation is in fact global: there is a single pair `(c₁,c₂)` with
`F t = c₁ + c₂ t` for a.e. `t ∈ (0,b)`. -/
lemma exists_affine_of_forall_local {b : ℝ} (hb : 0 < b) {F : ℝ → ℝ}
    (h : ∀ a ∈ Ioo (0 : ℝ) b,
      ∃ c₁ c₂ : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo a b)), F t = c₁ + c₂ * t) :
    ∃ c₁ c₂ : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo 0 b)), F t = c₁ + c₂ * t := by
  classical
  have hpair : ∀ a ∈ Ioo (0 : ℝ) b,
      ∃ p : ℝ × ℝ, ∀ᵐ t ∂(volume.restrict (Ioo a b)), F t = p.1 + p.2 * t := by
    rintro a ha
    obtain ⟨c₁, c₂, hc⟩ := h a ha
    exact ⟨(c₁, c₂), hc⟩
  have hb2 : (b / 2) ∈ Ioo (0 : ℝ) b := ⟨by linarith, by linarith⟩
  obtain ⟨p, hp_spec⟩ := hpair (b / 2) hb2
  have hcons : ∀ a ∈ Ioo (0 : ℝ) b,
      ∀ᵐ t ∂(volume.restrict (Ioo a b)), F t = p.1 + p.2 * t := by
    rintro a ⟨ha0, hab⟩
    obtain ⟨q, hq⟩ := hpair a ⟨ha0, hab⟩
    rcases le_or_gt a (b / 2) with hle | hlt
    · have hsub : Ioo (b / 2) b ⊆ Ioo a b := fun t ht => ⟨by linarith [ht.1, hle], ht.2⟩
      have hq' : ∀ᵐ t ∂(volume.restrict (Ioo (b / 2) b)), F t = q.1 + q.2 * t :=
        MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub hq
      have hp' : ∀ᵐ t ∂(volume.restrict (Ioo (b / 2) b)), F t = p.1 + p.2 * t := hp_spec
      have hae : ∀ᵐ t ∂(volume.restrict (Ioo (b / 2) b)), q.1 + q.2 * t = p.1 + p.2 * t := by
        filter_upwards [hq', hp'] with t h1 h2
        rw [← h1, h2]
      have hqp := affine_eq_of_ae_eq (a := b / 2) (b := b) (by linarith) hae
      rwa [hqp.1, hqp.2] at hq
    · have hsub : Ioo a b ⊆ Ioo (b / 2) b := fun t ht => ⟨by linarith [hlt.le, ht.1], ht.2⟩
      have hp' : ∀ᵐ t ∂(volume.restrict (Ioo a b)), F t = p.1 + p.2 * t :=
        MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub hp_spec
      have hae : ∀ᵐ t ∂(volume.restrict (Ioo a b)), q.1 + q.2 * t = p.1 + p.2 * t := by
        filter_upwards [hq, hp'] with t h1 h2
        rw [← h1, h2]
      have hqp := affine_eq_of_ae_eq hab hae
      rwa [hqp.1, hqp.2] at hq
  refine ⟨p.1, p.2, ?_⟩
  have hfin : ∀ n : ℕ, ∀ᵐ t ∂(volume.restrict (Ioo (b / ((n : ℝ) + 2)) b)),
      F t = p.1 + p.2 * t := by
    intro n
    have h2n : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    refine hcons _ ⟨div_pos hb h2n, ?_⟩
    rw [div_lt_iff₀ h2n]
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    nlinarith [hb, hn]
  have hunion : Ioo (0 : ℝ) b = ⋃ n : ℕ, Ioo (b / ((n : ℝ) + 2)) b := by
    ext t
    simp only [mem_iUnion, mem_Ioo]
    constructor
    · rintro ⟨ht0, htb⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (b / t)
      refine ⟨n, ?_, htb⟩
      rw [div_lt_iff₀ (by positivity)]
      have h₁ := (div_lt_iff₀ ht0).mp hn
      nlinarith
    · rintro ⟨n, hn1, hn2⟩
      exact ⟨lt_trans (by positivity) hn1, hn2⟩
  rw [hunion, MeasureTheory.ae_restrict_iUnion_iff]
  exact hfin

/-- Local classical solutions of the Euler-type second order ODE on the intervals `(0,b)` glue to a
global classical solution on `(0,∞)`. -/
lemma exists_global_ode_solution {α L : ℝ} {W : ℝ → ℝ}
    (h : ∀ b : ℝ, 0 < b → ∃ V : ℝ → ℝ, ContDiffOn ℝ 2 V (Ioo 0 b) ∧
      (∀ t ∈ Ioo 0 b, α ^ 2 * t ^ 2 * deriv (deriv V) t + α * (3 * α - 5) * t * deriv V t
        + (α ^ 2 - 5 * α - L) * V t = 0) ∧ V =ᵐ[volume.restrict (Ioo 0 b)] W) :
    ∃ V : ℝ → ℝ, ContDiffOn ℝ 2 V (Ioi 0) ∧
      (∀ t ∈ Ioi 0, α ^ 2 * t ^ 2 * deriv (deriv V) t + α * (3 * α - 5) * t * deriv V t
        + (α ^ 2 - 5 * α - L) * V t = 0) ∧ V =ᵐ[volume.restrict (Ioi 0)] W := by
  classical
  let Vb : ℝ → ℝ → ℝ := fun b => if hb : 0 < b then Classical.choose (h b hb) else 0
  have hVb : ∀ b (hb : 0 < b), ContDiffOn ℝ 2 (Vb b) (Ioo 0 b) ∧
      (∀ t ∈ Ioo 0 b, α ^ 2 * t ^ 2 * deriv (deriv (Vb b)) t + α * (3 * α - 5) * t * deriv (Vb b) t
        + (α ^ 2 - 5 * α - L) * Vb b t = 0) ∧ Vb b =ᵐ[volume.restrict (Ioo 0 b)] W := by
    intro b hb
    have := Classical.choose_spec (h b hb)
    simpa only [Vb, dif_pos hb] using this
  have hcons : ∀ b b' (hb : 0 < b) (hb' : 0 < b'), EqOn (Vb b) (Vb b') (Ioo 0 (min b b')) := by
    intro b b' hb hb'
    have h1 : ∀ᵐ z ∂(volume.restrict (Ioo 0 b)), Vb b z = W z := (hVb b hb).2.2
    have h2 : ∀ᵐ z ∂(volume.restrict (Ioo 0 b')), Vb b' z = W z := (hVb b' hb').2.2
    have hsub1 : Ioo 0 (min b b') ⊆ Ioo 0 b :=
      fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left b b')⟩
    have hsub2 : Ioo 0 (min b b') ⊆ Ioo 0 b' :=
      fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right b b')⟩
    have h1' : ∀ᵐ z ∂(volume.restrict (Ioo 0 (min b b'))), Vb b z = W z :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub1 h1
    have h2' : ∀ᵐ z ∂(volume.restrict (Ioo 0 (min b b'))), Vb b' z = W z :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub2 h2
    have hu : (fun z => Vb b z) =ᵐ[volume.restrict (Ioo 0 (min b b'))] (fun z => Vb b' z) := by
      filter_upwards [h1', h2'] with z hz1 hz2
      rw [hz1, hz2]
    exact MeasureTheory.Measure.eqOn_Ioo_of_ae_eq volume hu
      ((hVb b hb).1.continuousOn.mono hsub1) ((hVb b' hb').1.continuousOn.mono hsub2)
  let V : ℝ → ℝ := fun z => if hz : 0 < z then Vb (z + 1) z else 0
  have hV_eq : ∀ z ∈ Ioi (0 : ℝ), EqOn V (Vb (z + 1)) (Ioo 0 (z + 1)) := by
    intro z hz
    refine fun z' hz' => ?_
    have hz'0 : 0 < z' := hz'.1
    have hz'z : z' < z + 1 := hz'.2
    have h1 : V z' = Vb (z' + 1) z' := by
      show (if h : 0 < z' then Vb (z' + 1) z' else 0) = Vb (z' + 1) z'
      rw [dif_pos hz'0]
    have h2 : Vb (z' + 1) z' = Vb (z + 1) z' := by
      have hmem : z' ∈ Ioo 0 (min (z' + 1) (z + 1)) := by
        refine ⟨hz'0, ?_⟩
        exact lt_min (by linarith) hz'z
      exact hcons (z' + 1) (z + 1) (by linarith) (by linarith) hmem
    rw [h1, h2]
  have hV_cd : ContDiffOn ℝ 2 V (Ioi 0) := by
    intro z hz
    have hz0 : (0 : ℝ) < z := hz
    rw [contDiffWithinAt_iff_contDiffAt (isOpen_Ioi.mem_nhds hz)]
    refine (ContDiffOn.congr (hVb (z + 1) (by linarith)).1
        (fun w hw => hV_eq z hz hw)).contDiffAt ?_
    exact isOpen_Ioo.mem_nhds ⟨hz0, by linarith⟩
  have hV_deriv1 : ∀ z ∈ Ioi (0 : ℝ), ∀ w ∈ Ioo 0 (z + 1),
      deriv V w = deriv (Vb (z + 1)) w := by
    intro z hz w hw
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hw) (fun w' hw' => hV_eq z hz hw'))
  have hV_deriv2 : ∀ z ∈ Ioi (0 : ℝ), ∀ w ∈ Ioo 0 (z + 1),
      deriv (deriv V) w = deriv (deriv (Vb (z + 1))) w := by
    intro z hz w hw
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hw) (fun w' hw' => hV_deriv1 z hz w' hw'))
  have hV_ode : ∀ t ∈ Ioi (0 : ℝ), α ^ 2 * t ^ 2 * deriv (deriv V) t
      + α * (3 * α - 5) * t * deriv V t + (α ^ 2 - 5 * α - L) * V t = 0 := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have htU : t ∈ Ioo 0 (t + 1) := ⟨ht0, by linarith⟩
    have hspec := (hVb (t + 1) (by linarith)).2.1 t htU
    rw [hV_deriv2 t ht t htU, hV_deriv1 t ht t htU, hV_eq t ht htU]
    exact hspec
  have hV_ae : ∀ᵐ z ∂(volume.restrict (Ioi 0)), V z = W z := by
    have hunion : Ioi (0 : ℝ) = ⋃ n : ℕ, Ioo (0 : ℝ) ((n : ℝ) + 1) := by
      ext t
      simp only [mem_iUnion, mem_Ioi, mem_Ioo]
      constructor
      · intro ht
        obtain ⟨n, hn⟩ := exists_nat_gt t
        exact ⟨n, ht, by linarith⟩
      · rintro ⟨n, hn1, -⟩
        exact hn1
    rw [hunion, MeasureTheory.ae_restrict_iUnion_iff]
    intro n
    have hpoint : ∀ w ∈ Ioo (0 : ℝ) ((n : ℝ) + 1), V w = Vb ((n : ℝ) + 1) w := by
      intro w hw
      have hw0 : 0 < w := hw.1
      have h1 : V w = Vb (w + 1) w := by
        show (if h : 0 < w then Vb (w + 1) w else 0) = Vb (w + 1) w
        rw [dif_pos hw0]
      have h2 : Vb (w + 1) w = Vb ((n : ℝ) + 1) w := by
        have hmem : w ∈ Ioo 0 (min (w + 1) ((n : ℝ) + 1)) := by
          refine ⟨hw0, ?_⟩
          exact lt_min (by linarith) hw.2
        exact hcons (w + 1) ((n : ℝ) + 1) (by linarith) (by positivity) hmem
      rw [h1, h2]
    have h1 : ∀ᵐ z ∂(volume.restrict (Ioo 0 ((n : ℝ) + 1))), V z = Vb ((n : ℝ) + 1) z :=
      (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2
        (Filter.Eventually.of_forall fun w hw => hpoint w hw)
    have h2 : ∀ᵐ z ∂(volume.restrict (Ioo 0 ((n : ℝ) + 1))),
        Vb ((n : ℝ) + 1) z = W z := (hVb ((n : ℝ) + 1) (by positivity)).2.2
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, hz2]
  exact ⟨V, hV_cd, hV_ode, hV_ae⟩

/-- The auxiliary modulus identity: `z^(2p) * z^(-4-2p) = z^(-4)` for `z > 0`. -/
private lemma rpow_two_mul_shift {z p : ℝ} (hz : 0 < z) :
    z ^ (2 * p) * z ^ (-4 - 2 * p) = z ^ (-4 : ℝ) := by
  rw [← Real.rpow_add hz]
  ring_nf

/-- `(z^p)^2 = z^(2p)` for `z ≥ 0`. -/
private lemma sq_rpow {z p : ℝ} (hz : 0 ≤ z) : (z ^ p) ^ 2 = z ^ (2 * p) := by
  rw [← Real.rpow_natCast (z ^ p) 2, ← Real.rpow_mul hz]
  ring_nf

theorem EulerWeakZero {α L : ℝ} (hα : 0 < α) {u : ℝ → ℝ}
    (hu : MeasureTheory.LocallyIntegrableOn u (Set.Ioi 0))
    (hweak : ∀ ρ : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n ρ) → HasCompactSupport ρ →
      tsupport ρ ⊆ Set.Ioi 0 →
      (∫ z in Set.Ioi 0, z ^ ((5 - α) / α) * (L * ρ z
        - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z)) * u z) = 0)
    (hint : MeasureTheory.IntegrableOn (fun z => (u z) ^ 2 * z ^ (-4 : ℝ)) (Set.Ioi 0)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), u z = 0 := by
  set W : ℝ → ℝ := fun z => u z * z ^ ((5 - α) / α) with hWdef
  have hW : MeasureTheory.LocallyIntegrableOn W (Set.Ioi 0) := by
    have hcont : ContinuousOn (fun z : ℝ => z ^ ((5 - α) / α)) (Set.Ioi 0) :=
      continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt hz))
    simpa only [hWdef] using hu.mul_continuousOn hcont isOpen_Ioi.isLocallyClosed
  have hweakW : ∀ ρ : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n ρ) → HasCompactSupport ρ →
      tsupport ρ ⊆ Set.Ioi 0 →
      (∫ z in Set.Ioi 0, W z * (L * ρ z
        - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z))) = 0 := by
    intro ρ hρ hρc hsupp
    have h := hweak ρ hρ hρc hsupp
    have hcongr : (∫ z in Set.Ioi 0, W z * (L * ρ z
        - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z)))
        = ∫ z in Set.Ioi 0, z ^ ((5 - α) / α) * (L * ρ z
        - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z)) * u z := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      simp only [hWdef]
      ring
    rw [hcongr, h]
  -- Step 1: the function figuring in the local affine identity is a.e. affine on `(0,b)`.
  have key : ∀ b : ℝ, 0 < b → ∃ c₁ c₂ : ℝ, ∀ᵐ t ∂(volume.restrict (Set.Ioo 0 b)),
      -(α ^ 2 * t ^ 2 * W t) - α * (5 + α) * (∫ z in t..b, W z * z)
        + L * (∫ z in t..b, (z - t) * W z) = c₁ + c₂ * t := by
    intro b hb
    refine exists_affine_of_forall_local hb ?_
    intro a ha
    obtain ⟨ha0, hab⟩ := ha
    set F : ℝ → ℝ := fun t => -(α ^ 2 * t ^ 2 * W t) - α * (5 + α) * (∫ z in t..b, W z * z)
        + L * (∫ z in t..b, (z - t) * W z) with hFdef
    have hFint : MeasureTheory.LocallyIntegrableOn F (Set.Ioo a b) := by
      have hIoo0 : Set.Ioo a b ⊆ Set.Ioi 0 := fun z hz => lt_trans ha0 hz.1
      have hprod : MeasureTheory.LocallyIntegrableOn (fun t : ℝ => W t * t ^ 2) (Set.Ioo a b) :=
        (hW.mono_set hIoo0).mul_continuousOn (by fun_prop) isLocallyClosed_Ioo
      have hA : MeasureTheory.LocallyIntegrableOn (fun t : ℝ => -(α ^ 2 * t ^ 2 * W t))
          (Set.Ioo a b) := by
        have h1 : MeasureTheory.LocallyIntegrableOn (fun t : ℝ => (W t * t ^ 2) * (-(α ^ 2)))
            (Set.Ioo a b) := hprod.mul_continuousOn continuousOn_const isLocallyClosed_Ioo
        refine h1.congr ?_
        filter_upwards with t
        ring
      have hInt1 : MeasureTheory.IntegrableOn W (Set.uIcc a b) :=
        hW.integrableOn_compact_subset (fun z hz => by
          rcases Set.mem_uIcc.mp hz with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact lt_of_lt_of_le ha0 h1
          · exact lt_of_lt_of_le (lt_trans ha0 hab) h1) isCompact_uIcc
      have hInt2 : MeasureTheory.IntegrableOn (fun z : ℝ => W z * z) (Set.uIcc a b) :=
        hInt1.mul_continuousOn continuous_id.continuousOn isCompact_uIcc
      have hmem : Set.Ioo a b ⊆ Set.uIcc a b :=
        fun z hz => Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt hz.1, le_of_lt hz.2⟩)
      have hcontA : ContinuousOn (fun t : ℝ => ∫ z in t..b, W z * z) (Set.Ioo a b) :=
        (intervalIntegral.continuousOn_primitive_interval_left hInt2).mono hmem
      have hcontC : ContinuousOn (fun t : ℝ => ∫ z in t..b, W z) (Set.Ioo a b) :=
        (intervalIntegral.continuousOn_primitive_interval_left hInt1).mono hmem
      have hB : Set.EqOn (fun t : ℝ => ∫ z in t..b, (z - t) * W z)
          (fun t : ℝ => (∫ z in t..b, W z * z) - t * (∫ z in t..b, W z)) (Set.Ioo a b) := by
        intro t ht
        change (∫ z in t..b, (z - t) * W z)
          = (∫ z in t..b, W z * z) - t * (∫ z in t..b, W z)
        have hsub : Set.uIcc t b ⊆ Set.uIcc a b := by
          rw [Set.uIcc_of_le (le_of_lt ht.2), Set.uIcc_of_le (le_of_lt hab)]
          intro z hz
          exact ⟨le_trans (le_of_lt ht.1) hz.1, hz.2⟩
        have h1 : (∫ z in t..b, (z - t) * W z) = ∫ z in t..b, (W z * z - t * W z) := by
          refine intervalIntegral.integral_congr ?_
          intro z hz
          ring
        have h2 : IntervalIntegrable (fun z : ℝ => t * W z) volume t b :=
          IntervalIntegrable.congr (f := fun z : ℝ => W z * t) (fun z hz => by ring)
            (((hInt1.mono_set hsub).mul_continuousOn continuousOn_const isCompact_uIcc).intervalIntegrable)
        rw [h1, intervalIntegral.integral_sub ((hInt2.mono_set hsub).intervalIntegrable) h2,
          intervalIntegral.integral_const_mul]
      have hcontB : ContinuousOn (fun t : ℝ => ∫ z in t..b, (z - t) * W z) (Set.Ioo a b) := by
        refine ContinuousOn.congr (hcontA.sub (continuousOn_id.mul hcontC)) ?_
        intro t ht
        change (∫ z in t..b, (z - t) * W z)
          = (∫ z in t..b, W z * z) - t * (∫ z in t..b, W z)
        exact hB ht
      have hR : MeasureTheory.LocallyIntegrableOn (fun t : ℝ => - α * (5 + α) * (∫ z in t..b, W z * z)
            + L * (∫ z in t..b, (z - t) * W z)) (Set.Ioo a b) :=
        ((hcontA.const_mul (- α * (5 + α))).add (hcontB.const_mul L)).locallyIntegrableOn
          measurableSet_Ioo
      have hFeq : F = fun t : ℝ => -(α ^ 2 * t ^ 2 * W t)
          + (- α * (5 + α) * (∫ z in t..b, W z * z) + L * (∫ z in t..b, (z - t) * W z)) := by
        funext t
        rw [hFdef]
        ring
      rw [hFeq]
      exact hA.add hR
    refine EulerWeakAffine hab hFint ?_
    intro ψ hψ hψc hsupp h1 h2
    obtain ⟨ρ, hρ, hρc, hρs, hρd⟩ := ExistsTestfunSecondDeriv hab hψ hψc hsupp h1 h2
    have hsupp0 : tsupport ρ ⊆ Set.Ioi 0 := fun z hz => lt_trans ha0 (hρs hz).1
    have hfub := EulerWeakFubini (α := α) (L := L) hW ha0 hab hρ hρc hρs
    have hzero : (∫ z in Set.Ioi 0, W z * (L * ρ z
        - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z))) = 0 :=
      hweakW ρ hρ hρc hsupp0
    rw [hzero] at hfub
    have hgoal : (∫ t in a..b, deriv (deriv ρ) t * F t) = 0 := by
      rw [hFdef]
      exact hfub.symm
    rw [show (∫ t in a..b, ψ t * F t) = ∫ t in a..b, deriv (deriv ρ) t * F t from by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      change ψ t * F t = deriv (deriv ρ) t * F t
      rw [hρd t]]
    exact hgoal
  -- Step 2: classical local solutions of the Euler-type ODE.
  have key2 : ∀ b : ℝ, 0 < b → ∃ V : ℝ → ℝ, ContDiffOn ℝ 2 V (Set.Ioo 0 b) ∧
      (∀ t ∈ Set.Ioo 0 b, α ^ 2 * t ^ 2 * deriv (deriv V) t + α * (3 * α - 5) * t * deriv V t
        + (α ^ 2 - 5 * α - L) * V t = 0) ∧ V =ᵐ[volume.restrict (Set.Ioo 0 b)] W := by
    intro b hb
    obtain ⟨c₁, c₂, hc⟩ := key b hb
    exact EulerWeakClassical (α := α) (L := L) hα hb hW hc
  obtain ⟨V, hVcd, hVode, hVae⟩ := exists_global_ode_solution key2
  -- Step 3: the weighted integrability of `V`.
  have hWint : MeasureTheory.IntegrableOn (fun z : ℝ => (W z) ^ 2 * z ^ (-((10 + 2 * α) / α)))
      (Set.Ioi 0) := by
    refine hint.congr_fun ?_ measurableSet_Ioi
    intro z hz
    have hz0 : 0 < z := hz
    have hMsplit : -((10 + 2 * α) / α) = -4 - 2 * ((5 - α) / α) := by
      field_simp
      ring
    rw [hWdef]
    change (u z) ^ 2 * z ^ (-4 : ℝ)
      = (u z * z ^ ((5 - α) / α)) ^ 2 * z ^ (-((10 + 2 * α) / α))
    rw [hMsplit, mul_pow, sq_rpow (le_of_lt hz0), mul_assoc, rpow_two_mul_shift hz0]
  have hVint : MeasureTheory.IntegrableOn (fun z : ℝ => (V z) ^ 2 * z ^ (-((10 + 2 * α) / α)))
      (Set.Ioi 0) := by
    refine hWint.congr_fun_ae ?_
    filter_upwards [hVae] with z hz
    rw [← hz]
  -- Step 4: `V` vanishes, hence so does `u`.
  have hν : (0 : ℝ) < (10 + α) / α := div_pos (by linarith) hα
  have hode : ∀ z ∈ Set.Ioi 0, z ^ 2 * deriv (deriv V) z + ((3 * α - 5) / α) * z * deriv V z
      + ((α ^ 2 - 5 * α - L) / α ^ 2) * V z = 0 := by
    intro z hz
    have h := hVode z hz
    have hα2 : α ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hα)
    field_simp
    linarith [h]
  have hVint' : MeasureTheory.IntegrableOn
      (fun z : ℝ => (V z) ^ 2 * z ^ ((-1 : ℝ) - (10 + α) / α)) (Set.Ioi 0) := by
    convert hVint using 2
    rw [show (-((10 + 2 * α) / α)) = (-1 : ℝ) - (10 + α) / α from by field_simp; ring]
  have hV0 : ∀ z ∈ Set.Ioi 0, V z = 0 :=
    EulerOdeZero (p := (3 * α - 5) / α) (q := (α ^ 2 - 5 * α - L) / α ^ 2)
      (ν := (10 + α) / α) hν hVcd hode hVint'
  have hW0 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), W z = 0 := by
    filter_upwards [hVae, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz hzmem
    rw [← hz]
    exact hV0 z hzmem
  filter_upwards [hW0, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz hzmem
  have hz0 : (0 : ℝ) < z := hzmem
  rw [hWdef] at hz
  exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt (Real.rpow_pos_of_pos hz0 _))

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.Lzero1_mul_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

theorem Lzero1_mul_sub (f g : ℝ → ℝ) (θ : ℝ) (hcos : Real.cos θ ≠ 0)
    (hf : Differentiable ℝ f) (hfd : Differentiable ℝ (deriv f))
    (hg : Differentiable ℝ g) (hgd : Differentiable ℝ (deriv g)) :
    Work.FTS.EllipticEst.Lzero1 (fun t => f t * g t) θ
        - f θ * Work.FTS.EllipticEst.Lzero1 g θ
      = -g θ * deriv (deriv f) θ + (Real.tan θ * g θ - 2 * deriv g θ) * deriv f θ := by
  -- `L₀ = -∂_θθ + ∂_θ(tan θ ·) - 6` is a second-order operator, so the product rule gives
  -- `L₀(fg) - f·L₀(g) = -g·f'' + (tan θ · g - 2g')·f'`.
  have hfg : deriv (fun t => f t * g t) = fun t => deriv f t * g t + f t * deriv g t := by
    funext t; exact deriv_mul (hf t) (hg t)
  have htan : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.mpr hcos
  have h2 : deriv (fun t => deriv f t * g t + f t * deriv g t) θ
      = deriv (fun t => deriv f t * g t) θ + deriv (fun t => f t * deriv g t) θ :=
    deriv_fun_add (hfd θ |>.mul (hg θ)) ((hf θ).mul (hgd θ))
  have h3 : deriv (fun t => deriv f t * g t) θ
      = deriv (deriv f) θ * g θ + deriv f θ * deriv g θ := deriv_mul (hfd θ) (hg θ)
  have h4 : deriv (fun t => f t * deriv g t) θ
      = deriv f θ * deriv g θ + f θ * deriv (deriv g) θ := deriv_mul (hf θ) (hgd θ)
  have h5 : deriv (fun t => Real.tan t * (f t * g t)) θ
      = deriv Real.tan θ * (f θ * g θ) + Real.tan θ * deriv (fun t => f t * g t) θ :=
    deriv_mul htan ((hf θ).mul (hg θ))
  have h6 : deriv (fun t => Real.tan t * g t) θ
      = deriv Real.tan θ * g θ + Real.tan θ * deriv g θ := deriv_mul htan (hg θ)
  have h7 : deriv (fun t => f t * g t) θ = deriv f θ * g θ + f θ * deriv g θ :=
    deriv_mul (hf θ) (hg θ)
  rw [Work.FTS.EllipticEst.Lzero1, Work.FTS.EllipticEst.Lzero1]
  rw [hfg]
  beta_reduce
  rw [h2, h3, h4, h5, h6, h7]
  ring

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceThetaStepPi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsLocalPStar

/-! ## Step: from the pointwise trace rate at `θ = (π/2)⁻` to the `L²` bound

This is the right-endpoint companion of `TraceThetaStep` (same directory).  The pointwise
hypothesis says that on `(π/4, π/2)` the slice `u` is close to `m` at the rate
`sin(2θ)^{(γ-1)/2}`.  On that interval `0 < sin(2θ) ≤ 1`, so the weight
`sin(2θ)^{-η}` is at least `1`; writing `m = u - (u - m)`, the elementary inequality
`m²/2 ≤ u² + (u - m)²` and the hypothesis give the pointwise bound

`(m²/2) sin^{-η} ≤ u² sin^{-η} + (100/(γ-1)) A sin^{γ-1-η}`

on `(π/4, π/2)`.  Integrating over that interval and comparing with the `Iθ`-integrals
(`∫_{(π/4,π/2)} u² sin^{-η} ≤ ∫_{Iθ} u² sin^{-η}` because the integrand is nonnegative,
and `∫_{(π/4,π/2)} sin^{γ-1-η} ≤ ∫_{(π/4,π/2)} sin^{-η}` because `sin^{γ-1} ≤ 1`) yields

`(m²/2) J ≤ K + (100/(γ-1)) A J`,  `J := ∫_{(π/4,π/2)} sin^{-η} ≥ π/4`,

and division by `J` gives the stated constants. -/

/-- Integrability of `θ ↦ sin(2θ)^p` on `(π/4, π/2)` for every `p > -1`. -/
private theorem tspIntegrableSinPow {p : ℝ} (hp : -1 < p) :
    IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  have hsub : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Work.Spaces.Iθ := by
    intro x hx
    exact ⟨by linarith [hx.1, Real.pi_pos], le_of_lt hx.2⟩
  by_cases hp0 : p ≤ 0
  · exact ((Work.Spaces.sin_two_rpow p hp hp0).1).mono_set hsub
  · have hp0' : 0 < p := not_le.mp hp0
    refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => (1 : ℝ)) ?_ ?_ ?_
    · simp
    · exact ((Measurable.pow_const (Real.measurable_sin.comp
        (measurable_const.mul measurable_id)) p)).aestronglyMeasurable
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hsin0 : 0 ≤ Real.sin (2 * θ) :=
        le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
          (by linarith [hθ.2]))
      have hnorm : ‖(Real.sin (2 * θ)) ^ p‖ ≤ (1 : ℝ) := by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg hsin0 p)]
        exact Real.rpow_le_one hsin0 (Real.sin_le_one _) (le_of_lt hp0')
      simpa using hnorm

/-- On `(π/4, π/2)` the weight `sin(2θ)^{-η}` is at least `1`. -/
private theorem tspOneLe {θ : ℝ} (h0 : Real.pi / 4 < θ) (h1 : θ < Real.pi / 2) :
    (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [h0, Real.pi_pos]) (by linarith)
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_rpow_of_nonpos hsin hle
    (show -(Work.Spaces.eta) ≤ 0 by linarith [Work.Spaces.eta_pos])
  rwa [Real.one_rpow] at h

/-- The weighted length of `(π/4, π/2)` is at least `π/4`. -/
private theorem tspPiDivFourLe :
    Real.pi / 4 ≤ ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hInt : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    tspIntegrableSinPow (p := -(Work.Spaces.eta)) (by linarith [Work.Spaces.eta_lt_one])
  have hInt1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    simp
  have hmono : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), (1 : ℝ))
      ≤ ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
          (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    integral_mono_ae hInt1 hInt
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun θ hθ => tspOneLe hθ.1 hθ.2))
  have hconst : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), (1 : ℝ)) = Real.pi / 4 := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), smul_eq_mul, mul_one]
    ring
  linarith [hmono, hconst]

theorem TraceThetaStepPi {γ m A : ℝ} {u : ℝ → ℝ} (hγ : 1 < γ) (hA : 0 ≤ A)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) Work.Spaces.Iθ)
    (hpt : ∀ θ ∈ Set.Ioo (Real.pi/4) (Real.pi/2),
      (u θ - m)^2 ≤ 100/(γ-1) * (Real.sin (2*θ))^(γ-1) * A) :
    m^2 ≤ 200/(γ-1) * A + 8/Real.pi * (∫ θ in Work.Spaces.Iθ,
        (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) := by
  have hγ1 : 0 < γ - 1 := by linarith
  have hγ10 : (0 : ℝ) ≤ 100 / (γ - 1) := by positivity
  have hsub : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Work.Spaces.Iθ := by
    intro x hx
    exact ⟨by linarith [hx.1, Real.pi_pos], le_of_lt hx.2⟩
  set K : ℝ := ∫ θ in Work.Spaces.Iθ,
    (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta) with hK
  set J0 : ℝ := ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
    (Real.sin (2*θ))^(-Work.Spaces.eta) with hJ
  have hIntU : IntegrableOn (fun θ : ℝ => (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := hint.mono_set hsub
  have hIntS : IntegrableOn (fun θ : ℝ => (Real.sin (2*θ))^(-Work.Spaces.eta))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    tspIntegrableSinPow (p := -(Work.Spaces.eta)) (by linarith [Work.Spaces.eta_lt_one])
  have hIntExp : IntegrableOn (fun θ : ℝ => (Real.sin (2*θ))^(γ-1-Work.Spaces.eta))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    tspIntegrableSinPow (p := γ - 1 - Work.Spaces.eta) (by linarith [Work.Spaces.eta_lt_one])
  -- the pointwise inequality `m²/2 · s ≤ u² · s + (100/(γ-1)) A sin^{γ-1-η}`
  have hpoint : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (Real.pi / 4) (Real.pi / 2))),
      (m^2/2) * (Real.sin (2*θ))^(-Work.Spaces.eta)
        ≤ (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)
          + (100/(γ-1))*A*((Real.sin (2*θ))^(γ-1-(Work.Spaces.eta))) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hsin : 0 < Real.sin (2*θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos]) (by linarith [hθ.2])
    have hsnn : 0 ≤ (Real.sin (2*θ))^(-Work.Spaces.eta) := Real.rpow_nonneg hsin.le _
    have hkey : m^2/2 ≤ (u θ)^2 + (100/(γ-1)) * (Real.sin (2*θ))^(γ-1) * A := by
      have hms : m^2 ≤ 2*(u θ)^2 + 2*(u θ - m)^2 := by nlinarith [sq_nonneg (2*u θ - m)]
      have hp := hpt θ hθ
      linarith
    have hrw : (Real.sin (2*θ))^(γ-1) * (Real.sin (2*θ))^(-Work.Spaces.eta)
        = (Real.sin (2*θ))^(γ-1-Work.Spaces.eta) := by
      rw [← Real.rpow_add hsin]
      ring_nf
    have h2 := mul_le_mul_of_nonneg_right hkey hsnn
    have heq : ((u θ)^2 + (100/(γ-1)) * (Real.sin (2*θ))^(γ-1) * A)
          * (Real.sin (2*θ))^(-Work.Spaces.eta)
        = (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)
          + (100/(γ-1))*A*((Real.sin (2*θ))^(γ-1-Work.Spaces.eta)) := by
      rw [add_mul, ← hrw]; ring
    rwa [heq] at h2
  have hF : IntegrableOn (fun θ : ℝ => (m^2/2) * (Real.sin (2*θ))^(-Work.Spaces.eta))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := MeasureTheory.Integrable.const_mul hIntS (m^2/2)
  have hG : IntegrableOn (fun θ : ℝ => (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)
      + (100/(γ-1))*A*((Real.sin (2*θ))^(γ-1-Work.Spaces.eta)))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    hIntU.add (MeasureTheory.Integrable.const_mul hIntExp ((100/(γ-1))*A))
  have hmono := integral_mono_ae hF hG hpoint
  rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add hIntU (MeasureTheory.Integrable.const_mul hIntExp _),
      MeasureTheory.integral_const_mul, ← hJ] at hmono
  -- comparison of the two integrals with their `Iθ`-counterparts
  have hA1 : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) ≤ K := by
    rw [hK]
    refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])) _)
    · exact Filter.Eventually.of_forall hsub
  have hA2 : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
      (Real.sin (2*θ))^(γ-1-Work.Spaces.eta)) ≤ J0 := by
    rw [hJ]
    refine integral_mono_ae hIntExp hIntS ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hsin : 0 < Real.sin (2*θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos]) (by linarith [hθ.2])
    have hle : (Real.sin (2*θ))^(γ-1-Work.Spaces.eta)
        ≤ (Real.sin (2*θ))^(-Work.Spaces.eta) := by
      rw [show γ - 1 - Work.Spaces.eta = (-Work.Spaces.eta) + (γ - 1) by ring,
        Real.rpow_add hsin]
      exact mul_le_of_le_one_right (Real.rpow_nonneg hsin.le _)
        (Real.rpow_le_one hsin.le (Real.sin_le_one _) (by linarith))
    exact hle
  have hmain : (m^2/2) * J0 ≤ K + (100/(γ-1))*A*J0 := by
    have hcoef : 0 ≤ (100/(γ-1))*A := mul_nonneg hγ10 hA
    have h3 := mul_le_mul_of_nonneg_left hA2 hcoef
    linarith [hmono, hA1, h3]
  have hJge : Real.pi / 4 ≤ J0 := by rw [hJ]; exact tspPiDivFourLe
  have hJpos : 0 < J0 := by linarith [hJge, Real.pi_pos]
  have hKnn : 0 ≤ K := by
    rw [hK]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])) _)
  have hJne : J0 ≠ 0 := ne_of_gt hJpos
  have h1 : m^2/2 ≤ K/J0 + 100/(γ-1)*A := by
    have hdiv : (m^2/2)*J0/J0 ≤ (K + (100/(γ-1))*A*J0)/J0 :=
      div_le_div_of_nonneg_right hmain hJpos.le
    rw [mul_div_assoc, div_self hJne, mul_one] at hdiv
    have hrhs : (K + (100/(γ-1))*A*J0)/J0 = K/J0 + 100/(γ-1)*A := by
      field_simp
    linarith [hdiv, hrhs.le, hrhs.ge]
  have hbnd : K/J0 ≤ (4/Real.pi) * K := by
    have hpi4 : 0 < Real.pi/4 := by linarith [Real.pi_pos]
    have hinv : J0⁻¹ ≤ (Real.pi/4)⁻¹ := inv_anti₀ hpi4 hJge
    have h4 : K/J0 = K * J0⁻¹ := by rw [div_eq_mul_inv]
    rw [h4]
    calc K * J0⁻¹ ≤ K * (Real.pi/4)⁻¹ := mul_le_mul_of_nonneg_left hinv hKnn
      _ = (4/Real.pi) * K := by rw [inv_div]; ring
  have h5 : m^2/2 ≤ (4/Real.pi)*K + 100/(γ-1)*A := by linarith [h1, hbnd]
  have h6 : m^2 ≤ (8/Real.pi)*K + 200/(γ-1)*A := by
    calc m^2 = 2*(m^2/2) := by ring
      _ ≤ 2*((4/Real.pi)*K + 100/(γ-1)*A) := mul_le_mul_of_nonneg_left h5 (by norm_num)
      _ = (8/Real.pi)*K + 200/(γ-1)*A := by ring
  have h7 : (8/Real.pi)*K + 200/(γ-1)*A = 200/(γ-1)*A + 8/Real.pi*K := by ring
  exact h6.trans h7.le

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.FstarDerivs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX.ProfRHSAux

open scoped Real Topology
open Filter

theorem FstarDerivs (α : ℝ) (z θ : ℝ) :
    Work.Construction.Fstar α z θ = Work.Spaces.Gam α θ * (α * Work.FM.Fstar z / Work.Spaces.c α) ∧
    Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        = Work.Spaces.Gam α θ * (α * (z * deriv Work.FM.Fstar z) / Work.Spaces.c α) ∧
    Work.Spaces.Dth (Work.Construction.Fstar α) z θ
        = (α * Work.FM.Fstar z / Work.Spaces.c α)
          * (Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold Work.Construction.Fstar; ring
  · unfold Work.Spaces.Dz Work.Spaces.pz Work.Construction.Fstar
    rw [deriv_const_mul_field]
    ring
  · unfold Work.Spaces.Dth Work.Spaces.pth Work.Construction.Fstar
    have hfun : (fun θ' => α * (Work.Spaces.Gam α θ' / Work.Spaces.c α) * Work.FM.Fstar z)
        = (fun θ' => (α * Work.FM.Fstar z / Work.Spaces.c α) * Work.Spaces.Gam α θ') := by
      funext θ'; ring
    rw [hfun, deriv_const_mul_field]
    ring

end Work.FTS.StrongEps.EpsRLX.ProfRHSAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.GamTraces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX.ProfRHSAux

open scoped Real Topology
open Filter

/-- The base `θ ↦ sin θ · cos²θ` of `Γ(θ) = (sin θ · cos²θ)^{α/3}` is continuous. -/
private theorem continuous_sin_mul_cos_sq :
    Continuous fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 :=
  Real.continuous_sin.mul (Real.continuous_cos.pow 2)

/-- `q(θ) = cos 2θ - 1/3` is continuous. -/
private theorem continuous_qfun : Continuous Work.Spaces.qfun := by
  show Continuous fun θ : ℝ => Real.cos (2 * θ) - 1 / 3
  exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).sub continuous_const

/-- `D_θ Γ = sin(2θ)·Γ'(θ) = α·q(θ)·Γ(θ)` on the open quadrant.  This is the exact
shape in which the angular derivative of `Γ` is needed for the trace statements. -/
private theorem sin_two_mul_deriv_Gam {α θ : ℝ} (hα : 0 < α)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ
      = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ := by
  have h := Work.Spaces.dthU_Gam α θ hα hθ
  simpa only [Work.Spaces.dthU_apply] using h

theorem GamTraces {α : ℝ} (hα : 0 < α) :
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.Gam α θ) (𝓝[>] 0) (𝓝 0) ∧
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.Gam α θ) (𝓝[<] (Real.pi / 2)) (𝓝 0) ∧
    Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ)
      (𝓝[>] 0) (𝓝 0) ∧
    Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ)
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  have hα3 : 0 < α / 3 := by positivity
  have hrpow : Continuous fun x : ℝ => x ^ (α / 3) :=
    Real.continuous_rpow_const (q := α / 3) (le_of_lt hα3)
  have hrpow0 : (0 : ℝ) ^ (α / 3) = 0 := Real.zero_rpow (ne_of_gt hα3)
  -- ## the two limits of `Γ` itself
  have hGam0 : Filter.Tendsto (fun θ : ℝ => Work.Spaces.Gam α θ) (𝓝[>] 0) (𝓝 0) := by
    change Filter.Tendsto (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
      (𝓝[>] 0) (𝓝 0)
    have hbase : Filter.Tendsto (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
        (𝓝[>] 0) (𝓝 0) := by
      simpa using (continuous_sin_mul_cos_sq.tendsto 0).mono_left nhdsWithin_le_nhds
    have h := (hrpow.tendsto 0).comp hbase
    simp only [hrpow0] at h
    exact h
  have hGampi : Filter.Tendsto (fun θ : ℝ => Work.Spaces.Gam α θ)
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    change Filter.Tendsto (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
      (𝓝[<] (Real.pi / 2)) (𝓝 0)
    have hbase : Filter.Tendsto (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
        (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
      simpa using
        (continuous_sin_mul_cos_sq.tendsto (Real.pi / 2)).mono_left nhdsWithin_le_nhds
    have h := (hrpow.tendsto 0).comp hbase
    simp only [hrpow0] at h
    exact h
  -- ## the two limits of `sin(2θ)·Γ'(θ) = α·q(θ)·Γ(θ)`
  have hprod0 : Filter.Tendsto (fun θ : ℝ => α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ)
      (𝓝[>] 0) (𝓝 0) := by
    have hq : Filter.Tendsto (fun θ : ℝ => α * Work.Spaces.qfun θ)
        (𝓝[>] 0) (𝓝 (α * Work.Spaces.qfun 0)) :=
      ((continuous_const.mul continuous_qfun).tendsto 0).mono_left nhdsWithin_le_nhds
    have h := hq.mul hGam0
    simpa using h
  have hprodpi : Filter.Tendsto (fun θ : ℝ => α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ)
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    have hq : Filter.Tendsto (fun θ : ℝ => α * Work.Spaces.qfun θ)
        (𝓝[<] (Real.pi / 2)) (𝓝 (α * Work.Spaces.qfun (Real.pi / 2))) :=
      ((continuous_const.mul continuous_qfun).tendsto _).mono_left nhdsWithin_le_nhds
    have h := hq.mul hGampi
    simpa using h
  have hev0 : (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ)
      =ᶠ[𝓝[>] 0] (fun θ : ℝ => α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ) := by
    show ∀ᶠ θ in 𝓝[>] 0, Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ
      = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ
    rw [eventually_nhdsWithin_iff]
    filter_upwards [isOpen_Iio.mem_nhds
      (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])] with θ hθ hmem
    exact sin_two_mul_deriv_Gam hα ⟨hmem, hθ⟩
  have hevpi : (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ)
      =ᶠ[𝓝[<] (Real.pi / 2)] (fun θ : ℝ => α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ) := by
    show ∀ᶠ θ in 𝓝[<] (Real.pi / 2), Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ
      = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ
    rw [eventually_nhdsWithin_iff]
    filter_upwards [isOpen_Ioi.mem_nhds
      (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])] with θ hθ hmem
    exact sin_two_mul_deriv_Gam hα ⟨hθ, hmem⟩
  exact ⟨hGam0, hGampi, Filter.Tendsto.congr' hev0.symm hprod0,
    Filter.Tendsto.congr' hevpi.symm hprodpi⟩

end Work.FTS.StrongEps.EpsRLX.ProfRHSAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.SA2Def =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.StrongEps.H5

set_option autoImplicit false

/-- The angular profile `α · D_θ²Γ / c(α)` of `D_θ(D_θ F_*)`: the third `F_*`-angular profile,
sitting next to `ClassCRHS.SA0 = αΓ/c` and `ClassCRHS.SA1 = α D_θΓ/c`.  With `D_θ = sin 2θ ∂_θ`,
one has `D_θ(D_θ F_*) = SA2 α θ · SR0 z` and `φ · D_θ(D_θ F_*) = SA2 α θ · SR0 z` on the open
quadrant. -/
def SA2 (α θ : ℝ) : ℝ :=
  α * Work.Spaces.dthU^[2] (fun t => Work.Spaces.Gam α t) θ / Work.Spaces.c α

end Work.FTS.StrongEps.H5
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.ThetaAux =====
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

/-! ## Helper lemmas for the `θ`-direction local-uniformity estimate -/

theorem Ioo_prod_ae_eq_Icc_prod (a b c d : ℝ) :
    (Set.Ioo a b ×ˢ Set.Ioo c d : Set (ℝ × ℝ)) =ᵐ[MeasureTheory.volume]
      (Set.Icc a b ×ˢ Set.Icc c d) := by
  rw [MeasureTheory.ae_eq_set]
  refine ⟨?_, volume_box_sdiff_openBox a b c d⟩
  have hempty : ((Set.Ioo a b ×ˢ Set.Ioo c d : Set (ℝ × ℝ)) \
      (Set.Icc a b ×ˢ Set.Icc c d)) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
    exact hp.2 ⟨⟨le_of_lt hp.1.1.1, le_of_lt hp.1.1.2⟩,
      ⟨le_of_lt hp.1.2.1, le_of_lt hp.1.2.2⟩⟩
  rw [hempty, measure_empty]

theorem aemeasurable_of_continuousOn_openBox {a b c d : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo a b ×ˢ Set.Ioo c d)) :
    AEMeasurable f (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
  have h1 : AEMeasurable f (MeasureTheory.volume.restrict (Set.Ioo a b ×ˢ Set.Ioo c d)) :=
    hf.aemeasurable (isOpen_Ioo.prod isOpen_Ioo).measurableSet
  convert h1 using 1
  exact (MeasureTheory.Measure.restrict_congr_set (Ioo_prod_ae_eq_Icc_prod a b c d)).symm

theorem continuousOn_pth_of_contDiffOn_one {a b c d : ℝ} {u : ℝ → ℝ → ℝ}
    (h1 : ContDiffOn ℝ 1 (Function.uncurry u) (Set.Ioo a b ×ˢ Set.Ioo c d)) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (fun θ' => u p.1 θ') p.2)
      (Set.Ioo a b ×ˢ Set.Ioo c d) := by
  have hV : IsOpen (Set.Ioo a b ×ˢ Set.Ioo c d) := isOpen_Ioo.prod isOpen_Ioo
  have hfd : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry u) p (0, 1))
      (Set.Ioo a b ×ˢ Set.Ioo c d) :=
    (h1.continuousOn_fderiv_of_isOpen hV le_rfl).clm_apply continuousOn_const
  refine hfd.congr fun p hp => ?_
  simpa only [Work.Spaces.pth] using
    (Work.Spaces.pth_eq_fderiv ((h1.differentiableOn (by simp)).differentiableAt
      (hV.mem_nhds hp)))

theorem aemeasurable_pth_sq_mul {a b c d : ℝ} {u w : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 (Function.uncurry u) (Set.Ioo a b ×ˢ Set.Ioo c d))
    (hw : ContinuousOn (Function.uncurry w) (Set.Icc a b ×ˢ Set.Icc c d)) :
    AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((deriv (fun θ' => u p.1 θ') p.2) ^ 2 * (w p.1 p.2) ^ 2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (deriv (fun θ' => u p.1 θ') p.2) ^ 2 * (w p.1 p.2) ^ 2)
      (Set.Ioo a b ×ˢ Set.Ioo c d) := by
    have h2 : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) (Set.Ioo a b ×ˢ Set.Ioo c d) :=
      hw.mono fun p hp => ⟨⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩,
        ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩⟩
    exact ((continuousOn_pth_of_contDiffOn_one hu).pow 2).mul (h2.pow 2)
  have h3 := aemeasurable_of_continuousOn_openBox hcont
  have h4a : AEMeasurable (fun p : ℝ × ℝ =>
      ‖(deriv (fun θ' => u p.1 θ') p.2) ^ 2 * (w p.1 p.2) ^ 2‖ₑ)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    AEStronglyMeasurable.enorm h3.aestronglyMeasurable
  refine AEMeasurable.congr h4a (Eventually.of_forall fun p => ?_)
  exact Real.enorm_eq_ofReal (by positivity)

theorem rho_bounds_theta {a b c d : ℝ} {ρ : ℝ → ℝ → ℝ}
    (hρc : ContinuousOn (Function.uncurry ρ) (Set.Icc a b ×ˢ Set.Icc c d)) :
    ∀ ε > 0, ∃ δ > 0, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, ∀ y ∈ Set.Icc c d,
      |θ - y| < δ → |ρ z θ - ρ z y| < ε := by
  intro ε hε
  have hK : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) :=
    (isCompact_Icc (a := a) (b := b)).prod (isCompact_Icc (a := c) (b := d))
  have hunif : UniformContinuousOn (Function.uncurry ρ) (Set.Icc a b ×ˢ Set.Icc c d) :=
    hK.uniformContinuousOn_of_continuous hρc
  obtain ⟨δ, hδ, hδ'⟩ := (Metric.uniformContinuousOn_iff.mp hunif) ε hε
  refine ⟨δ, hδ, fun z hz θ hθ y hy hθy => ?_⟩
  have hd : dist (z, θ) (z, y) < δ := by
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, Real.dist_eq]
    exact hθy
  have hres := hδ' (z, θ) ⟨hz, hθ⟩ (z, y) ⟨hz, hy⟩ hd
  rwa [Real.dist_eq] at hres

theorem liminf_le_liminf_of_le' {u v : ℕ → ℝ≥0∞} (h : ∀ j, u j ≤ v j) :
    Filter.liminf u Filter.atTop ≤ Filter.liminf v Filter.atTop := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat]
  refine iSup_le fun n => ?_
  refine le_trans ?_ (le_iSup (fun n => ⨅ i, ⨅ (_ : i ≥ n), v i) n)
  refine le_iInf fun i => le_iInf fun hi => ?_
  exact le_trans (le_trans (iInf_le _ i) (iInf_le _ hi)) (h i)

theorem liminf_le_of_eventually_le_const {u : ℕ → ℝ≥0∞} {c : ℝ≥0∞} {K : ℕ}
    (h : ∀ j ≥ K, u j ≤ c) : Filter.liminf u Filter.atTop ≤ c := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat]
  refine iSup_le fun n => ?_
  rcases le_or_gt n K with hn | hn
  · refine le_trans ?_ (h K le_rfl)
    exact le_trans (iInf_le _ K) (iInf_le _ (le_trans hn le_rfl))
  · exact le_trans (le_trans (iInf_le _ n) (iInf_le _ le_rfl)) (h n (le_of_lt hn))

theorem liminf_const_mul_of_ne_top {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) (x : ℕ → ℝ≥0∞) :
    Filter.liminf (fun n => c * x n) Filter.atTop = c * Filter.liminf x Filter.atTop := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat, ENNReal.mul_iSup]
  refine iSup_congr fun n => ?_
  rw [iInf_subtype' (p := fun i : ℕ => i ≥ n) (f := fun i _ => c * x i),
    iInf_subtype' (p := fun i : ℕ => i ≥ n) (f := fun i _ => x i),
    ENNReal.mul_iInf_of_ne hc0 hct]

theorem setLIntegral_mono_subset {α : Type*} [MeasurableSpace α] {μ : Measure α} {s t : Set α}
    {f : α → ℝ≥0∞} (hsm : MeasurableSet s) (htm : MeasurableSet t) (h : s ⊆ t) :
    ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in t, f x ∂μ := by
  rw [← MeasureTheory.lintegral_indicator hsm f, ← MeasureTheory.lintegral_indicator htm f]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (h hx)]
  · rw [Set.indicator_of_notMem hx]
    exact bot_le

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.aemeasurable_deriv_slice_of_contDiffOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

/-- The closed rectangle differs from the open one by a null set: any point of
`[a,b] × [c,d]` that is not in `(a,b) × (c,d)` has one of its coordinates at an endpoint. -/
private lemma volume_diff_box_Icc_Ioo (a b c d : ℝ) :
    (MeasureTheory.volume : Measure (ℝ × ℝ))
        ((Set.Icc a b ×ˢ Set.Icc c d) \ (Set.Ioo a b ×ˢ Set.Ioo c d)) = 0 := by
  have hsub : (Set.Icc a b ×ˢ Set.Icc c d) \ (Set.Ioo a b ×ˢ Set.Ioo c d)
      ⊆ ({a, b} ×ˢ (Set.univ : Set ℝ)) ∪ ((Set.univ : Set ℝ) ×ˢ ({c, d} : Set ℝ)) := by
    rintro ⟨x, y⟩ hp
    rw [Set.mem_sdiff, Set.mem_prod, Set.mem_prod, Set.mem_Ioo, Set.mem_Ioo, Set.mem_Icc,
      Set.mem_Icc] at hp
    obtain ⟨⟨hx, hy⟩, hnot⟩ := hp
    have hcase : (x = a ∨ x = b) ∨ (y = c ∨ y = d) := by
      rcases not_and_or.mp hnot with hA | hB
      · left
        rcases lt_or_ge a x with h | h
        · rcases lt_or_ge x b with h' | h'
          · exact absurd ⟨h, h'⟩ hA
          · exact Or.inr (le_antisymm hx.2 h')
        · exact Or.inl (le_antisymm h hx.1)
      · right
        rcases lt_or_ge c y with h | h
        · rcases lt_or_ge y d with h' | h'
          · exact absurd ⟨h, h'⟩ hB
          · exact Or.inr (le_antisymm hy.2 h')
        · exact Or.inl (le_antisymm h hy.1)
    rcases hcase with (h | h) | (h | h)
    · exact Or.inl ⟨by simp [h], trivial⟩
    · exact Or.inl ⟨by simp [h], trivial⟩
    · exact Or.inr ⟨trivial, by simp [h]⟩
    · exact Or.inr ⟨trivial, by simp [h]⟩
  refine measure_mono_null hsub ?_
  rw [measure_union_null_iff]
  constructor
  · have h : (MeasureTheory.volume : Measure ℝ) ({a, b} : Set ℝ) = 0 := by
      rw [show ({a, b} : Set ℝ) = {a} ∪ {b} from rfl, measure_union_null_iff]
      exact ⟨measure_singleton a, measure_singleton b⟩
    rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, h]; simp
  · have h : (MeasureTheory.volume : Measure ℝ) ({c, d} : Set ℝ) = 0 := by
      rw [show ({c, d} : Set ℝ) = {c} ∪ {d} from rfl, measure_union_null_iff]
      exact ⟨measure_singleton c, measure_singleton d⟩
    rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, h]; simp

theorem aemeasurable_deriv_slice_of_contDiffOn {a b c d : ℝ} {u w : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 (Function.uncurry u) (Set.Ioo a b ×ˢ Set.Ioo c d))
    (hw : ContinuousOn (Function.uncurry w) (Set.Icc a b ×ˢ Set.Icc c d)) :
    AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal ((deriv (fun z' => u z' p.2) p.1) ^ 2 * (w p.1 p.2) ^ 2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
  classical
  set S : Set (ℝ × ℝ) := Set.Ioo a b ×ˢ Set.Ioo c d with hS
  set T : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc c d with hT
  have hSopen : IsOpen S := by rw [hS]; exact isOpen_Ioo.prod isOpen_Ioo
  have hST : S ⊆ T := by
    rw [hS, hT]; exact Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self
  -- On the open rectangle the slice derivative is the continuous Fréchet derivative.
  have hfd : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry u) p) S :=
    hsm.continuousOn_fderiv_of_isOpen hSopen le_rfl
  have hev : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry u) p (1, 0)) S :=
    hfd.clm_apply (continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => ((1 : ℝ), (0 : ℝ))) S)
  have hwS : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) S := hw.mono hST
  have hreal : ContinuousOn (fun p : ℝ × ℝ =>
      (fderiv ℝ (Function.uncurry u) p (1, 0)) ^ 2 * (w p.1 p.2) ^ 2) S :=
    (hev.pow 2).mul (hwS.pow 2)
  have hGcont : ContinuousOn (fun p : ℝ × ℝ => ENNReal.ofReal
      ((fderiv ℝ (Function.uncurry u) p (1, 0)) ^ 2 * (w p.1 p.2) ^ 2)) S :=
    ENNReal.continuous_ofReal.comp_continuousOn hreal
  have hAeS : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
      ((fderiv ℝ (Function.uncurry u) p (1, 0)) ^ 2 * (w p.1 p.2) ^ 2))
      (MeasureTheory.volume.restrict S) := hGcont.aemeasurable hSopen.measurableSet
  -- On `S` the two integrands agree, by the identification of the slice derivative.
  have hae : (fun p : ℝ × ℝ => ENNReal.ofReal
      ((deriv (fun z' => u z' p.2) p.1) ^ 2 * (w p.1 p.2) ^ 2))
      =ᵐ[MeasureTheory.volume.restrict S] (fun p : ℝ × ℝ => ENNReal.ofReal
      ((fderiv ℝ (Function.uncurry u) p (1, 0)) ^ 2 * (w p.1 p.2) ^ 2)) := by
    filter_upwards [self_mem_ae_restrict hSopen.measurableSet] with p hp
    have hdiff : DifferentiableAt ℝ (Function.uncurry u) p :=
      (hsm.contDiffAt (hSopen.mem_nhds hp)).differentiableAt (by norm_num)
    have hkey : deriv (fun z' => u z' p.2) p.1
        = fderiv ℝ (Function.uncurry u) p (1, 0) := by
      have h1 := Work.Spaces.pz_eq_fderiv (G := u) hdiff
      simpa only [Work.Spaces.pz] using h1
    rw [hkey]
  -- The closed rectangle only differs from the open one on a null set.
  have hle : MeasureTheory.volume.restrict T = MeasureTheory.volume.restrict S := by
    apply Measure.restrict_congr_set
    rw [ae_eq_set]
    exact ⟨volume_diff_box_Icc_Ioo a b c d,
      by rw [Set.sdiff_eq_empty.mpr hST, measure_empty]⟩
  rw [hle]
  exact hAeS.congr hae.symm

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.backwardDiffQuot_ioo_ae =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A version of `diffQuot_backward_lintegral_le` with only almost-everywhere smoothness in `θ`
(module `Submission.Work.FTS.StrongEps.LocUnif.backwardDiffQuot_ioo_ae`; this file supersedes the
identically named declarations of the scratch module `_LZiooFallback`, which is kept only as a
stub.)

`Work.FTS.StrongEps.LocUnif.diffQuot_backward_lintegral_le` assumes that the slice
`z ↦ u z θ` is `C¹` for **every** `θ ∈ [c,d]`.  In the application the smoothness is only known
on the open rectangle `(a,b) × (c,d)`, i.e. off the two boundary lines `θ = c`, `θ = d` — which
are Lebesgue-null.  The two lemmas below are the corresponding statements with the hypothesis
weakened to `∀ᵐ θ ∈ [c,d]`; the proofs are the proofs of the original lemmas with
`lintegral_mono` replaced by `lintegral_mono_ae` and the pointwise input restated.
-/

noncomputable section

open MeasureTheory Set

namespace Work.FTS.StrongEps.LocUnif

set_option maxHeartbeats 1000000

/-- A one-dimensional a.e. property lifts to the rectangle, as a property of the second
coordinate. -/
theorem ae_slice_of_ae_restrict {a b c d : ℝ} {P : ℝ → Prop}
    (h : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc c d)), P θ) :
    ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)), P p.2 := by
  rw [MeasureTheory.ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc),
    MeasureTheory.ae_iff]
  refine measure_mono_null (t := Set.Icc a b ×ˢ {θ : ℝ | θ ∈ Set.Icc c d ∧ ¬ P θ}) ?_ ?_
  · intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    have h1 : p ∈ Set.Icc a b ×ˢ Set.Icc c d := by
      by_contra hc
      exact hp fun hmem => absurd hmem hc
    have h2 : ¬ P p.2 := fun hP => hp fun _ => hP
    exact ⟨h1.1, h1.2, h2⟩
  · have hT : (MeasureTheory.volume : Measure ℝ) {θ : ℝ | θ ∈ Set.Icc c d ∧ ¬ P θ} = 0 := by
      have h1 : ∀ᵐ θ ∂(MeasureTheory.volume : Measure ℝ), θ ∈ Set.Icc c d → P θ :=
        (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp h
      have h2 := MeasureTheory.ae_iff.mp h1
      rw [show {θ : ℝ | ¬(θ ∈ Set.Icc c d → P θ)} = {θ : ℝ | θ ∈ Set.Icc c d ∧ ¬ P θ}
        from by ext θ; exact not_imp] at h2
      exact h2
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, hT, mul_zero]

/-- **Pointwise backward-difference-quotient bound** (smoothness hypotheses supplied directly
rather than as a `∀ θ` statement).  This is `diffQuot_pointwise_le` with `hu_sm` and `hθ`
separated, so that the smoothness of the slice at `θ` can be the conclusion of an a.e. argument.
-/
theorem lz_diffQuot_pointwise_le_ioo {a b a' b' c d h C : ℝ}
    (haa' : a < a') (hb'b : b' < b) (hh : 0 < h) (hah : h < a' - a) (hC : 1 ≤ C)
    {w : ℝ → ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hw : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < w z θ)
    (hCw : ∀ z ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      |z - y| ≤ h → (w z θ) ^ 2 ≤ C * (w y θ) ^ 2)
    {θ : ℝ} (hu_sm : ContDiffOn ℝ 1 (fun z => u z θ) (Set.Ioo a b)) (hθ : θ ∈ Set.Icc c d)
    {z : ℝ} (hz : z ∈ Set.Icc a' b') :
    ENNReal.ofReal (((u z θ - u (z - h) θ) / h) ^ 2 * (w z θ) ^ 2)
      ≤ ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹ *
        ∫⁻ s in Set.Ioc 0 h,
          ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s)) ^ 2 * (w (z - s) θ) ^ 2) := by
  have hz_ab : z ∈ Set.Icc a b := ⟨by linarith [hz.1, haa'], by linarith [hz.2, hb'b]⟩
  have hsub : Set.Icc (z - h) z ⊆ Set.Ioo a b := by
    intro x hx
    exact ⟨by linarith [hx.1, hah, hz.1], by linarith [hx.2, hb'b, hz.2]⟩
  have hderiv_cont : ContinuousOn (deriv (fun z' => u z' θ)) (Set.Ioo a b) :=
    hu_sm.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have hcont : ContinuousOn (fun s => deriv (fun z' => u z' θ) (z - s)) (Set.Ioc 0 h) := by
    have hmap : Set.MapsTo (fun s : ℝ => z - s) (Set.Ioc 0 h) (Set.Ioo a b) :=
      fun s hs => hsub ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hcs : ContinuousOn (fun s : ℝ => z - s) (Set.Ioc 0 h) :=
      (continuous_const.sub continuous_id).continuousOn
    exact hderiv_cont.comp hcs hmap
  have hmeas : AEStronglyMeasurable (fun s => deriv (fun z' => u z' θ) (z - s))
      (MeasureTheory.volume.restrict (Set.Ioc 0 h)) :=
    hcont.aestronglyMeasurable measurableSet_Ioc
  have hFTC : ∫ s in (0:ℝ)..h, deriv (fun z' => u z' θ) (z - s) = u z θ - u (z - h) θ :=
    integral_deriv_slice_sub hh.le hsub hu_sm
  have hCS : ENNReal.ofReal ((u z θ - u (z - h) θ)^2)
      ≤ ENNReal.ofReal h *
        ∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2) := by
    have h := ofReal_interval_integral_sq_le hh.le
      (fun s => deriv (fun z' => u z' θ) (z - s)) hmeas
    rw [hFTC, sub_zero] at h
    exact h
  have hpb : ∀ s ∈ Set.Ioc 0 h,
      ENNReal.ofReal ((w z θ)^2) * ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2)
        ≤ ENNReal.ofReal C *
            ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2) := by
    intro s hs
    have hs_ab : z - s ∈ Set.Icc a b := by
      refine ⟨?_, ?_⟩
      · linarith [hz.1, hah, hs.2]
      · linarith [hz.2, hb'b, hs.1]
    have habs : |z - (z - s)| ≤ h := by
      rw [show z - (z - s) = s by ring, abs_of_pos hs.1]
      exact hs.2
    have hCw' : (w z θ)^2 ≤ C * (w (z - s) θ)^2 := hCw z hz_ab (z - s) hs_ab θ hθ habs
    have hCpos : 0 ≤ C := by linarith [hC]
    have hg2 : 0 ≤ (deriv (fun z' => u z' θ) (z - s))^2 := sq_nonneg _
    calc ENNReal.ofReal ((w z θ)^2) * ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2)
        = ENNReal.ofReal ((w z θ)^2 * (deriv (fun z' => u z' θ) (z - s))^2) :=
          (ENNReal.ofReal_mul (sq_nonneg _)).symm
      _ ≤ ENNReal.ofReal (C * ((w (z - s) θ)^2 * (deriv (fun z' => u z' θ) (z - s))^2)) :=
          ENNReal.ofReal_le_ofReal (by nlinarith [hCw', hg2])
      _ = ENNReal.ofReal C *
            ENNReal.ofReal ((w (z - s) θ)^2 * (deriv (fun z' => u z' θ) (z - s))^2) :=
          ENNReal.ofReal_mul hCpos
      _ = ENNReal.ofReal C *
            ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2) := by
          rw [mul_comm ((w (z - s) θ)^2) ((deriv (fun z' => u z' θ) (z - s))^2)]
  have hB : ENNReal.ofReal ((w z θ)^2) *
        (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2))
      ≤ ENNReal.ofReal C *
        (∫⁻ s in Set.Ioc 0 h,
          ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2)) := by
    have hmono := setLIntegral_mono' (μ := volume) measurableSet_Ioc hpb
    rw [lintegral_const_mul' (ENNReal.ofReal ((w z θ)^2))
          (fun s => ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2))
          ENNReal.ofReal_ne_top,
        lintegral_const_mul' (ENNReal.ofReal C)
          (fun s => ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2))
          ENNReal.ofReal_ne_top] at hmono
    exact hmono
  have hcore : ENNReal.ofReal (((u z θ - u (z - h) θ)/h)^2)
      = ENNReal.ofReal ((u z θ - u (z - h) θ)^2) * (ENNReal.ofReal h)⁻¹
        * (ENNReal.ofReal h)⁻¹ := by
    rw [show ((u z θ - u (z - h) θ)/h)^2
        = (u z θ - u (z - h) θ)^2 * (h⁻¹)^2 by ring]
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ h⁻¹),
        ENNReal.ofReal_inv_of_pos hh]
    ring
  have ht : ENNReal.ofReal h * (ENNReal.ofReal h)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hh) ENNReal.ofReal_ne_top
  have h1 := mul_le_mul_of_nonneg_right hCS (zero_le : (0 : ENNReal) ≤ (ENNReal.ofReal h)⁻¹)
  have h2 := mul_le_mul_of_nonneg_right h1 (zero_le : (0 : ENNReal) ≤ (ENNReal.ofReal h)⁻¹)
  have h3 := mul_le_mul_of_nonneg_right h2 (zero_le : (0 : ENNReal) ≤ ENNReal.ofReal ((w z θ)^2))
  have h4 := mul_le_mul_of_nonneg_right hB (zero_le : (0 : ENNReal) ≤ (ENNReal.ofReal h)⁻¹)
  calc ENNReal.ofReal (((u z θ - u (z - h) θ) / h) ^ 2 * (w z θ) ^ 2)
      = ENNReal.ofReal (((u z θ - u (z - h) θ) / h) ^ 2) * ENNReal.ofReal ((w z θ)^2) :=
        ENNReal.ofReal_mul (sq_nonneg _)
    _ = (ENNReal.ofReal ((u z θ - u (z - h) θ)^2) * (ENNReal.ofReal h)⁻¹
            * (ENNReal.ofReal h)⁻¹) * ENNReal.ofReal ((w z θ)^2) := by rw [hcore]
    _ ≤ (ENNReal.ofReal h *
            (∫⁻ s in Set.Ioc 0 h,
              ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2)))
          * (ENNReal.ofReal h)⁻¹ * (ENNReal.ofReal h)⁻¹ * ENNReal.ofReal ((w z θ)^2) := h3
    _ = ENNReal.ofReal ((w z θ)^2) *
          (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2))
          * (ENNReal.ofReal h)⁻¹ := by
        rw [show (ENNReal.ofReal h *
              (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2)))
              * (ENNReal.ofReal h)⁻¹ * (ENNReal.ofReal h)⁻¹ * ENNReal.ofReal ((w z θ)^2)
            = (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2))
              * (ENNReal.ofReal h * (ENNReal.ofReal h)⁻¹) * (ENNReal.ofReal h)⁻¹
              * ENNReal.ofReal ((w z θ)^2) from by ring]
        rw [ht]; ring
    _ ≤ (ENNReal.ofReal C *
          (∫⁻ s in Set.Ioc 0 h,
            ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2)))
          * (ENNReal.ofReal h)⁻¹ := h4
    _ = ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹ *
          ∫⁻ s in Set.Ioc 0 h,
            ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2) := by
        ring

/-- **The backward difference-quotient bound**, with only a.e. smoothness in `θ`. -/
theorem lz_diffQuot_backward_lintegral_le_ioo {a b a' b' c d h C : ℝ}
    (haa' : a < a') (hb'b : b' < b) (hh : 0 < h) (hah : h < a' - a) (hC : 1 ≤ C)
    {w : ℝ → ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hw : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < w z θ)
    (hCw : ∀ z ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      |z - y| ≤ h → (w z θ) ^ 2 ≤ C * (w y θ) ^ 2)
    (hu_sm : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc c d)),
      ContDiffOn ℝ 1 (fun z => u z θ) (Set.Ioo a b))
    (hmeas : AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal ((deriv (fun z' => u z' p.2) p.1) ^ 2 * (w p.1 p.2) ^ 2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))) :
    ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ENNReal.ofReal (((u p.1 p.2 - u (p.1 - h) p.2) / h) ^ 2 * (w p.1 p.2) ^ 2)
      ≤ ENNReal.ofReal C * ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
          ENNReal.ofReal ((deriv (fun z' => u z' p.2) p.1) ^ 2 * (w p.1 p.2) ^ 2) := by
  set G : ℝ × ℝ → ENNReal :=
    fun q => ENNReal.ofReal ((deriv (fun z' => u z' q.2) q.1) ^ 2 * (w q.1 q.2) ^ 2) with hGdef
  have hGmeas : AEMeasurable G (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    hmeas
  obtain ⟨G', hG'meas, hG'ae⟩ := hGmeas
  have hcne : ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hh).ne')
  -- The a.e. smoothness of the slice, lifted to the inner rectangle.
  have hae_sm : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Icc a' b' ×ˢ Set.Icc c d)),
      ContDiffOn ℝ 1 (fun z => u z p.2) (Set.Ioo a b) :=
    ae_slice_of_ae_restrict (a := a') (b := b') hu_sm
  have hae_sm_v : ∀ᵐ p ∂(MeasureTheory.volume : Measure (ℝ × ℝ)),
      p ∈ Set.Icc a' b' ×ˢ Set.Icc c d → ContDiffOn ℝ 1 (fun z => u z p.2) (Set.Ioo a b) :=
    (MeasureTheory.ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).mp hae_sm
  have hstep1 : ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ENNReal.ofReal (((u p.1 p.2 - u (p.1 - h) p.2) / h) ^ 2 * (w p.1 p.2) ^ 2)
      ≤ (ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹) *
        ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
          ∫⁻ s in Set.Ioc 0 h, G (p.1 - s, p.2) := by
    rw [← lintegral_indicator (measurableSet_Icc.prod measurableSet_Icc)
          (f := fun p : ℝ × ℝ =>
            ENNReal.ofReal (((u p.1 p.2 - u (p.1 - h) p.2) / h) ^ 2 * (w p.1 p.2) ^ 2)),
        ← lintegral_indicator (measurableSet_Icc.prod measurableSet_Icc)
          (f := fun p : ℝ × ℝ => ∫⁻ s in Set.Ioc 0 h, G (p.1 - s, p.2)),
        ← lintegral_const_mul' _ _ hcne]
    refine lintegral_mono_ae ?_
    filter_upwards [hae_sm_v] with p hp
    by_cases hpp : p ∈ Set.Icc a' b' ×ˢ Set.Icc c d
    · rw [Set.indicator_of_mem hpp, Set.indicator_of_mem hpp]
      exact lz_diffQuot_pointwise_le_ioo haa' hb'b hh hah hC hw hCw (hp hpp) hpp.2 hpp.1
    · rw [Set.indicator_of_notMem hpp, Set.indicator_of_notMem hpp, mul_zero]
  have hstep2 : ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ∫⁻ s in Set.Ioc 0 h, G (p.1 - s, p.2)
      = ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ∫⁻ s in Set.Ioc 0 h, G' (p.1 - s, p.2) :=
    lintegral_congr_ae (ae_lintegral_shift_eq haa' hb'b hh hah hG'ae)
  have hstep3 : ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ∫⁻ s in Set.Ioc 0 h, G' (p.1 - s, p.2)
      ≤ ENNReal.ofReal h * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q :=
    lintegral_lintegral_shift_le haa' hb'b hh hah hG'meas
  have hstep4 : ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q
      = ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G q :=
    lintegral_congr_ae hG'ae.symm
  calc ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
        ENNReal.ofReal (((u p.1 p.2 - u (p.1 - h) p.2) / h) ^ 2 * (w p.1 p.2) ^ 2)
      ≤ (ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹) *
        ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
          ∫⁻ s in Set.Ioc 0 h, G (p.1 - s, p.2) := hstep1
    _ = (ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹) *
        ∫⁻ p in Set.Icc a' b' ×ˢ Set.Icc c d,
          ∫⁻ s in Set.Ioc 0 h, G' (p.1 - s, p.2) := by rw [hstep2]
    _ ≤ (ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹) *
        (ENNReal.ofReal h * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G' q) :=
        mul_le_mul_right hstep3 _
    _ = (ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹) *
        (ENNReal.ofReal h * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G q) := by rw [hstep4]
    _ = ENNReal.ofReal C * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d, G q := by
        rw [mul_assoc, ← mul_assoc (ENNReal.ofReal h)⁻¹,
          ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hh).ne' ENNReal.ofReal_ne_top, one_mul]
    _ = ENNReal.ofReal C * ∫⁻ q in Set.Icc a b ×ˢ Set.Icc c d,
          ENNReal.ofReal ((deriv (fun z' => u z' q.2) q.1) ^ 2 * (w q.1 q.2) ^ 2) := rfl

end Work.FTS.StrongEps.LocUnif
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.deriv_sq_weighted_le_of_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- Fatou's lemma for real-valued functions: if `ofReal (f x) ≤ liminf_n ofReal (G n x)` almost
everywhere, then `∫⁻ ofReal f ≤ liminf_n ∫⁻ ofReal (G n)`.  This is the sharp lower-semicontinuity
statement for the lower Lebesgue integral, stated at the `ENNReal` level so no integrability
hypothesis is needed. -/
theorem lintegral_le_liminf_of_eventually_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {G : ℕ → α → ℝ} {f : α → ℝ}
    (hG : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (G n x)) μ)
    (h : ∀ᵐ x ∂μ, ENNReal.ofReal (f x) ≤
      Filter.liminf (fun n => ENNReal.ofReal (G n x)) Filter.atTop) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤
      Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (G n x) ∂μ) Filter.atTop :=
  (MeasureTheory.lintegral_mono_ae h).trans (MeasureTheory.lintegral_liminf_le' hG)


end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.diffQuot_backward_lintegral_le_theta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The backward difference-quotient weighted `L²` bound in the `θ`-variable

`diffQuot_backward_lintegral_le_theta`: the weighted `L²`-norm of the backward difference quotient
`θ ↦ (u z θ - u z (θ - h))/h` over `[a, b] × [c', d']` is bounded by `C` times the weighted
`L²`-norm of `∂_θu` over the larger rectangle `[a, b] × [c, d]`.

This is the `θ`-analogue of `Work.FTS.StrongEps.LocUnif.diffQuot_backward_lintegral_le` (which
differentiates in `z`); it is the "second half" of the local-uniformity extraction, consumed by
`lintegral_backwardDiffQuot_majorant_le_liminf_theta`.

## Proof

The statement is the `z`-statement in the coordinates `(θ, z)` instead of `(z, θ)`: applying
`diffQuot_backward_lintegral_le` to the *swapped* integrand `u' z θ = u θ z` and the *swapped*
weight `w' z θ = w θ z` with the intervals `a ↦ c`, `b ↦ d`, `c ↦ a`, `d ↦ b` produces the claim
with both rectangles transposed.  Both the hypothesis `hmeas` and the two integrals are then
transported back along the coordinate swap `(z, θ) ↦ (θ, z)`:

* set integrals over a product of intervals are invariant under the swap
  (`setLIntegral_prod_swap`, from Tonelli's `MeasureTheory.lintegral_prod_swap` and
  `Measure.prod_restrict` / `Measure.volume_eq_prod`);
* a.e. measurability is invariant under the swap (`aemeasurable_restrict_prod_swap`, from
  `AEMeasurable.prod_swap`).

This is exactly the reduction recommended in the area notes
(`Submission/Work/FTS/StrongEps/LocUnif/NOTES_assembly_final.md`, item 2: "the `θ` direction
(mirror, or derived from the `z` version by the measure-preserving swap …)").
-/

noncomputable section

open scoped ENNReal
open MeasureTheory Set

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false

/-- The product of the restricted Lebesgue measures on `ℝ` is the restriction of Lebesgue
measure on `ℝ × ℝ` to the product of the two sets. -/
theorem restrict_prod_volume (A B : Set ℝ) :
    (MeasureTheory.volume.restrict A).prod (MeasureTheory.volume.restrict B)
      = MeasureTheory.volume.restrict (A ×ˢ B) := by
  rw [Measure.prod_restrict, Measure.volume_eq_prod]

/-- **Set integrals over a product of intervals are invariant under the swap of the two
coordinates.**  `∫⁻_{(x,y) ∈ A ×ˢ B} F y x = ∫⁻_{(x,y) ∈ B ×ˢ A} F x y`. -/
theorem setLIntegral_prod_swap {A B : Set ℝ} (F : ℝ → ℝ → ℝ≥0∞) :
    ∫⁻ p in A ×ˢ B, F p.2 p.1 = ∫⁻ p in B ×ˢ A, F p.1 p.2 := by
  have h := MeasureTheory.lintegral_prod_swap (μ := MeasureTheory.volume.restrict B)
    (ν := MeasureTheory.volume.restrict A) (f := fun p : ℝ × ℝ => F p.1 p.2)
  rw [restrict_prod_volume, restrict_prod_volume] at h
  exact h

/-- **Almost-everywhere measurability is invariant under the swap of the two coordinates**,
for the restrictions to a product of rectangles. -/
theorem aemeasurable_restrict_prod_swap {A B : Set ℝ} {F : ℝ → ℝ → ℝ≥0∞}
    (h : AEMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
      (MeasureTheory.volume.restrict (A ×ˢ B))) :
    AEMeasurable (fun p : ℝ × ℝ => F p.2 p.1) (MeasureTheory.volume.restrict (B ×ˢ A)) := by
  have h' : AEMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
      ((MeasureTheory.volume.restrict A).prod (MeasureTheory.volume.restrict B)) := by
    rwa [restrict_prod_volume]
  have h2 := h'.prod_swap
  rwa [restrict_prod_volume] at h2

theorem diffQuot_backward_lintegral_le_theta {a b c d c' d' h C : ℝ}
    (hcc' : c < c') (hd'd : d' < d) (hh : 0 < h) (hah : h < c' - c) (hC : 1 ≤ C)
    {w : ℝ → ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hw : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < w z θ)
    (hCw : ∀ z ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d, ∀ θ ∈ Set.Icc c d,
      |θ - y| ≤ h → (w z θ) ^ 2 ≤ C * (w z y) ^ 2)
    (hu_sm : ∀ z ∈ Set.Icc a b, ContDiffOn ℝ 1 (fun θ => u z θ) (Set.Ioo c d))
    (hu_c : ∀ z ∈ Set.Icc a b, ContinuousOn (fun θ => u z θ) (Set.Icc c d))
    (hmeas : AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal ((deriv (fun θ' => u p.1 θ') p.2) ^ 2 * (w p.1 p.2) ^ 2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))) :
    ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
        ENNReal.ofReal (((u p.1 p.2 - u p.1 (p.2 - h)) / h) ^ 2 * (w p.1 p.2) ^ 2)
      ≤ ENNReal.ofReal C * ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
          ENNReal.ofReal ((deriv (fun θ' => u p.1 θ') p.2) ^ 2 * (w p.1 p.2) ^ 2) := by
  -- The a.e. measurability of the `θ`-derivative energy, in the swapped coordinates.
  have hmeas' : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((deriv (fun z' => u p.2 z') p.1) ^ 2 * (w p.2 p.1) ^ 2))
      (volume.restrict (Set.Icc c d ×ˢ Set.Icc a b)) :=
    aemeasurable_restrict_prod_swap (F := fun x y =>
      ENNReal.ofReal ((deriv (fun θ' => u x θ') y) ^ 2 * (w x y) ^ 2)) (A := Set.Icc a b)
      (B := Set.Icc c d) hmeas
  -- The `z`-statement, in the swapped coordinates and with the intervals interchanged.
  have key := diffQuot_backward_lintegral_le (a := c) (b := d) (a' := c') (b' := d')
    (c := a) (d := b) (h := h) (C := C) (w := fun z θ => w θ z) (u := fun z θ => u θ z)
    hcc' hd'd hh hah hC
    (fun z hz θ hθ => hw θ hθ z hz)
    (fun Z hZ Y hY T hT habs => hCw T hT Y hY Z hZ habs)
    (fun θ hθ => hu_sm θ hθ)
    (fun θ hθ => hu_c θ hθ)
    hmeas'
  calc ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c' d',
        ENNReal.ofReal (((u p.1 p.2 - u p.1 (p.2 - h)) / h) ^ 2 * (w p.1 p.2) ^ 2)
      = ∫⁻ p in Set.Icc c' d' ×ˢ Set.Icc a b,
        ENNReal.ofReal (((u p.2 p.1 - u p.2 (p.1 - h)) / h) ^ 2 * (w p.2 p.1) ^ 2) :=
        (setLIntegral_prod_swap (A := Set.Icc c' d') (B := Set.Icc a b)
          (F := fun x y => ENNReal.ofReal (((u x y - u x (y - h)) / h) ^ 2 * (w x y) ^ 2))).symm
    _ ≤ ENNReal.ofReal C * ∫⁻ p in Set.Icc c d ×ˢ Set.Icc a b,
        ENNReal.ofReal ((deriv (fun z' => u p.2 z') p.1) ^ 2 * (w p.2 p.1) ^ 2) := key
    _ = ENNReal.ofReal C * ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((deriv (fun θ' => u p.1 θ') p.2) ^ 2 * (w p.1 p.2) ^ 2) := by
        rw [setLIntegral_prod_swap (A := Set.Icc c d) (B := Set.Icc a b)
          (F := fun x y => ENNReal.ofReal ((deriv (fun θ' => u x θ') y) ^ 2 * (w x y) ^ 2))]

end Work.FTS.StrongEps.LocUnif
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.ofReal_HkIntegrand_six_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped ENNReal
open Filter

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false

/-! ## The Fatou-type inequality for `liminf` of a finite sum in `ℝ≥0∞`

In `ℝ≥0∞` addition preserves arbitrary suprema (`ENNReal.iSup_add`, `ENNReal.add_iSup`), so
`liminf u + liminf v ≤ liminf (u + v)` for every filter (the superadditivity direction, i.e. the
Fatou direction: the left side is *smaller*).  Finitely many summands follow by induction. -/

private lemma liminf_add_le_ennreal (u v : ℕ → ℝ≥0∞) :
    Filter.liminf u Filter.atTop + Filter.liminf v Filter.atTop
      ≤ Filter.liminf (fun n => u n + v n) Filter.atTop := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat]
  rw [ENNReal.iSup_add]
  refine iSup_le fun N => ?_
  rw [ENNReal.add_iSup]
  refine iSup_le fun M => ?_
  rw [Filter.liminf_eq_iSup_iInf_of_nat]
  refine le_iSup_of_le (max N M) ?_
  refine le_iInf fun n => le_iInf fun hn => ?_
  have hN : N ≤ n := le_trans (le_max_left _ _) hn
  have hM : M ≤ n := le_trans (le_max_right _ _) hn
  have h1 : (⨅ i, ⨅ (_ : i ≥ N), u i) ≤ u n := le_trans (iInf_le _ n) (iInf_le _ hN)
  have h2 : (⨅ i, ⨅ (_ : i ≥ M), v i) ≤ v n := le_trans (iInf_le _ n) (iInf_le _ hM)
  exact add_le_add h1 h2

/-- The Fatou-type inequality for a finite sum of `ℝ≥0∞`-valued sequences: the sum of the
`liminf`s is at most the `liminf` of the sums. -/
private theorem liminf_finset_sum_le {ι : Type*} (s : Finset ι) (u : ι → ℕ → ℝ≥0∞) :
    (∑ k ∈ s, Filter.liminf (u k) Filter.atTop)
      ≤ Filter.liminf (fun n => ∑ k ∈ s, u k n) Filter.atTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      calc Filter.liminf (u a) Filter.atTop + (∑ k ∈ s, Filter.liminf (u k) Filter.atTop)
          ≤ Filter.liminf (u a) Filter.atTop
              + Filter.liminf (fun n => ∑ k ∈ s, u k n) Filter.atTop :=
            add_le_add le_rfl ih
        _ ≤ Filter.liminf (fun n => u a n + ∑ k ∈ s, u k n) Filter.atTop :=
            liminf_add_le_ennreal _ _

/-! ## The majorisation -/

/-- The level-6 integrand is dominated, in `ℝ≥0∞`, by the level-5 integrand plus the two
measurable majorants `V6z`, `V6t` built from the backward difference quotients of the level-5
slots. -/
theorem ofReal_HkIntegrand_six_le (α : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    ENNReal.ofReal (Work.Spaces.HkIntegrand α 6 f p.1 p.2)
      ≤ ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 f p.1 p.2)
        + Work.FTS.StrongEps.LocUnif.V6z α f p
        + Work.FTS.StrongEps.LocUnif.V6t α f p := by
  obtain ⟨hid, hZ, hT⟩ := Work.FTS.StrongEps.LocUnif.level6_identities α
  -- The three nonnegativity facts needed to split `ofReal` of a sum.
  have h5 : 0 ≤ Work.Spaces.HkIntegrand α 5 f p.1 p.2 :=
    Work.Spaces.HkIntegrand_nonneg α 5 f p.1 p.2
  have hZnn : 0 ≤ level6Z α f p.1 p.2 := by
    rw [level6Z]
    exact Finset.sum_nonneg fun k _ => sq_nonneg _
  have hTnn : 0 ≤ level6T α f p.1 p.2 := by
    rw [level6T]
    exact sq_nonneg _
  -- Per-slot: the weighted level-6 `z`-slot is dominated by the liminf of the backward
  -- difference quotients of its level-5 parent.
  have hk : ∀ k ∈ Finset.range 6,
      ENNReal.ofReal ((deriv (fun z' => Work.Spaces.mixed (5 - k) k f z' p.2) p.1
          * (p.1 * rho6 α k p.1 p.2)) ^ 2)
        ≤ Filter.liminf (fun j : ℕ => ENNReal.ofReal
            (((Work.Spaces.mixed (5 - k) k f p.1 p.2
                - Work.Spaces.mixed (5 - k) k f (p.1 - 1 / ((j : ℝ) + 1)) p.2) * ((j : ℝ) + 1)
              * (p.1 * rho6 α k p.1 p.2)) ^ 2)) Filter.atTop :=
    fun k _ => ofReal_deriv_sq_le_liminf_backwardDiffQuot _ _ _
  -- The `z`-directed half.
  have hZle : ENNReal.ofReal (level6Z α f p.1 p.2) ≤ V6z α f p := by
    rw [hZ f p, ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
    exact le_trans (Finset.sum_le_sum hk) (liminf_finset_sum_le (Finset.range 6) _)
  -- The `θ`-directed slot.
  have hTle : ENNReal.ofReal (level6T α f p.1 p.2) ≤ V6t α f p :=
    hT f p ▸ ofReal_deriv_sq_le_liminf_backwardDiffQuot
      (fun θ' => Work.Spaces.mixed 0 5 f p.1 θ') p.2
      (Real.sin (2 * p.2) * rho6 α 6 p.1 p.2)
  calc ENNReal.ofReal (Work.Spaces.HkIntegrand α 6 f p.1 p.2)
      = ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 f p.1 p.2
          + level6Z α f p.1 p.2 + level6T α f p.1 p.2) := by rw [hid f p.1 p.2]
    _ = ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 f p.1 p.2)
          + ENNReal.ofReal (level6Z α f p.1 p.2)
          + ENNReal.ofReal (level6T α f p.1 p.2) := by
        rw [ENNReal.ofReal_add (add_nonneg h5 hZnn) hTnn, ENNReal.ofReal_add h5 hZnn]
    _ ≤ ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 f p.1 p.2)
          + V6z α f p + V6t α f p := add_le_add (add_le_add le_rfl hZle) hTle

end Work.FTS.StrongEps.LocUnif
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.gRHSBound.abs_N0_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pointwise bound on `N₀` used by the `g`-equation right-hand-side estimate

`N₀` (paper tex `\eqref{N0}`) is a sum of six products of the form
`coefficient · L₁₂(·) · (F or g or a first derivative)`, with coefficients
`3/(2α)·sin(2θ)`, `-(cos2θ - sin²θ)`, `1/α`.  Since `|sin 2θ| ≤ 1` and
`|cos2θ - sin²θ| ≤ 2` for every `θ`, and every remaining factor is bounded by `B`
in absolute value, the triangle inequality gives

`|N₀| ≤ (3/(2α) + 2 + 1/α + 3/(2α) + 2 + 2) B² = (4/α + 6) B²`.

The constant `4/α + 6` of the statement is exactly the sum of the six coefficients.
-/

namespace Work.FTS.StrongEps.gRHSBound

open scoped Real

/-- `|x - y| ≤ |x| + |y|` (the `abs_sub_le` of this Mathlib is stated with a middle point). -/
private lemma abs_sub_le_abs_add_abs (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  simpa [sub_eq_add_neg] using abs_add_le x (-y)

/-- `|a*b*c| ≤ A*B'*C` from factorwise bounds. -/
private lemma abs_mul3_le {a b c A B' C : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B') (hc : |c| ≤ C) :
    |a * b * c| ≤ A * B' * C := by
  have hA : 0 ≤ A := le_trans (abs_nonneg a) ha
  have hB : 0 ≤ B' := le_trans (abs_nonneg b) hb
  have hC : 0 ≤ C := le_trans (abs_nonneg c) hc
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul ha hb (abs_nonneg b) hA) hc (abs_nonneg c) (mul_nonneg hA hB)

/-- `|a*b*c*d| ≤ A*B'*C*D` from factorwise bounds. -/
private lemma abs_mul4_le {a b c d A B' C D : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B')
    (hc : |c| ≤ C) (hd : |d| ≤ D) : |a * b * c * d| ≤ A * B' * C * D := by
  have hA : 0 ≤ A := le_trans (abs_nonneg a) ha
  have hB : 0 ≤ B' := le_trans (abs_nonneg b) hb
  have hC : 0 ≤ C := le_trans (abs_nonneg c) hc
  have hD : 0 ≤ D := le_trans (abs_nonneg d) hd
  rw [abs_mul, abs_mul, abs_mul]
  have h1 : |a| * |b| ≤ A * B' := mul_le_mul ha hb (abs_nonneg b) hA
  have h2 : |a| * |b| * |c| ≤ A * B' * C := mul_le_mul h1 hc (abs_nonneg c) (mul_nonneg hA hB)
  exact mul_le_mul h2 hd (abs_nonneg d) (mul_nonneg (mul_nonneg hA hB) hC)

/-- Triangle inequality for the six-term combination occurring in `N₀`. -/
private lemma abs_six_le (a b c d e f : ℝ) :
    |a - b + c + d - e - f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  have h1 : |a - b| ≤ |a| + |b| := abs_sub_le_abs_add_abs a b
  have h2 : |a - b + c| ≤ |a| + |b| + |c| := by
    have h := abs_add_le (a - b) c
    linarith [h1, abs_nonneg c]
  have h3 : |a - b + c + d| ≤ |a| + |b| + |c| + |d| := by
    have h := abs_add_le (a - b + c) d
    linarith [h2, abs_nonneg d]
  have h4 : |a - b + c + d - e| ≤ |a| + |b| + |c| + |d| + |e| := by
    have h := abs_sub_le_abs_add_abs (a - b + c + d) e
    linarith [h3, abs_nonneg e]
  have h5 : |a - b + c + d - e - f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
    have h := abs_sub_le_abs_add_abs (a - b + c + d - e) f
    linarith [h4, abs_nonneg f]
  exact h5

theorem abs_N0_le {α B : ℝ} (hα : 0 < α) (hB : 0 ≤ B)
    {F g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hL12Fstar : |Work.Construction.L12 (Work.Construction.Fstar α) z| ≤ B)
    (hL12g : |Work.Construction.L12 g z| ≤ B)
    (hFb : |F z θ| ≤ B) (hpFb : |Work.Spaces.pth F z θ| ≤ B)
    (hDzFb : |Work.Spaces.Dz F z θ| ≤ B) (hgb : |g z θ| ≤ B)
    (hDzgb : |Work.Spaces.Dz g z θ| ≤ B)
    (hpFstb : |Work.Spaces.pth (Work.Construction.Fstar α) z θ| ≤ B)
    (hDzFstb : |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ B) :
    |Work.Construction.N0 α F g z θ| ≤ (4 / α + 6) * B ^ 2 := by
  have hα1 : (0 : ℝ) < 3 / (2 * α) := by positivity
  have hα2 : (0 : ℝ) < 1 / α := by positivity
  have hs2 : |Work.Construction.s2 θ| ≤ 1 := by
    rw [Work.Construction.s2_eq]
    exact abs_le.mpr (Real.sin_mem_Icc (2 * θ))
  have hc2m : |Work.Construction.c2m θ| ≤ 2 := by
    rw [Work.Construction.c2m_eq]
    have hc := Real.cos_mem_Icc (2 * θ)
    have hs : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    have hs0 : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
    rw [abs_le]
    constructor <;> linarith [hc.1, hc.2, hs, hs0]
  have _hFuse := hFb
  -- unfold `N₀` and name its six summands
  simp only [Work.Construction.N0]
  set v1 : ℝ := (3 / (2 * α)) * Work.Construction.s2 θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ with hv1
  set v2 : ℝ := Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ with hv2
  set v3 : ℝ := (1 / α) * Work.Construction.L12 g z * g z θ with hv3
  set v4 : ℝ := (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 g z
      * Work.Spaces.pth F z θ with hv4
  set v5 : ℝ := Work.Construction.c2m θ * Work.Construction.L12 g z
      * Work.Spaces.Dz F z θ with hv5
  set v6 : ℝ := Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz g z θ with hv6
  -- factorwise bounds on the six summands
  have b1 : |v1| ≤ (3 / (2 * α)) * 1 * B * B := by
    rw [hv1]
    exact abs_mul4_le (a := 3 / (2 * α)) (b := Work.Construction.s2 θ)
      (c := Work.Construction.L12 (Work.Construction.Fstar α) z)
      (d := Work.Spaces.pth (Work.Construction.Fstar α) z θ)
      (A := 3 / (2 * α)) (B' := 1) (C := B) (D := B)
      (by rw [abs_of_pos hα1]) hs2 hL12Fstar hpFstb
  have b2 : |v2| ≤ 2 * B * B := by
    rw [hv2]
    exact abs_mul3_le (a := Work.Construction.c2m θ)
      (b := Work.Construction.L12 (Work.Construction.Fstar α) z)
      (c := Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
      (A := 2) (B' := B) (C := B) hc2m hL12Fstar hDzFstb
  have b3 : |v3| ≤ (1 / α) * B * B := by
    rw [hv3]
    exact abs_mul3_le (a := 1 / α) (b := Work.Construction.L12 g z) (c := g z θ)
      (A := 1 / α) (B' := B) (C := B) (by rw [abs_of_pos hα2]) hL12g hgb
  have b4 : |v4| ≤ (3 / (2 * α)) * 1 * B * B := by
    rw [hv4]
    exact abs_mul4_le (a := 3 / (2 * α)) (b := Work.Construction.s2 θ)
      (c := Work.Construction.L12 g z) (d := Work.Spaces.pth F z θ)
      (A := 3 / (2 * α)) (B' := 1) (C := B) (D := B)
      (by rw [abs_of_pos hα1]) hs2 hL12g hpFb
  have b5 : |v5| ≤ 2 * B * B := by
    rw [hv5]
    exact abs_mul3_le (a := Work.Construction.c2m θ) (b := Work.Construction.L12 g z)
      (c := Work.Spaces.Dz F z θ) (A := 2) (B' := B) (C := B) hc2m hL12g hDzFb
  have b6 : |v6| ≤ 2 * B * B := by
    rw [hv6]
    exact abs_mul3_le (a := Work.Construction.c2m θ)
      (b := Work.Construction.L12 (Work.Construction.Fstar α) z)
      (c := Work.Spaces.Dz g z θ) (A := 2) (B' := B) (C := B) hc2m hL12Fstar hDzgb
  have hmain : |v1 - v2 + v3 + v4 - v5 - v6| ≤ |v1| + |v2| + |v3| + |v4| + |v5| + |v6| :=
    abs_six_le v1 v2 v3 v4 v5 v6
  have hstep : |v1| + |v2| + |v3| + |v4| + |v5| + |v6|
      ≤ (3 / (2 * α)) * 1 * B * B + (2 * B * B) + ((1 / α) * B * B)
        + ((3 / (2 * α)) * 1 * B * B) + (2 * B * B) + (2 * B * B) := by
    linarith [b1, b2, b3, b4, b5, b6]
  have harith : (3 / (2 * α)) * 1 * B * B + (2 * B * B) + ((1 / α) * B * B)
        + ((3 / (2 * α)) * 1 * B * B) + (2 * B * B) + (2 * B * B)
      = (4 / α + 6) * B ^ 2 := by
    have hαne : α ≠ 0 := ne_of_gt hα
    field_simp
    ring
  rw [← harith]
  exact le_trans hmain hstep

end Work.FTS.StrongEps.gRHSBound
end
-- ===== merged: Submission.Work.FTS.StrongEps.gRHSBound.abs_N_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.gRHSBound

theorem abs_N_le {α B : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hB : 0 ≤ B)
    {F Φ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hFb : |F z θ| ≤ B) (hpFb : |Work.Spaces.pth F z θ| ≤ B)
    (hDzFb : |Work.Spaces.Dz F z θ| ≤ B)
    (hRopb : |Work.Construction.Rop α (Work.Construction.PhiTil α F Φ) z θ| ≤ B)
    (hUopb : |Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ| ≤ B)
    (hVopb : |Work.Construction.Vop (Work.Construction.PhiTil α F Φ) z θ| ≤ B)
    (hFKb : |Work.Construction.FK F z| ≤ B) :
    |Work.Construction.N α F Φ z θ| ≤ 8 * B ^ 2 := by
  have hαnn : 0 ≤ α := le_of_lt hα
  -- `N` is a sum of five products; bound each of them by a multiple of `B ^ 2`.
  have ht1 : |2 * Work.Construction.Rop α (Work.Construction.PhiTil α F Φ) z θ * F z θ|
      ≤ 2 * B ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have h : |Work.Construction.Rop α (Work.Construction.PhiTil α F Φ) z θ| * |F z θ|
        ≤ B * B :=
      mul_le_mul hRopb hFb (abs_nonneg _) hB
    nlinarith [h]
  have ht2 : |2 * Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ
        * Work.Spaces.pth F z θ| ≤ 2 * B ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have h : |Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ|
        * |Work.Spaces.pth F z θ| ≤ B * B :=
      mul_le_mul hUopb hpFb (abs_nonneg _) hB
    nlinarith [h]
  have ht3 : |2 * α * Work.Construction.Vop (Work.Construction.PhiTil α F Φ) z θ
        * Work.Spaces.Dz F z θ| ≤ 2 * B ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg hαnn]
    have h1 : α * |Work.Construction.Vop (Work.Construction.PhiTil α F Φ) z θ| ≤ 1 * B :=
      mul_le_mul hα1 hVopb (abs_nonneg _) (by norm_num)
    have h2 : (α * |Work.Construction.Vop (Work.Construction.PhiTil α F Φ) z θ|)
        * |Work.Spaces.Dz F z θ| ≤ (1 * B) * B :=
      mul_le_mul h1 hDzFb (abs_nonneg _) (by linarith)
    nlinarith [h2]
  have ht4 : |(1 / 2) * Work.Construction.s2 θ * Work.Construction.FK F z
        * Work.Spaces.pth F z θ| ≤ (1/2) * B ^ 2 := by
    have hs2 : |Work.Construction.s2 θ| ≤ 1 := by
      simp only [Work.Construction.s2]
      exact Real.abs_sin_le_one (2 * θ)
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1/2))]
    have h1 : |Work.Construction.s2 θ| * |Work.Construction.FK F z| ≤ 1 * B :=
      mul_le_mul hs2 hFKb (abs_nonneg _) (by norm_num)
    have h2 : (|Work.Construction.s2 θ| * |Work.Construction.FK F z|)
        * |Work.Spaces.pth F z θ| ≤ (1 * B) * B :=
      mul_le_mul h1 hpFb (abs_nonneg _) (by linarith)
    nlinarith [h2]
  have ht5 : |Real.sin θ ^ 2 * Work.Construction.FK F z * F z θ| ≤ B ^ 2 := by
    have hsin : |Real.sin θ ^ 2| ≤ 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one θ)
    rw [abs_mul, abs_mul]
    have h1 : |Real.sin θ ^ 2| * |Work.Construction.FK F z| ≤ 1 * B :=
      mul_le_mul hsin hFKb (abs_nonneg _) (by norm_num)
    have h2 : (|Real.sin θ ^ 2| * |Work.Construction.FK F z|) * |F z θ| ≤ (1 * B) * B :=
      mul_le_mul h1 hFb (abs_nonneg _) (by linarith)
    nlinarith [h2]
  change |2 * Work.Construction.Rop α (Work.Construction.PhiTil α F Φ) z θ * F z θ
      - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ * Work.Spaces.pth F z θ
      - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α F Φ) z θ * Work.Spaces.Dz F z θ
      - (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK F z * Work.Spaces.pth F z θ
      - Real.sin θ ^ 2 * Work.Construction.FK F z * F z θ| ≤ 8 * B ^ 2
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith [(abs_le.mp ht1).1, (abs_le.mp ht1).2, (abs_le.mp ht2).1, (abs_le.mp ht2).2,
      (abs_le.mp ht3).1, (abs_le.mp ht3).2, (abs_le.mp ht4).1, (abs_le.mp ht4).2,
      (abs_le.mp ht5).1, (abs_le.mp ht5).2, sq_nonneg B]
  · linarith [(abs_le.mp ht1).1, (abs_le.mp ht1).2, (abs_le.mp ht2).1, (abs_le.mp ht2).2,
      (abs_le.mp ht3).1, (abs_le.mp ht3).2, (abs_le.mp ht4).1, (abs_le.mp ht4).2,
      (abs_le.mp ht5).1, (abs_le.mp ht5).2, sq_nonneg B]

end Work.FTS.StrongEps.gRHSBound
end
-- ===== merged: Submission.Work.FTS.StrongEps.gRHSBound.abs_Nstar_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.gRHSBound

/-- The coefficient `μ + lam + μ·lam` of `D_z g` in `N_*` is bounded by `2` under the
modulation hypotheses `|μ| ≤ 1/2`, `|lam| ≤ 1`. -/
private theorem abs_modCoeff_le {μ lam : ℝ} (hμ : |μ| ≤ 1 / 2) (hlam : |lam| ≤ 1) :
    |μ + lam + μ * lam| ≤ 2 := by
  have h1 : |μ + lam| ≤ |μ| + |lam| := abs_add_le μ lam
  have h2 : |μ * lam| = |μ| * |lam| := abs_mul μ lam
  have hμ0 : (0 : ℝ) ≤ |μ| := abs_nonneg μ
  have hl0 : (0 : ℝ) ≤ |lam| := abs_nonneg lam
  have h3 : |μ| * |lam| ≤ (1 / 2) * 1 := mul_le_mul hμ hlam hl0 (by norm_num)
  calc |μ + lam + μ * lam| ≤ |μ + lam| + |μ * lam| := abs_add_le (μ + lam) (μ * lam)
    _ ≤ (|μ| + |lam|) + |μ| * |lam| := by rw [h2]; exact add_le_add h1 le_rfl
    _ ≤ 2 := by linarith

theorem abs_Nstar_le {μ lam B : ℝ} (hB : 0 ≤ B) (hμ : |μ| ≤ 1 / 2) (hlam : |lam| ≤ 1)
    {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hgb : |g z θ| ≤ B)
    (hDzgb : |Work.Spaces.Dz g z θ| ≤ B) :
    |Work.Construction.Nstar μ lam g z θ| ≤ 3 * B := by
  have hc : |μ + lam + μ * lam| ≤ 2 := abs_modCoeff_le hμ hlam
  have hg0 : (0 : ℝ) ≤ |g z θ| := abs_nonneg _
  have hd0 : (0 : ℝ) ≤ |Work.Spaces.Dz g z θ| := abs_nonneg _
  have h1 : |μ| * |g z θ| ≤ (1 / 2) * B := mul_le_mul hμ hgb hg0 (by norm_num)
  have h2 : |μ + lam + μ * lam| * |Work.Spaces.Dz g z θ| ≤ 2 * B :=
    mul_le_mul hc hDzgb hd0 (by norm_num)
  have hstep : |-μ * g z θ - (μ + lam + μ * lam) * Work.Spaces.Dz g z θ|
      ≤ |μ| * |g z θ| + |μ + lam + μ * lam| * |Work.Spaces.Dz g z θ| := by
    calc |-μ * g z θ - (μ + lam + μ * lam) * Work.Spaces.Dz g z θ|
        ≤ |-μ * g z θ| + |(μ + lam + μ * lam) * Work.Spaces.Dz g z θ| := by
          simpa using abs_sub_le (-μ * g z θ) 0 ((μ + lam + μ * lam) * Work.Spaces.Dz g z θ)
      _ = |μ| * |g z θ| + |μ + lam + μ * lam| * |Work.Spaces.Dz g z θ| := by
          rw [abs_mul, abs_neg, abs_mul]
  simp only [Work.Construction.Nstar]
  linarith

end Work.FTS.StrongEps.gRHSBound
end
-- ===== merged: Submission.Work.FTS.StrongPersist.Degen.bslOpZeroOfUopVopZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `U(Ξ) = V(Ξ) = 0` on the open quadrant implies `L(Ξ) = 0`

The statement and the proof below only involve the vocabulary of `Work.Construction`
(`Uop`, `Vop`), `Work.Elliptic` (`bslOp`, `Lzero`) and `Work.Spaces` (`pz`, `pth`, `pzIter`), so
this module is deliberately *self-contained*: it does not import the area's `StrongPersist.Defs`
(it is not used here), and therefore its verification does not depend on that file's state.

The elliptic operator `L = bslOp α` of (PolarBSL) annihilates every function in the joint kernel
of the two first-order operators

`U(Ξ) = -3Ξ - α z ∂_zΞ`,  `V(Ξ) = ∂_θΞ - tan θ · Ξ`.

The reason is the *exact algebraic identity*

`L(Ξ) = α z · ∂_z(U(Ξ)) + 2 U(Ξ) - ∂_θ(V(Ξ))`

(i.e. `L(Ξ) = α z pz(Uop α Ξ) + 2 Uop α Ξ - pth(Vop Ξ)`).
Indeed `Lzero(Ξ) = -∂_θ(V(Ξ)) - 6Ξ` because the two second-order angular terms cancel against
`∂_θ(V Ξ)`, and the two radial terms of `L` are `α z ∂_z(U Ξ) + 2U Ξ + 6Ξ`.

The statement is *not* vacuous: for every `α > 0` and every constant `c`, the function
`Ξ z θ = c z^{-3/α} / cos θ` satisfies `U Ξ = V Ξ = 0` on the open quadrant `(0,∞) × (0,π/2)`
(it is the general solution, the equations being a first-order system), and `L(Ξ) = 0`.

Both `U` and `V` vanish on the *whole* open quadrant, so the derivatives occurring in the
identity are *not* extra hypotheses: each of the three quantities `U Ξ`, `V Ξ`, `∂_z(U Ξ)`,
`∂_θ(V Ξ)` is a derivative of a function which is identically zero on a neighbourhood of the
point, hence zero.  Concretely, `∂_z(U Ξ)` is computed from the first-order equation
`∂_zΞ = -3Ξ/(α z)` (valid on the quadrant) by the quotient rule, which is why only the
*first* order differentiability `hdiffz`, `hdiffθ` of the statement is needed.
-/

noncomputable section

open scoped Real Topology

namespace Work.FTS.StrongPersist.Degen

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Pointwise consequences of `U(Ξ) = 0` on the open quadrant -/

/-- From `Uop α Ξ = 0` on the open quadrant: `∂_zΞ = -3Ξ/(α z)`. -/
private lemma pz_eq_of_Uop {α : ℝ} (hα : 0 < α) {Ξ : ℝ → ℝ → ℝ}
    (hU : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Construction.Uop α Ξ z θ = 0)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.pz Ξ z θ = -3 * Ξ z θ / (α * z) := by
  have h0 : -3 * Ξ z θ - α * z * Work.Spaces.pz Ξ z θ = 0 := by
    simpa only [Work.Construction.Uop] using hU z θ hz hθ1 hθ2
  have hne : α * z ≠ 0 := mul_ne_zero (ne_of_gt hα) (ne_of_gt hz)
  have h1 : α * z * Work.Spaces.pz Ξ z θ = -3 * Ξ z θ := by linarith
  rw [eq_div_iff hne]
  rw [mul_comm (Work.Spaces.pz Ξ z θ) (α * z)]
  exact h1

/-- From `Uop α Ξ = 0` on the open quadrant: `∂_z²Ξ = (9+3α)Ξ/(α²z²)`.

`∂_z²Ξ` is the derivative of `z' ↦ ∂_zΞ(z')`, and on the open quadrant that function agrees with
`z' ↦ -3Ξ/(α z')` (`pz_eq_of_Uop`), whose derivative at `z` is computed by the quotient rule. -/
private lemma pzIter_two_eq_of_Uop {α : ℝ} (hα : 0 < α) {Ξ : ℝ → ℝ → ℝ}
    (hU : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Construction.Uop α Ξ z θ = 0)
    (hdiffz : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun z' => Ξ z' θ) z)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.pzIter 2 Ξ z θ = (9 + 3 * α) * Ξ z θ / (α ^ 2 * z ^ 2) := by
  have hne : α * z ≠ 0 := mul_ne_zero (ne_of_gt hα) (ne_of_gt hz)
  have hpz : deriv (fun z' => Ξ z' θ) z = -3 * Ξ z θ / (α * z) :=
    pz_eq_of_Uop hα hU hz hθ1 hθ2
  -- on the open quadrant, `z' ↦ ∂_z Ξ(z')` agrees with the explicit quotient
  have hev : (fun z' => Work.Spaces.pz Ξ z' θ) =ᶠ[𝓝 z]
      (fun z' => -3 * Ξ z' θ / (α * z')) :=
    Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hz)
      (fun z' hz' => pz_eq_of_Uop hα hU hz' hθ1 hθ2)
  have hderiv : deriv (fun z' => -3 * Ξ z' θ / (α * z')) z
      = ((-3 * deriv (fun z' => Ξ z' θ) z) * (α * z) - (-3 * Ξ z θ) * α) / (α * z) ^ 2 := by
    have hnum : HasDerivAt (fun z' => -3 * Ξ z' θ) (-3 * deriv (fun z' => Ξ z' θ) z) z :=
      (hdiffz z θ hz hθ1 hθ2).hasDerivAt.const_mul (-3)
    have hden : HasDerivAt (fun z' => α * z') α z := by
      simpa using (hasDerivAt_id z).const_mul α
    have hd := (hnum.div hden hne).deriv
    rw [show ((fun z' => -3 * Ξ z' θ) / (fun z' => α * z'))
        = (fun z' => -3 * Ξ z' θ / (α * z')) from rfl] at hd
    exact hd
  rw [show Work.Spaces.pzIter 2 Ξ z θ = deriv (fun z' => Work.Spaces.pz Ξ z' θ) z from rfl,
    hev.deriv_eq, hderiv, hpz]
  have hs : (α * z) ^ 2 ≠ 0 := pow_ne_zero 2 hne
  have hs' : α ^ 2 * z ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-! ## Pointwise consequence of `V(Ξ) = 0` on the open quadrant -/

/-- From `Vop Ξ = 0` on the open quadrant: `Lzero Ξ = -6Ξ`.

The two second-order angular terms of `Lzero` are `-∂_θ²Ξ + ∂_θ(tan θ · Ξ)`, and they cancel
against `∂_θ(∂_θΞ - tan θ · Ξ) = ∂_θ(V Ξ)`: on the quadrant `∂_θΞ` agrees with
`tan θ · Ξ`, so `∂_θ²Ξ = ∂_θ(tan θ · Ξ)`.  The agreement is an equality of the two functions on
a neighbourhood of `θ` (the whole interval `(0,π/2)`), so it passes to the derivatives —
`Filter.EventuallyEq.deriv_eq` — with no second-order differentiability hypothesis. -/
private lemma Lzero_eq_of_Vop {Ξ : ℝ → ℝ → ℝ}
    (hV : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Construction.Vop Ξ z θ = 0)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Elliptic.Lzero Ξ z θ = -6 * Ξ z θ := by
  have hev : (fun θ' => Work.Spaces.pth Ξ z θ') =ᶠ[𝓝 θ]
      (fun θ' => Real.tan θ' * Ξ z θ') :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds hθ1 hθ2) (fun θ' hθ' => by
      have hv := hV z θ' hz hθ'.1 hθ'.2
      simp only [Work.Construction.Vop, Work.Spaces.pth] at hv ⊢
      linarith)
  have hderiv := hev.deriv_eq
  simp only [Work.Elliptic.Lzero]
  rw [show Work.Spaces.pthIter 2 Ξ z θ = deriv (fun θ' => Work.Spaces.pth Ξ z θ') θ from rfl]
  rw [show Work.Spaces.pth (fun z θ' => Real.tan θ' * Ξ z θ') z θ
        = deriv (fun θ' => Real.tan θ' * Ξ z θ') θ from rfl]
  rw [hderiv]
  ring

/-! ## The main theorem -/

theorem bslOpZeroOfUopVopZero {α : ℝ} (hα : 0 < α) {Ξ : ℝ → ℝ → ℝ}
    (hU : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Construction.Uop α Ξ z θ = 0)
    (hV : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Construction.Vop Ξ z θ = 0)
    (hdiffz : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → DifferentiableAt ℝ (fun z' => Ξ z' θ) z)
    (hdiffθ : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → DifferentiableAt ℝ (fun θ' => Ξ z θ') θ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ξ z θ = 0 := by
  intro z θ hz hθ1 hθ2
  have hLzero : Work.Elliptic.Lzero Ξ z θ = -6 * Ξ z θ :=
    Lzero_eq_of_Vop hV hz hθ1 hθ2
  have hZ : -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ξ z θ
      - (α * (5 + α) * z) * Work.Spaces.pz Ξ z θ = 6 * Ξ z θ := by
    have h1 := pzIter_two_eq_of_Uop hα hU hdiffz hz hθ1 hθ2
    have h2 := pz_eq_of_Uop hα hU hz hθ1 hθ2
    have hne : α * z ≠ 0 := mul_ne_zero (ne_of_gt hα) (ne_of_gt hz)
    have hs : α ^ 2 * z ^ 2 ≠ 0 := by positivity
    rw [h1, h2]
    field_simp
    ring
  simp only [Work.Elliptic.bslOp]
  rw [hLzero]
  linarith

end Work.FTS.StrongPersist.Degen
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45AbndInts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false

/-! ## Elementary facts about `Abnd` -/

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
private lemma sin_two_nonneg_Iθ_prv {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `Abnd α i` is measurable: it is either the constant `1` or
`(α + sin 2·)·sin(2·)^{α/5}`. -/
private lemma Abnd_measurable (α : ℝ) (i : ℕ) : Measurable (Abnd α i) := by
  by_cases h : i = 0
  · have hf : Abnd α i = fun _ : ℝ => (1 : ℝ) := by
      funext θ; rw [Abnd, ite_eq_left h]
    rw [hf]; exact measurable_const
  · have hf : Abnd α i = fun θ : ℝ => (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
      funext θ; rw [Abnd, ite_eq_right (by simpa using h)]
    rw [hf]; fun_prop

/-- Strong measurability of the `η`-weighted integrand. -/
private lemma Abnd_eta_integrand_aesm (α : ℝ) (i : ℕ) :
    AEStronglyMeasurable
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Abnd α i θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
  have h1 : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by fun_prop
  exact (h1.mul ((Abnd_measurable α i).pow_const 2)).aestronglyMeasurable

/-! ## The target -/

theorem T45AbndInts : ∃ D : ℝ, 0 < D ∧ ∀ α ∈ Set.Ioc 0 1,
    (∀ i : ℕ, MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2)
        ≤ D * α ^ (-(1 : ℝ))) ∧
    (∀ i : ℕ, MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2)
        ≤ D * α ^ (-(1 : ℝ))) ∧
    (∀ i : ℕ, 1 ≤ i → MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2)
        ≤ D * α ^ (-(1 : ℝ))) := by
  refine ⟨40000, by norm_num, ?_⟩
  intro α hα
  obtain ⟨hα0, hα1⟩ := hα
  -- `α^{-1} ≥ 1`, so it suffices to bound every integral by `40000`.
  have hαinv : (1 : ℝ) ≤ α ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg_one]; exact (one_le_inv₀ hα0).mpr hα1
  have hD : (40000 : ℝ) ≤ 40000 * α ^ (-(1 : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hαinv (by norm_num : (0 : ℝ) ≤ 40000)
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · -- Family 1: `sin(2θ)^{-η}·Abnd²`, bounded by `4·sin(2θ)^{-η}` since `Abnd ≤ 2`.
    intro i
    have hbase : Integrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (volume.restrict Work.Spaces.Iθ) := by
      have h1 : (-1 : ℝ) < -(Work.Spaces.eta) := by rw [Work.Spaces.eta]; norm_num
      have h2 : (-(Work.Spaces.eta)) ≤ 0 := by rw [Work.Spaces.eta]; norm_num
      exact (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) h1 h2).1
    have hnn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Abnd α i θ) ^ 2) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ_prv hθ
      have h1 := Abnd_nonneg hα0 hθ i
      positivity
    have hle : (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Abnd α i θ) ^ 2)
        ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => 4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ_prv hθ
      have h1 := Abnd_nonneg hα0 hθ i
      have h2 := Abnd_le_two hα0 hα1 hθ i
      have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs _
      have h4 : (Abnd α i θ) ^ 2 ≤ 4 := by nlinarith
      calc (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Abnd α i θ) ^ 2
          ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * 4 := mul_le_mul_of_nonneg_left h4 hsnn
        _ = 4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by ring
    have hbdd : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        ‖(fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Abnd α i θ) ^ 2) θ‖
          ≤ (fun θ : ℝ => 4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) θ := by
      filter_upwards [hle, hnn] with θ hle' hnn'
      rw [Real.norm_of_nonneg hnn']; exact hle'
    refine ⟨(hbase.const_mul 4).mono' (Abnd_eta_integrand_aesm α i) hbdd, ?_⟩
    calc (∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Abnd α i θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, 4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          integral_mono_of_nonneg hnn (hbase.const_mul 4) hle
      _ = 4 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ 40000 := by
          have h1 := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
            (by rw [Work.Spaces.eta]; norm_num) (by rw [Work.Spaces.eta]; norm_num)).2
          have hnum : (100 : ℝ) / (-(Work.Spaces.eta) + 1) = 10000 := by
            rw [Work.Spaces.eta]; norm_num
          rw [hnum] at h1
          linarith [h1]
      _ ≤ 40000 * α ^ (-(1 : ℝ)) := hD
  · -- Family 2: `Abnd²`, bounded by the constant `4`.
    intro i
    have hvol : volume Work.Spaces.Iθ < ⊤ := by
      rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    have hmeas : AEStronglyMeasurable (fun θ : ℝ => (Abnd α i θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) :=
      ((Abnd_measurable α i).pow_const 2).aestronglyMeasurable
    have hbdd : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ‖(Abnd α i θ) ^ 2‖ ≤ 4 := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have h1 := Abnd_nonneg hα0 hθ i
      have h2 := Abnd_le_two hα0 hα1 hθ i
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith
    refine ⟨MeasureTheory.IntegrableOn.of_bound hvol hmeas 4 hbdd, ?_⟩
    have hle : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        (Abnd α i θ) ^ 2 ≤ (fun _ : ℝ => (4 : ℝ)) θ := by
      filter_upwards [hbdd] with θ hθ; simpa using hθ
    have hnn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ : ℝ => (Abnd α i θ) ^ 2) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      positivity
    have h4int : Integrable (fun _ : ℝ => (4 : ℝ)) (volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.integrableOn_const (by rw [lt_top_iff_ne_top] at hvol; exact hvol)
    have hreal : volume.real Work.Spaces.Iθ = Real.pi / 2 := by
      rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
      ring
    calc ∫ θ in Work.Spaces.Iθ, (Abnd α i θ) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, (4 : ℝ) := integral_mono_of_nonneg hnn h4int hle
      _ = 4 * volume.real Work.Spaces.Iθ := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]
      _ = 4 * (Real.pi / 2) := by rw [hreal]
      _ ≤ 40000 * α ^ (-(1 : ℝ)) := by
          have hpi : Real.pi ≤ 4 := Real.pi_le_four
          linarith [hD]
  · -- Family 3: `sin(2θ)^{-γ}·Abnd²` for `i ≥ 1`; now the `sin(2θ)^{2α/5}` of `Abnd²`
    -- is essential.
    intro i hi
    have hi0 : i ≠ 0 := by omega
    have hq1 : (1 : ℝ) ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
    have hq2 : Work.Spaces.gam α < 1 + 2 * (α / 5) := by rw [Work.Spaces.gam]; linarith
    obtain ⟨hint, hbd⟩ := T45Aux.Abnd_rpow_sq_integral_le hα0 hα1 hi0 hq1 hq2
    refine ⟨hint, ?_⟩
    have hden : 2 * (α / 5) - Work.Spaces.gam α + 1 = 3 * α / 10 := by
      rw [Work.Spaces.gam]; ring
    rw [hden] at hbd
    have hkey : (4 : ℝ) * (100 / (3 * α / 10)) = (4000 / 3) / α := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      field_simp
      ring
    rw [hkey] at hbd
    have hfin : (4000 / 3 : ℝ) / α ≤ 40000 * α ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg_one, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr hα0.le)
    linarith [hbd, hfin]

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.dthU_sinSq_weight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted bound for the `D_θ`-iterates of `sin²`

`D_θ φ = sin (2θ) · φ'` (`Work.Spaces.dthU`).  The claim is that

`|D_θ^j (sin²) θ| · sin(2θ)^{-α/5} / (α + sin 2θ) ≤ C`,  `j = 1,…,6`, `0 < α ≤ 1`, `θ ∈ Iθ`,

for a universal constant `C` — i.e. the `α`-dependent singular factor `sin(2θ)^{-α/5}` is
absorbed by the *second order* vanishing of the iterates at the endpoints of `Iθ = [0,π/2]`.

The vanishing is the content of `dthUiter_sin_sq_iter`
(`Work.FTS.PhiStar.Psi0Aux.dthU_iter_elementary_bounds_repaired`): for `j = i+1 ≥ 1`

`D_θ^j (sin²) θ = cos²θ · sin²θ · R_i(cos²θ)`,  `R_i = Σ_k c_k X^k`,  `Σ_k |c_k| ≤ 1095801216`

(`dthUiterPRcoef_sum_le`).  Since `cos²θ · sin²θ = sin²(2θ)/4` this gives
`|D_θ^j (sin²) θ| ≤ 1095801216 · sin²(2θ)`, and then for `s = sin 2θ ∈ [0,1]`

`sin²(2θ) · s^{-α/5}/(α+s) ≤ s^{2-α/5}/(α+s) ≤ s^{1-α/5} ≤ 1`

because `α + s ≥ s` and `1 - α/5 ≥ 4/5 ≥ 0`.  Hence `C = 1095801216` works.
-/

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

/-- `sin (2θ) ≥ 0` for `θ ∈ Iθ = [0, π/2]`. -/
private lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  obtain ⟨h0, h1⟩ := hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩

/-- **The endpoint vanishing of the `D_θ`-iterates of `sin²`.**  For every `j ≥ 1` and
every real `θ`, `|D_θ^j (sin²) θ| ≤ 1095801216 · sin²(2θ)`; the factor `sin²(2θ)` is what
absorbs the singular weight `sin(2θ)^{-α/5}` near the two endpoints of `Iθ`. -/
private lemma dthU_sinSq_le (j : ℕ) (hj : 1 ≤ j) (hj6 : j ≤ 6) (θ : ℝ) :
    |Work.Spaces.dthU^[j] (fun θ : ℝ => Real.sin θ ^ 2) θ|
      ≤ 1095801216 * Real.sin (2 * θ) ^ 2 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i ≤ 6 := by omega
  rw [Work.FTS.PhiStar.Psi0Aux.dthUiter_sin_sq_iter i hi θ]
  have hb : |(Work.FTS.PhiStar.Psi0Aux.dthUiterPR i).eval (Real.cos θ ^ 2)| ≤ 1095801216 := by
    rw [Work.FTS.PhiStar.Psi0Aux.dthUiterPR_eval]
    exact le_trans
      (Work.FTS.PhiStar.Psi0Aux.dthUiter_abs_sum_pow_le _ _ _
        (sq_nonneg (Real.cos θ)) (Real.cos_sq_le_one θ))
      (Work.FTS.PhiStar.Psi0Aux.dthUiterPRcoef_sum_le i hi)
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.cos θ)),
    abs_of_nonneg (sq_nonneg (Real.sin θ))]
  have hcs : Real.cos θ ^ 2 * Real.sin θ ^ 2 = Real.sin (2 * θ) ^ 2 / 4 := by
    rw [Real.sin_two_mul]; ring
  calc Real.cos θ ^ 2 * Real.sin θ ^ 2
        * |(Work.FTS.PhiStar.Psi0Aux.dthUiterPR i).eval (Real.cos θ ^ 2)|
      = Real.sin (2 * θ) ^ 2 / 4
        * |(Work.FTS.PhiStar.Psi0Aux.dthUiterPR i).eval (Real.cos θ ^ 2)| := by rw [hcs]
    _ ≤ Real.sin (2 * θ) ^ 2 * 1095801216 :=
        mul_le_mul (by nlinarith [sq_nonneg (Real.sin (2 * θ))]) hb (abs_nonneg _)
          (sq_nonneg _)
    _ = 1095801216 * Real.sin (2 * θ) ^ 2 := by ring

/-- **The elementary supremum.**  For `0 < α ≤ 1` and `0 ≤ s ≤ 1`,
`s² · s^{-α/5} / (α + s) ≤ 1`:  the singular factor `s^{-α/5}` is defeated by the second
order zero of `s²` at `s = 0` (`s^{2-α/5} = s · s^{1-α/5}` with `1 - α/5 ≥ 4/5 ≥ 0`), and
the denominator `α + s ≥ s` removes the remaining power. -/
private lemma sinSq_mul_rpow_div_le (α s : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : s ^ 2 * s ^ (-(α / 5)) / (α + s) ≤ 1 := by
  rcases eq_or_lt_of_le hs0 with hs | hs
  · rw [← hs]; simp
  · have hs2 : s ^ 2 * s ^ (-(α / 5)) = s ^ (2 - α / 5) := by
      rw [show s ^ 2 = s ^ (2 : ℝ) from (Real.rpow_two s).symm, ← Real.rpow_add hs]
      congr 1
    have hsplit : s ^ (2 - α / 5) = s ^ (1 - α / 5) * s := by
      have h := Real.rpow_add hs (1 - α / 5) 1
      rw [Real.rpow_one] at h
      rw [← h]
      congr 1
      ring
    have h1 : s ^ (1 - α / 5) ≤ 1 :=
      Real.rpow_le_one (le_of_lt hs) hs1 (by linarith)
    have h2 : s / (α + s) ≤ 1 := by
      rw [div_le_one (by linarith : (0 : ℝ) < α + s)]
      linarith
    calc s ^ 2 * s ^ (-(α / 5)) / (α + s)
        = s ^ (1 - α / 5) * s / (α + s) := by rw [hs2, hsplit]
      _ = s ^ (1 - α / 5) * (s / (α + s)) := by rw [mul_div_assoc]
      _ ≤ 1 * 1 := mul_le_mul h1 h2 (div_nonneg (le_of_lt hs) (by linarith)) (by norm_num)
      _ = 1 := by norm_num

theorem dthU_sinSq_weight : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    ∀ (j : ℕ), 1 ≤ j → j ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] (fun θ => Real.sin θ ^ 2) θ|
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) ≤ C := by
  refine ⟨1095801216, by norm_num, ?_⟩
  intro α hα hα1 j hj1 hj6 θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one (2 * θ)
  have hr : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) := Real.rpow_nonneg hs0 _
  have hden : 0 ≤ α + Real.sin (2 * θ) := by linarith
  have h1 : |Work.Spaces.dthU^[j] (fun θ : ℝ => Real.sin θ ^ 2) θ|
        * (Real.sin (2 * θ)) ^ (-(α / 5))
      ≤ (1095801216 * Real.sin (2 * θ) ^ 2) * (Real.sin (2 * θ)) ^ (-(α / 5)) :=
    mul_le_mul_of_nonneg_right (dthU_sinSq_le j hj1 hj6 θ) hr
  calc |Work.Spaces.dthU^[j] (fun θ : ℝ => Real.sin θ ^ 2) θ|
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
      ≤ (1095801216 * Real.sin (2 * θ) ^ 2) * (Real.sin (2 * θ)) ^ (-(α / 5))
          / (α + Real.sin (2 * θ)) := div_le_div_of_nonneg_right h1 hden
    _ = 1095801216 * (Real.sin (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(α / 5))
          / (α + Real.sin (2 * θ))) := by ring
    _ ≤ 1095801216 * 1 :=
        mul_le_mul_of_nonneg_left (sinSq_mul_rpow_div_le α _ hα hα1 hs0 hs1) (by norm_num)
    _ = 1095801216 := by norm_num

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.HardSlotAux.IbpCutoffAnyQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `IbpCutoffAnyQ` — the cutoff angular integration by parts for an arbitrary real exponent

`Work.H2.T1Q.IbpCutoff` proves the angular integration by parts

  `∫_θ sin(2θ)^{-q}·(χ hf)·(sin(2θ)·hv')·hv
      = -∫_θ sin(2θ)^{-q}·(χ·((1/2) sin(2θ) hf' + (1-q) cos(2θ) hf)
                              + (1/2) sin(2θ) χ' hf)·hv²`

for `χ` smooth and vanishing off `[δ, π/2-δ]` (`0 < δ ≤ π/4`), `hf`, `hv` of class `C¹` on the
open interval `(0, π/2)`, **under the extra hypothesis `0 < q`**.  That hypothesis is never used
in the proof — the `rpow` factor `sin(2θ)^{-q}` is only ever handled on the compact support of
`χ`, where `sin(2θ) > 0` regardless of the sign of `q` (the auxiliary lemmas
`ibpCutoff_integrable`, `ibpCutoff_deriv` and the two `tendsto`-to-zero lemmas of
`Submission/Work/H2/T1Q/IbpCutoff.lean` are all stated for an arbitrary real `q`).

This file therefore records the same identity for an **arbitrary real `q`**, with the two
integrands named through `IbpG`/`IbpK`; it is the form needed by the `N6` hard-slot analysis,
where the slots carry the exponents `η = 99/100` and `γ = 1 + α/10 > 1` (so in particular
`q > 1` for the `γ`-slots, well outside the reach of the `IbpCutoff` statement as published).

The proof is a verbatim replay of the body of `Work.H2.T1Q.IbpCutoff` with the unused hypothesis
deleted.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.HardSlotAux

theorem IbpCutoffAnyQ {q : ℝ} {χ hf hv : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ π / 4)
    (hχ0 : ∀ θ : ℝ, θ ≤ δ → χ θ = 0)
    (hχ2 : ∀ θ : ℝ, π / 2 - δ ≤ θ → χ θ = 0)
    (hf' : ContDiffOn ℝ 1 hf (Set.Ioo 0 (π / 2)))
    (hv' : ContDiffOn ℝ 1 hv (Set.Ioo 0 (π / 2))) :
    MeasureTheory.IntegrableOn (Work.H2.T1Q.IbpG q χ hf hv) Work.Spaces.Iθ
      ∧ ∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpG q χ hf hv θ
        = -∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpK q χ hf hv θ := by
  have hpi : (0 : ℝ) < π / 2 := by positivity
  obtain ⟨hIntG, hIntK⟩ :=
    Work.H2.T1Q.ibpCutoff_integrable (q := q) hχ hδ hδ4 hχ0 hχ2 hf' hv'
  have hIcc : ∀ u : ℝ → ℝ, ∫ θ in Work.Spaces.Iθ, u θ = ∫ θ in (0 : ℝ)..(π / 2), u θ := by
    intro u
    rw [show Work.Spaces.Iθ = Set.Icc 0 (π / 2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi.le]
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      HasDerivAt (Work.H2.T1Q.IbpPrim q χ hf hv)
        (Work.H2.T1Q.IbpG q χ hf hv θ + Work.H2.T1Q.IbpK q χ hf hv θ) θ := by
    intro θ hθ
    exact Work.H2.T1Q.ibpCutoff_deriv hθ (hχ.contDiffAt.differentiableAt (by simp))
      ((hf'.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ))
      ((hv'.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ))
  have hint : IntervalIntegrable
      (fun θ => Work.H2.T1Q.IbpG q χ hf hv θ + Work.H2.T1Q.IbpK q χ hf hv θ)
      volume 0 (π / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hpi.le]
    exact hIntG.add hIntK
  have hFTC : ∫ θ in (0 : ℝ)..(π / 2),
      (Work.H2.T1Q.IbpG q χ hf hv θ + Work.H2.T1Q.IbpK q χ hf hv θ) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi hderiv hint
      (Work.H2.T1Q.ibpCutoff_prim_tendsto_zero_right hδ hχ0)
      (Work.H2.T1Q.ibpCutoff_prim_tendsto_zero_left hδ hχ2)
    simpa using h
  have hsplit : ∫ θ in Work.Spaces.Iθ,
        (Work.H2.T1Q.IbpG q χ hf hv θ + Work.H2.T1Q.IbpK q χ hf hv θ)
      = (∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpG q χ hf hv θ)
        + ∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpK q χ hf hv θ :=
    MeasureTheory.integral_add hIntG hIntK
  have hsum : (∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpG q χ hf hv θ)
      + ∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpK q χ hf hv θ = 0 := by
    rw [← hsplit, hIcc, hFTC]
  exact ⟨hIntG, by linarith⟩

end Work.FTS.StrongPersist.N6Trans.HardSlotAux
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.cosWeightPrim_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# Bounding the primitive of `sin(2θ)^{-η}/cos(θ)^4`

The goal is the single-`θ` estimate
`(∫_0^θ sin(2s)^{-η}/cos(s)^4 ds)^2 ≤ C · sin(2θ)^{-2η}/cos(θ)^6`.

The whole proof rests on the explicit comparison function
`Φ(θ) = 50 · sin(2θ)^{1-η} / cos(θ)^4`, whose derivative
`Φ'(θ) = 50 · sin(2θ)^{-η} · (2(1-η)cos(2θ) + 8 sin²θ) / cos(θ)^4`
dominates the integrand `g(θ) = sin(2θ)^{-η}/cos(θ)^4` pointwise on `(0, π/2)`, because
`2(1-η)cos(2θ) + 8 sin²θ = 2(1-η) + 4(1+η) sin²θ ≥ 2(1-η) = 1/50` (using `η = 99/100`).
Hence `∫_0^θ g ≤ Φ(θ) - Φ(0) = Φ(θ)`, and `Φ(θ)^2 ≤ 10^4 · sin(2θ)^{-2η}/cos(θ)^6`
since `Φ(θ)^2 = 10^4 sin²θ · sin(2θ)^{-2η}/cos(θ)^6` and `sin²θ ≤ 1`.
-/











end Work.FTS_EllLimOK.PkgJets
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.ctSmall_integral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set

/-!
# The `cos`-weight integrand near `s = 0`: `∫_0^T sin(2s)^{-η}/cos(s)^4 ds ≤ 1600`

The integrand `ctF s = sin(2s)^{-η}/cos(s)^4` (`η = 99/100`) has a single integrable
singularity at `s = 0`.  On the quarter interval `[0, π/4]`:

* `cos s ≥ cos(π/4) = √2/2`, hence `1/cos(s)^4 ≤ 4`;
* Jordan's inequality `sin(2s) ≥ (4/π) s` (applied to `2s ∈ [0, π/2]`) gives, since the
  exponent `-η` is negative, `sin(2s)^{-η} ≤ (π/4)^η s^{-η}` (with `0^{-η} = 0` at `s = 0`).

So `ctF s ≤ 4 (π/4)^η s^{-η}`, and the primitive of `s^{-η}` is `s^{1-η}/(1-η) = 100 s^{1/100}`.
For `T ≤ π/4` this gives

`∫_0^T ctF ≤ 4 (π/4)^η · 100 (π/4)^{1/100} = 400 · (π/4) = 100π ≤ 1600`.

The integrability statement is inherited from `cw_integrable` (`ctF` is literally `cwG`).
-/




end Work.FTS_EllLimOK.PkgJets
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.pinWeights =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.PkgJets

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The weights -/

/-- `ν θ = sin(2θ)^{-η}` with `η = Work.Spaces.eta = 99/100`. -/
def wNu (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- `W₁ θ = sin(2θ)^{-η}/cos⁴θ`: the weight of the slot `Ψ/cos θ` (i.e. of `A = cos θ·Ψ`). -/
def wOne (θ : ℝ) : ℝ := wNu θ / (Real.cos θ) ^ 4


/-- The primitive `Λ θ = ∫_0^θ W₁` of `W₁` from the regular end `θ = 0`. -/
def wLam (θ : ℝ) : ℝ := ∫ s in (0 : ℝ)..θ, wOne s

/-! ## Elementary facts -/

theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem cos_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩









@[simp] theorem wOne_zero : wOne 0 = 0 := by
  have h : (-(Work.Spaces.eta)) ≠ 0 := by norm_num [Work.Spaces.eta]
  simp [wOne, wNu, Real.zero_rpow, h]

@[simp] theorem wLam_zero : wLam 0 = 0 := by simp [wLam]



/-! ## Integrability of `W₁` near `0`, and the primitive -/





end Work.FTS_EllLimOK.PkgJets
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.VopTransfer.contDiff_Lop_iterate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.VopTransfer

/-- Helper: `Lop` sends `C^∞` functions (in the sense of `∀ k, ContDiff ℝ k`) to
`C^∞` functions.  The derivative lowers the order by one and the multiplication by
`sin (2θ)` restores it. -/
theorem contDiff_Lop (u : ℝ → ℝ) (hu : ∀ k : ℕ, ContDiff ℝ k u) :
    ∀ k : ℕ, ContDiff ℝ k (Work.Spaces.Lop u) := by
  intro k
  change ContDiff ℝ k ((fun θ : ℝ => Real.sin (2 * θ)) * deriv u)
  have hd : ContDiff ℝ k (deriv u) :=
    -- `ContDiff.deriv'` lowers the order by one
    ContDiff.deriv' (𝕜 := ℝ) (f := u) (n := (k : WithTop ℕ∞)) (hu (k + 1))
  have hsin : ContDiff ℝ k (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
  exact hsin.mul hd

theorem contDiff_Lop_iterate (u : ℝ → ℝ) (hu : ∀ k : ℕ, ContDiff ℝ k u) (r : ℕ) :
    ∀ k : ℕ, ContDiff ℝ k (Work.Spaces.Lop^[r] u) := by
  induction r with
  | zero => simpa using hu
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      exact contDiff_Lop _ ih

end Work.FTS_EllLimOK.VopTransfer
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Pointwise and derivative bounds for the profile `AK`

`AK α z θ = (Γ(θ)/c(α)) · 2z²/(1+z)³` (tex 1357 of Elgindi's paper): the profile
whose `L₁₂`-evaluations supply the modulation constants.  Everything here rests on
the two coarse numerical facts about the angular data, both already available in the
workspace:

* `Γ(θ) = (sin θ cos²θ)^{α/3} ∈ [0,1]` on `Iθ = [0,π/2]` (`Work.Spaces.Gam_bounds`),
* `1/10 ≤ c(α) ≤ 10` (`Work.Spaces.c_bounds`).

Hence `|Γ(θ)/c(α)| ≤ 10` on `Iθ`; the radial factor `2z²/(1+z)³` is `≤ 2z²`, and its
`z`-derivative is `2(2z-z²)/(1+z)⁴`, which is bounded by `1` on `z ≥ 0`
(`(1+z)⁴ - (4z+2z²) = 1 + z²(2+z)² ≥ 0`).  Both statements then follow with room to
spare.
-/

namespace Work.FTS_RegExport.RXR1.HJ

/-- The angular factor of `AK` is bounded by `10`: `Γ ∈ [0,1]` and `c(α) ≥ 1/10`. -/
theorem gam_div_c_abs_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 := by
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  obtain ⟨hc1, _⟩ := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hnonneg : 0 ≤ Work.Spaces.Gam α θ / Work.Spaces.c α :=
    div_nonneg hG0 (le_of_lt hcpos)
  rw [abs_of_nonneg hnonneg, div_le_iff₀ hcpos]
  nlinarith

/-- The `z`-derivative of the radial factor `2z²/(1+z)³` of `AK`. -/
theorem hasDerivAt_akFactor {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3)
      (2 * (2 * z - z ^ 2) / (1 + z) ^ 4) z := by
  have hnum : HasDerivAt (fun z' : ℝ => 2 * z' ^ 2) (4 * z) z := by
    have hp : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
      simpa using (hasDerivAt_pow 2 z)
    have h2 := hp.const_mul (2 : ℝ)
    convert h2 using 1
    ring
  have hden : HasDerivAt (fun z' : ℝ => (1 + z') ^ 3) (3 * (1 + z) ^ 2) z := by
    have h1 : HasDerivAt (fun z' : ℝ => 1 + z') (1 : ℝ) z := by
      simpa using (hasDerivAt_id z).const_add (1 : ℝ)
    have h2 := (hasDerivAt_pow 3 (1 + z)).comp z h1
    have h3 : ((fun x : ℝ => x ^ 3) ∘ (fun z' : ℝ => 1 + z'))
        = fun z' : ℝ => (1 + z') ^ 3 := rfl
    rw [h3] at h2
    convert h2 using 1
    ring
  have hne : (1 + z) ^ 3 ≠ 0 := by positivity
  have hdiv := hnum.div hden hne
  convert hdiv using 1
  field_simp
  ring

/-- Numerical bound `|2(2z-z²)| ≤ (1+z)⁴` for `z ≥ 0`, i.e. `4z+2z² ≤ (1+z)⁴`. -/
theorem abs_two_mul_two_z_le {z : ℝ} (hz : 0 ≤ z) :
    |2 * (2 * z - z ^ 2)| ≤ (1 + z) ^ 4 := by
  have h1 : |2 * z - z ^ 2| ≤ 2 * z + z ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg z]
  have h2 : 4 * z + 2 * z ^ 2 ≤ (1 + z) ^ 4 := by
    have e : (1 + z) ^ 4 - (4 * z + 2 * z ^ 2) = 1 + z ^ 2 * (2 + z) ^ 2 := by ring
    nlinarith [sq_nonneg (z * (2 + z)), sq_nonneg z, e]
  have h3 : |2 * (2 * z - z ^ 2)| = 2 * |2 * z - z ^ 2| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h3]
  linarith

theorem AKBounds {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → |Work.Construction.AK α z θ| ≤ 20 * z ^ 2) ∧
    (∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z →
      ∃ d : ℝ, HasDerivAt (fun z' : ℝ => Work.Construction.AK α z' θ) d z ∧ |d| ≤ 10) := by
  constructor
  · intro θ hθ z hz
    have hGc := gam_div_c_abs_le hα hα1 hθ
    have hden : (0 : ℝ) < (1 + z) ^ 3 := by positivity
    have hden1 : (1 : ℝ) ≤ (1 + z) ^ 3 := by nlinarith [sq_nonneg z, sq_nonneg (1 + z)]
    have hkey : |2 * z ^ 2 / (1 + z) ^ 3| = 2 * z ^ 2 / (1 + z) ^ 3 := by
      rw [abs_of_nonneg (by positivity)]
    rw [Work.Construction.AK, abs_mul, hkey]
    have h1 : |Work.Spaces.Gam α θ / Work.Spaces.c α| * (2 * z ^ 2 / (1 + z) ^ 3)
        ≤ 10 * (2 * z ^ 2 / (1 + z) ^ 3) :=
      mul_le_mul_of_nonneg_right hGc (by positivity)
    have h2 : 10 * (2 * z ^ 2 / (1 + z) ^ 3) ≤ 10 * (2 * z ^ 2) := by
      have : 2 * z ^ 2 / (1 + z) ^ 3 ≤ 2 * z ^ 2 := by
        rw [div_le_iff₀ hden]
        nlinarith
      linarith
    linarith
  · intro θ hθ z hz
    have hGc := gam_div_c_abs_le hα hα1 hθ
    have hg := hasDerivAt_akFactor hz
    refine ⟨(Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * (2 * z - z ^ 2) / (1 + z) ^ 4),
      ?_, ?_⟩
    · have h := hg.const_mul (Work.Spaces.Gam α θ / Work.Spaces.c α)
      simpa only [Work.Construction.AK] using h
    · have hden : (0 : ℝ) < (1 + z) ^ 4 := by positivity
      have hkey := abs_two_mul_two_z_le (le_of_lt hz)
      rw [abs_mul]
      have h4 : |2 * (2 * z - z ^ 2) / (1 + z) ^ 4|
          = |2 * (2 * z - z ^ 2)| / (1 + z) ^ 4 := by
        rw [abs_div, abs_of_pos hden]
      rw [h4]
      have h5 : |Work.Spaces.Gam α θ / Work.Spaces.c α|
            * (|2 * (2 * z - z ^ 2)| / (1 + z) ^ 4) ≤ 10 * 1 := by
        have h6 : |2 * (2 * z - z ^ 2)| / (1 + z) ^ 4 ≤ 1 := by
          rw [div_le_one hden]
          exact hkey
        have h7 : 0 ≤ |2 * (2 * z - z ^ 2)| / (1 + z) ^ 4 := by positivity
        nlinarith
      linarith

end Work.FTS_RegExport.RXR1.HJ
end
