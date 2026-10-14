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
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Have
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.ClassC.ModeEnergyDefs =====
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

/-! ## The radial weight and its derivative formulas -/

/-- `rw z = (1+z)^4/z^2`.  This is `(z·w(z))²`, with the singular factor `1/z^4` of `w²` split
off so that `rw z · (deriv a z)² = (z ∂_z a)² · w(z)²`. -/
def rw (z : ℝ) : ℝ := (1 + z) ^ 4 / z ^ 2

/-- The explicit formula for `d/dz rw` (with the junk value `0` at `z = 0`). -/
def rwb (z : ℝ) : ℝ := (1 + z) ^ 3 * (2 * z - 2) / z ^ 3

/-- The explicit formula for `d²/dz² rw`. -/
def rwbb (z : ℝ) : ℝ := (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4

/-- The explicit formula for `d/dz (rw z / z)`, i.e. for `d/dz (z w(z)²)`. -/
def rwc (z : ℝ) : ℝ := (1 + z) ^ 3 * (z - 3) / z ^ 4

/-- The boundary term of the integration by parts:
`flux α a z = α² rw z (∂_z a) a - (α²/2) rwb z a² + (α(5+α)/2) (rw z / z) a²`. -/
def flux (α : ℝ) (a : ℝ → ℝ) : ℝ → ℝ :=
  fun z => α ^ 2 * (rw z * (deriv a z * a z)) - (α ^ 2 / 2) * (rwb z * (a z) ^ 2)
    + ((α * (5 + α)) / 2) * (rw z / z) * (a z) ^ 2

lemma rw_eq_w (z : ℝ) : rw z = (z * Work.Spaces.w z) ^ 2 := by
  rw [Work.Spaces.w, rw]
  field_simp


/-- `flux` vanishes at `z = 0` (all three coefficients are multiples of `z`-powers). -/
lemma flux_zero (α : ℝ) (a : ℝ → ℝ) : flux α a 0 = 0 := by
  simp [flux, rw, rwb]

/-! ## The derivative of the weight -/

lemma hasDerivAt_rw {z : ℝ} (hz : z ≠ 0) : HasDerivAt rw (rwb z) z := by
  have h12 := (hasDerivAt_id z).add_const (1:ℝ)
  have h34 := h12.pow 4
  have h := h34.div (hasDerivAt_pow 2 z) (pow_ne_zero 2 hz)
  convert h using 1
  · -- the function
    funext t
    simp only [Pi.div_apply, Pi.pow_apply, Pi.add_apply, id_eq]
    rw [show rw t = (1 + t) ^ 4 / t ^ 2 from rfl]
    ring_nf
  · -- the derivative value
    simp only [Pi.pow_apply, Pi.add_apply, Pi.mul_apply, id_eq]
    rw [show rwb z = (1 + z) ^ 3 * (2 * z - 2) / z ^ 3 from rfl]
    field_simp
    ring_nf

lemma hasDerivAt_rwb {z : ℝ} (hz : z ≠ 0) : HasDerivAt rwb (rwbb z) z := by
  have h12 : HasDerivAt (fun t : ℝ => t + 1) 1 z := (hasDerivAt_id z).add_const 1
  have h2 : HasDerivAt (fun t : ℝ => 2 * t - 2) 2 z := by
    have h := ((hasDerivAt_id z).const_mul (2:ℝ)).sub_const 2
    convert h using 1
    · funext x; simp
    · ring
  have hnum := (h12.pow 3).mul h2
  have h := hnum.div (hasDerivAt_pow 3 z) (pow_ne_zero 3 hz)
  convert h using 1
  · -- the function
    funext t
    simp only [Pi.div_apply, Pi.pow_apply, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, id_eq]
    rw [show rwb t = (1 + t) ^ 3 * (2 * t - 2) / t ^ 3 from rfl]
    ring_nf
  · -- the derivative value
    simp only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, id_eq]
    rw [show rwbb z = (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4 from rfl]
    field_simp
    ring_nf

lemma hasDerivAt_rwDiv {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (fun t : ℝ => rw t / t) (rwc z) z := by
  have h := (hasDerivAt_rw hz).div (hasDerivAt_id z) hz
  convert h using 1
  · -- the function
    funext t
    simp only [Pi.div_apply, id_eq]
  · -- the derivative value
    simp only [Pi.div_apply, id_eq]
    rw [show rwc z = (1 + z) ^ 3 * (z - 3) / z ^ 4 from rfl,
      show rwb z = (1 + z) ^ 3 * (2 * z - 2) / z ^ 3 from rfl,
      show rw z = (1 + z) ^ 4 / z ^ 2 from rfl]
    field_simp
    ring_nf

/-! ## The two bounds that make the identity coercive -/

lemma abs_rwbb_le {z : ℝ} (hz : 0 < z) : |rwbb z| ≤ 6 * (Work.Spaces.w z) ^ 2 := by
  have hz4 : (0:ℝ) < z ^ 4 := by positivity
  have hpos : 0 ≤ (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) :=
    mul_nonneg (sq_nonneg _) (by nlinarith [sq_nonneg (z - 1)])
  have hnum : (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) ≤ 6 * (1 + z) ^ 4 := by
    have h1 : (0:ℝ) < 4 * z * (1 + z) ^ 2 * (z + 4) :=
      mul_pos (mul_pos (mul_pos (by norm_num) hz) (pow_pos (by linarith) 2)) (by linarith)
    nlinarith [h1]
  calc |rwbb z| = ((1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6)) / z ^ 4 := by
        rw [rwbb, abs_div, abs_of_pos hz4, abs_of_nonneg hpos]
    _ ≤ 6 * (1 + z) ^ 4 / z ^ 4 := by gcongr
    _ = 6 * (Work.Spaces.w z) ^ 2 := by rw [Work.Spaces.w]; ring

lemma abs_rwc_le {z : ℝ} (hz : 0 < z) : |rwc z| ≤ 3 * (Work.Spaces.w z) ^ 2 := by
  have hz4 : (0:ℝ) < z ^ 4 := by positivity
  have h3 : |z - 3| ≤ 3 * (1 + z) := by
    rw [abs_le]
    constructor <;> linarith
  have hnum : |(1 + z) ^ 3 * (z - 3)| ≤ 3 * (1 + z) ^ 4 := by
    calc |(1 + z) ^ 3 * (z - 3)| = (1 + z) ^ 3 * |z - 3| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (1 + z) ^ 3 * (3 * (1 + z)) := by gcongr
      _ = 3 * (1 + z) ^ 4 := by ring
  calc |rwc z| = |(1 + z) ^ 3 * (z - 3)| / z ^ 4 := by
        rw [rwc, abs_div, abs_of_pos hz4]
    _ ≤ 3 * (1 + z) ^ 4 / z ^ 4 := by gcongr
    _ = 3 * (Work.Spaces.w z) ^ 2 := by rw [Work.Spaces.w]; ring

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.paperHardyIter =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Filter
open scoped Topology

/-! ### Elementary auxiliary facts -/

/-- AM-GM in the form `2ab ≤ t a² + b²/t` for `t > 0`. -/
private lemma two_mul_le_mul_sq_add_div_sq_prv {t a b : ℝ} (ht : 0 < t) :
    2 * a * b ≤ t * a ^ 2 + b ^ 2 / t := by
  have h : 0 ≤ (t * a - b) ^ 2 := sq_nonneg _
  rw [show t * a ^ 2 + b ^ 2 / t = (t ^ 2 * a ^ 2 + b ^ 2) / t by
    field_simp]
  rw [le_div_iff₀ ht]
  nlinarith [h]




/-- Weighted integration by parts for the Hardy inequality, `C^1` version: for `0 < y < x₁` and
`v` of class `C^1` on the closed interval `[y,x₁]`,

`(1+γ)/2 * ∫_y^{x₁} x^{2k-γ} v²
   = ∫_y^{x₁} x^{2k-γ} v (x v' + (k+1) v) - ½(x₁^{2k+1-γ} v(x₁)²) + ½(y^{2k+1-γ} v(y)²)`.

(This is the `C^1` version of `hardyIter_ibp`; the latter assumes analyticity, which is not
available here.) -/
private theorem ibp_fts {v : ℝ → ℝ} {γ x₁ y : ℝ} (k : ℕ) (hy : 0 < y) (hyx : y < x₁)
    (hv : ContDiffOn ℝ 1 v (Set.Icc y x₁)) :
    (1 + γ) / 2 * (∫ x in y..x₁, x ^ (2 * (k : ℝ) - γ) * v x ^ 2)
      = (∫ x in y..x₁, x ^ (2 * (k : ℝ) - γ) * v x * (x * deriv v x + ((k : ℝ) + 1) * v x))
        - 1 / 2 * (x₁ ^ (2 * (k : ℝ) + 1 - γ) * v x₁ ^ 2)
        + 1 / 2 * (y ^ (2 * (k : ℝ) + 1 - γ) * v y ^ 2) := by
  have hyle : y ≤ x₁ := le_of_lt hyx
  have hpos : ∀ x ∈ Set.Icc y x₁, 0 < x := fun x hx => lt_of_lt_of_le hy hx.1
  have hdv : ∀ x ∈ Set.Ioo y x₁, HasDerivAt v (deriv v x) x := by
    intro x hx
    have hmem : Set.Icc y x₁ ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
    exact ((hv.contDiffAt hmem).differentiableAt (by simp)).hasDerivAt
  have hdvW : ∀ x ∈ Set.Ioo y x₁, derivWithin v (Set.Icc y x₁) x = deriv v x :=
    fun x hx => derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)
  have hcontv : ContinuousOn v (Set.Icc y x₁) := hv.continuousOn
  have hcontdvW : ContinuousOn (derivWithin v (Set.Icc y x₁)) (Set.Icc y x₁) :=
    hv.continuousOn_derivWithin (uniqueDiffOn_Icc hyx) le_rfl
  have hcont_rpow_p : ContinuousOn (fun x : ℝ => x ^ (2 * (k : ℝ) + 1 - γ)) (Set.Icc y x₁) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (hpos x hx)))
  have hcont_rpow_a : ContinuousOn (fun x : ℝ => x ^ (2 * (k : ℝ) - γ)) (Set.Icc y x₁) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (hpos x hx)))
  have hcontDp : ContinuousOn
      (fun x : ℝ => (2 * (k : ℝ) + 1 - γ) * x ^ (2 * (k : ℝ) - γ) * v x ^ 2
        + 2 * (x ^ (2 * (k : ℝ) + 1 - γ) * v x * derivWithin v (Set.Icc y x₁) x))
      (Set.Icc y x₁) := by
    refine ((continuousOn_const.mul hcont_rpow_a).mul (hcontv.pow 2)).add ?_
    exact ((hcont_rpow_p.mul hcontv).mul hcontdvW).const_mul 2
  have hII : IntervalIntegrable
      (fun x : ℝ => (2 * (k : ℝ) + 1 - γ) * x ^ (2 * (k : ℝ) - γ) * v x ^ 2
        + 2 * (x ^ (2 * (k : ℝ) + 1 - γ) * v x * derivWithin v (Set.Icc y x₁) x)) volume y x₁ :=
    ContinuousOn.intervalIntegrable_of_Icc hyle hcontDp
  have hderivP : ∀ x ∈ Set.Ioo y x₁,
      HasDerivAt (fun x : ℝ => x ^ (2 * (k : ℝ) + 1 - γ) * v x ^ 2)
        ((2 * (k : ℝ) + 1 - γ) * x ^ (2 * (k : ℝ) - γ) * v x ^ 2
          + 2 * (x ^ (2 * (k : ℝ) + 1 - γ) * v x * derivWithin v (Set.Icc y x₁) x)) x := by
    intro x hx
    have hx0 : 0 < x := hpos x ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have hexp : 2 * (k : ℝ) + 1 - γ - 1 = 2 * (k : ℝ) - γ := by ring
    have hp : HasDerivAt (fun x : ℝ => x ^ (2 * (k : ℝ) + 1 - γ))
        ((2 * (k : ℝ) + 1 - γ) * x ^ (2 * (k : ℝ) - γ)) x := by
      have h := Real.hasDerivAt_rpow_const (x := x) (p := 2 * (k : ℝ) + 1 - γ)
        (Or.inl (ne_of_gt hx0))
      rwa [hexp] at h
    have hvsq : HasDerivAt (fun x : ℝ => v x ^ 2) (2 * v x * deriv v x) x := by
      convert (hdv x hx).pow 2 using 1
      ring
    have hmain := hp.mul hvsq
    have hval : (2 * (k : ℝ) + 1 - γ) * x ^ (2 * (k : ℝ) - γ) * v x ^ 2
        + x ^ (2 * (k : ℝ) + 1 - γ) * (2 * v x * deriv v x)
        = (2 * (k : ℝ) + 1 - γ) * x ^ (2 * (k : ℝ) - γ) * v x ^ 2
          + 2 * (x ^ (2 * (k : ℝ) + 1 - γ) * v x * derivWithin v (Set.Icc y x₁) x) := by
      rw [hdvW x hx]; ring
    rwa [hval] at hmain
  have hcontP : ContinuousOn (fun x : ℝ => x ^ (2 * (k : ℝ) + 1 - γ) * v x ^ 2) (Set.Icc y x₁) :=
    hcont_rpow_p.mul (hcontv.pow 2)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hyle hcontP hderivP hII
  have hFTC' : (∫ x in y..x₁, (2 * (k : ℝ) + 1 - γ) * x ^ (2 * (k : ℝ) - γ) * v x ^ 2
        + 2 * (x ^ (2 * (k : ℝ) + 1 - γ) * v x * derivWithin v (Set.Icc y x₁) x))
      = x₁ ^ (2 * (k : ℝ) + 1 - γ) * v x₁ ^ 2 - y ^ (2 * (k : ℝ) + 1 - γ) * v y ^ 2 := by
    simpa using hFTC
  have hpt : ∀ x ∈ Set.Icc y x₁,
      (2 * (k : ℝ) + 1 - γ) * x ^ (2 * (k : ℝ) - γ) * v x ^ 2
        + 2 * (x ^ (2 * (k : ℝ) + 1 - γ) * v x * derivWithin v (Set.Icc y x₁) x)
      = 2 * (x ^ (2 * (k : ℝ) - γ) * v x
            * (x * derivWithin v (Set.Icc y x₁) x + ((k : ℝ) + 1) * v x))
        - (1 + γ) * (x ^ (2 * (k : ℝ) - γ) * v x ^ 2) := by
    intro x hx
    have hx0 : 0 < x := hpos x hx
    have hpow : x ^ (2 * (k : ℝ) + 1 - γ) = x ^ (2 * (k : ℝ) - γ) * x := by
      rw [show 2 * (k : ℝ) + 1 - γ = (2 * (k : ℝ) - γ) + 1 by ring, Real.rpow_add hx0,
        Real.rpow_one]
    rw [hpow]
    ring
  have hcontG1 : ContinuousOn
      (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * v x
        * (x * derivWithin v (Set.Icc y x₁) x + ((k : ℝ) + 1) * v x)) (Set.Icc y x₁) :=
    (hcont_rpow_a.mul hcontv).mul
      ((continuousOn_id.mul hcontdvW).add (hcontv.const_mul _))
  have hcontG2 : ContinuousOn (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * v x ^ 2) (Set.Icc y x₁) :=
    hcont_rpow_a.mul (hcontv.pow 2)
  have hII1 : IntervalIntegrable (fun x : ℝ => 2 * (x ^ (2 * (k : ℝ) - γ) * v x
      * (x * derivWithin v (Set.Icc y x₁) x + ((k : ℝ) + 1) * v x))) volume y x₁ :=
    (ContinuousOn.intervalIntegrable_of_Icc hyle hcontG1).const_mul 2
  have hII2 : IntervalIntegrable (fun x : ℝ => (1 + γ) * (x ^ (2 * (k : ℝ) - γ) * v x ^ 2))
      volume y x₁ :=
    (ContinuousOn.intervalIntegrable_of_Icc hyle hcontG2).const_mul (1 + γ)
  have hDp_eq : (∫ x in y..x₁, (2 * (k : ℝ) + 1 - γ) * x ^ (2 * (k : ℝ) - γ) * v x ^ 2
        + 2 * (x ^ (2 * (k : ℝ) + 1 - γ) * v x * derivWithin v (Set.Icc y x₁) x))
      = ∫ x in y..x₁, (2 * (x ^ (2 * (k : ℝ) - γ) * v x
            * (x * derivWithin v (Set.Icc y x₁) x + ((k : ℝ) + 1) * v x))
          - (1 + γ) * (x ^ (2 * (k : ℝ) - γ) * v x ^ 2)) :=
    intervalIntegral.integral_congr (fun x hx => hpt x (by rwa [Set.uIcc_of_le hyle] at hx))
  have hsplit : (∫ x in y..x₁, (2 * (x ^ (2 * (k : ℝ) - γ) * v x
            * (x * derivWithin v (Set.Icc y x₁) x + ((k : ℝ) + 1) * v x))
          - (1 + γ) * (x ^ (2 * (k : ℝ) - γ) * v x ^ 2)))
      = 2 * (∫ x in y..x₁, x ^ (2 * (k : ℝ) - γ) * v x
            * (x * derivWithin v (Set.Icc y x₁) x + ((k : ℝ) + 1) * v x))
        - (1 + γ) * (∫ x in y..x₁, x ^ (2 * (k : ℝ) - γ) * v x ^ 2) := by
    rw [intervalIntegral.integral_sub hII1 hII2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have key : 2 * (∫ x in y..x₁, x ^ (2 * (k : ℝ) - γ) * v x
            * (x * derivWithin v (Set.Icc y x₁) x + ((k : ℝ) + 1) * v x))
        - (1 + γ) * (∫ x in y..x₁, x ^ (2 * (k : ℝ) - γ) * v x ^ 2)
      = x₁ ^ (2 * (k : ℝ) + 1 - γ) * v x₁ ^ 2 - y ^ (2 * (k : ℝ) + 1 - γ) * v y ^ 2 := by
    rw [← hsplit, ← hDp_eq]
    exact hFTC'
  have hCeq : (∫ x in y..x₁, x ^ (2 * (k : ℝ) - γ) * v x * (x * deriv v x + ((k : ℝ) + 1) * v x))
      = ∫ x in y..x₁, x ^ (2 * (k : ℝ) - γ) * v x
          * (x * derivWithin v (Set.Icc y x₁) x + ((k : ℝ) + 1) * v x) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ x₁ := by
      change ({x₁}ᶜ : Set ℝ) ∈ MeasureTheory.ae (volume : Measure ℝ)
      rw [MeasureTheory.compl_mem_ae_iff, MeasureTheory.measure_singleton]
    filter_upwards [hne] with x hx
    intro hmem
    have hmemIoc : x ∈ Set.Ioc y x₁ := by rwa [Set.uIoc_of_le hyle] at hmem
    have hxIoo : x ∈ Set.Ioo y x₁ := ⟨hmemIoc.1, lt_of_le_of_ne hmemIoc.2 hx⟩
    rw [hdvW x hxIoo]
  rw [hCeq]
  linarith [key]

/-- Continuity from the right of the set integral in its upper endpoint. -/
private theorem tendsto_setIntegral_Ioc_right {u : ℝ → ℝ} {y x₁ : ℝ} (hy : y < x₁)
    (hu : IntegrableOn u (Set.Ioc y x₁)) :
    Tendsto (fun x : ℝ => ∫ t in Set.Ioc y x, u t) (nhdsWithin x₁ (Set.Iio x₁))
      (nhds (∫ t in Set.Ioc y x₁, u t)) := by
  set ũ : ℝ → ℝ := (Set.Ioc y x₁).indicator u with hũ
  have hũint : Integrable ũ volume := hu.integrable_indicator measurableSet_Ioc
  have hyx_ev : ∀ᶠ x : ℝ in nhdsWithin x₁ (Set.Iio x₁), y < x :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hy)
  have hleft : Tendsto (fun x : ℝ => ∫ t in Set.Ioc x x₁, u t)
      (nhdsWithin x₁ (Set.Iio x₁)) (nhds 0) := by
    have hkey : Tendsto (fun x : ℝ => ∫ t, (Set.Ioc x x₁).indicator ũ t)
        (nhdsWithin x₁ (Set.Iio x₁)) (nhds 0) := by
      have hmain : Tendsto (fun x : ℝ => ∫ t, (Set.Ioc x x₁).indicator ũ t)
          (nhdsWithin x₁ (Set.Iio x₁)) (nhds (∫ t, (fun _ : ℝ => 0) t)) := by
        refine tendsto_integral_filter_of_dominated_convergence (α := ℝ) (G := ℝ) (ι := ℝ)
          (l := nhdsWithin x₁ (Set.Iio x₁)) (μ := volume)
          (F := fun x (t : ℝ) => (Set.Ioc x x₁).indicator ũ t) (f := fun _ : ℝ => 0)
          (fun t => ‖ũ t‖) ?_ ?_ hũint.norm ?_
        · filter_upwards with x
          exact hũint.aestronglyMeasurable.indicator measurableSet_Ioc
        · filter_upwards with x
          filter_upwards with t
          by_cases ht : t ∈ Set.Ioc x x₁
          · rw [Set.indicator_of_mem ht]
          · rw [Set.indicator_of_notMem ht]; simp
        · have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ x₁ := by
            rw [Filter.Eventually, mem_ae_iff]
            simpa using measure_singleton x₁
          filter_upwards [hae] with t htne
          rcases lt_or_gt_of_ne htne with ht | ht
          · have hev : ∀ᶠ x : ℝ in nhdsWithin x₁ (Set.Iio x₁),
                (Set.Ioc x x₁).indicator ũ t = 0 := by
              filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds ht)]
                with x hx
              rw [Set.indicator_of_notMem (fun h => absurd h.1 (not_lt.mpr hx.le))]
            exact tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)
          · have hev : ∀ᶠ x : ℝ in nhdsWithin x₁ (Set.Iio x₁),
                (Set.Ioc x x₁).indicator ũ t = 0 := by
              filter_upwards [self_mem_nhdsWithin] with x hx
              rw [Set.indicator_of_notMem (fun h => absurd h.2 (not_le.mpr ht))]
            exact tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)
      simpa using hmain
    refine hkey.congr' ?_
    filter_upwards [hyx_ev] with x hxy
    rw [integral_indicator measurableSet_Ioc]
    exact setIntegral_congr_fun measurableSet_Ioc fun t ht => by
      have hmem : t ∈ Set.Ioc y x₁ := ⟨hxy.trans ht.1, ht.2⟩
      rw [hũ, Set.indicator_of_mem hmem]
  have hadd : ∀ᶠ x : ℝ in nhdsWithin x₁ (Set.Iio x₁),
      ∫ t in Set.Ioc y x, u t = (∫ t in Set.Ioc y x₁, u t) - (∫ t in Set.Ioc x x₁, u t) := by
    filter_upwards [self_mem_nhdsWithin, hyx_ev] with x hx1 hxy
    have hunion : Set.Ioc y x ∪ Set.Ioc x x₁ = Set.Ioc y x₁ :=
      Set.Ioc_union_Ioc_eq_Ioc hxy.le hx1.le
    have h1 : IntegrableOn u (Set.Ioc y x) :=
      hu.mono_set fun t ht => ⟨ht.1, ht.2.trans hx1.le⟩
    have h2 : IntegrableOn u (Set.Ioc x x₁) :=
      hu.mono_set fun t ht => ⟨hxy.trans ht.1, ht.2⟩
    have h3 := setIntegral_union (s := Set.Ioc y x) (t := Set.Ioc x x₁)
      (Set.disjoint_left.mpr fun t ht1 ht2 => absurd ht2.1 (not_lt.mpr ht1.2))
      measurableSet_Ioc h1 h2
    rw [hunion] at h3
    linarith
  have hsub' : Tendsto (fun x : ℝ => (∫ t in Set.Ioc y x₁, u t) - (∫ t in Set.Ioc x x₁, u t))
      (nhdsWithin x₁ (Set.Iio x₁)) (nhds (∫ t in Set.Ioc y x₁, u t)) := by
    have h : Tendsto (fun _ : ℝ => (∫ t in Set.Ioc y x₁, u t))
        (nhdsWithin x₁ (Set.Iio x₁)) (nhds (∫ t in Set.Ioc y x₁, u t)) := tendsto_const_nhds
    have h2 := h.sub hleft
    rwa [sub_zero] at h2
  have heq : (fun x : ℝ => (∫ t in Set.Ioc y x₁, u t) - (∫ t in Set.Ioc x x₁, u t))
      =ᶠ[nhdsWithin x₁ (Set.Iio x₁)] fun x : ℝ => ∫ t in Set.Ioc y x, u t :=
    hadd.mono fun x hx => hx.symm
  exact hsub'.congr' heq

/-! ### The one-dimensional weighted Hardy inequality for iterated derivatives of `f/x` -/

/-- Core estimate: the weighted Hardy inequality with the constant `4/(1+γ)²`, stated for an
abstract pair `(v, F1)` related by `F1 = x·v' + (k+1)·v` on `(0,x₁)` (the relation satisfied by
`v = ∂^k(f/x)` and `F1 = ∂^{k+1}f`).  The left-hand side may take the junk value `0` when it is
not integrable. -/
private theorem core {k : ℕ} {γ x₁ : ℝ} (hx₁ : 0 < x₁) (hγ : -1 < γ)
    {v F1 : ℝ → ℝ}
    (hvC1 : ContDiffOn ℝ 1 v (Set.Ioo 0 x₁))
    (hF1cont : ContinuousOn F1 (Set.Ioo 0 x₁))
    (hJ : IntegrableOn (fun x => x ^ (2 * (k : ℝ) - γ) * F1 x ^ 2) (Set.Ioc 0 x₁))
    (hleib : ∀ x ∈ Set.Ioo 0 x₁, F1 x = x * deriv v x + ((k : ℝ) + 1) * v x) :
    (∫ x in Set.Ioc 0 x₁, x ^ (2 * (k : ℝ) - γ) * v x ^ 2)
      ≤ 4 / (1 + γ) ^ 2 * (∫ x in Set.Ioc 0 x₁, x ^ (2 * (k : ℝ) - γ) * F1 x ^ 2) := by
  set u : ℝ → ℝ := fun x => x ^ (2 * (k : ℝ) - γ) * v x ^ 2 with hu
  set A : ℝ := ∫ x in Set.Ioc 0 x₁, u x with hA
  set B : ℝ := ∫ x in Set.Ioc 0 x₁, x ^ (2 * (k : ℝ) - γ) * F1 x ^ 2 with hBdef
  have hγ1 : (0 : ℝ) < 1 + γ := by linarith
  have hne : (1 + γ) ≠ 0 := ne_of_gt hγ1
  have hPnn : ∀ x : ℝ, 0 < x → 0 ≤ x ^ (2 * (k : ℝ) - γ) :=
    fun x hx => Real.rpow_nonneg hx.le _
  have hunn : ∀ x : ℝ, 0 < x → 0 ≤ u x := fun x hx => by
    rw [hu]; exact mul_nonneg (hPnn x hx) (sq_nonneg _)
  have hwt : ContinuousOn (fun t : ℝ => t ^ (2 * (k : ℝ) - γ)) (Set.Ioo (0 : ℝ) x₁) := fun t ht =>
    (Real.continuousAt_rpow_const t _ (Or.inl (ne_of_gt ht.1))).continuousWithinAt
  by_cases hI : IntegrableOn u (Set.Ioc 0 x₁)
  · -- the left-hand side is honest
    have key : ∀ ε : ℝ, 0 < ε → 2 * ε < x₁ →
        (∫ x in Set.Ioc 0 x₁, u x) - (∫ x in Set.Ioc 0 (2 * ε), u x)
          ≤ 4 / (1 + γ) ^ 2 * B + (1 + 4 / (1 + γ)) * (∫ x in Set.Ioc 0 (2 * ε), u x) := by
      intro ε hε h2ε
      have hIccsub : Set.Icc ε (2 * ε) ⊆ Set.Ioo (0 : ℝ) x₁ :=
        fun t ht => ⟨lt_of_lt_of_le hε ht.1, ht.2.trans_lt h2ε⟩
      have hucont : ContinuousOn u (Set.Icc ε (2 * ε)) := by
        rw [hu]
        refine ContinuousOn.mul ?_ ?_
        · exact fun t ht =>
            (Real.continuousAt_rpow_const t _ (Or.inl (ne_of_gt (hIccsub ht).1))).continuousWithinAt
        · exact (hvC1.mono hIccsub).continuousOn.pow 2
      have hnnIoc : ∀ x ∈ Set.Ioc 0 (2 * ε), 0 ≤ u x := fun x hx => hunn x hx.1
      have hintIoc : IntegrableOn u (Set.Ioc 0 (2 * ε)) :=
        hI.mono_set fun t ht => ⟨ht.1, le_of_lt (ht.2.trans_lt h2ε)⟩
      obtain ⟨y, hy_mem, hy_bd⟩ := hardyIter_good_point hε hucont hnnIoc hintIoc
      set C : ℝ := ∫ x in Set.Ioc 0 (2 * ε), u x with hC
      have hy_bd' : y * u y ≤ 2 * C := by rw [hC]; exact hy_bd
      have hy_pos : 0 < y := lt_of_lt_of_le hε hy_mem.1
      have hy_lt : y < x₁ := lt_of_le_of_lt hy_mem.2 h2ε
      have hy_le : y ≤ 2 * ε := hy_mem.2
      have hu_y : IntegrableOn u (Set.Ioc y x₁) :=
        hI.mono_set fun t ht => ⟨hy_pos.trans ht.1, ht.2⟩
      have hF_y : IntegrableOn (fun t => t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2) (Set.Ioc y x₁) :=
        hJ.mono_set fun t ht => ⟨hy_pos.trans ht.1, ht.2⟩
      -- the per-`x` chain: IBP plus AM-GM
      have hchain : ∀ x : ℝ, y < x → x < x₁ →
          (1 + γ) / 2 * (∫ t in Set.Ioc y x, u t)
            ≤ 1 / 2 * ((1 + γ) / 2 * (∫ t in Set.Ioc y x, u t)
                + (2 / (1 + γ)) * (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2))
              + 1 / 2 * (y * u y) := by
        intro x hyx hxx
        have hsub : Set.Icc y x ⊆ Set.Ioo (0 : ℝ) x₁ :=
          fun t ht => ⟨lt_of_lt_of_le hy_pos ht.1, ht.2.trans_lt hxx⟩
        have hwtc : ContinuousOn (fun t : ℝ => t ^ (2 * (k : ℝ) - γ)) (Set.Icc y x) := hwt.mono hsub
        have hvc : ContinuousOn v (Set.Icc y x) := (hvC1.mono hsub).continuousOn
        have hFc : ContinuousOn F1 (Set.Icc y x) := hF1cont.mono hsub
        have hIntV : IntegrableOn (fun t => t ^ (2 * (k : ℝ) - γ) * v t ^ 2) (Set.Ioc y x) :=
          ((hwtc.mul (hvc.pow 2)).integrableOn_compact isCompact_Icc).mono_set
            Set.Ioc_subset_Icc_self
        have hIntF : IntegrableOn (fun t => t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2) (Set.Ioc y x) :=
          ((hwtc.mul (hFc.pow 2)).integrableOn_compact isCompact_Icc).mono_set
            Set.Ioc_subset_Icc_self
        -- the integration-by-parts inequality
        have hibp_le : (1 + γ) / 2 * (∫ t in Set.Ioc y x, u t)
            ≤ (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * |v t| * |F1 t|)
              + 1 / 2 * (y * u y) := by
          have hvsub : ContDiffOn ℝ 1 v (Set.Icc y x) := hvC1.mono hsub
          have hibp := ibp_fts (k := k) (γ := γ) (x₁ := x) (y := y) hy_pos hyx hvsub
          have h1 : (∫ t in y..x, t ^ (2 * (k : ℝ) - γ) * v t ^ 2) = ∫ t in Set.Ioc y x, u t :=
            intervalIntegral.integral_of_le hyx.le
          have h2 : (∫ t in y..x, t ^ (2 * (k : ℝ) - γ) * v t
                * (t * deriv v t + ((k : ℝ) + 1) * v t))
              = ∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * v t * F1 t := by
            rw [intervalIntegral.integral_of_le hyx.le]
            refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
            rw [hleib t (hsub (Set.Ioc_subset_Icc_self ht))]
          rw [h1, h2] at hibp
          have hyb : y ^ (2 * (k : ℝ) + 1 - γ) * v y ^ 2 = y * u y := by
            have hrr : y ^ (2 * (k : ℝ) + 1 - γ) = y ^ (2 * (k : ℝ) - γ) * y := by
              have h := Real.rpow_add_one (ne_of_gt hy_pos) (2 * (k : ℝ) - γ)
              rwa [show 2 * (k : ℝ) - γ + 1 = 2 * (k : ℝ) + 1 - γ from by ring] at h
            rw [hrr, hu]
            ring
          rw [hyb] at hibp
          have hxn : 0 ≤ x ^ (2 * (k : ℝ) + 1 - γ) * v x ^ 2 :=
            mul_nonneg (Real.rpow_nonneg (le_of_lt (hy_pos.trans hyx)) _) (sq_nonneg _)
          have habs : (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * v t * F1 t)
              ≤ ∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * |v t| * |F1 t| := by
            have hle : (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * v t * F1 t)
                ≤ ∫ t in Set.Ioc y x, |t ^ (2 * (k : ℝ) - γ) * v t * F1 t| :=
              le_trans (le_abs_self _) abs_integral_le_integral_abs
            have heq : (∫ t in Set.Ioc y x, |t ^ (2 * (k : ℝ) - γ) * v t * F1 t|)
                = ∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * |v t| * |F1 t| := by
              refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
              have ht0 : 0 ≤ t ^ (2 * (k : ℝ) - γ) :=
                Real.rpow_nonneg (le_of_lt (hy_pos.trans ht.1)) _
              rw [abs_mul, abs_mul, abs_of_nonneg ht0]
            rw [heq] at hle
            exact hle
          linarith [hibp, habs, hxn]
        -- AM-GM at the weight
        have hamgm_x : 2 * (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * |v t| * |F1 t|)
            ≤ (1 + γ) / 2 * (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * v t ^ 2)
              + (2 / (1 + γ)) * (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2) := by
          have hpw : ∀ t ∈ Set.Ioc y x,
              2 * (t ^ (2 * (k : ℝ) - γ) * |v t| * |F1 t|)
                ≤ (1 + γ) / 2 * (t ^ (2 * (k : ℝ) - γ) * v t ^ 2)
                  + (2 / (1 + γ)) * (t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2) := by
            intro t ht
            have ht0 : 0 < t := hy_pos.trans ht.1
            have hw : 0 ≤ t ^ (2 * (k : ℝ) - γ) := Real.rpow_nonneg ht0.le _
            have ham := two_mul_le_mul_sq_add_div_sq_prv (t := (1 + γ) / 2) (a := |v t|)
              (b := |F1 t|) (by linarith)
            have hdiv : |F1 t| ^ 2 / ((1 + γ) / 2) = (2 / (1 + γ)) * F1 t ^ 2 := by
              rw [sq_abs]
              field_simp [hne] <;> ring
            rw [hdiv, sq_abs] at ham
            have hmul := mul_le_mul_of_nonneg_left ham hw
            nlinarith [hmul]
          have hgcont : ContinuousOn (fun t => (1 + γ) / 2 * (t ^ (2 * (k : ℝ) - γ) * v t ^ 2)
              + (2 / (1 + γ)) * (t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2)) (Set.Icc y x) :=
            ContinuousOn.add
              (ContinuousOn.const_mul (hwtc.mul (hvc.pow 2)) _)
              (ContinuousOn.const_mul (hwtc.mul (hFc.pow 2)) _)
          have hgint : IntegrableOn (fun t => (1 + γ) / 2 * (t ^ (2 * (k : ℝ) - γ) * v t ^ 2)
              + (2 / (1 + γ)) * (t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2)) (Set.Ioc y x) :=
            (hgcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
          have hmono := setIntegral_mono_of_nonneg
            (f := fun t => 2 * (t ^ (2 * (k : ℝ) - γ) * |v t| * |F1 t|))
            (g := fun t => (1 + γ) / 2 * (t ^ (2 * (k : ℝ) - γ) * v t ^ 2)
              + (2 / (1 + γ)) * (t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2))
            (fun t ht => mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg
              (Real.rpow_nonneg (le_of_lt (hy_pos.trans ht.1)) _) (abs_nonneg _))
              (abs_nonneg _))) hpw hgint
          have hL : (∫ t in Set.Ioc y x, 2 * (t ^ (2 * (k : ℝ) - γ) * |v t| * |F1 t|))
              = 2 * ∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * |v t| * |F1 t| :=
            integral_const_mul 2 _
          have hR : (∫ t in Set.Ioc y x, (1 + γ) / 2 * (t ^ (2 * (k : ℝ) - γ) * v t ^ 2)
                + (2 / (1 + γ)) * (t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2))
              = (1 + γ) / 2 * (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * v t ^ 2)
                + (2 / (1 + γ)) * (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2) := by
            rw [integral_add]
            · rw [integral_const_mul, integral_const_mul]
            · exact hIntV.const_mul _
            · exact hIntF.const_mul _
          rw [hL, hR] at hmono
          exact hmono
        linarith [hibp_le, hamgm_x]
      -- pass to the limit `x → x₁⁻`
      have hlim1 : Tendsto (fun x : ℝ => (1 + γ) / 2 * (∫ t in Set.Ioc y x, u t))
          (nhdsWithin x₁ (Set.Iio x₁))
          (nhds ((1 + γ) / 2 * (∫ t in Set.Ioc y x₁, u t))) :=
        (tendsto_setIntegral_Ioc_right hy_lt hu_y).const_mul _
      have hGlim : Tendsto (fun x : ℝ => 1 / 2 * ((1 + γ) / 2 * (∫ t in Set.Ioc y x, u t)
              + (2 / (1 + γ)) * (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2))
            + 1 / 2 * (y * u y))
          (nhdsWithin x₁ (Set.Iio x₁))
          (nhds (1 / 2 * ((1 + γ) / 2 * (∫ t in Set.Ioc y x₁, u t)
              + (2 / (1 + γ)) * (∫ t in Set.Ioc y x₁, t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2))
            + 1 / 2 * (y * u y))) := by
        refine Tendsto.add ?_ tendsto_const_nhds
        refine Tendsto.const_mul _ ?_
        exact Tendsto.add ((tendsto_setIntegral_Ioc_right hy_lt hu_y).const_mul _)
          ((tendsto_setIntegral_Ioc_right hy_lt hF_y).const_mul _)
      have hchain_ev : ∀ᶠ x : ℝ in nhdsWithin x₁ (Set.Iio x₁),
          (1 + γ) / 2 * (∫ t in Set.Ioc y x, u t)
            ≤ 1 / 2 * ((1 + γ) / 2 * (∫ t in Set.Ioc y x, u t)
                + (2 / (1 + γ)) * (∫ t in Set.Ioc y x, t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2))
              + 1 / 2 * (y * u y) := by
        filter_upwards [self_mem_nhdsWithin,
          Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hy_lt)] with x hxx hyx
        exact hchain x hyx hxx
      have hlim := le_of_tendsto_of_tendsto hlim1 hGlim hchain_ev
      -- rearrange the resulting inequality
      have hAy_le : (∫ t in Set.Ioc y x₁, u t)
          ≤ (4 / (1 + γ) ^ 2) * (∫ t in Set.Ioc y x₁, t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2)
            + (2 / (1 + γ)) * (y * u y) := by
        have hpos : (0 : ℝ) < 4 / (1 + γ) := div_pos (by norm_num) hγ1
        have hmul := mul_le_mul_of_nonneg_left hlim hpos.le
        have e1 : 4 / (1 + γ) * ((1 + γ) / 2 * (∫ t in Set.Ioc y x₁, u t))
            = 2 * (∫ t in Set.Ioc y x₁, u t) := by
          field_simp [hne] <;> ring
        have e2 : 4 / (1 + γ) * (1 / 2 * ((1 + γ) / 2 * (∫ t in Set.Ioc y x₁, u t)
              + (2 / (1 + γ)) * (∫ t in Set.Ioc y x₁, t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2))
              + 1 / 2 * (y * u y))
            = (∫ t in Set.Ioc y x₁, u t)
              + (4 / (1 + γ) ^ 2) * (∫ t in Set.Ioc y x₁, t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2)
              + (2 / (1 + γ)) * (y * u y) := by
          field_simp [hne] <;> ring
        rw [e1, e2] at hmul
        linarith [hmul]
      -- comparison of `B` and of the two tail integrals
      have hBy_le : (∫ t in Set.Ioc y x₁, t ^ (2 * (k : ℝ) - γ) * F1 t ^ 2) ≤ B := by
        rw [hBdef]
        refine setIntegral_mono_set hJ ?_ ?_
        · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
          exact Eventually.of_forall fun t ht => mul_nonneg (hPnn t ht.1) (sq_nonneg _)
        · exact Eventually.of_forall fun t ht => ⟨hy_pos.trans ht.1, ht.2⟩
      have h4 : (∫ t in Set.Ioc y x₁, u t)
          ≤ (4 / (1 + γ) ^ 2) * B + (2 / (1 + γ)) * (y * u y) :=
        hAy_le.trans (add_le_add (mul_le_mul_of_nonneg_left hBy_le
          (div_nonneg (by norm_num) (sq_nonneg _))) le_rfl)
      have h5 : (∫ t in Set.Ioc y x₁, u t) ≤ (4 / (1 + γ) ^ 2) * B + (4 / (1 + γ)) * C := by
        refine h4.trans (add_le_add le_rfl ?_)
        have h2 : (2 / (1 + γ)) * (y * u y) ≤ (2 / (1 + γ)) * (2 * C) :=
          mul_le_mul_of_nonneg_left hy_bd' (div_nonneg (by norm_num) hγ1.le)
        have e : (2 / (1 + γ)) * (2 * C) = (4 / (1 + γ)) * C := by ring
        rw [e] at h2
        exact h2
      have hsplit : (∫ x in Set.Ioc 0 x₁, u x)
          = (∫ x in Set.Ioc 0 y, u x) + (∫ x in Set.Ioc y x₁, u x) := by
        have hunion : Set.Ioc 0 y ∪ Set.Ioc y x₁ = Set.Ioc 0 x₁ :=
          Set.Ioc_union_Ioc_eq_Ioc hy_pos.le hy_lt.le
        have h1 : IntegrableOn u (Set.Ioc 0 y) :=
          hI.mono_set fun t ht => ⟨ht.1, ht.2.trans hy_lt.le⟩
        have h3 := setIntegral_union (s := Set.Ioc 0 y) (t := Set.Ioc y x₁)
          (Set.disjoint_left.mpr fun t ht1 ht2 => absurd ht2.1 (not_lt.mpr ht1.2))
          measurableSet_Ioc h1 hu_y
        rw [hunion] at h3
        exact h3
      have hCy : (∫ x in Set.Ioc 0 y, u x) ≤ C := by
        rw [hC]
        refine setIntegral_mono_set hintIoc ?_ ?_
        · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
          exact Eventually.of_forall fun t ht => hunn t ht.1
        · exact Eventually.of_forall fun t ht => ⟨ht.1, ht.2.trans hy_le⟩
      have hCnn : 0 ≤ C := by
        rw [hC]
        exact setIntegral_nonneg measurableSet_Ioc fun t ht => hunn t ht.1
      have harith : (1 + 4 / (1 + γ)) * C = C + (4 / (1 + γ)) * C := by ring
      rw [harith]
      linarith [h5, hCy, hCnn, hsplit]
    -- pass to the limit `ε → 0⁺`
    have hlimC : Tendsto (fun ε : ℝ => ∫ x in Set.Ioc 0 (2 * ε), u x)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      refine (hardyIter_tendsto_zero hx₁ hI).comp ?_
      have h2 : Tendsto (fun ε : ℝ => 2 * ε) (nhds (0 : ℝ)) (nhds (2 * 0)) :=
        tendsto_id.const_mul 2
      simpa using h2.mono_left nhdsWithin_le_nhds
    have hL : Tendsto (fun ε : ℝ => (∫ x in Set.Ioc 0 x₁, u x) - (∫ x in Set.Ioc 0 (2 * ε), u x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (∫ x in Set.Ioc 0 x₁, u x)) := by
      simpa using tendsto_const_nhds.sub hlimC
    have hR : Tendsto (fun ε : ℝ => 4 / (1 + γ) ^ 2 * B
          + (1 + 4 / (1 + γ)) * (∫ x in Set.Ioc 0 (2 * ε), u x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (4 / (1 + γ) ^ 2 * B)) := by
      simpa using tendsto_const_nhds.add
        (hlimC.const_mul (1 + 4 / (1 + γ)))
    have hev : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 2 * ε < x₁ := by
      have h1 : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < x₁ / 2 :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (Iio_mem_nhds (show (0 : ℝ) < x₁ / 2 by linarith))
      filter_upwards [h1] with ε hε
      linarith
    have hkey_ev : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (∫ x in Set.Ioc 0 x₁, u x) - (∫ x in Set.Ioc 0 (2 * ε), u x)
          ≤ 4 / (1 + γ) ^ 2 * B + (1 + 4 / (1 + γ)) * (∫ x in Set.Ioc 0 (2 * ε), u x) := by
      filter_upwards [self_mem_nhdsWithin, hev] with ε hε h2ε
      exact key ε hε h2ε
    have hfin := le_of_tendsto_of_tendsto hL hR hkey_ev
    rw [hA]
    exact hfin
  · -- the left-hand side is the junk value `0`
    rw [hA, integral_undef hI, hBdef]
    exact mul_nonneg (div_nonneg (by norm_num) (sq_nonneg _))
      (setIntegral_nonneg measurableSet_Ioc fun t ht =>
        mul_nonneg (hPnn t ht.1) (sq_nonneg _))


end Work.FTS.H2.DivQ
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.radGreen_firstTerm_sq_div_z4_integrableOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

/-- Cauchy-Schwarz with the constant function `1` on the interval `[0,z]`, `z ≥ 0`:
`(∫_0^z f)² ≤ z ∫_0^z f²`.  Proved by completing the square. -/
private theorem cs_zero_interval {f : ℝ → ℝ} {z : ℝ} (hz : 0 ≤ z)
    (hf : IntervalIntegrable f volume 0 z)
    (hf2 : IntervalIntegrable (fun t : ℝ => f t ^ 2) volume 0 z) :
    (∫ t in (0 : ℝ)..z, f t) ^ 2 ≤ z * ∫ t in (0 : ℝ)..z, f t ^ 2 := by
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · subst hz0
    simp
  · set A : ℝ := ∫ t in (0 : ℝ)..z, f t with hA
    set B : ℝ := ∫ t in (0 : ℝ)..z, f t ^ 2 with hB
    have key : ∀ c : ℝ, 0 ≤ c ^ 2 * z - 2 * c * A + B := by
      intro c
      have hA1 : IntervalIntegrable (fun t : ℝ => f t ^ 2 - 2 * c * f t) volume 0 z :=
        hf2.sub (hf.const_mul (2 * c))
      have hA2 : IntervalIntegrable (fun _ : ℝ => c ^ 2) volume 0 z := intervalIntegrable_const
      have hiden : (∫ t in (0 : ℝ)..z, (f t - c) ^ 2) = c ^ 2 * z - 2 * c * A + B := by
        have h1 : (∫ t in (0 : ℝ)..z, (f t - c) ^ 2)
            = ∫ t in (0 : ℝ)..z, (f t ^ 2 - 2 * c * f t + c ^ 2) := by
          apply intervalIntegral.integral_congr
          intro t _
          ring
        rw [h1]
        have hadd : (∫ t in (0 : ℝ)..z, (f t ^ 2 - 2 * c * f t + c ^ 2))
            = (∫ t in (0 : ℝ)..z, (f t ^ 2 - 2 * c * f t))
              + (∫ t in (0 : ℝ)..z, c ^ 2) := by
          simpa using intervalIntegral.integral_add hA1 hA2
        rw [hadd]
        have hsub : (∫ t in (0 : ℝ)..z, (f t ^ 2 - 2 * c * f t))
            = (∫ t in (0 : ℝ)..z, f t ^ 2) - (∫ t in (0 : ℝ)..z, 2 * c * f t) := by
          simpa using intervalIntegral.integral_sub hf2 (hf.const_mul (2 * c))
        rw [hsub, ← hB]
        have hmul : (∫ t in (0 : ℝ)..z, 2 * c * f t) = 2 * c * (∫ t in (0 : ℝ)..z, f t) := by
          simpa using intervalIntegral.integral_const_mul (2 * c) f
        rw [hmul, ← hA]
        have hconst : (∫ t in (0 : ℝ)..z, c ^ 2) = c ^ 2 * z := by
          rw [intervalIntegral.integral_const]
          simp only [smul_eq_mul, sub_zero]
          ring
        rw [hconst]
        ring
      have hnn : 0 ≤ ∫ t in (0 : ℝ)..z, (f t - c) ^ 2 :=
        intervalIntegral.integral_nonneg hz (fun u _ => sq_nonneg (f u - c))
      linarith [hiden ▸ hnn]
    have hzA := key (A / z)
    have hexp : z * ((A / z) ^ 2 * z - 2 * (A / z) * A + B) = B * z - A ^ 2 := by
      field_simp
      ring
    have hle : A ^ 2 ≤ B * z := by
      have h : 0 ≤ B * z - A ^ 2 := by rw [← hexp]; exact mul_nonneg hzpos.le hzA
      linarith
    rw [mul_comm z B]
    exact hle

/-- The abstract version of the target statement: for a single exponent `r > -1` the
power-primitive `∫_0^z c t t^r`, weighted by `z^{-(r+1)}`, is square-integrable against
`z^{-4}` on `(0,1)`, whenever `c` is continuous there and `c(t)²/t⁴` is integrable.

This is the sharp form of the near-`0` estimate for the first term of the radial Green
function of `Work.FTS.PhiStar.Radial.radGreen`: the proof combines the Cauchy-Schwarz
inequality `(∫_0^z f)² ≤ z ∫_0^z f²` with the weighted Hardy/Tonelli computation
`∫_0^1 z^{-(2r+5)} ∫_0^z c² t^{2r}`. -/
private theorem key (r : ℝ) (hr : -1 < r) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioo 0 1))
    (hint : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1)) :
    IntegrableOn
      (fun z : ℝ => (z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4)
      (Set.Ioo 0 1) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  -- integrability of the two integrands on `Icc 0 1`
  have hfIcc : IntegrableOn (fun t : ℝ => c t * t ^ r) (Set.Icc 0 1) :=
    integrableOn_mul_rpow (by linarith) hc hint
  have hf2Icc : IntegrableOn (fun t : ℝ => (c t) ^ 2 * t ^ (2 * r)) (Set.Icc 0 1) :=
    integrableOn_sq_mul_rpow (by linarith) hc hint
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
  -- Cauchy-Schwarz with the constant function `1`
  have hcs : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      (∫ t in (0 : ℝ)..z, c t * t ^ r) ^ 2
        ≤ z * ∫ t in (0 : ℝ)..z, (c t) ^ 2 * t ^ (2 * r) := by
    intro z hz
    have hz0 : (0 : ℝ) ≤ z := le_of_lt hz.1
    have hz1 : z ≤ 1 := le_of_lt hz.2
    have hsub : Set.Icc 0 z ⊆ Set.Icc 0 1 :=
      fun x hx => ⟨hx.1, le_trans hx.2 hz1⟩
    have h1 : IntervalIntegrable (fun t : ℝ => c t * t ^ r) volume 0 z :=
      IntegrableOn.intervalIntegrable (by rw [uIcc_of_le hz0]; exact hfIcc.mono_set hsub)
    have h2' : IntervalIntegrable (fun t : ℝ => (c t) ^ 2 * t ^ (2 * r)) volume 0 z :=
      IntegrableOn.intervalIntegrable (by rw [uIcc_of_le hz0]; exact hf2Icc.mono_set hsub)
    have h2 : IntervalIntegrable (fun t : ℝ => (c t * t ^ r) ^ 2) volume 0 z :=
      h2'.congr fun t ht => by
        rw [uIoc_of_le hz0] at ht
        exact (hpow t (le_of_lt ht.1)).symm
    have h3 := cs_zero_interval hz0 h1 h2
    have h4 : (∫ t in (0 : ℝ)..z, (c t * t ^ r) ^ 2)
        = ∫ t in (0 : ℝ)..z, (c t) ^ 2 * t ^ (2 * r) :=
      intervalIntegral.integral_congr fun t ht => by
        rw [uIcc_of_le hz0] at ht
        exact hpow t ht.1
    rw [h4] at h3
    exact h3
  -- the bound `G z ≤ z^{-(2r+5)} * ∫_0^z (c t)^2 t^{2r}`
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
          = ((z ^ (-(r + 1))) ^ 2 * (∫ t in (0 : ℝ)..z, c t * t ^ r) ^ 2) * (z ^ 4)⁻¹ := by
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
  -- measurability of the three weight functions
  have hWcont : ContinuousOn (fun z : ℝ => ENNReal.ofReal (z ^ (-(2 * r + 5))))
      (Set.Ioo (0 : ℝ) 1) :=
    ENNReal.continuous_ofReal.continuousOn.comp
      (fun z hz => (Real.continuousAt_rpow_const z (-(2 * r + 5))
        (Or.inl (ne_of_gt hz.1))).continuousWithinAt)
      (fun z _ => mem_univ _)
  have hHcont : ContinuousOn (fun t : ℝ => ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)))
      (Set.Ioo (0 : ℝ) 1) :=
    ENNReal.continuous_ofReal.continuousOn.comp
      ((hc.pow 2).mul (fun z hz => (Real.continuousAt_rpow_const z (2 * r)
        (Or.inl (ne_of_gt hz.1))).continuousWithinAt))
      (fun z _ => mem_univ _)
  have hWmeas : AEMeasurable (fun z : ℝ => ENNReal.ofReal (z ^ (-(2 * r + 5))))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := hWcont.aemeasurable measurableSet_Ioo
  have hHmeas : AEMeasurable (fun t : ℝ => ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := hHcont.aemeasurable measurableSet_Ioo
  have hQmeas : AEMeasurable (fun t : ℝ => ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    (ENNReal.continuous_ofReal.continuousOn.comp
      ((hc.pow 2).div (continuousOn_id.pow 4) (fun z hz => pow_ne_zero 4 (ne_of_gt hz.1)))
      (fun z _ => mem_univ _)).aemeasurable measurableSet_Ioo
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
        ≤ ENNReal.ofReal (z ^ (-(2 * r + 5)) * ∫ t in (0 : ℝ)..z, (c t) ^ 2 * t ^ (2 * r)) :=
          ENNReal.ofReal_le_ofReal (hGbound z hz)
      _ = ENNReal.ofReal (z ^ (-(2 * r + 5)))
            * ∫⁻ t in Set.Ioo (0 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hz0) _), hconv]
  -- the lintegral bound
  have hlin1 : (∫⁻ z in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4))
      ≤ ∫⁻ z in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (z ^ (-(2 * r + 5)))
          * ∫⁻ t in Set.Ioo (0 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact hstep z hz
  have hlin2 : (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)) * ∫⁻ z in Set.Ioo t 1,
          ENNReal.ofReal (z ^ (-(2 * r + 5))))
      ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r))
          * ENNReal.ofReal (t ^ (-(2 * r + 4)) / (2 * r + 4)) := by
    have hr' : -(2 * r + 5) < (-1 : ℝ) := by linarith
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    rw [lintegral_ofReal_rpow_Ioo_left (r := -(2 * r + 5)) (t := t) ht.1 (le_of_lt ht.2) hr']
    refine ENNReal.ofReal_le_ofReal ?_
    have hut : 1 ≤ t ^ (-(2 * r + 4)) := by
      have h := Real.rpow_le_rpow_of_nonpos ht.1 (le_of_lt ht.2) (show -(2 * r + 4) ≤ 0 by linarith)
      rwa [Real.one_rpow] at h
    have hv : (0 : ℝ) < 2 * r + 4 := by linarith
    rw [show -(2 * r + 5) + 1 = -(2 * r + 4) by ring]
    have hkey : (1 - t ^ (-(2 * r + 4))) / (-(2 * r + 4))
        = (t ^ (-(2 * r + 4)) - 1) / (2 * r + 4) := by
      rw [div_neg, ← neg_div, neg_sub]
    rw [hkey, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr (le_of_lt hv))
  have hlin3 : (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r))
        * ENNReal.ofReal (t ^ (-(2 * r + 4)) / (2 * r + 4)))
      = (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
          * (ENNReal.ofReal (2 * r + 4))⁻¹ := by
    have hv : (0 : ℝ) < 2 * r + 4 := by linarith
    have hpt : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r))
            * ENNReal.ofReal (t ^ (-(2 * r + 4)) / (2 * r + 4))
          = ENNReal.ofReal ((c t) ^ 2 / t ^ 4) * (ENNReal.ofReal (2 * r + 4))⁻¹ := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have hA : ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)) * ENNReal.ofReal (t ^ (-(2 * r + 4)))
          = ENNReal.ofReal ((c t) ^ 2 / t ^ 4) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt ht0) _))]
        congr 1
        rw [div_eq_mul_inv, ← Real.rpow_natCast t 4, ← Real.rpow_neg (le_of_lt ht0) ((4 : ℕ) : ℝ)]
        rw [mul_assoc, ← Real.rpow_add ht0]
        congr 1
        ring
      have hB : ENNReal.ofReal (t ^ (-(2 * r + 4)) / (2 * r + 4))
          = ENNReal.ofReal (t ^ (-(2 * r + 4))) * (ENNReal.ofReal (2 * r + 4))⁻¹ := by
        rw [ENNReal.ofReal_div_of_pos hv, div_eq_mul_inv]
      rw [hB, ← mul_assoc, hA]
    rw [lintegral_congr_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hpt t ht)]
    rw [lintegral_mul_const'' _ hQmeas]
  have hfin : (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4)) < ∞ := by
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] (fun t : ℝ => (c t) ^ 2 / t ^ 4) :=
      Eventually.of_forall fun t => div_nonneg (sq_nonneg _) (by positivity)
    exact (hasFiniteIntegral_iff_ofReal hnn).mp hint.hasFiniteIntegral
  have hmain : (∫⁻ z in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4))
      ≤ (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
          * (ENNReal.ofReal (2 * r + 4))⁻¹ := by
    calc (∫⁻ z in Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal ((z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4))
        ≤ ∫⁻ z in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (z ^ (-(2 * r + 5)))
            * ∫⁻ t in Set.Ioo (0 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)) := hlin1
      _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r))
            * ∫⁻ z in Set.Ioo t 1, ENNReal.ofReal (z ^ (-(2 * r + 5))) :=
          lintegral_Ioo_triangle (a := 0) (b := 1) h01 hWmeas hHmeas
      _ ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r))
            * ENNReal.ofReal (t ^ (-(2 * r + 4)) / (2 * r + 4)) := hlin2
      _ = (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
            * (ENNReal.ofReal (2 * r + 4))⁻¹ := hlin3
  have hlt : (∫⁻ z in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((z ^ (-(r + 1)) * (∫ t in (0 : ℝ)..z, c t * t ^ r)) ^ 2 / z ^ 4)) < ∞ :=
    lt_of_le_of_lt hmain (ENNReal.mul_lt_top hfin
      (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (by linarith : (0 : ℝ) < 2 * r + 4))))
  -- continuity of the target function and conclusion
  have hPcont : ContinuousOn (fun z : ℝ => ∫ t in (0 : ℝ)..z, c t * t ^ r) (Set.Ioo (0 : ℝ) 1) :=
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


end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.RadGreenSupport.src_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.RadGreenSupport

/-- From the hypothesis `|c^(k)(t)| ≤ A/(1+t^{k+1})` at `k = 0` one gets the two elementary
bounds on `|c|` used below: `|c t| ≤ A/(1+t)` and `|c t| ≤ A` for `t > 0`. -/
theorem src_abs_le {A : ℝ} (hA : 0 ≤ A) {c : ℝ → ℝ}
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ t : ℝ, 0 < t → |iteratedDeriv k c t| ≤ A / (1 + t ^ (k + 1))) :
    (∀ t : ℝ, 0 < t → |c t| ≤ A / (1 + t)) ∧ (∀ t : ℝ, 0 < t → |c t| ≤ A) := by
  have hc_le : ∀ t : ℝ, 0 < t → |c t| ≤ A / (1 + t) := by
    intro t ht
    have h := hb 0 (by norm_num : (0 : ℕ) ≤ 2) t ht
    simpa only [iteratedDeriv_zero, Nat.zero_add, pow_one] using h
  refine ⟨hc_le, fun t ht => ?_⟩
  refine le_trans (hc_le t ht) ?_
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + t)]
  nlinarith [hA, ht]

theorem src_integrable {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hc : ContDiffOn ℝ 2 c (Set.Ioi 0))
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ t : ℝ, 0 < t → |iteratedDeriv k c t| ≤ A / (1 + t ^ (k + 1))) :
    MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1) ∧
    MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1) := by
  obtain ⟨hc_le, hc_le_A⟩ := src_abs_le hA hb
  have hm0 : (0 : ℝ) ≤ 2 * (m : ℝ) / α := by
    apply div_nonneg
    · have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    · exact hα.le
  have hnum : (0 : ℝ) < 2 * (m : ℝ) + 5 := by
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  constructor
  · -- on `(0,1)`: dominate by `A * t^(p-1)` with `p - 1 > -1`
    rw [MeasureTheory.IntegrableOn]
    refine MeasureTheory.Integrable.mono'
      (g := fun t : ℝ => A * t ^ ((2 * (m : ℝ) + 5) / α - 1)) ?_ ?_ ?_
    · have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ ((2 * (m : ℝ) + 5) / α - 1))
          (Set.Ioo (0 : ℝ) 1) :=
        (intervalIntegral.integrableOn_Ioo_rpow_iff (show (0 : ℝ) < 1 by norm_num)).2
          (by have := div_pos hnum hα; linarith)
      exact MeasureTheory.Integrable.const_mul hbase A
    · have hcont : ContinuousOn (fun t : ℝ => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
          (Set.Ioo (0 : ℝ) 1) :=
        (hc.continuousOn.mono Set.Ioo_subset_Ioi_self).mul
          (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1)))
      exact hcont.aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
      exact mul_le_mul_of_nonneg_right (hc_le_A t ht.1) (Real.rpow_nonneg ht.1.le _)
  · -- on `(1,∞)`: use `|c t| ≤ A/t`, leaving the exponent `-2m/α - 2 < -1`
    rw [MeasureTheory.IntegrableOn]
    refine MeasureTheory.Integrable.mono'
      (g := fun t : ℝ => A * t ^ (-(2 * (m : ℝ) / α) - 2)) ?_ ?_ ?_
    · have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-(2 * (m : ℝ) / α) - 2))
          (Set.Ioi 1) :=
        (integrableOn_Ioi_rpow_iff (show (0 : ℝ) < 1 by norm_num)).2 (by linarith)
      exact MeasureTheory.Integrable.const_mul hbase A
    · have hcont : ContinuousOn (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
          (Set.Ioi 1) :=
        (hc.continuousOn.mono (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).mul
          (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (lt_trans zero_lt_one hx))))
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      have hct : |c t| ≤ A / t :=
        le_trans (hc_le t ht0) (div_le_div_of_nonneg_left hA ht0 (by linarith))
      have h1 : t ^ (-1 : ℝ) * t ^ (-(2 * (m : ℝ) / α) - 1)
          = t ^ (-(2 * (m : ℝ) / α) - 2) := by
        have hexp : -1 + (-(2 * (m : ℝ) / α) - 1) = -(2 * (m : ℝ) / α) - 2 := by ring
        rw [← Real.rpow_add ht0, hexp]
      calc |c t| * t ^ (-(2 * (m : ℝ) / α) - 1)
          ≤ (A / t) * t ^ (-(2 * (m : ℝ) / α) - 1) :=
            mul_le_mul_of_nonneg_right hct (Real.rpow_nonneg ht0.le _)
        _ = A * (t ^ (-1 : ℝ) * t ^ (-(2 * (m : ℝ) / α) - 1)) := by
              rw [div_eq_mul_inv, ← Real.rpow_neg_one t]
              ring
        _ = A * t ^ (-(2 * (m : ℝ) / α) - 2) := by rw [h1]

end Work.FTS.PhiStar.RadGreenSupport
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.BmCut =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

/-! # A `C²` cutoff family on `[0, π/2]` whose derivatives also vanish at the layer ends

For every `δ > 0` we construct a `C²` function `bmcut δ : ℝ → ℝ` with values in `[0,1]` which
is `1` on `[δ, π/2-δ]`, vanishes outside `(δ/2, π/2-δ/2)`, whose first and second derivatives
are `O(1/δ)` resp. `O(1/δ²)` with `δ`-independent constants, and whose first two derivatives
vanish *everywhere outside the two open layers* `(δ/2,δ) ∪ (π/2-δ, π/2-δ/2)` — including at
the boundary points `δ/2`, `δ`, `π/2-δ`, `π/2-δ/2`.

The construction is the product of two rescaled copies of `Real.smoothTransition`
(`0` on `(-∞,0]`, `1` on `[1,∞)`):

`bmcut δ θ = ψ(2θ/δ - 1) · ψ(2(π/2-θ)/δ - 1)`  for `δ ≤ π/4`,

and `bmcut δ = 0` for `δ > π/4` (where the plateau condition is vacuous).  The vanishing of
the derivatives at the boundary points of the layers uses `ψ'(0) = ψ''(0) = ψ'(1) = ψ''(1) = 0`
(`BmCutAux.st_deriv_eq_zero_of_nonpos` and friends). -/

/-! ## The cutoff family -/

/-- The cutoff of size `δ`. -/
def bmcut (δ : ℝ) : ℝ → ℝ :=
  if δ ≤ Real.pi / 4 then
    ramp (2 / δ) (-1) * ramp (-(2 / δ)) ((2 / δ) * (Real.pi / 2) - 1)
  else 0

theorem bmcut_of_le {δ : ℝ} (h : δ ≤ Real.pi / 4) :
    bmcut δ = ramp (2 / δ) (-1) * ramp (-(2 / δ)) ((2 / δ) * (Real.pi / 2) - 1) := by
  rw [bmcut]
  exact ite_eq_left h

theorem bmcut_of_gt {δ : ℝ} (h : ¬ δ ≤ Real.pi / 4) : bmcut δ = 0 := by
  rw [bmcut]
  exact ite_eq_right h

/-- Membership test for the complement of an open interval. -/
theorem not_mem_Ioo_or {x a b : ℝ} (h : x ∉ Set.Ioo a b) : x ≤ a ∨ b ≤ x := by
  by_contra hcon
  rw [not_or] at hcon
  exact h ⟨not_le.mp hcon.1, not_le.mp hcon.2⟩

/-! ## Elementary arithmetic for the two ramps -/

private lemma arg_low {δ θ : ℝ} (hδ : 0 < δ) (h : θ ≤ δ / 2) :
    (2 / δ) * θ + (-1) ≤ 0 := by
  have h2 : (0 : ℝ) < 2 / δ := by positivity
  have hm := mul_le_mul_of_nonneg_left h h2.le
  have hh : (2 / δ) * (δ / 2) = 1 := by field_simp
  linarith

private lemma arg_high {δ θ : ℝ} (hδ : 0 < δ) (h : δ ≤ θ) :
    1 ≤ (2 / δ) * θ + (-1) := by
  have h2 : (0 : ℝ) < 2 / δ := by positivity
  have hm := mul_le_mul_of_nonneg_left h h2.le
  have hh : (2 / δ) * δ = 2 := by field_simp
  linarith

private lemma narg_low {δ θ : ℝ} (hδ : 0 < δ) (h : Real.pi / 2 - δ / 2 ≤ θ) :
    (-(2 / δ)) * θ + ((2 / δ) * (Real.pi / 2) - 1) ≤ 0 := by
  have h2 : (0 : ℝ) < 2 / δ := by positivity
  have hm := mul_le_mul_of_nonneg_left h h2.le
  have hh : (2 / δ) * (Real.pi / 2 - δ / 2) = (2 / δ) * (Real.pi / 2) - 1 := by
    field_simp
  linarith

private lemma narg_high {δ θ : ℝ} (hδ : 0 < δ) (h : θ ≤ Real.pi / 2 - δ) :
    1 ≤ (-(2 / δ)) * θ + ((2 / δ) * (Real.pi / 2) - 1) := by
  have h2 : (0 : ℝ) < 2 / δ := by positivity
  have hm := mul_le_mul_of_nonneg_left h h2.le
  have hh : (2 / δ) * (Real.pi / 2 - δ) = (2 / δ) * (Real.pi / 2) - 2 := by
    field_simp
  linarith

/-! ## Vanishing of the derivatives of a ramp on the flat pieces -/

theorem deriv_ramp_eq_zero {a b θ : ℝ} (h : a * θ + b ≤ 0 ∨ 1 ≤ a * θ + b) :
    deriv (ramp a b) θ = 0 := by
  rcases h with h | h
  · rw [deriv_ramp, st_deriv_eq_zero_of_nonpos h, zero_mul]
  · rw [deriv_ramp, st_deriv_eq_zero_of_one_le h, zero_mul]

theorem deriv2_ramp_eq_zero {a b θ : ℝ} (h : a * θ + b ≤ 0 ∨ 1 ≤ a * θ + b) :
    deriv (deriv (ramp a b)) θ = 0 := by
  rcases h with h | h
  · rw [deriv2_ramp, st_deriv2_eq_zero_of_nonpos h, zero_mul, zero_mul]
  · rw [deriv2_ramp, st_deriv2_eq_zero_of_one_le h, zero_mul, zero_mul]

/-- Leibniz for the second derivative of a product. -/
theorem deriv2_mul_eq {f g : ℝ → ℝ} {θ : ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (hf' : DifferentiableAt ℝ (deriv f) θ)
    (hg' : DifferentiableAt ℝ (deriv g) θ) :
    deriv (deriv (f * g)) θ
      = deriv (deriv f) θ * g θ + 2 * (deriv f θ * deriv g θ) + f θ * deriv (deriv g) θ := by
  have h1 : deriv (f * g) = fun x => deriv f x * g x + f x * deriv g x := by
    funext x
    exact deriv_mul (hf x) (hg x)
  rw [h1]
  have hd1 : DifferentiableAt ℝ (fun x => deriv f x * g x) θ := hf'.mul hg.differentiableAt
  have hd2 : DifferentiableAt ℝ (fun x => f x * deriv g x) θ := hf.differentiableAt.mul hg'
  rw [show (fun x => deriv f x * g x + f x * deriv g x)
      = (fun x => deriv f x * g x) + (fun x => f x * deriv g x) from rfl]
  rw [deriv_add hd1 hd2]
  have e1 : deriv (fun x => deriv f x * g x) θ
      = deriv (deriv f) θ * g θ + deriv f θ * deriv g θ := by
    rw [show (fun x => deriv f x * g x) = deriv f * g from rfl, deriv_mul hf' hg.differentiableAt]
  have e2 : deriv (fun x => f x * deriv g x) θ
      = deriv f θ * deriv g θ + f θ * deriv (deriv g) θ := by
    rw [show (fun x => f x * deriv g x) = f * deriv g from rfl, deriv_mul hf.differentiableAt hg']
  rw [e1, e2]
  ring

/-! ## The main existence theorem -/

set_option maxHeartbeats 1000000 in
theorem exists_bmcut_supp : ∃ χ : ℝ → ℝ → ℝ, ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧
    (∀ δ : ℝ, 0 < δ → ContDiff ℝ 2 (χ δ)) ∧
    (∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, 0 ≤ χ δ θ ∧ χ δ θ ≤ 1) ∧
    (∀ δ : ℝ, 0 < δ → ∀ θ ∈ Set.Icc δ (Real.pi / 2 - δ), χ δ θ = 1) ∧
    (∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, θ ∉ Set.Ioo (δ / 2) (Real.pi / 2 - δ / 2) → χ δ θ = 0) ∧
    (∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, |deriv (χ δ) θ| ≤ K₁ / δ) ∧
    (∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, |deriv (deriv (χ δ)) θ| ≤ K₂ / δ ^ 2) ∧
    (∀ δ : ℝ, 0 < δ → ∀ θ : ℝ,
      (θ ∉ Set.Ioo (δ / 2) δ ∧ θ ∉ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 - δ / 2)) →
      deriv (χ δ) θ = 0 ∧ deriv (deriv (χ δ)) θ = 0) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hb₁, hb₂⟩ := st_bounds
  refine ⟨bmcut, 4 * C₁ + 1, 8 * C₂ + 8 * C₁ ^ 2 + 1, by linarith,
    by nlinarith [sq_nonneg C₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `ContDiff`
    intro δ hδ
    by_cases h4 : δ ≤ Real.pi / 4
    · rw [bmcut_of_le h4]
      exact (ramp_contDiff _ _).mul (ramp_contDiff _ _)
    · rw [bmcut_of_gt h4]
      exact contDiff_const
  · -- `0 ≤ χ δ θ ≤ 1`
    intro δ hδ θ
    by_cases h4 : δ ≤ Real.pi / 4
    · rw [bmcut_of_le h4]
      refine ⟨mul_nonneg (ramp_nonneg _ _ _) (ramp_nonneg _ _ _), ?_⟩
      calc ramp (2 / δ) (-1) θ * ramp (-(2 / δ)) ((2 / δ) * (Real.pi / 2) - 1) θ
          ≤ 1 * 1 := mul_le_mul (ramp_le_one _ _ _) (ramp_le_one _ _ _)
              (ramp_nonneg _ _ _) (by norm_num)
        _ = 1 := by norm_num
    · rw [bmcut_of_gt h4]
      exact ⟨le_refl 0, zero_le_one⟩
  · -- the plateau
    intro δ hδ θ hθ
    by_cases h4 : δ ≤ Real.pi / 4
    · rw [bmcut_of_le h4]
      simp only [Pi.mul_apply]
      rw [ramp_eq_one _ _ _ (arg_high hδ hθ.1), ramp_eq_one _ _ _ (narg_high hδ hθ.2), one_mul]
    · exfalso
      linarith [hθ.1, hθ.2, not_le.mp h4]
  · -- vanishing outside the transition region
    intro δ hδ θ hθ
    by_cases h4 : δ ≤ Real.pi / 4
    · rw [bmcut_of_le h4]
      simp only [Pi.mul_apply]
      rcases not_mem_Ioo_or hθ with h | h
      · rw [ramp_eq_zero _ _ _ (arg_low hδ h), zero_mul]
      · rw [ramp_eq_zero _ _ _ (narg_low hδ h), mul_zero]
    · exact congrFun (bmcut_of_gt h4) θ
  · -- first derivative bound
    intro δ hδ θ
    by_cases h4 : δ ≤ Real.pi / 4
    · rw [bmcut_of_le h4]
      have hb := abs_deriv_mul_le (f := ramp (2 / δ) (-1))
        (g := ramp (-(2 / δ)) ((2 / δ) * (Real.pi / 2) - 1)) (θ := θ)
        (ramp_diff _ _).differentiableAt (ramp_diff _ _).differentiableAt
        (deriv_ramp_bound hb₁ _ _ θ) (deriv_ramp_bound hb₁ _ _ θ)
        (ramp_nonneg _ _ _) (ramp_le_one _ _ _) (ramp_nonneg _ _ _) (ramp_le_one _ _ _)
      refine le_trans hb ?_
      have hA1 : |(2 : ℝ) / δ| = 2 / δ := abs_of_pos (by positivity)
      have hA2 : |(-(2 / δ))| = 2 / δ := by rw [abs_neg, hA1]
      rw [hA1, hA2]
      have hsum : C₁ * (2 / δ) + C₁ * (2 / δ) = 4 * C₁ / δ := by ring
      rw [hsum, div_le_div_iff_of_pos_right hδ]
      linarith
    · have hz : deriv (bmcut δ) θ = 0 := by
        rw [bmcut_of_gt h4]
        exact deriv_const θ 0
      rw [hz, abs_zero]
      positivity
  · -- second derivative bound
    intro δ hδ θ
    by_cases h4 : δ ≤ Real.pi / 4
    · rw [bmcut_of_le h4]
      have hb := abs_deriv2_mul_le (f := ramp (2 / δ) (-1))
        (g := ramp (-(2 / δ)) ((2 / δ) * (Real.pi / 2) - 1)) (θ := θ)
        (ramp_diff _ _) (ramp_diff _ _) (ramp_diffAt_deriv _ _ θ) (ramp_diffAt_deriv _ _ θ)
        (deriv_ramp_bound hb₁ _ _ θ) (deriv_ramp_bound hb₁ _ _ θ)
        (deriv2_ramp_bound hb₂ _ _ θ) (deriv2_ramp_bound hb₂ _ _ θ)
        (ramp_nonneg _ _ _) (ramp_le_one _ _ _) (ramp_nonneg _ _ _) (ramp_le_one _ _ _)
      refine le_trans hb ?_
      have hA1 : |(2 : ℝ) / δ| = 2 / δ := abs_of_pos (by positivity)
      have hA2 : |(-(2 / δ))| = 2 / δ := by rw [abs_neg, hA1]
      rw [hA1, hA2]
      have hval : C₂ * ((2 / δ) * (2 / δ)) + 2 * (C₁ * (2 / δ)) * (C₁ * (2 / δ))
          + C₂ * ((2 / δ) * (2 / δ)) = (8 * C₂ + 8 * C₁ ^ 2) / δ ^ 2 := by ring
      rw [hval, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < δ ^ 2)]
      linarith [sq_nonneg C₁]
    · have hz : deriv (deriv (bmcut δ)) θ = 0 := by
        rw [bmcut_of_gt h4]
        have hfun : deriv (0 : ℝ → ℝ) = (0 : ℝ → ℝ) := by
          funext t
          exact deriv_const t 0
        rw [hfun]
        exact deriv_const θ 0
      rw [hz, abs_zero]
      positivity
  · -- the derivative support
    intro δ hδ θ hθ
    obtain ⟨h1, h2⟩ := hθ
    have h1' := not_mem_Ioo_or h1
    have h2' := not_mem_Ioo_or h2
    by_cases h4 : δ ≤ Real.pi / 4
    · rw [bmcut_of_le h4]
      rcases h1' with h1 | h1
      · -- `θ ≤ δ / 2`: the first ramp is flat (its derivative vanishes everywhere there)
        have hfa : (2 / δ) * θ + (-1) ≤ 0 := arg_low hδ h1
        have hdf : deriv (ramp (2 / δ) (-1)) θ = 0 :=
          deriv_ramp_eq_zero (a := 2 / δ) (b := -1) (Or.inl hfa)
        have hd2f : deriv (deriv (ramp (2 / δ) (-1))) θ = 0 :=
          deriv2_ramp_eq_zero (a := 2 / δ) (b := -1) (Or.inl hfa)
        have hfv : ramp (2 / δ) (-1) θ = 0 := ramp_eq_zero _ _ _ hfa
        constructor
        · rw [deriv_mul (ramp_diff _ _).differentiableAt (ramp_diff _ _).differentiableAt,
            hdf, hfv]
          ring
        · rw [deriv2_mul_eq (ramp_diff _ _) (ramp_diff _ _) (ramp_diffAt_deriv _ _ θ)
              (ramp_diffAt_deriv _ _ θ), hdf, hd2f, hfv]
          ring
      · -- `δ ≤ θ`: the first ramp is flat `1`
        have hfg1 : 1 ≤ (2 / δ) * θ + (-1) := arg_high hδ h1
        have hdf : deriv (ramp (2 / δ) (-1)) θ = 0 :=
          deriv_ramp_eq_zero (Or.inr hfg1)
        have hd2f : deriv (deriv (ramp (2 / δ) (-1))) θ = 0 :=
          deriv2_ramp_eq_zero (Or.inr hfg1)
        rcases h2' with h2 | h2
        · -- `θ ≤ π/2 - δ`: the second ramp is flat `1`
          have hdg : deriv (ramp (-(2 / δ)) ((2 / δ) * (Real.pi / 2) - 1)) θ = 0 :=
            deriv_ramp_eq_zero (a := -(2 / δ)) (b := (2 / δ) * (Real.pi / 2) - 1)
              (Or.inr (narg_high hδ h2))
          have hd2g : deriv (deriv (ramp (-(2 / δ)) ((2 / δ) * (Real.pi / 2) - 1))) θ = 0 :=
            deriv2_ramp_eq_zero (a := -(2 / δ)) (b := (2 / δ) * (Real.pi / 2) - 1)
              (Or.inr (narg_high hδ h2))
          constructor
          · rw [deriv_mul (ramp_diff _ _).differentiableAt (ramp_diff _ _).differentiableAt,
              hdf, hdg]
            ring
          · rw [deriv2_mul_eq (ramp_diff _ _) (ramp_diff _ _) (ramp_diffAt_deriv _ _ θ)
                (ramp_diffAt_deriv _ _ θ), hdf, hd2f, hdg, hd2g]
            ring
        · -- `π/2 - δ/2 ≤ θ`: the second ramp is flat `0`
          have hdg : deriv (ramp (-(2 / δ)) ((2 / δ) * (Real.pi / 2) - 1)) θ = 0 :=
            deriv_ramp_eq_zero (a := -(2 / δ)) (b := (2 / δ) * (Real.pi / 2) - 1)
              (Or.inl (narg_low hδ h2))
          have hd2g : deriv (deriv (ramp (-(2 / δ)) ((2 / δ) * (Real.pi / 2) - 1))) θ = 0 :=
            deriv2_ramp_eq_zero (a := -(2 / δ)) (b := (2 / δ) * (Real.pi / 2) - 1)
              (Or.inl (narg_low hδ h2))
          constructor
          · rw [deriv_mul (ramp_diff _ _).differentiableAt (ramp_diff _ _).differentiableAt,
              hdf, hdg]
            ring
          · rw [deriv2_mul_eq (ramp_diff _ _) (ramp_diff _ _) (ramp_diffAt_deriv _ _ θ)
                (ramp_diffAt_deriv _ _ θ), hdf, hd2f, hdg, hd2g]
            ring
    · have h1z : deriv (bmcut δ) θ = 0 := by
        rw [bmcut_of_gt h4]
        exact deriv_const θ 0
      have h2z : deriv (deriv (bmcut δ)) θ = 0 := by
        rw [bmcut_of_gt h4]
        have hfun : deriv (0 : ℝ → ℝ) = (0 : ℝ → ℝ) := by
          funext t
          exact deriv_const t 0
        rw [hfun]
        exact deriv_const θ 0
      exact ⟨h1z, h2z⟩

end Work.FTS.PhiStar.Series
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.modeRatioLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

theorem modeRatioLe (m : ℕ) (hm : 1 ≤ m) :
    Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
        / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
      ≤ (5 / 4) * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  -- Unfold the eigenvalue `lam m = 2m(2m+5) = 2M(2M+5)` with `M = (m:ℝ)`.
  simp only [Work.FTS.PhiStar.Gegenbauer.lam]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := by linarith
  -- The denominator is positive, as is `M^{3/2}`.
  have hYpos : (0 : ℝ) < 2 * (m : ℝ) * (2 * (m : ℝ) + 5) * Real.sqrt (2 * (m : ℝ) + 1) := by
    positivity
  have hrpos : (0 : ℝ) < (m : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hmpos _
  -- `M^{3/2} = M √M`.
  have hpow : (m : ℝ) ^ (3 / 2 : ℝ) = (m : ℝ) * Real.sqrt (m : ℝ) := by
    have h32 : (3 : ℝ) / 2 = 1 + 1 / 2 := by norm_num
    rw [h32, Real.rpow_add hmpos, Real.rpow_one, ← Real.sqrt_eq_rpow]
  -- Clear the two positive denominators: it suffices to prove
  -- `√((2M+2)(2M+3)) · M^{3/2} ≤ (5/4)·2M(2M+5)·√(2M+1)`.
  rw [div_le_iff₀ hYpos]
  rw [show (5 / 4) * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹
          * (2 * (m : ℝ) * (2 * (m : ℝ) + 5) * Real.sqrt (2 * (m : ℝ) + 1))
        = ((5 / 4) * (2 * (m : ℝ) * (2 * (m : ℝ) + 5) * Real.sqrt (2 * (m : ℝ) + 1)))
            / ((m : ℝ) ^ (3 / 2 : ℝ)) from by ring]
  rw [le_div_iff₀ hrpos]
  rw [hpow]
  -- `√((2M+2)(2M+3)) ≤ 2M+3` since `(2M+2)(2M+3) ≤ (2M+3)^2`.
  have hsqrtA : Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) ≤ 2 * (m : ℝ) + 3 := by
    calc Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
        ≤ Real.sqrt ((2 * (m : ℝ) + 3) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 * (m : ℝ) + 3 := Real.sqrt_sq (by linarith)
  -- `√M ≤ √(2M+1)`.
  have hsqrtM : Real.sqrt (m : ℝ) ≤ Real.sqrt (2 * (m : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  calc Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) * ((m : ℝ) * Real.sqrt (m : ℝ))
      ≤ (2 * (m : ℝ) + 3) * ((m : ℝ) * Real.sqrt (m : ℝ)) :=
        mul_le_mul_of_nonneg_right hsqrtA (by positivity)
    _ ≤ (2 * (m : ℝ) + 3) * ((m : ℝ) * Real.sqrt (2 * (m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsqrtM hmnn) (by linarith)
    _ ≤ ((5 / 2) * (2 * (m : ℝ) + 5)) * ((m : ℝ) * Real.sqrt (2 * (m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 5 / 4 * (2 * (m : ℝ) * (2 * (m : ℝ) + 5) * Real.sqrt (2 * (m : ℝ) + 1)) := by ring

end Work.FTS.PhiStar.Series.Deleg
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.rpowMajorant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

theorem rpowMajorant :
    (∀ (m : ℕ), 1 ≤ m → ∀ r : ℝ, r ≤ 3 →
        ((m : ℝ) + 1) ^ (r + 3 / 2)
          ≤ 8 * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) ∧
    (∀ D : ℝ, Summable fun m : ℕ => D * (((m : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) ∧
    (∀ (m : ℕ), 1 ≤ m → ∀ e : ℝ, 3 / 2 ≤ e →
        (((m : ℝ) + 1) ^ e)⁻¹ ≤ (((m : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
  refine ⟨?_, ?_, ?_⟩
  · -- The `rpow` majorant: `(m+1)^{r+3/2} ≤ 8 λ_m² √(2m+1)`.
    intro m hm r hr
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hbase : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith
    have hpos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
    -- monotonicity in the exponent, since `r + 3/2 ≤ 9/2` and the base is `≥ 1`
    have h1 : ((m : ℝ) + 1) ^ (r + 3 / 2) ≤ ((m : ℝ) + 1) ^ ((9 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    -- `(m+1)^{9/2} = (m+1)^4 √(m+1)`
    have h2 : ((m : ℝ) + 1) ^ ((9 : ℝ) / 2) = ((m : ℝ) + 1) ^ 4 * Real.sqrt ((m : ℝ) + 1) := by
      have hh : ((9 : ℝ) / 2) = 4 + 1 / 2 := by norm_num
      rw [hh, Real.rpow_add hpos]
      rw [show ((m : ℝ) + 1) ^ (4 : ℝ) = ((m : ℝ) + 1) ^ 4 by norm_num]
      rw [← Real.sqrt_eq_rpow]
    -- the polynomial bound `(m+1)^4 ≤ 32 m² (2m+5)²`
    have h3 : ((m : ℝ) + 1) ^ 4 ≤ 32 * (m : ℝ) ^ 2 * (2 * (m : ℝ) + 5) ^ 2 := by
      nlinarith [hmR]
    have h4 : Real.sqrt ((m : ℝ) + 1) ≤ Real.sqrt (2 * (m : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    have h5 : ((m : ℝ) + 1) ^ 4 * Real.sqrt ((m : ℝ) + 1)
        ≤ 32 * (m : ℝ) ^ 2 * (2 * (m : ℝ) + 5) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) :=
      mul_le_mul h3 h4 (Real.sqrt_nonneg _) (by positivity)
    have h6 : 32 * (m : ℝ) ^ 2 * (2 * (m : ℝ) + 5) ^ 2
        = 8 * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 := by
      simp only [Work.FTS.PhiStar.Gegenbauer.lam]; ring
    calc ((m : ℝ) + 1) ^ (r + 3 / 2) ≤ ((m : ℝ) + 1) ^ ((9 : ℝ) / 2) := h1
      _ = ((m : ℝ) + 1) ^ 4 * Real.sqrt ((m : ℝ) + 1) := h2
      _ ≤ 32 * (m : ℝ) ^ 2 * (2 * (m : ℝ) + 5) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) := h5
      _ = 8 * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) := by rw [h6]
  · -- The comparison series `∑ (m+1)^{-3/2}` converges.
    intro D
    have h : Summable (fun n : ℕ => (((n : ℕ) : ℝ) ^ ((3 : ℝ) / 2))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    have h2 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2))⁻¹) :=
      (summable_nat_add_iff (f := fun n : ℕ => (((n : ℕ) : ℝ) ^ ((3 : ℝ) / 2))⁻¹) 1).mpr h
    have h3 : Summable (fun m : ℕ => (((m : ℝ) + 1) ^ ((3 : ℝ) / 2))⁻¹) := by
      simpa [Nat.cast_add, Nat.cast_one] using h2
    exact h3.mul_left D
  · -- `(m+1)^{-e} ≤ (m+1)^{-3/2}` for `e ≥ 3/2`, base `≥ 1`.
    intro m hm e he
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hbase : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith
    have hx : (0 : ℝ) ≤ (m : ℝ) + 1 := by linarith
    rw [← Real.rpow_neg hx e, ← Real.rpow_neg hx (3 / 2)]
    exact Real.rpow_le_rpow_of_exponent_le hbase (by linarith)

end Work.FTS.PhiStar.Series.Deleg
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.termEstimates =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

/-- `x ^ (3/2) = x √x` for `x > 0`. -/
private lemma rpow_three_half {x : ℝ} (hx : 0 < x) : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  have h : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
  rw [h, Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- Growth of the Gegenbauer eigenvalue: for `m ≥ 1`,
`(m+1)^4 √(m+1) ≤ (lam m)^2 √(2m+1)`.
Indeed `m + 1 ≤ 2m` and `lam m = 2m(2m+5) ≥ 4m²`, so both sides are at least
`16 m^4 √(2m)`. -/
private lemma core_le (m : ℕ) (hm : 1 ≤ m) :
    ((m : ℝ) + 1) ^ 4 * Real.sqrt ((m : ℝ) + 1)
      ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) := by
  have hy1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hle : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by linarith
  have hx4 : ((m : ℝ) + 1) ^ 4 ≤ 16 * (m : ℝ) ^ 4 := by
    have h : ((m : ℝ) + 1) ^ 4 ≤ (2 * (m : ℝ)) ^ 4 := pow_le_pow_left₀ (by linarith) hle 4
    calc ((m : ℝ) + 1) ^ 4 ≤ (2 * (m : ℝ)) ^ 4 := h
      _ = 16 * (m : ℝ) ^ 4 := by ring
  have hlam_ge : 4 * (m : ℝ) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
    simp only [Work.FTS.PhiStar.Gegenbauer.lam]
    nlinarith [hy1]
  have hlam2 : 16 * (m : ℝ) ^ 4 ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 := by
    have h0 : (0 : ℝ) ≤ 4 * (m : ℝ) ^ 2 := by positivity
    calc 16 * (m : ℝ) ^ 4 = (4 * (m : ℝ) ^ 2) ^ 2 := by ring
      _ ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 := pow_le_pow_left₀ h0 hlam_ge 2
  have hsx : Real.sqrt ((m : ℝ) + 1) ≤ Real.sqrt (2 * (m : ℝ)) :=
    Real.sqrt_le_sqrt (by linarith)
  have hs2 : Real.sqrt (2 * (m : ℝ)) ≤ Real.sqrt (2 * (m : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  calc ((m : ℝ) + 1) ^ 4 * Real.sqrt ((m : ℝ) + 1)
      ≤ (16 * (m : ℝ) ^ 4) * Real.sqrt (2 * (m : ℝ)) :=
        mul_le_mul hx4 hsx (Real.sqrt_nonneg _) (by positivity)
    _ ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) :=
        mul_le_mul hlam2 hs2 (Real.sqrt_nonneg _) (by positivity)

/-- The decay factor `M` times the growth factor `L` dominates `(m+1)^3`:
for `m ≥ 1`,
`(m+1)^3 ≤ ((m+1)^(3/2))⁻¹ * ((lam m)^2 √(2m+1))`. -/
private lemma x3_le_ML (m : ℕ) (hm : 1 ≤ m) :
    ((m : ℝ) + 1) ^ 3 ≤ (((m : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹ *
      ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) := by
  have hx : (0 : ℝ) < (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := by positivity
    linarith
  have hb : 0 < ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) :=
    mul_pos hx (Real.sqrt_pos.2 hx)
  have hcore := core_le m hm
  have h1 : ((m : ℝ) + 1) ^ 3 * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))
      ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) := by
    calc ((m : ℝ) + 1) ^ 3 * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))
        = ((m : ℝ) + 1) ^ 4 * Real.sqrt ((m : ℝ) + 1) := by ring
      _ ≤ _ := hcore
  have h2 : ((m : ℝ) + 1) ^ 3 ≤
      ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) /
        (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)) := (le_div_iff₀ hb).mpr h1
  rw [rpow_three_half hx]
  rw [inv_mul_eq_div]
  exact h2

theorem termEstimates (α : ℝ) (hα : 0 < α) (Cdec CB Kφ : ℝ) (hCdec : 0 < Cdec)
    (hCB : 0 < CB) (hKφ : 0 < Kφ) (cθ : ℝ) (hcθ : 0 < cθ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (m : ℕ), 1 ≤ m →
      let L := (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)
      let M := (((m : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹
      (α ^ 2 * Cdec * CB * Kφ / L * (3 * ((m : ℝ) + 1)) ≤ D * M) ∧
      (α ^ 2 * Cdec * CB * Kφ / L * (900 * ((m : ℝ) + 1) ^ 2 / cθ ^ 2) ≤ D * M) ∧
      (α ^ 2 * Cdec * CB * Kφ / L * (27000 * ((m : ℝ) + 1) ^ 3 / cθ ^ 4) ≤ D * M) ∧
      (α ^ 2 * Cdec * CB * Kφ / L * (9000 * ((m : ℝ) + 1) ^ 2 / cθ ^ 3) ≤ D * M) := by
  have hApos : 0 < α ^ 2 * Cdec * CB * Kφ := by positivity
  have hKpos : 0 < 3 + 900 / cθ ^ 2 + 27000 / cθ ^ 4 + 9000 / cθ ^ 3 := by positivity
  refine ⟨α ^ 2 * Cdec * CB * Kφ * (3 + 900 / cθ ^ 2 + 27000 / cθ ^ 4 + 9000 / cθ ^ 3),
    by positivity, ?_⟩
  intro m hm
  dsimp only
  have hx : (0 : ℝ) < (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := by positivity
    linarith
  have hx1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hLpos : 0 < (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) := by
    have h : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
      simp only [Work.FTS.PhiStar.Gegenbauer.lam]
      have hm0 : (0 : ℝ) < (m : ℝ) := by
        have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith
      nlinarith [hm0]
    exact mul_pos (pow_pos h 2) (Real.sqrt_pos.2 (by linarith))
  have hML := x3_le_ML m hm
  have hDpos : 0 < α ^ 2 * Cdec * CB * Kφ *
      (3 + 900 / cθ ^ 2 + 27000 / cθ ^ 4 + 9000 / cθ ^ 3) := by positivity
  -- the four estimates have the common shape: it suffices that the polynomial factor is
  -- bounded by `C (m+1)^3` with `C` one of the three constants below, since `M·L ≥ (m+1)^3`.
  have step : ∀ P C : ℝ, P ≤ C * ((m : ℝ) + 1) ^ 3 →
      C ≤ 3 + 900 / cθ ^ 2 + 27000 / cθ ^ 4 + 9000 / cθ ^ 3 →
      α ^ 2 * Cdec * CB * Kφ /
          ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) * P
        ≤ (α ^ 2 * Cdec * CB * Kφ * (3 + 900 / cθ ^ 2 + 27000 / cθ ^ 4 + 9000 / cθ ^ 3))
            * (((m : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹ := by
    intro P C hP hC
    rw [div_mul_eq_mul_div]
    rw [div_le_iff₀ hLpos]
    rw [rpow_three_half hx]
    rw [rpow_three_half hx] at hML
    have h3 : (0 : ℝ) ≤ ((m : ℝ) + 1) ^ 3 := by positivity
    calc α ^ 2 * Cdec * CB * Kφ * P
        ≤ α ^ 2 * Cdec * CB * Kφ * (C * ((m : ℝ) + 1) ^ 3) :=
          mul_le_mul_of_nonneg_left hP hApos.le
      _ = (α ^ 2 * Cdec * CB * Kφ * C) * ((m : ℝ) + 1) ^ 3 := by ring
      _ ≤ (α ^ 2 * Cdec * CB * Kφ *
            (3 + 900 / cθ ^ 2 + 27000 / cθ ^ 4 + 9000 / cθ ^ 3)) * ((m : ℝ) + 1) ^ 3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC hApos.le) h3
      _ ≤ (α ^ 2 * Cdec * CB * Kφ *
            (3 + 900 / cθ ^ 2 + 27000 / cθ ^ 4 + 9000 / cθ ^ 3)) *
            ((((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹ *
              ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hML hDpos.le
      _ = (α ^ 2 * Cdec * CB * Kφ *
            (3 + 900 / cθ ^ 2 + 27000 / cθ ^ 4 + 9000 / cθ ^ 3)) *
            (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹ *
              ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine step (3 * ((m : ℝ) + 1)) 3 ?_ ?_
    · have h13 : ((m : ℝ) + 1) ^ 1 ≤ ((m : ℝ) + 1) ^ 3 := pow_le_pow_right₀ hx1 (by norm_num)
      simpa [pow_one] using mul_le_mul_of_nonneg_left h13 (by norm_num : (0 : ℝ) ≤ 3)
    · have h1 : (0 : ℝ) ≤ 900 / cθ ^ 2 := by positivity
      have h2 : (0 : ℝ) ≤ 27000 / cθ ^ 4 := by positivity
      have h3 : (0 : ℝ) ≤ 9000 / cθ ^ 3 := by positivity
      linarith
  · refine step (900 * ((m : ℝ) + 1) ^ 2 / cθ ^ 2) (900 / cθ ^ 2) ?_ ?_
    · have h23 : ((m : ℝ) + 1) ^ 2 ≤ ((m : ℝ) + 1) ^ 3 := pow_le_pow_right₀ hx1 (by norm_num)
      have hc : (0 : ℝ) ≤ 900 / cθ ^ 2 := by positivity
      calc 900 * ((m : ℝ) + 1) ^ 2 / cθ ^ 2 = 900 / cθ ^ 2 * ((m : ℝ) + 1) ^ 2 := by ring
        _ ≤ 900 / cθ ^ 2 * ((m : ℝ) + 1) ^ 3 := mul_le_mul_of_nonneg_left h23 hc
    · have h1 : (0 : ℝ) ≤ 27000 / cθ ^ 4 := by positivity
      have h3 : (0 : ℝ) ≤ 9000 / cθ ^ 3 := by positivity
      have h4 : (0 : ℝ) ≤ 3 := by norm_num
      linarith
  · refine step (27000 * ((m : ℝ) + 1) ^ 3 / cθ ^ 4) (27000 / cθ ^ 4) ?_ ?_
    · have h : 27000 * ((m : ℝ) + 1) ^ 3 / cθ ^ 4 = 27000 / cθ ^ 4 * ((m : ℝ) + 1) ^ 3 := by ring
      exact le_of_eq h
    · have h2 : (0 : ℝ) ≤ 900 / cθ ^ 2 := by positivity
      have h3 : (0 : ℝ) ≤ 9000 / cθ ^ 3 := by positivity
      have h4 : (0 : ℝ) ≤ 3 := by norm_num
      linarith
  · refine step (9000 * ((m : ℝ) + 1) ^ 2 / cθ ^ 3) (9000 / cθ ^ 3) ?_ ?_
    · have h23 : ((m : ℝ) + 1) ^ 2 ≤ ((m : ℝ) + 1) ^ 3 := pow_le_pow_right₀ hx1 (by norm_num)
      have hc : (0 : ℝ) ≤ 9000 / cθ ^ 3 := by positivity
      calc 9000 * ((m : ℝ) + 1) ^ 2 / cθ ^ 3 = 9000 / cθ ^ 3 * ((m : ℝ) + 1) ^ 2 := by ring
        _ ≤ 9000 / cθ ^ 3 * ((m : ℝ) + 1) ^ 3 := mul_le_mul_of_nonneg_left h23 hc
    · have h1 : (0 : ℝ) ≤ 900 / cθ ^ 2 := by positivity
      have h2 : (0 : ℝ) ≤ 27000 / cθ ^ 4 := by positivity
      have h4 : (0 : ℝ) ≤ 3 := by norm_num
      linarith

end Work.FTS.PhiStar.Series.Deleg
end
-- ===== merged: Submission.Work.FTS.PressureOn.offPlanes.IbpProd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integration by parts with one exceptional hyperplane, in product form

`Work.FTS.PressureOn.offPlanes.ibp_off_plane_prod`: the `(E × ℝ)`-version of
`ibp_except_zero`, obtained by Fubini (`MeasureTheory.integral_prod`) and the fibrewise
one-dimensional statement.  The exceptional set is the hyperplane `{t = 0}`.
-/

open MeasureTheory Filter Topology

namespace Work.FTS.PressureOn.offPlanes

theorem ibp_off_plane_prod {E : Type*} [MeasurableSpace E] [MeasureSpace E]
    {μ : Measure E} [SFinite μ]
    {G Gp Ψ Ψp : E × ℝ → ℝ}
    (hΨGp : Integrable (fun p => Ψ p * Gp p) (μ.prod volume))
    (hΨpG : Integrable (fun p => Ψp p * G p) (μ.prod volume))
    (hGc : ∀ᵐ y ∂μ, Continuous (fun t => G (y, t)))
    (hΨc : ∀ᵐ y ∂μ, Continuous (fun t => Ψ (y, t)))
    (hΨd : ∀ᵐ y ∂μ, ∀ t, HasDerivAt (fun s => Ψ (y, s)) (Ψp (y, t)) t)
    (hGd : ∀ᵐ y ∂μ, ∀ t, t ≠ 0 → HasDerivAt (fun s => G (y, s)) (Gp (y, t)) t)
    (hbot : ∀ᵐ y ∂μ, Tendsto (fun t => Ψ (y, t) * G (y, t)) atBot (𝓝 0))
    (htop : ∀ᵐ y ∂μ, Tendsto (fun t => Ψ (y, t) * G (y, t)) atTop (𝓝 0)) :
    ∫ p, Ψ p * Gp p ∂(μ.prod volume) = -∫ p, Ψp p * G p ∂(μ.prod volume) := by
  have h1 : ∫ p, Ψ p * Gp p ∂(μ.prod volume)
      = ∫ y, (∫ t, Ψ (y, t) * Gp (y, t)) ∂μ := integral_prod _ hΨGp
  have h2 : ∫ p, Ψp p * G p ∂(μ.prod volume)
      = ∫ y, (∫ t, Ψp (y, t) * G (y, t)) ∂μ := integral_prod _ hΨpG
  rw [h1, h2, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hΨGp.prod_right_ae, hΨpG.prod_right_ae, hGc, hΨc, hΨd, hGd, hbot, htop]
    with y h1y h2y hcy hcy' hdy hdy' hby hty
  exact ibp_except_zero hdy hdy' hcy hcy' h1y h2y hby hty

end Work.FTS.PressureOn.offPlanes
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux.slotIdents.pth_pth_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux.slotIdents



end Work.FTS.StrongEps.E5Aux.slotIdents
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.AbsL12densLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

/-
The generic domination step: if the angular integrand `K θ * |Y s θ|` is dominated by
`A * cos θ` on `Iθ = [0,π/2]`, then the density `L12dens K Y s = ∫ θ in Iθ, K θ * Y s θ / s`
is bounded by `A / s`.  Uses `norm_integral_le_integral_norm`, `abs_mul`, `abs_div`,
`abs_of_nonneg (K ≥ 0 on Iθ)`, `MeasureTheory.integral_mono_of_nonneg` against the
integrable majorant `A * cos θ` (continuous on the compact interval) and
`∫ θ in Iθ, Real.cos θ = 1` (interval integral: `∫_0^{π/2} cos = 1`).
-/
/-! ## Elementary angular facts used below -/

/-- `K θ = 3 sin θ cos²θ` is nonnegative on `Iθ = [0,π/2]`. -/
lemma K_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  rw [Work.Spaces.K]
  exact mul_nonneg (mul_nonneg (by norm_num)
    (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])))
    (sq_nonneg _)

/-- The normalisation `∫_0^{π/2} cos θ dθ = 1`. -/
lemma integral_cos_Iθ : (∫ θ in Work.Spaces.Iθ, Real.cos θ) = 1 := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ Real.pi / 2 by linarith [Real.pi_pos])]
  rw [integral_cos, Real.sin_pi_div_two, Real.sin_zero]
  norm_num

theorem AbsL12densLe {Y : ℝ → ℝ → ℝ} {s A : ℝ} (hs : 0 < s) (hA : 0 ≤ A)
    (h : ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.K θ * |Y s θ| ≤ A * Real.cos θ) :
    |Work.FM.L12dens Work.Spaces.K Y s| ≤ A / s := by
  have _hA : 0 ≤ A := hA
  -- `L12dens K Y s` is the set integral of `K θ * Y s θ / s` over `Iθ = [0,π/2]`.
  have hmono : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ * Y s θ / s|)
      ≤ ∫ θ in Work.Spaces.Iθ, A * Real.cos θ / s := by
    refine MeasureTheory.setIntegral_mono_of_nonneg (fun θ _ => abs_nonneg _) ?_ ?_
    · intro θ hθ
      rw [abs_div, abs_mul, abs_of_nonneg (K_nonneg_of_mem_Iθ hθ), abs_of_pos hs]
      exact div_le_div_of_nonneg_right (h θ hθ) hs.le
    · rw [Work.Spaces.Iθ]
      exact (continuous_const.mul Real.continuous_cos).div_const s |>.integrableOn_Icc
  have h2 : (∫ θ in Work.Spaces.Iθ, A * Real.cos θ / s)
      = A / s * (∫ θ in Work.Spaces.Iθ, Real.cos θ) := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  calc |Work.FM.L12dens Work.Spaces.K Y s|
      ≤ ∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ * Y s θ / s| := by
        show |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Y s θ / s| ≤ _
        exact MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ θ in Work.Spaces.Iθ, A * Real.cos θ / s := hmono
    _ = A / s * (∫ θ in Work.Spaces.Iθ, Real.cos θ) := h2
    _ = A / s := by rw [integral_cos_Iθ, mul_one]

end Work.FTS.StrongEps.E5Aux2
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.AngIntK =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.StrongEps.E5Aux2

/-!
# `∫_{Iθ} K θ = 1`

The angular normalisation `∫_{[0,π/2]} 3 sin θ cos²θ dθ = 1` of the paper
(`K θ = 3 sin θ cos²θ`, the weight of the `φ`-variable in the `(ρ,θ)` reduction).

The primitive of `K` is `-cos³`, since `(-cos³θ)' = 3 sin θ cos²θ`, so the integral is
`cos³ 0 - cos³ (π/2) = 1 - 0 = 1`.  The set integral over `Iθ = [0,π/2]` is converted to the
interval integral `∫_0^{π/2}` by `MeasureTheory.integral_Icc_eq_integral_Ioc` followed by
`intervalIntegral.integral_of_le` (the removed point `{0}` is null).
-/

/-- `K` is continuous, hence interval integrable. -/
theorem continuous_K : Continuous (fun θ : ℝ => Work.Spaces.K θ) := by
  unfold Work.Spaces.K
  fun_prop

/-- The primitive `-cos³` of `K θ = 3 sin θ cos²θ`. -/
theorem hasDerivAt_neg_cos_cube (x : ℝ) :
    HasDerivAt (fun θ : ℝ => -(Real.cos θ) ^ 3) (Work.Spaces.K x) x := by
  have h3 : HasDerivAt (fun θ : ℝ => -(Real.cos θ) ^ 3)
      (-(3 * (Real.cos x) ^ (3 - 1) * (-Real.sin x))) x :=
    ((Real.hasDerivAt_cos x).pow 3).neg
  convert h3 using 1
  rw [Work.Spaces.K]
  norm_num
  ring

/-- `∫_{[0,π/2]} K θ dθ = 1`, as an interval integral. -/
theorem integral_K_interval :
    (∫ θ in (0 : ℝ)..(Real.pi / 2), Work.Spaces.K θ) = 1 := by
  have hint : IntervalIntegrable (fun θ : ℝ => Work.Spaces.K θ) volume
      (0 : ℝ) (Real.pi / 2) := continuous_K.intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_neg_cos_cube x) hint
  rw [h]
  simp [Real.cos_pi_div_two, Real.cos_zero]

theorem AngIntK : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ) = 1 := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hIθ : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) := rfl
  rw [hIθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hpi]
  exact integral_K_interval

end Work.FTS.StrongEps.E5Aux2
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.EulerOdeZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

/-- Multiplying a solution of the constant-coefficient equation `X'' + aX' + bX = 0` by the
exponential `t ↦ exp (c * t)` gives a solution of `Y'' + (a - 2c)Y' + (b - a c + c²)Y = 0`. -/
lemma mul_exp_ode {a b c : ℝ} {X : ℝ → ℝ} (hX : ContDiff ℝ 2 X)
    (hode : ∀ t, deriv (deriv X) t + a * deriv X t + b * X t = 0) :
    ∀ t, deriv (deriv (fun t => X t * Real.exp (c * t))) t
      + (a - 2*c) * deriv (fun t => X t * Real.exp (c*t)) t
      + (b - a*c + c^2) * (X t * Real.exp (c*t)) = 0 := by
  have hg : ∀ s, HasDerivAt (fun t => Real.exp (c*t)) (c * Real.exp (c*s)) s := by
    intro s
    have h1 : HasDerivAt (fun t : ℝ => c*t) c s := by
      simpa using (hasDerivAt_id s).const_mul c
    simpa [mul_comm] using h1.exp
  have hg2 : ∀ s, HasDerivAt (fun t => c * Real.exp (c*t)) (c * (c * Real.exp (c*s))) s := by
    intro s
    simpa using (hg s).const_mul c
  have hd1 : ∀ s, deriv (fun t => X t * Real.exp (c*t)) s
      = deriv X s * Real.exp (c*s) + X s * (c * Real.exp (c*s)) := by
    intro s
    exact (((hX.differentiable (by norm_num)).differentiableAt.hasDerivAt).mul (hg s)).deriv
  have hd2 : ∀ s, deriv (deriv (fun t => X t * Real.exp (c*t))) s
      = (deriv (deriv X) s * Real.exp (c*s) + deriv X s * (c*Real.exp (c*s)))
        + (deriv X s * (c*Real.exp (c*s)) + X s * (c*(c*Real.exp (c*s)))) := by
    intro s
    have hfun : deriv (fun t => X t * Real.exp (c*t))
        = fun t => deriv X t * Real.exp (c*t) + X t * (c * Real.exp (c*t)) := funext hd1
    rw [hfun]
    have hA : HasDerivAt (fun t => deriv X t * Real.exp (c*t))
        (deriv (deriv X) s * Real.exp (c*s) + deriv X s * (c*Real.exp (c*s))) s :=
      (((hX.differentiable_deriv_two).differentiableAt).hasDerivAt).mul (hg s)
    have hB : HasDerivAt (fun t => X t * (c * Real.exp (c*t)))
        (deriv X s * (c*Real.exp (c*s)) + X s * (c*(c*Real.exp (c*s)))) s :=
      ((hX.differentiable (by norm_num)).differentiableAt.hasDerivAt).mul (hg2 s)
    exact (hA.add hB).deriv
  intro t
  rw [hd2 t, hd1 t]
  linear_combination (Real.exp (c * t)) * hode t

/-- **Vanishing of `L²` solutions of a constant-coefficient second order equation.** If `U` is `C²`
on `ℝ`, solves `U'' + a U' + b U = 0` and is square-integrable, then `U ≡ 0`.

Proof by the classical classification of solutions, with `D = a² - 4b`:
* `D > 0`: `U = c₁ e^{r₁t} + c₂ e^{r₂t}` with the two distinct real roots, and such a combination
  is never `L²` on `ℝ` unless it vanishes;
* `D = 0`: `U = (c₁ + c₂t) e^{rt}`, same conclusion;
* `D < 0`: `U = e^{-at/2}(A cos ωt + B sin ωt)` with `ω > 0`, and `e^{ct}(A cos ωt + B sin ωt)²`
  is never integrable on `ℝ` when `ω ≠ 0` unless `A = B = 0`. -/
lemma ode_lin2_L2_eq_zero {a b : ℝ} {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (hode : ∀ t, deriv (deriv U) t + a * deriv U t + b * U t = 0)
    (hint : MeasureTheory.Integrable (fun t => (U t) ^ 2)) : ∀ t, U t = 0 := by
  rcases lt_trichotomy (a ^ 2 - 4 * b) 0 with hD | hD | hD
  · -- `D < 0` : oscillatory solutions
    obtain ⟨hb, hω⟩ : b - a^2/4 = (Real.sqrt (b - a^2/4))^2 ∧ 0 < Real.sqrt (b - a^2/4) := by
      have h1 : 0 < b - a^2/4 := by nlinarith
      exact ⟨(Real.sq_sqrt (le_of_lt h1)).symm, Real.sqrt_pos.2 h1⟩
    obtain ⟨A, B, hAB⟩ := ode_rep_trig hω hb hU hode
    have hI : MeasureTheory.Integrable (fun t => Real.exp ((-a) * t)
        * (A * Real.cos (Real.sqrt (b - a^2/4) * t)
            + B * Real.sin (Real.sqrt (b - a^2/4) * t)) ^ 2) := by
      refine hint.congr ?_
      filter_upwards with t
      rw [hAB t, mul_pow]
      have hexp : Real.exp (-(a * t / 2)) ^ 2 = Real.exp ((-a) * t) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      rw [hexp]
    obtain ⟨hA, hB⟩ := not_integrable_exp_trig (by positivity : Real.sqrt (b - a^2/4) ≠ 0) hI
    intro t
    rw [hAB t, hA, hB]; ring
  · -- `D = 0` : double root
    have ha : a = -2 * (-a/2) := by ring
    have hb : b = (-a/2)^2 := by nlinarith
    obtain ⟨c1, c2, h12⟩ := ode_rep_double ha hb hU hode
    have hI : MeasureTheory.Integrable (fun t => ((c1 + c2 * t) * Real.exp ((-a/2) * t)) ^ 2) := by
      refine hint.congr ?_
      filter_upwards with t
      rw [h12 t]
    obtain ⟨hc1, hc2⟩ := not_integrable_poly_exp (r := -a/2) hI
    intro t
    rw [h12 t, hc1, hc2]; ring
  · -- `D > 0` : two distinct real roots
    set s := Real.sqrt (a^2 - 4*b) with hsdef
    have hsq : s ^ 2 = a^2 - 4*b := Real.sq_sqrt (le_of_lt hD)
    set r1 := (-a + s)/2 with hr1
    set r2 := (-a - s)/2 with hr2
    have hsum : r1 + r2 = -a := by rw [hr1, hr2]; ring
    have hprod : r1 * r2 = b := by rw [hr1, hr2]; nlinarith
    have hlt : r2 < r1 := by rw [hr1, hr2]; linarith [Real.sqrt_pos.2 hD]
    obtain ⟨c1, c2, h12⟩ := ode_rep_distinct hsum hprod (ne_of_gt hlt) hU hode
    have hI : MeasureTheory.Integrable (fun t => (c1 * Real.exp (r1 * t) + c2 * Real.exp (r2 * t)) ^ 2) := by
      refine hint.congr ?_
      filter_upwards with t
      rw [h12 t]
    obtain ⟨hc1, hc2⟩ := not_integrable_two_exp hlt hI
    intro t
    rw [h12 t, hc1, hc2]; ring

theorem EulerOdeZero {p q ν : ℝ} (hν : 0 < ν) {V : ℝ → ℝ} (hV : ContDiffOn ℝ 2 V (Set.Ioi 0))
    (hode : ∀ z ∈ Set.Ioi 0, z ^ 2 * deriv (deriv V) z + p * z * deriv V z + q * V z = 0)
    (hint : MeasureTheory.IntegrableOn (fun z => (V z) ^ 2 * z ^ ((-1 : ℝ) - ν)) (Set.Ioi 0)) :
    ∀ z ∈ Set.Ioi 0, V z = 0 := by
  have hνpos : 0 < ν := hν
  -- Step 1: substitute `z = exp t`.
  have hWcd : ContDiff ℝ 2 (fun t => V (Real.exp t)) := by
    rw [← contDiffOn_univ]
    exact hV.comp ((Real.contDiff_exp.contDiffOn).of_le le_top) (fun t _ => Real.exp_pos t)
  have hW1 : ∀ t, deriv (fun s => V (Real.exp s)) t = deriv V (Real.exp t) * Real.exp t := by
    intro t
    exact (((hV.contDiffAt (isOpen_Ioi.mem_nhds (Real.exp_pos t))).differentiableAt
      (by norm_num)).hasDerivAt.comp t (Real.hasDerivAt_exp t)).deriv
  have hW2 : ∀ t, deriv (deriv (fun s => V (Real.exp s))) t
      = deriv (deriv V) (Real.exp t) * Real.exp t * Real.exp t + deriv V (Real.exp t) * Real.exp t := by
    intro t
    have h1 : deriv (fun s => V (Real.exp s)) = fun s => deriv V (Real.exp s) * Real.exp s := by
      funext s; exact hW1 s
    have hdVd : DifferentiableAt ℝ (deriv V) (Real.exp t) :=
      ((hV.contDiffAt (isOpen_Ioi.mem_nhds (Real.exp_pos t))).derivWithin (m := 1)
        (by norm_num)).differentiableAt (by norm_num)
    rw [h1]
    exact (((hdVd.hasDerivAt).comp t (Real.hasDerivAt_exp t)).mul (Real.hasDerivAt_exp t)).deriv
  have hodeW : ∀ t, deriv (deriv (fun s => V (Real.exp s))) t
      + (p - 1) * deriv (fun s => V (Real.exp s)) t + q * V (Real.exp t) = 0 := by
    intro t
    rw [hW2 t, hW1 t]
    have h1 := hode (Real.exp t) (Real.exp_pos t)
    linear_combination h1
  -- Step 2: absorb the weight `z ^ (-ν)`, i.e. multiply by `exp (-(ν/2) ·)` in the `t` variable.
  have hY := mul_exp_ode (a := p - 1) (b := q) (c := -ν/2) hWcd hodeW
  have hUode : ∀ t, deriv (deriv (fun s => V (Real.exp s) * Real.exp ((-ν/2)*s))) t
      + (p - 1 + ν) * deriv (fun s => V (Real.exp s) * Real.exp ((-ν/2)*s)) t
      + (ν^2/4 + (p-1)*ν/2 + q) * (V (Real.exp t) * Real.exp ((-ν/2)*t)) = 0 := by
    intro t
    have h := hY t
    rw [show (p-1) - 2*(-ν/2) = p - 1 + ν by ring,
        show q - (p-1)*(-ν/2) + (-ν/2)^2 = ν^2/4 + (p-1)*ν/2 + q by ring] at h
    exact h
  have hUcd : ContDiff ℝ 2 (fun s => V (Real.exp s) * Real.exp ((-ν/2)*s)) :=
    hWcd.mul (by fun_prop)
  -- Step 3: transport the integrability hypothesis to the `t` variable.
  have hbase : MeasureTheory.Integrable (fun t => (V (Real.exp t))^2 * Real.exp (-(ν*t))) := by
    have h := (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Set.univ) (f := Real.exp) (f' := Real.exp)
      MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (Real.exp_injective.injOn) (fun z => (V z)^2 * z^((-1:ℝ)-ν)))
    have him : Real.exp '' (Set.univ : Set ℝ) = Set.Ioi 0 := by
      rw [Set.image_univ]; exact Real.range_exp
    rw [him] at h
    have h2 := h.1 hint
    rw [MeasureTheory.integrableOn_univ] at h2
    refine h2.congr ?_
    filter_upwards with x
    rw [Real.abs_exp, smul_eq_mul]
    have hpow : Real.exp x ^ ((-1:ℝ) - ν) = Real.exp (-(ν*x)) / Real.exp x := by
      rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp,
        show x * (-1 - ν) = -(ν*x) - x by ring, Real.exp_sub]
    rw [hpow, show Real.exp x * (V (Real.exp x)^2 * (Real.exp (-(ν*x)) / Real.exp x))
        = V (Real.exp x)^2 * (Real.exp x * (Real.exp (-(ν*x)) / Real.exp x)) by ring]
    field_simp
  have hUint : MeasureTheory.Integrable (fun s => (V (Real.exp s) * Real.exp ((-ν/2)*s))^2) := by
    refine hbase.congr ?_
    filter_upwards with s
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1
    congr 1
    push_cast
    ring
  -- Step 4: an `L²` solution of the constant-coefficient equation vanishes identically.
  have hzero : ∀ t, V (Real.exp t) * Real.exp ((-ν/2)*t) = 0 :=
    ode_lin2_L2_eq_zero hUcd hUode hUint
  intro z hz
  have h := hzero (Real.log z)
  rw [Real.exp_log hz] at h
  exact (mul_eq_zero.mp h).resolve_right (Real.exp_ne_zero _)

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.EulerWeakAffine =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

set_option autoImplicit false

/-- A function vanishing outside the open interval `(a,b)` has the same integral over `a..b` as
over the whole line. -/
theorem intervalIntegral_eq_integral_of_vanishing {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ}
    (hφ : ∀ x ∉ Set.Ioo a b, φ x = 0) : (∫ x in a..b, φ x) = ∫ x, φ x := by
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => hφ x (fun hc => hx ⟨hc.1, hc.2.le⟩))

/-- If `F` is locally integrable on `(a,b)` and `ψ` is continuous with compact support in `(a,b)`,
then `ψ * F` is globally integrable. -/
theorem integrable_mul_of_locallyIntegrableOn_Ioo {a b : ℝ} {F ψ : ℝ → ℝ}
    (hF : LocallyIntegrableOn F (Set.Ioo a b)) (hψcont : Continuous ψ)
    (hψcs : HasCompactSupport ψ) (hψsup : tsupport ψ ⊆ Set.Ioo a b) :
    Integrable (fun x => ψ x * F x) := by
  let K : Set ℝ := tsupport ψ
  have hK : IsCompact K := hψcs
  have hFK : IntegrableOn F K := hF.integrableOn_compact_subset hψsup hK
  have hFind : Integrable (K.indicator F) := by
    rw [integrable_indicator_iff hK.measurableSet]
    exact hFK
  have hkey : Integrable (fun x => ψ x • (K.indicator F) x) :=
    LocallyIntegrable.integrable_smul_left_of_hasCompactSupport hFind.locallyIntegrable hψcont hψcs
  have hprod : (fun x => ψ x * F x) = fun x => ψ x • (K.indicator F) x := by
    funext x
    by_cases hx : x ∈ K
    · simp [Set.indicator_of_mem hx, smul_eq_mul]
    · have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [Set.indicator_of_notMem hx, hz]
  rwa [hprod]

/-- **The two-moment elimination.**  Given the moment identities of a normalised bump `χ` on
`(a,b)`, the pairing of `F` against an arbitrary test function is a fixed linear combination of
the first two moments of that test function. -/
theorem momentRepresentation {a b : ℝ} {F : ℝ → ℝ}
    (hF : LocallyIntegrableOn F (Set.Ioo a b))
    (h : ∀ ψ : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      tsupport ψ ⊆ Set.Ioo a b → (∫ t in a..b, ψ t) = 0 → (∫ t in a..b, t * ψ t) = 0 →
      (∫ t in a..b, ψ t * F t) = 0)
    {χ : ℝ → ℝ} (hχcd : ContDiff ℝ ∞ χ) (hχcs : HasCompactSupport χ)
    (hχsup : tsupport χ ⊆ Set.Ioo a b) (hχint : (∫ t in a..b, χ t) = 1)
    (hχd0 : (∫ t in a..b, deriv χ t) = 0) (hχd1 : (∫ t in a..b, t * deriv χ t) = -1) :
    ∃ c₁ c₂ : ℝ, ∀ ψ : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      tsupport ψ ⊆ Set.Ioo a b →
      (∫ t in a..b, ψ t * F t) = c₁ * (∫ t in a..b, ψ t) + c₂ * (∫ t in a..b, t * ψ t) := by
  -- the first moment of `χ`, and the dual pair `η₁`, `η₂`
  set c : ℝ := ∫ t in a..b, t * χ t with hc
  set η₁ : ℝ → ℝ := fun t => χ t + c * deriv χ t with hη₁
  set η₂ : ℝ → ℝ := fun t => (-1 : ℝ) * deriv χ t with hη₂
  have hχcont : Continuous χ := hχcd.continuous
  have hdχ : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχcd).2
  have hdcont : Continuous (deriv χ) := hdχ.continuous
  have hcd : ∀ n : ℕ, ContDiff ℝ n χ := fun n => hχcd.of_le (WithTop.coe_le_coe.mpr le_top)
  have hdcd : ∀ n : ℕ, ContDiff ℝ n (deriv χ) := fun n => hdχ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hη₁cd : ∀ n : ℕ, ContDiff ℝ n η₁ := by
    intro n
    rw [hη₁]
    simpa only [smul_eq_mul] using (hcd n).add ((hdcd n).const_smul c)
  have hη₂cd : ∀ n : ℕ, ContDiff ℝ n η₂ := by
    intro n
    rw [hη₂]
    simpa only [smul_eq_mul] using (hdcd n).const_smul (-1 : ℝ)
  have hη₁cont : Continuous η₁ := (hη₁cd 0).continuous
  have hη₂cont : Continuous η₂ := (hη₂cd 0).continuous
  -- interval integrability of the pieces
  have hχII : IntervalIntegrable χ volume a b := hχcont.intervalIntegrable a b
  have hdII : IntervalIntegrable (deriv χ) volume a b := hdcont.intervalIntegrable a b
  have htχII : IntervalIntegrable (fun t : ℝ => t * χ t) volume a b :=
    (continuous_id.mul hχcont).intervalIntegrable a b
  have htdII : IntervalIntegrable (fun t : ℝ => t * deriv χ t) volume a b :=
    (continuous_id.mul hdcont).intervalIntegrable a b
  have hη₁II : IntervalIntegrable η₁ volume a b := hη₁cont.intervalIntegrable a b
  have hη₂II : IntervalIntegrable η₂ volume a b := hη₂cont.intervalIntegrable a b
  -- supports
  have hη₁sup : tsupport η₁ ⊆ Set.Ioo a b := by
    rw [hη₁]
    refine (tsupport_binop_subset (fun x y : ℝ => x + y) (by norm_num) χ
      (fun t => c * deriv χ t)).trans ?_
    exact union_subset hχsup (((tsupport_mul_subset_right (f := fun _ : ℝ => c)).trans
      (tsupport_deriv_subset)).trans hχsup)
  have hη₂sup : tsupport η₂ ⊆ Set.Ioo a b := by
    rw [hη₂]
    exact ((tsupport_mul_subset_right (f := fun _ : ℝ => (-1 : ℝ))).trans
      (tsupport_deriv_subset)).trans hχsup
  have hη₁cs : HasCompactSupport η₁ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_tsupport η₁).trans (hη₁sup.trans Ioo_subset_Icc_self))
  have hη₂cs : HasCompactSupport η₂ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_tsupport η₂).trans (hη₂sup.trans Ioo_subset_Icc_self))
  -- the moment identities making `(η₁, η₂)` the dual basis of `(M₀, M₁)`
  have hm₁ : (∫ t in a..b, η₁ t) = 1 := by
    have hs : (∫ t in a..b, η₁ t) = (∫ t in a..b, χ t) + ∫ t in a..b, c * deriv χ t := by
      calc (∫ t in a..b, η₁ t) = ∫ t in a..b, (χ t + c * deriv χ t) :=
            intervalIntegral.integral_congr (fun t _ => by simp only [hη₁])
        _ = _ := intervalIntegral.integral_add hχII (hdII.const_mul c)
    rw [hs, intervalIntegral.integral_const_mul, hχd0, mul_zero, add_zero, hχint]
  have hm₂ : (∫ t in a..b, t * η₁ t) = 0 := by
    have hs : (∫ t in a..b, t * η₁ t)
        = (∫ t in a..b, t * χ t) + ∫ t in a..b, c * (t * deriv χ t) := by
      calc (∫ t in a..b, t * η₁ t) = ∫ t in a..b, (t * χ t + c * (t * deriv χ t)) :=
            intervalIntegral.integral_congr (fun t _ => by simp only [hη₁]; ring)
        _ = _ := intervalIntegral.integral_add htχII (htdII.const_mul c)
    rw [hs, intervalIntegral.integral_const_mul, hχd1, ← hc]
    ring
  have hn₁ : (∫ t in a..b, η₂ t) = 0 := by
    have hs : (∫ t in a..b, η₂ t) = ∫ t in a..b, (-1 : ℝ) * deriv χ t :=
      intervalIntegral.integral_congr (fun t _ => by simp only [hη₂])
    rw [hs, intervalIntegral.integral_const_mul, hχd0, mul_zero]
  have hn₂ : (∫ t in a..b, t * η₂ t) = 1 := by
    have hs : (∫ t in a..b, t * η₂ t) = ∫ t in a..b, (-1 : ℝ) * (t * deriv χ t) :=
      intervalIntegral.integral_congr (fun t _ => by simp only [hη₂]; ring)
    rw [hs, intervalIntegral.integral_const_mul, hχd1]
    norm_num
  -- the two candidate constants
  have hIFη₁ : Integrable (fun t => η₁ t * F t) :=
    integrable_mul_of_locallyIntegrableOn_Ioo hF hη₁cont hη₁cs hη₁sup
  have hIFη₂ : Integrable (fun t => η₂ t * F t) :=
    integrable_mul_of_locallyIntegrableOn_Ioo hF hη₂cont hη₂cs hη₂sup
  refine ⟨∫ t in a..b, η₁ t * F t, ∫ t in a..b, η₂ t * F t, ?_⟩
  intro ψ hψcd hψcs hψsup
  -- the corrected test function
  set M : ℝ := ∫ t in a..b, ψ t with hM
  set N : ℝ := ∫ t in a..b, t * ψ t with hN
  set ψ₀ : ℝ → ℝ := fun t => ψ t - M * η₁ t - N * η₂ t with hψ₀
  have hψcont : Continuous ψ := (hψcd 0).continuous
  have hψII : IntervalIntegrable ψ volume a b := hψcont.intervalIntegrable a b
  have htψII : IntervalIntegrable (fun t : ℝ => t * ψ t) volume a b :=
    (continuous_id.mul hψcont).intervalIntegrable a b
  have hψ₀cd : ∀ n : ℕ, ContDiff ℝ n ψ₀ := by
    intro n
    rw [hψ₀]
    have h1 : ContDiff ℝ (↑n) (fun t : ℝ => ψ t - M * η₁ t) := by
      simpa only [smul_eq_mul] using (hψcd n).sub ((hη₁cd n).const_smul M)
    simpa only [smul_eq_mul] using h1.sub ((hη₂cd n).const_smul N)
  have hψ₀sup : tsupport ψ₀ ⊆ Set.Ioo a b := by
    rw [hψ₀]
    refine (tsupport_binop_subset (fun x y : ℝ => x - y) (by norm_num)
      (fun t => ψ t - M * η₁ t) (fun t => N * η₂ t)).trans ?_
    refine union_subset ?_ (((tsupport_mul_subset_right (f := fun _ : ℝ => N)).trans hη₂sup))
    refine (tsupport_binop_subset (fun x y : ℝ => x - y) (by norm_num) ψ
      (fun t => M * η₁ t)).trans ?_
    exact union_subset hψsup (((tsupport_mul_subset_right (f := fun _ : ℝ => M)).trans hη₁sup))
  have hψ₀cs : HasCompactSupport ψ₀ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_tsupport ψ₀).trans (hψ₀sup.trans Ioo_subset_Icc_self))
  -- its moments vanish
  have hψ₀m0 : (∫ t in a..b, ψ₀ t) = 0 := by
    have hMη₁ : IntervalIntegrable (fun t : ℝ => M * η₁ t) volume a b := hη₁II.const_mul M
    have hNη₂ : IntervalIntegrable (fun t : ℝ => N * η₂ t) volume a b := hη₂II.const_mul N
    calc (∫ t in a..b, ψ₀ t) = ∫ t in a..b, (ψ t - (M * η₁ t + N * η₂ t)) :=
          intervalIntegral.integral_congr (fun t _ => by simp only [hψ₀]; ring)
      _ = (∫ t in a..b, ψ t) - ∫ t in a..b, (M * η₁ t + N * η₂ t) :=
          intervalIntegral.integral_sub hψII (hMη₁.add hNη₂)
      _ = (∫ t in a..b, ψ t) - ((∫ t in a..b, M * η₁ t) + ∫ t in a..b, N * η₂ t) := by
          rw [intervalIntegral.integral_add hMη₁ hNη₂]
      _ = M - (M * (∫ t in a..b, η₁ t) + N * (∫ t in a..b, η₂ t)) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ← hM]
      _ = 0 := by rw [hm₁, hn₁]; ring
  have hψ₀m1 : (∫ t in a..b, t * ψ₀ t) = 0 := by
    have hMη₁ : IntervalIntegrable (fun t : ℝ => M * (t * η₁ t)) volume a b :=
      ((continuous_id.mul hη₁cont).intervalIntegrable a b).const_mul M
    have hNη₂ : IntervalIntegrable (fun t : ℝ => N * (t * η₂ t)) volume a b :=
      ((continuous_id.mul hη₂cont).intervalIntegrable a b).const_mul N
    calc (∫ t in a..b, t * ψ₀ t)
        = ∫ t in a..b, (t * ψ t - (M * (t * η₁ t) + N * (t * η₂ t))) :=
          intervalIntegral.integral_congr (fun t _ => by simp only [hψ₀]; ring)
      _ = (∫ t in a..b, t * ψ t) - ∫ t in a..b, (M * (t * η₁ t) + N * (t * η₂ t)) :=
          intervalIntegral.integral_sub htψII (hMη₁.add hNη₂)
      _ = (∫ t in a..b, t * ψ t)
            - ((∫ t in a..b, M * (t * η₁ t)) + ∫ t in a..b, N * (t * η₂ t)) := by
          rw [intervalIntegral.integral_add hMη₁ hNη₂]
      _ = N - (M * (∫ t in a..b, t * η₁ t) + N * (∫ t in a..b, t * η₂ t)) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ← hN]
      _ = 0 := by rw [hm₂, hn₂]; ring
  have hkey : (∫ t in a..b, ψ₀ t * F t) = 0 := h ψ₀ hψ₀cd hψ₀cs hψ₀sup hψ₀m0 hψ₀m1
  -- expanding the pairing of `ψ₀` with `F`
  have hIFψ : Integrable (fun t => ψ t * F t) :=
    integrable_mul_of_locallyIntegrableOn_Ioo hF hψcont hψcs hψsup
  have hsplit : (∫ t in a..b, ψ₀ t * F t)
      = (∫ t in a..b, ψ t * F t) - M * (∫ t in a..b, η₁ t * F t)
        - N * (∫ t in a..b, η₂ t * F t) := by
    have h1 : IntervalIntegrable (fun t : ℝ => ψ t * F t) volume a b := hIFψ.intervalIntegrable
    have h2 : IntervalIntegrable (fun t : ℝ => M * (η₁ t * F t)) volume a b :=
      hIFη₁.intervalIntegrable.const_mul M
    have h3 : IntervalIntegrable (fun t : ℝ => N * (η₂ t * F t)) volume a b :=
      hIFη₂.intervalIntegrable.const_mul N
    calc (∫ t in a..b, ψ₀ t * F t)
        = ∫ t in a..b, ((ψ t * F t - M * (η₁ t * F t)) - N * (η₂ t * F t)) :=
          intervalIntegral.integral_congr (fun t _ => by simp only [hψ₀]; ring)
      _ = (∫ t in a..b, (ψ t * F t - M * (η₁ t * F t)))
            - ∫ t in a..b, N * (η₂ t * F t) :=
          intervalIntegral.integral_sub (h1.sub h2) h3
      _ = ((∫ t in a..b, ψ t * F t) - ∫ t in a..b, M * (η₁ t * F t))
            - ∫ t in a..b, N * (η₂ t * F t) := by rw [intervalIntegral.integral_sub h1 h2]
      _ = _ := by rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hgoal : (∫ t in a..b, ψ t * F t)
      = (∫ t in a..b, η₁ t * F t) * M + (∫ t in a..b, η₂ t * F t) * N := by
    linarith [hkey, hsplit]
  exact hgoal

/-- **Orthogonality to test functions with two vanishing moments forces affinity.**  If a locally
integrable `F` on `(a,b)` is orthogonal (as a distribution) to every smooth compactly supported
test function on `(a,b)` whose zeroth and first moments vanish, then `F` is almost everywhere
affine on `(a,b)`. -/
theorem EulerWeakAffine {a b : ℝ} (hab : a < b) {F : ℝ → ℝ} (hF : MeasureTheory.LocallyIntegrableOn F (Set.Ioo a b))
    (h : ∀ ψ : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo a b →
      (∫ t in a..b, ψ t) = 0 → (∫ t in a..b, t * ψ t) = 0 → (∫ t in a..b, ψ t * F t) = 0) :
    ∃ c₁ c₂ : ℝ, ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioo a b)), F t = c₁ + c₂ * t := by
  obtain ⟨χ, hχcd, hχcs, hχsup, hχint, hχd0, hχd1⟩ := existsBumpMoments hab
  obtain ⟨c₁, c₂, hkey⟩ := momentRepresentation hF h hχcd hχcs hχsup hχint hχd0 hχd1
  refine ⟨c₁, c₂, ?_⟩
  -- `F - (c₁ + c₂ ·)` is orthogonal to every test function
  have hfli : LocallyIntegrableOn (fun t => F t - (c₁ + c₂ * t)) (Set.Ioo a b) :=
    hF.sub (((continuous_const.add (continuous_const.mul continuous_id)).locallyIntegrable).locallyIntegrableOn _)
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioo a b → F t - (c₁ + c₂ * t) = 0 := by
    refine IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero isOpen_Ioo hfli ?_
    intro ψ hψcd hψcs hψsup
    have hψcd' : ∀ n : ℕ, ContDiff ℝ n ψ := fun n => hψcd.of_le (WithTop.coe_le_coe.mpr le_top)
    have hψcont : Continuous ψ := (hψcd' 0).continuous
    have hIFψ : Integrable (fun t => ψ t * F t) :=
      integrable_mul_of_locallyIntegrableOn_Ioo hF hψcont hψcs hψsup
    have hIψ : Integrable ψ := hψcont.integrable_of_hasCompactSupport hψcs
    have htψ : Integrable (fun t => t * ψ t) :=
      (continuous_id.mul hψcont).integrable_of_hasCompactSupport hψcs.mul_left
    have h1 : (∫ t in a..b, ψ t * (F t - (c₁ + c₂ * t))) = 0 := by
      have hIFψII : IntervalIntegrable (fun t : ℝ => ψ t * F t) volume a b := hIFψ.intervalIntegrable
      have hIψII : IntervalIntegrable ψ volume a b := hψcont.intervalIntegrable a b
      have htψII : IntervalIntegrable (fun t : ℝ => t * ψ t) volume a b :=
        (continuous_id.mul hψcont).intervalIntegrable a b
      calc (∫ t in a..b, ψ t * (F t - (c₁ + c₂ * t)))
          = ∫ t in a..b, (ψ t * F t - c₁ * ψ t - c₂ * (t * ψ t)) :=
            intervalIntegral.integral_congr (fun t _ => by ring)
        _ = (∫ t in a..b, ψ t * F t) - c₁ * (∫ t in a..b, ψ t)
              - c₂ * (∫ t in a..b, t * ψ t) := by
            rw [intervalIntegral.integral_sub (hIFψII.sub (hIψII.const_mul c₁)) (htψII.const_mul c₂),
              intervalIntegral.integral_sub hIFψII (hIψII.const_mul c₁),
              intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        _ = 0 := by rw [hkey ψ hψcd' hψcs hψsup]; ring
    have hvan : ∀ x ∉ Set.Ioo a b, ψ x * (F x - (c₁ + c₂ * x)) = 0 := by
      intro x hx
      have hxψ : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun hc => hx (hψsup hc))
      rw [hxψ, zero_mul]
    have hconv : (∫ x, ψ x • (F x - (c₁ + c₂ * x)))
        = ∫ x in a..b, ψ x * (F x - (c₁ + c₂ * x)) := by
      simp only [smul_eq_mul]
      exact (intervalIntegral_eq_integral_of_vanishing hab.le hvan).symm
    rw [hconv, h1]
  -- transfer the a.e. statement to the restricted measure
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hae] with t ht hmem
  linarith [ht hmem]

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.EulerWeakClassical =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open MeasureTheory Set Filter
open scoped Topology ContDiff

theorem EulerWeakClassical {α L b : ℝ} (hα : 0 < α) (hb : 0 < b) {W : ℝ → ℝ}
    (hW : MeasureTheory.LocallyIntegrableOn W (Set.Ioi 0)) {c₁ c₂ : ℝ}
    (haff : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioo 0 b)),
      -(α ^ 2 * t ^ 2 * W t) - α * (5 + α) * (∫ z in t..b, W z * z) + L * (∫ z in t..b, (z - t) * W z)
        = c₁ + c₂ * t) :
    ∃ V : ℝ → ℝ, ContDiffOn ℝ 2 V (Set.Ioo 0 b) ∧
      (∀ t ∈ Set.Ioo 0 b, α ^ 2 * t ^ 2 * deriv (deriv V) t + α * (3 * α - 5) * t * deriv V t
        + (α ^ 2 - 5 * α - L) * V t = 0) ∧ V =ᵐ[MeasureTheory.volume.restrict (Set.Ioo 0 b)] W := by
  have hαne : α ≠ 0 := ne_of_gt hα
  set I : Set ℝ := Set.Ioo 0 b with hI
  have hIopen : IsOpen I := by rw [hI]; exact isOpen_Ioo
  have hImeas : MeasurableSet I := hIopen.measurableSet
  have hIIoi : I ⊆ Set.Ioi (0 : ℝ) := by rw [hI]; exact Set.Ioo_subset_Ioi_self
  have hWz : MeasureTheory.LocallyIntegrableOn (fun z => W z * z) (Set.Ioi 0) := by
    have hfun : (fun z : ℝ => W z * z) = fun z => z * W z := by funext z; ring
    rw [hfun]
    exact locallyIntegrableOn_mul_id hW
  let GW : ℝ → ℝ := fun t => ∫ z in t..b, W z * z
  let HW : ℝ → ℝ := fun t => ∫ z in t..b, W z
  let FW : ℝ → ℝ := fun t => -(c₁ + c₂ * t) - α * (5 + α) * GW t + L * (GW t - t * HW t)
  let V : ℝ → ℝ := fun t => FW t / (α ^ 2 * t ^ 2)
  have hsplit : ∀ t ∈ Set.Ioi (0 : ℝ), (∫ z in t..b, (z - t) * W z) = GW t - t * HW t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hsub : Set.uIcc t b ⊆ Set.Ioi (0 : ℝ) := by
      rcases le_total t b with h | h
      · rw [Set.uIcc_of_le h]; intro x hx; exact lt_of_lt_of_le ht0 hx.1
      · rw [Set.uIcc_of_ge h]; intro x hx; exact lt_of_lt_of_le hb hx.1
    have hWint : MeasureTheory.IntegrableOn W (Set.uIcc t b) :=
      hW.integrableOn_compact_subset hsub isCompact_uIcc
    have hWzint : MeasureTheory.IntegrableOn (fun z => W z * z) (Set.uIcc t b) :=
      hWz.integrableOn_compact_subset hsub isCompact_uIcc
    have h1 : IntervalIntegrable W MeasureTheory.volume t b := hWint.intervalIntegrable
    have h2 : IntervalIntegrable (fun z => W z * z) MeasureTheory.volume t b :=
      hWzint.intervalIntegrable
    have h3 : IntervalIntegrable (fun z => t * W z) MeasureTheory.volume t b := h1.const_mul t
    calc ∫ z in t..b, (z - t) * W z
        = ∫ z in t..b, (W z * z - t * W z) :=
            intervalIntegral.integral_congr fun z _ => by ring
      _ = (∫ z in t..b, W z * z) - (∫ z in t..b, t * W z) :=
            intervalIntegral.integral_sub h2 h3
      _ = (∫ z in t..b, W z * z) - t * (∫ z in t..b, W z) := by
            rw [intervalIntegral.integral_const_mul]
      _ = GW t - t * HW t := by simp only [GW, HW]
  have hFWeq : FW =ᵐ[MeasureTheory.volume.restrict I] (fun t => α ^ 2 * t ^ 2 * W t) := by
    filter_upwards [haff, MeasureTheory.ae_restrict_mem hImeas] with t ht hmem
    have hsp := hsplit t hmem.1
    rw [hsp] at ht
    simp only [GW, HW, FW] at ht ⊢
    linarith
  have hVeq : V =ᵐ[MeasureTheory.volume.restrict I] W := by
    filter_upwards [hFWeq, MeasureTheory.ae_restrict_mem hImeas] with t ht hmem
    have hne : α ^ 2 * t ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hαne) (pow_ne_zero 2 (ne_of_gt hmem.1))
    simp only [V]
    rw [ht]
    exact mul_div_cancel_left₀ (W t) hne
  have hHWcont : ContinuousOn HW (Set.Ioi (0 : ℝ)) := by
    simp only [HW]; exact continuousOn_integral_left hb hW
  have hGWcont : ContinuousOn GW (Set.Ioi (0 : ℝ)) := by
    simp only [GW]; exact continuousOn_integral_left hb hWz
  have hFWcont : ContinuousOn FW (Set.Ioi (0 : ℝ)) := by
    simp only [FW]
    fun_prop
  have hVcont : ContinuousOn V (Set.Ioi (0 : ℝ)) := by
    simp only [V]
    have hden : ContinuousOn (fun t : ℝ => α ^ 2 * t ^ 2) (Set.Ioi 0) := by fun_prop
    exact hFWcont.div hden fun t ht =>
      mul_ne_zero (pow_ne_zero 2 hαne) (pow_ne_zero 2 (ne_of_gt ht))
  let H : ℝ → ℝ := fun t => ∫ z in t..b, V z
  let G : ℝ → ℝ := fun t => ∫ z in t..b, V z * z
  let F : ℝ → ℝ := fun t => -(c₁ + c₂ * t) - α * (5 + α) * G t + L * (G t - t * H t)
  have hVGcont : ContinuousOn (fun z : ℝ => V z * z) (Set.Ioi (0 : ℝ)) :=
    hVcont.mul continuousOn_id
  have hHc1 : ContDiffOn ℝ 1 H I := (contDiffOn_one_integral_left hb hVcont).1.mono hIIoi
  have hGc1 : ContDiffOn ℝ 1 G I := (contDiffOn_one_integral_left hb hVGcont).1.mono hIIoi
  have hHderiv : ∀ t ∈ I, deriv H t = -V t :=
    fun t ht => (contDiffOn_one_integral_left hb hVcont).2 t (hIIoi ht)
  have hGderiv : ∀ t ∈ I, deriv G t = -(V t * t) :=
    fun t ht => (contDiffOn_one_integral_left hb hVGcont).2 t (hIIoi ht)
  have hFc1 : ContDiffOn ℝ 1 F I := by
    simp only [F]
    have hA : ContDiffOn ℝ 1 (fun t : ℝ => -(c₁ + c₂ * t)) I := by fun_prop
    have hB : ContDiffOn ℝ 1 (fun t : ℝ => α * (5 + α) * G t) I :=
      (contDiffOn_const (c := α * (5 + α))).mul hGc1
    have hC : ContDiffOn ℝ 1 (fun t : ℝ => L * (G t - t * H t)) I :=
      (contDiffOn_const (c := L)).mul (hGc1.sub (contDiffOn_id.mul hHc1))
    exact (hA.sub hB).add hC
  have hGH : ∀ t ∈ I, G t = GW t ∧ H t = HW t := by
    intro t ht
    have ha : (0 : ℝ) < t := ht.1
    have hab : t < b := ht.2
    have hae : ∀ᵐ x ∂(MeasureTheory.volume), x ∈ Set.uIoc t b → V x = W x := by
      have h1 : ∀ᵐ x ∂(MeasureTheory.volume), x ∈ Set.Ioo (0 : ℝ) b → V x = W x :=
        MeasureTheory.ae_imp_of_ae_restrict hVeq
      have h2 : ∀ᵐ x ∂(MeasureTheory.volume), x ≠ b := MeasureTheory.Measure.ae_ne volume b
      filter_upwards [h1, h2] with x hx1 hxb hxu
      rw [Set.uIoc_of_le hab.le] at hxu
      exact hx1 ⟨lt_trans ha hxu.1, lt_of_le_of_ne hxu.2 hxb⟩
    constructor
    · simp only [G, GW]
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hae] with x hx hxu
      rw [hx hxu]
    · simp only [H, HW]
      exact intervalIntegral.integral_congr_ae hae
  have hVF : ∀ t ∈ I, V t = F t / (α ^ 2 * t ^ 2) := by
    intro t ht
    obtain ⟨hGt, hHt⟩ := hGH t ht
    have hFeq : FW t = F t := by simp only [FW, F, hGt, hHt]
    simp only [V]
    rw [hFeq]
  have hE1 : ∀ t ∈ I, F t = α ^ 2 * t ^ 2 * V t := by
    intro t ht
    have hne : α ^ 2 * t ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hαne) (pow_ne_zero 2 (ne_of_gt ht.1))
    rw [hVF t ht, mul_div_cancel₀ (F t) hne]
  have hVc1 : ContDiffOn ℝ 1 V I := by
    have hden : ContDiffOn ℝ 1 (fun t : ℝ => α ^ 2 * t ^ 2) I := by fun_prop
    have hdiv : ContDiffOn ℝ 1 (fun t : ℝ => F t / (α ^ 2 * t ^ 2)) I :=
      hFc1.div hden fun t ht =>
        mul_ne_zero (pow_ne_zero 2 hαne) (pow_ne_zero 2 (ne_of_gt ht.1))
    exact hdiv.congr fun t ht => hVF t ht
  -- Step 10: first derivative of `F`
  let DF : ℝ → ℝ := fun t => -c₂ + α * (5 + α) * (V t * t) - L * H t
  have hFderiv : ∀ t ∈ I, deriv F t = DF t := by
    intro t ht
    have hGA : HasDerivAt G (-(V t * t)) t := by
      have hd : DifferentiableAt ℝ G t :=
        (hGc1.differentiableOn (by norm_num)).differentiableAt (hIopen.mem_nhds ht)
      have h := hd.hasDerivAt
      rwa [hGderiv t ht] at h
    have hHA : HasDerivAt H (-(V t)) t := by
      have hd : DifferentiableAt ℝ H t :=
        (hHc1.differentiableOn (by norm_num)).differentiableAt (hIopen.mem_nhds ht)
      have h := hd.hasDerivAt
      rwa [hHderiv t ht] at h
    have hA : HasDerivAt (fun s : ℝ => -(c₁ + c₂ * s)) (-c₂) t := by
      have h1 : HasDerivAt (fun s : ℝ => c₂ * s) c₂ t := by
        have hh : HasDerivAt (fun s : ℝ => c₂ * s) (c₂ * 1) t :=
          (hasDerivAt_id t).const_mul c₂
        rw [mul_one] at hh
        exact hh
      exact (h1.const_add c₁).neg
    have hB : HasDerivAt (fun s : ℝ => α * (5 + α) * G s) (α * (5 + α) * (-(V t * t))) t :=
      hGA.const_mul (α * (5 + α))
    have hC : HasDerivAt (fun s : ℝ => L * (G s - s * H s))
        (L * (-(V t * t) - (1 * H t + t * (-(V t))))) t :=
      (hGA.sub ((hasDerivAt_id t).mul hHA)).const_mul L
    have hmain : HasDerivAt F
        (-c₂ - α * (5 + α) * (-(V t * t)) + L * (-(V t * t) - (1 * H t + t * (-(V t))))) t :=
      (hA.sub hB).add hC
    rw [hmain.deriv]
    simp only [DF]
    ring
  -- quadratic auxiliary
  have hsqderiv : ∀ t : ℝ, deriv (fun s : ℝ => s ^ 2) t = 2 * t := by
    intro t
    have h1 : deriv (fun s : ℝ => s) t = 1 := (hasDerivAt_id t).deriv
    have h := deriv_pow (f := fun s : ℝ => s) (x := t)
      (by fun_prop : DifferentiableAt ℝ (fun s : ℝ => s) t) 2
    rw [h1] at h
    simpa [Nat.reduceSub, pow_one, mul_one] using h
  have hsqHas : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    intro t
    have hd : DifferentiableAt ℝ (fun s : ℝ => s ^ 2) t := by fun_prop
    have h := hd.hasDerivAt
    rwa [hsqderiv t] at h
  have hquad : ∀ t : ℝ, deriv (fun s : ℝ => α ^ 2 * s ^ 2) t = 2 * α ^ 2 * t := by
    intro t
    rw [deriv_const_mul (α ^ 2) (hsqHas t).differentiableAt, hsqderiv t]
    ring
  have hquadHas : ∀ t : ℝ, HasDerivAt (fun s : ℝ => α ^ 2 * s ^ 2) (2 * α ^ 2 * t) t := by
    intro t
    have hd : DifferentiableAt ℝ (fun s : ℝ => α ^ 2 * s ^ 2) t := by fun_prop
    have h := hd.hasDerivAt
    rwa [hquad t] at h
  have hlinHas : ∀ t : ℝ, HasDerivAt (fun s : ℝ => 2 * α ^ 2 * s) (2 * α ^ 2) t := by
    intro t
    have hh : HasDerivAt (fun s : ℝ => 2 * α ^ 2 * s) ((2 * α ^ 2) * 1) t :=
      (hasDerivAt_id t).const_mul (2 * α ^ 2)
    rw [mul_one] at hh
    exact hh
  -- Step 11: derivative of `V` (explicitly) and `C¹` of `V`
  let DVe : ℝ → ℝ := fun t => (DF t * (α ^ 2 * t ^ 2) - F t * (2 * α ^ 2 * t)) / (α ^ 2 * t ^ 2) ^ 2
  have hDV : ∀ t ∈ I, deriv V t = DVe t := by
    intro t ht
    have hEq : V =ᶠ[𝓝 t] (fun s : ℝ => F s / (α ^ 2 * s ^ 2)) := by
      filter_upwards [hIopen.mem_nhds ht] with s hs
      exact hVF s hs
    rw [hEq.deriv_eq]
    change deriv (F / fun s : ℝ => α ^ 2 * s ^ 2) t = DVe t
    have hFd : DifferentiableAt ℝ F t :=
      (hFc1.differentiableOn (by norm_num)).differentiableAt (hIopen.mem_nhds ht)
    have hne : α ^ 2 * t ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hαne) (pow_ne_zero 2 (ne_of_gt ht.1))
    rw [deriv_div hFd (hquadHas t).differentiableAt hne, hFderiv t ht, hquad t]
  -- Step 12: `DF` and its derivative
  let D2F : ℝ → ℝ := fun t => α * (5 + α) * (deriv V t * t + V t) + L * V t
  have hVd : ∀ t ∈ I, HasDerivAt V (deriv V t) t :=
    fun t ht =>
      ((hVc1.differentiableOn (by norm_num)).differentiableAt (hIopen.mem_nhds ht)).hasDerivAt
  have hDFderiv : ∀ t ∈ I, deriv DF t = D2F t := by
    intro t ht
    have hHA : HasDerivAt H (-(V t)) t := by
      have hd : DifferentiableAt ℝ H t :=
        (hHc1.differentiableOn (by norm_num)).differentiableAt (hIopen.mem_nhds ht)
      have h := hd.hasDerivAt
      rwa [hHderiv t ht] at h
    have hprod : HasDerivAt (fun s : ℝ => V s * s) (deriv V t * t + V t * 1) t :=
      (hVd t ht).mul (hasDerivAt_id t)
    have hG' : HasDerivAt (fun s : ℝ => α * (5 + α) * (V s * s))
        (α * (5 + α) * (deriv V t * t + V t * 1)) t :=
      hprod.const_mul (α * (5 + α))
    have hH' : HasDerivAt (fun s : ℝ => L * H s) (L * (-(V t))) t := hHA.const_mul L
    have hmain : HasDerivAt DF
        (0 + α * (5 + α) * (deriv V t * t + V t * 1) - L * (-(V t))) t :=
      ((hasDerivAt_const t (-c₂)).add hG').sub hH'
    rw [hmain.deriv, zero_add]
    simp only [D2F]
    ring
  have hIddF : ∀ t ∈ I, deriv (deriv F) t = D2F t := by
    intro t ht
    have hFE : deriv F =ᶠ[𝓝 t] DF := by
      filter_upwards [hIopen.mem_nhds ht] with s hs
      exact hFderiv s hs
    rw [hFE.deriv_eq, hDFderiv t ht]
  -- Step 13: `C¹` of `DF` and of `DVe`
  have hDFc1 : ContDiffOn ℝ 1 DF I := by
    simp only [DF]
    fun_prop
  have hDVeC1 : ContDiffOn ℝ 1 DVe I := by
    have hN : ContDiffOn ℝ 1
        (fun t : ℝ => DF t * (α ^ 2 * t ^ 2) - F t * (2 * α ^ 2 * t)) I := by
      fun_prop
    have hD : ContDiffOn ℝ 1 (fun t : ℝ => (α ^ 2 * t ^ 2) ^ 2) I := by fun_prop
    simp only [DVe]
    exact hN.div hD fun t ht =>
      pow_ne_zero 2 (mul_ne_zero (pow_ne_zero 2 hαne) (pow_ne_zero 2 (ne_of_gt ht.1)))
  -- Step 14: `V` is `C²` on `I`
  have hVc2 : ContDiffOn ℝ 2 V I := by
    rw [show (2 : ℕ∞ω) = 1 + 1 from by norm_num,
      contDiffOn_succ_iff_deriv_of_isOpen hIopen]
    refine ⟨hVc1.differentiableOn (by norm_num), by simp, ?_⟩
    exact hDVeC1.congr fun t ht => hDV t ht
  -- Step 15: the second expression for `deriv (deriv F) t`
  let Psi : ℝ → ℝ := fun s => α ^ 2 * s ^ 2 * V s
  let Psi' : ℝ → ℝ := fun s => 2 * α ^ 2 * s * V s + α ^ 2 * s ^ 2 * deriv V s
  have hPsiHas : ∀ s ∈ I, HasDerivAt Psi ((2 * α ^ 2 * s) * V s + (α ^ 2 * s ^ 2) * deriv V s) s := by
    intro s hs
    have hVs : DifferentiableAt ℝ V s :=
      (hVc1.differentiableOn (by norm_num)).differentiableAt (hIopen.mem_nhds hs)
    exact (hquadHas s).mul hVs.hasDerivAt
  have hPsideriv : ∀ s ∈ I, deriv Psi s = Psi' s := by
    intro s hs
    exact (hPsiHas s hs).deriv
  have hIIddF : ∀ t ∈ I,
      deriv (deriv F) t = 2 * α ^ 2 * V t + 4 * α ^ 2 * t * deriv V t
        + α ^ 2 * t ^ 2 * deriv (deriv V) t := by
    intro t ht
    have hFE : deriv F =ᶠ[𝓝 t] deriv Psi := by
      filter_upwards [hIopen.mem_nhds ht] with s hs
      have hEq : F =ᶠ[𝓝 s] Psi := by
        filter_upwards [hIopen.mem_nhds hs] with u hu
        simp only [Psi]
        exact hE1 u hu
      exact hEq.deriv_eq
    rw [hFE.deriv_eq]
    have hPsiEq : deriv Psi =ᶠ[𝓝 t] Psi' := by
      filter_upwards [hIopen.mem_nhds ht] with s hs
      exact hPsideriv s hs
    rw [hPsiEq.deriv_eq]
    have hdVc1 : ContDiffOn ℝ 1 (deriv V) I := hVc2.deriv_of_isOpen hIopen (by norm_num)
    have hVd' : HasDerivAt (deriv V) (deriv (deriv V) t) t :=
      ((hdVc1.differentiableOn (by norm_num)).differentiableAt (hIopen.mem_nhds ht)).hasDerivAt
    have h1 : HasDerivAt (fun s : ℝ => 2 * α ^ 2 * s * V s)
        (2 * α ^ 2 * V t + 2 * α ^ 2 * t * deriv V t) t :=
      (hlinHas t).mul (hVd t ht)
    have h2 : HasDerivAt (fun s : ℝ => α ^ 2 * s ^ 2 * deriv V s)
        (2 * α ^ 2 * t * deriv V t + α ^ 2 * t ^ 2 * deriv (deriv V) t) t :=
      (hquadHas t).mul hVd'
    have hmain : HasDerivAt Psi'
        (2 * α ^ 2 * V t + 2 * α ^ 2 * t * deriv V t
          + (2 * α ^ 2 * t * deriv V t + α ^ 2 * t ^ 2 * deriv (deriv V) t)) t :=
      h1.add h2
    rw [hmain.deriv]
    ring
  refine ⟨V, hVc2, ?_, hVeq⟩
  intro t ht
  have h1 : deriv (deriv F) t = α * (5 + α) * (deriv V t * t + V t) + L * V t :=
    hIddF t ht
  have h2 := hIIddF t ht
  have key : α ^ 2 * t ^ 2 * deriv (deriv V) t
      = α * (5 + α) * (deriv V t * t + V t) + L * V t
        - 2 * α ^ 2 * V t - 4 * α ^ 2 * t * deriv V t := by
    rw [← h1, h2]; ring
  calc α ^ 2 * t ^ 2 * deriv (deriv V) t + α * (3 * α - 5) * t * deriv V t
        + (α ^ 2 - 5 * α - L) * V t
      = (α * (5 + α) * (deriv V t * t + V t) + L * V t
          - 2 * α ^ 2 * V t - 4 * α ^ 2 * t * deriv V t)
        + α * (3 * α - 5) * t * deriv V t + (α ^ 2 - 5 * α - L) * V t := by rw [key]
      _ = 0 := by ring

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.FubiniWeightZ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS.StrongEps.EComparison

open MeasureTheory

/-- **Fubini/weight identity for the weighted primitive of `W`.**

For `0 < a < b`, `W` locally integrable on `(0,∞)` and a test function `ρ` compactly supported
inside `(a,b)`,
```
∫_a^b ρ''(t) * ∫_t^b (z - t) W z dz dt = ∫_a^b W z * ρ z dz .
```
The double integral runs over the triangle `a ≤ t ≤ z ≤ b`, so Fubini rewrites it as an integral
in `z` whose inner `t`-integral is `∫_a^z ρ''(t)(z-t)dt = ρ z` (second-order Taylor formula,
using that `ρ` vanishes near `a`).

Mechanism: replace `∫_t^b (z-t)W z dz` by the integral over the fixed box `Icc a b` of the
truncated function `(z-t)W z·1_{t ≤ z}` (`intervalIntegral_eq_setIntegral_indicator`), pull out
the constant `ρ'' t`, apply Fubini on the box
(`MeasureTheory.integral_integral_swap`, whose integrability side condition is
`integrable_fubiniWeightZ_integrand`), and evaluate the inner integral in `t` at fixed `z`
(`intervalIntegral_secondDeriv_mul_sub`), together with the identification of the interval
integrals `a..b` with the box integrals. -/
theorem FubiniWeightZ {a b : ℝ} {W ρ : ℝ → ℝ}
    (hW : MeasureTheory.LocallyIntegrableOn W (Set.Ioi 0)) (ha : 0 < a) (hab : a < b)
    (hρ : ∀ n : ℕ, ContDiff ℝ n ρ) (hρc : HasCompactSupport ρ)
    (hsupp : tsupport ρ ⊆ Set.Ioo a b) :
    (∫ t in a..b, deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z))
      = ∫ z in a..b, W z * ρ z := by
  have hab' : a ≤ b := hab.le
  -- `ρ` vanishes on a neighbourhood of `a`
  have hρa_ev : ρ =ᶠ[nhds a] 0 := by
    rw [← notMem_tsupport_iff_eventuallyEq]
    refine fun hmem => absurd (hsupp hmem) ?_
    rw [Set.mem_Ioo]
    exact fun h => absurd h.1 (lt_irrefl a)
  -- the joint integrand on the box is product-integrable
  have hfun : (Function.uncurry (fun t z : ℝ =>
        deriv (deriv ρ) t * (if t ≤ z then (z - t) * W z else 0)))
      = fun p : ℝ × ℝ => deriv (deriv ρ) p.1 *
        (if p.1 ≤ p.2 then (p.2 - p.1) * W p.2 else 0) := by
    funext p
    rfl
  have hInt : MeasureTheory.Integrable
      (Function.uncurry (fun t z : ℝ =>
        deriv (deriv ρ) t * (if t ≤ z then (z - t) * W z else 0)))
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc a b))) := by
    rw [hfun]
    exact integrable_fubiniWeightZ_integrand hW ha hab hρ
  -- the reduction to the box
  have hL : (∫ t in a..b, deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z))
      = ∫ t in Set.Icc a b, deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z) :=
    (intervalIntegral.integral_of_le hab').trans (integral_Icc_eq_integral_Ioc).symm
  -- rewrite the `z`-integral as an integral over the box
  have key1 : (∫ t in Set.Icc a b, deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z))
      = ∫ t in Set.Icc a b, ∫ z in Set.Icc a b,
          deriv (deriv ρ) t * (if t ≤ z then (z - t) * W z else 0) := by
    refine setIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
    have h1 : (∫ z in Set.Icc a b, deriv (deriv ρ) t * (if t ≤ z then (z - t) * W z else 0))
        = deriv (deriv ρ) t * ∫ z in Set.Icc a b, (if t ≤ z then (z - t) * W z else 0) :=
      integral_const_mul (deriv (deriv ρ) t) _
    rw [h1, ← intervalIntegral_eq_setIntegral_indicator ht.1 ht.2 (fun z => (z - t) * W z)]
  -- Fubini
  have key2 : (∫ t in Set.Icc a b, ∫ z in Set.Icc a b,
        deriv (deriv ρ) t * (if t ≤ z then (z - t) * W z else 0))
      = ∫ z in Set.Icc a b, ∫ t in Set.Icc a b,
        deriv (deriv ρ) t * (if t ≤ z then (z - t) * W z else 0) :=
    integral_integral_swap (μ := volume.restrict (Set.Icc a b))
      (ν := volume.restrict (Set.Icc a b))
      (f := fun t z : ℝ => deriv (deriv ρ) t * (if t ≤ z then (z - t) * W z else 0)) hInt
  -- the inner `t`-integral at fixed `z`
  have key3 : (∫ z in Set.Icc a b, ∫ t in Set.Icc a b,
        deriv (deriv ρ) t * (if t ≤ z then (z - t) * W z else 0))
      = ∫ z in Set.Icc a b, W z * ρ z := by
    refine setIntegral_congr_fun measurableSet_Icc (fun z hz => ?_)
    have e0 : (∫ t in Set.Icc a b, deriv (deriv ρ) t * (if t ≤ z then (z - t) * W z else 0))
        = ∫ t in Set.Icc a b, W z * (if t ≤ z then deriv (deriv ρ) t * (z - t) else 0) :=
      setIntegral_congr_fun measurableSet_Icc (fun t _ => by
        by_cases h : t ≤ z
        · rw [ite_eq_left h, ite_eq_left h]; ring
        · rw [ite_eq_right h, ite_eq_right h, mul_zero, mul_zero])
    have e1 : (∫ t in Set.Icc a b, W z * (if t ≤ z then deriv (deriv ρ) t * (z - t) else 0))
        = W z * ∫ t in Set.Icc a b,
            (if t ≤ z then deriv (deriv ρ) t * (z - t) else 0) :=
      integral_const_mul (W z) _
    have e2 : (∫ t in Set.Icc a b, (if t ≤ z then deriv (deriv ρ) t * (z - t) else 0))
        = ρ z := by
      have h3a : (∫ t in Set.Icc a b, (if t ≤ z then deriv (deriv ρ) t * (z - t) else 0))
          = ∫ t in Set.Icc a z, (if t ≤ z then deriv (deriv ρ) t * (z - t) else 0) :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
          (Set.Icc_subset_Icc_right hz.2) (fun t ht => by
            have hle : ¬ (t ≤ z) := fun h => ht.2 ⟨ht.1.1, h⟩
            rw [ite_eq_right hle])
      have h3b : (∫ t in Set.Icc a z, (if t ≤ z then deriv (deriv ρ) t * (z - t) else 0))
          = ∫ t in Set.Icc a z, deriv (deriv ρ) t * (z - t) :=
        setIntegral_congr_fun measurableSet_Icc (fun t ht => by rw [ite_eq_left ht.2])
      have h3c : (∫ t in Set.Icc a z, deriv (deriv ρ) t * (z - t))
          = ∫ t in a..z, deriv (deriv ρ) t * (z - t) := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hz.1]
      rw [h3a, h3b, h3c, intervalIntegral_secondDeriv_mul_sub hz.1 (by simpa using hρ 3) hρa_ev]
    rw [e0, e1, e2]
  have hR : (∫ z in Set.Icc a b, W z * ρ z) = ∫ z in a..b, W z * ρ z :=
    (integral_Icc_eq_integral_Ioc).trans (intervalIntegral.integral_of_le hab').symm
  exact hL.trans (key1.trans (key2.trans (key3.trans hR)))

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.sin_two_rpow_integral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open MeasureTheory

/-- A set integral of a nonnegative function bounded by a constant `C` on the set `s` is at most
`C` times the (real) measure of `s`.  No measurability or integrability of `f` is needed. -/
private lemma setIntegral_le_const_mul_measureReal {s : Set ℝ} {f : ℝ → ℝ} {C : ℝ}
    (hs : MeasurableSet s) (hfin : volume s < ⊤) (hf : ∀ x ∈ s, 0 ≤ f x)
    (hC : ∀ x ∈ s, f x ≤ C) : ∫ x in s, f x ≤ C * volume.real s := by
  have h1 : ‖∫ x in s, f x‖ ≤ C * volume.real s :=
    norm_setIntegral_le_of_norm_le_const_ae' hfin
      (Filter.Eventually.of_forall fun x hx => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf x hx)]
        exact hC x hx)
  have h2 : 0 ≤ ∫ x in s, f x :=
    setIntegral_nonneg_ae hs (Filter.Eventually.of_forall fun x hx => hf x hx)
  rwa [Real.norm_eq_abs, abs_of_nonneg h2] at h1

/-- `(2δ)^e * δ = 2^e * δ^(e+1)`. -/
private lemma two_mul_rpow_mul_self {δ e : ℝ} (hδ : 0 < δ) :
    (2 * δ) ^ e * δ = 2 ^ e * δ ^ (e + 1) := by
  rw [Real.mul_rpow (by norm_num) (le_of_lt hδ), mul_assoc]
  have h : δ ^ (e + 1) = δ ^ e * δ := by simpa using Real.rpow_add hδ e 1
  rw [← h]

/-- The exponent `2 + η` is nonnegative. -/
private lemma two_add_eta_nonneg : (0 : ℝ) ≤ 2 + Work.Spaces.eta := by
  linarith [Work.Spaces.eta_nonneg]

/-- `sin (2x) ≥ 0` for `x ∈ (0, π/4]`. -/
private lemma sin_two_nonneg_of_mem {x : ℝ} (hx0 : 0 < x) (hx4 : x ≤ Real.pi / 4) :
    0 ≤ Real.sin (2 * x) := by
  refine Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) ?_
  linarith [Real.pi_pos]

theorem sin_two_rpow_integral_le (δ : ℝ) (hδ : 0 < δ) (hδ4 : δ ≤ Real.pi / 4) :
    (∫ θ in Set.Ioo (0 : ℝ) δ, (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)
        ≤ (2 : ℝ) ^ (2 + Work.Spaces.eta) * δ ^ (3 + Work.Spaces.eta)) ∧
      (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)
        ≤ (2 : ℝ) ^ (2 + Work.Spaces.eta) * δ ^ (3 + Work.Spaces.eta)) ∧
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta) ≤ Real.pi / 2) := by
  have heta := two_add_eta_nonneg
  refine ⟨?_, ?_, ?_⟩
  · -- left end: `sin (2θ) ≤ 2θ ≤ 2δ` on `(0, δ)`
    have hfin : volume (Set.Ioo (0 : ℝ) δ) < ⊤ := by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    have hnn : ∀ x ∈ Set.Ioo (0 : ℝ) δ,
        0 ≤ (Real.sin (2 * x)) ^ (2 + Work.Spaces.eta) := by
      intro x hx
      exact Real.rpow_nonneg (sin_two_nonneg_of_mem hx.1 (le_trans (le_of_lt hx.2) hδ4)) _
    have hbd : ∀ x ∈ Set.Ioo (0 : ℝ) δ,
        (Real.sin (2 * x)) ^ (2 + Work.Spaces.eta) ≤ (2 * δ) ^ (2 + Work.Spaces.eta) := by
      intro x hx
      have h2x0 : 0 ≤ 2 * x := by linarith [hx.1]
      have hsinle : Real.sin (2 * x) ≤ 2 * δ :=
        le_trans (Real.sin_le h2x0) (by linarith [hx.2])
      exact Real.rpow_le_rpow (Real.sin_nonneg_of_nonneg_of_le_pi h2x0 (by
        linarith [hx.2, hδ4, Real.pi_pos])) hsinle heta
    have hmain := setIntegral_le_const_mul_measureReal measurableSet_Ioo hfin hnn hbd
    rw [Real.volume_real_Ioo_of_le (le_of_lt hδ), sub_zero] at hmain
    calc ∫ x in Set.Ioo (0 : ℝ) δ, (Real.sin (2 * x)) ^ (2 + Work.Spaces.eta)
        ≤ (2 * δ) ^ (2 + Work.Spaces.eta) * δ := hmain
      _ = 2 ^ (2 + Work.Spaces.eta) * δ ^ (2 + Work.Spaces.eta + 1) :=
          two_mul_rpow_mul_self hδ
      _ = 2 ^ (2 + Work.Spaces.eta) * δ ^ (3 + Work.Spaces.eta) := by
          rw [show (2 : ℝ) + Work.Spaces.eta + 1 = 3 + Work.Spaces.eta by ring]
  · -- right end: substitute `u = π/2 - θ`, then `sin (2θ) = sin (2u) ≤ 2u ≤ 2δ`
    have hfin : volume (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) < ⊤ := by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    have hnn : ∀ x ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
        0 ≤ (Real.sin (2 * x)) ^ (2 + Work.Spaces.eta) := by
      intro x hx
      refine Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
        (by linarith [hx.1, hδ4, Real.pi_pos]) ?_) _
      linarith [hx.2]
    have hbd : ∀ x ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
        (Real.sin (2 * x)) ^ (2 + Work.Spaces.eta) ≤ (2 * δ) ^ (2 + Work.Spaces.eta) := by
      intro x hx
      set u := Real.pi / 2 - x with hu
      have hu0 : 0 < u := by rw [hu]; linarith [hx.2]
      have hud : u < δ := by rw [hu]; linarith [hx.1]
      have hsin0 : 0 ≤ Real.sin (2 * u) :=
        sin_two_nonneg_of_mem hu0 (le_trans (le_of_lt hud) hδ4)
      have hsinle : Real.sin (2 * u) ≤ 2 * δ :=
        le_trans (Real.sin_le (by linarith)) (by linarith)
      have h2x : 2 * x = Real.pi - 2 * u := by rw [hu]; ring
      rw [h2x, Real.sin_pi_sub]
      exact Real.rpow_le_rpow hsin0 hsinle heta
    have hmain := setIntegral_le_const_mul_measureReal measurableSet_Ioo hfin hnn hbd
    rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]), show
      Real.pi / 2 - (Real.pi / 2 - δ) = δ by ring] at hmain
    calc ∫ x in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
          (Real.sin (2 * x)) ^ (2 + Work.Spaces.eta)
        ≤ (2 * δ) ^ (2 + Work.Spaces.eta) * δ := hmain
      _ = 2 ^ (2 + Work.Spaces.eta) * δ ^ (2 + Work.Spaces.eta + 1) :=
          two_mul_rpow_mul_self hδ
      _ = 2 ^ (2 + Work.Spaces.eta) * δ ^ (3 + Work.Spaces.eta) := by
          rw [show (2 : ℝ) + Work.Spaces.eta + 1 = 3 + Work.Spaces.eta by ring]
  · -- the whole interval: `sin (2θ) ≤ 1`
    have hIθ : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) := rfl
    have hfin : volume Work.Spaces.Iθ < ⊤ := by
      rw [hIθ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    have hnn : ∀ x ∈ Work.Spaces.Iθ, 0 ≤ (Real.sin (2 * x)) ^ (2 + Work.Spaces.eta) := by
      intro x hx
      rw [hIθ] at hx
      exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
        (by linarith [hx.2])) _
    have hbd : ∀ x ∈ Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (2 + Work.Spaces.eta) ≤ 1 := by
      intro x hx
      rw [hIθ] at hx
      exact Real.rpow_le_one (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
        (by linarith [hx.2])) (Real.sin_le_one _) heta
    have hmain := setIntegral_le_const_mul_measureReal measurableSet_Icc hfin hnn hbd
    rw [Real.volume_real_Icc_of_le (by linarith [Real.pi_pos]), sub_zero, one_mul] at hmain
    exact hmain

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.abs_le_sqrt_interval_integral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

open MeasureTheory

/-- **One-dimensional Gagliardo–Nirenberg / Agmon inequality.** If `g` is differentiable on
`[c,d]` with derivative `g'` continuous there, then for every `z ∈ [c,d]`,
`|g z| ≤ ‖g‖₂/√(d-c) + √(d-c)·‖g'‖₂`, where `‖·‖₂` denotes the `L²` norm on `[c,d]`.

The proof integrates the pointwise bound `|g z| ≤ |g y| + ∫_c^d |g'|` (valid for every
`y ∈ [c,d]`, obtained from the fundamental theorem of calculus together with
`|∫_y^z g'| ≤ ∫_c^d |g'|`) over `y ∈ [c,d]` and divides by `d - c`; the two `L²` norms are
then estimated by Cauchy–Schwarz (`sq_integral_interval_le`, the square form of
`(∫ f)² ≤ (b-a) ∫ f²`). -/
theorem abs_le_sqrt_interval_integral {c d : ℝ} (hcd : c < d) {g g' : ℝ → ℝ}
    (hder : ∀ x ∈ Set.Icc c d, HasDerivAt g (g' x) x)
    (hg'cont : ContinuousOn g' (Set.Icc c d)) :
    ∀ z ∈ Set.Icc c d,
      |g z| ≤ Real.sqrt (∫ x in c..d, (g x) ^ 2) / Real.sqrt (d - c)
        + Real.sqrt (d - c) * Real.sqrt (∫ x in c..d, (g' x) ^ 2) := by
  intro z hz
  have hcdle : c ≤ d := hcd.le
  have hdpos : 0 < d - c := sub_pos.mpr hcd
  have hdne : d - c ≠ 0 := ne_of_gt hdpos
  set T : ℝ := Real.sqrt (d - c) with hTdef
  set S : ℝ := Real.sqrt (∫ x in c..d, (g x) ^ 2) with hSdef
  set U : ℝ := Real.sqrt (∫ x in c..d, (g' x) ^ 2) with hUdef
  have hgcont : ContinuousOn g (Set.Icc c d) :=
    fun x hx => (hder x hx).continuousAt.continuousWithinAt
  have habsg_cont : ContinuousOn (fun x => |g x|) (Set.Icc c d) := hgcont.abs
  have habsg'_cont : ContinuousOn (fun x => |g' x|) (Set.Icc c d) := hg'cont.abs
  set A : ℝ := ∫ x in c..d, |g x| with hA
  set B : ℝ := ∫ x in c..d, |g' x| with hB
  have hAnn : 0 ≤ ∫ x in c..d, |g x| :=
    intervalIntegral.integral_nonneg hcdle (fun x _ => abs_nonneg _)
  have hBnn : 0 ≤ ∫ x in c..d, |g' x| :=
    intervalIntegral.integral_nonneg hcdle (fun x _ => abs_nonneg _)
  have hAnnA : 0 ≤ A := by rw [hA]; exact hAnn
  have hBnnB : 0 ≤ B := by rw [hB]; exact hBnn
  have hInt_absg : IntervalIntegrable (fun y => |g y|) volume c d :=
    ContinuousOn.intervalIntegrable_of_Icc hcdle habsg_cont
  have hInt_absg' : IntervalIntegrable (fun y => |g' y|) volume c d :=
    ContinuousOn.intervalIntegrable_of_Icc hcdle habsg'_cont
  -- the pointwise bound: `|g z| ≤ |g y| + B` for every `y ∈ [c,d]`
  have key : ∀ y ∈ Set.Icc c d, |g z| ≤ |g y| + B := by
    intro y hy
    have hsubIcc : Set.uIcc y z ⊆ Set.Icc c d := by
      intro t ht
      rw [Set.mem_uIcc] at ht
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨le_trans hy.1 h1, le_trans h2 hz.2⟩
      · exact ⟨le_trans hz.1 h1, le_trans h2 hy.2⟩
    have hsubIoc : Set.uIoc y z ⊆ Set.uIoc c d := by
      intro t ht
      rw [Set.mem_uIoc] at ht
      rw [Set.uIoc_of_le hcdle]
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨lt_of_le_of_lt hy.1 h1, le_trans h2 hz.2⟩
      · exact ⟨lt_of_le_of_lt hz.1 h1, le_trans h2 hy.2⟩
    have hFTC : ∫ t in y..z, g' t = g z - g y :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hder t (hsubIcc ht))
        (ContinuousOn.intervalIntegrable (hg'cont.mono hsubIcc))
    have h1 : |∫ t in Set.uIoc y z, g' t| ≤ ∫ t in Set.uIoc y z, |g' t| := by
      simpa only [Real.norm_eq_abs] using
        MeasureTheory.norm_integral_le_integral_norm
          (μ := volume.restrict (Set.uIoc y z)) (f := g')
    have hfi : IntegrableOn (fun t => |g' t|) (Set.uIoc c d) volume := by
      rw [Set.uIoc_of_le hcdle]; exact hInt_absg'.1
    have h2 : ∫ t in Set.uIoc y z, |g' t| ≤ ∫ t in Set.uIoc c d, |g' t| :=
      MeasureTheory.setIntegral_mono_set hfi
        (Filter.Eventually.of_forall (fun t => abs_nonneg (g' t)))
        (Filter.Eventually.of_forall hsubIoc)
    have huIocB : ∫ t in Set.uIoc c d, |g' t| = B := by
      rw [hB, Set.uIoc_of_le hcdle, ← intervalIntegral.integral_of_le hcdle]
    have hEq : |∫ t in y..z, g' t| = |∫ t in Set.uIoc y z, g' t| :=
      intervalIntegral.abs_integral_eq_abs_integral_uIoc g'
    have hstep : |∫ t in y..z, g' t| ≤ B := by
      rw [hEq]
      exact h1.trans (h2.trans (le_of_eq huIocB))
    have hsum : g y + (g z - g y) = g z := by ring
    calc |g z| = |g y + (g z - g y)| := by rw [hsum]
      _ ≤ |g y| + |g z - g y| := abs_add_le _ _
      _ = |g y| + |∫ t in y..z, g' t| := by rw [← hFTC]
      _ ≤ |g y| + B := by linarith [hstep]
  -- integrate the pointwise bound over `y ∈ [c,d]`
  have hInt_const : IntervalIntegrable (fun _ : ℝ => |g z|) volume c d := intervalIntegrable_const
  have hInt_sum : IntervalIntegrable (fun y => |g y| + B) volume c d :=
    hInt_absg.add intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hcdle hInt_const hInt_sum key
  have e1 : ∫ y in c..d, |g z| = (d - c) * |g z| := by
    rw [intervalIntegral.integral_const]; simp [smul_eq_mul]
  have e2 : ∫ y in c..d, (|g y| + B) = A + (d - c) * B := by
    rw [intervalIntegral.integral_add hInt_absg intervalIntegrable_const, ← hA,
      intervalIntegral.integral_const]
    simp [smul_eq_mul]
  rw [e1, e2] at hmono
  have hmain : |g z| ≤ A / (d - c) + B := by
    have h1 : (d - c) * |g z| / (d - c) ≤ (A + (d - c) * B) / (d - c) :=
      div_le_div_of_nonneg_right hmono hdpos.le
    have h2 : (d - c) * |g z| / (d - c) = |g z| := by
      rw [div_eq_iff hdne]; ring
    have h3 : (A + (d - c) * B) / (d - c) = A / (d - c) + B := by
      have hmul : (d - c) * B / (d - c) = B := by rw [div_eq_iff hdne]; ring
      rw [add_div, hmul]
    linarith [h1, h2, h3]
  -- Cauchy–Schwarz for `A` and `B`
  have hAcs : A ≤ T * S := by
    have hi : IntervalIntegrable (fun x : ℝ => |g x| ^ 2) volume c d :=
      ContinuousOn.intervalIntegrable_of_Icc hcdle (habsg_cont.pow 2)
    have hsq : ∫ x in c..d, |g x| ^ 2 = ∫ x in c..d, (g x) ^ 2 :=
      intervalIntegral.integral_congr (fun x _ => sq_abs (g x))
    have hcs : (∫ x in c..d, |g x|) ^ 2 ≤ (d - c) * ∫ x in c..d, (g x) ^ 2 := by
      have h := sq_integral_interval_le (f := fun x => |g x|) hcdle hi
      rwa [hsq] at h
    calc A = Real.sqrt (A ^ 2) := (Real.sqrt_sq hAnnA).symm
      _ = Real.sqrt ((∫ x in c..d, |g x|) ^ 2) := by rw [hA]
      _ ≤ Real.sqrt ((d - c) * ∫ x in c..d, (g x) ^ 2) := Real.sqrt_le_sqrt hcs
      _ = T * S := by rw [hTdef, hSdef, Real.sqrt_mul hdpos.le]
  have hBcs : B ≤ T * U := by
    have hi : IntervalIntegrable (fun x : ℝ => |g' x| ^ 2) volume c d :=
      ContinuousOn.intervalIntegrable_of_Icc hcdle (habsg'_cont.pow 2)
    have hsq : ∫ x in c..d, |g' x| ^ 2 = ∫ x in c..d, (g' x) ^ 2 :=
      intervalIntegral.integral_congr (fun x _ => sq_abs (g' x))
    have hcs : (∫ x in c..d, |g' x|) ^ 2 ≤ (d - c) * ∫ x in c..d, (g' x) ^ 2 := by
      have h := sq_integral_interval_le (f := fun x => |g' x|) hcdle hi
      rwa [hsq] at h
    calc B = Real.sqrt (B ^ 2) := (Real.sqrt_sq hBnnB).symm
      _ = Real.sqrt ((∫ x in c..d, |g' x|) ^ 2) := by rw [hB]
      _ ≤ Real.sqrt ((d - c) * ∫ x in c..d, (g' x) ^ 2) := Real.sqrt_le_sqrt hcs
      _ = T * U := by rw [hTdef, hUdef, Real.sqrt_mul hdpos.le]
  have hT : 0 < T := by rw [hTdef]; exact Real.sqrt_pos.mpr hdpos
  have hT2 : T * T = d - c := by rw [hTdef, ← pow_two, Real.sq_sqrt hdpos.le]
  have hAratio : A / (d - c) ≤ S / T := by
    rw [div_le_div_iff₀ hdpos hT]
    calc A * T ≤ (T * S) * T := mul_le_mul_of_nonneg_right hAcs hT.le
      _ = S * (T * T) := by ring
      _ = S * (d - c) := by rw [hT2]
  linarith [hmain, hAratio, hBcs]

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.HkIntegrand_sub_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits

/-- **Subadditivity of the `ℋ^k`-integrand for a difference**: if every mixed derivative
`D_z^j D_θ^i G` (`j + i ≤ k`) is pointwise the difference of the corresponding derivatives of
`A` and `B`, then

`HkIntegrand α k G z θ ≤ 2 · HkIntegrand α k A z θ + 2 · HkIntegrand α k B z θ`.

This is purely algebraic: `HkIntegrand` is a sum of squares of the finitely many slots
(`D_z^i G · w/sin(2θ)^{η/2}` for `0 ≤ i ≤ k`, and `D_z^j D_θ^i G · W` for `1 ≤ i`, `i + j ≤ k`),
and each slot of `G` is the difference of the corresponding slots, so
`(x - y)² ≤ 2x² + 2y²` applied slotwise and summed gives the claim.  The `D_z`-slots are the
`i = 0` case of the mixed slots, so the single hypothesis `hsub` covers both sums. -/
theorem HkIntegrand_sub_le {α : ℝ} {k : ℕ} {G A B : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hsub : ∀ j i : ℕ, j + i ≤ k →
      Work.Spaces.mixed j i G z θ = Work.Spaces.mixed j i A z θ - Work.Spaces.mixed j i B z θ) :
    Work.Spaces.HkIntegrand α k G z θ
      ≤ 2 * Work.Spaces.HkIntegrand α k A z θ + 2 * Work.Spaces.HkIntegrand α k B z θ := by
  -- the `D_z`-slots are the mixed slots with `i = 0`
  have hdz : ∀ i : ℕ, i ≤ k → Work.Spaces.DzIter i G z θ
      = Work.Spaces.DzIter i A z θ - Work.Spaces.DzIter i B z θ := by
    intro i hi
    have h := hsub i 0 (by omega)
    simpa only [Work.Spaces.mixed_zero_right] using h
  -- the elementary square estimate `(x - y)² c² ≤ 2 (xc)² + 2 (yc)²`
  have hsq : ∀ x y c : ℝ, ((x - y) * c) ^ 2 ≤ 2 * (x * c) ^ 2 + 2 * (y * c) ^ 2 := by
    intro x y c
    nlinarith [sq_nonneg ((x + y) * c)]
  -- the `D_z`-sum
  have hS1 : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i G z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i A z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
        + 2 * (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i B z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    have hterm : ∀ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i G z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ 2 * (Work.Spaces.DzIter i A z θ
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
            + 2 * (Work.Spaces.DzIter i B z θ
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      intro i hi
      have hik : i ≤ k := by
        have := Finset.mem_range.mp hi; omega
      rw [hdz i hik]
      exact hsq _ _ _
    calc (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i G z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ i ∈ Finset.range (k + 1),
            (2 * (Work.Spaces.DzIter i A z θ
                * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
              + 2 * (Work.Spaces.DzIter i B z θ
                * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) :=
          Finset.sum_le_sum hterm
      _ = 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i A z θ
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
          + 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i B z θ
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- the mixed sum
  have hS2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
        + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i B z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    have hinner : ∀ i ∈ Finset.range (k + 1),
        (∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ 2 * (∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          + 2 * (∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i B z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      intro i hi
      have hterm : ∀ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ 2 * (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
            + 2 * (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i B z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
        intro j hj
        split_ifs with hc
        · rw [hsub j i (by omega)]
          exact hsq _ _ _
        · norm_num
      calc (∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ ∑ j ∈ Finset.range (k + 1),
              (2 * (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
                + 2 * (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i B z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) :=
            Finset.sum_le_sum hterm
        _ = 2 * (∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
            + 2 * (∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i B z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ ∑ i ∈ Finset.range (k + 1),
            (2 * (∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
              + 2 * (∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i B z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) :=
          Finset.sum_le_sum hinner
      _ = 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i A z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i B z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [Work.Spaces.HkIntegrand]
  linarith [hS1, hS2]

end Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.integral_sq_add_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open MeasureTheory Filter

/-- `L²`-Minkowski (equivalently Cauchy–Schwarz / convexity of the square root) for nonnegative
functions: if `a`, `b ≥ 0` are a.e.-strongly measurable with square-integrable squares, then
`∫ (a + b)² ≤ (√(∫ a²) + √(∫ b²))²`.

Proof: expand the square, estimate the cross term `∫ a b` by Cauchy–Schwarz/Hölder with
conjugate exponents `p = q = 2`, and observe that the resulting right-hand side is the expansion
of `(√(∫ a²) + √(∫ b²))²`. -/
theorem integral_sq_add_le {μ : MeasureTheory.Measure ℝ} {a b : ℝ → ℝ}
    (han : ∀ x, 0 ≤ a x) (hbn : ∀ x, 0 ≤ b x)
    (ha : MeasureTheory.AEStronglyMeasurable a μ)
    (hb : MeasureTheory.AEStronglyMeasurable b μ)
    (h2a : MeasureTheory.Integrable (fun x => a x ^ 2) μ)
    (h2b : MeasureTheory.Integrable (fun x => b x ^ 2) μ) :
    (∫ x, (a x + b x) ^ 2 ∂μ)
      ≤ (Real.sqrt (∫ x, a x ^ 2 ∂μ) + Real.sqrt (∫ x, b x ^ 2 ∂μ)) ^ 2 := by
  have hA0 : 0 ≤ ∫ x, a x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg (a x)
  have hB0 : 0 ≤ ∫ x, b x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg (b x)
  have hmA : MemLp a (ENNReal.ofReal (2 : ℝ)) μ := by
    rw [ENNReal.ofReal_ofNat]; exact (memLp_two_iff_integrable_sq ha).2 h2a
  have hmB : MemLp b (ENNReal.ofReal (2 : ℝ)) μ := by
    rw [ENNReal.ofReal_ofNat]; exact (memLp_two_iff_integrable_sq hb).2 h2b
  -- the product `a * b` is integrable, by `|a b| ≤ (a² + b²)/2`
  have h2ab : Integrable (fun x => a x * b x) μ := by
    refine ((h2a.add h2b).div_const 2).mono' (ha.mul hb) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    show |a x| * |b x| ≤ (a x ^ 2 + b x ^ 2) / 2
    nlinarith [sq_nonneg (|a x| - |b x|), sq_abs (a x), sq_abs (b x)]
  -- Cauchy–Schwarz for the cross term
  have hCS : ∫ x, a x * b x ∂μ
      ≤ Real.sqrt (∫ x, a x ^ 2 ∂μ) * Real.sqrt (∫ x, b x ^ 2 ∂μ) := by
    have hpq : (2 : ℝ).HolderConjugate 2 :=
      Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
        (Filter.Eventually.of_forall han) (Filter.Eventually.of_forall hbn) hmA hmB
    simpa [Real.sqrt_eq_rpow] using h
  -- expansion of the square
  have h2ab2 : Integrable (fun x => 2 * (a x * b x)) μ := by
    simpa only [smul_eq_mul] using h2ab.const_mul (2 : ℝ)
  have e0 : ∫ x, (a x + b x) ^ 2 ∂μ = ∫ x, a x ^ 2 + 2 * (a x * b x) + b x ^ 2 ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have e1 : ∫ x, a x ^ 2 + 2 * (a x * b x) ∂μ
      = (∫ x, a x ^ 2 ∂μ) + (∫ x, 2 * (a x * b x) ∂μ) := integral_add h2a h2ab2
  have e2 : ∫ x, a x ^ 2 + 2 * (a x * b x) + b x ^ 2 ∂μ
      = (∫ x, a x ^ 2 + 2 * (a x * b x) ∂μ) + (∫ x, b x ^ 2 ∂μ) :=
    integral_add (h2a.add h2ab2) h2b
  have e3 : (∫ x, 2 * (a x * b x) ∂μ) = 2 * (∫ x, a x * b x ∂μ) :=
    integral_const_mul 2 (fun x => a x * b x)
  have hexp : ∫ x, (a x + b x) ^ 2 ∂μ
      = (∫ x, a x ^ 2 ∂μ) + 2 * (∫ x, a x * b x ∂μ) + (∫ x, b x ^ 2 ∂μ) := by
    rw [e0, e2, e1, e3]
  have hsq : (Real.sqrt (∫ x, a x ^ 2 ∂μ) + Real.sqrt (∫ x, b x ^ 2 ∂μ)) ^ 2
      = (∫ x, a x ^ 2 ∂μ)
        + 2 * (Real.sqrt (∫ x, a x ^ 2 ∂μ) * Real.sqrt (∫ x, b x ^ 2 ∂μ))
        + (∫ x, b x ^ 2 ∂μ) := by
    rw [add_sq, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
    ring
  rw [hexp, hsq]
  nlinarith [hCS]

end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.AeCompExpNeg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

theorem AeCompExpNeg {P : ℝ → Prop} {z ε : ℝ} (hz : 0 < z) (hε : 0 < ε)
    (h : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), P u) :
    ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), P (z * Real.exp (-(ε * p))) := by
  classical
  -- The bad set on `(0,∞)`, which is null by the hypothesis.
  set N : Set ℝ := {w | ¬ P w} ∩ Set.Ioi 0 with hN
  have hNvol : volume N = 0 := by
    have h' := (MeasureTheory.ae_iff).mp h
    rwa [Measure.restrict_apply' measurableSet_Ioi] at h'
  -- Membership in `N` is exactly failure of `P` at `z * exp (-(ε p))`.
  have hTN : ∀ p : ℝ, (z * Real.exp (-(ε * p)) ∈ N ↔ ¬ P (z * Real.exp (-(ε * p)))) := by
    intro p
    rw [hN]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioi]
    exact ⟨fun h => h.1, fun h => ⟨h, mul_pos hz (Real.exp_pos _)⟩⟩
  -- Its preimage `T` under the map `p ↦ z * exp (-(ε p))`.
  set T : Set ℝ := {p | z * Real.exp (-(ε * p)) ∈ N} with hT
  have hTvol : volume T = 0 := by
    -- `T` is the image of the null set `N` under the differentiable map
    -- `w ↦ (log z - log w) / ε`, the inverse of `p ↦ z exp (-(ε p))`.
    have himg : T = (fun w => (Real.log z - Real.log w) / ε) '' N := by
      ext p
      rw [hT]
      constructor
      · intro hp
        refine ⟨z * Real.exp (-(ε * p)), hp, ?_⟩
        have hlog : Real.log (z * Real.exp (-(ε * p))) = Real.log z - ε * p := by
          rw [Real.log_mul hz.ne' (Real.exp_ne_zero _), Real.log_exp]
          ring
        show (Real.log z - Real.log (z * Real.exp (-(ε * p)))) / ε = p
        rw [hlog]
        field_simp
        ring
      · rintro ⟨w, hw, rfl⟩
        change z * Real.exp (-(ε * ((Real.log z - Real.log w) / ε))) ∈ N
        have hwpos : 0 < w := by rw [hN] at hw; exact hw.2
        have harg : -(ε * ((Real.log z - Real.log w) / ε)) = Real.log w - Real.log z := by
          field_simp
          ring
        have hexp : Real.exp (Real.log w - Real.log z) = w / z := by
          rw [Real.exp_sub, Real.exp_log hwpos, Real.exp_log hz]
        rw [harg, hexp, mul_div_cancel₀ w hz.ne']
        exact hw
    rw [himg]
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ hNvol
    intro w hw
    rw [hN] at hw
    exact (((Real.differentiableAt_log (hw.2 : 0 < w).ne').const_sub (Real.log z)).div_const
      ε).differentiableWithinAt
  -- Conclude.
  rw [MeasureTheory.ae_iff]
  have hset : {p : ℝ | ¬ P (z * Real.exp (-(ε * p)))} = T := by
    ext p
    simp only [hT, Set.mem_ofPred_eq]
    exact (hTN p).symm
  rw [hset, hTvol]

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.JepsMarginalDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-- The weighted angular energy of the `z`-slice of `f`,

  `Ibd α f z = ∫_{σ ∈ Iθ} sin(2σ)^{2-γ} * (∂_θ f z σ)² dσ`,

with `γ = Work.Spaces.gam α`.  This is exactly the factor multiplying `100/(γ-1) * sin(2θ)^{γ-1}`
on the right-hand side of the boundary bound `hbd`. -/
noncomputable def Ibd (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ σ in Work.Spaces.Iθ,
    (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ) ^ 2

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.LintegralExpCompIcc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open MeasureTheory in
/-- Change of variables for the substitution `p ↦ z * exp (-(ε * p))` on `[-1, 1]`, in the
form needed by the strong-`ε` construction: the map is an antitone diffeomorphism of
`[-1, 1]` onto `[z * exp (-ε), z * exp ε]` whose Jacobian factor
`ε * z * exp (-(ε * p))` is bounded below by `ε * z * exp (-ε)` on the interval. -/
theorem LintegralExpCompIcc {z ε : ℝ} (hz : 0 < z) (hε : 0 < ε) (F : ℝ → ENNReal) :
    ∫⁻ p in Set.Icc (-1 : ℝ) 1, F (z * Real.exp (-(ε * p)))
      ≤ ENNReal.ofReal (1 / (ε * z * Real.exp (-ε)))
        * ∫⁻ u in Set.Icc (z * Real.exp (-ε)) (z * Real.exp ε), F u := by
  have hcpos : 0 < ε * z * Real.exp (-ε) := by positivity
  have hderiv : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun p : ℝ => z * Real.exp (-(ε * p)))
        (-(ε * (z * Real.exp (-(ε * x))))) (Set.Icc (-1 : ℝ) 1) x := by
    intro x hx
    have h1 : HasDerivAt (fun p : ℝ => -(ε * p)) (-ε) x := by
      have h : HasDerivAt (fun p : ℝ => (-ε) * p) (-ε) x := hasDerivAt_const_mul (x := x) (-ε)
      simpa only [neg_mul] using h
    have h2 : HasDerivAt (fun p : ℝ => Real.exp (-(ε * p)))
        (Real.exp (-(ε * x)) * (-ε)) x := h1.exp
    have h3 : HasDerivAt (fun p : ℝ => z * Real.exp (-(ε * p)))
        (z * (Real.exp (-(ε * x)) * (-ε))) x := h2.const_mul z
    have heq : z * (Real.exp (-(ε * x)) * (-ε)) = -(ε * (z * Real.exp (-(ε * x)))) := by ring
    rw [heq] at h3
    exact h3.hasDerivWithinAt
  have hcont : ContinuousOn (fun p : ℝ => z * Real.exp (-(ε * p))) (Set.Icc (-1 : ℝ) 1) := by
    fun_prop
  have hanti : AntitoneOn (fun p : ℝ => z * Real.exp (-(ε * p))) (Set.Icc (-1 : ℝ) 1) := by
    intro a ha b hb hab
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hz.le
  have himg : (fun p : ℝ => z * Real.exp (-(ε * p))) '' Set.Icc (-1 : ℝ) 1
      = Set.Icc (z * Real.exp (-ε)) (z * Real.exp ε) := by
    have h := hcont.image_Icc_of_antitoneOn (show (-1 : ℝ) ≤ 1 by norm_num) hanti
    simpa using h
  have hcov' : ∫⁻ u in Set.Icc (z * Real.exp (-ε)) (z * Real.exp ε), F u
      = ∫⁻ p in Set.Icc (-1 : ℝ) 1,
          ENNReal.ofReal (ε * (z * Real.exp (-(ε * p)))) * F (z * Real.exp (-(ε * p))) := by
    have h := MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn
      (s := Set.Icc (-1 : ℝ) 1) (f := fun p : ℝ => z * Real.exp (-(ε * p)))
      (f' := fun x : ℝ => -(ε * (z * Real.exp (-(ε * x))))) measurableSet_Icc hderiv hanti F
    rw [himg] at h
    simpa only [neg_neg] using h
  have hpt : ∀ p ∈ Set.Icc (-1 : ℝ) 1,
      ENNReal.ofReal (ε * z * Real.exp (-ε)) * F (z * Real.exp (-(ε * p)))
        ≤ ENNReal.ofReal (ε * (z * Real.exp (-(ε * p)))) * F (z * Real.exp (-(ε * p))) := by
    intro p hp
    have hp1 : p ≤ 1 := hp.2
    have hexp : Real.exp (-ε) ≤ Real.exp (-(ε * p)) := Real.exp_le_exp.mpr (by nlinarith)
    have hzexp : z * Real.exp (-ε) ≤ z * Real.exp (-(ε * p)) :=
      mul_le_mul_of_nonneg_left hexp hz.le
    have hle : ε * z * Real.exp (-ε) ≤ ε * (z * Real.exp (-(ε * p))) := by
      calc ε * z * Real.exp (-ε) = ε * (z * Real.exp (-ε)) := by ring
        _ ≤ ε * (z * Real.exp (-(ε * p))) := mul_le_mul_of_nonneg_left hzexp hε.le
    exact mul_le_mul_left (ENNReal.ofReal_mono hle) (F (z * Real.exp (-(ε * p))))
  have hstep1 : ∫⁻ p in Set.Icc (-1 : ℝ) 1,
        ENNReal.ofReal (ε * z * Real.exp (-ε)) * F (z * Real.exp (-(ε * p)))
      ≤ ∫⁻ u in Set.Icc (z * Real.exp (-ε)) (z * Real.exp ε), F u := by
    rw [hcov']
    exact MeasureTheory.setLIntegral_mono' measurableSet_Icc hpt
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hstep1
  have hcne : ENNReal.ofReal (ε * z * Real.exp (-ε)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hcpos
  have hctop : ENNReal.ofReal (ε * z * Real.exp (-ε)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hconsteq : (ENNReal.ofReal (ε * z * Real.exp (-ε)))⁻¹
      = ENNReal.ofReal (1 / (ε * z * Real.exp (-ε))) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos hcpos]
  calc ∫⁻ p in Set.Icc (-1 : ℝ) 1, F (z * Real.exp (-(ε * p)))
      = (ENNReal.ofReal (ε * z * Real.exp (-ε)))⁻¹ *
          (ENNReal.ofReal (ε * z * Real.exp (-ε)) *
            ∫⁻ p in Set.Icc (-1 : ℝ) 1, F (z * Real.exp (-(ε * p)))) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hcne hctop, one_mul]
    _ ≤ (ENNReal.ofReal (ε * z * Real.exp (-ε)))⁻¹ *
          ∫⁻ u in Set.Icc (z * Real.exp (-ε)) (z * Real.exp ε), F u :=
        mul_le_mul_right hstep1 _
    _ = ENNReal.ofReal (1 / (ε * z * Real.exp (-ε))) *
          ∫⁻ u in Set.Icc (z * Real.exp (-ε)) (z * Real.exp ε), F u := by
        rw [hconsteq]

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.SinPowIntegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

theorem SinPowIntegral {γ : ℝ} (h1 : 1 < γ) (h2 : γ ≤ 2) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ Real.pi / 4) :
    ∫ x in a..b, (Real.sin (2 * x)) ^ (γ - 2) ≤ (100 / (γ - 1)) * (Real.sin (2 * b)) ^ (γ - 1) := by
  have hγ1 : 0 < γ - 1 := by linarith
  have hr : -1 < γ - 2 := by linarith
  have hb0 : 0 ≤ b := le_trans ha hab
  have hbpi : 2 * b ≤ Real.pi / 2 := by linarith [hb, Real.pi_pos]
  -- Integrability of the integrand on `0..b` (comparison with `x ↦ x ^ (γ-2)`).
  have hfint : IntervalIntegrable (fun x : ℝ => (Real.sin (2 * x)) ^ (γ - 2)) volume 0 b := by
    have hgint : IntervalIntegrable (fun x : ℝ => max 1 (2 ^ (γ - 2)) * x ^ (γ - 2)) volume 0 b :=
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b) hr).const_mul _
    refine hgint.mono_fun' ?_ ?_
    · exact ((Real.measurable_sin.comp
        (measurable_const.mul measurable_id)).pow_const _).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hx
      have hx' : x ∈ Set.Ioc (0 : ℝ) b := by rwa [Set.uIoc_of_le hb0] at hx
      have hxpos : 0 < x := hx'.1
      have h2xpos : 0 < 2 * x := by linarith
      have h2xle : 2 * x ≤ Real.pi / 2 := by linarith [hx'.2, hb, Real.pi_pos]
      have hsinpos : 0 < Real.sin (2 * x) :=
        Real.sin_pos_of_pos_of_lt_pi h2xpos (by linarith [Real.pi_pos, h2xle])
      have hxr : 0 ≤ x ^ (γ - 2) := Real.rpow_nonneg (le_of_lt hxpos) _
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt hsinpos) _)]
      rcases le_or_gt 0 (γ - 2) with hr0 | hr0
      · -- nonnegative exponent: `sin(2x) ≤ 2x`
        have hsle : Real.sin (2 * x) ≤ 2 * x := Real.sin_le (le_of_lt h2xpos)
        have hstep : (Real.sin (2 * x)) ^ (γ - 2) ≤ (2 * x) ^ (γ - 2) :=
          Real.rpow_le_rpow (le_of_lt hsinpos) hsle hr0
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hxpos)] at hstep
        exact hstep.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hxr)
      · -- negative exponent: Jordan's inequality `sin(2x) ≥ (4/π)x`
        have hjord : (4 / Real.pi) * x ≤ Real.sin (2 * x) := by
          have h := Real.mul_le_sin (x := 2 * x) (le_of_lt h2xpos) h2xle
          have he : 2 / Real.pi * (2 * x) = (4 / Real.pi) * x := by ring
          rwa [he] at h
        have hbase : 0 < (4 / Real.pi) * x := by positivity
        have hstep : (Real.sin (2 * x)) ^ (γ - 2) ≤ ((4 / Real.pi) * x) ^ (γ - 2) :=
          Real.rpow_le_rpow_of_nonpos hbase hjord (le_of_lt hr0)
        have hsplit : ((4 / Real.pi) * x) ^ (γ - 2)
            = (4 / Real.pi) ^ (γ - 2) * x ^ (γ - 2) :=
          Real.mul_rpow (by positivity) (le_of_lt hxpos)
        have hcoef : (4 / Real.pi) ^ (γ - 2) ≤ 1 := by
          have hp4 : (0 : ℝ) < Real.pi / 4 := by positivity
          have hle1 : Real.pi / 4 ≤ 1 := by linarith [Real.pi_lt_four]
          have h' : (4 / Real.pi) = (Real.pi / 4)⁻¹ := by rw [inv_div]
          rw [h', Real.inv_rpow (le_of_lt hp4), ← Real.rpow_neg (le_of_lt hp4)]
          exact Real.rpow_le_one (le_of_lt hp4) hle1 (neg_nonneg.mpr (le_of_lt hr0))
        calc (Real.sin (2 * x)) ^ (γ - 2) ≤ ((4 / Real.pi) * x) ^ (γ - 2) := hstep
          _ = (4 / Real.pi) ^ (γ - 2) * x ^ (γ - 2) := hsplit
          _ ≤ 1 * x ^ (γ - 2) := mul_le_mul_of_nonneg_right hcoef hxr
          _ ≤ max 1 (2 ^ (γ - 2)) * x ^ (γ - 2) := by
              simpa using mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) (2 ^ (γ - 2))) hxr
  -- The integrand is nonnegative on `(0, b]`.
  have hnn : ((fun _ : ℝ => (0 : ℝ)) ≤ᵐ[volume.restrict (Set.Ioc 0 b)]
      (fun x : ℝ => (Real.sin (2 * x)) ^ (γ - 2))) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => ?_)
    have h2xle : 2 * x ≤ Real.pi := by linarith [hx.2, hb, Real.pi_pos]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1]) h2xle) _
  have hstep1 : ∫ x in a..b, (Real.sin (2 * x)) ^ (γ - 2)
      ≤ ∫ x in (0 : ℝ)..b, (Real.sin (2 * x)) ^ (γ - 2) :=
    intervalIntegral.integral_mono_interval (c := 0) (d := b) ha hab le_rfl hnn hfint
  have hstep2 : ∫ x in (0 : ℝ)..b, (Real.sin (2 * x)) ^ (γ - 2) ≤ b ^ (γ - 1) / (γ - 1) := by
    have h := Work.FTS.GalBasis.cc.sin_pow_int_general (γ := γ) (θ' := b) h1 hb0 hb
    have hmax : max (1 : ℝ) (2 ^ (γ - 2)) = 1 := by
      rw [max_eq_left]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    rwa [hmax, one_mul] at h
  have hsin_nn : 0 ≤ Real.sin (2 * b) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos, hb])
  -- `b ≤ sin(2b)` on `[0, π/4]` (Jordan).
  have hbsin : b ≤ Real.sin (2 * b) := by
    have hj := Real.mul_le_sin (x := 2 * b) (by linarith) hbpi
    have he : 2 / Real.pi * (2 * b) = (4 / Real.pi) * b := by ring
    have h4 : (4 / Real.pi) * b ≤ Real.sin (2 * b) := by rwa [he] at hj
    have h1' : (1 : ℝ) ≤ 4 / Real.pi := by
      rw [one_le_div (by positivity : (0 : ℝ) < Real.pi)]
      exact Real.pi_le_four
    have hble : b ≤ (4 / Real.pi) * b := by
      have := mul_le_mul_of_nonneg_right h1' hb0
      simpa using this
    linarith
  have hbpow : b ^ (γ - 1) ≤ (Real.sin (2 * b)) ^ (γ - 1) :=
    Real.rpow_le_rpow hb0 hbsin (by linarith)
  have hfinal : b ^ (γ - 1) / (γ - 1)
      ≤ (100 / (γ - 1)) * (Real.sin (2 * b)) ^ (γ - 1) := by
    have h100 : b ^ (γ - 1) ≤ 100 * (Real.sin (2 * b)) ^ (γ - 1) := by
      have hs0 : 0 ≤ (Real.sin (2 * b)) ^ (γ - 1) := Real.rpow_nonneg hsin_nn _
      linarith
    have hinv : 0 ≤ (γ - 1)⁻¹ := inv_nonneg.mpr (le_of_lt hγ1)
    calc b ^ (γ - 1) / (γ - 1) = b ^ (γ - 1) * (γ - 1)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (100 * (Real.sin (2 * b)) ^ (γ - 1)) * (γ - 1)⁻¹ :=
            mul_le_mul_of_nonneg_right h100 hinv
      _ = (100 / (γ - 1)) * (Real.sin (2 * b)) ^ (γ - 1) := by rw [div_eq_mul_inv]; ring
  calc ∫ x in a..b, (Real.sin (2 * x)) ^ (γ - 2)
      ≤ ∫ x in (0 : ℝ)..b, (Real.sin (2 * x)) ^ (γ - 2) := hstep1
    _ ≤ b ^ (γ - 1) / (γ - 1) := hstep2
    _ ≤ (100 / (γ - 1)) * (Real.sin (2 * b)) ^ (γ - 1) := hfinal

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.inv_zw_sq_integrableOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsLocalPStar

/-!
# Integrability of `(1/(z·w(z)))²` on `(0,∞)`

Since `w(z) = (1+z)²/z²`, we have `z·w(z) = (1+z)²/z` for `z > 0`, hence

`(1/(z·w(z)))² = z²/(1+z)⁴ ≤ (1+z)^{-2}`,

and `∫_0^∞ (1+s)^{-2} ds = 1 ≤ 2`.  The two helper lemmas below record the
elementary improper integral of the majorant (integrability and its value `1`)
and the pointwise comparison.
-/

/-- The majorant `(1+s)^{-2}` is integrable on `(0,∞)`. -/
private lemma integrableOn_one_add_rpow_neg_two :
    MeasureTheory.IntegrableOn (fun s : ℝ => (1 + s) ^ (-(2 : ℝ))) (Set.Ioi (0 : ℝ)) := by
  have h := integrableOn_add_rpow_Ioi_of_lt (a := -(2 : ℝ)) (c := 0) (m := 1)
    (by norm_num) (by norm_num)
  simpa [add_comm] using h

/-- `∫_0^∞ (1+s)^{-2} ds = 1`, via the antiderivative `s ↦ -(1+s)^{-1}`. -/
private lemma integral_one_add_rpow_neg_two :
    ∫ s in Set.Ioi (0 : ℝ), (1 + s) ^ (-(2 : ℝ)) = 1 := by
  have hg : MeasureTheory.IntegrableOn (fun s : ℝ => (1 + s) ^ (-(2 : ℝ)))
      (Set.Ioi (0 : ℝ)) := integrableOn_one_add_rpow_neg_two
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun s : ℝ => -((1 + s) ^ (-(1 : ℝ)))) ((1 + x) ^ (-(2 : ℝ))) x := by
    intro x hx
    have hpos : (0 : ℝ) < 1 + x := by linarith [Set.mem_Ici.mp hx]
    have hd0 : HasDerivAt (fun s : ℝ => 1 + s) (1 : ℝ) x := by
      simpa using (hasDerivAt_id x).const_add (1 : ℝ)
    have hd1 : HasDerivAt (fun s : ℝ => (1 + s) ^ (-(1 : ℝ)))
        (1 * (-(1 : ℝ)) * (1 + x) ^ (-(1 : ℝ) - 1)) x :=
      hd0.rpow_const (Or.inl (ne_of_gt hpos))
    have hd2 : HasDerivAt (fun s : ℝ => -((1 + s) ^ (-(1 : ℝ))))
        (-(1 * (-(1 : ℝ)) * (1 + x) ^ (-(1 : ℝ) - 1))) x := hd1.neg
    have hexp : -(1 : ℝ) - 1 = -(2 : ℝ) := by norm_num
    refine hd2.congr_deriv ?_
    rw [hexp]
    ring
  have htend : Tendsto (fun s : ℝ => -((1 + s) ^ (-(1 : ℝ)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => (1 + s) ^ (-(1 : ℝ))) atTop (𝓝 0) := by
      simpa only [Function.comp_def, id_eq] using
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).comp
          (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
    simpa using h1.neg
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hg htend
  rw [hmain]
  simp

/-- Pointwise comparison: for `z > 0`, `(1/(z·w(z)))² ≤ (1+z)^{-2}`. -/
private lemma div_mul_w_sq_le (z : ℝ) (hz : 0 < z) :
    (1 / (z * Work.Spaces.w z)) ^ 2 ≤ (1 + z) ^ (-(2 : ℝ)) := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hzw : z * Work.Spaces.w z = (1 + z) ^ 2 / z := by
    rw [Work.Spaces.w]
    field_simp
  rw [hzw, one_div_div, Real.rpow_neg (le_of_lt h1z), Real.rpow_two, div_pow,
    inv_eq_one_div]
  have h4 : ((1 + z) ^ 2) ^ 2 = (1 + z) ^ 4 := by ring
  rw [h4]
  have hsq : z ^ 2 ≤ (1 + z) ^ 2 := by nlinarith
  calc z ^ 2 / (1 + z) ^ 4 ≤ (1 + z) ^ 2 / (1 + z) ^ 4 :=
        div_le_div_of_nonneg_right hsq (by positivity)
    _ = 1 / (1 + z) ^ 2 := by
        field_simp

theorem inv_zw_sq_integrableOn :
    MeasureTheory.IntegrableOn (fun z : ℝ => (1 / (z * Work.Spaces.w z)) ^ 2) (Set.Ioi (0:ℝ)) ∧
      0 ≤ ∫ z in Set.Ioi (0:ℝ), (1 / (z * Work.Spaces.w z)) ^ 2 ∧
      (∫ z in Set.Ioi (0:ℝ), (1 / (z * Work.Spaces.w z)) ^ 2) ≤ 2 := by
  have hmeas : Measurable (fun z : ℝ => (1 / (z * Work.Spaces.w z)) ^ 2) := by
    unfold Work.Spaces.w
    fun_prop
  have hmaj : MeasureTheory.IntegrableOn (fun s : ℝ => (1 + s) ^ (-(2 : ℝ))) (Set.Ioi (0 : ℝ)) :=
    integrableOn_one_add_rpow_neg_two
  have hle : ∀ z ∈ Set.Ioi (0 : ℝ), (1 / (z * Work.Spaces.w z)) ^ 2 ≤ (1 + z) ^ (-(2 : ℝ)) :=
    fun z hz => div_mul_w_sq_le z hz
  have hint : MeasureTheory.IntegrableOn (fun z : ℝ => (1 / (z * Work.Spaces.w z)) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.Integrable.mono' hmaj hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hle z hz
  refine ⟨hint, ?_, ?_⟩
  · exact integral_nonneg (fun z => by positivity)
  · have hmono := setIntegral_mono_on hint hmaj measurableSet_Ioi hle
    have hval := integral_one_add_rpow_neg_two
    linarith

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.D5.ae_ident_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Identification of the a.e. limit of the level-5 slots with the mixed derivative of the limit

`Work.FTS.StrongEps.LocUnif.D5.ae_limit_eq_deriv`: let a sequence `L n` converge uniformly to
`Llim` on a closed box `[a₀,b₀] × [c,d]`, let `W n` be the `z`-derivative of `L n` on the smaller
box `[a,b] × [c,d]` (where `a₀ < a < b < b₀`), and let `w` be an a.e. limit of `W n` whose slices
converge in `L¹([a,b])` for a.e. angle `θ`.  Then `w` agrees a.e. with the (totalised) partial
derivative `∂_z Llim`.
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif.D5

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Two elementary helpers -/

/-- **The `ε`-`δ` form of `HasDerivAt`.** -/
theorem exists_delta_hasDerivAt {f : ℝ → ℝ} {f' x : ℝ} (h : HasDerivAt f f' x) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, 0 < |y - x| → |y - x| < δ →
      |(f y - f x) / (y - x) - f'| < ε := by
  rw [hasDerivAt_iff_tendsto_slope] at h
  rw [Metric.tendsto_nhds] at h
  have h2 : ∀ᶠ y in 𝓝 x, y ≠ x → dist (slope f x y) f' < ε := by
    have h3 := h ε hε
    rwa [eventually_nhdsWithin_iff] at h3
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp h2
  refine ⟨δ, hδpos, fun y hy hyδ => ?_⟩
  have hyball : y ∈ Metric.ball x δ := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hyδ
  have hyne : y ≠ x := by
    intro hyx
    rw [hyx, sub_self, abs_zero] at hy
    exact absurd hy (lt_irrefl 0)
  have h4 := hδ hyball hyne
  rw [slope_def_field, Real.dist_eq] at h4
  simpa [abs_sub_comm] using h4

/-- **A bound valid at all rational points of an open set extends to the whole set**, by density
of `ℚ` and continuity. -/
theorem abs_le_of_forall_rat_of_continuousOn {g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hg : ContinuousOn g s) {c : ℝ} (h : ∀ q : ℚ, (q : ℝ) ∈ s → |g (q : ℝ)| ≤ c) :
    ∀ x ∈ s, |g x| ≤ c := by
  intro x hx
  by_contra hcon
  push Not at hcon
  have hopen : IsOpen (s ∩ (fun y : ℝ => |g y|) ⁻¹' (Set.Ioi c)) :=
    hg.abs.isOpen_inter_preimage hs isOpen_Ioi
  have hmem : x ∈ s ∩ (fun y : ℝ => |g y|) ⁻¹' (Set.Ioi c) := ⟨hx, hcon⟩
  obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp hopen x hmem
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x < x + δ by linarith)
  have hqmem : (q : ℝ) ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm, abs_lt]
    exact ⟨by linarith, by linarith⟩
  have hq' := hδ hqmem
  rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi] at hq'
  exact absurd (h q hq'.1) (not_le.mpr hq'.2)

end Work.FTS.StrongEps.LocUnif.D5
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.D5.slice_interval_tendsto_of_L1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter Set

namespace Work.FTS.StrongEps.LocUnif.D5

set_option maxHeartbeats 1600000

/-- The `L¹`-norm (as a lower integral) of the `θ`-slice of `W k - w` over `[a,b]`. -/
private noncomputable def SliceLInt (a b : ℝ) (W : ℕ → ℝ → ℝ → ℝ) (w : ℝ → ℝ → ℝ)
    (k : ℕ) (θ : ℝ) : ENNReal :=
  ∫⁻ z in Set.Icc a b, ENNReal.ofReal |W k z θ - w z θ|

/-- The uncurried difference of the `k`-th approximant and the limit is a.e. measurable for
the product of the two restricted measures. -/
private lemma aemeasurable_uncurried_sub {a b c d : ℝ} {W : ℕ → ℝ → ℝ → ℝ}
    {w : ℝ → ℝ → ℝ}
    (hWm : ∀ k : ℕ, AEMeasurable (fun p : ℝ × ℝ => W k p.1 p.2)
      (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)))
    (hwm : AEMeasurable (fun p : ℝ × ℝ => w p.1 p.2)
      (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))) (k : ℕ) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal |W k p.1 p.2 - w p.1 p.2|)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d))) := by
  rw [Measure.prod_restrict]
  exact ((((hWm k).sub hwm).abs).ennreal_ofReal)

/-- A.e. in `θ`, the `z`-slices of an a.e. measurable function on the box are a.e. measurable
for the restricted measure in `z`. -/
private lemma slice_measurable_ae {a b c d : ℝ} {W : ℕ → ℝ → ℝ → ℝ} {w : ℝ → ℝ → ℝ}
    (hWm : ∀ k : ℕ, AEMeasurable (fun p : ℝ × ℝ => W k p.1 p.2)
      (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)))
    (hwm : AEMeasurable (fun p : ℝ × ℝ => w p.1 p.2)
      (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))) :
    ∀ᵐ θ ∂(volume.restrict (Set.Icc c d)),
      (∀ k : ℕ, AEMeasurable (fun z : ℝ => W k z θ)
        (volume.restrict (Set.Icc a b))) ∧
      AEMeasurable (fun z : ℝ => w z θ) (volume.restrict (Set.Icc a b)) := by
  have hbox : ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d)))
      = volume.restrict (Set.Icc a b ×ˢ Set.Icc c d) := Measure.prod_restrict _ _
  have key : ∀ (X : ℝ × ℝ → ℝ),
      AEMeasurable X (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) →
      ∀ᵐ θ ∂(volume.restrict (Set.Icc c d)),
        AEMeasurable (fun z : ℝ => X (z, θ)) (volume.restrict (Set.Icc a b)) := by
    intro X hX
    obtain ⟨G, hG, hGeq⟩ := hX
    rw [← hbox] at hGeq
    have hswap := (Measure.measurePreserving_swap
      (μ := volume.restrict (Set.Icc c d))
      (ν := volume.restrict (Set.Icc a b))).quasiMeasurePreserving.ae hGeq
    have h2 := Measure.ae_ae_of_ae_prod hswap
    filter_upwards [h2] with θ hθ
    have hGm : Measurable (fun z : ℝ => G (z, θ)) :=
      hG.comp (measurable_prodMk_right (y := θ))
    refine hGm.aemeasurable.congr ?_
    filter_upwards [hθ] with z hz
    simpa using hz.symm
  refine Eventually.and ?_ ?_
  · rw [ae_all_iff]
    intro k
    exact key (fun p : ℝ × ℝ => W k p.1 p.2) (hWm k)
  · exact key (fun p : ℝ × ℝ => w p.1 p.2) hwm

/-- The norm of an interval integral is bounded by the lower integral of the modulus over the
corresponding `Ioc`-interval. -/
private lemma norm_intervalIntegral_le_toReal {z z₀ : ℝ} {h : ℝ → ℝ} :
    ‖∫ u in z..z₀, h u‖
      ≤ (∫⁻ u in Set.Ioc (min z z₀) (max z z₀), ENNReal.ofReal |h u|).toReal := by
  rcases le_total z z₀ with hle | hle
  · rw [intervalIntegral.integral_of_le hle, min_eq_left hle, max_eq_right hle]
    refine (MeasureTheory.norm_integral_le_lintegral_norm _).trans ?_
    rw [show (∫⁻ u in Set.Ioc z z₀, ENNReal.ofReal ‖h u‖)
        = (∫⁻ u in Set.Ioc z z₀, ENNReal.ofReal |h u|) from
      lintegral_congr fun u => by rw [Real.norm_eq_abs]]
  · rw [intervalIntegral.integral_symm z₀ z, norm_neg, intervalIntegral.integral_of_le hle,
      min_eq_right hle, max_eq_left hle]
    refine (MeasureTheory.norm_integral_le_lintegral_norm _).trans ?_
    rw [show (∫⁻ u in Set.Ioc z₀ z, ENNReal.ofReal ‖h u‖)
        = (∫⁻ u in Set.Ioc z₀ z, ENNReal.ofReal |h u|) from
      lintegral_congr fun u => by rw [Real.norm_eq_abs]]

/-- `L¹`-convergence of a sequence of functions on `[a,b]` to `g` implies the convergence of the
interval integrals against any subinterval. -/
private lemma interval_tendsto_aux {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hmf : ∀ k, AEMeasurable (f k) (volume.restrict (Set.Icc a b)))
    (hmg : AEMeasurable g (volume.restrict (Set.Icc a b)))
    (hP : Tendsto (fun k => ∫⁻ z in Set.Icc a b, ENNReal.ofReal |f k z - g z|)
      atTop (nhds 0)) :
    ∀ z ∈ Set.Icc a b, ∀ z₀ ∈ Set.Icc a b,
      Tendsto (fun k => ∫ u in z..z₀, f k u) atTop (nhds (∫ u in z..z₀, g u)) := by
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp hP 1 zero_lt_one
  have key : ∀ z ∈ Set.Icc a b, ∀ z₀ ∈ Set.Icc a b,
      ∀ᶠ k in atTop,
        ‖(∫ u in z..z₀, f k u) - (∫ u in z..z₀, g u)‖
          ≤ (∫⁻ u in Set.Icc a b, ENNReal.ofReal |f k u - g u|).toReal := by
    intro z hz z₀ hz₀
    filter_upwards [eventually_atTop.mpr ⟨N, hN⟩] with k hk
    have hfin : (∫⁻ u in Set.Icc a b, ENNReal.ofReal |f k u - g u|) < ⊤ :=
      lt_of_le_of_lt hk ENNReal.one_lt_top
    have hsub : Set.Ioc (min z z₀) (max z z₀) ⊆ Set.Icc a b := fun u hu =>
      ⟨le_trans (le_min hz.1 hz₀.1) hu.1.le, le_trans hu.2 (max_le hz.2 hz₀.2)⟩
    have hdiff : IntervalIntegrable (fun u => f k u - g u) volume z z₀ := by
      rw [intervalIntegrable_iff]
      refine ⟨?_, ?_⟩
      · exact (((hmf k).mono_set hsub).aestronglyMeasurable).sub
          ((hmg.mono_set hsub).aestronglyMeasurable)
      · change ∫⁻ u, ‖f k u - g u‖ₑ ∂(volume.restrict (Set.uIoc z z₀)) < ⊤
        have h1 : ∫⁻ u, ‖f k u - g u‖ₑ ∂(volume.restrict (Set.uIoc z z₀))
            = ∫⁻ u in Set.Ioc (min z z₀) (max z z₀), ENNReal.ofReal |f k u - g u| := by
          rw [show Set.uIoc z z₀ = Set.Ioc (min z z₀) (max z z₀) from rfl]
          exact lintegral_congr fun u => Real.enorm_eq_ofReal_abs _
        rw [h1]
        exact lt_of_le_of_lt (lintegral_mono_set hsub) hfin
    by_cases h1 : IntervalIntegrable (f k) volume z z₀
    · by_cases h2 : IntervalIntegrable g volume z z₀
      · rw [← intervalIntegral.integral_sub h1 h2]
        refine (norm_intervalIntegral_le_toReal (z := z) (z₀ := z₀)).trans ?_
        refine ENNReal.toReal_mono hfin.ne (lintegral_mono_set ?_)
        intro u hu
        exact ⟨le_trans (le_min hz.1 hz₀.1) hu.1.le, le_trans hu.2 (max_le hz.2 hz₀.2)⟩
      · exact absurd ((h1.sub hdiff).congr (fun u _ => by ring)) h2
    · by_cases h2 : IntervalIntegrable g volume z z₀
      · exact absurd ((hdiff.add h2).congr (fun u _ => by ring)) h1
      · rw [intervalIntegral.integral_undef h1, intervalIntegral.integral_undef h2,
          sub_zero, norm_zero]
        exact ENNReal.toReal_nonneg
  intro z hz z₀ hz₀
  have hbound := key z hz z₀ hz₀
  have hlim : Tendsto (fun k => (∫⁻ u in Set.Icc a b, ENNReal.ofReal |f k u - g u|).toReal)
      atTop (nhds 0) := by
    have h := (ENNReal.tendsto_toReal (show (0 : ENNReal) ≠ ⊤ by simp)).comp hP
    have h0 : (0 : ENNReal).toReal = 0 := by simp
    rw [h0] at h
    exact h
  have hsqueeze : Tendsto
      (fun k => ‖(∫ u in z..z₀, f k u) - (∫ u in z..z₀, g u)‖) atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) hbound hlim
  have h0 : Tendsto (fun k => (∫ u in z..z₀, f k u) - (∫ u in z..z₀, g u))
      atTop (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hsqueeze
  have h1 := h0.add_const (∫ u in z..z₀, g u)
  simpa only [sub_add_cancel, zero_add] using h1

theorem slice_interval_tendsto_of_L1 {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {W : ℕ → ℝ → ℝ → ℝ} {w : ℝ → ℝ → ℝ}
    (hWm : ∀ k : ℕ, AEMeasurable
      (fun p : ℝ × ℝ => W k p.1 p.2)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)))
    (hwm : AEMeasurable
      (fun p : ℝ × ℝ => w p.1 p.2)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)))
    (hL1 : Filter.Tendsto (fun k => ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal |W k p.1 p.2 - w p.1 p.2|) Filter.atTop (nhds 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc c d)),
        ∀ z ∈ Set.Icc a b, ∀ z₀ ∈ Set.Icc a b,
          Filter.Tendsto (fun k => ∫ u in z..z₀, W (ψ k) u θ) Filter.atTop
            (nhds (∫ u in z..z₀, w u θ)) := by
  -- Measurability of the `θ`-slices of the lower integrals
  have hLmeas : ∀ k, AEMeasurable (SliceLInt a b W w k)
      (volume.restrict (Set.Icc c d)) := by
    intro k
    exact (aemeasurable_uncurried_sub hWm hwm k).lintegral_prod_left
  -- Tonelli: the iterated lower integral is the lower integral over the box
  have key : ∀ k, ∫⁻ θ, SliceLInt a b W w k θ ∂(volume.restrict (Set.Icc c d))
      = ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
          ENNReal.ofReal |W k p.1 p.2 - w p.1 p.2| := by
    intro k
    have hf : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal |W k p.1 p.2 - w p.1 p.2|)
        ((volume : Measure (ℝ × ℝ)).restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
      have h' := aemeasurable_uncurried_sub hWm hwm k
      rw [Measure.prod_restrict] at h'
      exact h'
    have h := MeasureTheory.setLIntegral_prod_symm
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (s := Set.Icc a b) (t := Set.Icc c d)
      (f := fun p : ℝ × ℝ => ENNReal.ofReal |W k p.1 p.2 - w p.1 p.2|) hf
    exact h.symm
  have hLtot : Filter.Tendsto
      (fun k => ∫⁻ θ, SliceLInt a b W w k θ ∂(volume.restrict (Set.Icc c d)))
      Filter.atTop (nhds 0) :=
    hL1.congr' (Eventually.of_forall fun k => (key k).symm)
  -- extract the a.e.-convergent subsequence
  obtain ⟨ψ, hψ, hψae⟩ := exists_strictMono_tendsto_ae_of_lintegral_tendsto hLmeas hLtot
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [hψae, slice_measurable_ae hWm hwm] with θ hθ hslice
  refine interval_tendsto_aux hab (fun k => hslice.1 (ψ k)) hslice.2 ?_
  exact hθ

end Work.FTS.StrongEps.LocUnif.D5
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.V5Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false

/-- The measurable majorant of the slots of order `≤ 5` along a sequence `fn`:
`liminf_n ofReal (HkIntegrand α 5 (fn n) p)`. -/
def V5 (α : ℝ) (fn : ℕ → ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  Filter.liminf (fun n : ℕ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (fn n) p.1 p.2))
    Filter.atTop

end Work.FTS.StrongEps.LocUnif
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.V6Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false

/-- The weight with which the level-6 slot `mixed j i` (`i + j = 6`) occurs in
`Work.Spaces.HkIntegrand α 6`: the pure `D_z^6` slot (`i = 0`) carries the radial weight
`w z / sin(2θ)^{η/2}`, while every slot with `i ≥ 1` carries the full weight
`Wt α z θ = w z · sin(2θ)^{-γ/2}`. -/
def rho6 (α : ℝ) (i : ℕ) (z θ : ℝ) : ℝ :=
  if i = 0 then Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
  else Work.Spaces.Wt α z θ

/-- The `z`-directed part of the level-6 slots of `HkIntegrand α 6 g`: the slot
`D_z^6 g = mixed 6 0 g` together with the five mixed slots `mixed (6 - i) i g` with
`1 ≤ i ≤ 5`.  (The remaining level-6 slot, `mixed 0 6 g = D_θ^6 g`, is `level6T`.) -/
def level6Z (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 6, (Work.Spaces.mixed (6 - i) i g z θ * rho6 α i z θ) ^ 2

/-- The `θ`-directed level-6 slot `D_θ^6 g = mixed 0 6 g` of `HkIntegrand α 6 g`. -/
def level6T (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.mixed 0 6 g z θ * rho6 α 6 z θ) ^ 2

/-- **The measurable majorant of the six `z`-directed level-6 slots of the limit.**

For each of the six level-5 slots `W_i = mixed (5 - i) i f` (`0 ≤ i ≤ 5`), whose child
`D_z W_i = mixed (6 - i) i f` is a level-6 slot with weight `rho6 α i`, the majorant takes
the `liminf` (as `j → ∞`) of the squared `j`-th *backward* difference quotient of `W_i`
with step `1/(j+1)`, weighted by `z · rho6 α i` — so that the limiting quantity is
`z · ∂_z W_i · rho6 α i = D_z W_i · rho6 α i`. -/
def V6z (α : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  Filter.liminf (fun j : ℕ => ∑ i ∈ Finset.range 6, ENNReal.ofReal
    (((Work.Spaces.mixed (5 - i) i f p.1 p.2
        - Work.Spaces.mixed (5 - i) i f (p.1 - 1 / ((j : ℝ) + 1)) p.2) * ((j : ℝ) + 1)
      * (p.1 * rho6 α i p.1 p.2)) ^ 2)) Filter.atTop

/-- **The measurable majorant of the `θ`-directed level-6 slot of the limit** (`mixed 0 6 f
= D_θ (mixed 0 5 f)`), built from the backward difference quotients in `θ` of the level-5
slot `mixed 0 5 f`, weighted by `sin(2θ) · Wt α`. -/
def V6t (α : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  Filter.liminf (fun j : ℕ => ENNReal.ofReal
    (((Work.Spaces.mixed 0 5 f p.1 p.2
        - Work.Spaces.mixed 0 5 f p.1 (p.2 - 1 / ((j : ℝ) + 1))) * ((j : ℝ) + 1)
      * (Real.sin (2 * p.2) * rho6 α 6 p.1 p.2)) ^ 2)) Filter.atTop

end Work.FTS.StrongEps.LocUnif
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.ae_shift_preimage_sub_snd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

/-- **Almost-everywhere statements transfer under a vertical translation.**  The
second-coordinate analogue of `ae_shift_preimage_sub`: if `Q` holds almost everywhere on `A`,
and the shift `q ↦ (q.1, q.2 - h)` maps `B` into `A`, then `Q` holds almost everywhere on `B`
after the shift.  Only the translation invariance of Lebesgue measure on `ℝ × ℝ` is used. -/
theorem ae_shift_preimage_sub_snd {A B : Set (ℝ × ℝ)} {h : ℝ} {Q : ℝ × ℝ → Prop}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hQ : ∀ᵐ q ∂(MeasureTheory.volume.restrict A), Q q)
    (hmap : ∀ q ∈ B, (q.1, q.2 - h) ∈ A) :
    ∀ᵐ q ∂(MeasureTheory.volume.restrict B), Q (q.1, q.2 - h) := by
  rw [MeasureTheory.ae_iff]
  have hA0 : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      ({q : ℝ × ℝ | ¬ Q q} ∩ A) = 0 := by
    rw [← MeasureTheory.Measure.restrict_apply' hAm]
    exact MeasureTheory.ae_iff.mp hQ
  rw [MeasureTheory.Measure.restrict_apply' hBm]
  have hpre : ((fun q : ℝ × ℝ => (q.1, q.2 - h)) ⁻¹' ({q : ℝ × ℝ | ¬ Q q} ∩ A))
      = ((fun q : ℝ × ℝ => (0, -h) + q) ⁻¹' ({q : ℝ × ℝ | ¬ Q q} ∩ A)) := by
    rw [show (fun q : ℝ × ℝ => (q.1, q.2 - h)) = (fun q : ℝ × ℝ => (0, -h) + q) from by
      funext q
      ext <;> simp [sub_eq_add_neg, add_comm]]
  refine MeasureTheory.measure_mono_null
    (t := ((fun q : ℝ × ℝ => (q.1, q.2 - h)) ⁻¹' ({q : ℝ × ℝ | ¬ Q q} ∩ A))) ?_ ?_
  · rintro q ⟨hq1, hq2⟩
    exact ⟨hq1, hmap q hq2⟩
  · rw [hpre, MeasureTheory.measure_preimage_add]
    exact hA0

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.aemeasurable_comp_sub_of_aemeasurable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

/-- **A.e.-measurability transfers under a horizontal translation.**  If `f` is
a.e.-measurable on `A` and the shift `q ↦ (q.1 - h, q.2)` maps `B` into `A`, then the
composite `q ↦ f (q.1 - h, q.2)` is a.e.-measurable on `B`.

Proof: `AEMeasurable f (volume.restrict A)` unfolds to a *measurable* `g` with
`f =ᵐ[volume.restrict A] g`; the a.e. equality is transported across the shift by
`ae_shift_preimage_sub`, and `g ∘ shift` is measurable. -/
theorem aemeasurable_comp_sub_of_aemeasurable {A B : Set (ℝ × ℝ)} {h : ℝ} {β : Type*}
    [MeasurableSpace β] {f : ℝ × ℝ → β}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hmap : ∀ q ∈ B, (q.1 - h, q.2) ∈ A)
    (hf : AEMeasurable f (MeasureTheory.volume.restrict A)) :
    AEMeasurable (fun q : ℝ × ℝ => f (q.1 - h, q.2)) (MeasureTheory.volume.restrict B) := by
  obtain ⟨g, hgm, hfg⟩ := hf
  refine ⟨fun q : ℝ × ℝ => g (q.1 - h, q.2), hgm.comp ?_, ?_⟩
  · exact (measurable_fst.sub_const h).prodMk measurable_snd
  · have h := ae_shift_preimage_sub (Q := fun q => f q = g q) hAm hBm hfg hmap
    filter_upwards [h] with q hq
    exact hq

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.aemeasurable_ofReal_HkIntegrand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

theorem aemeasurable_ofReal_HkIntegrand {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hslots : ∀ (j i : ℕ), ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i g p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d))
    (ha : 0 < a) (hc : 0 < c) (hd : d < π / 2) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k g p.1 p.2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
  -- The three positivity hypotheses are not needed for measurability itself: they are what
  -- places the rectangle inside the open quadrant, i.e. they are what makes the slots
  -- `ContinuousOn` on it in the applications of this lemma.
  have hquad : ∀ (z θ : ℝ), z ∈ Set.Icc a b → θ ∈ Set.Icc c d →
      0 < z ∧ 0 < θ ∧ θ < π / 2 := by
    intro z θ hz hθ
    exact ⟨by linarith [hz.1, ha], by linarith [hθ.1, hc], by linarith [hθ.2, hd]⟩
  have hs : MeasurableSet (Set.Icc a b ×ˢ Set.Icc c d) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hslot : ∀ j i : ℕ, AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.mixed j i g p.1 p.2)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    fun j i => (hslots j i).aemeasurable hs
  -- the radial weight `w z / sin(2θ)^{η/2}` is Borel measurable
  have hw : AEMeasurable (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    ((((measurable_const.add measurable_fst).pow_const 2).div
        (measurable_fst.pow_const 2)).div
      ((Real.measurable_sin.comp (measurable_const.mul measurable_snd)).pow
        measurable_const)).aemeasurable
  -- the full weight `W = w · sin(2θ)^{-γ/2}` is Borel measurable
  have hWt : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := by
    have h : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
        = fun p : ℝ × ℝ =>
            Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
      funext p; rfl
    rw [h]
    exact ((((measurable_const.add measurable_fst).pow_const 2).div
        (measurable_fst.pow_const 2)).mul
      ((Real.measurable_sin.comp (measurable_const.mul measurable_snd)).pow
        measurable_const)).aemeasurable
  -- the `D_z`-block: `DzIter i g = mixed i 0 g`
  have hsum1 : AEMeasurable
      (∑ i ∈ Finset.range (k + 1), fun p : ℝ × ℝ =>
        (Work.Spaces.DzIter i g p.1 p.2
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    Finset.aemeasurable_sum _ (fun i _ => ((hslot i 0).mul hw).pow_const 2)
  -- the mixed block
  have hsum2 : AEMeasurable
      (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), fun p : ℝ × ℝ =>
        (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i g p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2 else 0))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    Finset.aemeasurable_sum _ (fun i _ => Finset.aemeasurable_sum _ (fun j _ => by
      by_cases hc' : 1 ≤ i ∧ i + j ≤ k
      · simp only [ite_eq_left hc']
        exact ((hslot j i).mul hWt).pow_const 2
      · simp only [ite_eq_right hc']
        exact aemeasurable_zero))
  have hpoly : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k g p.1 p.2)
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) :=
    (hsum1.add hsum2).congr (by
      filter_upwards with p
      simp only [Pi.add_apply, Finset.sum_apply]
      rfl)
  exact ENNReal.measurable_ofReal.comp_aemeasurable hpoly

end Work.FTS.StrongEps.LocUnif
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.diffQuot_pointwise_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

open MeasureTheory Set

theorem diffQuot_pointwise_le {a b a' b' c d h C : ℝ}
    (haa' : a < a') (hb'b : b' < b) (hh : 0 < h) (hah : h < a' - a) (hC : 1 ≤ C)
    {w : ℝ → ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hw : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < w z θ)
    (hCw : ∀ z ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      |z - y| ≤ h → (w z θ) ^ 2 ≤ C * (w y θ) ^ 2)
    (hu_sm : ∀ θ ∈ Set.Icc c d, ContDiffOn ℝ 1 (fun z => u z θ) (Set.Ioo a b))
    {z θ : ℝ} (hz : z ∈ Set.Icc a' b') (hθ : θ ∈ Set.Icc c d) :
    ENNReal.ofReal (((u z θ - u (z - h) θ) / h) ^ 2 * (w z θ) ^ 2)
      ≤ ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹ *
        ∫⁻ s in Set.Ioc 0 h,
          ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s)) ^ 2 * (w (z - s) θ) ^ 2) := by
  -- `z ∈ (a,b)` and `z - h ∈ (a,b)`; the whole closed interval `[z-h,z]` lies in `Ioo a b`.
  have hz_ab : z ∈ Set.Icc a b := ⟨by linarith [hz.1, haa'], by linarith [hz.2, hb'b]⟩
  have hsub : Set.Icc (z - h) z ⊆ Set.Ioo a b := by
    intro x hx
    exact ⟨by linarith [hx.1, hah, hz.1], by linarith [hx.2, hb'b, hz.2]⟩
  -- Continuity of the `z`-derivative of the slice on the integration range.
  have hderiv_cont : ContinuousOn (deriv (fun z' => u z' θ)) (Set.Ioo a b) :=
    (hu_sm θ hθ).continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have hcont : ContinuousOn (fun s => deriv (fun z' => u z' θ) (z - s)) (Set.Ioc 0 h) := by
    have hmap : Set.MapsTo (fun s : ℝ => z - s) (Set.Ioc 0 h) (Set.Ioo a b) :=
      fun s hs => hsub ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hcs : ContinuousOn (fun s : ℝ => z - s) (Set.Ioc 0 h) :=
      (continuous_const.sub continuous_id).continuousOn
    exact hderiv_cont.comp hcs hmap
  have hmeas : AEStronglyMeasurable (fun s => deriv (fun z' => u z' θ) (z - s))
      (MeasureTheory.volume.restrict (Set.Ioc 0 h)) :=
    hcont.aestronglyMeasurable measurableSet_Ioc
  -- Fundamental theorem of calculus for the slice, backward difference.
  have hFTC : ∫ s in (0:ℝ)..h, deriv (fun z' => u z' θ) (z - s) = u z θ - u (z - h) θ :=
    integral_deriv_slice_sub hh.le hsub (hu_sm θ hθ)
  -- Cauchy–Schwarz against the constant weight `1`.
  have hCS : ENNReal.ofReal ((u z θ - u (z - h) θ)^2)
      ≤ ENNReal.ofReal h *
        ∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2) := by
    have h := ofReal_interval_integral_sq_le hh.le
      (fun s => deriv (fun z' => u z' θ) (z - s)) hmeas
    rw [hFTC, sub_zero] at h
    exact h
  -- Pointwise comparison of the weights, valid on `Ioc 0 h`.
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
      _ = ENNReal.ofReal C * ENNReal.ofReal ((w (z - s) θ)^2 * (deriv (fun z' => u z' θ) (z - s))^2) :=
          ENNReal.ofReal_mul hCpos
      _ = ENNReal.ofReal C * ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2) := by
          rw [mul_comm ((w (z - s) θ)^2) ((deriv (fun z' => u z' θ) (z - s))^2)]
  -- Integrate the pointwise comparison against the Cauchy–Schwarz weight.
  have hB : ENNReal.ofReal ((w z θ)^2) *
        (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2))
      ≤ ENNReal.ofReal C *
        (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2)) := by
    have hmono := setLIntegral_mono' (μ := volume) measurableSet_Ioc hpb
    rw [lintegral_const_mul' (ENNReal.ofReal ((w z θ)^2))
          (fun s => ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2)) ENNReal.ofReal_ne_top,
        lintegral_const_mul' (ENNReal.ofReal C)
          (fun s => ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2))
          ENNReal.ofReal_ne_top] at hmono
    exact hmono
  -- `ofReal` arithmetic for the squared difference quotient.
  have hcore : ENNReal.ofReal (((u z θ - u (z - h) θ)/h)^2)
      = ENNReal.ofReal ((u z θ - u (z - h) θ)^2) * (ENNReal.ofReal h)⁻¹ * (ENNReal.ofReal h)⁻¹ := by
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
    _ = (ENNReal.ofReal ((u z θ - u (z - h) θ)^2) * (ENNReal.ofReal h)⁻¹ * (ENNReal.ofReal h)⁻¹)
          * ENNReal.ofReal ((w z θ)^2) := by rw [hcore]
    _ ≤ (ENNReal.ofReal h * (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2)))
          * (ENNReal.ofReal h)⁻¹ * (ENNReal.ofReal h)⁻¹ * ENNReal.ofReal ((w z θ)^2) := h3
    _ = ENNReal.ofReal ((w z θ)^2) *
          (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2))
          * (ENNReal.ofReal h)⁻¹ := by
        rw [show (ENNReal.ofReal h * (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2)))
              * (ENNReal.ofReal h)⁻¹ * (ENNReal.ofReal h)⁻¹ * ENNReal.ofReal ((w z θ)^2)
            = (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2))
              * (ENNReal.ofReal h * (ENNReal.ofReal h)⁻¹) * (ENNReal.ofReal h)⁻¹
              * ENNReal.ofReal ((w z θ)^2) from by ring]
        rw [ht]; ring
    _ ≤ (ENNReal.ofReal C *
          (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2)))
          * (ENNReal.ofReal h)⁻¹ := h4
    _ = ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹ *
          ∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2) := by
        ring

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.exists_scaling_const_seq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

/-- A continuous real function on the closed rectangle `[a,b] × [c,d]` (`a < b`, `c < d`) is
bounded above. -/
lemma exists_upper_bound_of_continuousOn {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {ρ : ℝ → ℝ → ℝ}
    (hρc : ContinuousOn (Function.uncurry ρ) (Set.Icc a b ×ˢ Set.Icc c d)) :
    ∃ M : ℝ, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, ρ z θ ≤ M := by
  have hK : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) :=
    (isCompact_Icc (a := a) (b := b)).prod (isCompact_Icc (a := c) (b := d))
  have hne : (Set.Icc a b ×ˢ Set.Icc c d).Nonempty :=
    ⟨(a, c), by rw [Set.mem_prod]; exact ⟨⟨le_rfl, hab.le⟩, ⟨le_rfl, hcd.le⟩⟩⟩
  obtain ⟨p, _hp, hmax⟩ := hK.exists_isMaxOn hne hρc
  exact ⟨ρ p.1 p.2, fun z hz θ hθ => (isMaxOn_iff.mp hmax) (z, θ) ⟨hz, hθ⟩⟩

theorem exists_scaling_const_seq {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {ι : Type*} [Fintype ι] (hne : Nonempty ι) {ρ : ι → ℝ → ℝ → ℝ}
    (hρc : ∀ k, ContinuousOn (Function.uncurry (ρ k)) (Set.Icc a b ×ˢ Set.Icc c d))
    (hρp : ∀ k, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < ρ k z θ) :
    ∃ C : ℕ → ℝ, (∀ j, 1 ≤ C j) ∧
      (∀ (j : ℕ) (k : ι) (z y θ : ℝ), z ∈ Set.Icc a b → y ∈ Set.Icc a b → θ ∈ Set.Icc c d →
        |z - y| ≤ 1 / ((j : ℝ) + 1) → (ρ k z θ) ^ 2 ≤ C j * (ρ k y θ) ^ 2) ∧
      Filter.Tendsto C Filter.atTop (nhds 1) := by
  -- per-`k` positive lower bound and uniform continuity on the box
  choose m hm using fun k => (rho_bounds hab hcd (hρc k) (hρp k)).1
  -- per-`k` upper bound on the box
  choose M hM using fun k => exists_upper_bound_of_continuousOn hab hcd (hρc k)
  have hmpos : ∀ k, 0 < m k := fun k => (hm k).1
  have hmle : ∀ k, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, m k ≤ ρ k z θ := fun k => (hm k).2
  -- a global upper bound for all the ratios
  have huniv : (Finset.univ : Finset ι).Nonempty := ⟨Classical.choice hne, Finset.mem_univ _⟩
  set B : ℝ := Finset.univ.sup' huniv (fun k => (M k) ^ 2 / (m k) ^ 2) with hBdef
  -- the set of ratios admissible at scale `j`
  let T : ℕ → Set ℝ := fun j => {v : ℝ | ∃ k : ι, ∃ z ∈ Set.Icc a b, ∃ y ∈ Set.Icc a b,
      ∃ θ ∈ Set.Icc c d, |z - y| ≤ 1 / ((j : ℝ) + 1) ∧ v = (ρ k z θ) ^ 2 / (ρ k y θ) ^ 2}
  have ha_mem : a ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hc_mem : c ∈ Set.Icc c d := ⟨le_rfl, hcd.le⟩
  have hone : ∀ j, (1 : ℝ) ∈ T j := by
    intro j
    refine ⟨Classical.choice hne, a, ha_mem, a, ha_mem, c, hc_mem, ?_, ?_⟩
    · rw [sub_self, abs_zero]
      exact le_of_lt (one_div_pos.mpr (by positivity))
    · rw [div_self]
      exact pow_ne_zero 2 (ne_of_gt (hρp _ a ha_mem c hc_mem))
  have hTne : ∀ j, (T j).Nonempty := fun j => ⟨1, hone j⟩
  have hTbdd : ∀ j, BddAbove (T j) := by
    intro j
    refine ⟨B, ?_⟩
    intro v hv
    obtain ⟨k, z, hz, y, hy, θ, hθ, _, hv⟩ := hv
    rw [hv]
    have hzpos : 0 < ρ k z θ := hρp k z hz θ hθ
    have hypos : 0 < ρ k y θ := hρp k y hy θ hθ
    have h1 : (ρ k z θ) ^ 2 ≤ (M k) ^ 2 :=
      pow_le_pow_left₀ hzpos.le (hM k z hz θ hθ) 2
    have h2 : (m k) ^ 2 ≤ (ρ k y θ) ^ 2 :=
      pow_le_pow_left₀ (hmpos k).le (hmle k y hy θ hθ) 2
    have h3 : (ρ k z θ) ^ 2 / (ρ k y θ) ^ 2 ≤ (M k) ^ 2 / (m k) ^ 2 :=
      div_le_div₀ (sq_nonneg _) h1 (pow_pos (hmpos k) 2) h2
    exact le_trans h3 (Finset.le_sup' (fun k => (M k) ^ 2 / (m k) ^ 2) (Finset.mem_univ k))
  have h1j : ∀ j, 1 ≤ sSup (T j) := fun j => le_csSup (hTbdd j) (hone j)
  refine ⟨fun j => sSup (T j), h1j, ?_, ?_⟩
  · intro j k z y θ hz hy hθ hzy
    have hypos : 0 < ρ k y θ := hρp k y hy θ hθ
    have hv : (ρ k z θ) ^ 2 / (ρ k y θ) ^ 2 ∈ T j := ⟨k, z, hz, y, hy, θ, hθ, hzy, rfl⟩
    have hle : (ρ k z θ) ^ 2 / (ρ k y θ) ^ 2 ≤ sSup (T j) := le_csSup (hTbdd j) hv
    rw [div_le_iff₀ (pow_pos hypos 2)] at hle
    exact hle
  · rw [tendsto_order]
    constructor
    · intro a' ha'
      exact Filter.Eventually.of_forall (fun j => lt_of_lt_of_le ha' (h1j j))
    · intro b hb
      have hb1 : 0 < b - 1 := by linarith
      set e : ℝ := min ((b - 1) / 4) (1 / 2) with hedef
      have hepos : 0 < e := by rw [hedef]; exact lt_min (by linarith) (by norm_num)
      have he1 : e ≤ 1 / 2 := by rw [hedef]; exact min_le_right _ _
      have he2 : e ≤ (b - 1) / 4 := by rw [hedef]; exact min_le_left _ _
      have hkey : (1 + e) ^ 2 < b := by
        have h1 : e ^ 2 ≤ e * (1 / 2) := by
          calc e ^ 2 = e * e := by ring
            _ ≤ e * (1 / 2) := mul_le_mul_of_nonneg_left he1 hepos.le
        nlinarith [h1, he1, he2, hepos]
      choose δ hδ using fun k =>
        (rho_bounds hab hcd (hρc k) (hρp k)).2 (e * m k) (mul_pos hepos (hmpos k))
      have hEv : ∀ᶠ j : ℕ in Filter.atTop, ∀ k : ι, 1 / ((j : ℝ) + 1) < δ k := by
        refine Filter.eventually_all.mpr ?_
        intro k
        exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
          (Iio_mem_nhds (hδ k).1)
      filter_upwards [hEv] with j hj
      have hsup : sSup (T j) ≤ (1 + e) ^ 2 := by
        refine csSup_le (hTne j) ?_
        intro v hv
        obtain ⟨k, z, hz, y, hy, θ, hθ, hzy, hv⟩ := hv
        rw [hv]
        have hypos : 0 < ρ k y θ := hρp k y hy θ hθ
        have hzpos : 0 < ρ k z θ := hρp k z hz θ hθ
        have hδk : |z - y| < δ k := lt_of_le_of_lt hzy (hj k)
        have hdiff : |ρ k z θ - ρ k y θ| < e * m k := (hδ k).2 z hz y hy θ hθ hδk
        have hstep : ρ k z θ < (1 + e) * ρ k y θ := by
          have hlt : ρ k z θ - ρ k y θ < e * m k := (abs_sub_lt_iff.mp hdiff).1
          have hme : e * m k ≤ e * ρ k y θ :=
            mul_le_mul_of_nonneg_left (hmle k y hy θ hθ) hepos.le
          nlinarith
        rw [div_le_iff₀ (pow_pos hypos 2)]
        calc (ρ k z θ) ^ 2 ≤ ((1 + e) * ρ k y θ) ^ 2 :=
              le_of_lt (pow_lt_pow_left₀ hstep hzpos.le (by norm_num))
          _ = (1 + e) ^ 2 * (ρ k y θ) ^ 2 := by ring
      linarith

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.lintegral_subbox_eq_iSup =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

open MeasureTheory

/-- The closed sub-boxes of the rectangle `[a,b] × [c,d]`, obtained by shrinking each side by
the margin `(b-a)/(k+2)` respectively `(d-c)/(k+2)`.  They increase with `k` and exhaust the
open rectangle `(a,b) × (c,d)`. -/
private def subbox (a b c d : ℝ) (k : ℕ) : Set (ℝ × ℝ) :=
  Set.Icc (a + (b - a) / ((k : ℝ) + 2)) (b - (b - a) / ((k : ℝ) + 2)) ×ˢ
    Set.Icc (c + (d - c) / ((k : ℝ) + 2)) (d - (d - c) / ((k : ℝ) + 2))

/-- The sub-boxes `subbox a b c d k` are increasing in `k`. -/
private lemma subbox_mono {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    Monotone (subbox a b c d) := by
  apply monotone_nat_of_le_succ
  intro k
  have hb : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hd : (0 : ℝ) < d - c := sub_pos.mpr hcd
  have hδb : (b - a) / (((k + 1 : ℕ) : ℝ) + 2) ≤ (b - a) / ((k : ℝ) + 2) := by
    apply div_le_div_of_nonneg_left (le_of_lt hb) (by positivity)
    push_cast
    linarith
  have hδd : (d - c) / (((k + 1 : ℕ) : ℝ) + 2) ≤ (d - c) / ((k : ℝ) + 2) := by
    apply div_le_div_of_nonneg_left (le_of_lt hd) (by positivity)
    push_cast
    linarith
  intro p hp
  simp only [subbox, Set.mem_prod, Set.mem_Icc] at hp ⊢
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hp
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

-- The hypothesis `hg` of the target statement is not needed for the argument: the identity
-- holds for an arbitrary `g : ℝ × ℝ → ENNReal`.  Silence the unused-variable linter rather
-- than change the statement of the lemma.
set_option linter.unusedVariables false

/-- The Lebesgue integral of a nonnegative function over the closed rectangle `[a,b] × [c,d]`
is the supremum of its integrals over the increasing family of closed sub-boxes obtained by
cutting off the margin `(b-a)/(k+2)` (resp. `(d-c)/(k+2)`) from each side.

This is monotone convergence along an exhaustion of the rectangle, modulo the null set
consisting of its boundary. -/
theorem lintegral_subbox_eq_iSup {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {g : ℝ × ℝ → ENNReal}
    (hg : AEMeasurable g (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))) :
    ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d, g p =
      ⨆ k : ℕ, ∫⁻ p in (Set.Icc (a + (b - a) / ((k : ℝ) + 2)) (b - (b - a) / ((k : ℝ) + 2)) ×ˢ
          Set.Icc (c + (d - c) / ((k : ℝ) + 2)) (d - (d - c) / ((k : ℝ) + 2))), g p := by
  -- the sub-boxes increase with `k`, hence form a directed family
  have hdir : Directed (fun x1 x2 : Set (ℝ × ℝ) => x1 ⊆ x2) (subbox a b c d) :=
    (subbox_mono hab hcd).directed_le
  -- they exhaust the open rectangle, which differs from the closed one by a null boundary
  have hUnion : (⋃ k, subbox a b c d k) = Set.Ioo a b ×ˢ Set.Ioo c d := by
    simpa only [subbox] using iUnion_subbox hab hcd
  have hnull : volume (Set.Icc a b ×ˢ Set.Icc c d \ Set.Ioo a b ×ˢ Set.Ioo c d : Set (ℝ × ℝ)) = 0 :=
    volume_box_sdiff_openBox a b c d
  have hae : (Set.Icc a b ×ˢ Set.Icc c d : Set (ℝ × ℝ)) =ᵐ[volume]
      (Set.Ioo a b ×ˢ Set.Ioo c d) := by
    rw [ae_eq_set]
    refine ⟨hnull, ?_⟩
    rw [Set.sdiff_eq_empty.mpr (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)]
    simp
  rw [Measure.restrict_congr_set hae]
  rw [← hUnion]
  rw [setLIntegral_iUnion_of_directed g hdir]
  rfl

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.ofReal_deriv_sq_le_liminf_backwardDiffQuot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

/-- `ENNReal.ofReal` of the square of the derivative is dominated by the
`liminf` of `ENNReal.ofReal` of the squares of the backward difference quotients
with step `1/(j+1)`.

When `f` is differentiable at `x` the backward difference quotients converge to
`deriv f x`, hence so do their (squares and) `ofReal`s, and the `liminf` of a
convergent sequence is its limit.  When `f` is not differentiable at `x`,
`deriv f x = 0` by definition, so the left-hand side is `0` and the claim is
trivial. -/
theorem ofReal_deriv_sq_le_liminf_backwardDiffQuot (f : ℝ → ℝ) (x ρ : ℝ) :
    ENNReal.ofReal ((deriv f x * ρ) ^ 2)
      ≤ Filter.liminf (fun j : ℕ => ENNReal.ofReal
          (((f x - f (x - 1 / ((j : ℝ) + 1))) * ((j : ℝ) + 1) * ρ) ^ 2)) Filter.atTop := by
  by_cases hx : DifferentiableAt ℝ f x
  · -- Differentiable case: the backward difference quotients converge to `deriv f x`.
    have hs : Filter.Tendsto (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hspos : ∀ j : ℕ, 0 < (1 : ℝ) / ((j : ℝ) + 1) := fun j => by positivity
    have hT : Filter.Tendsto
        (fun j : ℕ => (f x - f (x - 1 / ((j : ℝ) + 1))) / (1 / ((j : ℝ) + 1)))
        Filter.atTop (nhds (deriv f x)) :=
      tendsto_backward_diffQuot hx hs hspos
    have hw : Filter.Tendsto
        (fun j : ℕ => ((f x - f (x - 1 / ((j : ℝ) + 1))) / (1 / ((j : ℝ) + 1))) * ρ)
        Filter.atTop (nhds (deriv f x * ρ)) :=
      hT.mul tendsto_const_nhds
    have h2 : Filter.Tendsto
        (fun j : ℕ => (((f x - f (x - 1 / ((j : ℝ) + 1))) / (1 / ((j : ℝ) + 1))) * ρ) ^ 2)
        Filter.atTop (nhds ((deriv f x * ρ) ^ 2)) :=
      hw.pow 2
    have h3 : Filter.Tendsto
        (fun j : ℕ => ENNReal.ofReal
          ((((f x - f (x - 1 / ((j : ℝ) + 1))) / (1 / ((j : ℝ) + 1))) * ρ) ^ 2))
        Filter.atTop (nhds (ENNReal.ofReal ((deriv f x * ρ) ^ 2))) :=
      ENNReal.tendsto_ofReal h2
    -- `(j+1) = 1/(1/(j+1))`, so the two sequences agree.
    have heq : (fun j : ℕ => ENNReal.ofReal
          ((((f x - f (x - 1 / ((j : ℝ) + 1))) * ((j : ℝ) + 1) * ρ) ^ 2)))
        = fun j : ℕ => ENNReal.ofReal
          ((((f x - f (x - 1 / ((j : ℝ) + 1))) / (1 / ((j : ℝ) + 1))) * ρ) ^ 2) := by
      funext j
      congr 1
      have h : ((f x - f (x - 1 / ((j : ℝ) + 1))) / (1 / ((j : ℝ) + 1)))
          = ((f x - f (x - 1 / ((j : ℝ) + 1))) * ((j : ℝ) + 1)) := by
        field_simp
      rw [h]
    rw [heq, Filter.Tendsto.liminf_eq h3]
  · -- Non-differentiable case: `deriv f x = 0`, so the left-hand side vanishes.
    have hd : deriv f x = 0 := deriv_zero_of_not_differentiableAt hx
    simp [hd]

end Work.FTS.StrongEps.LocUnif
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.EqcAux.exists_cutoff_rect_C2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.StrongLWP.Sobolev.EqcAux

set_option autoImplicit false

/-! ## Two general tools for compact support -/

/-- The support of a product `(z,θ) ↦ f z * g θ` of two one-variable functions is contained
in `support f ×ˢ support g`; taking closures gives
`tsupport (·) ⊆ tsupport f ×ˢ tsupport g`. -/
lemma tsupport_prodMul_subset {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → ℝ} {g : β → ℝ} :
    tsupport (fun p : α × β => f p.1 * g p.2) ⊆ tsupport f ×ˢ tsupport g := by
  show closure (Function.support (fun p : α × β => f p.1 * g p.2)) ⊆
    closure (Function.support f) ×ˢ closure (Function.support g)
  rw [← closure_prod_eq]
  apply closure_mono
  intro p hp
  rw [Set.mem_prod]
  exact mul_ne_zero_iff.mp hp

/-- **Compact support is preserved by forming the product of two one-variable functions.** -/
lemma hasCompactSupport_prodMul {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → ℝ} {g : β → ℝ} (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (fun p : α × β => f p.1 * g p.2) :=
  IsCompact.of_isClosed_subset (hf.prod hg) (isClosed_tsupport _)
    (tsupport_prodMul_subset (f := f) (g := g))

/-- **A `C²` function with compact support has bounded first and second derivatives.**
`fderiv f` is continuous (`ContDiff.continuous_fderiv`) and compactly supported
(`HasCompactSupport.fderiv`), hence bounded in norm; the same argument, one order up, gives
the bound on the second derivative.  The constant `M` is chosen positive. -/
lemma exists_bound_fderiv_fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (h2 : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) :
    ∃ M : ℝ, 0 < M ∧ (∀ x, ‖fderiv ℝ f x‖ ≤ M) ∧ (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) := by
  have hcf : HasCompactSupport (fderiv ℝ f) := HasCompactSupport.fderiv (𝕜 := ℝ) hc
  have h1 : ContDiff ℝ (1 : WithTop ℕ∞) f := h2.of_le (by norm_num)
  obtain ⟨M₁, hM₁⟩ := (h1.continuous_fderiv (by norm_num)).bounded_above_of_compact_support hcf
  have hd : ContDiff ℝ (1 : WithTop ℕ∞) (fderiv ℝ f) := h2.fderiv_right (by norm_num)
  have hcf2 : HasCompactSupport (fderiv ℝ (fderiv ℝ f)) :=
    HasCompactSupport.fderiv (𝕜 := ℝ) hcf
  obtain ⟨M₂, hM₂⟩ := (hd.continuous_fderiv (by norm_num)).bounded_above_of_compact_support hcf2
  exact ⟨|M₁| + |M₂| + 1, by positivity,
    fun x => by linarith [hM₁ x, le_abs_self M₁, abs_nonneg M₂],
    fun x => by linarith [hM₂ x, le_abs_self M₂, abs_nonneg M₁]⟩

/-! ## The target -/

/-- **A `C^∞` rectangular cut-off with a uniform bound on the first two derivatives.**
The two one-dimensional factors come from `smoothIntervalCutoff`; their product is the
cut-off `χ`.  All the clauses are immediate from the defining properties of the factors,
except the two derivative bounds, which come from `exists_bound_fderiv_fderiv` and compact
support.

The hypotheses `0 < a'`, `0 < c'` and `d' < π / 2` are not used: the construction works for
arbitrary nested rectangles. -/
theorem exists_cutoff_rect_C2 {a b c d a' b' c' d' : ℝ}
    (ha' : 0 < a') (h1 : a' < a) (h2 : a ≤ b) (h3 : b < b')
    (hc' : 0 < c') (h4 : c' < c) (h5 : c ≤ d) (h6 : d < d') (h7 : d' < π / 2) :
    ∃ (χ : ℝ × ℝ → ℝ) (M : ℝ), 0 < M ∧ (∀ n : ℕ, ContDiff ℝ n χ) ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x) ∧ (∀ x, χ x ≤ 1) ∧
      (∀ z, z ∈ Set.Icc a b → ∀ θ, θ ∈ Set.Icc c d → χ (z, θ) = 1) ∧
      (∀ x, x ∉ Set.Icc a' b' ×ˢ Set.Icc c' d' → χ x = 0) ∧
      (∀ x, ‖fderiv ℝ χ x‖ ≤ M) ∧ (∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ M) := by
  obtain ⟨g, hgsm, hgcs, hgnn, hgle, hgone, hgzero⟩ := smoothIntervalCutoff h1 h3
  obtain ⟨v, hvsm, hvcs, hvnn, hvle, hvone, hvzero⟩ := smoothIntervalCutoff h4 h6
  have hsm : ∀ n : ℕ, ContDiff ℝ n (fun p : ℝ × ℝ => g p.1 * v p.2) := fun n =>
    ((hgsm n).comp contDiff_fst).mul ((hvsm n).comp contDiff_snd)
  have hcs : HasCompactSupport (fun p : ℝ × ℝ => g p.1 * v p.2) :=
    hasCompactSupport_prodMul hgcs hvcs
  obtain ⟨M, hMpos, hMn1, hMn2⟩ := exists_bound_fderiv_fderiv (hsm 2) hcs
  exact ⟨fun p : ℝ × ℝ => g p.1 * v p.2, M, hMpos, hsm, hcs,
    fun x => mul_nonneg (hgnn x.1) (hvnn x.2),
    fun x => by
      calc g x.1 * v x.2 ≤ 1 * 1 := mul_le_mul (hgle x.1) (hvle x.2) (hvnn x.2) zero_le_one
        _ = 1 := by ring,
    fun z hz θ hθ => by
      show g z * v θ = 1
      rw [hgone z hz, hvone θ hθ, mul_one],
    fun x hx => by
      obtain ⟨z, θ⟩ := x
      show g z * v θ = 0
      by_cases hz : z ∈ Set.Icc a' b'
      · have hθ : θ ∉ Set.Icc c' d' := fun hθ => hx (Set.mem_prod.mpr ⟨hz, hθ⟩)
        rw [hvzero θ hθ, mul_zero]
      · rw [hgzero z hz, zero_mul],
    hMn1, hMn2⟩

end Work.FTS.StrongLWP.Sobolev.EqcAux
end
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.grad_L2_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf

open MeasureTheory

/-!
# The two-dimensional `L²`-gradient interpolation inequality

For a `C²` compactly supported function `v : ℝ × ℝ → ℝ` we prove

`∫ ‖fderiv ℝ v‖² ≤ 4 √(∫ v²) √(∫ ‖fderiv ℝ (fderiv ℝ v)‖²)`.

The proof has three ingredients.

* A norm computation on `ℝ × ℝ` (whose norm is the sup norm): for a linear functional `ℓ` the
  dual norm is bounded by the sum of the absolute values of its two coordinate values, whence
  `‖ℓ‖² ≤ (ℓ (1,1))² + (ℓ (1,-1))²`.
* Integration by parts in the two diagonal directions `(1,1)` and `(1,-1)`
  (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`): for `w = ∂_u v`,
  `∫ w² = -∫ (∂_u w) v ≤ |∫ (∂_u w) v|`.
* Cauchy–Schwarz (`Work.Blocks.IMC.cs_integral_mul_le`) and the pointwise bound
  `|∂_u w| ≤ ‖fderiv ℝ (fderiv ℝ v)‖` valid for `‖u‖ = 1`.
-/


/-- The norm of a compactly supported function has compact support. -/
private lemma hasCompactSupport_norm {α : Type*} [TopologicalSpace α] {E : Type*}
    [NormedAddCommGroup E] {f : α → E} (hf : HasCompactSupport f) :
    HasCompactSupport (fun x => ‖f x‖) := hf.norm

/-- Rewriting the pointwise square as a product. -/
private lemma integrable_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (h : Integrable (fun x => f x * f x) μ) : Integrable (fun x => f x ^ 2) μ :=
  h.congr (Filter.Eventually.of_forall fun x => by simp [sq])

/-- `x ↦ f x ^ 2` is integrable for a continuous compactly supported `f`. -/
private lemma integrable_sq_of {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    {f : α → ℝ} (hc : Continuous f) (hf : HasCompactSupport f) :
    Integrable (fun x => f x ^ 2) μ :=
  integrable_sq ((hc.mul hc).integrable_of_hasCompactSupport
    (by simpa only [Pi.mul_apply] using hf.mul_right (f' := f)))

/-- `x ↦ ‖f x‖ ^ 2` is integrable for a continuous compactly supported `f`. -/
private lemma integrable_norm_sq_of {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    {E : Type*} [NormedAddCommGroup E] {f : α → E} (hc : Continuous f)
    (hf : HasCompactSupport f) : Integrable (fun x => ‖f x‖ ^ 2) μ :=
  integrable_sq ((hc.norm.mul hc.norm).integrable_of_hasCompactSupport
    (by simpa only [Pi.mul_apply] using
      (hasCompactSupport_norm hf).mul_right (f' := fun x => ‖f x‖)))

/-- The dual norm on `ℝ × ℝ` (with the sup norm) is bounded by the sum of the absolute values of
the two coordinate values. -/
private lemma norm_bound (ℓ : ℝ × ℝ →L[ℝ] ℝ) : ‖ℓ‖ ≤ |ℓ (1,0)| + |ℓ (0,1)| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  have h1 : y = y.1 • ((1:ℝ),0) + y.2 • ((0:ℝ),(1:ℝ)) := by ext <;> simp
  have hℓy : ℓ y = y.1 * ℓ (1,0) + y.2 * ℓ (0,1) := by
    conv_lhs => rw [h1]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [hℓy, Real.norm_eq_abs]
  calc |y.1 * ℓ (1, 0) + y.2 * ℓ (0, 1)|
      ≤ |y.1 * ℓ (1, 0)| + |y.2 * ℓ (0, 1)| := abs_add_le _ _
    _ = |y.1| * |ℓ (1, 0)| + |y.2| * |ℓ (0, 1)| := by rw [abs_mul, abs_mul]
    _ ≤ ‖y‖ * |ℓ (1, 0)| + ‖y‖ * |ℓ (0, 1)| := by
        have h1 : |y.1| ≤ ‖y‖ := by simpa [Real.norm_eq_abs] using norm_fst_le y
        have h2 : |y.2| ≤ ‖y‖ := by simpa [Real.norm_eq_abs] using norm_snd_le y
        nlinarith [abs_nonneg (ℓ (1,0)), abs_nonneg (ℓ (0,1)), norm_nonneg y]
    _ = (|ℓ (1, 0)| + |ℓ (0, 1)|) * ‖y‖ := by ring

/-- Squaring: the `ℓ²`-norm of a linear functional on `ℝ × ℝ` is dominated by its values on the
two diagonal directions `(1,1)` and `(1,-1)`. -/
private lemma norm_sq_le_diag (ℓ : ℝ × ℝ →L[ℝ] ℝ) :
    ‖ℓ‖ ^ 2 ≤ (ℓ (1,1)) ^ 2 + (ℓ (1,-1)) ^ 2 := by
  have hb := norm_bound ℓ
  have h11 : ℓ (1,1) = ℓ (1,0) + ℓ (0,1) := by
    have : ((1:ℝ),(1:ℝ)) = ((1:ℝ),0) + ((0:ℝ),(1:ℝ)) := by ext <;> norm_num
    rw [this, map_add]
  have h1m : ℓ (1,-1) = ℓ (1,0) - ℓ (0,1) := by
    have : ((1:ℝ),(-1:ℝ)) = ((1:ℝ),0) - ((0:ℝ),(1:ℝ)) := by ext <;> norm_num
    rw [this, map_sub]
  rw [h11, h1m]
  calc ‖ℓ‖ ^ 2 ≤ (|ℓ (1,0)| + |ℓ (0,1)|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ ≤ (ℓ (1,0) + ℓ (0,1)) ^ 2 + (ℓ (1,0) - ℓ (0,1)) ^ 2 := by
        nlinarith [sq_nonneg (|ℓ (1,0)| - |ℓ (0,1)|), sq_abs (ℓ (1,0)), sq_abs (ℓ (0,1)),
          abs_nonneg (ℓ (1,0)), abs_nonneg (ℓ (0,1))]

/-- The directional `L²`-gradient bound: for a unit vector `u`,
`∫ ((fderiv ℝ v x) u)² ≤ √(∫ v²) √(∫ ‖fderiv ℝ (fderiv ℝ v)‖²)`. -/
private lemma grad_dir_le {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hc : HasCompactSupport v)
    {u : ℝ × ℝ} (hu : ‖u‖ = 1) :
    ∫ x, ((fderiv ℝ v x) u) ^ 2 ≤ Real.sqrt (∫ x, (v x) ^ 2) *
      Real.sqrt (∫ x, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) := by
  set w : ℝ × ℝ → ℝ := fun x => (fderiv ℝ v x) u with hw
  have hwcd : ContDiff ℝ 1 w := by
    rw [hw]
    have h1 : ContDiff ℝ 1 (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (fderiv ℝ v p.1) p.2) :=
      hv.contDiff_fderiv_apply (m := 1) (by norm_num)
    have h2 : ContDiff ℝ 1 (fun x : ℝ × ℝ => (x, u)) := by fun_prop
    exact h1.comp h2
  have hdfv : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hcw : HasCompactSupport w := hc.fderiv_apply ℝ u
  have hdw : Continuous (fun x => (fderiv ℝ w x) u) :=
    (hwcd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdcw : HasCompactSupport (fun x => (fderiv ℝ w x) u) := hcw.fderiv_apply ℝ u
  have hdv : Continuous (fun x => (fderiv ℝ v x) u) :=
    (hv.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hA1 : Integrable (fun x => ((fderiv ℝ w x) u) ^ 2) :=
    integrable_sq_of (f := fun x => (fderiv ℝ w x) u) hdw hdcw
  have hA2 : Integrable (fun x => (v x) ^ 2) :=
    integrable_sq_of (f := v) hdfv.continuous hc
  have hI1 : Integrable (fun x => (fderiv ℝ w x) u * v x) := by
    refine (hdw.mul hdfv.continuous).integrable_of_hasCompactSupport ?_
    simpa only [Pi.mul_apply] using hdcw.mul_right (f' := v)
  have hI2 : Integrable (fun x => w x * (fderiv ℝ v x) u) := by
    refine (hwcd.continuous.mul hdv).integrable_of_hasCompactSupport ?_
    simpa only [Pi.mul_apply] using hcw.mul_right (f' := (fun x => (fderiv ℝ v x) u))
  have hI3 : Integrable (fun x => w x * v x) := by
    refine (hwcd.continuous.mul hdfv.continuous).integrable_of_hasCompactSupport ?_
    simpa only [Pi.mul_apply] using hcw.mul_right (f' := v)
  have hIBP : ∫ x, w x * (fderiv ℝ v x) u = -∫ x, (fderiv ℝ w x) u * v x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (f := w) (g := v) (v := u) hI1 hI2 hI3
      (fun x _ => hwcd.differentiable (by norm_num) x) (fun x _ => hdfv x)
  have hw2 : ∫ x, (w x) ^ 2 = ∫ x, w x * (fderiv ℝ v x) u := by
    apply integral_congr_ae
    filter_upwards with x
    simp only [hw]
    ring
  have hchain : ∀ x, fderiv ℝ w x =
      (ContinuousLinearMap.apply ℝ ℝ u).comp (fderiv ℝ (fderiv ℝ v) x) := by
    intro x
    rw [hw]
    have hdf' : Differentiable ℝ (fderiv ℝ v) :=
      (hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    have h := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.apply ℝ ℝ u)).comp x
      ((hdf' x).hasFDerivAt)
    simpa [Function.comp_def] using h.fderiv
  have hbd : ∀ x, ‖(fderiv ℝ w x) u‖ ≤ ‖fderiv ℝ (fderiv ℝ v) x‖ := by
    intro x
    rw [hchain x]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    calc ‖(fderiv ℝ (fderiv ℝ v) x u) u‖
        ≤ ‖fderiv ℝ (fderiv ℝ v) x u‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ v) x‖ * ‖u‖) * ‖u‖ := by
          have h1 := ContinuousLinearMap.le_opNorm (fderiv ℝ (fderiv ℝ v) x) u
          nlinarith [norm_nonneg u, norm_nonneg (fderiv ℝ (fderiv ℝ v) x)]
      _ = ‖fderiv ℝ (fderiv ℝ v) x‖ := by rw [hu]; ring
  have hBcs : HasCompactSupport (fun x => fderiv ℝ (fderiv ℝ v) x) :=
    hc.of_isClosed_subset (isClosed_tsupport _)
      ((tsupport_fderiv_subset (𝕜 := ℝ) (f := fderiv ℝ v)).trans
        (tsupport_fderiv_subset (𝕜 := ℝ) (f := v)))
  have hBc1 : Continuous (fun x => fderiv ℝ (fderiv ℝ v) x) :=
    (hv.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hA3 : Integrable (fun x => ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) :=
    integrable_norm_sq_of (f := fun x => fderiv ℝ (fderiv ℝ v) x) hBc1 hBcs
  have h2 : ∫ x, ((fderiv ℝ w x) u) ^ 2 ≤ ∫ x, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2 := by
    apply integral_mono hA1 hA3
    intro x
    have hx := pow_le_pow_left₀ (norm_nonneg ((fderiv ℝ w x) u)) (hbd x) 2
    rwa [Real.norm_eq_abs, sq_abs] at hx
  have hCS := Work.Blocks.IMC.cs_integral_mul_le volume (hdw.aestronglyMeasurable)
    (hdfv.continuous.aestronglyMeasurable) hA1 hA2
  calc ∫ x, ((fderiv ℝ v x) u) ^ 2
      = ∫ x, (w x) ^ 2 := by simp only [hw]
    _ = ∫ x, w x * (fderiv ℝ v x) u := hw2
    _ = -∫ x, (fderiv ℝ w x) u * v x := hIBP
    _ ≤ |∫ x, (fderiv ℝ w x) u * v x| := neg_le_abs _
    _ ≤ Real.sqrt (∫ x, ((fderiv ℝ w x) u) ^ 2) * Real.sqrt (∫ x, (v x) ^ 2) := hCS
    _ ≤ Real.sqrt (∫ x, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) * Real.sqrt (∫ x, (v x) ^ 2) := by
        apply mul_le_mul_of_nonneg_right
        · exact Real.sqrt_le_sqrt h2
        · exact Real.sqrt_nonneg _
    _ = Real.sqrt (∫ x, (v x) ^ 2) * Real.sqrt (∫ x, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) := by
        ring

theorem grad_L2_le {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hc : HasCompactSupport v) :
    ∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 2 ≤ 4 * Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
      * Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) := by
  have hvcf : Continuous (fun x : ℝ × ℝ => fderiv ℝ v x) := hv.continuous_fderiv (by norm_num)
  have hc11 : HasCompactSupport (fun x : ℝ × ℝ => (fderiv ℝ v x) ((1:ℝ),1)) :=
    hc.fderiv_apply ℝ ((1:ℝ),1)
  have hc1m : HasCompactSupport (fun x : ℝ × ℝ => (fderiv ℝ v x) ((1:ℝ),-1)) :=
    hc.fderiv_apply ℝ ((1:ℝ),-1)
  have hcd11 : Continuous (fun x : ℝ × ℝ => (fderiv ℝ v x) ((1:ℝ),1)) :=
    hvcf.clm_apply continuous_const
  have hcd1m : Continuous (fun x : ℝ × ℝ => (fderiv ℝ v x) ((1:ℝ),-1)) :=
    hvcf.clm_apply continuous_const
  have hf1 : Integrable (fun x : ℝ × ℝ => ((fderiv ℝ v x) ((1:ℝ),1)) ^ 2) :=
    integrable_sq_of (f := fun x : ℝ × ℝ => (fderiv ℝ v x) ((1:ℝ),1)) hcd11 hc11
  have hf2 : Integrable (fun x : ℝ × ℝ => ((fderiv ℝ v x) ((1:ℝ),-1)) ^ 2) :=
    integrable_sq_of (f := fun x : ℝ × ℝ => (fderiv ℝ v x) ((1:ℝ),-1)) hcd1m hc1m
  have hL : Integrable (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ 2) :=
    integrable_norm_sq_of (f := fderiv ℝ v) hvcf (hc.fderiv ℝ)
  have hpt : ∀ x : ℝ × ℝ,
      ‖fderiv ℝ v x‖ ^ 2 ≤ ((fderiv ℝ v x) ((1:ℝ),1)) ^ 2 + ((fderiv ℝ v x) ((1:ℝ),-1)) ^ 2 :=
    fun x => norm_sq_le_diag (fderiv ℝ v x)
  have h1 : ∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 2 ≤
      ∫ x : ℝ × ℝ, (((fderiv ℝ v x) ((1:ℝ),1)) ^ 2 + ((fderiv ℝ v x) ((1:ℝ),-1)) ^ 2) :=
    integral_mono hL (hf1.add hf2) hpt
  rw [integral_add hf1 hf2] at h1
  have e1 := grad_dir_le hv hc (u := ((1:ℝ),1)) (by norm_num)
  have e2 := grad_dir_le hv hc (u := ((1:ℝ),-1)) (by norm_num)
  have hX : 0 ≤ Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2) *
      Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc ∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 2
      ≤ (∫ x : ℝ × ℝ, ((fderiv ℝ v x) ((1:ℝ),1)) ^ 2) +
          ∫ x : ℝ × ℝ, ((fderiv ℝ v x) ((1:ℝ),-1)) ^ 2 := h1
    _ ≤ Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2) *
            Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) +
          Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2) *
            Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) := add_le_add e1 e2
    _ = 2 * (Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2) *
            Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)) := by ring
    _ ≤ 4 * (Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2) *
            Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2)) := by
        nlinarith [hX]
    _ = 4 * Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2)
          * Real.sqrt (∫ x : ℝ × ℝ, ‖fderiv ℝ (fderiv ℝ v) x‖ ^ 2) := by ring

end Work.FTS.StrongLWP.Sobolev.HolderHalf
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.leg_one_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory
open scoped Pointwise

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf

/-! ## First leg of the 2-D Morrey estimate

Averaging the segment identity over the ball `B(0,a)`:
`⨍_{ζ ∈ B(0,a)} |v p - v (p+ζ)| ≤ √2 (∫ ‖∇v‖⁴)^{1/4} √a`.

The substitution `ξ = t ζ` turns the inner integral at time `t` into `t^{-3}` times the same
quantity over `B(0,ta)`; Hölder (together with `‖ξ‖ ≤ ta` on that ball) gives
`t^{-3} · 4^{3/4}(ta)^{5/2}(∫‖∇v‖⁴)^{1/4} = 4^{3/4}a^{5/2}(∫‖∇v‖⁴)^{1/4} · t^{-1/2}`,
and `∫_0^1 t^{-1/2} dt = 2`. The final constant is
`(1/(4a²))·2·4^{3/4} = 2^{5/2}/4 = √2`. -/

/-- Integrability of a continuous function on a ball (via compactness of the closed ball). -/
private lemma legOne_integrableOn_ball_of_continuous {g : ℝ × ℝ → ℝ} (hg : Continuous g)
    (x : ℝ × ℝ) (r : ℝ) : IntegrableOn g (Metric.ball x r) volume :=
  (ContinuousOn.integrableOn_compact (isCompact_closedBall x r) hg.continuousOn).mono_set
    Metric.ball_subset_closedBall

/-- Volume of a ball of `ℝ × ℝ` (product/sup norm) in real form. -/
private lemma legOne_ball_volume_real (x : ℝ × ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (ℝ × ℝ)).real (Metric.ball x r) = 4 * r ^ 2 := by
  rw [Measure.real_def, vol_ball_prod x hr, ENNReal.toReal_ofReal (by positivity)]

/-- `4^{3/4} = 2√2`. -/
private lemma legOne_rpow_four : (4 : ℝ) ^ (3 / 4 : ℝ) = 2 * Real.sqrt 2 := by
  have h2 : (2 : ℝ) ^ (3 / 2 : ℝ) = 2 * Real.sqrt 2 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have h4 : (4 : ℝ) = (2 : ℝ) ^ (((2 : ℕ) : ℝ)) := by
    rw [Real.rpow_natCast]; norm_num
  nth_rewrite 1 [h4]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    show (((2 : ℕ) : ℝ)) * (3 / 4) = 3 / 2 by norm_num]
  exact h2

/-- `(4 R²)^{3/4} (R⁴ X)^{1/4} = 4^{3/4} R^{5/2} X^{1/4}` for `R > 0`, `X ≥ 0`. -/
private lemma legOne_rpow_arith {R X : ℝ} (hR : 0 < R) (hX : 0 ≤ X) :
    (4 * R ^ 2) ^ (3 / 4 : ℝ) * (R ^ 4 * X) ^ (1 / 4 : ℝ)
      = (4 : ℝ) ^ (3 / 4 : ℝ) * R ^ (5 / 2 : ℝ) * X ^ (1 / 4 : ℝ) := by
  have h4R : (4 * R ^ 2) ^ (3 / 4 : ℝ) = (4 : ℝ) ^ (3 / 4 : ℝ) * R ^ (3 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity : (0 : ℝ) ≤ R ^ 2)]
    congr 1
    rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR.le,
      show (((2 : ℕ) : ℝ)) * (3 / 4) = 3 / 2 by norm_num]
  have hRX : (R ^ 4 * X) ^ (1 / 4 : ℝ) = R * X ^ (1 / 4 : ℝ) := by
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ R ^ 4) hX]
    congr 1
    rw [← Real.rpow_natCast R 4, ← Real.rpow_mul hR.le,
      show (((4 : ℕ) : ℝ)) * (1 / 4) = 1 by norm_num, Real.rpow_one]
  have hR5 : R ^ (5 / 2 : ℝ) = R ^ (3 / 2 : ℝ) * R := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hR, Real.rpow_one]
  rw [h4R, hRX, hR5]
  ring

/-- Scaling arithmetic of the `t`-integral. -/
private lemma legOne_t_scale_arith {a t X : ℝ} (ha : 0 < a) (ht : 0 < t) :
    (t ^ 3)⁻¹ * ((4 : ℝ) ^ (3 / 4 : ℝ) * (t * a) ^ (5 / 2 : ℝ) * X)
      = ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ) * X) * t ^ (-(1 / 2) : ℝ) := by
  have h1 : (t * a) ^ (5 / 2 : ℝ) = t ^ (5 / 2 : ℝ) * a ^ (5 / 2 : ℝ) :=
    Real.mul_rpow ht.le ha.le
  have h2 : (t ^ 3)⁻¹ = t ^ (-(((3 : ℕ) : ℝ))) := by
    rw [← Real.rpow_natCast t 3, ← Real.rpow_neg ht.le]
  have h3 : (4 : ℝ) ^ (3 / 4 : ℝ) * (t ^ (5 / 2 : ℝ) * a ^ (5 / 2 : ℝ)) * X
      = t ^ (5 / 2 : ℝ) * ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ) * X) := by ring
  rw [h1, h2, h3, ← mul_assoc, ← Real.rpow_add ht,
    show -(((3 : ℕ) : ℝ)) + 5 / 2 = -(1 / 2) by norm_num]
  ring

/-- Final arithmetic: `(1/(4a²))·2·4^{3/4}a^{5/2} = √2 √a`. -/
private lemma legOne_final_arith {a X : ℝ} (ha : 0 < a) :
    (1 / (4 * a ^ 2)) * (2 * ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ) * X))
      = Real.sqrt 2 * X * Real.sqrt a := by
  have ha5 : a ^ (5 / 2 : ℝ) = a ^ 2 * Real.sqrt a := by
    have h : a ^ (5 / 2 : ℝ) = a ^ (((2 : ℕ) : ℝ)) * a ^ (1 / 2 : ℝ) := by
      rw [show (5 / 2 : ℝ) = (((2 : ℕ) : ℝ)) + 1 / 2 by norm_num, Real.rpow_add ha]
    rw [h, Real.rpow_natCast a 2, ← Real.sqrt_eq_rpow]
  rw [legOne_rpow_four, ha5]
  have hden : (4 * a ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The pointwise segment bound obtained from the fundamental theorem of calculus. -/
private lemma legOne_abs_sub_le_integral_fderiv {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v)
    {p z : ℝ × ℝ}
    (hseg : v z - v p = ∫ t in (0 : ℝ)..1, (fderiv ℝ v (p + t • (z - p))) (z - p)) :
    |v z - v p| ≤ ∫ t in (0 : ℝ)..1, ‖fderiv ℝ v (p + t • (z - p))‖ * ‖z - p‖ := by
  have hcont : Continuous (fun t : ℝ => (fderiv ℝ v (p + t • (z - p))) (z - p)) :=
    (hv.continuous_fderiv_apply (by norm_num)).comp
      ((continuous_const.add (continuous_id.smul continuous_const)).prodMk continuous_const)
  have hcont2 : Continuous (fun t : ℝ => fderiv ℝ v (p + t • (z - p))) :=
    (hv.continuous_fderiv (by norm_num)).comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hint1 : IntervalIntegrable
      (fun t : ℝ => |(fderiv ℝ v (p + t • (z - p))) (z - p)|) volume 0 1 := by
    simpa only [Real.norm_eq_abs] using hcont.norm.intervalIntegrable 0 1
  have hint2 : IntervalIntegrable
      (fun t : ℝ => ‖fderiv ℝ v (p + t • (z - p))‖ * ‖z - p‖) volume 0 1 :=
    (hcont2.norm.mul_const ‖z - p‖).intervalIntegrable 0 1
  rw [hseg]
  refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num : (0 : ℝ) ≤ 1)).trans ?_
  refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hint1 hint2
    (fun t _ => ?_)
  simpa only [Real.norm_eq_abs] using (fderiv ℝ v (p + t • (z - p))).le_opNorm (z - p)

/-- Change of variables `ξ = t ζ` in the weighted ball integral. -/
private lemma legOne_smul_subst {v : ℝ × ℝ → ℝ} (p : ℝ × ℝ) {a t : ℝ} (ht : 0 < t) :
    ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖
      = (t ^ 3)⁻¹ * ∫ ξ in Metric.ball (0 : ℝ × ℝ) (t * a), ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖ := by
  have ht0 : t ≠ 0 := ht.ne'
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  have hsmulball : t • Metric.ball (0 : ℝ × ℝ) a = Metric.ball (0 : ℝ × ℝ) (t * a) := by
    rw [smul_ball ht0, smul_zero, Real.norm_of_nonneg ht.le]
  have hfun : (fun ζ : ℝ × ℝ => ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖)
      = fun ζ : ℝ × ℝ => (fun ξ : ℝ × ℝ => ‖t⁻¹ • ξ‖ * ‖fderiv ℝ v (p + ξ)‖) (t • ζ) := by
    funext ζ
    simp only [smul_smul, inv_mul_cancel₀ ht0, one_smul]
  have hcongr : ∀ ξ : ℝ × ℝ,
      ‖t⁻¹ • ξ‖ * ‖fderiv ℝ v (p + ξ)‖ = t⁻¹ * (‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖) := by
    intro ξ
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
    ring
  rw [hfun, Measure.setIntegral_comp_smul_of_pos (μ := volume)
      (f := fun ξ : ℝ × ℝ => ‖t⁻¹ • ξ‖ * ‖fderiv ℝ v (p + ξ)‖)
      (s := Metric.ball (0 : ℝ × ℝ) a) ht, hsmulball, hfin]
  rw [smul_eq_mul, setIntegral_congr_fun measurableSet_ball (fun ξ _ => hcongr ξ),
    integral_const_mul]
  have h3 : (t ^ 2)⁻¹ * t⁻¹ = (t ^ 3)⁻¹ := by
    rw [← mul_inv_rev, show t * t ^ 2 = t ^ 3 by ring]
  rw [← h3, mul_assoc]

/-- The `L⁴`/Hölder bound on a ball. -/
private lemma legOne_ball_L4_bound {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v)
    (hc : HasCompactSupport v) (p : ℝ × ℝ) {R : ℝ} (hR : 0 < R) :
    ∫ ξ in Metric.ball (0 : ℝ × ℝ) R, ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖
      ≤ (4 : ℝ) ^ (3 / 4 : ℝ) * R ^ (5 / 2 : ℝ)
        * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ) := by
  have hR0 : (0 : ℝ) ≤ R := hR.le
  have hAint : Integrable (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ 4) volume := by
    have hcs : HasCompactSupport (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ 4) :=
      (hc.fderiv ℝ).mono (by
        intro x hx
        simp only [Function.mem_support] at hx ⊢
        intro h0
        exact hx (by rw [h0]; norm_num))
    exact ((hv.continuous_fderiv (by norm_num)).norm.pow 4).integrable_of_hasCompactSupport hcs
  obtain ⟨M, hM⟩ :=
    (hc.fderiv ℝ).exists_bound_of_continuous (hv.continuous_fderiv (by norm_num))
  have hvol : volume (Metric.ball (0 : ℝ × ℝ) R) = ENNReal.ofReal (4 * R ^ 2) :=
    vol_ball_prod (0 : ℝ × ℝ) hR0
  have hvol_lt : volume (Metric.ball (0 : ℝ × ℝ) R) < ⊤ := by
    rw [hvol]; exact ENNReal.ofReal_lt_top
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : ℝ × ℝ) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hvol_lt⟩
  have hfncont : Continuous (fun ξ : ℝ × ℝ => ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖) :=
    continuous_norm.mul
      (((hv.continuous_fderiv (by norm_num)).norm).comp (continuous_const.add continuous_id))
  have hMemLp : MemLp (fun ξ : ℝ × ℝ => ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖) 4
      (volume.restrict (Metric.ball (0 : ℝ × ℝ) R)) := by
    refine MemLp.of_bound hfncont.aestronglyMeasurable (R * max M 0) ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with ξ hξ
    rw [Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul ?_ ((hM (p + ξ)).trans (le_max_left M 0)) (norm_nonneg _) hR0
    have h2 : ‖ξ‖ < R := by
      simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hξ
    exact h2.le
  have hHolder := Morrey2D.integral_abs_le_L4_mul_vol
    (s := Metric.ball (0 : ℝ × ℝ) R)
    (f := fun ξ : ℝ × ℝ => ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖) hvol_lt hMemLp
  have hL : (∫ x in Metric.ball (0 : ℝ × ℝ) R,
        |(fun ξ : ℝ × ℝ => ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖) x|)
      = ∫ ξ in Metric.ball (0 : ℝ × ℝ) R, ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖ := by
    refine setIntegral_congr_fun measurableSet_ball (fun ξ _ => ?_)
    exact abs_of_nonneg (by positivity)
  have hR4 : (∫ x in Metric.ball (0 : ℝ × ℝ) R,
        |(fun ξ : ℝ × ℝ => ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖) x| ^ 4)
      ≤ R ^ 4 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) := by
    have habs : ∀ x : ℝ × ℝ,
        |(fun ξ : ℝ × ℝ => ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖) x| ^ 4
          = (‖x‖ * ‖fderiv ℝ v (p + x)‖) ^ 4 := by
      intro x
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs, ← pow_mul]
    rw [setIntegral_congr_fun measurableSet_ball (fun x _ => habs x)]
    have hpt : ∀ x ∈ Metric.ball (0 : ℝ × ℝ) R,
        (‖x‖ * ‖fderiv ℝ v (p + x)‖) ^ 4 ≤ R ^ 4 * ‖fderiv ℝ v (p + x)‖ ^ 4 := by
      intro x hx
      have h1 : ‖x‖ ≤ R := by
        have h2 : ‖x‖ < R := by
          simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hx
        exact h2.le
      have h2 : ‖x‖ ^ 4 ≤ R ^ 4 := pow_le_pow_left₀ (norm_nonneg x) h1 4
      calc (‖x‖ * ‖fderiv ℝ v (p + x)‖) ^ 4
          = ‖x‖ ^ 4 * ‖fderiv ℝ v (p + x)‖ ^ 4 := mul_pow _ _ 4
        _ ≤ R ^ 4 * ‖fderiv ℝ v (p + x)‖ ^ 4 := by gcongr
    have hcont1 : Continuous (fun x : ℝ × ℝ => (‖x‖ * ‖fderiv ℝ v (p + x)‖) ^ 4) :=
      hfncont.pow 4
    have hcont2 : Continuous (fun x : ℝ × ℝ => R ^ 4 * ‖fderiv ℝ v (p + x)‖ ^ 4) :=
      continuous_const.mul ((((hv.continuous_fderiv (by norm_num)).norm).comp
        (continuous_const.add continuous_id)).pow 4)
    calc ∫ x in Metric.ball (0 : ℝ × ℝ) R, (‖x‖ * ‖fderiv ℝ v (p + x)‖) ^ 4
        ≤ ∫ x in Metric.ball (0 : ℝ × ℝ) R, R ^ 4 * ‖fderiv ℝ v (p + x)‖ ^ 4 :=
          setIntegral_mono_on (legOne_integrableOn_ball_of_continuous hcont1 0 R)
            (legOne_integrableOn_ball_of_continuous hcont2 0 R) measurableSet_ball hpt
      _ = R ^ 4 * ∫ x in Metric.ball (0 : ℝ × ℝ) R, ‖fderiv ℝ v (p + x)‖ ^ 4 :=
          integral_const_mul _ _
      _ ≤ R ^ 4 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hshift : ∫ x in Metric.ball (0 : ℝ × ℝ) R, ‖fderiv ℝ v (p + x)‖ ^ 4
              = ∫ w in Metric.ball p R, ‖fderiv ℝ v w‖ ^ 4 := by
            have h := Morrey2D.setIntegral_comp_smul_add_ball
              (f := fun w : ℝ × ℝ => ‖fderiv ℝ v w‖ ^ 4) (a := R) (t := 1)
              (by norm_num : (0 : ℝ) < 1) p
            simpa using h
          rw [hshift]
          exact setIntegral_le_integral hAint (ae_of_all _ (fun w => by positivity))
  rw [hL] at hHolder
  have hHolder' : ∫ ξ in Metric.ball (0 : ℝ × ℝ) R, ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖
      ≤ (4 * R ^ 2) ^ (3 / 4 : ℝ)
        * (R ^ 4 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4)) ^ (1 / 4 : ℝ) := by
    rw [← Measure.real_def, legOne_ball_volume_real (0 : ℝ × ℝ) hR0] at hHolder
    refine hHolder.trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hR4 (by norm_num))
      (Real.rpow_nonneg (by positivity) _)
  refine hHolder'.trans (le_of_eq ?_)
  exact legOne_rpow_arith hR (integral_nonneg (fun x => by positivity))

/-- The main inequality after the `t`-integration. -/
private lemma legOne_main {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v)
    (hseg : ∀ p z : ℝ × ℝ, v z - v p = ∫ t in (0 : ℝ)..1,
      (fderiv ℝ v (p + t • (z - p))) (z - p)) (p : ℝ × ℝ) {a : ℝ} (ha : 0 < a) :
    ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, |v p - v (p + ζ)|
      ≤ 2 * ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ)
        * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)) := by
  have hpt : ∀ ζ : ℝ × ℝ,
      |v p - v (p + ζ)| ≤ ∫ t in (0 : ℝ)..1, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖ := by
    intro ζ
    have h := legOne_abs_sub_le_integral_fderiv hv (hseg p (p + ζ))
    rw [abs_sub_comm] at h
    simpa [add_sub_cancel_left, mul_comm] using h
  have hjoint : Integrable
      (Function.uncurry fun (t : ℝ) (ζ : ℝ × ℝ) => ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume.restrict (Metric.ball (0 : ℝ × ℝ) a))) := by
    have hcont : Continuous (Function.uncurry
        fun (t : ℝ) (ζ : ℝ × ℝ) => ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖) := by
      show Continuous fun q : ℝ × (ℝ × ℝ) => ‖q.2‖ * ‖fderiv ℝ v (p + q.1 • q.2)‖
      refine continuous_norm.comp continuous_snd |>.mul ?_
      exact (((hv.continuous_fderiv (by norm_num)).norm).comp
        (continuous_const.add (continuous_fst.smul continuous_snd)))
    have hIntOn : IntegrableOn
        (Function.uncurry fun (t : ℝ) (ζ : ℝ × ℝ) => ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖)
        (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : ℝ × ℝ) a) volume :=
      ContinuousOn.integrableOn_compact
        (isCompact_Icc.prod (isCompact_closedBall (0 : ℝ × ℝ) a)) hcont.continuousOn
    have hIntOn' : IntegrableOn
        (Function.uncurry fun (t : ℝ) (ζ : ℝ × ℝ) => ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖)
        (Set.Ioc (0 : ℝ) 1 ×ˢ Metric.ball (0 : ℝ × ℝ) a) volume :=
      hIntOn.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Metric.ball_subset_closedBall)
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hIntOn'
  have hInner : IntegrableOn (fun ζ : ℝ × ℝ =>
      ∫ t in (0 : ℝ)..1, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖) (Metric.ball (0 : ℝ × ℝ) a) volume := by
    have h1 : Integrable (fun ζ : ℝ × ℝ =>
        ∫ t, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
        (volume.restrict (Metric.ball (0 : ℝ × ℝ) a)) := hjoint.integral_prod_right
    refine h1.congr ?_
    filter_upwards with ζ
    exact (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm
  have hleft : IntegrableOn (fun ζ : ℝ × ℝ => |v p - v (p + ζ)|)
      (Metric.ball (0 : ℝ × ℝ) a) volume := by
    refine legOne_integrableOn_ball_of_continuous ?_ 0 a
    have h1 : Continuous (fun ζ : ℝ × ℝ => v p - v (p + ζ)) :=
      continuous_const.sub (hv.continuous.comp (continuous_const.add continuous_id))
    simpa only [Real.norm_eq_abs] using h1.norm
  have hB : ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, |v p - v (p + ζ)|
      ≤ ∫ ζ in Metric.ball (0 : ℝ × ℝ) a,
          ∫ t in (0 : ℝ)..1, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖ :=
    setIntegral_mono_on hleft hInner measurableSet_ball (fun ζ _ => hpt ζ)
  have hIocEq : ∫ ζ in Metric.ball (0 : ℝ × ℝ) a,
        (∫ t in (0 : ℝ)..1, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖)
      = ∫ ζ in Metric.ball (0 : ℝ × ℝ) a,
          ∫ t in Set.Ioc (0 : ℝ) 1, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖ :=
    setIntegral_congr_fun measurableSet_ball
      (fun ζ _ => intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1))
  have hswap : ∫ ζ in Metric.ball (0 : ℝ × ℝ) a,
        ∫ t in Set.Ioc (0 : ℝ) 1, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖
      = ∫ t in Set.Ioc (0 : ℝ) 1,
          ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖ :=
    (integral_integral_swap hjoint).symm
  have hC : ∫ t in Set.Ioc (0 : ℝ) 1,
        (∫ ζ in Metric.ball (0 : ℝ × ℝ) a, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖)
      = ∫ t in Set.Ioc (0 : ℝ) 1, (t ^ 3)⁻¹ *
          (∫ ξ in Metric.ball (0 : ℝ × ℝ) (t * a), ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖) :=
    setIntegral_congr_fun measurableSet_Ioc (fun t ht => legOne_smul_subst p ht.1)
  have hD : ∫ t in Set.Ioc (0 : ℝ) 1, (t ^ 3)⁻¹ *
        (∫ ξ in Metric.ball (0 : ℝ × ℝ) (t * a), ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖)
      ≤ ∫ t in Set.Ioc (0 : ℝ) 1,
          ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ)
            * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)) * t ^ (-(1 / 2) : ℝ) := by
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      exact mul_nonneg (inv_nonneg.mpr (by positivity))
        (setIntegral_nonneg measurableSet_ball (fun ξ _ => by positivity))
    · have hrp : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) volume 0 1 :=
        intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))
      exact hrp.1.const_mul _
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      calc (t ^ 3)⁻¹ *
            (∫ ξ in Metric.ball (0 : ℝ × ℝ) (t * a), ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖)
          ≤ (t ^ 3)⁻¹ * ((4 : ℝ) ^ (3 / 4 : ℝ) * (t * a) ^ (5 / 2 : ℝ)
              * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left (legOne_ball_L4_bound hv hc p (by positivity))
              (by positivity)
        _ = ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ)
              * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)) * t ^ (-(1 / 2) : ℝ) :=
            legOne_t_scale_arith ha ht0
  have hrpow : ∫ t in Set.Ioc (0 : ℝ) 1, t ^ (-(1 / 2) : ℝ) = 2 := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2)))]
    norm_num [Real.zero_rpow]
  have hE : ∫ t in Set.Ioc (0 : ℝ) 1,
        ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ)
          * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)) * t ^ (-(1 / 2) : ℝ)
      = ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ)
          * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)) * 2 := by
    rw [integral_const_mul, hrpow]
  calc ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, |v p - v (p + ζ)|
      ≤ ∫ ζ in Metric.ball (0 : ℝ × ℝ) a,
          ∫ t in (0 : ℝ)..1, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖ := hB
    _ = ∫ ζ in Metric.ball (0 : ℝ × ℝ) a,
          ∫ t in Set.Ioc (0 : ℝ) 1, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖ := hIocEq
    _ = ∫ t in Set.Ioc (0 : ℝ) 1,
          ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, ‖ζ‖ * ‖fderiv ℝ v (p + t • ζ)‖ := hswap
    _ = ∫ t in Set.Ioc (0 : ℝ) 1, (t ^ 3)⁻¹ *
          (∫ ξ in Metric.ball (0 : ℝ × ℝ) (t * a), ‖ξ‖ * ‖fderiv ℝ v (p + ξ)‖) := hC
    _ ≤ ∫ t in Set.Ioc (0 : ℝ) 1,
          ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ)
            * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)) * t ^ (-(1 / 2) : ℝ) := hD
    _ = ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ)
          * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)) * 2 := hE
    _ = 2 * ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ)
          * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)) := by ring

/-- **First leg of the 2-D Morrey estimate.**  Averaging the segment identity over the ball
`B(0,a)` (a square of volume `4a²` in the product norm on `ℝ × ℝ`) gives
`⨍_{ζ ∈ B(0,a)} |v p - v (p+ζ)| ≤ √2 (∫ ‖∇v‖⁴)^{1/4} √a`.
Proof route: segment bound `|v(p+ζ) - v p| ≤ ‖ζ‖ ∫_0^1 ‖∇v(p+tζ)‖ dt`; Fubini in `(ζ,t)`;
substitution `ξ = t ζ` (`MeasureTheory.Measure.setIntegral_comp_smul` + `smul_ball`, using
`Module.finrank ℝ (ℝ × ℝ) = 2`); Hölder `(4, 4/3)` on each ball `B(0,ta)` of volume `4t²a²`;
finally `∫_0^1 t^{-1/2} dt = 2`. -/
theorem leg_one_bound {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v)
    (hseg : ∀ p z : ℝ × ℝ, v z - v p = ∫ t in (0 : ℝ)..1, (fderiv ℝ v (p + t • (z - p))) (z - p))
    (p : ℝ × ℝ) {a : ℝ} (ha : 0 < a) :
    (1 / (4 * a ^ 2)) * ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, |v p - v (p + ζ)|
      ≤ Real.sqrt 2 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ) * Real.sqrt a := by
  calc (1 / (4 * a ^ 2)) * ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, |v p - v (p + ζ)|
      ≤ (1 / (4 * a ^ 2)) * (2 * ((4 : ℝ) ^ (3 / 4 : ℝ) * a ^ (5 / 2 : ℝ)
          * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left (legOne_main hv hc hseg p ha) (by positivity)
    _ = Real.sqrt 2 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ) * Real.sqrt a :=
        legOne_final_arith ha

end Work.FTS.StrongLWP.Sobolev.HolderHalf
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.leg_two_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory
open Work.FTS.StrongLWP.Sobolev.HolderHalf.Morrey2D

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf

-- the skeleton carried this `namespace` line twice; it is kept so that the literal name
-- `...HolderHalf.Work.FTS.StrongLWP.Sobolev.HolderHalf.leg_two_bound` also exists
set_option linter.dupNamespace false

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf

private lemma hasCompactSupport_norm_fderiv {v : ℝ × ℝ → ℝ} (hc : HasCompactSupport v) :
    HasCompactSupport (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖) :=
  (HasCompactSupport.fderiv ℝ hc).comp_left (g := fun L : ℝ × ℝ →L[ℝ] ℝ => ‖L‖) (by simp)

/-- `∫_0^1 t^{-1/2} dt = 2`, the `s`-integral of the two-leg Morrey estimate. -/
private lemma integral_rpow_neg_half : ∫ t in (0 : ℝ)..1, t ^ (-1 / 2 : ℝ) = 2 := by
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))]
  norm_num

private lemma integrable_norm_fderiv_pow4 {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v)
    (hc : HasCompactSupport v) :
    Integrable (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ 4) := by
  have hcont : Continuous (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ 4) :=
    (hv.continuous_fderiv (by norm_num)).norm.pow 4
  have hcs : HasCompactSupport (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ 4) :=
    (HasCompactSupport.fderiv ℝ hc).comp_left
      (g := fun L : ℝ × ℝ →L[ℝ] ℝ => ‖L‖ ^ 4) (by simp)
  exact hcont.integrable_of_hasCompactSupport hcs

/-- **Second leg of the 2-D Morrey estimate.**  Averaging the segment identity (from `p+ζ` to `q`)
over the ball `B(0,a)` gives
`⨍_{ζ ∈ B(0,a)} |v (p+ζ) - v q| ≤ √2 (∫ ‖∇v‖⁴)^{1/4} (a + dist p q)/√a`.
Proof route: `‖(p+ζ) - q‖ ≤ a + dist p q`; Fubini in `(ζ,s)`; substitution `w = q + s((p+ζ)-q)`;
Hölder `(4, 4/3)` on each ball `B(q+s(p-q), sa)` of volume `4s²a²`; finally
`∫_0^1 s^{-1/2} ds = 2`. -/
theorem leg_two_bound {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v)
    (hseg : ∀ p z : ℝ × ℝ, v z - v p = ∫ t in (0 : ℝ)..1, (fderiv ℝ v (p + t • (z - p))) (z - p))
    (p q : ℝ × ℝ) {a : ℝ} (ha : 0 < a) :
    (1 / (4 * a ^ 2)) * ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, |v (p + ζ) - v q|
      ≤ Real.sqrt 2 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)
        * ((a + dist p q) / Real.sqrt a) := by
  have hfderiv : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by norm_num)
  have hcsn : HasCompactSupport (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖) :=
    hasCompactSupport_norm_fderiv hc
  have hint4 : Integrable (fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ 4) :=
    integrable_norm_fderiv_pow4 hv hc
  set d : ℝ := dist p q with hd
  set G4 : ℝ := ∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4 with hG4
  have hd0 : 0 ≤ d := by rw [hd]; exact dist_nonneg
  have hG40 : 0 ≤ G4 := by
    rw [hG4]
    exact integral_nonneg fun x => by positivity
  set B : Set (ℝ × ℝ) := Metric.ball (0 : ℝ × ℝ) a with hB
  set Λ : (ℝ × ℝ) → ℝ → ℝ := fun ζ t => ‖fderiv ℝ v (q + t • ((p + ζ) - q))‖ with hΛ
  have hΛcont : Continuous (Function.uncurry Λ) := by
    have hun : Function.uncurry Λ
        = fun x : (ℝ × ℝ) × ℝ => ‖fderiv ℝ v (q + x.2 • ((p + x.1) - q))‖ := by
      rw [hΛ]; rfl
    rw [hun]
    have h1 : Continuous fun x : (ℝ × ℝ) × ℝ => x.2 • ((p + x.1) - q) :=
      continuous_snd.smul ((continuous_const.add continuous_fst).sub continuous_const)
    have h2 : Continuous fun x : (ℝ × ℝ) × ℝ => q + x.2 • ((p + x.1) - q) :=
      continuous_const.add h1
    exact (hfderiv.comp h2).norm
  have hmble : MeasurableSet B := by rw [hB]; exact Metric.isOpen_ball.measurableSet
  -- Step 1: pointwise segment bound
  have hpt : ∀ ζ ∈ B, |v (p + ζ) - v q| ≤ (a + d) * ∫ t in (0 : ℝ)..1, Λ ζ t := by
    intro ζ hζ
    have hζlt : ‖ζ‖ < a := by
      have h := hζ
      rw [hB, Metric.mem_ball, dist_zero_right] at h
      exact h
    have hzq : ‖(p + ζ) - q‖ ≤ a + d := by
      have h1 : (p + ζ) - q = (p - q) + ζ := by abel
      calc ‖(p + ζ) - q‖ = ‖(p - q) + ζ‖ := by rw [h1]
        _ ≤ ‖p - q‖ + ‖ζ‖ := norm_add_le _ _
        _ = d + ‖ζ‖ := by rw [hd, dist_eq_norm]
        _ ≤ d + a := by linarith
        _ = a + d := by ring
    have hnn : 0 ≤ ∫ t in (0 : ℝ)..1, Λ ζ t := by
      refine intervalIntegral.integral_nonneg (by norm_num) ?_
      intro t ht
      rw [hΛ]
      positivity
    calc |v (p + ζ) - v q| ≤ ‖(p + ζ) - q‖ * ∫ t in (0 : ℝ)..1, Λ ζ t := by
          rw [hΛ]
          exact abs_sub_le_mul_integral_norm_fderiv hv hseg q (p + ζ)
      _ ≤ (a + d) * ∫ t in (0 : ℝ)..1, Λ ζ t := mul_le_mul_of_nonneg_right hzq hnn
  -- integrability of both sides on the ball
  have hleft_int : IntegrableOn (fun ζ : ℝ × ℝ => |v (p + ζ) - v q|) B := by
    have hcont : Continuous fun ζ : ℝ × ℝ => |v (p + ζ) - v q| :=
      ((hv.continuous.comp (continuous_const.add continuous_id)).sub continuous_const).abs
    rw [hB]
    exact (hcont.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℝ × ℝ) a)).mono_set
      Metric.ball_subset_closedBall
  have hright_int : IntegrableOn (fun ζ : ℝ × ℝ => (a + d) * ∫ t in (0 : ℝ)..1, Λ ζ t) B := by
    have hcont : Continuous fun ζ : ℝ × ℝ => (a + d) * ∫ t in (0 : ℝ)..1, Λ ζ t :=
      continuous_const.mul
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hΛcont 0 1)
    rw [hB]
    exact (hcont.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℝ × ℝ) a)).mono_set
      Metric.ball_subset_closedBall
  have hstep1 : ∫ ζ in B, |v (p + ζ) - v q|
      ≤ ∫ ζ in B, (a + d) * ∫ t in (0 : ℝ)..1, Λ ζ t :=
    setIntegral_mono_on hleft_int hright_int hmble hpt
  have hstep2 : ∫ ζ in B, (a + d) * ∫ t in (0 : ℝ)..1, Λ ζ t
      = (a + d) * ∫ ζ in B, (∫ t in (0 : ℝ)..1, Λ ζ t) := by
    rw [integral_const_mul]
  have hstep3 : ∫ ζ in B, (∫ t in (0 : ℝ)..1, Λ ζ t)
      = ∫ t in (0 : ℝ)..1, ∫ ζ in B, Λ ζ t := by
    rw [hB]
    exact integral_ball_integral_swap hΛcont ha
  -- Step 2: the per-t bound
  have hkey : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∫ ζ in B, Λ ζ t ≤ (4 * a ^ 2) ^ (3 / 4 : ℝ) * t ^ (-1 / 2 : ℝ) * G4 ^ (1 / 4 : ℝ) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    set c : ℝ × ℝ := q + t • (p - q) with hc
    have hArg : ∀ y : ℝ × ℝ, c + t • y = q + t • ((p + y) - q) := by
      intro y
      rw [hc]
      simp only [smul_sub, smul_add]
      abel
    have hsub : ∫ y in Metric.ball (0 : ℝ × ℝ) a, ‖fderiv ℝ v (c + t • y)‖
        = (t ^ 2)⁻¹ * ∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖ := by
      simpa only using setIntegral_comp_smul_add_ball (fun w : ℝ × ℝ => ‖fderiv ℝ v w‖) ht0 c
    have hlhs : ∫ ζ in B, Λ ζ t = (t ^ 2)⁻¹ * ∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖ := by
      rw [hB, hΛ]
      have h1 : (∫ y in Metric.ball (0 : ℝ × ℝ) a, ‖fderiv ℝ v (q + t • ((p + y) - q))‖)
          = ∫ y in Metric.ball (0 : ℝ × ℝ) a, ‖fderiv ℝ v (c + t • y)‖ := by
        apply setIntegral_congr_fun measurableSet_ball
        intro y hy
        show ‖fderiv ℝ v (q + t • ((p + y) - q))‖ = ‖fderiv ℝ v (c + t • y)‖
        rw [hArg y]
      rw [h1]
      exact hsub
    -- Hölder on the ball `ball c (t*a)`
    have hvol : (volume (Metric.ball c (t * a))).toReal = 4 * (t * a) ^ 2 := by
      rw [vol_ball_prod c (by positivity), ENNReal.toReal_ofReal (by positivity)]
    have hlt : volume (Metric.ball c (t * a)) < ⊤ := by
      rw [vol_ball_prod c (by positivity)]
      exact ENNReal.ofReal_lt_top
    have hmem : MemLp (fun w : ℝ × ℝ => ‖fderiv ℝ v w‖) 4
        (volume.restrict (Metric.ball c (t * a))) :=
      (hfderiv.norm.memLp_of_hasCompactSupport hcsn).restrict _
    have hholder := integral_abs_le_L4_mul_vol hlt hmem
    have habs4 : (∫ w in Metric.ball c (t * a), |‖fderiv ℝ v w‖| ^ 4)
        = ∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖ ^ 4 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro w hw
      show |‖fderiv ℝ v w‖| ^ 4 = ‖fderiv ℝ v w‖ ^ 4
      rw [abs_of_nonneg (norm_nonneg _)]
    have hholder' : ∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖
        ≤ (volume (Metric.ball c (t * a))).toReal ^ (3 / 4 : ℝ)
          * (∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖ ^ 4) ^ (1 / 4 : ℝ) := by
      calc ∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖
          = ∫ w in Metric.ball c (t * a), |‖fderiv ℝ v w‖| := by
            apply setIntegral_congr_fun measurableSet_ball
            intro w hw
            show ‖fderiv ℝ v w‖ = |‖fderiv ℝ v w‖|
            rw [abs_of_nonneg (norm_nonneg _)]
        _ ≤ (volume (Metric.ball c (t * a))).toReal ^ (3 / 4 : ℝ)
              * (∫ w in Metric.ball c (t * a), |‖fderiv ℝ v w‖| ^ 4) ^ (1 / 4 : ℝ) := hholder
        _ = (volume (Metric.ball c (t * a))).toReal ^ (3 / 4 : ℝ)
              * (∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖ ^ 4) ^ (1 / 4 : ℝ) := by
              rw [habs4]
    have h4le : (∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖ ^ 4) ≤ G4 := by
      have h := setIntegral_le_integral (μ := volume) (s := Metric.ball c (t * a))
        (f := fun x : ℝ × ℝ => ‖fderiv ℝ v x‖ ^ 4) hint4
        (Filter.Eventually.of_forall fun x => by positivity)
      rw [hG4]
      exact h
    calc ∫ ζ in B, Λ ζ t
        = (t ^ 2)⁻¹ * ∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖ := hlhs
      _ ≤ (t ^ 2)⁻¹ * ((volume (Metric.ball c (t * a))).toReal ^ (3 / 4 : ℝ)
            * (∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖ ^ 4) ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hholder' (by positivity)
      _ = (t ^ 2)⁻¹ * ((4 * (t * a) ^ 2) ^ (3 / 4 : ℝ)
            * (∫ w in Metric.ball c (t * a), ‖fderiv ℝ v w‖ ^ 4) ^ (1 / 4 : ℝ)) := by
          rw [hvol]
      _ ≤ (t ^ 2)⁻¹ * ((4 * (t * a) ^ 2) ^ (3 / 4 : ℝ) * G4 ^ (1 / 4 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow (by positivity) h4le (by norm_num)
      _ = (4 * a ^ 2) ^ (3 / 4 : ℝ) * t ^ (-1 / 2 : ℝ) * G4 ^ (1 / 4 : ℝ) := by
          rw [← mul_assoc, rpow_scale_identity ha ht0]
  -- Step 3: integrate the per-t bound
  have h7 : ∫ t in (0 : ℝ)..1, ∫ ζ in B, Λ ζ t
      ≤ (4 * a ^ 2) ^ (3 / 4 : ℝ) * G4 ^ (1 / 4 : ℝ) * 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hrpow : IntegrableOn (fun t : ℝ => t ^ (-1 / 2 : ℝ)) (Set.Ioc (0 : ℝ) 1) volume := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -1 / 2)
    have hgint : Integrable (fun t : ℝ =>
        (4 * a ^ 2) ^ (3 / 4 : ℝ) * t ^ (-1 / 2 : ℝ) * G4 ^ (1 / 4 : ℝ))
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      Integrable.mul_const (Integrable.const_mul hrpow ((4 * a ^ 2) ^ (3 / 4 : ℝ)))
        (G4 ^ (1 / 4 : ℝ))
    have hmono := integral_mono_of_nonneg
      (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
      (f := fun t : ℝ => ∫ ζ in B, Λ ζ t)
      (g := fun t : ℝ => (4 * a ^ 2) ^ (3 / 4 : ℝ) * t ^ (-1 / 2 : ℝ) * G4 ^ (1 / 4 : ℝ))
      (Filter.Eventually.of_forall fun t => integral_nonneg fun ζ => by rw [hΛ]; positivity)
      hgint
      ((ae_restrict_mem measurableSet_Ioc).mono (fun t ht => hkey t ht))
    refine hmono.trans (le_of_eq ?_)
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      integral_rpow_neg_half]
    ring
  -- Step 4: assembly
  have hmain : ∫ ζ in B, |v (p + ζ) - v q|
      ≤ (a + d) * (2 * (4 * a ^ 2) ^ (3 / 4 : ℝ) * G4 ^ (1 / 4 : ℝ)) := by
    calc ∫ ζ in B, |v (p + ζ) - v q|
        ≤ ∫ ζ in B, (a + d) * ∫ t in (0 : ℝ)..1, Λ ζ t := hstep1
      _ = (a + d) * ∫ ζ in B, (∫ t in (0 : ℝ)..1, Λ ζ t) := hstep2
      _ = (a + d) * ∫ t in (0 : ℝ)..1, ∫ ζ in B, Λ ζ t := by rw [hstep3]
      _ ≤ (a + d) * ((4 * a ^ 2) ^ (3 / 4 : ℝ) * G4 ^ (1 / 4 : ℝ) * 2) :=
          mul_le_mul_of_nonneg_left h7 (by positivity)
      _ = (a + d) * (2 * (4 * a ^ 2) ^ (3 / 4 : ℝ) * G4 ^ (1 / 4 : ℝ)) := by ring
  calc (1 / (4 * a ^ 2)) * ∫ ζ in B, |v (p + ζ) - v q|
      ≤ (1 / (4 * a ^ 2)) *
          ((a + d) * (2 * (4 * a ^ 2) ^ (3 / 4 : ℝ) * G4 ^ (1 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = Real.sqrt 2 * G4 ^ (1 / 4 : ℝ) * ((a + d) / Real.sqrt a) := arith_final ha

end Work.FTS.StrongLWP.Sobolev.HolderHalf

/-- The same statement under the name obtained when the (duplicated) `namespace` line of the
original skeleton is kept; it is a definitional copy of
`Work.FTS.StrongLWP.Sobolev.HolderHalf.leg_two_bound` and is provided only for compatibility. -/
theorem leg_two_bound {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v)
    (hseg : ∀ p z : ℝ × ℝ, v z - v p = ∫ t in (0 : ℝ)..1, (fderiv ℝ v (p + t • (z - p))) (z - p))
    (p q : ℝ × ℝ) {a : ℝ} (ha : 0 < a) :
    (1 / (4 * a ^ 2)) * ∫ ζ in Metric.ball (0 : ℝ × ℝ) a, |v (p + ζ) - v q|
      ≤ Real.sqrt 2 * (∫ x : ℝ × ℝ, ‖fderiv ℝ v x‖ ^ 4) ^ (1 / 4 : ℝ)
        * ((a + dist p q) / Real.sqrt a) :=
  _root_.Work.FTS.StrongLWP.Sobolev.HolderHalf.Work.FTS.StrongLWP.Sobolev.HolderHalf.leg_two_bound
    hv hc hseg p q ha

end Work.FTS.StrongLWP.Sobolev.HolderHalf
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.nash_2d =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf

open MeasureTheory

/-- Cauchy–Schwarz for the product of two square roots, in the form needed below:
`∫ √A √B ≤ √(∫A) √(∫B)` for nonnegative `A B`, together with integrability of `√A √B`. -/
lemma cs_sqrt {A B : ℝ → ℝ} (hA : Integrable A) (hB : Integrable B)
    (hAn : ∀ t, 0 ≤ A t) (hBn : ∀ t, 0 ≤ B t) :
    Integrable (fun t => Real.sqrt (A t) * Real.sqrt (B t)) ∧
    ∫ t, Real.sqrt (A t) * Real.sqrt (B t) ≤ Real.sqrt (∫ t, A t) * Real.sqrt (∫ t, B t) := by
  refine ⟨Work.Coercivity.integrable_sqrt_mul_sqrt volume A B hA hB hAn hBn, ?_⟩
  have habs := Work.Blocks.IMC.cs_integral_mul_le (mu := volume)
    (f := fun t => Real.sqrt (A t)) (g := fun t => Real.sqrt (B t))
    (Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable)
    (Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable)
    (hA.congr (Filter.Eventually.of_forall fun t => (Real.sq_sqrt (hAn t)).symm))
    (hB.congr (Filter.Eventually.of_forall fun t => (Real.sq_sqrt (hBn t)).symm))
  have hAsq : (∫ t, (Real.sqrt (A t)) ^ 2) = ∫ t, A t :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => Real.sq_sqrt (hAn t))
  have hBsq : (∫ t, (Real.sqrt (B t)) ^ 2) = ∫ t, B t :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => Real.sq_sqrt (hBn t))
  have hnn : 0 ≤ ∫ t, Real.sqrt (A t) * Real.sqrt (B t) :=
    MeasureTheory.integral_nonneg fun t => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [hAsq, hBsq, abs_of_nonneg hnn] at habs
  exact habs

/-- Derivative of the second-coordinate slice equals the `(0,1)` partial derivative. -/
lemma deriv_snd {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u) (s t : ℝ) :
    deriv (fun r : ℝ => u (s, r)) t = fderiv ℝ u (s, t) (0, 1) := by
  have hd : DifferentiableAt ℝ u (s, t) :=
    (hu.differentiable (by norm_num)).differentiableAt
  have hφ : HasFDerivAt (fun r : ℝ => (s, r)) (ContinuousLinearMap.inr ℝ ℝ ℝ) t :=
    hasFDerivAt_prodMk_right s t
  have hcomp : HasDerivAt (fun r : ℝ => u (s, r))
      (fderiv ℝ u (s, t) (ContinuousLinearMap.inr ℝ ℝ ℝ 1)) t :=
    (hd.hasFDerivAt.comp t hφ).hasDerivAt
  rw [hcomp.deriv, ContinuousLinearMap.inr_apply]

set_option maxHeartbeats 1000000 in
/-- Two-dimensional Nash inequality: for `u : ℝ² → ℝ` of class `C¹` with compact support,
`∫ u⁴ ≤ 4 (∫ u²) (∫ ‖∇u‖²)`, deduced from the one-dimensional Agmon/Nash inequality `h1d`
applied to the slices in both coordinate directions. -/
theorem nash_2d {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u)
    (h1d : ∀ (f : ℝ → ℝ), ContDiff ℝ 1 f → HasCompactSupport f →
      ∀ y : ℝ, (f y) ^ 2 ≤ 2 * Real.sqrt (∫ x : ℝ, (f x) ^ 2) * Real.sqrt (∫ x : ℝ, (deriv f x) ^ 2)) :
    ∫ x : ℝ × ℝ, (u x) ^ 4 ≤ 4 * (∫ x : ℝ × ℝ, (u x) ^ 2) * (∫ x : ℝ × ℝ, ‖fderiv ℝ u x‖ ^ 2) := by
  obtain ⟨hctA, hctB, hcsA, hcsB, hderiv, hbdA, hbdB⟩ :=
    NashData.slice_facts hu hc
  obtain ⟨hI2, hI4, hIfd, hIt2, hIs2, hItf, hIsf, hTeq1, hTeq2, hTle1, hTle2⟩ :=
    NashData.integrable_facts hu hc
  let A : ℝ → ℝ := fun t => ∫ s : ℝ, (u (s, t)) ^ 2
  let B : ℝ → ℝ := fun t => ∫ s : ℝ, (deriv (fun r : ℝ => u (r, t)) s) ^ 2
  let C : ℝ → ℝ := fun s => ∫ t : ℝ, (u (s, t)) ^ 2
  let D : ℝ → ℝ := fun s => ∫ t : ℝ, (deriv (fun r : ℝ => u (s, r)) t) ^ 2
  -- integrability of the four slice-integral functions
  have hAint : Integrable A := hIt2
  have hBint : Integrable B := by
    refine hItf.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [B]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => by simp only [hderiv])
  have hCint : Integrable C := hIs2
  have hDint : Integrable D := by
    refine hIsf.congr (Filter.Eventually.of_forall fun s => ?_)
    simp only [D]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => by
      simp only [deriv_snd hu s t])
  -- nonnegativity
  have hAnn : ∀ t, 0 ≤ A t := fun t => by
    simp only [A]
    exact MeasureTheory.integral_nonneg fun s => sq_nonneg _
  have hBnn : ∀ t, 0 ≤ B t := fun t => by
    simp only [B]
    exact MeasureTheory.integral_nonneg fun s => sq_nonneg _
  have hCnn : ∀ s, 0 ≤ C s := fun s => by
    simp only [C]
    exact MeasureTheory.integral_nonneg fun t => sq_nonneg _
  have hDnn : ∀ s, 0 ≤ D s := fun s => by
    simp only [D]
    exact MeasureTheory.integral_nonneg fun t => sq_nonneg _
  -- the scalar identities and bounds
  have hAeq : (∫ t : ℝ, A t) = ∫ p : ℝ × ℝ, (u p) ^ 2 := by
    simp only [A]; exact hTeq1
  have hCeq : (∫ s : ℝ, C s) = ∫ p : ℝ × ℝ, (u p) ^ 2 := by
    simp only [C]; exact hTeq2
  have hBle : (∫ t : ℝ, B t) ≤ ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 := by
    have h1 : (∫ t : ℝ, B t) = ∫ t : ℝ, ∫ s : ℝ, (fderiv ℝ u (s, t) (1, 0)) ^ 2 := by
      simp only [B]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t =>
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => by simp only [hderiv]))
    rw [h1]; exact hTle1
  have hDle : (∫ s : ℝ, D s) ≤ ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 := by
    have h1 : (∫ s : ℝ, D s) = ∫ s : ℝ, ∫ t : ℝ, (fderiv ℝ u (s, t) (0, 1)) ^ 2 := by
      simp only [D]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s =>
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => by
          simp only [deriv_snd hu s t]))
    rw [h1]; exact hTle2
  have hQ0nn : 0 ≤ ∫ p : ℝ × ℝ, (u p) ^ 2 :=
    MeasureTheory.integral_nonneg fun p => sq_nonneg _
  have hQ1nn : 0 ≤ ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 :=
    MeasureTheory.integral_nonneg fun p => sq_nonneg _
  -- pointwise Agmon bounds, in the two coordinate directions
  have keyA : ∀ s t : ℝ, (u (s, t)) ^ 2 ≤ 2 * Real.sqrt (A t) * Real.sqrt (B t) := by
    intro s t
    have h := h1d (fun r : ℝ => u (r, t)) (hctA t) (hcsA t) s
    simpa only [A, B] using h
  have keyC : ∀ s t : ℝ, (u (s, t)) ^ 2 ≤ 2 * Real.sqrt (C s) * Real.sqrt (D s) := by
    intro s t
    have h := h1d (fun r : ℝ => u (s, r)) (hctB s) (hcsB s) t
    simpa only [C, D] using h
  have keypt : ∀ p : ℝ × ℝ, (u p) ^ 4 ≤
      4 * (Real.sqrt (A p.2) * Real.sqrt (B p.2)) *
        (Real.sqrt (C p.1) * Real.sqrt (D p.1)) := by
    rintro ⟨s, t⟩
    have h1 := keyA s t
    have h2 := keyC s t
    have h3 : (u (s, t)) ^ 2 * (u (s, t)) ^ 2 ≤
        (2 * Real.sqrt (A t) * Real.sqrt (B t)) *
          (2 * Real.sqrt (C s) * Real.sqrt (D s)) :=
      mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
    calc (u (s, t)) ^ 4 = (u (s, t)) ^ 2 * (u (s, t)) ^ 2 := by ring
      _ ≤ (2 * Real.sqrt (A t) * Real.sqrt (B t)) *
            (2 * Real.sqrt (C s) * Real.sqrt (D s)) := h3
      _ = 4 * (Real.sqrt (A t) * Real.sqrt (B t)) *
            (Real.sqrt (C s) * Real.sqrt (D s)) := by ring
  have hPint : Integrable (fun t : ℝ => Real.sqrt (A t) * Real.sqrt (B t)) :=
    (cs_sqrt hAint hBint hAnn hBnn).1
  have hQint : Integrable (fun s : ℝ => Real.sqrt (C s) * Real.sqrt (D s)) :=
    (cs_sqrt hCint hDint hCnn hDnn).1
  have hRHSint : Integrable (fun p : ℝ × ℝ =>
      4 * (Real.sqrt (A p.2) * Real.sqrt (B p.2)) *
        (Real.sqrt (C p.1) * Real.sqrt (D p.1))) := by
    refine (Integrable.mul_prod (hQint.const_mul 4) hPint).congr
      (Filter.Eventually.of_forall fun p => ?_)
    ring
  have hstep1 : ∫ p : ℝ × ℝ, (u p) ^ 4 ≤ ∫ p : ℝ × ℝ,
      4 * (Real.sqrt (A p.2) * Real.sqrt (B p.2)) *
        (Real.sqrt (C p.1) * Real.sqrt (D p.1)) := by
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => ?_)
      hRHSint (Filter.Eventually.of_forall keypt)
    positivity
  have hstep2 : ∫ p : ℝ × ℝ,
      4 * (Real.sqrt (A p.2) * Real.sqrt (B p.2)) *
        (Real.sqrt (C p.1) * Real.sqrt (D p.1))
      = 4 * (∫ t : ℝ, Real.sqrt (A t) * Real.sqrt (B t)) *
          (∫ s : ℝ, Real.sqrt (C s) * Real.sqrt (D s)) := by
    rw [show (∫ p : ℝ × ℝ,
        4 * (Real.sqrt (A p.2) * Real.sqrt (B p.2)) *
          (Real.sqrt (C p.1) * Real.sqrt (D p.1)))
        = ∫ p : ℝ × ℝ,
            (fun s : ℝ => 4 * (Real.sqrt (C s) * Real.sqrt (D s))) p.1 *
              (fun t : ℝ => Real.sqrt (A t) * Real.sqrt (B t)) p.2 from
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)]
    rw [Measure.volume_eq_prod ℝ ℝ,
      MeasureTheory.integral_prod_mul
        (f := fun s : ℝ => 4 * (Real.sqrt (C s) * Real.sqrt (D s)))
        (g := fun t : ℝ => Real.sqrt (A t) * Real.sqrt (B t)),
      MeasureTheory.integral_const_mul]
    ring
  have hbig : 4 * (∫ t : ℝ, Real.sqrt (A t) * Real.sqrt (B t)) *
        (∫ s : ℝ, Real.sqrt (C s) * Real.sqrt (D s))
      ≤ 4 * (Real.sqrt (∫ t : ℝ, A t) * Real.sqrt (∫ t : ℝ, B t)) *
          (Real.sqrt (∫ s : ℝ, C s) * Real.sqrt (∫ s : ℝ, D s)) := by
    have h2 : 0 ≤ ∫ s : ℝ, Real.sqrt (C s) * Real.sqrt (D s) :=
      MeasureTheory.integral_nonneg fun s => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (cs_sqrt hAint hBint hAnn hBnn).2 (by norm_num))
      (cs_sqrt hCint hDint hCnn hDnn).2 h2 (by positivity)
  have hfinal : 4 * (Real.sqrt (∫ t : ℝ, A t) * Real.sqrt (∫ t : ℝ, B t)) *
        (Real.sqrt (∫ s : ℝ, C s) * Real.sqrt (∫ s : ℝ, D s))
      ≤ 4 * (∫ p : ℝ × ℝ, (u p) ^ 2) * (∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2) := by
    rw [hAeq, hCeq]
    have hb := Real.sqrt_le_sqrt hBle
    have hd := Real.sqrt_le_sqrt hDle
    have hsq0 : Real.sqrt (∫ p : ℝ × ℝ, (u p) ^ 2) * Real.sqrt (∫ p : ℝ × ℝ, (u p) ^ 2)
        = ∫ p : ℝ × ℝ, (u p) ^ 2 := by
      rw [← pow_two, Real.sq_sqrt hQ0nn]
    have hsq1 : Real.sqrt (∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2) *
        Real.sqrt (∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2)
        = ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 := by
      rw [← pow_two, Real.sq_sqrt hQ1nn]
    have hprod : Real.sqrt (∫ t : ℝ, B t) * Real.sqrt (∫ s : ℝ, D s)
        ≤ ∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2 :=
      (mul_le_mul hb hd (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans hsq1.le
    have hre : 4 * (Real.sqrt (∫ p : ℝ × ℝ, (u p) ^ 2) * Real.sqrt (∫ t : ℝ, B t)) *
        (Real.sqrt (∫ p : ℝ × ℝ, (u p) ^ 2) * Real.sqrt (∫ s : ℝ, D s))
        = 4 * (Real.sqrt (∫ p : ℝ × ℝ, (u p) ^ 2) * Real.sqrt (∫ p : ℝ × ℝ, (u p) ^ 2)) *
          (Real.sqrt (∫ t : ℝ, B t) * Real.sqrt (∫ s : ℝ, D s)) := by ring
    rw [hre, hsq0]
    exact mul_le_mul_of_nonneg_left hprod (by nlinarith [hQ0nn])
  calc ∫ p : ℝ × ℝ, (u p) ^ 4
      ≤ ∫ p : ℝ × ℝ, 4 * (Real.sqrt (A p.2) * Real.sqrt (B p.2)) *
          (Real.sqrt (C p.1) * Real.sqrt (D p.1)) := hstep1
    _ = 4 * (∫ t : ℝ, Real.sqrt (A t) * Real.sqrt (B t)) *
          (∫ s : ℝ, Real.sqrt (C s) * Real.sqrt (D s)) := hstep2
    _ ≤ 4 * (Real.sqrt (∫ t : ℝ, A t) * Real.sqrt (∫ t : ℝ, B t)) *
          (Real.sqrt (∫ s : ℝ, C s) * Real.sqrt (∫ s : ℝ, D s)) := hbig
    _ ≤ 4 * (∫ p : ℝ × ℝ, (u p) ^ 2) * (∫ p : ℝ × ℝ, ‖fderiv ℝ u p‖ ^ 2) := hfinal

end Work.FTS.StrongLWP.Sobolev.HolderHalf
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.HolderHalf.sup_le_of_holder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf

open MeasureTheory

/-- **Averaging core of the `C^{1/2}` sup bound.**  Let `s` be a measurable set of volume `4`
all of whose points are at distance at most `1` from `p` (think of the open unit square centred
at `p`, which in the product metric on `ℝ × ℝ` has volume `4` and diameter `2`).  If `v` obeys
the Hölder-`1/2` bound with constant `P ≥ 0`, then on account of the pointwise estimate
`|v p| ≤ |v p - v z| + |v z| ≤ P + |v z|` (`z ∈ s`) and Cauchy–Schwarz on `s`,
`|v p| ≤ P + (1/2) √(∫_s v²)`. -/
theorem abs_le_of_holder_on_set {v : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)} {p : ℝ × ℝ} {P : ℝ}
    (hP : 0 ≤ P) (hM : ∀ z z' : ℝ × ℝ, |v z - v z'| ≤ P * Real.sqrt (dist z z'))
    (hs : MeasurableSet s) (hvol : volume s = ENNReal.ofReal 4)
    (hdiam : ∀ z ∈ s, dist z p ≤ 1)
    (hint2 : IntegrableOn (fun z => (v z) ^ 2) s)
    (hint1 : IntegrableOn (fun z => |v z|) s) :
    |v p| ≤ P + Real.sqrt (∫ z in s, (v z) ^ 2) / 2 := by
  have hvolreal : volume.real s = 4 := by
    change (volume s).toReal = 4
    rw [hvol, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4)]
  have : IsFiniteMeasure (volume.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.ofReal_lt_top⟩
  -- the pointwise bound `|v p| ≤ P + |v z|` on `s`
  have hpt : ∀ z ∈ s, |v p| ≤ P + |v z| := by
    intro z hz
    have h1 : |v p - v z| ≤ P := by
      have h3 : Real.sqrt (dist p z) ≤ 1 := by
        rw [Real.sqrt_le_one, dist_comm]
        exact hdiam z hz
      calc |v p - v z| ≤ P * Real.sqrt (dist p z) := hM p z
        _ ≤ P * 1 := mul_le_mul_of_nonneg_left h3 hP
        _ = P := mul_one P
    rw [show v p = (v p - v z) + v z from by ring]
    exact (abs_add_le _ _).trans (add_le_add h1 le_rfl)
  have hIntP : Integrable (fun z : ℝ × ℝ => P + |v z|) (volume.restrict s) :=
    (integrable_const P).add hint1
  have hIntc : Integrable (fun _ : ℝ × ℝ => |v p|) (volume.restrict s) :=
    integrable_const (|v p|)
  have hmono : (∫ z in s, |v p|) ≤ ∫ z in s, (P + |v z|) :=
    MeasureTheory.setIntegral_mono_on hIntc hIntP hs (fun z hz => hpt z hz)
  have hL : (∫ z in s, |v p|) = 4 * |v p| := by
    rw [MeasureTheory.setIntegral_const, hvolreal, smul_eq_mul]
  have hR : (∫ z in s, (P + |v z|)) = 4 * P + ∫ z in s, |v z| := by
    have h1 := MeasureTheory.integral_add (f := fun _ : ℝ × ℝ => P)
      (g := fun z : ℝ × ℝ => |v z|) (integrable_const P) hint1
    rw [h1]
    have h2 : (∫ z in s, (P : ℝ)) = 4 * P := by
      rw [MeasureTheory.setIntegral_const, hvolreal, smul_eq_mul]
    rw [h2]
  -- Cauchy–Schwarz on `s`
  have hcs := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict s)
    (f := fun z : ℝ × ℝ => |v z|) (g := fun _ : ℝ × ℝ => (1 : ℝ))
    hint1.aestronglyMeasurable aestronglyMeasurable_const
    (hint2.congr (Filter.Eventually.of_forall fun z => (sq_abs (v z)).symm))
    (by
      have h1 : Integrable (fun _ : ℝ × ℝ => (1 : ℝ)) (volume.restrict s) :=
        integrable_const (1 : ℝ)
      simpa only [one_pow] using h1)
  have hL2 : (∫ z in s, |v z| ^ 2) = ∫ z in s, (v z) ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => sq_abs (v z))
  have hone : (∫ z : ℝ × ℝ, (1 : ℝ) ^ 2 ∂(volume.restrict s)) = 4 := by
    have h1 : (∫ z : ℝ × ℝ, (1 : ℝ) ^ 2 ∂(volume.restrict s))
        = ∫ _z : ℝ × ℝ, (1 : ℝ) ∂(volume.restrict s) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => one_pow 2)
    rw [h1, MeasureTheory.integral_const]
    change ((volume.restrict s) Set.univ).toReal * 1 = 4
    rw [Measure.restrict_apply_univ, hvol,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hCS : (∫ z in s, |v z|) ≤ 2 * Real.sqrt (∫ z in s, (v z) ^ 2) := by
    have h1 : |∫ z : ℝ × ℝ, |v z| * 1 ∂(volume.restrict s)| = ∫ z in s, |v z| := by
      rw [show (fun z : ℝ × ℝ => |v z| * 1) = fun z => |v z| from by funext z; rw [mul_one]]
      exact abs_of_nonneg (MeasureTheory.integral_nonneg
        (f := fun z : ℝ × ℝ => |v z|) fun z => abs_nonneg (v z))
    calc (∫ z in s, |v z|) = |∫ z : ℝ × ℝ, |v z| * 1 ∂(volume.restrict s)| := h1.symm
      _ ≤ Real.sqrt (∫ z : ℝ × ℝ, |v z| ^ 2 ∂(volume.restrict s))
            * Real.sqrt (∫ z : ℝ × ℝ, (1 : ℝ) ^ 2 ∂(volume.restrict s)) := hcs
      _ = 2 * Real.sqrt (∫ z in s, (v z) ^ 2) := by
          rw [hL2, hone, show Real.sqrt 4 = 2 by norm_num]
          ring
  have h4 : 4 * |v p| ≤ 4 * P + 2 * Real.sqrt (∫ z in s, (v z) ^ 2) := by
    calc 4 * |v p| = ∫ z in s, |v p| := hL.symm
      _ ≤ ∫ z in s, (P + |v z|) := hmono
      _ = 4 * P + ∫ z in s, |v z| := hR
      _ ≤ 4 * P + 2 * Real.sqrt (∫ z in s, (v z) ^ 2) := by linarith
  linarith

theorem sup_le_of_holder {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v)
    (P : ℝ) (hP : 0 ≤ P) (hM : ∀ z z' : ℝ × ℝ, |v z - v z'| ≤ P * Real.sqrt (dist z z')) :
    ∀ p : ℝ × ℝ, |v p| ≤ P + Real.sqrt (∫ x : ℝ × ℝ, (v x) ^ 2) / 2 := by
  intro p
  have hcont : Continuous v := hv.continuous
  set s : Set (ℝ × ℝ) :=
    Set.Ioo (p.1 - 1) (p.1 + 1) ×ˢ Set.Ioo (p.2 - 1) (p.2 + 1) with hsdef
  have hsm : MeasurableSet s := by
    rw [hsdef]
    exact measurableSet_Ioo.prod measurableSet_Ioo
  have hvol : volume s = ENNReal.ofReal 4 := by
    rw [hsdef, Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo,
      show p.1 + 1 - (p.1 - 1) = 2 by ring, show p.2 + 1 - (p.2 - 1) = 2 by ring,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hdiam : ∀ z ∈ s, dist z p ≤ 1 := by
    intro z hz
    rw [hsdef] at hz
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_le (le_of_lt (abs_lt.mpr ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩))
      (le_of_lt (abs_lt.mpr ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩))
  have hIntv : Integrable v volume := hcont.integrable_of_hasCompactSupport hc
  have hInt1 : Integrable (fun z : ℝ × ℝ => |v z|) volume := hIntv.abs
  have hInt2 : Integrable (fun z : ℝ × ℝ => (v z) ^ 2) volume := by
    have hsupp : HasCompactSupport (fun z : ℝ × ℝ => (v z) ^ 2) :=
      hc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
    exact (hcont.pow 2).integrable_of_hasCompactSupport hsupp
  have hbound := abs_le_of_holder_on_set (v := v) (s := s) (p := p) (P := P) hP hM hsm hvol
    hdiam hInt2.restrict hInt1.restrict
  have hmonoJ : (∫ z in s, (v z) ^ 2) ≤ ∫ z : ℝ × ℝ, (v z) ^ 2 :=
    MeasureTheory.setIntegral_le_integral hInt2 (Filter.Eventually.of_forall fun z => sq_nonneg _)
  calc |v p| ≤ P + Real.sqrt (∫ z in s, (v z) ^ 2) / 2 := hbound
    _ ≤ P + Real.sqrt (∫ z : ℝ × ℝ, (v z) ^ 2) / 2 := by
        linarith [Real.sqrt_le_sqrt hmonoJ]

end Work.FTS.StrongLWP.Sobolev.HolderHalf
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.R.SinBoundaryTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux.R

open MeasureTheory Filter Set intervalIntegral

/-- Near `0`, the function `θ ↦ θ⁻¹` is not integrable: it is the boundary case of
`intervalIntegrable_inv_iff`. -/
private lemma not_integrableOn_inv_Ioc {δ : ℝ} (hδ : 0 < δ) :
    ¬ MeasureTheory.IntegrableOn (fun θ : ℝ => θ⁻¹) (Set.Ioc 0 δ) := by
  intro h
  have h2 : IntervalIntegrable (fun θ : ℝ => θ⁻¹) volume (0 : ℝ) δ := by
    refine ⟨h, ?_⟩
    rw [Set.Ioc_eq_empty_of_le hδ.le]
    exact MeasureTheory.integrableOn_empty
  rcases (intervalIntegrable_inv_iff (a := (0 : ℝ)) (b := δ)).1 h2 with h' | h'
  · exact (ne_of_lt hδ) h'
  · exact h' (by rw [Set.uIcc_of_le hδ.le]; exact ⟨le_rfl, hδ.le⟩)

/-- The translate `θ ↦ (θ - π/2)⁻¹` is not integrable on `(π/2 - δ, π/2)`. -/
private lemma not_integrableOn_sub_inv_Ioc {δ : ℝ} (hδ : 0 < δ) :
    ¬ MeasureTheory.IntegrableOn (fun θ : ℝ => (θ - Real.pi / 2)⁻¹)
      (Set.Ioc (Real.pi / 2 - δ) (Real.pi / 2)) := by
  intro h
  have hlt : Real.pi / 2 - δ < Real.pi / 2 := by linarith
  have h2 : IntervalIntegrable (fun θ : ℝ => (θ - Real.pi / 2)⁻¹) volume
      (Real.pi / 2 - δ) (Real.pi / 2) := by
    refine ⟨h, ?_⟩
    rw [Set.Ioc_eq_empty_of_le hlt.le]
    exact MeasureTheory.integrableOn_empty
  rcases (intervalIntegrable_sub_inv_iff (a := Real.pi / 2 - δ) (b := Real.pi / 2)
    (c := Real.pi / 2)).1 h2 with h' | h'
  · exact (ne_of_gt hδ) (by linarith : δ = 0)
  · exact h' (by rw [Set.uIcc_of_le hlt.le]; exact ⟨by linarith, le_rfl⟩)

/-- The left limit of `sin (2·) u` is nonnegative, and strictly positive only if `u` is not
integrable; since `u` is integrable, it vanishes. -/
private lemma limit_eq_zero_left {u : ℝ → ℝ} {L : ℝ}
    (hu : MeasureTheory.IntegrableOn u (Set.Icc 0 (Real.pi / 2)))
    (hu0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ u θ)
    (hLtend : Filter.Tendsto (fun θ => Real.sin (2 * θ) * u θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) :
    L = 0 := by
  have hnonneg : 0 ≤ L := by
    refine ge_of_tendsto hLtend ?_
    filter_upwards [Ioo_mem_nhdsGT (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2)]
      with θ hθ
    exact mul_nonneg
      (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])))
      (hu0 θ hθ)
  by_contra hLne
  have hLpos : 0 < L := lt_of_le_of_ne hnonneg (Ne.symm hLne)
  have hL4pos : 0 < L / 4 := by linarith
  have hev : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), L / 2 < Real.sin (2 * θ) * u θ :=
    hLtend.eventually (Ioi_mem_nhds (by linarith : L / 2 < L))
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp hev
  set δ : ℝ := min (ε / 2) (Real.pi / 4) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith [Real.pi_pos])
  have hδle : δ ≤ ε / 2 := min_le_left _ _
  have hδle2 : δ ≤ Real.pi / 4 := min_le_right _ _
  have hsub : Set.Ioc (0 : ℝ) δ ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    intro θ hθ
    exact ⟨hθ.1.le, by linarith [hθ.2, hδle2, Real.pi_pos]⟩
  -- on `(0, δ]` the function `u` dominates `(L/4) θ⁻¹`
  have hbound : ∀ θ ∈ Set.Ioc (0 : ℝ) δ, ‖(L / 4) * θ⁻¹‖ ≤ ‖u θ‖ := by
    intro θ hθ
    have hθpos : 0 < θ := hθ.1
    have hθpi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨hθ.1, by linarith [hθ.2, hδle2, Real.pi_pos]⟩
    have huθ : 0 ≤ u θ := hu0 θ hθpi
    rw [Real.norm_of_nonneg (mul_nonneg hL4pos.le (inv_nonneg.mpr hθ.1.le)),
      Real.norm_of_nonneg huθ]
    have hFθ : L / 2 < Real.sin (2 * θ) * u θ := by
      refine hε ?_ hθpos
      rw [Real.dist_eq, sub_zero, abs_of_pos hθpos]
      linarith [hθ.2, hδle, hεpos]
    have hsle : Real.sin (2 * θ) ≤ 2 * θ := Real.sin_le (by linarith)
    have h3 : L / 2 < (2 * θ) * u θ :=
      lt_of_lt_of_le hFθ (mul_le_mul_of_nonneg_right hsle huθ)
    have h4 : L / (4 * θ) ≤ u θ := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [h3]
    have h5 : (L / 4) * θ⁻¹ = L / (4 * θ) := by
      simp only [div_eq_mul_inv, mul_inv]
      ring
    linarith [h4, h5]
  -- hence `θ ↦ θ⁻¹` would be integrable on `(0, δ]`, contradiction
  have hintu : MeasureTheory.IntegrableOn u (Set.Ioc (0 : ℝ) δ) := hu.mono_set hsub
  have haesm : AEStronglyMeasurable (fun θ : ℝ => (L / 4) * θ⁻¹)
      (volume.restrict (Set.Ioc (0 : ℝ) δ)) := by
    refine ((continuousOn_const.mul ((continuousOn_id :
      ContinuousOn (fun x : ℝ => x) (Set.Ioc (0 : ℝ) δ)).inv₀ ?_)).aestronglyMeasurable
        measurableSet_Ioc)
    intro x hx; exact ne_of_gt hx.1
  have hae : ∀ᵐ θ ∂(volume.restrict (Set.Ioc (0 : ℝ) δ)), ‖(L / 4) * θ⁻¹‖ ≤ ‖u θ‖ := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall (fun θ hθ => hbound θ hθ)
  have hint1 : MeasureTheory.IntegrableOn (fun θ : ℝ => (L / 4) * θ⁻¹) (Set.Ioc (0 : ℝ) δ) :=
    MeasureTheory.Integrable.mono hintu haesm hae
  have hint2 : MeasureTheory.IntegrableOn (fun θ : ℝ => θ⁻¹) (Set.Ioc (0 : ℝ) δ) := by
    have h := MeasureTheory.Integrable.const_mul hint1 ((L / 4)⁻¹)
    have heq : (fun θ : ℝ => (L / 4)⁻¹ * ((L / 4) * θ⁻¹)) = fun θ : ℝ => θ⁻¹ := by
      funext θ
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hL4pos), one_mul]
    rwa [heq] at h
  exact (not_integrableOn_inv_Ioc hδpos) hint2

/-- The right limit of `sin (2·) u` is nonnegative, and strictly positive only if `u` is not
integrable; since `u` is integrable, it vanishes. -/
private lemma limit_eq_zero_right {u : ℝ → ℝ} {L : ℝ}
    (hu : MeasureTheory.IntegrableOn u (Set.Icc 0 (Real.pi / 2)))
    (hu0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ u θ)
    (hLtend : Filter.Tendsto (fun θ => Real.sin (2 * θ) * u θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L)) :
    L = 0 := by
  have hnonneg : 0 ≤ L := by
    refine ge_of_tendsto hLtend ?_
    filter_upwards [Ioo_mem_nhdsLT (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2)]
      with θ hθ
    exact mul_nonneg
      (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])))
      (hu0 θ hθ)
  by_contra hLne
  have hLpos : 0 < L := lt_of_le_of_ne hnonneg (Ne.symm hLne)
  have hL4pos : 0 < L / 4 := by linarith
  have hev : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      L / 2 < Real.sin (2 * θ) * u θ :=
    hLtend.eventually (Ioi_mem_nhds (by linarith : L / 2 < L))
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp hev
  set δ : ℝ := min (ε / 2) (Real.pi / 4) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith [Real.pi_pos])
  have hδle : δ ≤ ε / 2 := min_le_left _ _
  have hδle2 : δ ≤ Real.pi / 4 := min_le_right _ _
  set a : ℝ := Real.pi / 2 - δ with hadef
  have hapos : 0 < a := by rw [hadef]; linarith [hδle2, Real.pi_pos]
  have halt : a < Real.pi / 2 := by rw [hadef]; linarith
  have hsub : Set.Ioc a (Real.pi / 2) ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    intro θ hθ
    exact ⟨le_of_lt (lt_trans hapos hθ.1), hθ.2⟩
  -- on `(a, π/2]` the function `u` dominates `(L/4) (θ - π/2)⁻¹` up to sign
  have hbound : ∀ θ ∈ Set.Ioc a (Real.pi / 2), ‖(L / 4) * (θ - Real.pi / 2)⁻¹‖ ≤ ‖u θ‖ := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ.2 with h | h
    · subst h; simp
    · have hθpos : 0 < θ := lt_trans hapos hθ.1
      have huθ : 0 ≤ u θ := hu0 θ ⟨hθpos, h⟩
      have hinv : (θ - Real.pi / 2)⁻¹ < 0 := inv_lt_zero.mpr (by linarith)
      rw [Real.norm_of_nonpos (mul_neg_of_pos_of_neg hL4pos hinv).le,
        Real.norm_of_nonneg huθ]
      have hthis : -((L / 4) * (θ - Real.pi / 2)⁻¹) = (L / 4) * (Real.pi / 2 - θ)⁻¹ := by
        rw [show θ - Real.pi / 2 = -(Real.pi / 2 - θ) by ring, inv_neg]
        ring
      rw [hthis]
      have hsle : Real.sin (2 * θ) ≤ 2 * (Real.pi / 2 - θ) := by
        have h1 : 2 * θ = Real.pi - 2 * (Real.pi / 2 - θ) := by ring
        have h2 : (0 : ℝ) ≤ 2 * (Real.pi / 2 - θ) := by linarith
        calc Real.sin (2 * θ) = Real.sin (Real.pi - 2 * (Real.pi / 2 - θ)) := by rw [h1]
          _ = Real.sin (2 * (Real.pi / 2 - θ)) := Real.sin_pi_sub _
          _ ≤ 2 * (Real.pi / 2 - θ) := Real.sin_le h2
      have hFθ : L / 2 < Real.sin (2 * θ) * u θ := by
        refine hε ?_ h
        rw [Real.dist_eq, abs_of_neg (by linarith : θ - Real.pi / 2 < 0)]
        linarith [hθ.1, hδle, hεpos]
      have h3 : L / 2 < (2 * (Real.pi / 2 - θ)) * u θ :=
        lt_of_lt_of_le hFθ (mul_le_mul_of_nonneg_right hsle huθ)
      have h4 : L / (4 * (Real.pi / 2 - θ)) ≤ u θ := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [h3]
      have h5 : (L / 4) * (Real.pi / 2 - θ)⁻¹ = L / (4 * (Real.pi / 2 - θ)) := by
        simp only [div_eq_mul_inv, mul_inv]
        ring
      linarith [h4, h5]
  -- hence `θ ↦ (θ - π/2)⁻¹` would be integrable on `(a, π/2]`, contradiction
  have hintu : MeasureTheory.IntegrableOn u (Set.Ioc a (Real.pi / 2)) := hu.mono_set hsub
  have haesm : AEStronglyMeasurable (fun θ : ℝ => (L / 4) * (θ - Real.pi / 2)⁻¹)
      (volume.restrict (Set.Ioc a (Real.pi / 2))) :=
    ((((measurable_id.sub measurable_const)).inv).const_mul (L / 4)).aestronglyMeasurable.restrict
  have hae : ∀ᵐ θ ∂(volume.restrict (Set.Ioc a (Real.pi / 2))),
      ‖(L / 4) * (θ - Real.pi / 2)⁻¹‖ ≤ ‖u θ‖ := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall (fun θ hθ => hbound θ hθ)
  have hint1 : MeasureTheory.IntegrableOn (fun θ : ℝ => (L / 4) * (θ - Real.pi / 2)⁻¹)
      (Set.Ioc a (Real.pi / 2)) :=
    MeasureTheory.Integrable.mono hintu haesm hae
  have hint2 : MeasureTheory.IntegrableOn (fun θ : ℝ => (θ - Real.pi / 2)⁻¹)
      (Set.Ioc a (Real.pi / 2)) := by
    have h := MeasureTheory.Integrable.const_mul hint1 ((L / 4)⁻¹)
    have heq : (fun θ : ℝ => (L / 4)⁻¹ * ((L / 4) * (θ - Real.pi / 2)⁻¹))
        = fun θ : ℝ => (θ - Real.pi / 2)⁻¹ := by
      funext θ
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hL4pos), one_mul]
    rwa [heq] at h
  have hnot : ¬ MeasureTheory.IntegrableOn (fun θ : ℝ => (θ - Real.pi / 2)⁻¹)
      (Set.Ioc a (Real.pi / 2)) := by
    rw [hadef]
    exact not_integrableOn_sub_inv_Ioc hδpos
  exact hnot hint2

/-- The left endpoint: `sin (2θ) u θ → 0` as `θ → 0⁺`. -/
private lemma left_tendsto {u v' : ℝ → ℝ}
    (hu : MeasureTheory.IntegrableOn u (Set.Icc 0 (Real.pi / 2)))
    (hu0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ u θ)
    (hv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ' => Real.sin (2 * θ') * u θ') (v' θ) θ)
    (hv' : MeasureTheory.IntegrableOn v' (Set.Icc 0 (Real.pi / 2))) :
    Filter.Tendsto (fun θ => Real.sin (2 * θ) * u θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hc0 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hc2 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      HasDerivAt (fun θ => Real.sin (2 * θ) * u θ) (v' x) x :=
    fun x hx => hv x ⟨hx.1, by linarith [hx.2]⟩
  have hcont : ContinuousAt (fun θ => Real.sin (2 * θ) * u θ) (Real.pi / 4) :=
    (hv (Real.pi / 4) ⟨by linarith, by linarith⟩).continuousAt
  have hint : IntervalIntegrable v' volume (0 : ℝ) (Real.pi / 4) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hc0.le]
    exact hv'.mono_set (Set.Icc_subset_Icc_right hc2.le)
  have hex := tendstoGT_of_hasDerivAt_integrableOn hc0 hderiv hcont hint
  set L : ℝ := Real.sin (2 * (Real.pi / 4)) * u (Real.pi / 4)
    - ∫ x in (0 : ℝ)..(Real.pi / 4), v' x with hL
  have hLtend : Filter.Tendsto (fun θ => Real.sin (2 * θ) * u θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L) := by
    rw [hL]; exact hex
  have hLzero : L = 0 := limit_eq_zero_left hu hu0 hLtend
  rw [hLzero] at hLtend
  exact hLtend

/-- The right endpoint: `sin (2θ) u θ → 0` as `θ → (π/2)⁻`. -/
private lemma right_tendsto {u v' : ℝ → ℝ}
    (hu : MeasureTheory.IntegrableOn u (Set.Icc 0 (Real.pi / 2)))
    (hu0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ u θ)
    (hv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ' => Real.sin (2 * θ') * u θ') (v' θ) θ)
    (hv' : MeasureTheory.IntegrableOn v' (Set.Icc 0 (Real.pi / 2))) :
    Filter.Tendsto (fun θ => Real.sin (2 * θ) * u θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hc0 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hc2 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hderiv : ∀ x ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      HasDerivAt (fun θ => Real.sin (2 * θ) * u θ) (v' x) x :=
    fun x hx => hv x ⟨by linarith [hx.1], hx.2⟩
  have hcont : ContinuousAt (fun θ => Real.sin (2 * θ) * u θ) (Real.pi / 4) :=
    (hv (Real.pi / 4) ⟨by linarith, by linarith⟩).continuousAt
  have hint : IntervalIntegrable v' volume (Real.pi / 4) (Real.pi / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hc2.le]
    exact hv'.mono_set (Set.Icc_subset_Icc_left hc0.le)
  have hex := tendstoLT_of_hasDerivAt_integrableOn hc2 hderiv hcont hint
  set L : ℝ := Real.sin (2 * (Real.pi / 4)) * u (Real.pi / 4)
    + ∫ x in (Real.pi / 4)..(Real.pi / 2), v' x with hL
  have hLtend : Filter.Tendsto (fun θ => Real.sin (2 * θ) * u θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L) := by
    rw [hL]; exact hex
  have hLzero : L = 0 := limit_eq_zero_right hu hu0 hLtend
  rw [hLzero] at hLtend
  exact hLtend

theorem SinBoundaryTendsto {u v' : ℝ → ℝ}
    (hu : MeasureTheory.IntegrableOn u (Set.Icc 0 (Real.pi / 2)))
    (hu0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ u θ)
    (hv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ' => Real.sin (2 * θ') * u θ') (v' θ) θ)
    (hv' : MeasureTheory.IntegrableOn v' (Set.Icc 0 (Real.pi / 2))) :
    Filter.Tendsto (fun θ => Real.sin (2 * θ) * u θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ => Real.sin (2 * θ) * u θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
  ⟨left_tendsto hu hu0 hv hv', right_tendsto hu hu0 hv hv'⟩

end Work.FTS.StrongPersist.H6Aux.R
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.tendsto_sin_mul_zero_of_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Vanishing of a `sin(2θ)u`-profile at the endpoints of `Iθ`

Let `u : ℝ → ℝ` be integrable on `Iθ = [0, π/2]` and let
`F θ = sin (2θ) · u θ` have an integrable derivative `v'` on `(0, π/2)`.  Then `F` vanishes at both
endpoints:

`sin (2θ) u θ → 0` as `θ → 0⁺` and as `θ → (π/2)⁻`.

The point is that `F` has finite total variation, so it cannot oscillate near an endpoint, while a
non-vanishing limit at an endpoint forces `|u θ| ≳ dist (θ, endpoint)⁻¹`, which is not integrable
(logarithmic divergence) — contradicting the integrability of `u`.  Concretely: if `F` did not tend
to `0`, there would be `ε > 0` and points `θ₀` arbitrarily close to the endpoint with
`|F θ₀| ≥ ε`; a shrinking-interval integral bound `∫ |v'| < ε/2` (absolute continuity of the
integral) then gives `|F θ| ≥ ε/2` on a whole one-sided neighbourhood of the endpoint, whence
`|u θ| ≥ (ε/4)/θ` (respectively `≥ (ε/4)/(π/2 - θ)`), which is not integrable.

The auxiliary facts (shrinking integral → 0, the oscillation bound, and the non-integrability of
`c/θ` and `c/(L-θ)`) are the lemmas in `Submission.Work.FTS.StrongPersist.H6Aux.EndLimits`.
-/

namespace Work.FTS.StrongPersist.H6Aux

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.StrongPersist.H6Aux.EndLimits

theorem tendsto_sin_mul_zero_of_integrable {u v' : ℝ → ℝ}
    (hu : MeasureTheory.IntegrableOn u Work.Spaces.Iθ)
    (hu0 : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), 0 ≤ u θ)
    (hv : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      HasDerivAt (fun θ' => Real.sin (2*θ') * u θ') (v' θ) θ)
    (hv' : MeasureTheory.IntegrableOn v' Work.Spaces.Iθ) :
    Filter.Tendsto (fun θ => Real.sin (2*θ) * u θ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ => Real.sin (2*θ) * u θ) (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0) := by
  set F : ℝ → ℝ := fun θ => Real.sin (2*θ) * u θ with hF
  have hpi2 : (0:ℝ) < Real.pi/2 := by linarith [Real.pi_pos]
  have hderiv : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), HasDerivAt F (v' θ) θ := hv
  have hint' : IntegrableOn v' (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    hv'.mono_set (fun x hx => ⟨hx.1.le, hx.2.le⟩)
  have huint' : IntegrableOn u (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    hu.mono_set (fun x hx => ⟨hx.1.le, hx.2.le⟩)
  constructor
  · -- ### the left endpoint `0⁺`
    have hA : Tendsto (fun r : ℝ => ∫ x in (0:ℝ)..r, |v' x|)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
      tendsto_intervalIntegral_abs_left hpi2 hint'
    by_contra hcon
    rw [Metric.tendsto_nhds] at hcon
    push Not at hcon
    obtain ⟨ε, hε, hfreq⟩ := hcon
    simp only [Real.dist_eq, sub_zero] at hfreq
    obtain ⟨δ, _hδ, hδsub⟩ := (nhdsGT_basis (0:ℝ)).mem_iff.1
      (hA.eventually (Metric.ball_mem_nhds (0:ℝ) (by linarith : (0:ℝ) < ε / 2)))
    set r : ℝ := min (δ/2) (Real.pi/4) with hrdef
    have hrpos : 0 < r := by
      rw [hrdef]; exact lt_min (by linarith) (by linarith [Real.pi_pos])
    have hrδ : r < δ := by
      rw [hrdef]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hrpi : r < Real.pi/2 := by
      rw [hrdef]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
    have hAr : (∫ x in (0:ℝ)..r, |v' x|) < ε/2 := by
      have h := hδsub ⟨hrpos, hrδ⟩
      simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at h
      linarith [le_abs_self (∫ x in (0:ℝ)..r, |v' x|)]
    have hmem : Set.Ioo (0:ℝ) r ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
      (nhdsGT_basis (0:ℝ)).mem_iff.2 ⟨r, hrpos, subset_rfl⟩
    obtain ⟨θ₀, hθ₀big, hθ₀mem⟩ := (hfreq.and_eventually hmem).exists
    have hIntOn : IntegrableOn v' (Set.Ioc (0:ℝ) r) :=
      hint'.mono_set (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hrpi⟩)
    have hIntAbs : IntervalIntegrable v' volume (0:ℝ) r :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hrpos.le).2 hIntOn
    have hderivr : ∀ θ ∈ Set.Ioo (0:ℝ) r, HasDerivAt F (v' θ) θ :=
      fun θ hθ => hderiv θ ⟨hθ.1, lt_trans hθ.2 hrpi⟩
    have hkey : ∀ θ, 0 < θ → θ < r → ε / 2 ≤ |F θ| := by
      intro θ hθ hθr
      have hdiff : |F θ - F θ₀| ≤ ∫ x in (0:ℝ)..r, |v' x| := by
        rcases le_total θ θ₀ with hle | hle
        · rw [abs_sub_comm]
          exact abs_sub_le_integral_abs (a := (0:ℝ)) (b := r) (θ₁ := θ) (θ₂ := θ₀)
            hderivr hIntAbs hθ hle hθ₀mem.2
        · exact abs_sub_le_integral_abs (a := (0:ℝ)) (b := r) (θ₁ := θ₀) (θ₂ := θ)
            hderivr hIntAbs hθ₀mem.1 hle hθr
      have h1 : |F θ₀| ≤ |F θ| + |F θ - F θ₀| := by
        calc |F θ₀| = |F θ + (F θ₀ - F θ)| := by congr 1; ring
          _ ≤ |F θ| + |F θ₀ - F θ| := abs_add_le _ _
          _ = |F θ| + |F θ - F θ₀| := by rw [abs_sub_comm]
      linarith [hAr, hdiff, hθ₀big, h1]
    have hle : ∀ θ ∈ Set.Ioo (0:ℝ) r, ε / 4 / θ ≤ |u θ| := by
      intro θ hθ
      have hFθ : ε / 2 ≤ |F θ| := hkey θ hθ.1 hθ.2
      have hs : 0 < Real.sin (2*θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, hrpi, Real.pi_pos])
      have hFval : F θ = Real.sin (2*θ) * u θ := by rw [hF]
      have habs : |F θ| = Real.sin (2*θ) * |u θ| := by
        rw [hFval, abs_mul, abs_of_pos hs]
      have hsinle : Real.sin (2*θ) ≤ 2*θ := Real.sin_le (by linarith [hθ.1])
      have h1 : ε / 4 / θ ≤ (ε/2)/Real.sin (2*θ) := by
        rw [div_le_div_iff₀ hθ.1 hs]
        have hmul : (ε/4) * Real.sin (2*θ) ≤ (ε/4) * (2*θ) :=
          mul_le_mul_of_nonneg_left hsinle (by linarith [hε] : (0:ℝ) ≤ ε/4)
        have hmul2 : (ε/4) * (2*θ) = (ε/2) * θ := by ring
        linarith [hmul, hmul2]
      have h4 : (ε/2)/Real.sin (2*θ) ≤ |u θ| := by
        have hmul : |u θ| * Real.sin (2*θ) = |F θ| := by rw [habs, mul_comm]
        rw [div_le_iff₀ hs, hmul]
        exact hFθ
      exact le_trans h1 h4
    have huAbsOn : IntegrableOn (fun θ => |u θ|) (Set.Ioo (0:ℝ) r) :=
      Integrable.abs (huint'.mono_set (fun x hx => ⟨hx.1, lt_trans hx.2 hrpi⟩))
    refine (not_integrableOn_Ioo_div (c := ε/4) (r := r) (by linarith) hrpos) ?_
    refine Integrable.mono' huAbsOn ?_ ?_
    · exact (measurable_const.div measurable_id).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith [hε]) hθ.1.le)]
      exact hle θ hθ
  · -- ### the right endpoint `(π/2)⁻`
    have hA2 : Tendsto (fun t : ℝ => ∫ x in t..Real.pi/2, |v' x|)
        (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0) :=
      tendsto_intervalIntegral_abs_right hpi2 hint'
    by_contra hcon
    rw [Metric.tendsto_nhds] at hcon
    push Not at hcon
    obtain ⟨ε, hε, hfreq⟩ := hcon
    simp only [Real.dist_eq, sub_zero] at hfreq
    obtain ⟨t₀, ht₀lt, ht₀sub⟩ := (nhdsLT_basis (Real.pi/2)).mem_iff.1
      (hA2.eventually (Metric.ball_mem_nhds (0:ℝ) (by linarith : (0:ℝ) < ε / 2)))
    set t : ℝ := (max t₀ 0 + Real.pi/2)/2 with htdef
    have htpos : 0 < t := by
      rw [htdef]
      have := le_max_right t₀ (0:ℝ)
      linarith [Real.pi_pos]
    have htt : t₀ < t := by
      rw [htdef]
      have := le_max_left t₀ (0:ℝ)
      linarith
    have htlt : t < Real.pi/2 := by
      rw [htdef]
      have := max_lt ht₀lt hpi2
      linarith
    have hAt : (∫ x in t..Real.pi/2, |v' x|) < ε/2 := by
      have h := ht₀sub ⟨htt, htlt⟩
      simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at h
      linarith [le_abs_self (∫ x in t..Real.pi/2, |v' x|)]
    have hmem : Set.Ioo t (Real.pi/2) ∈ nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2)) :=
      (nhdsLT_basis (Real.pi/2)).mem_iff.2 ⟨t, htlt, subset_rfl⟩
    obtain ⟨θ₀, hθ₀big, hθ₀mem⟩ := (hfreq.and_eventually hmem).exists
    have hIntOn : IntegrableOn v' (Set.Ioo t (Real.pi/2)) :=
      hint'.mono_set (fun x hx => ⟨lt_trans htpos hx.1, hx.2⟩)
    have hIntAbs : IntervalIntegrable v' volume t (Real.pi/2) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le htlt.le).2 hIntOn
    have hderivt : ∀ θ ∈ Set.Ioo t (Real.pi/2), HasDerivAt F (v' θ) θ :=
      fun θ hθ => hderiv θ ⟨lt_trans htpos hθ.1, hθ.2⟩
    have hkey : ∀ θ, t < θ → θ < Real.pi/2 → ε / 2 ≤ |F θ| := by
      intro θ hθt hθpi
      have hdiff : |F θ - F θ₀| ≤ ∫ x in t..Real.pi/2, |v' x| := by
        rcases le_total θ θ₀ with hle | hle
        · rw [abs_sub_comm]
          exact abs_sub_le_integral_abs (a := t) (b := Real.pi/2) (θ₁ := θ) (θ₂ := θ₀)
            hderivt hIntAbs hθt hle hθ₀mem.2
        · exact abs_sub_le_integral_abs (a := t) (b := Real.pi/2) (θ₁ := θ₀) (θ₂ := θ)
            hderivt hIntAbs hθ₀mem.1 hle hθpi
      have h1 : |F θ₀| ≤ |F θ| + |F θ - F θ₀| := by
        calc |F θ₀| = |F θ + (F θ₀ - F θ)| := by congr 1; ring
          _ ≤ |F θ| + |F θ₀ - F θ| := abs_add_le _ _
          _ = |F θ| + |F θ - F θ₀| := by rw [abs_sub_comm]
      linarith [hAt, hdiff, hθ₀big, h1]
    have hle : ∀ θ ∈ Set.Ioo t (Real.pi/2), ε / 4 / (Real.pi/2 - θ) ≤ |u θ| := by
      intro θ hθ
      have hFθ : ε / 2 ≤ |F θ| := hkey θ hθ.1 hθ.2
      have hpos : 0 < Real.pi/2 - θ := by linarith [hθ.2]
      have hs : 0 < Real.sin (2*θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, htpos]) (by linarith [hθ.2])
      have hFval : F θ = Real.sin (2*θ) * u θ := by rw [hF]
      have habs : |F θ| = Real.sin (2*θ) * |u θ| := by
        rw [hFval, abs_mul, abs_of_pos hs]
      have hsinle : Real.sin (2*θ) ≤ 2*(Real.pi/2 - θ) := by
        have hπ : Real.pi - 2*θ = 2*(Real.pi/2 - θ) := by ring
        calc Real.sin (2*θ) = Real.sin (Real.pi - 2*θ) := (Real.sin_pi_sub (2*θ)).symm
          _ = Real.sin (2*(Real.pi/2 - θ)) := by rw [hπ]
          _ ≤ 2*(Real.pi/2 - θ) := Real.sin_le (by linarith)
      have h1 : ε / 4 / (Real.pi/2 - θ) ≤ (ε/2)/Real.sin (2*θ) := by
        rw [div_le_div_iff₀ hpos hs]
        have hmul : (ε/4) * Real.sin (2*θ) ≤ (ε/4) * (2*(Real.pi/2 - θ)) :=
          mul_le_mul_of_nonneg_left hsinle (by linarith [hε] : (0:ℝ) ≤ ε/4)
        have hmul2 : (ε/4) * (2*(Real.pi/2 - θ)) = (ε/2) * (Real.pi/2 - θ) := by ring
        linarith [hmul, hmul2]
      have h4 : (ε/2)/Real.sin (2*θ) ≤ |u θ| := by
        have hmul : |u θ| * Real.sin (2*θ) = |F θ| := by rw [habs, mul_comm]
        rw [div_le_iff₀ hs, hmul]
        exact hFθ
      exact le_trans h1 h4
    have huAbsOn : IntegrableOn (fun θ => |u θ|) (Set.Ioo t (Real.pi/2)) :=
      Integrable.abs (huint'.mono_set (fun x hx => ⟨lt_trans htpos hx.1, hx.2⟩))
    refine (not_integrableOn_Ioo_div_sub (c := ε/4) (L := Real.pi/2) (t := t)
      (by linarith) htlt) ?_
    refine Integrable.mono' huAbsOn ?_ ?_
    · exact (measurable_const.div (measurable_const.sub measurable_id)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith [hε]) (by linarith [hθ.2]))]
      exact hle θ hθ

end Work.FTS.StrongPersist.H6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45Defs =====
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

/-- The angular factor `m(θ)` of the pointwise bound for `D_z^j D_θ^i A` when `A` is
`𝒲^{l,∞}`-bounded: `1` for `i = 0` and `(α + sin 2θ)·sin(2θ)^{α/5}` for `i ≥ 1`
(`Spaces.pz_Dth_sup_bound`). -/
def Abnd (α : ℝ) (i : ℕ) (θ : ℝ) : ℝ :=
  if i = 0 then 1
  else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)

/-- `Abnd` is nonnegative on the angular interval. -/
theorem Abnd_nonneg {α : ℝ} (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (i : ℕ) :
    0 ≤ Abnd α i θ := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  unfold Abnd
  split_ifs with h
  · norm_num
  · exact mul_nonneg (by linarith) (Real.rpow_nonneg hs _)

/-- `Abnd α i θ ≤ 2` for every `α ∈ (0,1]` and `θ ∈ Iθ`. -/
theorem Abnd_le_two {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (i : ℕ) : Abnd α i θ ≤ 2 := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  unfold Abnd
  split_ifs with h
  · norm_num
  · have h1 : α + Real.sin (2 * θ) ≤ 2 := by linarith
    have h2 : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 :=
      Real.rpow_le_one hs hs1 (by linarith)
    calc (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)
        ≤ 2 * 1 := by
          refine mul_le_mul h1 h2 (Real.rpow_nonneg hs _) (by norm_num)
      _ = 2 := by ring

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.CS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth

set_option maxHeartbeats 1600000

/-- The square-root form of the Cauchy–Schwarz inequality on a set, with a.e. nonnegativity. -/
theorem cs_sqrt_le_ae {s : Set ℝ} {A B : ℝ → ℝ}
    (hA : MeasureTheory.IntegrableOn A s) (hB : MeasureTheory.IntegrableOn B s)
    (hAnn : ∀ᵐ x ∂(MeasureTheory.volume.restrict s), 0 ≤ A x)
    (hBnn : ∀ᵐ x ∂(MeasureTheory.volume.restrict s), 0 ≤ B x) :
    (∫ x in s, Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt (∫ x in s, A x) * Real.sqrt (∫ x in s, B x) := by
  have hu_meas : AEStronglyMeasurable (fun x => Real.sqrt (A x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have hv_meas : AEStronglyMeasurable (fun x => Real.sqrt (B x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable
  have hu_sq : Integrable (fun x => Real.sqrt (A x) ^ 2) (volume.restrict s) :=
    hA.congr (hAnn.mono (fun x hx => (Real.sq_sqrt hx).symm))
  have hv_sq : Integrable (fun x => Real.sqrt (B x) ^ 2) (volume.restrict s) :=
    hB.congr (hBnn.mono (fun x hx => (Real.sq_sqrt hx).symm))
  have hu_lp : MemLp (fun x => Real.sqrt (A x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hu_meas).mpr hu_sq
  have hv_lp : MemLp (fun x => Real.sqrt (B x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hv_meas).mpr hv_sq
  have hcs := Work.Spaces.cs_integral hu_lp hv_lp
  have e1 : (∫ x in s, Real.sqrt (A x) ^ 2) = ∫ x in s, A x :=
    integral_congr_ae (hAnn.mono fun x hx => Real.sq_sqrt hx)
  have e2 : (∫ x in s, Real.sqrt (B x) ^ 2) = ∫ x in s, B x :=
    integral_congr_ae (hBnn.mono fun x hx => Real.sq_sqrt hx)
  rw [e1, e2] at hcs
  calc (∫ x in s, Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt ((∫ x in s, A x) * (∫ x in s, B x)) := Real.le_sqrt_of_sq_le hcs
    _ = Real.sqrt (∫ x in s, A x) * Real.sqrt (∫ x in s, B x) :=
        Real.sqrt_mul (integral_nonneg_of_ae hAnn) _

/-- **Iterated Cauchy–Schwarz.**  For a weight `ρ` nonnegative on `Iz × Iθ` and functions
`A`, `B` whose weighted squares have integrable angular slices and integrable marginals,

`∫∫ ρ |A| |B| ≤ √(∫∫ ρ A²) · √(∫∫ ρ B²)`. -/
theorem cs_iterated {ρ A B : ℝ → ℝ → ℝ}
    (hρ : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ ρ z θ)
    (hsA : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => ρ z θ * (A z θ) ^ 2) Work.Spaces.Iθ)
    (hsB : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => ρ z θ * (B z θ) ^ 2) Work.Spaces.Iθ)
    (hmA : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (A z θ) ^ 2) Work.Spaces.Iz)
    (hmB : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (B z θ) ^ 2) Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * |A z θ| * |B z θ|)
      ≤ Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * (A z θ) ^ 2)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * (B z θ) ^ 2) := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  set F : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (A z θ) ^ 2 with hF
  set G : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (B z θ) ^ 2 with hG
  have hFA : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), 0 ≤ F z :=
    MeasureTheory.ae_restrict_of_forall_mem hIzm (fun z hz => MeasureTheory.setIntegral_nonneg hIθm
      (fun θ hθ => mul_nonneg (hρ z hz θ hθ) (sq_nonneg _)))
  have hGA : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), 0 ≤ G z :=
    MeasureTheory.ae_restrict_of_forall_mem hIzm (fun z hz => MeasureTheory.setIntegral_nonneg hIθm
      (fun θ hθ => mul_nonneg (hρ z hz θ hθ) (sq_nonneg _)))
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, ρ z θ * |A z θ| * |B z θ|)
        ≤ Real.sqrt (F z) * Real.sqrt (G z) := by
    intro z hz
    have hcongr : (∫ θ in Work.Spaces.Iθ, ρ z θ * |A z θ| * |B z θ|)
        = ∫ θ in Work.Spaces.Iθ, Real.sqrt (ρ z θ * (A z θ) ^ 2)
            * Real.sqrt (ρ z θ * (B z θ) ^ 2) := by
      refine integral_congr_ae (MeasureTheory.ae_restrict_of_forall_mem hIθm (fun θ hθ => ?_))
      show ρ z θ * |A z θ| * |B z θ|
        = Real.sqrt (ρ z θ * (A z θ) ^ 2) * Real.sqrt (ρ z θ * (B z θ) ^ 2)
      have hsq : (Real.sqrt (ρ z θ)) ^ 2 = ρ z θ := Real.sq_sqrt (hρ z hz θ hθ)
      have hmul : Real.sqrt (ρ z θ) * Real.sqrt (ρ z θ) = ρ z θ := by rw [← sq, hsq]
      have hA' : Real.sqrt (ρ z θ * (A z θ) ^ 2) = Real.sqrt (ρ z θ) * |A z θ| := by
        rw [Real.sqrt_mul (hρ z hz θ hθ), Real.sqrt_sq_eq_abs]
      have hB' : Real.sqrt (ρ z θ * (B z θ) ^ 2) = Real.sqrt (ρ z θ) * |B z θ| := by
        rw [Real.sqrt_mul (hρ z hz θ hθ), Real.sqrt_sq_eq_abs]
      calc ρ z θ * |A z θ| * |B z θ|
          = Real.sqrt (ρ z θ) * Real.sqrt (ρ z θ) * |A z θ| * |B z θ| := by rw [hmul]
        _ = (Real.sqrt (ρ z θ) * |A z θ|) * (Real.sqrt (ρ z θ) * |B z θ|) := by ring
        _ = Real.sqrt (ρ z θ * (A z θ) ^ 2) * Real.sqrt (ρ z θ * (B z θ) ^ 2) := by
              rw [hA', hB']
    rw [hcongr]
    exact cs_sqrt_le_ae (hsA z hz) (hsB z hz)
      (MeasureTheory.ae_restrict_of_forall_mem hIθm
        (fun θ hθ => mul_nonneg (hρ z hz θ hθ) (sq_nonneg _)))
      (MeasureTheory.ae_restrict_of_forall_mem hIθm
        (fun θ hθ => mul_nonneg (hρ z hz θ hθ) (sq_nonneg _)))
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * |A z θ| * |B z θ|)
      ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (F z) * Real.sqrt (G z) := by
    refine integral_mono_of_nonneg ?_ ?_ (MeasureTheory.ae_restrict_of_forall_mem hIzm hslice)
    · exact MeasureTheory.ae_restrict_of_forall_mem hIzm
        (fun z hz => MeasureTheory.setIntegral_nonneg hIθm
          (fun θ hθ => mul_nonneg (mul_nonneg (hρ z hz θ hθ) (abs_nonneg _)) (abs_nonneg _)))
    · have hF_sq : Integrable (fun z => Real.sqrt (F z) ^ 2) (volume.restrict Work.Spaces.Iz) :=
        hmA.congr (hFA.mono (fun z hz => (Real.sq_sqrt hz).symm))
      have hG_sq : Integrable (fun z => Real.sqrt (G z) ^ 2) (volume.restrict Work.Spaces.Iz) :=
        hmB.congr (hGA.mono (fun z hz => (Real.sq_sqrt hz).symm))
      have hF_lp : MemLp (fun z => Real.sqrt (F z)) 2 (volume.restrict Work.Spaces.Iz) :=
        (memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable
          hmA.aestronglyMeasurable)).mpr hF_sq
      have hG_lp : MemLp (fun z => Real.sqrt (G z)) 2 (volume.restrict Work.Spaces.Iz) :=
        (memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable
          hmB.aestronglyMeasurable)).mpr hG_sq
      exact memLp_one_iff_integrable.mp (hF_lp.mul hG_lp)
  calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * |A z θ| * |B z θ|)
      ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (F z) * Real.sqrt (G z) := houter
    _ ≤ Real.sqrt (∫ z in Work.Spaces.Iz, F z) * Real.sqrt (∫ z in Work.Spaces.Iz, G z) :=
        cs_sqrt_le_ae hmA hmB hFA hGA
    _ = Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * (A z θ) ^ 2)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * (B z θ) ^ 2) := by
        simp only [hF, hG]

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.sinHardyGamLeft =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular weighted Hardy inequality on the quarter interval

For `1 < c ≤ 2` and `u` of class `C¹` on `(0, π/4)` whose left trace vanishes, one has

  `∫_{(0,π/4)} sin(2θ)^{-c} u² ≤ 4/(c-1)² ∫_{(0,π/4)} sin(2θ)^{2-c} (u')²`,

as an inequality of Lebesgue integrals in `ℝ≥0∞` (so no integrability hypothesis is needed:
the left-hand side is finite as soon as the right-hand one is).  This is the *sharp* Hardy
constant for the power weight, `4/(1+η)²` with `η = c-2 ∈ (-1,0]`.

## Route

Put `η := c - 2` so that `2 + η = c`, `1 + η = c - 1` and `-η = 2 - c`.

* **Weight comparison with powers.**  Jordan's inequality `sin(2θ) ≥ (4/π)θ` on `(0,π/4)` gives,
  in the two directions needed, `sin(2θ)^{-c} ≤ (π/4)^c θ^{-c}` and `θ^{2-c} ≤ (π/4)^{2-c}
  sin(2θ)^{2-c}` (the second uses that the exponent `2-c` is nonnegative).
* **Power Hardy.**  `powerHardy_open` (the completion-of-squares / Fatou argument of
  `TT.SinHardy.Narrow`) gives `∫_{(0,π/4)} θ^{-c} u² ≤ (4/(c-1)²) ∫_{(0,π/4)} θ^{2-c} (u')²`
  directly as a `∫⁻`-inequality.
* The constants multiply to `(π/4)^c · (4/(c-1)²) · (π/4)^{2-c} = (π/4)² · 4/(c-1)² ≤ 4/(c-1)²`.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

/-- **Jordan's inequality on the quarter interval**: `θ ≤ (π/4) sin(2θ)` for `0 < θ < π/4`. -/
private lemma quarter_le_sin {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    θ ≤ (Real.pi / 4) * Real.sin (2 * θ) := by
  have h2θ0 : (0 : ℝ) ≤ 2 * θ := by linarith [hθ.1]
  have h2θπ : 2 * θ ≤ Real.pi / 2 := by linarith [hθ.2, Real.pi_pos]
  have h := Real.mul_le_sin h2θ0 h2θπ
  have heq : (Real.pi / 4) * (2 / Real.pi * (2 * θ)) = θ := by
    field_simp
    ring
  calc θ = (Real.pi / 4) * (2 / Real.pi * (2 * θ)) := heq.symm
    _ ≤ (Real.pi / 4) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left h (by positivity)

/-- `sin(2θ)^{-c} ≤ (π/4)^c θ^{-c}` on `(0,π/4)` for `c > 0`. -/
private lemma sin_pow_neg_le {c : ℝ} (hc : 0 < c) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    (Real.sin (2 * θ)) ^ (-c) ≤ (Real.pi / 4) ^ c * θ ^ (-c) := by
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hj := quarter_le_sin hθ
  have hdiv : θ / Real.sin (2 * θ) ≤ Real.pi / 4 := by
    rw [div_le_iff₀ hsinpos]; linarith [hj]
  have h1 : (θ / Real.sin (2 * θ)) ^ c ≤ (Real.pi / 4) ^ c :=
    Real.rpow_le_rpow (div_nonneg hθ.1.le hsinpos.le) hdiv hc.le
  have h2 : (θ / Real.sin (2 * θ)) ^ c = θ ^ c * (Real.sin (2 * θ)) ^ (-c) := by
    rw [Real.div_rpow hθ.1.le hsinpos.le, div_eq_mul_inv, ← Real.rpow_neg hsinpos.le]
  have h3 : θ ^ c * (Real.sin (2 * θ)) ^ (-c) ≤ (Real.pi / 4) ^ c := h2 ▸ h1
  have hθc : (0 : ℝ) < θ ^ c := Real.rpow_pos_of_pos hθ.1 c
  have h4 : (Real.sin (2 * θ)) ^ (-c) ≤ (Real.pi / 4) ^ c / θ ^ c := by
    rw [le_div_iff₀ hθc]; linarith [h3]
  have h5 : (Real.pi / 4) ^ c / θ ^ c = (Real.pi / 4) ^ c * θ ^ (-c) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hθ.1.le]
  linarith [h4, h5]

/-- `θ^{2-c} ≤ (π/4)^{2-c} sin(2θ)^{2-c}` on `(0,π/4)` for `c ≤ 2`. -/
private lemma pow_le_sin_pow {c : ℝ} (hc2 : c ≤ 2) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    θ ^ (2 - c) ≤ (Real.pi / 4) ^ (2 - c) * (Real.sin (2 * θ)) ^ (2 - c) := by
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hj := quarter_le_sin hθ
  have h2c : (0 : ℝ) ≤ 2 - c := by linarith
  calc θ ^ (2 - c) ≤ ((Real.pi / 4) * Real.sin (2 * θ)) ^ (2 - c) :=
        Real.rpow_le_rpow hθ.1.le hj h2c
    _ = (Real.pi / 4) ^ (2 - c) * (Real.sin (2 * θ)) ^ (2 - c) :=
        Real.mul_rpow (by positivity) hsinpos.le

theorem sinHardyGamLeft (c : ℝ) (hc1 : 1 < c) (hc2 : c ≤ 2) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Set.Ioo (0 : ℝ) (Real.pi / 4)))
    (h0 : Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      ≤ ENNReal.ofReal (4 / (c - 1) ^ 2) *
        (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := by
  have h4pos : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hc0 : (0 : ℝ) < c := by linarith
  have hKpos : (0 : ℝ) < 4 / (c - 1) ^ 2 := by positivity
  have hpi_nn : (0 : ℝ) ≤ (Real.pi / 4) ^ c := (Real.rpow_pos_of_pos h4pos c).le
  have hpi_nn2 : (0 : ℝ) ≤ (Real.pi / 4) ^ (2 - c) := (Real.rpow_pos_of_pos h4pos (2 - c)).le
  -- ## Step A: compare `sin(2θ)^{-c}` with the power `θ^{-c}`
  have hA : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      ≤ ENNReal.ofReal ((Real.pi / 4) ^ c) *
        (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), ENNReal.ofReal (θ ^ (-c) * (u θ) ^ 2)) := by
    rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine MeasureTheory.lintegral_mono_ae ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall fun θ hθ => ?_)
    have hcmp := sin_pow_neg_le hc0 hθ
    rw [← ENNReal.ofReal_mul hpi_nn]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2
        ≤ ((Real.pi / 4) ^ c * θ ^ (-c)) * (u θ) ^ 2 :=
          mul_le_mul_of_nonneg_right hcmp (sq_nonneg _)
      _ = (Real.pi / 4) ^ c * (θ ^ (-c) * (u θ) ^ 2) := by ring
  -- ## Step B: the power-weighted Hardy inequality
  have hB := Work.FTS.EllipticEst.TT.SinHardy.NarrowAlt.powerHardy_open
      (a := Real.pi / 4) (η := c - 2) h4pos (by linarith) (by linarith)
      (hu.continuousOn.aemeasurable measurableSet_Ioo) hu h0
  have hB' : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), ENNReal.ofReal (θ ^ (-c) * (u θ) ^ 2))
      ≤ ENNReal.ofReal (4 / (c - 1) ^ 2) *
        (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ENNReal.ofReal (θ ^ (2 - c) * (deriv u θ) ^ 2)) := by
    have e1 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ENNReal.ofReal (u θ ^ 2 * θ ^ (-(2 + (c - 2)))))
        = (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), ENNReal.ofReal (θ ^ (-c) * (u θ) ^ 2)) := by
      refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      congr 1
      rw [show -(2 + (c - 2)) = -c by ring]
      ring
    have e2 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ENNReal.ofReal (deriv u θ ^ 2 * θ ^ (-(c - 2))))
        = (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ENNReal.ofReal (θ ^ (2 - c) * (deriv u θ) ^ 2)) := by
      refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      congr 1
      rw [show -(c - 2) = 2 - c by ring]
      ring
    rw [e1, e2] at hB
    rw [show (4 : ℝ) / (1 + (c - 2)) ^ 2 = 4 / (c - 1) ^ 2 by ring] at hB
    exact hB
  -- ## Step C: compare the power `θ^{2-c}` with `sin(2θ)^{2-c}`
  have hC : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), ENNReal.ofReal (θ ^ (2 - c) * (deriv u θ) ^ 2))
      ≤ ENNReal.ofReal ((Real.pi / 4) ^ (2 - c)) *
        (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
          ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := by
    rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine MeasureTheory.lintegral_mono_ae ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall fun θ hθ => ?_)
    have hcmp := pow_le_sin_pow hc2 hθ
    rw [← ENNReal.ofReal_mul hpi_nn2]
    refine ENNReal.ofReal_le_ofReal ?_
    calc θ ^ (2 - c) * (deriv u θ) ^ 2
        ≤ ((Real.pi / 4) ^ (2 - c) * (Real.sin (2 * θ)) ^ (2 - c)) * (deriv u θ) ^ 2 :=
          mul_le_mul_of_nonneg_right hcmp (sq_nonneg _)
      _ = (Real.pi / 4) ^ (2 - c) * ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2) := by ring
  -- ## the constant bookkeeping
  have hAD : (Real.pi / 4) ^ c * (Real.pi / 4) ^ (2 - c) = (Real.pi / 4) ^ 2 := by
    rw [← Real.rpow_add h4pos c (2 - c)]
    norm_num
  have hmerge : ∀ X : ℝ≥0∞, ENNReal.ofReal ((Real.pi / 4) ^ c) *
        (ENNReal.ofReal (4 / (c - 1) ^ 2) * (ENNReal.ofReal ((Real.pi / 4) ^ (2 - c)) * X))
      = ENNReal.ofReal ((Real.pi / 4) ^ 2 * (4 / (c - 1) ^ 2)) * X := by
    intro X
    have hkey : (Real.pi / 4) ^ c * (4 / (c - 1) ^ 2) * (Real.pi / 4) ^ (2 - c)
        = (Real.pi / 4) ^ 2 * (4 / (c - 1) ^ 2) := by
      rw [← hAD]; ring
    calc ENNReal.ofReal ((Real.pi / 4) ^ c) *
          (ENNReal.ofReal (4 / (c - 1) ^ 2) * (ENNReal.ofReal ((Real.pi / 4) ^ (2 - c)) * X))
        = ENNReal.ofReal ((Real.pi / 4) ^ c * (4 / (c - 1) ^ 2) * (Real.pi / 4) ^ (2 - c)) * X := by
          rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hpi_nn,
            ← ENNReal.ofReal_mul (mul_nonneg hpi_nn hKpos.le)]
      _ = ENNReal.ofReal ((Real.pi / 4) ^ 2 * (4 / (c - 1) ^ 2)) * X := by rw [hkey]
  -- ## assembly
  calc (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
        ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      ≤ ENNReal.ofReal ((Real.pi / 4) ^ c) *
          (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), ENNReal.ofReal (θ ^ (-c) * (u θ) ^ 2)) := hA
    _ ≤ ENNReal.ofReal ((Real.pi / 4) ^ c) * (ENNReal.ofReal (4 / (c - 1) ^ 2) *
          (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal (θ ^ (2 - c) * (deriv u θ) ^ 2))) :=
        mul_le_mul_right hB' (ENNReal.ofReal ((Real.pi / 4) ^ c))
    _ ≤ ENNReal.ofReal ((Real.pi / 4) ^ c) * (ENNReal.ofReal (4 / (c - 1) ^ 2) *
          (ENNReal.ofReal ((Real.pi / 4) ^ (2 - c)) *
            (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
              ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)))) :=
        mul_le_mul_right (mul_le_mul_right hC (ENNReal.ofReal (4 / (c - 1) ^ 2)))
          (ENNReal.ofReal ((Real.pi / 4) ^ c))
    _ = ENNReal.ofReal ((Real.pi / 4) ^ 2 * (4 / (c - 1) ^ 2)) *
          (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := hmerge _
    _ ≤ ENNReal.ofReal (4 / (c - 1) ^ 2) *
          (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
            ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := by
        refine mul_le_mul_left ?_ _
        refine ENNReal.ofReal_le_ofReal ?_
        have hle1 : (Real.pi / 4) ≤ 1 := by linarith [Real.pi_lt_four]
        have hsq1 : ((Real.pi / 4)) ^ 2 ≤ 1 := by nlinarith [h4pos.le, hle1]
        nlinarith [hsq1, hKpos.le]

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.truncBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval

open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

/-! ## The radial weight `w` and the auxiliary function `t ↦ t (w t)²`

Everything is completely elementary: `(w t)² = (1+t)⁴/t⁴`, so `t (w t)² = (1+t)⁴/t³`, whose
derivative is `(1+t)³ (t-3)/t⁴`, and `|t - 3| ≤ 4 (1+t)` on `(0,∞)` gives the pointwise bound
`|deriv| ≤ 4 (w t)²` used in `truncBound`. -/

/-- `(w t)² = (1+t)⁴/t⁴` for the radial weight `w t = (1+t)²/t²` (the identity also holds at
`t = 0`, since both sides vanish by totality of division). -/
lemma w_sq_eq (t : ℝ) : (Work.Spaces.w t) ^ 2 = (1 + t) ^ 4 / t ^ 4 := by
  rw [Work.Spaces.w, div_pow, ← pow_mul, ← pow_mul]

/-- The derivative of `t ↦ t (w t)²` on `(0,∞)`: `t (w t)² = (1+t)⁴/t³`. -/
lemma deriv_tmul_w_sq {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun s : ℝ => s * (Work.Spaces.w s) ^ 2)
      (((1 + z) ^ 3 * (z - 3)) / z ^ 4) z := by
  have hcongr : (fun s : ℝ => s * (Work.Spaces.w s) ^ 2)
      =ᶠ[𝓝 z] (fun s : ℝ => (1 + s) ^ 4 / s ^ 3) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with s _hs
    have hs4 : (Work.Spaces.w s) ^ 2 = (1 + s) ^ 4 / s ^ 4 := w_sq_eq s
    rw [hs4]
    field_simp
  have h1 : HasDerivAt (fun s : ℝ => (1 + s) ^ 4) (4 * (1 + z) ^ 3) z := by
    have h : HasDerivAt (fun s : ℝ => 1 + s) (1 : ℝ) z := by
      simpa using (hasDerivAt_id z).const_add (1 : ℝ)
    have h3 := h.pow 4
    norm_num at h3
    exact h3
  have h2 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * z ^ 2) z := by
    have h3 := (hasDerivAt_id z).pow 3
    norm_num at h3
    exact h3
  have h3 := h1.div h2 (pow_ne_zero 3 (ne_of_gt hz))
  have hv : (4 * (1 + z) ^ 3 * z ^ 3 - (1 + z) ^ 4 * (3 * z ^ 2)) / (z ^ 3) ^ 2
      = ((1 + z) ^ 3 * (z - 3)) / z ^ 4 := by
    field_simp
    ring
  rw [← hv]
  exact h3.congr_of_eventuallyEq hcongr

/-- The pointwise bound on the derivative of `t ↦ t (w t)²` on `(0,∞)`:
`|(1+t)³ (t-3)/t⁴| ≤ 4 (w t)²`, because `|t-3| ≤ 4(1+t)`. -/
lemma abs_deriv_tmul_w_sq_le {z : ℝ} (hz : 0 < z) :
    |((1 + z) ^ 3 * (z - 3)) / z ^ 4| ≤ 4 * (Work.Spaces.w z) ^ 2 := by
  rw [w_sq_eq]
  have hz4 : (0 : ℝ) < z ^ 4 := pow_pos hz 4
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hb : |z - 3| ≤ 4 * (1 + z) := by
    rw [abs_le]; constructor <;> linarith
  have hstep : |((1 + z) ^ 3 * (z - 3)) / z ^ 4| = (1 + z) ^ 3 * |z - 3| / z ^ 4 := by
    rw [abs_div, abs_mul, abs_pow, abs_of_pos h1z, abs_of_pos hz4]
  rw [hstep]
  calc (1 + z) ^ 3 * |z - 3| / z ^ 4
      ≤ (1 + z) ^ 3 * (4 * (1 + z)) / z ^ 4 := by
        apply div_le_div_of_nonneg_right _ hz4.le
        exact mul_le_mul_of_nonneg_left hb (pow_nonneg h1z.le 3)
    _ = 4 * ((1 + z) ^ 4 / z ^ 4) := by
        field_simp

/-- Truncated form of the radial self-pairing bound.  With
`H t = (w t)^2 * (Y t)^2`, `G t = ((w t)^2 * (Y t)^2) * t` and
`F z = (w z)^2 * ((z * deriv Y z) * Y z)`, one has on `(0,∞)`
`deriv (fun t => t * (w t)^2) t = (1+t)^3 * (t-3) / t^4` (from `(w t)^2 = (1+t)^4/t^4`),
so that `deriv G t = deriv (fun s => s * (w s)^2) t * (Y t)^2 + 2 * F t`, and
`|deriv (fun t => t * (w t)^2) t| ≤ 4 * (w t)^2` for `t > 0` (as `|t-3| ≤ 4*(1+t)`).
Integrating the derivative identity over `[a,b] ⊂ (0,∞)` (FTC) then gives the bound below.
Requires `open scoped Interval` for the `a..b` notation. -/
theorem truncBound {Y : ℝ → ℝ} (hY : ContDiffOn ℝ 1 Y (Set.Ioi 0)) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    |∫ z in a..b, (Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z)|
      ≤ (1 / 2) * (((Work.Spaces.w b) ^ 2 * (Y b) ^ 2) * b
            + ((Work.Spaces.w a) ^ 2 * (Y a) ^ 2) * a)
        + 2 * ∫ z in a..b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := by
  have huI : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun z hz => lt_of_lt_of_le ha hz.1
  have hYd : ∀ z ∈ Set.Icc a b, HasDerivAt Y (deriv Y z) z := fun z hz =>
    ((hY.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds (hsub hz))).hasDerivAt
  have hYc : ContinuousOn Y (Set.Icc a b) := (hY.continuousOn).mono hsub
  have hYdc : ContinuousOn (deriv Y) (Set.Icc a b) :=
    (hY.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  have hw : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Icc a b) := by
    change ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Icc a b)
    refine ContinuousOn.div ?_ ?_ (fun z hz => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha hz.1)))
    · fun_prop
    · fun_prop
  have hW'c : ContinuousOn (fun z : ℝ => ((1 + z) ^ 3 * (z - 3)) / z ^ 4) (Set.Icc a b) := by
    refine ContinuousOn.div ?_ ?_ (fun z hz => pow_ne_zero 4 (ne_of_gt (lt_of_lt_of_le ha hz.1)))
    · fun_prop
    · fun_prop
  have hInt : ∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc a b) → IntervalIntegrable f volume a b :=
    fun f hf => (show ContinuousOn f (Set.uIcc a b) from by rw [huI]; exact hf).intervalIntegrable
  have habsW' : ∀ z ∈ Set.Icc a b,
      |((1 + z) ^ 3 * (z - 3)) / z ^ 4| ≤ 4 * (Work.Spaces.w z) ^ 2 :=
    fun z hz => abs_deriv_tmul_w_sq_le (hsub hz)
  have hWd : ∀ z ∈ Set.Icc a b, HasDerivAt (fun s : ℝ => s * (Work.Spaces.w s) ^ 2)
      (((1 + z) ^ 3 * (z - 3)) / z ^ 4) z := fun z hz => deriv_tmul_w_sq (hsub hz)
  -- the derivative of `t ↦ t (w t)² (Y t)²`
  have hGd : ∀ z ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => t * (Work.Spaces.w t) ^ 2 * (Y t) ^ 2)
        (((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2
          + 2 * ((Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z))) z := by
    intro z hz
    rw [huI] at hz
    have h1 := hWd z hz
    have h2 := (hYd z hz).pow 2
    have h3 := h1.mul h2
    have hfun : (fun t : ℝ => t * (Work.Spaces.w t) ^ 2 * (Y t) ^ 2)
        = (fun s : ℝ => s * (Work.Spaces.w s) ^ 2) * (fun s : ℝ => (Y s) ^ 2) := by
      funext s; rfl
    rw [hfun]
    convert h3 using 1
    simp only [Pi.pow_apply]
    ring
  have hIntI1 : IntervalIntegrable
      (fun z : ℝ => ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2) volume a b :=
    hInt _ (hW'c.mul (hYc.pow 2))
  have hIntI2 : IntervalIntegrable
      (fun z : ℝ => 2 * ((Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z))) volume a b :=
    hInt _ (continuousOn_const.mul ((hw.pow 2).mul ((continuousOn_id.mul hYdc).mul hYc)))
  have hIntG' : IntervalIntegrable
      (fun z : ℝ => ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2
        + 2 * ((Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z))) volume a b :=
    hInt _ ((hW'c.mul (hYc.pow 2)).add (continuousOn_const.mul
      ((hw.pow 2).mul ((continuousOn_id.mul hYdc).mul hYc))))
  -- FTC for `t ↦ t (w t)² (Y t)²`
  have hFTC : ∫ z in a..b, (((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2
        + 2 * ((Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z)))
      = b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2
        - a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro z hz; exact hGd z hz
    · exact hIntG'
  have hsplit : (∫ z in a..b, (((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2
        + 2 * ((Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z))))
      = (∫ z in a..b, ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2)
        + 2 * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z)) := by
    rw [intervalIntegral.integral_add hIntI1 hIntI2, intervalIntegral.integral_const_mul]
  -- bound on the `(w')`-half
  have hI1 : |∫ z in a..b, ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2|
      ≤ 4 * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by
    calc |∫ z in a..b, ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2|
        ≤ ∫ z in a..b, |((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2| :=
          intervalIntegral.abs_integral_le_integral_abs hab
      _ = ∫ z in a..b, |((1 + z) ^ 3 * (z - 3)) / z ^ 4| * (Y z) ^ 2 := by
          apply intervalIntegral.integral_congr
          intro z _
          dsimp only
          rw [abs_mul, abs_of_nonneg (sq_nonneg (Y z))]
      _ ≤ ∫ z in a..b, 4 * ((Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by
          apply intervalIntegral.integral_mono_on hab
          · exact hInt _ ((hW'c.abs).mul (hYc.pow 2))
          · exact hInt _ (continuousOn_const.mul ((hw.pow 2).mul (hYc.pow 2)))
          · intro z hz
            calc |((1 + z) ^ 3 * (z - 3)) / z ^ 4| * (Y z) ^ 2
                ≤ (4 * (Work.Spaces.w z) ^ 2) * (Y z) ^ 2 :=
                  mul_le_mul_of_nonneg_right (habsW' z hz) (sq_nonneg (Y z))
              _ = 4 * ((Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by ring
      _ = 4 * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by
          rw [intervalIntegral.integral_const_mul]
  -- the integration-by-parts identity for `∫ w² (z Y') Y`
  have hkey : 2 * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z))
      = (b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2
          - a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2)
        - ∫ z in a..b, ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2 := by
    linarith [hFTC, hsplit]
  have hI2 : (∫ z in a..b, (Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z))
      = (1 / 2) * ((b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2
          - a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2)
        - (∫ z in a..b, ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2)) := by
    linarith [hkey]
  rw [hI2]
  have hB1 : (0 : ℝ) ≤ b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2 :=
    mul_nonneg (mul_nonneg (le_trans ha.le hab) (sq_nonneg _)) (sq_nonneg _)
  have hB2 : (0 : ℝ) ≤ a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2 :=
    mul_nonneg (mul_nonneg ha.le (sq_nonneg _)) (sq_nonneg _)
  have hB : |b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2 - a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2|
      ≤ b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2 + a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2 := by
    have := abs_sub_le (b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2) 0
      (a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2)
    simpa [abs_of_nonneg hB1, abs_of_nonneg hB2] using this
  calc |(1 / 2) * ((b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2
          - a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2)
        - (∫ z in a..b, ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2))|
      = (1 / 2) * |(b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2
          - a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2)
        - (∫ z in a..b, ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2)| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ (1 / 2) * (|b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2
          - a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2|
        + |∫ z in a..b, ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2|) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          simpa using abs_sub_le (b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2
            - a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2) 0
            (∫ z in a..b, ((1 + z) ^ 3 * (z - 3)) / z ^ 4 * (Y z) ^ 2)
    _ ≤ (1 / 2) * ((b * (Work.Spaces.w b) ^ 2 * (Y b) ^ 2
          + a * (Work.Spaces.w a) ^ 2 * (Y a) ^ 2)
        + 4 * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          linarith [hB, hI1]
    _ = (1 / 2) * (((Work.Spaces.w b) ^ 2 * (Y b) ^ 2) * b
          + ((Work.Spaces.w a) ^ 2 * (Y a) ^ 2) * a)
        + 2 * ∫ z in a..b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := by ring

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkPairCS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open MeasureTheory



end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkShiftHigh_absCS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

/-- Pointwise Cauchy–Schwarz for the two weighted squares: if `ρ ≥ 0` then the modulus of the
pairing `g·(ρ·A·B)` equals `√(g²·ρ·A²)·√(ρ·B²)`. -/
theorem fkShiftHigh_sqrt_eq_abs {g : ℝ → ℝ} {A B ρ : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : 0 ≤ ρ p.1 p.2) :
    ‖g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)‖
      = Real.sqrt ((g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2)
        * Real.sqrt (ρ p.1 p.2 * (B p.1 p.2) ^ 2) := by
  have hFnn : 0 ≤ (g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hp) (sq_nonneg _)
  have hGnn : 0 ≤ ρ p.1 p.2 * (B p.1 p.2) ^ 2 := mul_nonneg hp (sq_nonneg _)
  rw [Real.norm_eq_abs, ← Real.sqrt_mul hFnn (ρ p.1 p.2 * (B p.1 p.2) ^ 2),
    show (g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2 * (ρ p.1 p.2 * (B p.1 p.2) ^ 2)
        = (g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)) ^ 2 from by ring,
    Real.sqrt_sq_eq_abs]

theorem fkShiftHigh_absCS {μ : MeasureTheory.Measure (ℝ × ℝ)} {g : ℝ → ℝ}
    {A B ρ : ℝ → ℝ → ℝ}
    (hρ : ∀ᵐ p ∂μ, 0 ≤ ρ p.1 p.2)
    (haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)) μ)
    (hF : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2) μ)
    (hG : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ρ p.1 p.2 * (B p.1 p.2) ^ 2) μ) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)) μ ∧
      |∫ p, g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2) ∂μ|
        ≤ Real.sqrt (∫ p, (g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2 ∂μ)
          * Real.sqrt (∫ p, ρ p.1 p.2 * (B p.1 p.2) ^ 2 ∂μ) := by
  have hae : (fun p : ℝ × ℝ => ‖g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)‖)
      =ᵐ[μ] (fun p : ℝ × ℝ => Real.sqrt ((g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2)
        * Real.sqrt (ρ p.1 p.2 * (B p.1 p.2) ^ 2)) :=
    hρ.mono fun p hp => fkShiftHigh_sqrt_eq_abs hp
  -- the dominating function `(F + G)/2`
  have hbound : (fun p : ℝ × ℝ => ‖g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)‖)
      ≤ᵐ[μ] (fun p : ℝ × ℝ => ((g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2
        + ρ p.1 p.2 * (B p.1 p.2) ^ 2) / 2) := by
    filter_upwards [hae, hρ] with p hp hpρ
    rw [hp]
    have hFnn : 0 ≤ (g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2 :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hpρ) (sq_nonneg _)
    have hGnn : 0 ≤ ρ p.1 p.2 * (B p.1 p.2) ^ 2 := mul_nonneg hpρ (sq_nonneg _)
    nlinarith [sq_nonneg (Real.sqrt ((g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2)
        - Real.sqrt (ρ p.1 p.2 * (B p.1 p.2) ^ 2)),
      Real.sq_sqrt hFnn, Real.sq_sqrt hGnn]
  have hInt : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)) μ :=
    MeasureTheory.Integrable.mono' ((hF.add hG).div_const 2) haesm hbound
  refine ⟨hInt, ?_⟩
  have hcongr : ∫ p, ‖g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)‖ ∂μ
      = ∫ p, Real.sqrt ((g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2)
        * Real.sqrt (ρ p.1 p.2 * (B p.1 p.2) ^ 2) ∂μ :=
    MeasureTheory.integral_congr_ae hae
  have hFnn_ae : 0 ≤ᵐ[μ]
      (fun p : ℝ × ℝ => (g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2) :=
    hρ.mono fun p hp => mul_nonneg (mul_nonneg (sq_nonneg _) hp) (sq_nonneg _)
  have hGnn_ae : 0 ≤ᵐ[μ] (fun p : ℝ × ℝ => ρ p.1 p.2 * (B p.1 p.2) ^ 2) :=
    hρ.mono fun p hp => mul_nonneg hp (sq_nonneg _)
  calc |∫ p, g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2) ∂μ|
      = ‖∫ p, g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2) ∂μ‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ p, ‖g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)‖ ∂μ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ p, Real.sqrt ((g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2)
          * Real.sqrt (ρ p.1 p.2 * (B p.1 p.2) ^ 2) ∂μ := hcongr
    _ ≤ Real.sqrt (∫ p, (g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2 ∂μ)
          * Real.sqrt (∫ p, ρ p.1 p.2 * (B p.1 p.2) ^ 2 ∂μ) :=
        Work.FTS.TransportS.TvUniform.integral_sqrt_mul_sqrt_le μ hFnn_ae hGnn_ae hF hG

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumB1FiveArith =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

/-- The purely numerical form of the coefficient bound used in `rowSumB1FiveArith`:
for `0 < α ≤ 1` one has `√3 · √(4/π + 200/(γ-1)) ≤ 100 α^{-1/2}`, where `γ = gam α = 1 + α/10`.

Since `γ - 1 = α/10`, the bracket is `4/π + 2000/α`; it is enough that
`3 · (4/π + 2000/α) ≤ 10000/α`, which holds because `α ≤ 1` and `π > 3`. -/
private lemma sqrt_three_mul_sqrt_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Real.sqrt 3 * Real.sqrt (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
      ≤ 100 * α ^ (-(1 / 2 : ℝ)) := by
  have hg : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
  rw [hg]
  have h200 : 200 / (α / 10) = 2000 / α := by field_simp; norm_num
  rw [h200]
  rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num)]
  have hS : (0 : ℝ) ≤ 100 * α ^ (-(1 / 2 : ℝ)) := by positivity
  rw [Real.sqrt_le_left hS]
  have hSsq : (100 * α ^ (-(1 / 2 : ℝ))) ^ 2 = 10000 / α := by
    rw [mul_pow]
    have h2 : (α ^ (-(1 / 2 : ℝ))) ^ 2 = α ^ (-(1 : ℝ)) := by
      rw [sq, ← Real.rpow_add hα]
      norm_num
    rw [h2, Real.rpow_neg_one]
    norm_num
    field_simp
  rw [hSsq]
  have h3 : 3 * (4 / Real.pi + 2000 / α) ≤ 10000 / α := by
    have h1 : 3 * (4 / Real.pi + 2000 / α) ≤ 3 * (10000 / (3 * α)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      field_simp
      nlinarith [Real.pi_gt_three, Real.pi_pos]
    have h2 : 3 * (10000 / (3 * α)) = 10000 / α := by field_simp
    linarith
  exact h3

theorem rowSumB1FiveArith {α M K6 N P Q : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hM : 0 ≤ M) (hK6 : 0 ≤ K6) (hN : 0 ≤ N)
    (hP : P ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1)) * K6 ^ 2)
    (hQ : Q ≤ N ^ 2) :
    Real.sqrt 3 * M * (Real.sqrt P * Real.sqrt Q)
      ≤ 100 * α ^ (-(1 / 2 : ℝ)) * M * K6 * N := by
  set Cf : ℝ := 4 / Real.pi + 200 / (Work.Spaces.gam α - 1) with hCf
  have hgam : (0 : ℝ) < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one α]; linarith
  have hCf_nonneg : 0 ≤ Cf := by
    rw [hCf]
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    positivity
  -- bound `√P` by `√Cf · K6` and `√Q` by `N`
  have hP' : Real.sqrt P ≤ Real.sqrt Cf * K6 := by
    have h1 : Real.sqrt P ≤ Real.sqrt (Cf * K6 ^ 2) := Real.sqrt_le_sqrt hP
    rwa [Real.sqrt_mul hCf_nonneg, Real.sqrt_sq hK6] at h1
  have hQ' : Real.sqrt Q ≤ N := by
    have h1 : Real.sqrt Q ≤ Real.sqrt (N ^ 2) := Real.sqrt_le_sqrt hQ
    rwa [Real.sqrt_sq hN] at h1
  have hcoef : Real.sqrt 3 * Real.sqrt Cf ≤ 100 * α ^ (-(1 / 2 : ℝ)) := by
    rw [hCf]
    exact sqrt_three_mul_sqrt_le hα hα1
  have hsqrtCKN : 0 ≤ Real.sqrt Cf * K6 := mul_nonneg (Real.sqrt_nonneg Cf) hK6
  have hSM : 0 ≤ Real.sqrt 3 * M := mul_nonneg (Real.sqrt_nonneg 3) hM
  have hcoef_nonneg : 0 ≤ 100 * α ^ (-(1 / 2 : ℝ)) := by positivity
  calc Real.sqrt 3 * M * (Real.sqrt P * Real.sqrt Q)
      ≤ Real.sqrt 3 * M * (Real.sqrt Cf * K6 * N) := by
        apply mul_le_mul_of_nonneg_left _ hSM
        exact mul_le_mul hP' hQ' (Real.sqrt_nonneg Q) hsqrtCKN
    _ = (Real.sqrt 3 * Real.sqrt Cf) * (M * K6 * N) := by ring
    _ ≤ (100 * α ^ (-(1 / 2 : ℝ))) * (M * K6 * N) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = 100 * α ^ (-(1 / 2 : ℝ)) * M * K6 * N := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.setIntegral_Ioc_le_of_uniform_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

theorem setIntegral_Ioc_le_of_uniform_bound {ε C K : ℝ} (hε : 0 < ε)
    {F G : ℝ → ℝ}
    (hFint : MeasureTheory.IntegrableOn F (Set.Ioc (0 : ℝ) ε))
    (hGint : MeasureTheory.IntegrableOn G (Set.Ioc (0 : ℝ) ε))
    (hineq : ∀ δ ∈ Set.Ioo (0 : ℝ) ε,
      (∫ x in Set.Ioc δ ε, F x) ≤ C * (∫ x in Set.Ioc δ ε, G x) + K) :
    (∫ x in Set.Ioc (0 : ℝ) ε, F x) ≤ C * (∫ x in Set.Ioc (0 : ℝ) ε, G x) + K := by
  -- We exhaust `Ioc 0 ε` by the increasing family `Ioc (ε/(n+2)) ε` and pass to the limit
  -- in the hypothesis, which holds for every point of that family.
  have hunion : (⋃ n : ℕ, Set.Ioc (ε / ((n : ℝ) + 2)) ε) = Set.Ioc (0 : ℝ) ε := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ioc]
    constructor
    · rintro ⟨n, hn1, hn2⟩
      exact ⟨lt_of_lt_of_le (by positivity) (le_of_lt hn1), hn2⟩
    · rintro ⟨hx0, hxε⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (ε / x)
      refine ⟨n, ?_, hxε⟩
      have h3 : ε < (n : ℝ) * x := (div_lt_iff₀ hx0).mp hn
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
      nlinarith [h3, hx0]
  have hs : ∀ n : ℕ, MeasurableSet (Set.Ioc (ε / ((n : ℝ) + 2)) ε) := fun _ => measurableSet_Ioc
  have hmono : Monotone (fun n : ℕ => Set.Ioc (ε / ((n : ℝ) + 2)) ε) := by
    intro n m hnm x hx
    simp only [Set.mem_Ioc] at hx ⊢
    have hle : ε / ((m : ℝ) + 2) ≤ ε / ((n : ℝ) + 2) :=
      div_le_div_of_nonneg_left hε.le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hnm 2)
    exact ⟨lt_of_le_of_lt hle hx.1, hx.2⟩
  have hF_tend : Filter.Tendsto (fun n : ℕ => ∫ x in Set.Ioc (ε / ((n : ℝ) + 2)) ε, F x)
      Filter.atTop (nhds (∫ x in Set.Ioc (0 : ℝ) ε, F x)) := by
    have h := MeasureTheory.tendsto_setIntegral_of_monotone hs hmono (by rw [hunion]; exact hFint)
    rwa [hunion] at h
  have hG_tend : Filter.Tendsto (fun n : ℕ => ∫ x in Set.Ioc (ε / ((n : ℝ) + 2)) ε, G x)
      Filter.atTop (nhds (∫ x in Set.Ioc (0 : ℝ) ε, G x)) := by
    have h := MeasureTheory.tendsto_setIntegral_of_monotone hs hmono (by rw [hunion]; exact hGint)
    rwa [hunion] at h
  have hR_tend : Filter.Tendsto
      (fun n : ℕ => C * (∫ x in Set.Ioc (ε / ((n : ℝ) + 2)) ε, G x) + K) Filter.atTop
      (nhds (C * (∫ x in Set.Ioc (0 : ℝ) ε, G x) + K)) :=
    (tendsto_const_nhds.mul hG_tend).add tendsto_const_nhds
  refine le_of_tendsto_of_tendsto hF_tend hR_tend (Filter.Eventually.of_forall fun n => ?_)
  exact hineq _ ⟨by positivity,
    div_lt_self hε (by have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)⟩

end Work.FTS.StrongPersist.N6Trans.SixRoute
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.slicePtBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

set_option maxHeartbeats 1000000

/-! ## Elementary `rpow` and `sin` facts on `(0, π/2)` -/

/-- `(x ^ a) ^ 2 = x ^ (2 * a)` for `x > 0`. -/
private lemma spb_rpow_sq (x a : ℝ) (hx : 0 < x) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [pow_two, ← Real.rpow_add hx, show a + a = 2 * a by ring]

/-- `sin (2x) ≥ 0` on `(0, π/2)`. -/
private lemma spb_sin_nonneg {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 ≤ Real.sin (2 * x) := by
  refine Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1]) ?_
  linarith [hx.2, Real.pi_pos]

/-- `sin (2x) > 0` on a subinterval `(a,b) ⊆ (0, π/2)`. -/
private lemma spb_sin_pos {a b x : ℝ} (hx : x ∈ Set.Ioo a b) (ha : 0 < a)
    (hb : b < Real.pi / 2) : 0 < Real.sin (2 * x) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1, ha]) (by linarith [hx.2, hb, Real.pi_pos])

/-! ## The Cauchy–Schwarz step on a subinterval of `(0, π/2)` -/

/-- **Weighted Cauchy–Schwarz on a subinterval.**  For `a ≤ b` with `(a,b) ⊆ (0,π/2)`,
`(∫_a^b |f'|)² ≤ (∫_{(0,π/2)} (f')² sin(2θ)^{1-β}) · (∫_{(0,π/2)} sin(2θ)^{β-1})`,
as long as the two whole-interval integrals are finite.

Route: split `|f'| = (|f'| sin^{(1-β)/2}) · sin^{(β-1)/2}` and apply Cauchy–Schwarz
(`Work.Spaces.cs_integral`) on the subinterval `(a,b)`, then bound the two subinterval
integrals by the whole ones with `setIntegral_mono_set`. -/
private lemma cs_subinterval {β : ℝ} {f : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) (Set.Ioo 0 (Real.pi / 2)))
    (hintB : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (β - 1)) (Set.Ioo 0 (Real.pi / 2)))
    {a b : ℝ} (_hab : a ≤ b) (ha : 0 < a) (hb : b < Real.pi / 2) :
    (∫ x in Set.Ioo a b, |deriv f x|) ^ 2 ≤
      (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β)) *
        (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (Real.sin (2 * x)) ^ (β - 1)) := by
  have hsub : Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨lt_trans ha hx.1, lt_trans hx.2 hb⟩
  have hsub_ae : Set.Ioo a b ≤ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    Filter.Eventually.of_forall fun x hx => hsub hx
  have hsinpos : ∀ x ∈ Set.Ioo a b, 0 < Real.sin (2 * x) :=
    fun x hx => spb_sin_pos hx ha hb
  have hsinfull : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ Real.sin (2 * x) :=
    fun x hx => spb_sin_nonneg hx
  have hIntF : MeasureTheory.IntegrableOn
      (fun x => (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β)) (Set.Ioo a b) :=
    hint.mono_set hsub
  have hIntS : MeasureTheory.IntegrableOn
      (fun x => (Real.sin (2 * x)) ^ (β - 1)) (Set.Ioo a b) := hintB.mono_set hsub
  have hmu : Measurable (fun x : ℝ => |deriv f x| * (Real.sin (2 * x)) ^ ((1 - β) / 2)) := by
    measurability
  have hmv : Measurable (fun x : ℝ => (Real.sin (2 * x)) ^ ((β - 1) / 2)) := by measurability
  have hu2 : MeasureTheory.IntegrableOn
      (fun x => (|deriv f x| * (Real.sin (2 * x)) ^ ((1 - β) / 2)) ^ 2) (Set.Ioo a b) := by
    refine hIntF.congr_fun ?_ measurableSet_Ioo
    intro x hx
    dsimp only
    rw [mul_pow, sq_abs, spb_rpow_sq _ _ (hsinpos x hx),
      show 2 * ((1 - β) / 2) = 1 - β by ring]
  have hv2 : MeasureTheory.IntegrableOn
      (fun x => ((Real.sin (2 * x)) ^ ((β - 1) / 2)) ^ 2) (Set.Ioo a b) := by
    refine hIntS.congr_fun ?_ measurableSet_Ioo
    intro x hx
    dsimp only
    rw [spb_rpow_sq _ _ (hsinpos x hx), show 2 * ((β - 1) / 2) = β - 1 by ring]
  have hu_mem : MeasureTheory.MemLp
      (fun x => |deriv f x| * (Real.sin (2 * x)) ^ ((1 - β) / 2)) 2
      (MeasureTheory.volume.restrict (Set.Ioo a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hmu.aestronglyMeasurable).2 hu2
  have hv_mem : MeasureTheory.MemLp
      (fun x => (Real.sin (2 * x)) ^ ((β - 1) / 2)) 2
      (MeasureTheory.volume.restrict (Set.Ioo a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hmv.aestronglyMeasurable).2 hv2
  have hcs := Work.Spaces.cs_integral hu_mem hv_mem
  have e1 : (∫ x in Set.Ioo a b,
        (|deriv f x| * (Real.sin (2 * x)) ^ ((1 - β) / 2))
          * ((Real.sin (2 * x)) ^ ((β - 1) / 2)))
      = ∫ x in Set.Ioo a b, |deriv f x| := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [mul_assoc, ← Real.rpow_add (hsinpos x hx),
      show (1 - β) / 2 + (β - 1) / 2 = 0 by ring, Real.rpow_zero, mul_one]
  have e2 : (∫ x in Set.Ioo a b,
        (|deriv f x| * (Real.sin (2 * x)) ^ ((1 - β) / 2)) ^ 2)
      = ∫ x in Set.Ioo a b, (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [mul_pow, sq_abs, spb_rpow_sq _ _ (hsinpos x hx),
      show 2 * ((1 - β) / 2) = 1 - β by ring]
  have e3 : (∫ x in Set.Ioo a b, ((Real.sin (2 * x)) ^ ((β - 1) / 2)) ^ 2)
      = ∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (β - 1) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [spb_rpow_sq _ _ (hsinpos x hx), show 2 * ((β - 1) / 2) = β - 1 by ring]
  have key : (∫ x in Set.Ioo a b, |deriv f x|) ^ 2 ≤
      (∫ x in Set.Ioo a b, (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β))
        * (∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (β - 1)) := by
    calc (∫ x in Set.Ioo a b, |deriv f x|) ^ 2
        = (∫ x in Set.Ioo a b,
            (|deriv f x| * (Real.sin (2 * x)) ^ ((1 - β) / 2))
              * ((Real.sin (2 * x)) ^ ((β - 1) / 2))) ^ 2 := by rw [e1]
      _ ≤ (∫ x in Set.Ioo a b, (|deriv f x| * (Real.sin (2 * x)) ^ ((1 - β) / 2)) ^ 2)
            * (∫ x in Set.Ioo a b, ((Real.sin (2 * x)) ^ ((β - 1) / 2)) ^ 2) := hcs
      _ = (∫ x in Set.Ioo a b, (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β))
            * (∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (β - 1)) := by rw [e2, e3]
  have hFnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))]
      (fun x => (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β)) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2
      (Filter.Eventually.of_forall fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsinfull x hx) _))
  have hSnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))]
      (fun x => (Real.sin (2 * x)) ^ (β - 1)) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2
      (Filter.Eventually.of_forall fun x hx => Real.rpow_nonneg (hsinfull x hx) _)
  have hA : (∫ x in Set.Ioo a b, (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β))
      ≤ ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β) :=
    MeasureTheory.setIntegral_mono_set hint hFnn hsub_ae
  have hB : (∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (β - 1))
      ≤ ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (Real.sin (2 * x)) ^ (β - 1) :=
    MeasureTheory.setIntegral_mono_set hintB hSnn hsub_ae
  have hA0 : 0 ≤ ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
      (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun x hx => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsinfull x hx) _))
  have hB0 : 0 ≤ ∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (β - 1) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun x hx => Real.rpow_nonneg (le_of_lt (hsinpos x hx)) _)
  exact key.trans (mul_le_mul hA hB hB0 hA0)

/-! ## The fundamental theorem step -/

/-- **The fundamental theorem of calculus on a subinterval.**  For `a ≤ b` in `(0, π/2)` and `f`
of class `C¹` on `(0, π/2)`, `|f a - f b| ≤ ∫_a^b |f'|`. -/
private lemma ftc_bound {f : ℝ → ℝ} (hsm : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)))
    {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hb : b < Real.pi / 2) :
    |f a - f b| ≤ ∫ x in Set.Ioo a b, |deriv f x| := by
  have hsub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hFTC : ∫ x in a..b, deriv f x = f b - f a :=
    intervalIntegral.integral_deriv_of_contDiffOn_Icc (hsm.mono hsub) hab
  calc |f a - f b| = |f b - f a| := abs_sub_comm _ _
    _ = |∫ x in a..b, deriv f x| := by rw [hFTC]
    _ ≤ ∫ x in a..b, |deriv f x| := intervalIntegral.abs_integral_le_integral_abs hab
    _ = ∫ x in Set.Ioo a b, |deriv f x| := by
        rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- **The pointwise difference bound for a `C¹` function on `(0,π/2)`, with the critical
`sin(2θ)^{β-1}` weight.**  For `0 < β ≤ 1` and `f` of class `C¹` on the open interval whose
`sin(2·)^{1-β}`-weighted squared derivative and whose weight `sin(2·)^{β-1}` are both integrable
on `(0,π/2)`:

`f(θ)² ≤ 2 f(π/4)² + 2 · (∫_0^{π/2} f'(t)² sin(2t)^{1-β} dt) · (∫_0^{π/2} sin(2t)^{β-1} dt)`
for every `θ ∈ (0,π/2)`.

Route: the fundamental theorem `f(π/4) - f(θ) = ∫_θ^{π/4} f'` (the interval `[θ,π/4]` lies inside
the open interval where `f` is `C¹`), then `|f(θ)| ≤ |f(π/4)| + ∫_θ^{π/4}|f'|`, then
Cauchy–Schwarz (`Work.Spaces.cs_integral`) applied to `u = sin(2·)^{(1-β)/2} f'` and
`v = sin(2·)^{(β-1)/2}` (whose product is `|f'|`) on the interval `(θ,π/4)`, where the two
subinterval integrals are bounded by the corresponding integrals over the whole `(0,π/2)`
(monotonicity of the integral of a nonnegative integrable function).
The two integrability hypotheses are the exact certificates this needs; `hintB` is not implied by
`hint` (both hold for every `β ∈ (0,1]`, but proving that is a separate `rpow`-integral
computation). -/
theorem slicePtBound {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {f : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β)) (Set.Ioo 0 (Real.pi / 2)))
    (hintB : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (β - 1)) (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (f θ) ^ 2 ≤ 2 * (f (Real.pi / 4)) ^ 2
        + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
                (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 - β))
            * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin (2 * θ)) ^ (β - 1)) := by
  have _ := hβ
  have _ := hβ1
  intro θ hθ
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hπ4pos : 0 < Real.pi / 4 := by linarith [Real.pi_pos]
  have hπ4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  set A : ℝ := ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
      (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β) with hA
  set B : ℝ := ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (Real.sin (2 * x)) ^ (β - 1) with hB
  rcases le_total θ (Real.pi / 4) with hle | hle
  · -- `θ ≤ π/4`: integrate over `(θ, π/4)`
    have hbnd := ftc_bound hsm hle hθ0 hπ4lt
    have haux : |f θ| ≤ |f (Real.pi / 4)| + ∫ x in Set.Ioo θ (Real.pi / 4), |deriv f x| := by
      have h1 : |f θ| ≤ |f (Real.pi / 4)| + |f θ - f (Real.pi / 4)| := by
        calc |f θ| = |f (Real.pi / 4) + (f θ - f (Real.pi / 4))| := by
              rw [show f (Real.pi / 4) + (f θ - f (Real.pi / 4)) = f θ by ring]
          _ ≤ _ := abs_add_le _ _
      linarith [hbnd]
    have hI2 : (∫ x in Set.Ioo θ (Real.pi / 4), |deriv f x|) ^ 2 ≤ A * B := by
      rw [hA, hB]
      exact cs_subinterval hint hintB hle hθ0 hπ4lt
    calc f θ ^ 2 = (|f θ|) ^ 2 := (sq_abs _).symm
      _ ≤ (|f (Real.pi / 4)| + ∫ x in Set.Ioo θ (Real.pi / 4), |deriv f x|) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) haux 2
      _ ≤ 2 * (|f (Real.pi / 4)|) ^ 2
            + 2 * (∫ x in Set.Ioo θ (Real.pi / 4), |deriv f x|) ^ 2 := by
            nlinarith [sq_nonneg (|f (Real.pi / 4)| - ∫ x in Set.Ioo θ (Real.pi / 4), |deriv f x|)]
      _ = 2 * (f (Real.pi / 4)) ^ 2
            + 2 * (∫ x in Set.Ioo θ (Real.pi / 4), |deriv f x|) ^ 2 := by rw [sq_abs]
      _ ≤ 2 * (f (Real.pi / 4)) ^ 2 + 2 * (A * B) := by linarith [hI2]
      _ = 2 * (f (Real.pi / 4)) ^ 2
            + 2 * (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
                    (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β))
                * (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
                    (Real.sin (2 * x)) ^ (β - 1)) := by rw [hA, hB]; ring
  · -- `π/4 ≤ θ`: integrate over `(π/4, θ)`
    have hbnd := ftc_bound hsm hle hπ4pos hθ1
    rw [abs_sub_comm] at hbnd
    have haux : |f θ| ≤ |f (Real.pi / 4)| + ∫ x in Set.Ioo (Real.pi / 4) θ, |deriv f x| := by
      have h1 : |f θ| ≤ |f (Real.pi / 4)| + |f θ - f (Real.pi / 4)| := by
        calc |f θ| = |f (Real.pi / 4) + (f θ - f (Real.pi / 4))| := by
              rw [show f (Real.pi / 4) + (f θ - f (Real.pi / 4)) = f θ by ring]
          _ ≤ _ := abs_add_le _ _
      linarith [hbnd]
    have hI2 : (∫ x in Set.Ioo (Real.pi / 4) θ, |deriv f x|) ^ 2 ≤ A * B := by
      rw [hA, hB]
      exact cs_subinterval hint hintB hle hπ4pos hθ1
    calc f θ ^ 2 = (|f θ|) ^ 2 := (sq_abs _).symm
      _ ≤ (|f (Real.pi / 4)| + ∫ x in Set.Ioo (Real.pi / 4) θ, |deriv f x|) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) haux 2
      _ ≤ 2 * (|f (Real.pi / 4)|) ^ 2
            + 2 * (∫ x in Set.Ioo (Real.pi / 4) θ, |deriv f x|) ^ 2 := by
            nlinarith [sq_nonneg (|f (Real.pi / 4)| - ∫ x in Set.Ioo (Real.pi / 4) θ, |deriv f x|)]
      _ = 2 * (f (Real.pi / 4)) ^ 2
            + 2 * (∫ x in Set.Ioo (Real.pi / 4) θ, |deriv f x|) ^ 2 := by rw [sq_abs]
      _ ≤ 2 * (f (Real.pi / 4)) ^ 2 + 2 * (A * B) := by linarith [hI2]
      _ = 2 * (f (Real.pi / 4)) ^ 2
            + 2 * (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
                    (deriv f x) ^ 2 * (Real.sin (2 * x)) ^ (1 - β))
                * (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
                    (Real.sin (2 * x)) ^ (β - 1)) := by rw [hA, hB]; ring

end Work.FTS.StrongPersist.N6Trans.SixRoute
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.DecayAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

/-! ## The derivative at a one-sided vanishing point is `0` -/



/-! ## The endpoint `θ`-derivatives of a function vanishing off the open strip -/







/-! ## Squeezing at `+∞` -/



end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.JConvAux.ofReal_integral_le_liminf_ofReal_integral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JConvAux.ofReal_integral_le_liminf_ofReal_integral` — the `θ`-Fatou step, in `ℝ≥0∞`

The real-valued `θ`-integrals of a sequence of nonnegative functions converge at least to the
integral of the a.e. limit, in the `ℝ≥0∞`-form used by `FTS_EllLimOK.HkSq_le_of_JConv`
(`∫⁻ liminf ≤ liminf ∫⁻`, `MeasureTheory.lintegral_liminf_le'`, plus the two conversions
`integral_eq_lintegral_of_nonneg_ae` and `ofReal_integral_eq_lintegral_ofReal` and
`ENNReal.ofReal_toReal_le`).

Note the Bochner-integral convention: if `A` is not integrable the left-hand side is `ofReal 0 = 0`
and the inequality is trivial, so no integrability of `A` is needed.
-/
open scoped Real Topology
open MeasureTheory Filter

namespace Work.FTS_EllLimOK.JConvAux


end Work.FTS_EllLimOK.JConvAux
end
-- ===== merged: Submission.Work.FTS_EllLimOK.Pinning.tendsto_cos_mul_eq_zero_of_integrable_div_cos_sq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pinning lemma: `cos θ · f θ → 0` at `π/2`

If `∫_0^{π/2} (f θ / cos θ)² dθ` is finite and `cos θ · f θ` has a limit `J` as
`θ → (π/2)⁻`, then `J = 0`.

The reason is quantitative.  Writing `g θ = cos θ · f θ`, the integrand is
`(g θ / cos²θ)² = g θ² / cos⁴θ`, and near `θ = π/2` we have `cos x ≤ π/2 - x`, so
`1/cos⁴x ≥ 1/(π/2 - x)⁴`.  If `|g| > d > 0` on a tail `(t, π/2)`, then on the short
interval `(π/2 - θ, π/2)` (length `θ`) the integrand exceeds `d²/θ⁴`, whence

`d²/θ³ ≤ ∫_{π/2-θ}^{π/2} (f/cos)² ≤ ∫_t^{π/2} (f/cos)²`,

which is impossible for small `θ`.  So every `d > 0` is attained as a bound on `g`
somewhere in the tail, which forces the limit to be `0`.

This is the `1/cos⁴`-analogue of
`Work.FTS_EllLimOK.SliceTrace.exists_abs_le_of_integrable_inv_cos_sq_aux` (which is the
`1/cos²` statement for `f` itself).
-/

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS_EllLimOK.Pinning



end Work.FTS_EllLimOK.Pinning
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.CosWeightDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter




/-- The second weight `sin(2θ)^{-η} / cos(θ)^2` appearing on the RHS of the goal. -/
noncomputable def cwB (θ : ℝ) : ℝ :=
  (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / (Real.cos θ) ^ (2 : ℕ)

end Work.FTS_EllLimOK.PkgJets
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.ctF_le_ctA =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets


end Work.FTS_EllLimOK.PkgJets
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.ctG_le_ctB =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

/-!
# The reflected comparison function dominates `ctG` on `(0, π/4]`

`ctG w = sin(2w)^{-η}/sin(w)^4` and `ctB w = (4/π)^{-η}(π/2)^4 w^{-(4+η)}`, `η = 99/100`.
Since `sin(t) ≥ (2/π)t` on `[0, π/2]`, we have `sin w ≥ (2/π)w` (so `1/sin(w)^4 ≤ (π/2)^4 w^{-4}`)
and `sin(2w) ≥ (4/π)w` (so `sin(2w)^{-η} ≤ (4/π)^{-η} w^{-η}`).  Multiplying the two bounds
gives `ctG w ≤ (4/π)^{-η}(π/2)^4 w^{-4}w^{-η} = ctB w` for `w > 0`.  Note the endpoint
`w = π/4` is admissible: there `ctG = 4`, `ctB = 16`.
-/


end Work.FTS_EllLimOK.PkgJets
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.ctTail_integral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real
open MeasureTheory Set

/-!
# The `cos`-weight tail bound on `[π/4, T]`

For `T ∈ (π/4, π/2)` we bound the tail of the divergent primitive

`∫_{π/4}^T sin(2s)^{-η}/cos(s)^4 ds ≤ 1000 · (π/2 - T)^{-(3+η)}`,  `η = 99/100`.

Writing `δ = π/2 - T ∈ (0, π/4)` and reflecting by `w = π/2 - s` (the substitution
`intervalIntegral.integral_comp_sub_left` together with `ctF_sub`, which turns `ctF (π/2 - w)`
into `ctG w`), the integral becomes `∫_δ^{π/4} ctG w dw`.  On `(0, π/4]` the elementary
Jordan-type inequalities `sin(2w) ≥ (4/π) w` and `sin w ≥ (2/π) w` give the pointwise bound
`ctG w ≤ 16 w^{-(4+η)}`; integrating `w^{-(4+η)}` exactly (`integral_rpow`) yields
`16·(δ^{-(3+η)} - (π/4)^{-(3+η)})/(3+η) ≤ 16 δ^{-(3+η)} ≤ 1000 δ^{-(3+η)}`.
-/


end Work.FTS_EllLimOK.PkgJets
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.integral_Icc_le_of_subinterval_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter


end Work.FTS_EllLimOK.PkgJets
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.H2.Dev.end_rate_pi_half =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `end_rate_pi_half` — the endpoint rate of a slice of the self-similar profile

Let `S` solve the slice equation

`S'' = tan θ · S' + (cos θ)⁻² · S − 6 S − G`

on `(0, π/2)`, with `|G t| ≤ MG · (π/2 − t)^β` and `|S t| ≤ CS · (π/2 − t)` for `β ∈ (0, 1]`,
and suppose moreover that `Φ := S'' + 4 S + G` is **bounded** on `(0, π/2)` (this is the
hypothesis `hWb`; it pins down the regular branch of the linear equation for `Φ`).  Then

`|S''(θ)| ≤ 100 (MG + CS) · (π/2 − θ)^β`  on `(π/4, π/2)`.

The proof combines two earlier lemmas:

* `BoxAux.th2Ident`: `(cos θ)³ Φ(θ) = ∫_θ^{π/2} sin t · (cos t)² · G t dt` — the closed
  form of `Φ` obtained from the ODE and the FTC (the boundedness of `Φ` kills the boundary
  term at `π/2`);
* `BoxAux.cos_inv_cube_mul_integral_le`: `(cos θ)⁻³ ∫_θ^{π/2} sin t (cos t)² (π/2−t)^β dt
  ≤ 32 (π/2−θ)^β`.

Combining: `|Φ(θ)| ≤ (cos θ)⁻³ · MG · ∫_θ^{π/2} sin t (cos t)² (π/2−t)^β dt ≤ 32 MG δ^β`
with `δ = π/2 − θ`, and then `S'' = Φ − 4S − G` gives the claim.
-/

open MeasureTheory
open scoped Topology

namespace Work.FTS_EllLimOK.ProducerH.H2.Dev

theorem end_rate_pi_half {S G : ℝ → ℝ} {β MG CS MW : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hMG : 0 ≤ MG) (hCS : 0 ≤ CS)
    (hS : ContDiffOn ℝ 2 S (Set.Ioo (0:ℝ) (Real.pi / 2)))
    (hGc : ContinuousOn G (Set.Ioo (0:ℝ) (Real.pi / 2)))
    (hGle : ∀ t ∈ Set.Ioo (0:ℝ) (Real.pi / 2), |G t| ≤ MG)
    (hode : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      deriv (deriv S) θ = Real.tan θ * deriv S θ + ((Real.cos θ)^2)⁻¹ * S θ - 6 * S θ - G θ)
    (hWb : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      |deriv (deriv S) θ + 4 * S θ + G θ| ≤ MW)
    (hRate : ∀ t ∈ Set.Ioo (0:ℝ) (Real.pi / 2), |G t| ≤ MG * (Real.pi / 2 - t) ^ β)
    (hSr : ∀ t ∈ Set.Ioo (0:ℝ) (Real.pi / 2), |S t| ≤ CS * (Real.pi / 2 - t)) :
    ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      |deriv (deriv S) θ| ≤ (100 * (MG + CS)) * (Real.pi / 2 - θ) ^ β := by
  intro θ hθ
  have hθ45 : Real.pi / 4 < θ := hθ.1
  have hθlt : θ < Real.pi / 2 := hθ.2
  have hθpos : 0 < θ := by linarith [Real.pi_pos]
  have hθIoo : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨hθpos, hθlt⟩
  have hcospos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  set δ : ℝ := Real.pi / 2 - θ with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδle1 : δ ≤ 1 := by rw [hδdef]; linarith [Real.pi_lt_four]
  have hδβge : δ ≤ δ ^ β := by
    have h := Real.rpow_le_rpow_of_exponent_ge hδpos hδle1 hβ1
    rwa [Real.rpow_one] at h
  have hδβnn : 0 ≤ δ ^ β := Real.rpow_nonneg hδpos.le β
  -- the closed form of `Φ = S'' + 4S + G`
  have hident := Work.FTS_EllLimOK.ProducerH.BoxAux.th2Ident hS hGc hGle hode hWb θ hθIoo
  set X : ℝ := deriv (deriv S) θ + 4 * S θ + G θ with hXdef
  set I : ℝ := ∫ t in θ..(Real.pi/2), Real.sin t * (Real.cos t)^2 * G t with hIdef
  set J : ℝ := ∫ t in θ..(Real.pi/2), Real.sin t * (Real.cos t)^2 * (Real.pi/2 - t)^β with hJdef
  have hident' : (Real.cos θ)^3 * X = I := by rw [hXdef, hIdef]; exact hident
  -- bound the integral against the rate of `G`
  have hI_le : |I| ≤ MG * J := by
    rw [hIdef, hJdef]
    have hcd : Continuous (fun t : ℝ => Real.sin t * (Real.cos t)^2) :=
      Real.continuous_sin.mul (Real.continuous_cos.pow 2)
    have hcont_pow : ContinuousOn (fun t : ℝ => (Real.pi/2 - t)^β) (Set.uIcc θ (Real.pi/2)) :=
      (continuous_const.sub continuous_id).continuousOn.rpow_const (fun _ _ => Or.inr hβ.le)
    have hJint : IntervalIntegrable (fun t : ℝ => Real.sin t * (Real.cos t)^2 * (Real.pi/2 - t)^β)
        volume θ (Real.pi/2) := ((hcd.continuousOn).mul hcont_pow).intervalIntegrable
    have hgint : IntervalIntegrable
        (fun t : ℝ => MG * (Real.sin t * (Real.cos t)^2 * (Real.pi/2 - t)^β)) volume θ (Real.pi/2) :=
      hJint.const_mul MG
    have hle : θ ≤ Real.pi/2 := hθlt.le
    have hpt : ∀ᵐ t ∂volume, t ∈ Set.Ioc θ (Real.pi/2) →
        ‖Real.sin t * (Real.cos t)^2 * G t‖
          ≤ MG * (Real.sin t * (Real.cos t)^2 * (Real.pi/2 - t)^β) := by
      filter_upwards with t ht
      rcases eq_or_lt_of_le ht.2 with h | h
      · rw [h]
        simp [Real.cos_pi_div_two, Real.zero_rpow hβ.ne']
      · have htIoo : t ∈ Set.Ioo (0:ℝ) (Real.pi/2) := ⟨by linarith [hθpos, ht.1], h⟩
        have hGt := hRate t htIoo
        have hsinnn : 0 ≤ Real.sin t :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθpos, ht.1]) (by linarith [Real.pi_pos])
        have hcos2nn : 0 ≤ (Real.cos t)^2 := sq_nonneg _
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hsinnn, abs_of_nonneg hcos2nn]
        calc Real.sin t * (Real.cos t)^2 * |G t|
            ≤ Real.sin t * (Real.cos t)^2 * (MG * (Real.pi/2 - t)^β) :=
              mul_le_mul_of_nonneg_left hGt (mul_nonneg hsinnn hcos2nn)
          _ = MG * (Real.sin t * (Real.cos t)^2 * (Real.pi/2 - t)^β) := by ring
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hle hpt hgint
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at hnorm
    exact hnorm
  have hcoef_nn : 0 ≤ ((Real.cos θ)^3)⁻¹ := inv_nonneg.mpr (pow_pos hcospos 3).le
  -- the normalized integral is `≤ 32 δ^β`
  have hJb : ((Real.cos θ)^3)⁻¹ * J ≤ 32 * δ^β := by
    have h := Work.FTS_EllLimOK.ProducerH.BoxAux.cos_inv_cube_mul_integral_le hβ hβ1
      (show θ ∈ Set.Icc (Real.pi/4) (Real.pi/2) from ⟨hθ45.le, hθlt.le⟩)
    rw [hJdef, hδdef, ← inv_pow]
    exact h
  -- hence `|Φ| ≤ 32 MG δ^β`
  have hX_le : |X| ≤ 32 * MG * δ^β := by
    have hXeq : X = ((Real.cos θ)^3)⁻¹ * I := by
      rw [← hident']
      exact (inv_mul_cancel_left₀ (by positivity : (Real.cos θ)^3 ≠ 0) X).symm
    have h2 : |X| = ((Real.cos θ)^3)⁻¹ * |I| := by
      rw [hXeq, abs_mul, abs_of_nonneg hcoef_nn]
    rw [h2]
    calc ((Real.cos θ)^3)⁻¹ * |I|
        ≤ ((Real.cos θ)^3)⁻¹ * (MG * J) := mul_le_mul_of_nonneg_left hI_le hcoef_nn
      _ = MG * (((Real.cos θ)^3)⁻¹ * J) := by ring
      _ ≤ MG * (32 * δ^β) := mul_le_mul_of_nonneg_left hJb hMG
      _ = 32 * MG * δ^β := by ring
  have hSθ : |S θ| ≤ CS * δ := by rw [hδdef]; exact hSr θ hθIoo
  have hGθ : |G θ| ≤ MG * δ^β := by rw [hδdef]; exact hRate θ hθIoo
  -- `S'' = Φ − 4S − G`
  have hS'' : |deriv (deriv S) θ| = |X - 4 * S θ - G θ| := by
    congr 1
    rw [hXdef]; ring
  rw [hS'']
  have h_abs : |X - 4 * S θ - G θ| ≤ |X| + 4 * |S θ| + |G θ| := by
    have h1 : |X - 4 * S θ - G θ| ≤ |X - 4 * S θ| + |G θ| := by
      have hh := abs_add_le (X - 4 * S θ) (-(G θ))
      simpa [sub_eq_add_neg] using hh
    have h2 : |X - 4 * S θ| ≤ |X| + 4 * |S θ| := by
      have hh := abs_add_le X (-(4 * S θ))
      rw [abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)] at hh
      simpa [sub_eq_add_neg] using hh
    linarith
  calc |X - 4 * S θ - G θ| ≤ |X| + 4 * |S θ| + |G θ| := h_abs
    _ ≤ 32 * MG * δ^β + 4 * CS * δ + MG * δ^β := by linarith
    _ ≤ 100 * (MG + CS) * δ^β := by nlinarith [hδβge, hMG, hCS, hδβnn]

end Work.FTS_EllLimOK.ProducerH.H2.Dev
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.H2.eg_limit_family =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2

open scoped Topology
open Filter Set

-- The hypothesis `A < B` of `eg_limit_family` is part of the requested interface but is not
-- needed by the argument (which works for any `A`, `B`); silence the unused-variable linter.
set_option linter.unusedVariables false

/-- A point of `(0, π/2)` at which `M θ` is as small as we like. -/
private lemma exists_theta_small {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 2 * (M * θ) < ε / 2 := by
  obtain ⟨c, hcpos, hc⟩ := exists_pos_mul_lt (show (0 : ℝ) < ε / 2 by linarith) (2 * M)
  refine ⟨min (Real.pi / 4) c, ⟨lt_min (by linarith [Real.pi_pos]) hcpos, ?_⟩, ?_⟩
  · exact lt_of_le_of_lt (min_le_left _ _) (by linarith [Real.pi_pos])
  · have hle : min (Real.pi / 4) c ≤ c := min_le_right _ _
    calc 2 * (M * min (Real.pi / 4) c) = (2 * M) * min (Real.pi / 4) c := by ring
      _ ≤ (2 * M) * c := mul_le_mul_of_nonneg_left hle (by linarith [hM])
      _ < ε / 2 := hc

/-- A point of `(0, π/2)` at which `M (π/2 - θ)` is as small as we like. -/
private lemma exists_theta_close_pi {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 2 * (M * (Real.pi / 2 - θ)) < ε / 2 := by
  obtain ⟨c, hcpos, hc⟩ := exists_pos_mul_lt (show (0 : ℝ) < ε / 2 by linarith) (2 * M)
  refine ⟨Real.pi / 2 - min (Real.pi / 4) c, ⟨?_, ?_⟩, ?_⟩
  · have hle : min (Real.pi / 4) c ≤ Real.pi / 4 := min_le_left _ _
    linarith [Real.pi_pos]
  · have hpos : 0 < min (Real.pi / 4) c := lt_min (by linarith [Real.pi_pos]) hcpos
    linarith
  · have hsub : Real.pi / 2 - (Real.pi / 2 - min (Real.pi / 4) c) = min (Real.pi / 4) c := by ring
    rw [hsub]
    have hle : min (Real.pi / 4) c ≤ c := min_le_right _ _
    calc 2 * (M * min (Real.pi / 4) c) = (2 * M) * min (Real.pi / 4) c := by ring
      _ ≤ (2 * M) * c := mul_le_mul_of_nonneg_left hle (by linarith [hM])
      _ < ε / 2 := hc

/-- **Endpoint limits of a uniformly Lipschitz family.**  Let `F : ℝ → ℝ → ℝ` be a family of
functions of `θ` which on the strip `z ∈ [A,B]`, `θ ∈ (0, π/2)` is `C¹` in `θ` with
`θ`-derivative bounded by `M`, and whose slices `z ↦ F θ z` are continuous on `[A,B]`.  Then
both one-sided θ-limits exist for every `z ∈ [A,B]`, they are approached at the optimal
Lipschitz rate `M`, and they are continuous functions of `z` on `[A,B]`. -/
theorem eg_limit_family {F : ℝ → ℝ → ℝ} {A B M : ℝ} (hAB : A < B) (hM : 0 ≤ M)
    (hcd : ∀ z ∈ Set.Icc A B, ContDiffOn ℝ 1 (fun θ => F θ z) (Set.Ioo 0 (Real.pi / 2)))
    (hderiv : ∀ z ∈ Set.Icc A B, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |deriv (fun θ' => F θ' z) θ| ≤ M)
    (hcont : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ContinuousOn (fun z => F θ z) (Set.Icc A B)) :
    ∃ L R : ℝ → ℝ,
      (∀ z ∈ Set.Icc A B, Filter.Tendsto (fun θ => F θ z) (nhdsWithin 0 (Set.Ioi 0)) (nhds (L z))) ∧
      (∀ z ∈ Set.Icc A B, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |F θ z - L z| ≤ M * θ) ∧
      (∀ z ∈ Set.Icc A B, Filter.Tendsto (fun θ => F θ z)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (R z))) ∧
      (∀ z ∈ Set.Icc A B, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |F θ z - R z| ≤ M * (Real.pi / 2 - θ)) ∧
      ContinuousOn L (Set.Icc A B) ∧ ContinuousOn R (Set.Icc A B) := by
  have hpi : (0 : ℝ) < Real.pi / 2 := Real.pi_div_two_pos
  -- ## Existence of the two one-sided limits, for every `z ∈ [A,B]`
  have hexL : ∀ z : ℝ, ∃ L : ℝ, z ∈ Set.Icc A B →
      Filter.Tendsto (fun θ => F θ z) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
    intro z
    by_cases hz : z ∈ Set.Icc A B
    · obtain ⟨L, hL⟩ := (Work.FTS_EllLimOK.ProducerH.ThetaZero.tendsto_of_deriv_bounded hpi
        (hcd z hz) (hderiv z hz)).1
      exact ⟨L, fun _ => hL⟩
    · exact ⟨0, fun h => absurd h hz⟩
  have hexR : ∀ z : ℝ, ∃ R : ℝ, z ∈ Set.Icc A B →
      Filter.Tendsto (fun θ => F θ z) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds R) := by
    intro z
    by_cases hz : z ∈ Set.Icc A B
    · obtain ⟨R, hR⟩ := (Work.FTS_EllLimOK.ProducerH.ThetaZero.tendsto_of_deriv_bounded hpi
        (hcd z hz) (hderiv z hz)).2
      exact ⟨R, fun _ => hR⟩
    · exact ⟨0, fun h => absurd h hz⟩
  let L : ℝ → ℝ := fun z => Classical.choose (hexL z)
  let R : ℝ → ℝ := fun z => Classical.choose (hexR z)
  have hLtend : ∀ z ∈ Set.Icc A B,
      Filter.Tendsto (fun θ => F θ z) (nhdsWithin 0 (Set.Ioi 0)) (nhds (L z)) :=
    fun z hz => Classical.choose_spec (hexL z) hz
  have hRtend : ∀ z ∈ Set.Icc A B,
      Filter.Tendsto (fun θ => F θ z) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds (R z)) :=
    fun z hz => Classical.choose_spec (hexR z) hz
  -- ## The family is Lipschitz in `θ` on the open strip, with the uniform constant `M`
  have hlip : ∀ z ∈ Set.Icc A B,
      LipschitzOnWith ⟨M, hM⟩ (fun θ => F θ z) (Set.Ioo 0 (Real.pi / 2)) := by
    intro z hz
    refine Convex.lipschitzOnWith_of_nnnorm_deriv_le (fun x hx => ?_) (fun x hx => ?_)
      (convex_Ioo 0 (Real.pi / 2))
    · exact ((hcd z hz).differentiableOn_one x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
    · have hm : |deriv (fun θ => F θ z) x| ≤ M := hderiv z hz x hx
      exact_mod_cast hm
  -- ## The rate at `θ → 0⁺`
  have hboundL : ∀ z ∈ Set.Icc A B, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |F θ z - L z| ≤ M * θ := by
    intro z hz θ hθ
    have hev : ∀ᶠ θ' in nhdsWithin (0 : ℝ) (Set.Ioi 0), |F θ' z - F θ z| ≤ M * θ := by
      filter_upwards [Ioo_mem_nhdsGT hθ.1] with θ' hθ'
      have hθ'm : θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ'.1, lt_trans hθ'.2 hθ.2⟩
      have h1 : dist (F θ' z) (F θ z) ≤ M * dist θ' θ := (hlip z hz).dist_le_mul θ' hθ'm θ hθ
      rw [Real.dist_eq, Real.dist_eq] at h1
      have h2 : |θ' - θ| = θ - θ' := by
        rw [abs_of_neg (show θ' - θ < 0 by linarith [hθ'.2])]
        ring
      rw [h2] at h1
      calc |F θ' z - F θ z| = dist (F θ' z) (F θ z) := by rw [Real.dist_eq]
        _ ≤ M * (θ - θ') := h1
        _ ≤ M * θ := by nlinarith [hM, hθ'.1]
    have hT : Filter.Tendsto (fun θ' => F θ' z - F θ z) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (L z - F θ z)) := (hLtend z hz).sub_const (F θ z)
    have hTabs : Filter.Tendsto (fun θ' => |F θ' z - F θ z|) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds |L z - F θ z|) := by
      simpa only [Real.norm_eq_abs] using hT.norm
    have := le_of_tendsto hTabs hev
    calc |F θ z - L z| = |L z - F θ z| := abs_sub_comm _ _
      _ ≤ M * θ := this
  -- ## The rate at `θ → (π/2)⁻`
  have hboundR : ∀ z ∈ Set.Icc A B, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |F θ z - R z| ≤ M * (Real.pi / 2 - θ) := by
    intro z hz θ hθ
    have hev : ∀ᶠ θ' in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        |F θ' z - F θ z| ≤ M * (Real.pi / 2 - θ) := by
      filter_upwards [Ioo_mem_nhdsLT hθ.2] with θ' hθ'
      have hθ'm : θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨lt_trans hθ.1 hθ'.1, hθ'.2⟩
      have h1 : dist (F θ' z) (F θ z) ≤ M * dist θ' θ := (hlip z hz).dist_le_mul θ' hθ'm θ hθ
      rw [Real.dist_eq, Real.dist_eq] at h1
      have h2 : |θ' - θ| = θ' - θ := abs_of_pos (show 0 < θ' - θ by linarith [hθ'.1])
      rw [h2] at h1
      calc |F θ' z - F θ z| = dist (F θ' z) (F θ z) := by rw [Real.dist_eq]
        _ ≤ M * (θ' - θ) := h1
        _ ≤ M * (Real.pi / 2 - θ) := by nlinarith [hM, hθ'.2]
    have hT : Filter.Tendsto (fun θ' => F θ' z - F θ z)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (R z - F θ z)) :=
      (hRtend z hz).sub_const (F θ z)
    have hTabs : Filter.Tendsto (fun θ' => |F θ' z - F θ z|)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds |R z - F θ z|) := by
      simpa only [Real.norm_eq_abs] using hT.norm
    have := le_of_tendsto hTabs hev
    calc |F θ z - R z| = |R z - F θ z| := abs_sub_comm _ _
      _ ≤ M * (Real.pi / 2 - θ) := this
  -- ## Continuity of the limit functions on `[A,B]`
  have hcontL : ContinuousOn L (Set.Icc A B) := by
    intro z hz
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨θ₀, hθ₀, hθ₀s⟩ := exists_theta_small hM hε
    have hcw : ContinuousWithinAt (fun z => F θ₀ z) (Set.Icc A B) z :=
      (hcont θ₀ hθ₀).continuousWithinAt hz
    rw [Metric.continuousWithinAt_iff] at hcw
    obtain ⟨δ, hδpos, hδ⟩ := hcw (ε / 2) (by linarith)
    refine ⟨δ, hδpos, fun z' hz' hdist => ?_⟩
    have h1 : |F θ₀ z' - F θ₀ z| < ε / 2 := by
      have := hδ hz' hdist
      rwa [Real.dist_eq] at this
    have h2 : |F θ₀ z - L z| ≤ M * θ₀ := hboundL z hz θ₀ hθ₀
    have h3 : |F θ₀ z' - L z'| ≤ M * θ₀ := hboundL z' hz' θ₀ hθ₀
    rw [Real.dist_eq]
    have hsplit : L z' - L z
        = (L z' - F θ₀ z') + (F θ₀ z' - F θ₀ z) + (F θ₀ z - L z) := by ring
    rw [hsplit]
    calc |(L z' - F θ₀ z') + (F θ₀ z' - F θ₀ z) + (F θ₀ z - L z)|
        ≤ |(L z' - F θ₀ z') + (F θ₀ z' - F θ₀ z)| + |F θ₀ z - L z| :=
          abs_add_le ((L z' - F θ₀ z') + (F θ₀ z' - F θ₀ z)) (F θ₀ z - L z)
      _ ≤ (|L z' - F θ₀ z'| + |F θ₀ z' - F θ₀ z|) + |F θ₀ z - L z| := by
          have h := abs_add_le (L z' - F θ₀ z') (F θ₀ z' - F θ₀ z)
          linarith
      _ < ε := by
          have h3' : |L z' - F θ₀ z'| ≤ M * θ₀ := by
            rw [abs_sub_comm (L z') (F θ₀ z')]
            exact h3
          linarith
  have hcontR : ContinuousOn R (Set.Icc A B) := by
    intro z hz
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨θ₀, hθ₀, hθ₀s⟩ := exists_theta_close_pi hM hε
    have hcw : ContinuousWithinAt (fun z => F θ₀ z) (Set.Icc A B) z :=
      (hcont θ₀ hθ₀).continuousWithinAt hz
    rw [Metric.continuousWithinAt_iff] at hcw
    obtain ⟨δ, hδpos, hδ⟩ := hcw (ε / 2) (by linarith)
    refine ⟨δ, hδpos, fun z' hz' hdist => ?_⟩
    have h1 : |F θ₀ z' - F θ₀ z| < ε / 2 := by
      have := hδ hz' hdist
      rwa [Real.dist_eq] at this
    have h2 : |F θ₀ z - R z| ≤ M * (Real.pi / 2 - θ₀) := hboundR z hz θ₀ hθ₀
    have h3 : |F θ₀ z' - R z'| ≤ M * (Real.pi / 2 - θ₀) := hboundR z' hz' θ₀ hθ₀
    rw [Real.dist_eq]
    have hsplit : R z' - R z
        = (R z' - F θ₀ z') + (F θ₀ z' - F θ₀ z) + (F θ₀ z - R z) := by ring
    rw [hsplit]
    calc |(R z' - F θ₀ z') + (F θ₀ z' - F θ₀ z) + (F θ₀ z - R z)|
        ≤ |(R z' - F θ₀ z') + (F θ₀ z' - F θ₀ z)| + |F θ₀ z - R z| :=
          abs_add_le ((R z' - F θ₀ z') + (F θ₀ z' - F θ₀ z)) (F θ₀ z - R z)
      _ ≤ (|R z' - F θ₀ z'| + |F θ₀ z' - F θ₀ z|) + |F θ₀ z - R z| := by
          have h := abs_add_le (R z' - F θ₀ z') (F θ₀ z' - F θ₀ z)
          linarith
      _ < ε := by
          have h3' : |R z' - F θ₀ z'| ≤ M * (Real.pi / 2 - θ₀) := by
            rw [abs_sub_comm (R z') (F θ₀ z')]
            exact h3
          linarith
  exact ⟨L, R, hLtend, hboundL, hRtend, hboundR, hcontL, hcontR⟩

end Work.FTS_EllLimOK.ProducerH.H2
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.H2.wRateModulusUnif =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2

open MeasureTheory

/-- `∫_x^{π/2} sin t · cos²t dt = cos³x / 3`. -/
theorem integral_sin_mul_cos_sq (x : ℝ) :
    ∫ t in x..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 = (Real.cos x) ^ 3 / 3 := by
  have hderiv : ∀ t ∈ Set.uIcc x (Real.pi / 2),
      HasDerivAt (fun t : ℝ => -((Real.cos t) ^ 3) / 3)
        (Real.sin t * (Real.cos t) ^ 2) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => (Real.cos t) ^ 3)
        (3 * (Real.cos t) ^ 2 * (-Real.sin t)) t := by
      have h := (Real.hasDerivAt_cos t).pow 3
      convert h using 1
    have h2 : HasDerivAt (fun t : ℝ => -((Real.cos t) ^ 3) / 3)
        ((3 * (Real.cos t) ^ 2 * (-Real.sin t)) * (-(1 / 3))) t := by
      have h := (h1.neg).div_const 3
      convert h using 1
      ring
    convert h2 using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun t : ℝ => Real.sin t * (Real.cos t) ^ 2).intervalIntegrable _ _)]
  simp [Real.cos_pi_div_two]
  ring

/-- The ordered (`θ ≤ θ'`) case of the modulus estimate. -/
private theorem wRateOrdered {β L c₁ : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hL : 0 ≤ L)
    {G : ℝ → ℝ} (hGc : ContinuousOn G (Set.Ioo 0 (Real.pi / 2)))
    (h1 : ∀ t ∈ Set.Ioo 0 (Real.pi / 2), |G t - c₁| ≤ L * (Real.pi / 2 - t) ^ β)
    {θ θ' : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hθ' : θ' ∈ Set.Ioo 0 (Real.pi / 2))
    (hle : θ ≤ θ') :
    |((Real.cos θ) ^ 3)⁻¹ * (∫ t in θ..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * G t)
      - ((Real.cos θ') ^ 3)⁻¹ * (∫ t in θ'..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * G t)|
      ≤ 4 * L * |θ - θ'| ^ β := by
  have hθle : θ ≤ Real.pi / 2 := le_of_lt hθ.2
  have hθ'le : θ' ≤ Real.pi / 2 := le_of_lt hθ'.2
  have hcont : ContinuousOn (fun t : ℝ => G t - c₁) (Set.Ioo 0 (Real.pi / 2)) :=
    hGc.sub continuousOn_const
  have hbnd : ∀ t ∈ Set.Ioo 0 (Real.pi / 2), |G t - c₁| ≤ L * (Real.pi / 2) ^ β := by
    intro t ht
    refine (h1 t ht).trans (mul_le_mul_of_nonneg_left ?_ hL)
    exact Real.rpow_le_rpow (by linarith [ht.2]) (by linarith [ht.1]) hβ.le
  have hInt : ∀ x ∈ Set.Ioo 0 (Real.pi / 2),
      IntervalIntegrable (fun t : ℝ => Real.sin t * (Real.cos t) ^ 2 * (G t - c₁))
        volume x (Real.pi / 2) :=
    fun x hx => sinCosSqInt hcont hbnd hx.1 (le_of_lt hx.2)
  -- split off the constant `c₁`
  have hsplit : ∀ x ∈ Set.Ioo 0 (Real.pi / 2),
      (∫ t in x..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * G t)
        = (∫ t in x..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (G t - c₁))
          + c₁ * ((Real.cos x) ^ 3 / 3) := by
    intro x hx
    have hI1 := hInt x hx
    have hI2 : IntervalIntegrable (fun t : ℝ => c₁ * (Real.sin t * (Real.cos t) ^ 2))
        volume x (Real.pi / 2) :=
      (by fun_prop : Continuous fun t : ℝ => c₁ * (Real.sin t * (Real.cos t) ^ 2)).intervalIntegrable _ _
    rw [show (∫ t in x..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * G t)
        = ∫ t in x..(Real.pi / 2),
            (Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)
              + c₁ * (Real.sin t * (Real.cos t) ^ 2))
        from intervalIntegral.integral_congr (fun t _ => by ring)]
    rw [intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_const_mul,
      integral_sin_mul_cos_sq x]
  -- the resulting identity for `W`
  have hWid : ∀ x ∈ Set.Ioo 0 (Real.pi / 2),
      ((Real.cos x) ^ 3)⁻¹ * (∫ t in x..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * G t)
          - c₁ / 3
        = ((Real.cos x) ^ 3)⁻¹
          * (∫ t in x..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)) := by
    intro x hx
    rw [hsplit x hx]
    have hcx : Real.cos x ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2]⟩)
    field_simp
    ring
  -- pointwise bound in the `π/2`-endpoint regime (distance `≤ Real.pi/2 - θ'`)
  have hpt' : ∀ t ∈ Set.Ioo θ' (Real.pi / 2),
      |Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)|
        ≤ L * (Real.pi / 2 - θ') ^ β * (Real.sin t * (Real.cos t) ^ 2) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hθ'.1 ht.1
    have ht1 : t < Real.pi / 2 := ht.2
    have hsin : 0 ≤ Real.sin t :=
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos]))
    have hcos : 0 ≤ Real.cos t :=
      le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ht1⟩)
    have hsq : 0 ≤ Real.sin t * (Real.cos t) ^ 2 := mul_nonneg hsin (pow_nonneg hcos 2)
    have hGt : |G t - c₁| ≤ L * (Real.pi / 2 - t) ^ β := h1 t ⟨ht0, ht1⟩
    have hdt : Real.pi / 2 - t ≤ Real.pi / 2 - θ' := by linarith [ht.1]
    have hd0 : 0 ≤ Real.pi / 2 - t := by linarith [ht1]
    have hrp : (Real.pi / 2 - t) ^ β ≤ (Real.pi / 2 - θ') ^ β := Real.rpow_le_rpow hd0 hdt hβ.le
    calc |Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)|
        = (Real.sin t * (Real.cos t) ^ 2) * |G t - c₁| := by
          rw [abs_mul, abs_of_nonneg hsq]
      _ ≤ (Real.sin t * (Real.cos t) ^ 2) * (L * (Real.pi / 2 - t) ^ β) :=
          mul_le_mul_of_nonneg_left hGt hsq
      _ ≤ (Real.sin t * (Real.cos t) ^ 2) * (L * (Real.pi / 2 - θ') ^ β) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrp hL) hsq
      _ = L * (Real.pi / 2 - θ') ^ β * (Real.sin t * (Real.cos t) ^ 2) := by ring
  -- pointwise bound on `(θ, θ')` (distance `≤ Real.pi/2 - θ`)
  have hpt : ∀ t ∈ Set.Ioo θ θ',
      |Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)|
        ≤ L * (Real.pi / 2 - θ) ^ β * (Real.sin t * (Real.cos t) ^ 2) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hθ.1 ht.1
    have ht1 : t < Real.pi / 2 := by linarith [ht.2, hθ'le]
    have hsin : 0 ≤ Real.sin t :=
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos]))
    have hcos : 0 ≤ Real.cos t :=
      le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ht1⟩)
    have hsq : 0 ≤ Real.sin t * (Real.cos t) ^ 2 := mul_nonneg hsin (pow_nonneg hcos 2)
    have hGt : |G t - c₁| ≤ L * (Real.pi / 2 - t) ^ β := h1 t ⟨ht0, ht1⟩
    have hdt : Real.pi / 2 - t ≤ Real.pi / 2 - θ := by linarith [ht.1]
    have hd0 : 0 ≤ Real.pi / 2 - t := by linarith [ht1]
    have hrp : (Real.pi / 2 - t) ^ β ≤ (Real.pi / 2 - θ) ^ β := Real.rpow_le_rpow hd0 hdt hβ.le
    calc |Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)|
        = (Real.sin t * (Real.cos t) ^ 2) * |G t - c₁| := by
          rw [abs_mul, abs_of_nonneg hsq]
      _ ≤ (Real.sin t * (Real.cos t) ^ 2) * (L * (Real.pi / 2 - t) ^ β) :=
          mul_le_mul_of_nonneg_left hGt hsq
      _ ≤ (Real.sin t * (Real.cos t) ^ 2) * (L * (Real.pi / 2 - θ) ^ β) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrp hL) hsq
      _ = L * (Real.pi / 2 - θ) ^ β * (Real.sin t * (Real.cos t) ^ 2) := by ring
  -- the endpoint bound at `θ'`
  have htail : |∫ t in θ'..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)|
      ≤ L * (Real.pi / 2 - θ') ^ β * (Real.cos θ') ^ 3 / 3 := by
    have hf : IntervalIntegrable (fun t : ℝ => Real.sin t * (Real.cos t) ^ 2 * (G t - c₁))
        volume θ' (Real.pi / 2) := hInt θ' hθ'
    have hb : IntervalIntegrable
        (fun t : ℝ => L * (Real.pi / 2 - θ') ^ β * (Real.sin t * (Real.cos t) ^ 2))
        volume θ' (Real.pi / 2) :=
      (by fun_prop : Continuous fun t : ℝ =>
        L * (Real.pi / 2 - θ') ^ β * (Real.sin t * (Real.cos t) ^ 2)).intervalIntegrable _ _
    have h2' : (∫ t in θ'..(Real.pi / 2), |Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)|)
        ≤ ∫ t in θ'..(Real.pi / 2),
            L * (Real.pi / 2 - θ') ^ β * (Real.sin t * (Real.cos t) ^ 2) :=
      intervalIntegral.integral_mono_on_of_le_Ioo hθ'le hf.abs hb hpt'
    have h3' : (∫ t in θ'..(Real.pi / 2),
          L * (Real.pi / 2 - θ') ^ β * (Real.sin t * (Real.cos t) ^ 2))
        = L * (Real.pi / 2 - θ') ^ β * ((Real.cos θ') ^ 3 / 3) := by
      rw [intervalIntegral.integral_const_mul, integral_sin_mul_cos_sq θ']
    calc |∫ t in θ'..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)|
        ≤ ∫ t in θ'..(Real.pi / 2), |Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)| :=
          intervalIntegral.abs_integral_le_integral_abs hθ'le
      _ ≤ ∫ t in θ'..(Real.pi / 2),
            L * (Real.pi / 2 - θ') ^ β * (Real.sin t * (Real.cos t) ^ 2) := h2'
      _ = L * (Real.pi / 2 - θ') ^ β * ((Real.cos θ') ^ 3 / 3) := h3'
      _ = L * (Real.pi / 2 - θ') ^ β * (Real.cos θ') ^ 3 / 3 := by ring
  -- the intermediate value of the primitive of `sin · cos²`
  have hcosint : (∫ t in θ..θ', Real.sin t * (Real.cos t) ^ 2)
      = (Real.cos θ) ^ 3 / 3 - (Real.cos θ') ^ 3 / 3 := by
    have hc : Continuous fun t : ℝ => Real.sin t * (Real.cos t) ^ 2 := by fun_prop
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := volume) θ θ')
      (hc.intervalIntegrable (μ := volume) θ' (Real.pi / 2))
    rw [integral_sin_mul_cos_sq θ, integral_sin_mul_cos_sq θ'] at hadd
    linarith
  -- the two-point bound
  have hFbound : |(∫ t in θ..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (G t - c₁))
      - (∫ t in θ'..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (G t - c₁))|
      ≤ L * (Real.pi / 2 - θ) ^ β * ((Real.cos θ) ^ 3 - (Real.cos θ') ^ 3) / 3 := by
    have hff : IntervalIntegrable (fun t : ℝ => Real.sin t * (Real.cos t) ^ 2 * (G t - c₁))
        volume θ θ' :=
      (hInt θ hθ).mono_set (by
        rw [Set.uIcc_of_le hle, Set.uIcc_of_le hθle]
        exact Set.Icc_subset_Icc le_rfl hθ'le)
    have hadd := intervalIntegral.integral_add_adjacent_intervals hff (hInt θ' hθ')
    have hdiff : (∫ t in θ..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (G t - c₁))
        - (∫ t in θ'..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (G t - c₁))
        = ∫ t in θ..θ', Real.sin t * (Real.cos t) ^ 2 * (G t - c₁) := by linarith
    have hb : IntervalIntegrable
        (fun t : ℝ => L * (Real.pi / 2 - θ) ^ β * (Real.sin t * (Real.cos t) ^ 2))
        volume θ θ' :=
      (by fun_prop : Continuous fun t : ℝ =>
        L * (Real.pi / 2 - θ) ^ β * (Real.sin t * (Real.cos t) ^ 2)).intervalIntegrable _ _
    have h2 : (∫ t in θ..θ', |Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)|)
        ≤ ∫ t in θ..θ', L * (Real.pi / 2 - θ) ^ β * (Real.sin t * (Real.cos t) ^ 2) :=
      intervalIntegral.integral_mono_on_of_le_Ioo hle hff.abs hb hpt
    have h3 : (∫ t in θ..θ', L * (Real.pi / 2 - θ) ^ β * (Real.sin t * (Real.cos t) ^ 2))
        = L * (Real.pi / 2 - θ) ^ β * ((Real.cos θ) ^ 3 / 3 - (Real.cos θ') ^ 3 / 3) := by
      rw [intervalIntegral.integral_const_mul, hcosint]
    rw [hdiff]
    calc |∫ t in θ..θ', Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)|
        ≤ ∫ t in θ..θ', |Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)| :=
          intervalIntegral.abs_integral_le_integral_abs hle
      _ ≤ ∫ t in θ..θ', L * (Real.pi / 2 - θ) ^ β * (Real.sin t * (Real.cos t) ^ 2) := h2
      _ = L * (Real.pi / 2 - θ) ^ β * ((Real.cos θ) ^ 3 / 3 - (Real.cos θ') ^ 3 / 3) := h3
      _ = L * (Real.pi / 2 - θ) ^ β * ((Real.cos θ) ^ 3 - (Real.cos θ') ^ 3) / 3 := by ring
  -- final algebra
  have hcos_pos' : 0 < Real.cos θ' :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ'.1, Real.pi_pos], hθ'.2⟩
  have hcosle : Real.cos θ' ≤ Real.cos θ :=
    Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hθ.1)
      (by linarith [hθ'.2, Real.pi_pos]) hle
  have hδ'nn : 0 ≤ Real.pi / 2 - θ' := by linarith [hθ'.2]
  have hδδ : Real.pi / 2 - θ' ≤ Real.pi / 2 - θ := by linarith [hle]
  have hδpos : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have hcoslow : 2 / Real.pi * (Real.pi / 2 - θ) ≤ Real.cos θ := by
    have h := Real.mul_le_sin (x := Real.pi / 2 - θ) (by linarith [hθ.2])
      (by linarith [hθ.1])
    have h2 : Real.cos θ = Real.sin (Real.pi / 2 - θ) := by
      have := Real.cos_pi_div_two_sub (Real.pi / 2 - θ)
      rwa [show Real.pi / 2 - (Real.pi / 2 - θ) = θ from by ring] at this
    linarith [h, h2]
  have hsub : Real.cos θ - Real.cos θ' ≤ θ' - θ := by
    have h := Real.abs_cos_sub_cos_le θ θ'
    rw [abs_of_nonneg (sub_nonneg.mpr hcosle),
      abs_of_nonpos (sub_nonpos.mpr hle)] at h
    linarith
  have hdδ : θ' - θ ≤ Real.pi / 2 - θ := by linarith [hθ'le]
  have hsubst : ((Real.cos θ) ^ 3)⁻¹ * (∫ t in θ..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * G t)
      - ((Real.cos θ') ^ 3)⁻¹
        * (∫ t in θ'..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * G t)
      = ((Real.cos θ) ^ 3)⁻¹ * (∫ t in θ..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (G t - c₁))
        - ((Real.cos θ') ^ 3)⁻¹
          * (∫ t in θ'..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * (G t - c₁)) := by
    have hA := hWid θ hθ
    have hB := hWid θ' hθ'
    linarith
  rw [hsubst, abs_of_nonpos (sub_nonpos.mpr hle),
    show -(θ - θ') = θ' - θ from by ring]
  exact wRateArithAux hL hcos_pos' hcosle hδ'nn hδδ hδpos hβ hβ1 hcoslow hsub hdδ hFbound htail

theorem wRateModulusUnif {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {L c₁ : ℝ}, 0 ≤ L → ∀ {G : ℝ → ℝ},
      ContinuousOn G (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
      (∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |G t - c₁| ≤ L * (Real.pi / 2 - t) ^ β) →
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |((Real.cos θ) ^ 3)⁻¹ * (∫ t in θ..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * G t)
          - ((Real.cos θ') ^ 3)⁻¹
            * (∫ t in θ'..(Real.pi / 2), Real.sin t * (Real.cos t) ^ 2 * G t)|
          ≤ C * L * |θ - θ'| ^ β := by
  refine ⟨4, by norm_num, ?_⟩
  intro L c₁ hL G hGc h1 θ hθ θ' hθ'
  rcases le_total θ θ' with hle | hle
  · exact wRateOrdered hβ hβ1 hL hGc h1 hθ hθ' hle
  · have h2 := wRateOrdered hβ hβ1 hL hGc h1 hθ' hθ hle
    rw [abs_sub_comm, abs_sub_comm θ θ']
    exact h2

end Work.FTS_EllLimOK.ProducerH.H2
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.SliceBound.slice_second_deriv_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.SliceBound

open Set Real Filter
open scoped Real Topology

local notation "sliceI" => Set.Ioo 0 (π / 2)

/-!
# The angular slice ODE: boundedness of `S''`

We consider a function `S : ℝ → ℝ` of class `C²` on `(0, π/2)` solving the linear ODE

  `S''(θ) = tan θ · S'(θ) + cos(θ)⁻² · S(θ) - 6 S(θ) - G(θ)`

with `f := sin(2θ)/2 · S' + S`, and `S`, `f`, `G` bounded by `M`.  The claim is that `S''`
is bounded by `K · M` on `(0, π/2)`.

The key point is that the ODE, rewritten in terms of the combination

  `W θ = f θ / cos²θ - 2 S θ = V θ / cos²θ`,   `V θ = f θ - 2 S θ cos²θ`,

becomes `W' = tan θ (3 W - G)` (equivalently `V' = tan θ (V - G cos²θ)`).  Then
`Z θ = 3 V θ cos θ - M cos³θ` satisfies `Z' = 3 sin θ cos²θ (M - G) ≥ 0`, so `Z` is
nondecreasing on `(0, π/2)`.  If `W θ₀ > M/3` at some point, then `Z θ₀ > 0` and
`Z θ ≥ Z θ₀ > 0` for all `θ ≥ θ₀`, which together with `V ≤ M + 2 M cos²` (from
`f = V + 2 S cos²` and the bound on `S`) forces `Z₀ ≤ 9 M cos θ` on `(θ₀, π/2)`, hence
`Z₀ ≤ 0` in the limit `θ → π/2`: a contradiction.  So `W ≤ M/3`; the mirror argument with
`Zt θ = 3 V θ cos θ + M cos³θ` (nonincreasing, `Zt' = -3 sin θ cos²θ (G + M) ≤ 0`) gives
`W ≥ -M/3`.  Finally `S'' = W - 4S - G`, so `|S''| ≤ M/3 + 4M + M ≤ 6M`.
-/

/-- `f θ = sin (2θ) / 2 * S'(θ) + S θ`. -/
noncomputable def sliceF (S : ℝ → ℝ) (θ : ℝ) : ℝ :=
  Real.sin (2 * θ) / 2 * deriv S θ + S θ

/-- `V θ = f θ - 2 S θ cos²θ`, the "homogeneous variable" of the ODE. -/
noncomputable def sliceV (S : ℝ → ℝ) (θ : ℝ) : ℝ :=
  sliceF S θ - 2 * S θ * (Real.cos θ) ^ 2

/-- `Z θ = 3 V θ cos θ - M cos³θ`; it is nondecreasing on `(0, π/2)`. -/
noncomputable def sliceZ (S : ℝ → ℝ) (M θ : ℝ) : ℝ :=
  3 * sliceV S θ * Real.cos θ - M * (Real.cos θ) ^ 3

/-- `Zt θ = 3 V θ cos θ + M cos³θ`; it is nonincreasing on `(0, π/2)`. -/
noncomputable def sliceZt (S : ℝ → ℝ) (M θ : ℝ) : ℝ :=
  3 * sliceV S θ * Real.cos θ + M * (Real.cos θ) ^ 3


end Work.FTS_EllLimOK.ProducerH.SliceBound
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.cs_rpow_bounded =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

open MeasureTheory

/-- The Lebesgue measure restricted to the interval `(0, 1]`. -/
private noncomputable def csMu : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)

/-- `v^(β/2) * v^(β/2) = v^β` for `v > 0` — the split of the `rpow` weight. -/
private lemma half_rpow_mul {β v : ℝ} (hv : 0 < v) :
    v ^ (β / 2) * v ^ (β / 2) = v ^ β := by
  rw [← Real.rpow_add hv, show β / 2 + β / 2 = β by ring]

/-- Abstract Cauchy–Schwarz on a measure space, with only `Integrable` hypotheses
(no measurability assumption on `f` or `g`): `(∫ f g)² ≤ (∫ f²)(∫ g²)`.

Proof: for every real `t` the integral `∫ (f - t g)²` is nonnegative and expands to the
quadratic `A - 2tB + t²C`; evaluating this quadratic (at `t = B/C`, or deriving `B = 0`
when `C = 0`) gives `B² ≤ A C`. -/
private lemma cs_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable (fun x => f x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ)
    (hg : Integrable (fun x => g x ^ 2) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  suffices ∀ A B C : ℝ, A = ∫ x, f x ^ 2 ∂μ → B = ∫ x, f x * g x ∂μ →
      C = ∫ x, g x ^ 2 ∂μ → B ^ 2 ≤ A * C from this _ _ _ rfl rfl rfl
  intro A B C hA hB hC
  have hquad : ∀ t : ℝ, 0 ≤ A - 2 * t * B + t ^ 2 * C := by
    intro t
    have hae : (fun x => (f x - t * g x) ^ 2)
        =ᵐ[μ] (fun x => f x ^ 2 - 2 * t * (f x * g x) + t ^ 2 * (g x) ^ 2) :=
      Filter.Eventually.of_forall fun x => by ring
    have hnn : 0 ≤ ∫ x, (f x - t * g x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have heval : (∫ x, (f x - t * g x) ^ 2 ∂μ) = A - 2 * t * B + t ^ 2 * C := by
      have e2 : (∫ x, f x ^ 2 - 2 * t * (f x * g x) + t ^ 2 * (g x) ^ 2 ∂μ)
          = (∫ x, f x ^ 2 - 2 * t * (f x * g x) ∂μ)
            + (∫ x, t ^ 2 * (g x) ^ 2 ∂μ) :=
        integral_add (hf.sub (hfg.const_mul (2 * t))) (hg.const_mul (t ^ 2))
      have e3 : (∫ x, f x ^ 2 - 2 * t * (f x * g x) ∂μ)
          = (∫ x, f x ^ 2 ∂μ) - (∫ x, 2 * t * (f x * g x) ∂μ) :=
        integral_sub hf (hfg.const_mul (2 * t))
      have e4 : (∫ x, 2 * t * (f x * g x) ∂μ) = 2 * t * (∫ x, f x * g x ∂μ) :=
        integral_const_mul (2 * t) (fun x => f x * g x)
      have e5 : (∫ x, t ^ 2 * (g x) ^ 2 ∂μ) = t ^ 2 * (∫ x, g x ^ 2 ∂μ) :=
        integral_const_mul (t ^ 2) (fun x => g x ^ 2)
      rw [integral_congr_ae hae, e2, e3, e4, e5, ← hA, ← hB, ← hC]
    linarith [hnn, heval]
  have hA0 : 0 ≤ A := by rw [hA]; exact integral_nonneg fun x => sq_nonneg (f x)
  have hC0 : 0 ≤ C := by rw [hC]; exact integral_nonneg fun x => sq_nonneg (g x)
  by_cases hCz : C = 0
  · have hB0 : B = 0 := by
      by_contra hBn
      have h2 : 2 * ((A + 1) / (2 * B)) * B = A + 1 := by
        field_simp
      have h3 := hquad ((A + 1) / (2 * B))
      rw [hCz, mul_zero, add_zero] at h3
      linarith [h3, h2]
    rw [hB0, hCz]
    simp
  · have hCpos : 0 < C := lt_of_le_of_ne hC0 (Ne.symm hCz)
    have h4 : 0 ≤ (A - 2 * (B / C) * B + (B / C) ^ 2 * C) * C :=
      mul_nonneg (hquad (B / C)) hCpos.le
    have hid : (A - 2 * (B / C) * B + (B / C) ^ 2 * C) * C = A * C - B ^ 2 := by
      field_simp
      ring
    rw [hid] at h4
    linarith

/-- If `v ↦ v^β * a v` is integrable on `(0,1]` and `|a| ≤ M` there, then also
`v ↦ v^β * a v^2` is integrable there.  (`a` need not be measurable: it is the quotient of
the integrable `v ↦ v^β * a v` by the continuous positive function `v ↦ v^β`.) -/
private lemma integrable_sq_of_integrable {β M : ℝ} (hM : 0 ≤ M) {a : ℝ → ℝ}
    (ha : ∀ v, v ∈ Set.Ioc (0 : ℝ) 1 → |a v| ≤ M)
    (hF : Integrable (fun v : ℝ => v ^ β * a v) csMu) :
    Integrable (fun v : ℝ => v ^ β * (a v) ^ 2) csMu := by
  have hb : AEStronglyMeasurable (fun v : ℝ => v ^ (-β)) csMu :=
    (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))).aestronglyMeasurable
      measurableSet_Ioc
  have haesm : AEStronglyMeasurable a csMu := by
    have h1 : AEStronglyMeasurable (fun v : ℝ => (v ^ β * a v) * v ^ (-β)) csMu :=
      hF.aestronglyMeasurable.mul hb
    refine h1.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have h2 : v ^ β * v ^ (-β) = 1 := by
      rw [← Real.rpow_add hv.1, add_neg_cancel, Real.rpow_zero]
    calc (v ^ β * a v) * v ^ (-β) = a v * (v ^ β * v ^ (-β)) := by ring
      _ = a v * 1 := by rw [h2]
      _ = a v := by ring
  have hGaesm : AEStronglyMeasurable (fun v : ℝ => v ^ β * (a v) ^ 2) csMu := by
    have h1 : AEStronglyMeasurable (fun v : ℝ => (v ^ β * a v) * a v) csMu :=
      hF.aestronglyMeasurable.mul haesm
    exact h1.congr (Filter.Eventually.of_forall fun v => by ring)
  refine Integrable.mono' ((hF.const_mul M).norm) hGaesm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
  have hvp : 0 < v ^ β := Real.rpow_pos_of_pos hv.1 β
  have hle : |a v| ^ 2 ≤ M * |a v| := by
    rw [sq]
    exact mul_le_mul_of_nonneg_right (ha v hv) (abs_nonneg (a v))
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hvp, abs_of_nonneg hM]
  calc v ^ β * |a v| ^ 2 ≤ v ^ β * (M * |a v|) := mul_le_mul_of_nonneg_left hle hvp.le
    _ = M * (v ^ β * |a v|) := by ring

/-- Cauchy–Schwarz with the `rpow` weight split as `β = β/2 + β/2`, in the case where all
three integrability hypotheses hold. -/
private lemma cs_rpow_aux {β : ℝ} {a : ℝ → ℝ}
    (hW : Integrable (fun v : ℝ => v ^ β) csMu)
    (hF : Integrable (fun v : ℝ => v ^ β * a v) csMu)
    (hG : Integrable (fun v : ℝ => v ^ β * (a v) ^ 2) csMu) :
    (∫ v, v ^ β * a v ∂csMu) ^ 2
      ≤ (∫ v, v ^ β ∂csMu) * (∫ v, v ^ β * (a v) ^ 2 ∂csMu) := by
  have hmem : ∀ᵐ v ∂csMu, v ∈ Set.Ioc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioc
  have ee_W : (fun v : ℝ => v ^ β) =ᵐ[csMu] (fun v : ℝ => (v ^ (β / 2)) ^ 2) := by
    filter_upwards [hmem] with v hv
    rw [pow_two, half_rpow_mul hv.1]
  have ee_F : (fun v : ℝ => v ^ β * a v) =ᵐ[csMu]
      (fun v : ℝ => v ^ (β / 2) * (v ^ (β / 2) * a v)) := by
    filter_upwards [hmem] with v hv
    rw [← mul_assoc, half_rpow_mul hv.1]
  have ee_G : (fun v : ℝ => v ^ β * (a v) ^ 2) =ᵐ[csMu]
      (fun v : ℝ => (v ^ (β / 2) * a v) ^ 2) := by
    filter_upwards [hmem] with v hv
    have h2 : (v ^ (β / 2)) ^ 2 = v ^ β := by rw [pow_two, half_rpow_mul hv.1]
    rw [mul_pow, h2]
  have hp : Integrable (fun v : ℝ => (v ^ (β / 2)) ^ 2) csMu := hW.congr ee_W
  have hpq : Integrable (fun v : ℝ => v ^ (β / 2) * (v ^ (β / 2) * a v)) csMu :=
    hF.congr ee_F
  have hq : Integrable (fun v : ℝ => (v ^ (β / 2) * a v) ^ 2) csMu := hG.congr ee_G
  have key := cs_sq_le (μ := csMu) (f := fun v : ℝ => v ^ (β / 2))
    (g := fun v : ℝ => v ^ (β / 2) * a v) hp hpq hq
  rw [integral_congr_ae ee_F.symm, integral_congr_ae ee_W.symm,
    integral_congr_ae ee_G.symm] at key
  exact key

/-- Cauchy–Schwarz for the `rpow`-weighted interval integral.  For `-1 < β` and `a` bounded by `M`
on `(0,1]`, the square of `∫₀¹ v^β a(v) dv` is at most `(∫₀¹ v^β) * (∫₀¹ v^β a(v)²)`.

No measurability of `a` is assumed: if `v ↦ v^β a(v)^2` is not (interval-)integrable, then
`v ↦ v^β a(v)` is not integrable either, so by the `integral_undef` convention both sides vanish. -/
theorem cs_rpow_bounded {β M : ℝ} (hβ : -1 < β) {a : ℝ → ℝ} (hM : 0 ≤ M)
    (ha : ∀ v, v ∈ Set.Ioc (0 : ℝ) 1 → |a v| ≤ M) :
    (∫ v in (0 : ℝ)..1, v ^ β * a v) ^ 2
      ≤ (∫ v in (0 : ℝ)..1, v ^ β) * (∫ v in (0 : ℝ)..1, v ^ β * (a v) ^ 2) := by
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  simp only [intervalIntegral.integral_of_le h01]
  change (∫ v, v ^ β * a v ∂csMu) ^ 2
      ≤ (∫ v, v ^ β ∂csMu) * (∫ v, v ^ β * (a v) ^ 2 ∂csMu)
  have hW : Integrable (fun v : ℝ => v ^ β) csMu := by
    have h := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1) hβ
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h01] at h
    exact h
  by_cases hG : Integrable (fun v : ℝ => v ^ β * (a v) ^ 2) csMu
  · by_cases hF : Integrable (fun v : ℝ => v ^ β * a v) csMu
    · exact cs_rpow_aux hW hF hG
    · rw [integral_undef hF]
      have hY : 0 ≤ ∫ v, v ^ β ∂csMu := integral_nonneg_of_ae <| by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
        exact Real.rpow_nonneg hv.1.le β
      have hZ : 0 ≤ ∫ v, v ^ β * (a v) ^ 2 ∂csMu := integral_nonneg_of_ae <| by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
        exact mul_nonneg (Real.rpow_nonneg hv.1.le β) (sq_nonneg (a v))
      simpa using mul_nonneg hY hZ
  · have hFn : ¬ Integrable (fun v : ℝ => v ^ β * a v) csMu :=
      fun hF => hG (integrable_sq_of_integrable hM ha hF)
    rw [integral_undef hFn, integral_undef hG]
    simp

end Work.FTS_EllLimOK.ProducerH
end
-- ===== merged: Submission.Work.FTS_EllLimOK.SliceTrace.deriv_tendsto_zero_at_pi_div_two =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.SliceTrace

/-!
# Endpoint decay of `deriv f` at `π/2`

Auxiliary lemmas for `deriv_tendsto_zero_at_pi_div_two`.

With `g = deriv f` and `s θ = sin (2θ)` the two integrability hypotheses are

* `∫ (g')² s^{-η} < ∞`, which makes the *variation* of `g` near `π/2` small
  (fundamental theorem of calculus together with `2ab ≤ a² + b²`), and
* `∫ g² s^{-γ} < ∞` with `γ > 1`, which forces a point near `π/2` where `g` is small
  (because `s^{-γ}` fails to be integrable at `π/2`).

Combining the two gives `g x → 0`.
-/

lemma sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])

lemma sin_two_le_one {θ : ℝ} : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

/-- **Tail integrals of an `L¹`-function on `(0, π/2)` vanish at the right endpoint.** -/
theorem tendsto_setIntegral_tail_pi_div_two {F : ℝ → ℝ}
    (hF : MeasureTheory.IntegrableOn F (Set.Ioo 0 (Real.pi / 2))) :
    Filter.Tendsto (fun s : ℝ => ∫ x in Set.Ioo (Real.pi / 2 - s) (Real.pi / 2), F x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hmeas : Filter.Tendsto
      (fun s : ℝ => MeasureTheory.volume (Set.Ioo (Real.pi / 2 - s) (Real.pi / 2)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun s : ℝ => ENNReal.ofReal s) (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
      have hcont : Filter.Tendsto (fun s : ℝ => s) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (0 : ℝ)) :=
        Filter.Tendsto.mono_left Filter.tendsto_id nhdsWithin_le_nhds
      simpa only [ENNReal.ofReal_zero] using
        ENNReal.tendsto_ofReal (f := nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (m := fun s : ℝ => s) (a := 0) hcont
    have hEq : (fun s : ℝ =>
          MeasureTheory.volume (Set.Ioo (Real.pi / 2 - s) (Real.pi / 2)))
        = fun s : ℝ => ENNReal.ofReal s := by
      funext s
      rw [Real.volume_Ioo, show Real.pi / 2 - (Real.pi / 2 - s) = s by ring]
    rw [hEq]
    exact h1
  have hGint : MeasureTheory.Integrable ((Set.Ioo 0 (Real.pi / 2)).indicator F)
      MeasureTheory.volume := hF.integrable_indicator measurableSet_Ioo
  have hmain : Filter.Tendsto
      (fun s : ℝ => ∫ x in Set.Ioo (Real.pi / 2 - s) (Real.pi / 2),
        (Set.Ioo 0 (Real.pi / 2)).indicator F x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    hGint.tendsto_setIntegral_nhds_zero
      (s := fun s : ℝ => Set.Ioo (Real.pi / 2 - s) (Real.pi / 2)) hmeas
  have heq : (fun s : ℝ => ∫ x in Set.Ioo (Real.pi / 2 - s) (Real.pi / 2),
        (Set.Ioo 0 (Real.pi / 2)).indicator F x)
      =ᶠ[nhds (0 : ℝ)]
        (fun s : ℝ => ∫ x in Set.Ioo (Real.pi / 2 - s) (Real.pi / 2), F x) := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity)] with s hs
    rw [Set.mem_Iio] at hs
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [Set.mem_Ioo] at hx
    exact Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨by linarith [hx.1, hs], hx.2⟩) F
  exact Filter.Tendsto.congr' (Filter.Eventually.filter_mono nhdsWithin_le_nhds heq) hmain

/-- If `F` is integrable on `(0, π/2)` then for every target length `a > 0` and `ε > 0`
there is a tail `(t, π/2)` of length at most `a` whose integral is at most `ε`. -/
theorem exists_tail_le {F : ℝ → ℝ} (hF : MeasureTheory.IntegrableOn F (Set.Ioo 0 (Real.pi / 2)))
    {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ t ∈ Set.Ioo 0 (Real.pi / 2),
      Real.pi / 2 - t ≤ a ∧ ∫ x in Set.Ioo t (Real.pi / 2), F x ≤ ε := by
  have htail := tendsto_setIntegral_tail_pi_div_two hF
  rw [Metric.tendsto_nhdsWithin_nhds] at htail
  obtain ⟨δ, hδ0, hδ⟩ := htail ε hε
  set s : ℝ := min (min (δ / 2) a) (Real.pi / 4) with hs
  have hs0 : 0 < s := lt_min (lt_min (by linarith) ha) (by positivity)
  have hsa : s ≤ a := le_trans (min_le_left _ _) (min_le_right _ _)
  have hsδ : s < δ :=
    lt_of_le_of_lt (min_le_left _ _) (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have hsπ : s ≤ Real.pi / 4 := min_le_right _ _
  have hint : ∫ x in Set.Ioo (Real.pi / 2 - s) (Real.pi / 2), F x ≤ ε := by
    have h := hδ (x := s) (by rw [Set.mem_Ioi]; exact hs0)
      (by rw [Real.dist_eq, sub_zero, abs_of_pos hs0]; exact hsδ)
    rw [Real.dist_eq, sub_zero] at h
    exact le_of_lt (abs_lt.mp h).2
  refine ⟨Real.pi / 2 - s, ⟨by linarith [hsπ, Real.pi_pos], by linarith [hs0]⟩,
    by linarith [hsa], hint⟩

/-- Integrability of `sin (2·)^η` on a tail, for `η ≥ 0`. -/
theorem integrableOn_sin_two_rpow {η : ℝ} (hη : 0 ≤ η) {t : ℝ} (ht : 0 ≤ t) :
    MeasureTheory.IntegrableOn (fun x : ℝ => (Real.sin (2 * x)) ^ η)
      (Set.Ioo t (Real.pi / 2)) := by
  have hvol : MeasureTheory.volume (Set.Ioo t (Real.pi / 2)) ≠ ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo t (Real.pi / 2)) :=
    MeasureTheory.integrableOn_const hvol
  refine MeasureTheory.Integrable.mono' h1
    ((by fun_prop : Measurable fun x : ℝ => (Real.sin (2 * x)) ^ η).aestronglyMeasurable) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
  have hx' : 0 < Real.sin (2 * x) := sin_two_pos_of_mem_Ioo ⟨lt_of_le_of_lt ht hx.1, hx.2⟩
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx' η)]
  exact Real.rpow_le_one (le_of_lt hx') sin_two_le_one hη

/-- The `η`-weighted integral of `sin (2·)` over a tail is at most the tail length. -/
theorem setIntegral_sin_two_rpow_le_length {η : ℝ} (hη : 0 ≤ η) {t : ℝ} (ht : 0 ≤ t)
    (ht2 : t ≤ Real.pi / 2) :
    ∫ x in Set.Ioo t (Real.pi / 2), (Real.sin (2 * x)) ^ η ≤ Real.pi / 2 - t := by
  have hvol : MeasureTheory.volume (Set.Ioo t (Real.pi / 2)) ≠ ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo t (Real.pi / 2)) :=
    MeasureTheory.integrableOn_const hvol
  have hpoint : ∀ x ∈ Set.Ioo t (Real.pi / 2), (Real.sin (2 * x)) ^ η ≤ (1 : ℝ) :=
    fun x hx => Real.rpow_le_one (le_of_lt (sin_two_pos_of_mem_Ioo
      ⟨lt_of_le_of_lt ht hx.1, hx.2⟩)) sin_two_le_one hη
  calc ∫ x in Set.Ioo t (Real.pi / 2), (Real.sin (2 * x)) ^ η
      ≤ ∫ x in Set.Ioo t (Real.pi / 2), (1 : ℝ) :=
        MeasureTheory.setIntegral_mono_on (integrableOn_sin_two_rpow hη ht) h1
          measurableSet_Ioo hpoint
    _ = Real.pi / 2 - t := by
        rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioo,
          ENNReal.toReal_ofReal (show (0 : ℝ) ≤ Real.pi / 2 - t by linarith [ht2])]
        simp




end Work.FTS_EllLimOK.SliceTrace
end
-- ===== merged: Submission.Work.FTS_EllLimOK.UniqAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-- **A continuous nonnegative square on `Iθ` with vanishing integral vanishes identically.** -/
theorem eq_zero_of_integral_sq_eq_zero {g : ℝ → ℝ}
    (hcont : ContinuousOn g (Set.Icc 0 (π / 2)))
    (hint : (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2) = 0) :
    ∀ θ ∈ Work.Spaces.Iθ, g θ = 0 := by
  have hIθ : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) := rfl
  have hne : (0 : ℝ) ≠ π / 2 := ne_of_lt (by linarith [Real.pi_pos])
  have hcont' : ContinuousOn (fun θ => (g θ) ^ 2) (Set.Icc 0 (π / 2)) := hcont.pow 2
  have hnonneg : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ => (g θ) ^ 2) :=
    Filter.Eventually.of_forall fun θ => sq_nonneg _
  have hint' : IntegrableOn (fun θ => (g θ) ^ 2) Work.Spaces.Iθ :=
    hcont'.integrableOn_compact isCompact_Icc
  have hae : (fun θ => (g θ) ^ 2) =ᵐ[volume.restrict Work.Spaces.Iθ] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg hint').mp hint
  have hclos : Work.Spaces.Iθ ⊆ closure (interior Work.Spaces.Iθ) := by
    rw [hIθ]
    exact (closure_interior_Icc hne).symm.subset
  have hEqOn := MeasureTheory.Measure.eqOn_of_ae_eq hae hcont' continuousOn_const hclos
  intro θ hθ
  have h : (g θ) ^ 2 = 0 := hEqOn hθ
  exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h

end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.VopTransfer.derivUnderIntegralIoo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.VopTransfer

/-- Differentiation under the integral sign for the angular integral
`z ↦ ∫_θ^{π/2} cos s · W z s ds`, over a (non-degenerate) subinterval of `(0, π/2)`.

The proof is the standard dominated-differentiation theorem for interval integrals
(`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`): the integrand
`cos s * W z s` is jointly continuous on `V × (θ, π/2)`, its `z`-derivative
`cos s * W' z s` is uniformly bounded by the constant `C`, and `C ≥ 0` because `W` is
bounded by `C` and the strip is non-empty. -/
theorem derivUnderIntegralIoo {W W' : ℝ → ℝ → ℝ} {θ C : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    {V : Set ℝ} (hV : IsOpen V) {z₀ : ℝ} (hz₀ : z₀ ∈ V)
    (hW : ContinuousOn (Function.uncurry W) (V ×ˢ Set.Ioo θ (π / 2)))
    (hW' : ContinuousOn (Function.uncurry W') (V ×ˢ Set.Ioo θ (π / 2)))
    (hWb : ∀ x ∈ V, ∀ s ∈ Set.Ioo θ (π / 2), |W x s| ≤ C)
    (hW'b : ∀ x ∈ V, ∀ s ∈ Set.Ioo θ (π / 2), |W' x s| ≤ C)
    (hd : ∀ s ∈ Set.Ioo θ (π / 2), ∀ x ∈ V, HasDerivAt (fun x' => W x' s) (W' x s) x) :
    HasDerivAt (fun z => ∫ s in θ..(π / 2), Real.cos s * W z s)
      (∫ s in θ..(π / 2), Real.cos s * W' z₀ s) z₀ := by
  have hle : θ ≤ π / 2 := le_of_lt hθ.2
  -- the constant `C` is nonnegative: `W` is bounded by `C` on the non-empty strip.
  have hC : 0 ≤ C := by
    have hs : (θ + π / 2) / 2 ∈ Set.Ioo θ (π / 2) :=
      ⟨by linarith [hθ.2], by linarith [hθ.2]⟩
    have h1 : |W z₀ ((θ + π / 2) / 2)| ≤ C := hWb z₀ hz₀ _ hs
    have h2 : (0 : ℝ) ≤ |W z₀ ((θ + π / 2) / 2)| := abs_nonneg _
    linarith
  -- slices of a jointly continuous function are continuous on the open interval
  have hslice : ∀ (f : ℝ → ℝ → ℝ), ContinuousOn (Function.uncurry f) (V ×ˢ Set.Ioo θ (π / 2)) →
      ∀ x ∈ V, ContinuousOn (fun t => f x t) (Set.Ioo θ (π / 2)) := by
    intro f hf x hx
    have hg : Continuous fun t : ℝ => (x, t) := continuous_const.prodMk continuous_id
    have hmaps : Set.MapsTo (fun t : ℝ => (x, t)) (Set.Ioo θ (π / 2))
        (V ×ˢ Set.Ioo θ (π / 2)) := fun t ht => ⟨hx, ht⟩
    have hcomp := hf.comp hg.continuousOn hmaps
    have heq : (Function.uncurry f ∘ fun t : ℝ => (x, t)) = fun t => f x t := by
      funext t
      rfl
    rwa [heq] at hcomp
  -- the measure `volume.restrict (θ, π/2)` does not see the right endpoint
  have hμ : volume.restrict (Set.uIoc θ (π / 2)) = volume.restrict (Set.Ioo θ (π / 2)) := by
    rw [Set.uIoc_of_le hle]
    exact (MeasureTheory.restrict_Ioo_eq_restrict_Ioc).symm
  have hmeasIoo : ∀ (f : ℝ → ℝ → ℝ),
      ContinuousOn (Function.uncurry f) (V ×ˢ Set.Ioo θ (π / 2)) → ∀ x ∈ V,
      AEStronglyMeasurable (fun t => Real.cos t * f x t)
        (volume.restrict (Set.Ioo θ (π / 2))) := by
    intro f hf x hx
    exact (Real.continuous_cos.continuousOn.mul (hslice f hf x hx)).aestronglyMeasurable
      isOpen_Ioo.measurableSet
  have hF_meas : ∀ᶠ x in 𝓝 z₀, AEStronglyMeasurable (fun t => Real.cos t * W x t)
      (volume.restrict (Set.uIoc θ (π / 2))) := by
    filter_upwards [hV.mem_nhds hz₀] with x hx
    rw [hμ]
    exact hmeasIoo W hW x hx
  have hF'_meas : AEStronglyMeasurable (fun t => Real.cos t * W' z₀ t)
      (volume.restrict (Set.uIoc θ (π / 2))) := by
    rw [hμ]
    exact hmeasIoo W' hW' z₀ hz₀
  have hF_int : IntervalIntegrable (fun t => Real.cos t * W z₀ t) volume θ (π / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hle]
    refine MeasureTheory.IntegrableOn.of_bound (s := Set.Ioo θ (π / 2)) ?_ ?_ C ?_
    · rw [Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top
    · exact hmeasIoo W hW z₀ hz₀
    · refine MeasureTheory.ae_restrict_of_forall_mem isOpen_Ioo.measurableSet fun t ht => ?_
      rw [Real.norm_eq_abs, abs_mul]
      calc |Real.cos t| * |W z₀ t| ≤ 1 * C :=
            mul_le_mul (Real.abs_cos_le_one t) (hWb z₀ hz₀ t ht) (abs_nonneg _) zero_le_one
        _ = C := one_mul C
  have hbound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc θ (π / 2) → ∀ x ∈ V,
      ‖Real.cos t * W' x t‖ ≤ C :=
    Eventually.of_forall fun t ht x hx => by
      rw [Set.uIoc_of_le hle] at ht
      rcases eq_or_lt_of_le ht.2 with h | h
      · subst h
        rw [Real.cos_pi_div_two, zero_mul, norm_zero]
        exact hC
      · rw [Real.norm_eq_abs, abs_mul]
        calc |Real.cos t| * |W' x t| ≤ 1 * C :=
              mul_le_mul (Real.abs_cos_le_one t) (hW'b x hx t ⟨ht.1, h⟩) (abs_nonneg _)
                zero_le_one
          _ = C := one_mul C
  have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc θ (π / 2) → ∀ x ∈ V,
      HasDerivAt (fun x' => Real.cos t * W x' t) (Real.cos t * W' x t) x :=
    Eventually.of_forall fun t ht x hx => by
      rw [Set.uIoc_of_le hle] at ht
      rcases eq_or_lt_of_le ht.2 with h | h
      · subst h
        have hfun : (fun x' : ℝ => Real.cos (π / 2) * W x' (π / 2)) = fun _ : ℝ => 0 := by
          funext x'
          rw [Real.cos_pi_div_two, zero_mul]
        rw [hfun, show Real.cos (π / 2) * W' x (π / 2) = 0 by
          rw [Real.cos_pi_div_two, zero_mul]]
        exact hasDerivAt_const x 0
      · exact (hd t ⟨ht.1, h⟩ x hx).const_mul (Real.cos t)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := volume) (E := ℝ) (a := θ) (b := π / 2) (bound := fun _ => C)
    (F := fun z s => Real.cos s * W z s) (F' := fun z s => Real.cos s * W' z s)
    (x₀ := z₀) (s := V)
    (hV.mem_nhds hz₀) hF_meas hF_int hF'_meas hbound intervalIntegrable_const hdiff).2

end Work.FTS_EllLimOK.VopTransfer
end
-- ===== merged: Submission.Work.FTS_EllLimOK.abs_sub_le_of_box_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK

theorem abs_sub_le_of_box_bounds {g : ℝ → ℝ → ℝ} {a b c d L : ℝ}
    (hz : ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a b,
      HasDerivWithinAt (fun z' : ℝ => g z' θ) (Work.Spaces.pz g z θ) (Set.Icc a b) z)
    (hth : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      HasDerivWithinAt (fun θ' : ℝ => g z θ') (Work.Spaces.pth g z θ) (Set.Icc c d) θ)
    (hzb : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, |Work.Spaces.pz g z θ| ≤ L)
    (hthb : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, |Work.Spaces.pth g z θ| ≤ L) :
    ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d, ∀ q ∈ Set.Icc a b ×ˢ Set.Icc c d,
      |g p.1 p.2 - g q.1 q.2| ≤ L * (|p.1 - q.1| + |p.2 - q.2|) := by
  intro p hp q hq
  rw [Set.mem_prod] at hp hq
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  -- Mean value inequality along the `z`-direction, at fixed angle `p.2`.
  have hzline : ‖g p.1 p.2 - g q.1 p.2‖ ≤ L * ‖p.1 - q.1‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun z' : ℝ => g z' p.2) (f' := fun z' : ℝ => Work.Spaces.pz g z' p.2)
      (fun z' hz' => hz p.2 hp2 z' hz')
      (fun z' hz' => by simpa using hzb z' hz' p.2 hp2)
      (convex_Icc a b) hq1 hp1
  -- Mean value inequality along the `θ`-direction, at fixed radius `q.1`.
  have hthline : ‖g q.1 p.2 - g q.1 q.2‖ ≤ L * ‖p.2 - q.2‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun θ' : ℝ => g q.1 θ') (f' := fun θ' : ℝ => Work.Spaces.pth g q.1 θ')
      (fun θ' hθ' => hth q.1 hq1 θ' hθ')
      (fun θ' hθ' => by simpa using hthb q.1 hq1 θ' hθ')
      (convex_Icc c d) hq2 hp2
  have h1 : |g p.1 p.2 - g q.1 p.2| ≤ L * |p.1 - q.1| := by simpa using hzline
  have h2 : |g q.1 p.2 - g q.1 q.2| ≤ L * |p.2 - q.2| := by simpa using hthline
  calc |g p.1 p.2 - g q.1 q.2|
      = |(g p.1 p.2 - g q.1 p.2) + (g q.1 p.2 - g q.1 q.2)| := by ring_nf
    _ ≤ |g p.1 p.2 - g q.1 p.2| + |g q.1 p.2 - g q.1 q.2| := abs_add_le _ _
    _ ≤ L * |p.1 - q.1| + L * |p.2 - q.2| := add_le_add h1 h2
    _ = L * (|p.1 - q.1| + |p.2 - q.2|) := by ring

end Work.FTS_EllLimOK
end
-- ===== merged: Submission.Work.FTS_EllLimOK.aemeasurable_slice_of_tendsto_Ioo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

/-- A pointwise limit, on the open interval `(0, π/2)`, of functions continuous there is
almost everywhere measurable for the measure `volume` restricted to `Iθ = [0, π/2]`.

The endpoints `0` and `π/2` are null for `volume`, so the restricted measures on the open
and the closed interval coincide, and on the open interval the limit of measurable
functions is measurable. -/
theorem aemeasurable_slice_of_tendsto_Ioo {un : ℕ → ℝ → ℝ} {u : ℝ → ℝ}
    (hcont : ∀ n : ℕ, ContinuousOn (un n) (Set.Ioo (0 : ℝ) (π / 2)))
    (hconv : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Filter.Tendsto (fun n => un n θ) Filter.atTop (nhds (u θ))) :
    AEMeasurable u (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hs : MeasurableSet (Set.Ioo (0 : ℝ) (π / 2)) := isOpen_Ioo.measurableSet
  -- On the open interval the limit is a.e. measurable.
  have h1 : AEMeasurable u (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    refine aemeasurable_of_tendsto_metrizable_ae' (fun n => (hcont n).aemeasurable hs) ?_
    filter_upwards [ae_restrict_mem hs] with θ hθ
    exact hconv θ hθ
  -- The open and closed intervals differ by the null set `{0, π/2}`.
  rw [Work.Spaces.Iθ, ← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
  exact h1

end Work.FTS_EllLimOK
end
-- ===== merged: Submission.Work.FTS_EllLimOK.phi_eq_zero_of_euler_gap_weighted =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `phi_eq_zero_of_euler_gap_weighted`

Weighted variant of `EllipticEst.phi_eq_zero_of_euler_gap`: a non-negative `C²` function `Φ` on
`(0,∞)` which

* is integrable on `(0,∞)`;
* satisfies the Euler-gap inequality `α²z²Φ'' + α(5+α)zΦ' ≥ 0`;
* has `Φ z · z^{-4}` integrable on `(0,1)` (instead of the boundedness of `Φ'` near `0`),

vanishes identically.

The proof is the same Euler-ODE argument as in the unweighted case: with `c = (5+α)/α > 1` the
inequality says `(z^c Φ')' ≥ 0`, so `G(z) = z^c Φ'(z)` is non-decreasing.  The two alternatives
`G(z₀) > 0` (then `Φ` is bounded below on a half-line and is not integrable) and `G(z₀) < 0`
(then `Φ` grows like `z^{1-c}` near `0` and `Φ z^{-4}` is not integrable) are both excluded; hence
`G ≡ 0`, `Φ` is constant, and integrability forces the constant to be `0`.
-/

namespace Work.FTS_EllLimOK

open MeasureTheory Filter
open scoped Topology

/-- The key differential computation: with `c = (5+α)/α`, the Euler gap inequality
`α²z²Φ'' + α(5+α)zΦ' ≥ 0` is equivalent, after multiplication by the positive factor
`z^{c-2}/α²`, to the nonnegativity of the derivative of `z ↦ z^c Φ'(z)`. -/
private theorem euler_key (α : ℝ) (hα : 0 < α) (Phi : ℝ → ℝ)
    (hineq : ∀ z ∈ Set.Ioi (0 : ℝ),
      0 ≤ α ^ 2 * z ^ 2 * deriv (deriv Phi) z + α * (5 + α) * z * deriv Phi z)
    {z : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ)) :
    0 ≤ ((5 + α) / α) * z ^ (((5 + α) / α) - 1) * deriv Phi z
      + z ^ ((5 + α) / α) * deriv (deriv Phi) z := by
  set c : ℝ := (5 + α) / α with hcdef
  have hz0 : 0 < z := hz
  have hzpow : 0 < z ^ (c - 2) := Real.rpow_pos_of_pos hz0 _
  have hα2 : 0 < α ^ 2 := by positivity
  have hineqz : 0 ≤ α ^ 2 * z ^ (2 : ℝ) * deriv (deriv Phi) z + α * (5 + α) * z * deriv Phi z := by
    have h := hineq z hz
    have he : z ^ (2 : ℕ) = z ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    rwa [he] at h
  have h1 : 0 ≤ z ^ (c - 2) *
      (α ^ 2 * z ^ (2 : ℝ) * deriv (deriv Phi) z + α * (5 + α) * z * deriv Phi z) :=
    mul_nonneg hzpow.le hineqz
  have hc2 : z ^ (c - 2) * z ^ (2 : ℝ) = z ^ c := by
    rw [← Real.rpow_add hz0, show c - 2 + 2 = c from by ring]
  have hc1 : z ^ (c - 2) * z = z ^ (c - 1) := by
    calc z ^ (c - 2) * z = z ^ (c - 2) * z ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = z ^ (c - 1) := by rw [← Real.rpow_add hz0, show c - 2 + 1 = c - 1 from by ring]
  have hcα : α ^ 2 * c = α * (5 + α) := by
    rw [hcdef]; field_simp
  have key : z ^ (c - 2) *
        (α ^ 2 * z ^ (2 : ℝ) * deriv (deriv Phi) z + α * (5 + α) * z * deriv Phi z)
      = α ^ 2 * (c * z ^ (c - 1) * deriv Phi z + z ^ c * deriv (deriv Phi) z) := by
    have hA : z ^ (c - 2) * (α ^ 2 * z ^ (2 : ℝ) * deriv (deriv Phi) z)
        = α ^ 2 * (z ^ c * deriv (deriv Phi) z) := by
      calc z ^ (c - 2) * (α ^ 2 * z ^ (2 : ℝ) * deriv (deriv Phi) z)
          = α ^ 2 * ((z ^ (c - 2) * z ^ (2 : ℝ)) * deriv (deriv Phi) z) := by ring
        _ = α ^ 2 * (z ^ c * deriv (deriv Phi) z) := by rw [hc2]
    have hB : z ^ (c - 2) * (α * (5 + α) * z * deriv Phi z)
        = α ^ 2 * (c * z ^ (c - 1) * deriv Phi z) := by
      calc z ^ (c - 2) * (α * (5 + α) * z * deriv Phi z)
          = (α * (5 + α)) * ((z ^ (c - 2) * z) * deriv Phi z) := by ring
        _ = (α * (5 + α)) * (z ^ (c - 1) * deriv Phi z) := by rw [hc1]
        _ = (α ^ 2 * c) * (z ^ (c - 1) * deriv Phi z) := by rw [← hcα]
        _ = α ^ 2 * (c * z ^ (c - 1) * deriv Phi z) := by ring
    rw [mul_add, hA, hB]; ring
  have hfin : 0 ≤ c * z ^ (c - 1) * deriv Phi z + z ^ c * deriv (deriv Phi) z :=
    nonneg_of_mul_nonneg_right (key ▸ h1) hα2
  rwa [hcdef] at hfin

/-- If `f z ≥ m · z^p` for `z ∈ (0,a)` with `m > 0`, `a > 0` and `p ≤ 3`, then
`z ↦ f z · z^{-4}` is not integrable on `(0,1)`: near `0` it dominates the divergent power
`z^{p-4}`. -/
private theorem not_integrableOn_mul_rpow_Ioo {f : ℝ → ℝ} {a m p : ℝ} (ha : 0 < a) (hm : 0 < m)
    (hp : p ≤ 3) (hf : ∀ z ∈ Set.Ioo (0 : ℝ) a, m * z ^ p ≤ f z) :
    ¬ MeasureTheory.IntegrableOn (fun z => f z * z ^ (-4 : ℝ)) (Set.Ioo (0 : ℝ) 1) := by
  intro h
  set b : ℝ := min a 1 with hbdef
  have hbpos : 0 < b := lt_min ha one_pos
  have hb1 : b ≤ 1 := min_le_right _ _
  have hba : b ≤ a := min_le_left _ _
  have h' : MeasureTheory.IntegrableOn (fun z => f z * z ^ (-4 : ℝ)) (Set.Ioo (0 : ℝ) b) :=
    h.mono_set (Set.Ioo_subset_Ioo_right hb1)
  -- the dominating function `z ↦ (1/m) * (f z * z^{-4})`
  have hg : MeasureTheory.IntegrableOn (fun z => (1 / m) * (f z * z ^ (-4 : ℝ)))
      (Set.Ioo (0 : ℝ) b) := by
    change Integrable (fun z => f z * z ^ (-4 : ℝ)) (volume.restrict (Set.Ioo (0 : ℝ) b)) at h'
    change Integrable (fun z => (1 / m) * (f z * z ^ (-4 : ℝ)))
      (volume.restrict (Set.Ioo (0 : ℝ) b))
    exact h'.const_mul (1 / m)
  -- `z ↦ z^{p-4}` is dominated by it on `(0,b)`
  have hzpow : MeasureTheory.IntegrableOn (fun z => z ^ (p - 4)) (Set.Ioo (0 : ℝ) b) := by
    change Integrable (fun z => (1 / m) * (f z * z ^ (-4 : ℝ)))
      (volume.restrict (Set.Ioo (0 : ℝ) b)) at hg
    change Integrable (fun z => z ^ (p - 4)) (volume.restrict (Set.Ioo (0 : ℝ) b))
    refine hg.mono' ?_ ?_
    · exact ((continuous_id.continuousOn).rpow_const
        (fun x hx => Or.inl (ne_of_gt hx.1))).aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      have hz0 : 0 < z := hz.1
      have hza : z ∈ Set.Ioo (0 : ℝ) a := ⟨hz0, lt_of_lt_of_le hz.2 hba⟩
      have hmz : m * z ^ p ≤ f z := hf z hza
      have hz4 : (0 : ℝ) < z ^ (-4 : ℝ) := Real.rpow_pos_of_pos hz0 _
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hz0 (p - 4))]
      have hsplit : m * z ^ p * z ^ (-4 : ℝ) = m * z ^ (p - 4) := by
        rw [mul_assoc, ← Real.rpow_add hz0, show p + -4 = p - 4 from by ring]
      calc z ^ (p - 4) = (1 / m) * (m * z ^ (p - 4)) := by
            field_simp
        _ ≤ (1 / m) * (f z * z ^ (-4 : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc m * z ^ (p - 4) = m * z ^ p * z ^ (-4 : ℝ) := hsplit.symm
              _ ≤ f z * z ^ (-4 : ℝ) := mul_le_mul_of_nonneg_right hmz hz4.le
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff hbpos).mp hzpow
  linarith

/-- Grönwall comparison, "upward" direction: if `Φ' ≥ k·z^{-c}` past `z₀` (with `c > 1`), then
`Φ` is bounded below on `(z₀,∞)` by the integral of `k·z^{-c}`. -/
private theorem le_of_deriv_ge_rpow {Phi : ℝ → ℝ} {z₀ k c : ℝ} (hc : 1 < c) (hz₀ : 0 < z₀)
    (hder : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt Phi (deriv Phi z) z) (hnn : 0 ≤ Phi z₀)
    (hge : ∀ z ∈ Set.Ioi z₀, k * z ^ (-c) ≤ deriv Phi z) :
    ∀ z ∈ Set.Ioi z₀, (k / (c - 1)) * (z₀ ^ (1 - c) - z ^ (1 - c)) ≤ Phi z := by
  have hc1 : c - 1 ≠ 0 := by linarith
  have hpsi : ∀ z ∈ Set.Ioi z₀,
      HasDerivAt (fun s => Phi s + (k / (c - 1)) * s ^ (1 - c)) (deriv Phi z - k * z ^ (-c)) z := by
    intro z hz
    have hz0 : 0 < z := lt_trans hz₀ hz
    have h1 := (hder z hz0).add
      ((Real.hasDerivAt_rpow_const (x := z) (p := 1 - c) (Or.inl (ne_of_gt hz0))).const_mul
        (k / (c - 1)))
    convert h1 using 1
    rw [show (1 - c) - 1 = -c from by ring]
    field_simp
    ring
  have hmono : MonotoneOn (fun s => Phi s + (k / (c - 1)) * s ^ (1 - c)) (Set.Ici z₀) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici z₀) ?_ ?_ ?_
    · intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hz₀ hx
      exact ((hder x hx0).add
        ((Real.hasDerivAt_rpow_const (x := x) (p := 1 - c)
          (Or.inl (ne_of_gt hx0))).const_mul (k / (c - 1)))).continuousAt.continuousWithinAt
    · rw [interior_Ici]; intro x hx
      exact (hpsi x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]; intro x hx
      rw [(hpsi x hx).deriv]
      linarith [hge x hx]
  intro z hz
  have hzx : z ∈ Set.Ici z₀ := Set.mem_Ici.mpr (le_of_lt hz)
  have h := hmono (Set.mem_Ici.mpr le_rfl) hzx hz.le
  linarith

/-- Grönwall comparison, "downward" direction: if `Φ' ≤ -k·z^{-c}` below `z₀` (with `c > 1`), then
`Φ` is bounded below on `(0,z₀)` by minus the integral of `k·z^{-c}`. -/
private theorem le_of_deriv_le_rpow {Phi : ℝ → ℝ} {z₀ k c : ℝ} (hc : 1 < c) (hz₀ : 0 < z₀)
    (hder : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt Phi (deriv Phi z) z) (hnn : 0 ≤ Phi z₀)
    (hle : ∀ z ∈ Set.Ioo (0 : ℝ) z₀, deriv Phi z ≤ -(k * z ^ (-c))) :
    ∀ z ∈ Set.Ioo (0 : ℝ) z₀, (k / (c - 1)) * (z ^ (1 - c) - z₀ ^ (1 - c)) ≤ Phi z := by
  intro z hz
  have hz0 : 0 < z := hz.1
  have hzz₀ : z ≤ z₀ := le_of_lt hz.2
  have hpsi : ∀ s ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun t => Phi t - (k / (c - 1)) * t ^ (1 - c))
        (deriv Phi s + k * s ^ (-c)) s := by
    intro s hs
    have h1 := (hder s hs).sub
      ((Real.hasDerivAt_rpow_const (x := s) (p := 1 - c) (Or.inl (ne_of_gt hs))).const_mul
        (k / (c - 1)))
    convert h1 using 1
    rw [show (1 - c) - 1 = -c from by ring]
    have hc1 : c - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hmono : AntitoneOn (fun t => Phi t - (k / (c - 1)) * t ^ (1 - c)) (Set.Icc z z₀) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc z z₀) ?_ ?_ ?_
    · intro x hx
      exact (hpsi x (lt_of_lt_of_le hz0 hx.1)).continuousAt.continuousWithinAt
    · rw [interior_Icc]; intro x hx
      exact (hpsi x (lt_of_lt_of_le hz0 (le_of_lt hx.1))).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro x hx
      rw [(hpsi x (lt_of_lt_of_le hz0 (le_of_lt hx.1))).deriv]
      linarith [hle x (Set.mem_Ioo.mpr ⟨lt_of_lt_of_le hz0 (le_of_lt hx.1), hx.2⟩)]
  have h := hmono (Set.mem_Icc.mpr ⟨le_rfl, hzz₀⟩) (Set.mem_Icc.mpr ⟨hzz₀, le_rfl⟩) hzz₀
  linarith

theorem phi_eq_zero_of_euler_gap_weighted (α : ℝ) (hα : 0 < α) (Phi : ℝ → ℝ)
    (hder1 : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt Phi (deriv Phi z) z)
    (hder2 : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (deriv Phi) (deriv (deriv Phi) z) z)
    (hineq : ∀ z ∈ Set.Ioi (0 : ℝ),
      0 ≤ α ^ 2 * z ^ 2 * deriv (deriv Phi) z + α * (5 + α) * z * deriv Phi z)
    (hnonneg : ∀ z ∈ Set.Ioi (0 : ℝ), 0 ≤ Phi z)
    (hint : MeasureTheory.IntegrableOn Phi (Set.Ioi (0 : ℝ)))
    (hweight : MeasureTheory.IntegrableOn (fun z => Phi z * z ^ (-4 : ℝ)) (Set.Ioo (0 : ℝ) 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), Phi z = 0 := by
  set c : ℝ := (5 + α) / α with hcdef
  have hc : 1 < c := by
    rw [hcdef, lt_div_iff₀ hα]
    linarith
  have hc1 : (0 : ℝ) < c - 1 := by linarith
  -- the derivative of `G z = z^c Φ'(z)`
  have hGderiv : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun w : ℝ => w ^ c * deriv Phi w)
      (c * z ^ (c - 1) * deriv Phi z + z ^ c * deriv (deriv Phi) z) z := by
    intro z hz
    exact (Real.hasDerivAt_rpow_const (x := z) (p := c) (Or.inl (ne_of_gt hz))).mul (hder2 z hz)
  have hGkey : ∀ z ∈ Set.Ioi (0 : ℝ),
      0 ≤ c * z ^ (c - 1) * deriv Phi z + z ^ c * deriv (deriv Phi) z := by
    intro z hz
    have h := euler_key α hα Phi hineq hz
    rw [hcdef]
    exact h
  -- `G` is non-decreasing
  have hGmono : MonotoneOn (fun z => z ^ c * deriv Phi z) (Set.Ioi (0 : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
    · intro z hz; exact (hGderiv z hz).continuousAt.continuousWithinAt
    · rw [interior_Ioi]; intro z hz
      exact (hGderiv z hz).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]; intro z hz
      rw [(hGderiv z hz).deriv]
      exact hGkey z hz
  -- `Φ'` in terms of `G`
  have hderivPhi : ∀ z ∈ Set.Ioi (0 : ℝ), deriv Phi z = z ^ (-c) * (z ^ c * deriv Phi z) := by
    intro z hz
    have hzc : z ^ c ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hz c)
    rw [Real.rpow_neg hz.le, ← mul_assoc, inv_mul_cancel₀ hzc, one_mul]
  by_cases hcase1 : ∃ z₀ ∈ Set.Ioi (0 : ℝ), 0 < z₀ ^ c * deriv Phi z₀
  · -- `G` positive somewhere: `Φ` is bounded below on a half-line, hence not integrable
    obtain ⟨z₀, hz₀, hgt⟩ := hcase1
    have hz₀pos : (0 : ℝ) < z₀ := Set.mem_Ioi.mp hz₀
    have hge : ∀ z ∈ Set.Ioi z₀, (z₀ ^ c * deriv Phi z₀) * z ^ (-c) ≤ deriv Phi z := by
      intro z hz
      have hzlt : z₀ < z := Set.mem_Ioi.mp hz
      have hz0 : 0 < z := lt_trans hz₀pos hzlt
      have hG := hGmono hz₀ hz0 hzlt.le
      rw [hderivPhi z hz0]
      calc z₀ ^ c * deriv Phi z₀ * z ^ (-c)
          = (z₀ ^ c * deriv Phi z₀) * z ^ (-c) := by ring
        _ ≤ (z ^ c * deriv Phi z) * z ^ (-c) :=
            mul_le_mul_of_nonneg_right hG (Real.rpow_pos_of_pos hz0 (-c)).le
        _ = z ^ (-c) * (z ^ c * deriv Phi z) := by ring
    have hbound := le_of_deriv_ge_rpow hc hz₀pos hder1 (hnonneg z₀ hz₀) hge
    refine absurd hint (_root_.Work.FTS.EllipticEst.not_integrableOn_of_le_const_on_Ioi
      (a := 2 * z₀)
      (m := (z₀ ^ c * deriv Phi z₀) / (c - 1) * (z₀ ^ (1 - c) - (2 * z₀) ^ (1 - c)))
      (by linarith) ?_ ?_)
    · refine mul_pos (div_pos hgt hc1) ?_
      have h2 : (2 * z₀) ^ (1 - c) < z₀ ^ (1 - c) := by
        rw [Real.rpow_lt_rpow_iff_of_neg (by linarith : (0 : ℝ) < 2 * z₀) hz₀pos
          (by linarith : 1 - c < 0)]
        linarith
      linarith
    · intro z hz
      have hzlt : 2 * z₀ < z := Set.mem_Ioi.mp hz
      have hz0 : 0 < z := by linarith
      have hb := hbound z (Set.mem_Ioi.mpr (by linarith : z₀ < z))
      have h2 : z ^ (1 - c) ≤ (2 * z₀) ^ (1 - c) := by
        rw [Real.rpow_le_rpow_iff_of_neg hz0 (by linarith : (0 : ℝ) < 2 * z₀)
          (by linarith : 1 - c < 0)]
        linarith
      have hcoef : 0 ≤ (z₀ ^ c * deriv Phi z₀) / (c - 1) := div_nonneg hgt.le hc1.le
      calc (z₀ ^ c * deriv Phi z₀) / (c - 1) * (z₀ ^ (1 - c) - (2 * z₀) ^ (1 - c))
          ≤ (z₀ ^ c * deriv Phi z₀) / (c - 1) * (z₀ ^ (1 - c) - z ^ (1 - c)) := by
            apply mul_le_mul_of_nonneg_left _ hcoef
            linarith
        _ ≤ Phi z := hb
  · push_neg at hcase1
    by_cases hcase2 : ∃ z₀ ∈ Set.Ioi (0 : ℝ), z₀ ^ c * deriv Phi z₀ < 0
    · -- `G` negative somewhere: `Φ` grows like `z^{1-c}` near `0`
      obtain ⟨z₀, hz₀, hlt⟩ := hcase2
      set k : ℝ := -(z₀ ^ c * deriv Phi z₀) with hkdef
      have hk : 0 < k := by rw [hkdef]; linarith
      have hle : ∀ z ∈ Set.Ioo (0 : ℝ) z₀, deriv Phi z ≤ -(k * z ^ (-c)) := by
        intro z hz
        have hz0 : 0 < z := hz.1
        have hG := hGmono hz0 hz₀ (le_of_lt hz.2)
        have hGz : z ^ c * deriv Phi z ≤ -k := by
          rw [hkdef, neg_neg]
          exact hG
        rw [hderivPhi z hz0]
        calc z ^ (-c) * (z ^ c * deriv Phi z) ≤ z ^ (-c) * (-k) :=
              mul_le_mul_of_nonneg_left hGz (Real.rpow_pos_of_pos hz0 (-c)).le
          _ = -(k * z ^ (-c)) := by ring
      have hbound := le_of_deriv_le_rpow hc hz₀ hder1 (hnonneg z₀ hz₀) hle
      set z₁ : ℝ := z₀ * 2 ^ (-(1 / (c - 1))) with hz₁def
      have hz₁pos : 0 < z₁ := by
        rw [hz₁def]; exact mul_pos hz₀ (Real.rpow_pos_of_pos (by norm_num) _)
      have hz₁le : z₁ ≤ z₀ := by
        rw [hz₁def]
        calc z₀ * 2 ^ (-(1 / (c - 1))) ≤ z₀ * 2 ^ (0 : ℝ) := by
              apply mul_le_mul_of_nonneg_left _ hz₀.le
              apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
              exact neg_nonpos.mpr (div_nonneg (by norm_num) hc1.le)
          _ = z₀ := by rw [Real.rpow_zero, mul_one]
      have hz₁pow : z₁ ^ (1 - c) = 2 * z₀ ^ (1 - c) := by
        rw [hz₁def, Real.mul_rpow hz₀.le (Real.rpow_pos_of_pos (by norm_num) _).le,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        have hcne : c - 1 ≠ 0 := ne_of_gt hc1
        have he : -(1 / (c - 1)) * (1 - c) = 1 := by
          field_simp
          ring
        rw [he, Real.rpow_one]
        ring
      refine absurd hweight (not_integrableOn_mul_rpow_Ioo (a := z₁) (m := k / (2 * (c - 1)))
        (p := 1 - c) hz₁pos (by positivity) (by linarith) ?_)
      intro z hz
      have hz0 : 0 < z := hz.1
      have hzz₀ : z < z₀ := lt_of_lt_of_le hz.2 hz₁le
      have hb := hbound z (Set.mem_Ioo.mpr ⟨hz0, hzz₀⟩)
      have hzp : (2 : ℝ) * z₀ ^ (1 - c) ≤ z ^ (1 - c) := by
        rw [← hz₁pow]
        rw [Real.rpow_le_rpow_iff_of_neg hz₁pos hz0 (by linarith : 1 - c < 0)]
        exact le_of_lt hz.2
      have hid : k / (2 * (c - 1)) = k / (c - 1) * (1 / 2) := by
        rw [mul_one_div, div_div, show 2 * (c - 1) = (c - 1) * 2 from by ring]
      calc k / (2 * (c - 1)) * z ^ (1 - c)
          = k / (c - 1) * ((1 / 2) * z ^ (1 - c)) := by rw [hid]; ring
        _ ≤ k / (c - 1) * (z ^ (1 - c) - z₀ ^ (1 - c)) := by
            apply mul_le_mul_of_nonneg_left _ (div_nonneg hk.le hc1.le)
            linarith
        _ ≤ Phi z := hb
    · -- `G ≡ 0`
      push_neg at hcase2
      have hGzero : ∀ z ∈ Set.Ioi (0 : ℝ), z ^ c * deriv Phi z = 0 :=
        fun z hz => le_antisymm (hcase1 z hz) (hcase2 z hz)
      have hdz : ∀ z ∈ Set.Ioi (0 : ℝ), deriv Phi z = 0 := by
        intro z hz
        rcases mul_eq_zero.mp (hGzero z hz) with h | h
        · exact absurd h (ne_of_gt (Real.rpow_pos_of_pos hz c))
        · exact h
      have hcont : ContinuousOn Phi (Set.Ioi (0 : ℝ)) :=
        fun z hz => (hder1 z hz).continuousAt.continuousWithinAt
      have hdiff : DifferentiableOn ℝ Phi (interior (Set.Ioi (0 : ℝ))) := by
        rw [interior_Ioi]; intro z hz
        exact (hder1 z hz).differentiableAt.differentiableWithinAt
      have hmono : MonotoneOn Phi (Set.Ioi (0 : ℝ)) :=
        monotoneOn_of_deriv_nonneg (convex_Ioi 0) hcont hdiff (by
          rw [interior_Ioi]; intro z hz
          rw [hdz z hz])
      have hcont' : ContinuousOn (fun z => -Phi z) (Set.Ioi (0 : ℝ)) := fun z hz =>
        (hder1 z hz).neg.continuousAt.continuousWithinAt
      have hdiff' : DifferentiableOn ℝ (fun z => -Phi z) (interior (Set.Ioi (0 : ℝ))) := by
        rw [interior_Ioi]; intro z hz
        exact (hder1 z hz).neg.differentiableAt.differentiableWithinAt
      have hantimono : MonotoneOn (fun z => -Phi z) (Set.Ioi (0 : ℝ)) :=
        monotoneOn_of_deriv_nonneg (convex_Ioi 0) hcont' hdiff' (by
          rw [interior_Ioi]; intro z hz
          have hneg : deriv (fun z => -Phi z) z = -deriv Phi z := (hder1 z hz).neg.deriv
          rw [hneg, hdz z hz]
          norm_num)
      have h1mem : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr one_pos
      have hconst : ∀ w ∈ Set.Ioi (0 : ℝ), Phi w = Phi 1 := by
        intro w hw
        rcases le_total w 1 with h | h
        · exact le_antisymm (hmono hw h1mem h) (by have := hantimono hw h1mem h; linarith)
        · exact le_antisymm (by have := hantimono h1mem hw h; linarith) (hmono h1mem hw h)
      have hC0 : Phi 1 = 0 := by
        by_contra hne
        have hpos1 : 0 < Phi 1 := lt_of_le_of_ne (hnonneg 1 h1mem) (Ne.symm hne)
        have hint' : MeasureTheory.IntegrableOn (fun _ : ℝ => Phi 1) (Set.Ioi (0 : ℝ)) :=
          hint.congr_fun (fun w hw => hconst w hw) measurableSet_Ioi
        exact _root_.Work.FTS.EllipticEst.not_integrableOn_of_le_const_on_Ioi
          (f := fun _ : ℝ => Phi 1) (a := 1) (m := Phi 1) one_pos hpos1
          (fun z _ => le_refl _) hint'
      intro z hz
      rw [hconst z hz, hC0]

end Work.FTS_EllLimOK
end
-- ===== merged: Submission.Work.FTS_RegExport.RXB.K_mul_sqrt_le_of_L2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXB

-- the hypothesis `hM : 0 ≤ M` of the requested statement is not needed by the argument below
-- (if `M < 0` then `hL2` forces `G = 0` a.e. and the conclusion is trivial anyway)
set_option linter.unusedVariables false

open scoped Real

/-- `K` is continuous. -/
private lemma continuous_K_prv : Continuous Work.Spaces.K := by
  unfold Work.Spaces.K
  continuity

/-- `K` is nonnegative on `Iθ`. -/
private lemma K_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  rw [Work.Spaces.K]
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h2 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  positivity

/-- `K` is bounded by `3` on `Iθ`. -/
private lemma K_le_three_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : Work.Spaces.K θ ≤ 3 := by
  rw [Work.Spaces.K]
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h2 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have h3 : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  nlinarith [h1, h2, h3]

/-- Cauchy–Schwarz for the angular weight `K(θ) = 3 sin θ cos²θ`: a nonnegative `G` whose square
has integral at most `M` on `Iθ` satisfies `∫_{Iθ} K θ * G θ ≤ 5 √M`, and `θ ↦ K θ * G θ` is
integrable on `Iθ`. -/
theorem K_mul_sqrt_le_of_L2 {M : ℝ} {G : ℝ → ℝ}
    (hG : MeasureTheory.AEStronglyMeasurable G (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hnn : ∀ θ, 0 ≤ G θ)
    (hint : MeasureTheory.IntegrableOn (fun θ => (G θ) ^ 2) Work.Spaces.Iθ)
    (hL2 : (∫ θ in Work.Spaces.Iθ, (G θ) ^ 2) ≤ M) (hM : 0 ≤ M) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * G θ) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * G θ) ≤ 5 * Real.sqrt M := by
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hmem : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Work.Spaces.Iθ :=
    MeasureTheory.ae_restrict_mem hIθ_meas
  -- `K²` is integrable on `Iθ` and has integral at most `9 · (π/2)`
  have hK2_int : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ ^ 2) Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact (continuous_K_prv.pow 2).integrableOn_Icc
  have hK2_le : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ ^ 2) ≤ 9 * (π/2) := by
    have h9 : MeasureTheory.IntegrableOn (fun _ : ℝ => (9:ℝ)) Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    have hae : (fun θ : ℝ => Work.Spaces.K θ ^ 2) ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun _ => (9:ℝ)) := by
      filter_upwards [hmem] with θ hθ
      have h0 := K_nonneg_of_mem_Iθ hθ
      have h1 := K_le_three_of_mem_Iθ hθ
      nlinarith
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, (9:ℝ) := MeasureTheory.integral_mono_ae hK2_int h9 hae
      _ = 9 * (π/2) := by
        rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, Work.Spaces.Iθ,
          Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
        ring
  -- both `K` and `G` lie in `L²(Iθ)`
  have hKmem : MeasureTheory.MemLp (fun θ => Work.Spaces.K θ) 2
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq continuous_K_prv.aestronglyMeasurable).mpr hK2_int
  have hGmem : MeasureTheory.MemLp G 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hG).mpr hint
  have hKnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Spaces.K θ) := by
    filter_upwards [hmem] with θ hθ
    exact K_nonneg_of_mem_Iθ hθ
  have hGnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] G :=
    Filter.Eventually.of_forall hnn
  -- Hölder with `p = q = 2`
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) hKnn hGnn
    (by simpa using hKmem) (by simpa using hGmem)
  -- `‖K‖₂ ≤ 5`
  have hK5 : Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ ^ 2) ≤ 5 := by
    refine (Real.sqrt_le_sqrt hK2_le).trans ?_
    have h9 : 9 * (π/2) ≤ 25 := by nlinarith [Real.pi_lt_four]
    calc Real.sqrt (9 * (π/2)) ≤ Real.sqrt 25 := Real.sqrt_le_sqrt h9
      _ = 5 := by norm_num
  have hbound : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * G θ) ≤ 5 * Real.sqrt M := by
    refine hholder.trans ?_
    simp only [Real.rpow_two, ← Real.sqrt_eq_rpow]
    exact mul_le_mul hK5 (Real.sqrt_le_sqrt hL2) (Real.sqrt_nonneg _) (by norm_num)
  -- integrability of `K * G` (product of two `L²` functions)
  have hmul : MeasureTheory.MemLp (fun θ => Work.Spaces.K θ * G θ) 1
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hKmem.mul hGmem
  exact ⟨MeasureTheory.memLp_one_iff_integrable.mp hmul, hbound⟩

end Work.FTS_RegExport.RXB
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5.zhmod_of =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR5

theorem zhmod_of {α S M B : ℝ} {h : ℝ → ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hdiff : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ x ∈ Set.Ioi (0:ℝ),
      DifferentiableAt ℝ (fun z' => h z' θ τ) x)
    (hdb : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ x ∈ Set.Ioi (0:ℝ),
      |deriv (fun z' => h z' θ τ) x| ≤ M)
    (hc0 : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ,
      ContinuousAt (fun z' => h z' θ τ) 0)
    (hb : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → |h z θ τ| ≤ B) :
    ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |h z θ τ - h z' θ τ| ≤ max M (2 * B) * |z - z'| ^ α := by
  intro τ hτ θ hθ z z' hz hz'
  -- The mean value theorem on `(0, ∞)` makes each `θ`-slice `M`-Lipschitzian on `[0, ∞)`:
  -- differentiability is assumed on the open half-line and only continuity is needed at `0`.
  have hlip : ∀ y y' : ℝ, 0 ≤ y → 0 ≤ y' →
      |h y θ τ - h y' θ τ| ≤ M * |y - y'| :=
    Work.FTS.RegPkgGal.Der.Lib.lip_of_bounded_deriv hM
      (fun x hx => hdiff τ hτ θ hθ x hx)
      (fun x hx => hdb τ hτ θ hθ x hx)
      (hc0 τ hτ θ hθ)
  -- Interpolate between the Lipschitz bound (small distances) and the sup bound (large ones).
  exact Work.FTS.RegPkgGal.Der.Lib.holder_of_lipschitz_of_bounded hα hα1 hM hB hlip
    (fun y hy => hb τ hτ θ hθ y hy) z z' hz hz'

end Work.FTS_RegExport.RXR5
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.SysAux.DzIter_two_pt_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The two-point expansion `D_z² = D_z + z²∂_z²` with only an open, `C²` hypothesis

`Work.Spaces.DzIter_two_pt` proves the expansion `D_z² h = z ∂_z h + z² ∂_z² h` under the
hypothesis that the `z`-slices are *analytic* (`ContDiffOn ℝ ⊤ ...`), which is far stronger than
what the consumers of this file have available: their slices are only `C²` on the open half-line
`(0,∞)`, and only for `θ` in the open interval `(0,π/2)`.

The proof here uses only that hypothesis.  Unfold `D_z² h = D_z (D_z h)` and
`D_z g z θ = z ∂_z g(z,θ)`: the identity is the one-variable product rule in `z` applied to
`t ↦ t · ∂_z h(t,θ)`, whose second factor is differentiable at `z` because a function that is `C²`
on the open set `(0,∞)` has a `C¹` derivative there
(`ContDiffOn.deriv_of_isOpen`, then `ContDiffOn.differentiableOn`).  The value of that derivative
is `∂_z²h(z,θ) = pzIter 2 h z θ` by definition of `pzIter`.
-/

open Set Filter

namespace Work.FTS_RegExport.RXT.SysAux

/-- **The expansion `D_z² = z ∂_z + z² ∂_z²` at a point, from `C²`-smoothness of the `z`-slices.**
For `z > 0` and `θ ∈ (0,π/2)`, if the `z`-slice `z' ↦ h z' θ` is `C²` on the open half-line
`(0,∞)`, then `D_z² h z θ = z ∂_z h z θ + z² ∂_z² h z θ`. -/
theorem DzIter_two_pt_open {h : ℝ → ℝ → ℝ}
    (hsmooth : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ContDiffOn ℝ 2 (fun z => h z θ) (Set.Ioi 0))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter 2 h z θ = z * Work.Spaces.pzIter 1 h z θ
      + z ^ 2 * Work.Spaces.pzIter 2 h z θ := by
  have hzI : z ∈ Set.Ioi (0 : ℝ) := hz
  -- the `z`-slice is `C²` on the open set `(0,∞)`, hence its derivative is `C¹` there
  have hcd : ContDiffOn ℝ 2 (fun z' : ℝ => h z' θ) (Set.Ioi 0) := hsmooth θ hθ
  have hd1 : ContDiffOn ℝ 1 (deriv (fun z' : ℝ => h z' θ)) (Set.Ioi 0) :=
    hcd.deriv_of_isOpen isOpen_Ioi (by norm_num)
  -- so `t ↦ ∂_z h(t,θ) = pzIter 1 h t θ` is differentiable at `z`
  have hdiff : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.pzIter 1 h t θ) z := by
    have h2 : DifferentiableAt ℝ (deriv (fun z' : ℝ => h z' θ)) z :=
      (hd1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hzI)
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz] using h2
  have hdg : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.pz h t θ) z := by
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz] using hdiff
  -- the one-variable product rule for `t ↦ t * ∂_z h(t,θ)`
  have hderiv : deriv (fun t : ℝ => t * Work.Spaces.pz h t θ) z
      = Work.Spaces.pz h z θ + z * Work.Spaces.pzIter 2 h z θ := by
    have h1' : deriv ((fun t : ℝ => t) * fun t : ℝ => Work.Spaces.pz h t θ) z
        = deriv (fun t : ℝ => t) z * Work.Spaces.pz h z θ
          + z * deriv (fun t : ℝ => Work.Spaces.pz h t θ) z :=
      deriv_mul (c := fun t : ℝ => t) (d := fun t : ℝ => Work.Spaces.pz h t θ)
        differentiableAt_id hdg
    rw [show (fun t : ℝ => t * Work.Spaces.pz h t θ)
          = ((fun t : ℝ => t) * fun t : ℝ => Work.Spaces.pz h t θ) from rfl,
        h1', deriv_id'', one_mul]
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
  -- and the definitional unfolding `D_z² h z θ = z * ∂_z (t ↦ t * ∂_z h(t,θ)) z`
  rw [show Work.Spaces.DzIter 2 h z θ
        = z * deriv (fun t : ℝ => t * Work.Spaces.pz h t θ) z from rfl, hderiv]
  show z * (Work.Spaces.pz h z θ + z * Work.Spaces.pzIter 2 h z θ)
      = z * Work.Spaces.pzIter 1 h z θ + z ^ 2 * Work.Spaces.pzIter 2 h z θ
  rw [show Work.Spaces.pzIter 1 h = Work.Spaces.pz h from rfl]
  ring

end Work.FTS_RegExport.RXT.SysAux
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.SysAux.abs_setIntegral_Itheta_mul_K_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.SysAux

/-- On the angular interval `Iθ = [0, π/2]` the kernel `K(θ) = 3 sin θ cos²θ` is
nonnegative and bounded by `3`. -/
theorem abs_K_le_three_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ| ≤ 3 := by
  have h3 : (0 : ℝ) ≤ Real.cos θ ^ 2 := sq_nonneg _
  rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
    abs_of_nonneg h3]
  nlinarith [Real.abs_sin_le_one θ, Real.cos_sq_le_one θ, abs_nonneg (Real.sin θ)]

/-- The Lebesgue measure of `Iθ = [0, π/2]` is `π/2`. -/
theorem volume_real_Iθ : MeasureTheory.volume.real Work.Spaces.Iθ = Real.pi / 2 := by
  rw [MeasureTheory.Measure.real_def, Work.Spaces.Iθ, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2 - 0)]
  ring

/-- The Lebesgue measure of `Iθ = [0, π/2]` is finite. -/
theorem volume_Iθ_lt_top : MeasureTheory.volume Work.Spaces.Iθ < ⊤ := by
  rw [Work.Spaces.Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

theorem abs_setIntegral_Itheta_mul_K_le {G : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hmeas : MeasureTheory.AEStronglyMeasurable G (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hb : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), |G θ| ≤ c) :
    |∫ θ in Work.Spaces.Iθ, G θ * Work.Spaces.K θ| ≤ c * 3 * (Real.pi / 2) := by
  -- the pointwise bound `‖G θ * K θ‖ ≤ 3 * c` holds almost everywhere on `Iθ`
  have hC : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖G θ * Work.Spaces.K θ‖ ≤ 3 * c := by
    filter_upwards [hb, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hG hθ
    rw [Real.norm_eq_abs, abs_mul]
    calc |G θ| * |Work.Spaces.K θ| ≤ c * 3 :=
          mul_le_mul hG (abs_K_le_three_of_mem_Iθ hθ) (abs_nonneg _) hc
      _ = 3 * c := by ring
  have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae
      (μ := MeasureTheory.volume) (s := Work.Spaces.Iθ)
      (f := fun θ => G θ * Work.Spaces.K θ) (C := 3 * c) volume_Iθ_lt_top hC
  rw [Real.norm_eq_abs, volume_real_Iθ] at h
  calc |∫ θ in Work.Spaces.Iθ, G θ * Work.Spaces.K θ| ≤ 3 * c * (Real.pi / 2) := h
    _ = c * 3 * (Real.pi / 2) := by ring

end Work.FTS_RegExport.RXT.SysAux
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.cone_max_principle =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 1600000

namespace Work.FTS_RegExport.RXT

open ConeAux


end Work.FTS_RegExport.RXT
end
-- ===== merged: Submission.Work.FTS_RegExport.THL.holder_of_deriv_sin_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# **A1a** — Hölder modulus from a `sin(2x)^{p-1}` derivative bound

`Work.FTS_RegExport.THL.holder_of_deriv_sin_bound`: if `h` has derivative bounded by
`C · sin(2x)^{p-1}` on `(0, π/2)` (with `0 < p ≤ 1`), then `h` is `p`-Hölder there with
constant `2 (π/4)^{1-p} C / p`.

The proof is the fundamental theorem of calculus:

* `h b - h a = ∫_a^b h'` for `a ≤ b` in the interval; the integrability of `h'` follows by
  domination from the bound, since `h'` agrees with the (measurable) derivative `deriv h` on
  the interval;
* `|∫_a^b h'| ≤ ∫_a^b |h'| ≤ C ∫_a^b sin(2σ)^{p-1}`, and the last integral is bounded by
  `2 (π/4)^{1-p} (b - a)^p / p` — this is the sibling leaf **A1b**
  `Work.FTS_RegExport.THL.integral_sin_two_rpow_le`, imported here.
-/

namespace Work.FTS_RegExport.THL

open MeasureTheory Set intervalIntegral

theorem holder_of_deriv_sin_bound {p C : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hC : 0 ≤ C)
    {h h' : ℝ → ℝ} (hd : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi / 2), HasDerivAt h (h' x) x)
    (hb : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi / 2), |h' x| ≤ C * Real.sin (2 * x) ^ (p - 1)) :
    ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), ∀ θ' ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      |h θ - h θ'| ≤ 2 * (Real.pi / 4) ^ (1 - p) / p * C * |θ - θ'| ^ p := by
  -- the estimate for an ordered pair `a ≤ b`
  have key : ∀ a b : ℝ, a ∈ Set.Ioo (0:ℝ) (Real.pi / 2) →
      b ∈ Set.Ioo (0:ℝ) (Real.pi / 2) → a ≤ b →
      |h b - h a| ≤ 2 * (Real.pi / 4) ^ (1 - p) / p * C * (b - a) ^ p := by
    intro a b ha hbmem hab
    have hsub : Set.uIoc a b ⊆ Set.Ioo (0:ℝ) (Real.pi / 2) := by
      intro x hx
      rw [Set.uIoc_of_le hab] at hx
      exact ⟨lt_of_lt_of_le ha.1 hx.1.le, lt_of_le_of_lt hx.2 hbmem.2⟩
    have hsubIcc : Set.uIcc a b ⊆ Set.Ioo (0:ℝ) (Real.pi / 2) := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hbmem.2⟩
    -- the dominating function `C · sin(2σ)^{p-1}` is continuous on the interval
    have hsin : ContinuousOn (fun σ : ℝ => Real.sin (2 * σ)) (Set.uIcc a b) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    have hne : ∀ σ ∈ Set.uIcc a b, Real.sin (2 * σ) ≠ 0 := by
      intro σ hσ
      have hσ' := hsubIcc hσ
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ'.1]) (by linarith [hσ'.2]))
    have hcontg : ContinuousOn (fun σ : ℝ => C * Real.sin (2 * σ) ^ (p - 1)) (Set.uIcc a b) :=
      continuousOn_const.mul (hsin.rpow_const (fun σ hσ => Or.inl (hne σ hσ)))
    have hg : IntervalIntegrable (fun σ : ℝ => C * Real.sin (2 * σ) ^ (p - 1)) volume a b :=
      hcontg.intervalIntegrable
    -- `h'` agrees with `deriv h` on the interval, hence is a.e. strongly measurable
    have hfm : AEStronglyMeasurable h' (volume.restrict (Set.uIoc a b)) :=
      ((measurable_deriv h).aestronglyMeasurable).congr
        (Set.EqOn.aeEq_restrict (fun x hx => (hd x (hsub hx)).deriv) measurableSet_uIoc)
    have hbnd : (fun x => ‖h' x‖) ≤ᵐ[volume.restrict (Set.uIoc a b)]
        (fun σ => C * Real.sin (2 * σ) ^ (p - 1)) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc
        (fun x hx => by simpa only [Real.norm_eq_abs] using hb x (hsub hx))
    have hint : IntervalIntegrable h' volume a b := IntervalIntegrable.mono_fun' hg hfm hbnd
    -- fundamental theorem of calculus
    have hFTC : ∫ σ in a..b, h' σ = h b - h a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hd x (hsubIcc hx)) hint
    have hstep : |h b - h a| ≤ ∫ σ in a..b, C * Real.sin (2 * σ) ^ (p - 1) := by
      have hmain : ‖∫ σ in a..b, h' σ‖ ≤ ∫ σ in a..b, C * Real.sin (2 * σ) ^ (p - 1) :=
        intervalIntegral.norm_integral_le_of_norm_le (f := h') hab
          (Filter.Eventually.of_forall (fun σ hσ => by
            have hσ' : σ ∈ Set.uIoc a b := by rw [Set.uIoc_of_le hab]; exact hσ
            simpa only [Real.norm_eq_abs] using hb σ (hsub hσ'))) hg
      rw [← hFTC]
      simpa only [Real.norm_eq_abs] using hmain
    have hIntB := integral_sin_two_rpow_le hp hp1 ha.1 hab hbmem.2
    have hcm : ∫ σ in a..b, C * Real.sin (2 * σ) ^ (p - 1)
        = C * ∫ σ in a..b, Real.sin (2 * σ) ^ (p - 1) :=
      intervalIntegral.integral_const_mul C _
    calc |h b - h a| ≤ ∫ σ in a..b, C * Real.sin (2 * σ) ^ (p - 1) := hstep
      _ = C * ∫ σ in a..b, Real.sin (2 * σ) ^ (p - 1) := hcm
      _ ≤ C * (2 * (Real.pi / 4) ^ (1 - p) / p * (b - a) ^ p) :=
          mul_le_mul_of_nonneg_left hIntB hC
      _ = 2 * (Real.pi / 4) ^ (1 - p) / p * C * (b - a) ^ p := by ring
  intro θ hθ θ' hθ'
  rcases le_total θ θ' with hle | hle
  · have hk := key θ θ' hθ hθ' hle
    rw [abs_sub_comm (h θ) (h θ'), abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
    exact hk
  · have hk := key θ' θ hθ' hθ hle
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    exact hk

end Work.FTS_RegExport.THL
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB2.sb2_deriv_law_rhs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB2

theorem sb2_deriv_law_rhs {αG : ℝ} {P F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter 2 P z' θ) z)
    (hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter 1 P z' θ) z)
    (hd0 : DifferentiableAt ℝ (fun z' => P z' θ) z)
    (hdF : DifferentiableAt ℝ (fun z' => F z' θ) z) :
    z * deriv (fun z' => -(αG ^ 2 * Work.Spaces.DzIter 2 P z' θ
            + 5 * αG * Work.Spaces.DzIter 1 P z' θ + 6 * P z' θ) - F z' θ) z
      = -(αG ^ 2 * Work.Spaces.DzIter 3 P z θ + 5 * αG * Work.Spaces.DzIter 2 P z θ
            + 6 * Work.Spaces.DzIter 1 P z θ) - Work.Spaces.Dz F z θ := by
  -- `D_z^{k+1} X z θ = z * deriv (fun z' => D_z^k X z' θ) z`, definitionally;
  -- the claim is that `z` times the derivative of the linear combination
  -- `-(αG² · D_z²P + 5αG · D_zP + 6P) - F` is the corresponding combination of
  -- `D_z`-derivatives, i.e. pure additivity/linearity of `deriv` plus one
  -- multiplication by `z`.
  have hA : HasDerivAt (fun z' => αG ^ 2 * Work.Spaces.DzIter 2 P z' θ
        + 5 * αG * Work.Spaces.DzIter 1 P z' θ + 6 * P z' θ)
      (αG ^ 2 * deriv (fun z' => Work.Spaces.DzIter 2 P z' θ) z
        + 5 * αG * deriv (fun z' => Work.Spaces.DzIter 1 P z' θ) z
        + 6 * deriv (fun z' => P z' θ) z) z :=
    ((HasDerivAt.const_mul (αG ^ 2) hd2.hasDerivAt).add
      (HasDerivAt.const_mul (5 * αG) hd1.hasDerivAt)).add
        (HasDerivAt.const_mul 6 hd0.hasDerivAt)
  have hD : deriv (fun z' => -(αG ^ 2 * Work.Spaces.DzIter 2 P z' θ
        + 5 * αG * Work.Spaces.DzIter 1 P z' θ + 6 * P z' θ) - F z' θ) z
      = -(αG ^ 2 * deriv (fun z' => Work.Spaces.DzIter 2 P z' θ) z
        + 5 * αG * deriv (fun z' => Work.Spaces.DzIter 1 P z' θ) z
        + 6 * deriv (fun z' => P z' θ) z) - deriv (fun z' => F z' θ) z :=
    (hA.neg.sub hdF.hasDerivAt).deriv
  have h3 : Work.Spaces.DzIter 3 P z θ
      = z * deriv (fun z' => Work.Spaces.DzIter 2 P z' θ) z := rfl
  have h2 : Work.Spaces.DzIter 2 P z θ
      = z * deriv (fun z' => Work.Spaces.DzIter 1 P z' θ) z := rfl
  have h1 : Work.Spaces.DzIter 1 P z θ = z * deriv (fun z' => P z' θ) z := rfl
  have hF' : Work.Spaces.Dz F z θ = z * deriv (fun z' => F z' θ) z := rfl
  rw [hD, h3, h2, h1, hF']
  ring

end Work.FTS_StreamBdry.SB2
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB3.P2Aux.FamOde.Ode =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FamOde.Ode` — the differentiated integrating factor and the Lipschitz comparison

For `F : ℝ → ℝ` a `θ`-slice satisfying `(F')' + c·F' = H` on `(0, π/2)` with
`c = coco` (`FamOde.coco`), the product `W := m·F'` with `m = wfn` satisfies
`W' = m·H` (`hasDerivAt_W`), and `|m·H| ≤ Φ = phfn A C` whenever `|H| ≤ A/sin 2θ + C`
(`abs_wfn_mul_le`).  We also record the Lipschitz comparison
`|W b - W a| ≤ C(b-a)` from a pointwise bound `|W'| ≤ C` on `(a,b)`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB3.P2Aux.FamOde

lemma hasDerivAt_wfn {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt wfn (wfn θ * coco θ) θ := by
  have h : HasDerivAt (fun x : ℝ => Real.sin x ^ 2 * Real.cos x ^ 3)
      (2 * Real.sin θ ^ (2 - 1) * Real.cos θ * Real.cos θ ^ 3
        + Real.sin θ ^ 2 * (3 * Real.cos θ ^ (3 - 1) * -Real.sin θ)) θ :=
    (Real.hasDerivAt_sin θ).pow 2 |>.mul ((Real.hasDerivAt_cos θ).pow 3)
  have hs : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [Real.pi_pos, hθ.2]))
  have hc : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  have key : (2 * Real.sin θ ^ (2 - 1) * Real.cos θ * Real.cos θ ^ 3
        + Real.sin θ ^ 2 * (3 * Real.cos θ ^ (3 - 1) * -Real.sin θ))
      = wfn θ * coco θ := by
    simp only [wfn, coco, Real.tan_eq_sin_div_cos, Real.sin_two_mul, Real.cos_two_mul']
    field_simp
    try ring
  convert h using 1
  · rfl
  · exact key.symm

lemma hasDerivAt_W {F Hz : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hodeθ : HasDerivAt (deriv F) (Hz θ - coco θ * deriv F θ) θ) :
    HasDerivAt (fun θ' => wfn θ' * deriv F θ') (wfn θ * Hz θ) θ := by
  have h := (hasDerivAt_wfn hθ).mul hodeθ
  convert h using 1
  ring



end Work.FTS_StreamBdry.SB3.P2Aux.FamOde
end
end
-- ===== merged: Submission.Work.Spaces.ThetaAgmon.AnnulusGeom =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces.ThetaAgmon

set_option autoImplicit false

/-- The angular dyadic annulus at scale `a`: the interval `[a, 2a]`.

For `2a ≤ π/2` the annulus is contained in `Iθ = [0,π/2]` (`annulus_subset_Iθ`), and for
`4a ≤ π/2` the function `sin(2θ)` is comparable to `a` on it (`sin_two_annulus_equiv`).
The dyadic decomposition of the angular variable consists of the annuli
`annulus (2^{-(k+1)})` for `k ≥ 0` and the central piece `[1/4, π/2]` (near the upper
endpoint one uses the reflected annuli `π/2 - annulus a`). -/
def annulus (a : ℝ) : Set ℝ := Set.Icc a (2 * a)









end Work.Spaces.ThetaAgmon
end
end
-- ===== merged: Submission.Work.Spaces.one_le_mul_w =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

/-- The radial weight beats the reciprocal of `z`: `1 ≤ z · w(z)` for `z > 0`, because
`z·w(z) = (1+z)²/z = z + 2 + 1/z ≥ 1`. -/
theorem one_le_mul_w (z : ℝ) (hz : 0 < z) : 1 ≤ z * Work.Spaces.w z := by
  have hzw : z * Work.Spaces.w z = (1 + z) ^ 2 / z := by
    rw [Work.Spaces.w]
    field_simp
  rw [hzw, le_div_iff₀ hz]
  nlinarith [sq_nonneg z]

end Work.Spaces
end
