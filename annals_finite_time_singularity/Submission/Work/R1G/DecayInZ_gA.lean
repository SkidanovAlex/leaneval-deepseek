import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.Coercivity.L2CoercivityTransportEta
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.integral_sin_two_rpow_neg
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.SolutionDelivery.Slices
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.WProductRule
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.Cutoff
import Submission.Work.Stability.holderWith_of_dist_le
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Holder.holderOnWith_of_norm_le
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.ConstructionInstance.AuxOmegaStar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Topology NNReal ENNReal

namespace Work.ConstructionInstance

/-- The factor of `Γ(θ) = (sin θ cos²θ)^β` produced by `Real.rpow` at a negative base: `1` if
the base (which has the sign of `x₂`) is `≥ 0`, and `cos (βπ)` if it is `< 0`. -/
def cSign (β t : ℝ) : ℝ := if 0 ≤ t then 1 else Real.cos (β * Real.pi)

/-- The non-negative homogeneous degree `3` profile `P(x) = |x₂| r(x)²`. -/
def Pall (x : R3) : ℝ := |x 2| * (Work.Cyl.radial x) ^ 2

/-- The non-negative amplitude `A0 β x = 2 |x₂|^β r(x)^{2β} / (1 + ρ(x)^{3β})²` of the model
field (equal to `2 (Pall x)^β / (1+ρ^{3β})²`, see `A0_eq_Pall`). -/
def A0 (β : ℝ) (x : R3) : ℝ :=
  2 * |x 2| ^ β * (Work.Cyl.radial x) ^ (2 * β) / (1 + (Work.Cyl.rho x) ^ (3 * β)) ^ 2

/-- The amplitude of `omegaStar β` including the sign factor of `Real.rpow` at the negative
base: `Aom β x = cSign β (x₂) · A0 β x`. -/
def Aom (β : ℝ) (x : R3) : ℝ := cSign β (x 2) * A0 β x

/-! ## Elementary `Real.rpow` facts -/

lemma rpow_sq_mul (β r : ℝ) (hr : 0 ≤ r) : ((r ^ 2 : ℝ)) ^ β = r ^ (2 * β) := by
  rw [Real.rpow_mul hr]; norm_num

lemma rpow_two_mul (β r : ℝ) (hr : 0 ≤ r) : r ^ (2 * β) = r ^ β * r ^ β := by
  rw [← rpow_sq_mul β r hr, show r ^ 2 = r * r by ring, Real.mul_rpow hr hr]

/-- For `0 ≤ a ≤ b` and `t ≥ 0`: `t ^ a ≤ (1 + t ^ b) ^ 2`. -/
lemma rpow_le_one_add_sq (a b t : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 ≤ t) :
    t ^ a ≤ (1 + t ^ b) ^ 2 := by
  have h1 : 0 ≤ t ^ b := Real.rpow_nonneg ht b
  rcases le_total t 1 with h | h
  · refine le_trans (Real.rpow_le_one ht h ha) ?_; nlinarith
  · rcases lt_or_eq_of_le h with ht1 | heq
    · have h2 : t ^ a ≤ t ^ b := by rw [Real.rpow_le_rpow_left_iff ht1]; exact hab
      nlinarith
    · subst heq; norm_num [Real.one_rpow]

lemma denom_pos (β : ℝ) (x : R3) : 0 < (1 + (Work.Cyl.rho x) ^ (3 * β)) ^ 2 := by
  have := Real.rpow_nonneg (Work.Cyl.rho_nonneg x) (3 * β); positivity

/-! ## The amplitude `A0` -/

lemma Pall_nonneg (x : R3) : 0 ≤ Pall x := by rw [Pall]; positivity

lemma Pall_le_rho_cube (x : R3) : Pall x ≤ Work.Cyl.rho x ^ 3 := by
  have h1 : |x 2| ≤ Work.Cyl.rho x := Work.Cyl.abs_axial_le_rho x
  have h2 : (Work.Cyl.radial x) ^ 2 ≤ Work.Cyl.rho x ^ 2 := by
    rw [Work.Cyl.radial_sq]; exact Work.Cyl.radSq_le_rho_sq x
  rw [Pall]
  nlinarith [abs_nonneg (x 2), sq_nonneg (Work.Cyl.rho x)]

lemma A0_nonneg (β : ℝ) (x : R3) : 0 ≤ A0 β x := by
  rw [A0]
  have h : 0 ≤ |x 2| ^ β * (Work.Cyl.radial x) ^ (2 * β) :=
    mul_nonneg (Real.rpow_nonneg (abs_nonneg _) β)
      (Real.rpow_nonneg (Work.Cyl.radial_nonneg x) (2 * β))
  exact div_nonneg (by linarith) (denom_pos β x).le

lemma A0_eq_Pall (β : ℝ) (x : R3) :
    A0 β x = 2 * (Pall x) ^ β / (1 + (Work.Cyl.rho x) ^ (3 * β)) ^ 2 := by
  have hr : 0 ≤ Work.Cyl.radial x := Work.Cyl.radial_nonneg x
  have hP : (Pall x) ^ β = |x 2| ^ β * (Work.Cyl.radial x) ^ (2 * β) := by
    rw [Pall, Real.mul_rpow (abs_nonneg (x 2)) (by positivity),
      ← rpow_sq_mul β (Work.Cyl.radial x) hr]
  rw [A0, hP]; ring

/-- `|x₂| r ≤ ρ²`. -/
lemma abs_ax_mul_radial_le (x : R3) :
    |x 2| * Work.Cyl.radial x ≤ Work.Cyl.rho x ^ 2 := by
  have h1 : |x 2| ≤ Work.Cyl.rho x := Work.Cyl.abs_axial_le_rho x
  have h2 : (Work.Cyl.radial x) ^ 2 ≤ Work.Cyl.rho x ^ 2 := by
    rw [Work.Cyl.radial_sq]; exact Work.Cyl.radSq_le_rho_sq x
  have h3 : 0 ≤ Work.Cyl.radial x := Work.Cyl.radial_nonneg x
  nlinarith [abs_nonneg (x 2), sq_nonneg (Work.Cyl.rho x - Work.Cyl.radial x)]

lemma A0_le_half (β : ℝ) (hβ : 0 < β) (x : R3) : A0 β x ≤ 1 / 2 := by
  have hρ : 0 ≤ Work.Cyl.rho x := Work.Cyl.rho_nonneg x
  have hP : Pall x ≤ Work.Cyl.rho x ^ 3 := Pall_le_rho_cube x
  have hP0 : 0 ≤ Pall x := Pall_nonneg x
  have h4 : (Pall x) ^ β ≤ (Work.Cyl.rho x ^ (3 : ℝ)) ^ β :=
    Real.rpow_le_rpow hP0 (by norm_num; exact hP) hβ.le
  have h5 : (Work.Cyl.rho x ^ (3 : ℝ)) ^ β = Work.Cyl.rho x ^ (3 * β) :=
    (Real.rpow_mul hρ 3 β).symm
  rw [A0_eq_Pall, div_le_iff₀ (denom_pos β x)]
  set t := Work.Cyl.rho x ^ (3 * β) with ht
  have ht0 : 0 ≤ t := by rw [ht]; exact Real.rpow_nonneg hρ _
  have h6 : (Pall x) ^ β ≤ t := h5 ▸ h4
  rw [ht] at h6
  nlinarith [sq_nonneg (1 - t)]

lemma A0_le_ax (β : ℝ) (hβ : 0 < β) (x : R3) : A0 β x ≤ 2 * |x 2| ^ β := by
  have hr : 0 ≤ Work.Cyl.radial x := Work.Cyl.radial_nonneg x
  have hρ : 0 ≤ Work.Cyl.rho x := Work.Cyl.rho_nonneg x
  rw [A0, div_le_iff₀ (denom_pos β x)]
  have h1 : (Work.Cyl.radial x) ^ (2 * β) ≤ (Work.Cyl.rho x) ^ (2 * β) :=
    Real.rpow_le_rpow hr (Work.Cyl.radial_le_rho x) (by linarith)
  have h2 : (Work.Cyl.rho x) ^ (2 * β) ≤ (1 + (Work.Cyl.rho x) ^ (3 * β)) ^ 2 :=
    rpow_le_one_add_sq (2 * β) (3 * β) _ (by linarith) (by linarith) hρ
  have hz : 0 ≤ |x 2| ^ β := Real.rpow_nonneg (abs_nonneg _) β
  nlinarith [h1, h2, hz, Real.rpow_nonneg hr (2 * β)]

lemma A0_le_rpow2 (β : ℝ) (hβ : 0 < β) (x : R3) :
    A0 β x ≤ 2 * (Work.Cyl.radial x) ^ (2 * β) := by
  have hr : 0 ≤ Work.Cyl.radial x := Work.Cyl.radial_nonneg x
  have hρ : 0 ≤ Work.Cyl.rho x := Work.Cyl.rho_nonneg x
  rw [A0, div_le_iff₀ (denom_pos β x)]
  have h1 : (|x 2|) ^ β ≤ (Work.Cyl.rho x) ^ β :=
    Real.rpow_le_rpow (abs_nonneg _) (Work.Cyl.abs_axial_le_rho x) hβ.le
  have h2 : (Work.Cyl.rho x) ^ β ≤ (1 + (Work.Cyl.rho x) ^ (3 * β)) ^ 2 :=
    rpow_le_one_add_sq β (3 * β) _ hβ.le (by linarith) hρ
  nlinarith [h1, h2, Real.rpow_nonneg hr (2 * β)]

lemma A0_le_rpow (β : ℝ) (hβ : 0 < β) (x : R3) :
    A0 β x ≤ 2 * (Work.Cyl.radial x) ^ β := by
  have hr : 0 ≤ Work.Cyl.radial x := Work.Cyl.radial_nonneg x
  have hρ : 0 ≤ Work.Cyl.rho x := Work.Cyl.rho_nonneg x
  rw [A0, div_le_iff₀ (denom_pos β x)]
  have hfac : |x 2| ^ β * (Work.Cyl.radial x) ^ (2 * β)
      = (|x 2| * Work.Cyl.radial x) ^ β * (Work.Cyl.radial x) ^ β := by
    rw [Real.mul_rpow (abs_nonneg _) hr, rpow_two_mul β _ hr]; ring
  have hkey : (|x 2| * Work.Cyl.radial x) ^ β ≤ (1 + (Work.Cyl.rho x) ^ (3 * β)) ^ 2 := by
    have h1 : (|x 2| * Work.Cyl.radial x) ^ β ≤ ((Work.Cyl.rho x) ^ 2) ^ β :=
      Real.rpow_le_rpow (by positivity) (abs_ax_mul_radial_le x) hβ.le
    rw [rpow_sq_mul β _ hρ] at h1
    exact le_trans h1
      (rpow_le_one_add_sq (2 * β) (3 * β) _ (by linarith) (by linarith) hρ)
  rw [show 2 * |x 2| ^ β * (Work.Cyl.radial x) ^ (2 * β)
      = 2 * (|x 2| ^ β * (Work.Cyl.radial x) ^ (2 * β)) by ring, hfac]
  have hrβ : 0 ≤ (Work.Cyl.radial x) ^ β := Real.rpow_nonneg hr β
  nlinarith [mul_le_mul_of_nonneg_right hkey hrβ]

lemma A0_eq_zero_of_radial_eq_zero (β : ℝ) (hβ : 0 < β) {x : R3}
    (h : Work.Cyl.radial x = 0) : A0 β x = 0 := by
  rw [A0, h, Real.zero_rpow (by positivity : (2 : ℝ) * β ≠ 0)]
  simp

/-! ## The signed amplitude `Aom` -/

lemma abs_cSign_le_one (β t : ℝ) : |cSign β t| ≤ 1 := by
  by_cases h : 0 ≤ t
  · rw [cSign, if_pos h]; norm_num
  · rw [cSign, if_neg h]
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

lemma abs_Aom_le_A0 (β : ℝ) (x : R3) : |Aom β x| ≤ A0 β x := by
  rw [Aom, abs_mul, abs_of_nonneg (A0_nonneg β x)]
  calc |cSign β (x 2)| * A0 β x ≤ 1 * A0 β x :=
        mul_le_mul_of_nonneg_right (abs_cSign_le_one β (x 2)) (A0_nonneg β x)
    _ = A0 β x := one_mul _

/-! ## `r` is `1`-Lipschitz and `‖e_θ‖ ≤ 1` -/

lemma norm_radialVec (x : R3) : ‖Work.Cyl.radialVec x‖ = Work.Cyl.radial x := by
  have h : ‖Work.Cyl.radialVec x‖ ^ 2 = Work.Cyl.radial x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, Work.Cyl.inner_radialVec_self, Work.Cyl.radial_sq]
  nlinarith [norm_nonneg (Work.Cyl.radialVec x), Work.Cyl.radial_nonneg x]

lemma radialVec_sub (x y : R3) :
    Work.Cyl.radialVec x - Work.Cyl.radialVec y = Work.Cyl.radialVec (x - y) := by
  ext i
  fin_cases i <;> simp [Work.Cyl.radialVec]

lemma radial_dist_le (x y : R3) :
    |Work.Cyl.radial x - Work.Cyl.radial y| ≤ ‖x - y‖ := by
  have h1 : ‖Work.Cyl.radialVec x‖ = Work.Cyl.radial x := norm_radialVec x
  have h2 : ‖Work.Cyl.radialVec y‖ = Work.Cyl.radial y := norm_radialVec y
  calc |Work.Cyl.radial x - Work.Cyl.radial y|
      = |‖Work.Cyl.radialVec x‖ - ‖Work.Cyl.radialVec y‖| := by rw [h1, h2]
    _ ≤ ‖Work.Cyl.radialVec x - Work.Cyl.radialVec y‖ := abs_norm_sub_norm_le _ _
    _ = ‖Work.Cyl.radialVec (x - y)‖ := by rw [radialVec_sub]
    _ = Work.Cyl.radial (x - y) := norm_radialVec _
    _ ≤ Work.Cyl.rho (x - y) := Work.Cyl.radial_le_rho _
    _ = ‖x - y‖ := Work.Cyl.rho_eq_norm _

lemma eTheta_norm_sub_le_two (x y : R3) : ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖ ≤ 2 := by
  refine le_trans (norm_sub_le _ _) ?_
  have h1 := norm_eTheta_le_one x
  have h2 := norm_eTheta_le_one y
  linarith

/-! ## From a pointwise norm bound to `HolderWith` -/

/-- `HolderWith` (with exponent the non-negative real `α`, written with the real calibration
`βr = α`) follows from the pointwise norm bound `‖f x - f y‖ ≤ C ‖x-y‖^βr`. -/
theorem holder_of_norm_le {α : ℝ≥0} {βr : ℝ} (hα : (α : ℝ) = βr) (hβ : 0 ≤ βr) {f : R3 → R3}
    {C : ℝ≥0} (h : ∀ x y : R3, ‖f x - f y‖ ≤ (C : ℝ) * ‖x - y‖ ^ βr) :
    HolderWith C α f := by
  intro x y
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, hα]
  rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (x - y)) hβ]
  rw [ENNReal.coe_nnreal_eq C, ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (h x y)










end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.Boxes =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-- `c * ‖c⁻¹ • v‖ = ‖v‖` for `c > 0`. -/
theorem mul_norm_inv_smul {c : ℝ} (hc : 0 < c) (v : R3) : c * ‖c⁻¹ • v‖ = ‖v‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc, inv_eq_one_div]
  field_simp

/-- **The perturbation bound implies a *uniform* bound of the scaled profile**: if `|g(z,θ)| ≤ Cg`
for all `z ≥ 0`, `θ ∈ Iθ` (the design's `(B1)`, `‖g‖_{ℋ⁴} ≤ Cα²` through
`Work.Spaces.Linf_H2`), then for every self-similar variable `z` the field `omegaSz p g z` is
bounded by `20p + Cg` — because `|F_*(z,θ)| ≤ 20pΓ(θ) ≤ 20p` **uniformly in `z`**
(`Defs.Fstar_abs_le`: the profile `2z/(1+z)²` decays at infinity). -/
theorem omegaSz_norm_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ} {Cg : ℝ}
    (hCg : 0 ≤ Cg) (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    {z : ℝ} (hz : 0 ≤ z) (x : R3) : ‖omegaSz p g z x‖ ≤ 20 * p + Cg := by
  rw [omegaSz_apply, norm_smul, Real.norm_eq_abs]
  have hθ_abs : |Work.Cyl.theta x| ≤ Real.pi / 2 := by
    rw [abs_le]
    exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _),
      le_of_lt (Real.arctan_lt_pi_div_two _)⟩
  have hθmem : |Work.Cyl.theta x| ∈ Work.Spaces.Iθ := ⟨abs_nonneg _, hθ_abs⟩
  have hbdd := profile_abs_le_of_abs (p := p) hp hp1 hgbdd z hz (Work.Cyl.theta x) hθ_abs
  have hnn : 0 ≤ 20 * p * Gamma (p / 3) |Work.Cyl.theta x| + Cg :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hp.le) (Gamma_nonneg hθmem)) hCg
  calc |profile p g z (Work.Cyl.theta x)| * ‖Work.Cyl.eTheta x‖
      ≤ (20 * p * Gamma (p / 3) |Work.Cyl.theta x| + Cg) * 1 :=
        mul_le_mul hbdd (norm_eTheta_le_one x) (norm_nonneg _) hnn
    _ ≤ 20 * p + Cg := by
        have hG : Gamma (p / 3) |Work.Cyl.theta x| ≤ 1 :=
          Gamma_le_one (by positivity) hθmem
        nlinarith [hp.le, hG, hCg]



end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.Gamma_abs_theta_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **`Γ(|θ x|) ≤ (r/ρ)^{2α}` off the axis.**

Since `Γ(θ) = (sin θ cos²θ)^β` and `cos |θ x| = r(x)/ρ(x)` (the paper's `cos θ = r/ρ`), the claim
is `(sin ψ · cos²ψ)^α ≤ (cos²ψ)^α` for `ψ = psi x = |θ x|`: the base on the left is the base on
the right multiplied by `sin ψ ≤ 1`, and both are nonnegative. -/
theorem Gamma_abs_theta_le {α : ℝ} (hα : 0 < α) {x : Work.Cyl.R3} (hr : 0 < Work.Cyl.radial x) :
    Work.ConstructionInstance.Gamma α (|Work.Cyl.theta x|)
      ≤ (Work.Cyl.radial x / Work.Cyl.rho x) ^ (2 * α) := by
  have hpsi : psi x = |Work.Cyl.theta x| := psi_eq_abs_theta hr
  have hIθ : psi x ∈ Work.Spaces.Iθ := psi_mem_Iθ x
  have hcos : Real.cos (psi x) = Work.Cyl.radial x / Work.Cyl.rho x := cos_psi x
  have hcosnn : 0 ≤ Real.cos (psi x) := by
    rw [hcos]; exact div_nonneg hr.le (Work.Cyl.rho_nonneg x)
  have hsin0 : 0 ≤ Real.sin (psi x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hIθ.1 (by linarith [hIθ.2, Real.pi_pos])
  have hbase : Real.sin (psi x) * Real.cos (psi x) ^ 2 ≤ Real.cos (psi x) ^ 2 := by
    simpa using mul_le_mul_of_nonneg_right (Real.sin_le_one (psi x)) (sq_nonneg (Real.cos (psi x)))
  have hbase0 : 0 ≤ Real.sin (psi x) * Real.cos (psi x) ^ 2 :=
    mul_nonneg hsin0 (sq_nonneg _)
  rw [← hpsi, Gamma]
  calc (Real.sin (psi x) * Real.cos (psi x) ^ 2) ^ α
      ≤ (Real.cos (psi x) ^ 2) ^ α := Real.rpow_le_rpow hbase0 hbase hα.le
    _ = Real.cos (psi x) ^ (2 * α) := by
        rw [← Real.rpow_natCast (Real.cos (psi x)) 2]
        exact (Real.rpow_mul hcosnn 2 α).symm
    _ = (Work.Cyl.radial x / Work.Cyl.rho x) ^ (2 * α) := by rw [hcos]

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.ModulatedData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-- **The modulated-box interface**: the `St0`–`St3` output about `(λ̄, ω)`, on the times before
the maximal time `T`, in the *self-similar* weighting.

* `hlam`/`hlam_le`/`hlam_low` — `0 < λ̄(t)`, `λ̄(t) ≤ 2(T-t)` and `(T-t)/2 ≤ λ̄(t)` for `t < T`
  (`St0`'s `κ ≤ 2` and its matching lower bound; the lower bound is what makes the weighted box
  equivalent to a *strip* bound, `strip_bdd_of_repaired`);
* `hlamd` — the rate bound `|λ̄'| ≤ 1/2` (the design's normalisation of `κ`);
* `hBdd`, `hBddDt` — the two self-similar boxes;
* `hansatz` — the `St5` lower bound.

Every field is a statement about the *physical* vorticity `ω : ℝ³ × ℝ → ℝ³` and the scalar `λ̄`;
nothing here refers to the profile `F = F_* + g`. -/
structure ModulatedData (α : NNReal) where
  /-- the blow-up time -/
  T : ℝ
  /-- `T > 0` -/
  hT : 0 < T
  /-- the self-similar `L^∞` constant -/
  M : ℝ
  /-- `M ≥ 0` -/
  hM : 0 ≤ M
  /-- the self-similar `L^∞` constant of `∂ₜω` -/
  M₁ : ℝ
  /-- `M₁ ≥ 0` -/
  hM₁ : 0 ≤ M₁
  /-- the `St5` constant -/
  c₀ : ℝ
  /-- `c₀ > 0` -/
  hc₀ : 0 < c₀
  /-- the modulation `λ̄` -/
  lam : ℝ → ℝ
  /-- the physical vorticity -/
  ω : R3 → ℝ → R3
  /-- `λ̄ > 0` before the maximal time -/
  hlam : ∀ t ∈ preWindow T, 0 < lam t
  /-- `λ̄(t) ≤ 2(T-t)` (`St0`, `κ ≤ 2`) -/
  hlam_le : ∀ t ∈ Set.Ico 0 T, lam t ≤ 2 * (T - t)
  /-- `(T-t)/2 ≤ λ̄(t)` (the matching lower bound of the design) -/
  hlam_low : ∀ t ∈ Set.Ico 0 T, (T - t) / 2 ≤ lam t
  /-- the rate bound `|λ̄'| ≤ 1/2` -/
  hlamd : ∀ t ∈ preWindow T, |deriv lam t| ≤ 1 / 2
  /-- **the `L^∞` box in the self-similar variable** -/
  hBdd : ∀ t ∈ preWindow T, ∀ y : R3, lam t * ‖ω y t‖ ≤ M
  /-- **the box for `∂ₜω`**, with the honest `λ̄²` weight -/
  hBddDt : ∀ t ∈ preWindow T, ∀ y : R3,
    (lam t) ^ 2 * ‖FiniteTimeSingularity.timeDeriv ω y t‖ ≤ M₁
  /-- **`St5`**: somewhere the vorticity is as large as `c₀α/λ̄(t)` -/
  hansatz : ∀ t ∈ Set.Ico 0 T, ∃ x : R3, c₀ * (α : ℝ) ≤ lam t * ‖ω x t‖

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.abs_psi_sub_le_angle =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Work.Cyl

namespace Work.ConstructionInstance

/-! ## A planar Cauchy–Schwarz inequality

The two-dimensional Cauchy–Schwarz inequality in the elementary form we need below: the scalar
product of the planar parts of two vectors of `ℝ³` is bounded by the product of their planar
radii. -/

/-- **Cauchy–Schwarz in the plane.**  For real `a b c d`,  `a c + b d ≤ √(a²+b²)·√(c²+d²)`.
The proof squares both sides (the right-hand side is nonnegative) and uses
`(a²+b²)(c²+d²) - (ac+bd)² = (ad - bc)² ≥ 0`. -/
theorem real_cauchy2 (a b c d : ℝ) :
    a * c + b * d ≤ Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + d ^ 2) := by
  have h1 : 0 ≤ Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + d ^ 2) := by positivity
  have h2 : (a * c + b * d) ^ 2 ≤ (Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + d ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    nlinarith [sq_nonneg (a * d - b * c)]
  nlinarith [sq_nonneg (a * c + b * d), h1, h2]

/-- **Planar Cauchy–Schwarz on `ℝ³`.**  `x₀y₀ + x₁y₁ ≤ r(x)·r(y)`, where `r = Cyl.radial` is the
planar radius: the horizontal part of `⟪x,y⟫` is at most the product of the horizontal radii. -/
theorem planar_inner_le (x y : R3) : x 0 * y 0 + x 1 * y 1 ≤ radial x * radial y := by
  have h := real_cauchy2 (x 0) (x 1) (y 0) (y 1)
  simpa only [radial, radSq] using h

/-- **The normalized inner product is at most `cos (ψx - ψy)`.**  Splitting
`⟪x,y⟫ = (x₀y₀ + x₁y₁) + x₂y₂` and using planar Cauchy–Schwarz on the first summand and
`x₂y₂ ≤ |x₂||y₂|` on the second,

  `⟪x,y⟫/(ρx·ρy) ≤ r(x)r(y)/(ρxρy) + |x₂||y₂|/(ρxρy) = cos ψx cos ψy + sin ψx sin ψy
                 = cos (ψx - ψy)`,

with `cos_psi`/`sin_psi` of `GCompDefs` converting the coordinates into `cos ψ`/`sin ψ`. -/
theorem inner_div_le_cos_psi_sub (x y : R3) (hx : 0 < rho x) (hy : 0 < rho y) :
    inner ℝ x y / (rho x * rho y) ≤ Real.cos (psi x - psi y) := by
  rw [inner_eq, Real.cos_sub, cos_psi x, cos_psi y, sin_psi hx, sin_psi hy]
  have hp : 0 < rho x * rho y := mul_pos hx hy
  have hplanar := planar_inner_le x y
  have haz : x 2 * y 2 ≤ |x 2| * |y 2| := by
    calc x 2 * y 2 ≤ |x 2 * y 2| := le_abs_self _
      _ = |x 2| * |y 2| := abs_mul _ _
  rw [div_le_iff₀ hp]
  have hR : (radial x / rho x * (radial y / rho y) + |x 2| / rho x * (|y 2| / rho y))
        * (rho x * rho y) = radial x * radial y + |x 2| * |y 2| := by
    field_simp
  rw [hR]
  linarith

/-- **`psi` is dominated by the angle between `x` and `y`.**  With `ψ z = arccos (r z / ρ z)`
(`r = Cyl.radial`, `ρ = Cyl.rho = ‖·‖`) this says `|ψ x - ψ y| ≤ angle x y`, where
`InnerProductGeometry.angle x y = arccos (⟪x,y⟫ / (‖x‖‖y‖))`.

Since both `ψ z` lie in `[0, π/2]`, `cos (ψx - ψy) = cos |ψx - ψy|` with `|ψx - ψy| ≤ π/2 ≤ π`, so
`arccos (cos (ψx - ψy)) = |ψx - ψy|` (`Real.arccos_cos`); the previous lemma gives
`⟪x,y⟫/(ρxρy) ≤ cos (ψx - ψy)`, and `Real.arccos_le_arccos` (which is unconditional in the
Mathlib convention for `Real.arccos`) reverses it. -/
theorem abs_psi_sub_le_angle (x y : Work.ConstructionInstance.R3)
    (hx : 0 < Work.Cyl.rho x) (hy : 0 < Work.Cyl.rho y) :
    |Work.ConstructionInstance.psi x - Work.ConstructionInstance.psi y| ≤
      InnerProductGeometry.angle x y := by
  have hxI := psi_mem_Iθ x
  have hyI := psi_mem_Iθ y
  have habs : |psi x - psi y| ≤ Real.pi := by
    rw [abs_le]
    constructor <;> linarith [hxI.1, hxI.2, hyI.1, hyI.2, Real.pi_pos]
  have e1 : Real.arccos (Real.cos (psi x - psi y)) = |psi x - psi y| := by
    rw [← Real.cos_abs]
    exact Real.arccos_cos (abs_nonneg _) habs
  have e2 : Real.arccos (inner ℝ x y / (rho x * rho y)) = InnerProductGeometry.angle x y := by
    rw [InnerProductGeometry.angle, rho_eq_norm x, rho_eq_norm y]
  have hmain := Real.arccos_le_arccos (inner_div_le_cos_psi_sub x y hx hy)
  rw [e1, e2] at hmain
  exact hmain

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.biotSavart_flip1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Matrix
open MeasureTheory

namespace Work.ConstructionInstance

/-! ## Reflection equivariance of `biotSavart` under the flip `x₁ ↦ -x₁`

The same argument as `Work.LWP.BiotSavart.biotSavart_reflZ`, run with the reflection
`flip1 = (x₀, x₁, x₃) ↦ (x₀, -x₁, x₃)` (as the linear isometry equivalence `flip1LE`).
Every point of the computation is already available: `flip1LE` is an isometry
(`flip1_norm`), the parity hypothesis `ω (flip1 x) = - flip1 (ω x)` says the integrand is
`flip1`-equivariant, and `flip1Coord_cross` (the reflection reverses the cross product,
`det = -1`) supplies the sign change that makes the two cancel. -/

/-- `(-a) ⨯₃ b = -(a ⨯₃ b)` for coordinate vectors of `ℝ³`. -/
private lemma cross_neg_left (a b : Fin 3 → ℝ) : (-a) ⨯₃ b = - (a ⨯₃ b) := by
  ext i
  fin_cases i <;> simp [cross_apply]

/-- `flip1LE` on a coordinate vector, in coordinates. -/
private lemma flip1LE_toLp (w : Fin 3 → ℝ) :
    flip1LE (WithLp.toLp 2 w) = WithLp.toLp 2 (flip1Coord w) := rfl

/-- `flip1LE` in coordinates, on `ofLp`. -/
private lemma flip1LE_ofLp (x : R3) : (flip1LE x).ofLp = flip1Coord x.ofLp := by
  rw [flip1LE_apply, flip1_ofLp]

/-- **The Biot–Savart integrand is equivariant under the flip `flip1`.**  If
`ω (flip1 x) = - flip1 (ω x)`, then the integrand of `biotSavart ω` at the reflected pair
`(flip1LE x, flip1LE z)` is `flip1LE` applied to the integrand at `(x, z)`. -/
private lemma biotSavart_integrand_flip1 {ω : R3 → R3}
    (h : ∀ x : R3, ω (flip1 x) = - flip1 (ω x)) (x z : R3) :
    WithLp.toLp 2 ((‖flip1LE x - flip1LE z‖ ^ (3 : ℕ))⁻¹ •
        ((ω (flip1LE z)) ⨯₃ (flip1LE x - flip1LE z)))
      = flip1LE (WithLp.toLp 2 ((‖x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (x - z)))) := by
  have h1 : ‖flip1LE x - flip1LE z‖ = ‖x - z‖ := by
    rw [← LinearIsometryEquiv.map_sub]
    exact flip1LE.norm_map (x - z)
  have hz : ω (flip1LE z) = - flip1LE (ω z) := by
    rw [flip1LE_apply]
    exact h z
  have e1 : (ω (flip1LE z)).ofLp = - flip1Coord ((ω z).ofLp) := by
    rw [hz, WithLp.ofLp_neg, flip1LE_ofLp]
  have e2 : (flip1LE x).ofLp - (flip1LE z).ofLp = flip1Coord (x.ofLp - z.ofLp) := by
    rw [flip1LE_ofLp, flip1LE_ofLp, ← flip1Coord_sub]
  have hkey : ((ω (flip1LE z)) ⨯₃ (flip1LE x - flip1LE z))
      = flip1Coord ((ω z) ⨯₃ (x - z)) := by
    rw [e1, e2, cross_neg_left, flip1Coord_cross, neg_neg]
  rw [h1, hkey, flip1LE_toLp, flip1Coord_smul]

/-- **`biotSavart` commutes with the linear isometry `flip1LE`** for a vorticity of parity
`ω ∘ flip1 = - flip1 ∘ ω`. -/
private lemma biotSavart_flip1LE {ω : R3 → R3}
    (h : ∀ x : R3, ω (flip1 x) = - flip1 (ω x)) (x : R3) :
    Work.LWP.biotSavart ω (flip1LE x) = flip1LE (Work.LWP.biotSavart ω x) := by
  rw [Work.LWP.biotSavart, Work.LWP.biotSavart]
  rw [LinearIsometryEquiv.map_smul]
  congr 1
  calc ∫ z, WithLp.toLp 2 ((‖flip1LE x - z‖ ^ (3 : ℕ))⁻¹ •
          ((ω z) ⨯₃ (flip1LE x - z)))
      = ∫ z, WithLp.toLp 2 ((‖flip1LE x - flip1LE z‖ ^ (3 : ℕ))⁻¹ •
          ((ω (flip1LE z)) ⨯₃ (flip1LE x - flip1LE z))) := by
        exact (MeasureTheory.integral_comp flip1LE (fun z => WithLp.toLp 2
          ((‖flip1LE x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (flip1LE x - z))))).symm
    _ = ∫ z, flip1LE (WithLp.toLp 2 ((‖x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (x - z)))) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with z
        exact biotSavart_integrand_flip1 h x z
    _ = flip1LE (∫ z, WithLp.toLp 2 ((‖x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (x - z)))) :=
        LinearIsometry.integral_comp_comm flip1LE.toLinearIsometry _

theorem biotSavart_flip1 {ω : Work.ConstructionInstance.R3 → Work.ConstructionInstance.R3}
    (hω : ∀ x : Work.ConstructionInstance.R3,
      ω (Work.ConstructionInstance.flip1 x) = - Work.ConstructionInstance.flip1 (ω x))
    (x : Work.ConstructionInstance.R3) :
    Work.LWP.biotSavart ω (Work.ConstructionInstance.flip1 x)
      = Work.ConstructionInstance.flip1 (Work.LWP.biotSavart ω x) :=
  biotSavart_flip1LE hω x

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.biotSavart_rotLE =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Matrix
open MeasureTheory

namespace Work.ConstructionInstance

/-! ## Two elementary rewrites for `rotLE` and `rotCoord` -/

/-- The coordinate form of `rotLE φ` on a vector written in coordinates: `rotLE` acts by
`rotCoord φ`. -/
lemma rotLE_toLp (φ : ℝ) (v : Fin 3 → ℝ) :
    rotLE φ (WithLp.toLp 2 v) = WithLp.toLp 2 (rotCoord φ v) := by
  rw [rotLE_apply, WithLp.ofLp_toLp]

/-- `rotCoord φ` is additive for differences as well: it is the coordinate action of the linear
map `rotLE φ` (see `rotCoord_add`, `rotCoord_smul`). -/
lemma rotLE_rotCoord_sub (φ : ℝ) (a b : Fin 3 → ℝ) :
    rotCoord φ (a - b) = rotCoord φ a - rotCoord φ b := by
  have h := map_sub (rotLE φ) (WithLp.toLp 2 a) (WithLp.toLp 2 b)
  rw [← WithLp.toLp_sub, rotLE_toLp] at h
  rw [← WithLp.toLp_sub, rotLE_toLp, rotLE_toLp] at h
  exact WithLp.toLp_injective 2 h


/-! ## The pointwise identity for the Biot–Savart integrand -/

/-- **The Biot–Savart integrand is equivariant under the rotation.**  For `ω` equivariant under
`rotLE φ`, the integrand of `biotSavart ω` at the rotated pair `(R x, R z)` is `R` applied to the
integrand at `(x, z)`. -/
lemma biotSavart_integrand_rotLE {ω : R3 → R3}
    (hω : ∀ (φ : ℝ) (x : R3), ω (rotLE φ x) = rotLE φ (ω x)) (φ : ℝ) (x z : R3) :
    WithLp.toLp 2 ((‖rotLE φ x - rotLE φ z‖ ^ (3 : ℕ))⁻¹ •
        ((ω (rotLE φ z)) ⨯₃ (rotLE φ x - rotLE φ z)))
      = rotLE φ (WithLp.toLp 2 ((‖x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (x - z)))) := by
  have h1 : ‖rotLE φ x - rotLE φ z‖ = ‖x - z‖ := by
    rw [← map_sub (rotLE φ) x z]
    exact (rotLE φ).norm_map (x - z)
  have hz : ω (rotLE φ z) = rotLE φ (ω z) := hω φ z
  rw [h1, hz]
  simp only [rotLE_ofLp]
  rw [rotLE_toLp]
  congr 1
  rw [rotCoord_smul, ← rotLE_rotCoord_sub, rotCoord_cross]

/-! ## Rotation equivariance of the Biot–Savart operator -/

/-- **`biotSavart` commutes with the rotations `rotLE φ` about the `x₃`-axis** for a vorticity `ω`
that is equivariant under those rotations.  This is the axisymmetry of the Biot–Savart map
(`Work.Cyl.IsAxiNoSwirl` is stated for the *differential* symmetry
`ω = f(radial, axial) • e_θ`; `Work.ConstructionInstance.isAxiNoSwirl_biotSavart` reduces it to
this equivariance through `eTheta_rotLE` and `radial_rotLE`/`axial_rotLE`).

Proved directly from the defining integral, with no Schauder input and no integrability
hypothesis on `ω`. -/
theorem biotSavart_rotLE {ω : Work.ConstructionInstance.R3 → Work.ConstructionInstance.R3}
    (hω : ∀ (φ : ℝ) (x : Work.ConstructionInstance.R3),
      ω (Work.ConstructionInstance.rotLE φ x) = Work.ConstructionInstance.rotLE φ (ω x))
    (φ : ℝ) (x : Work.ConstructionInstance.R3) :
    Work.LWP.biotSavart ω (Work.ConstructionInstance.rotLE φ x)
      = Work.ConstructionInstance.rotLE φ (Work.LWP.biotSavart ω x) := by
  rw [Work.LWP.biotSavart, Work.LWP.biotSavart]
  rw [LinearIsometryEquiv.map_smul]
  congr 1
  calc ∫ z, WithLp.toLp 2 ((‖rotLE φ x - z‖ ^ (3 : ℕ))⁻¹ •
          ((ω z) ⨯₃ (rotLE φ x - z)))
      = ∫ z, WithLp.toLp 2 ((‖rotLE φ x - rotLE φ z‖ ^ (3 : ℕ))⁻¹ •
          ((ω (rotLE φ z)) ⨯₃ (rotLE φ x - rotLE φ z))) :=
        (MeasureTheory.integral_comp (rotLE φ) (fun z => WithLp.toLp 2
          ((‖rotLE φ x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (rotLE φ x - z))))).symm
    _ = ∫ z, rotLE φ (WithLp.toLp 2 ((‖x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (x - z)))) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with z
        exact biotSavart_integrand_rotLE hω φ x z
    _ = rotLE φ (∫ z, WithLp.toLp 2 ((‖x - z‖ ^ (3 : ℕ))⁻¹ • ((ω z) ⨯₃ (x - z)))) :=
        LinearIsometry.integral_comp_comm (rotLE φ).toLinearIsometry _

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.continuousAt_psi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

open Work.Cyl

/-! ## Continuity of the corrected angle `psi` off the axis

`psi x = arccos (r x / ρ x)` is the corrected polar angle of `GCompDefs`.  On the axis `x = 0`
it is genuinely discontinuous (the ratio `r/ρ` has no limit at the origin: it is `1` along the
plane `x₃ = 0` and `0` along the axis), which is why the hypothesis `x ≠ 0` below is exactly
what the geometry allows.  Off the axis `rho x > 0` and `psi` is a composition
`Real.arccos ∘ (r / ρ)` of continuous functions, both `radial` and `rho` being built out of the
smooth coordinate functions of `ℝ³`. -/

/-- **`psi` is continuous off the axis.**  For `x ≠ 0` the three-dimensional radius `rho x`
is nonzero, so `x ↦ radial x / rho x` is continuous at `x`, and `Real.arccos` is continuous
everywhere. -/
theorem continuousAt_psi {x : Work.ConstructionInstance.R3} (hx : x ≠ 0) :
    ContinuousAt Work.ConstructionInstance.psi x := by
  have hρ : Work.Cyl.rho x ≠ 0 := ne_of_gt ((Work.Cyl.rho_pos_iff x).mpr hx)
  have hrad : ContinuousAt (fun y : R3 => Work.Cyl.radial y) x := by
    unfold Work.Cyl.radial Work.Cyl.radSq
    fun_prop
  have hrhop : ContinuousAt (fun y : R3 => Work.Cyl.rho y) x := by
    unfold Work.Cyl.rho Work.Cyl.radSq Work.Cyl.axial
    fun_prop
  have hdiv : ContinuousAt (fun y : R3 => Work.Cyl.radial y / Work.Cyl.rho y) x :=
    hrad.div hrhop hρ
  have hcomp := Real.continuous_arccos.continuousAt.comp hdiv
  unfold Work.ConstructionInstance.psi
  exact hcomp

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.div_omega0_all =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

noncomputable section

open Filter

/-! ## Smoothness of the profile off the plane `θ = 0`

This is the hypothesis `div_cutDatum` needs, and it is what makes the "off the two singular
sets" case go through: the profile `F = F_* + g` is `C¹` at every point `(z,θ)` with `θ ≠ 0`,
because the angular factor `Γ(θ) = (sinθcos²θ)^{p/3}` has a nonzero base there, while `g` is
smooth on the box `Ioi(-1) ×ˢ Ioo(-1)(π/2+1)` (`SmoothFar`).  On the two branches `θ > 0`,
`θ < 0` of the odd extension the profile is literally `F_* + g` resp. its reflection. -/

theorem contDiffAt_uncurry_profile {p : ℝ} {g : ℝ → ℝ → ℝ}
    (hsmooth : Work.Stability.SmoothFar g) {z θ : ℝ} (hz : -1 < z)
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) (hθ0 : θ ≠ 0) :
    ContDiffAt ℝ 1 (Function.uncurry (Work.ConstructionInstance.profile p g)) (z, θ) := by
  have hle : (1 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    simp [Work.Stability.smoothOrder]
  -- `g` is `C¹` at `(z,θ')` for `θ'` in the open quadrant
  have hgbox : ∀ θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ContDiffAt ℝ 1 (fun q : ℝ × ℝ => g q.1 q.2) (z, θ') := by
    intro θ' hθ'
    have hbox : (z, θ') ∈ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) :=
      ⟨hz, ⟨by linarith [hθ'.1], by linarith [hθ'.2]⟩⟩
    have h : ContDiffAt ℝ 1 (Function.uncurry g) (z, θ') :=
      ContDiffAt.of_le (hsmooth.contDiffAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hbox)) hle
    simpa [Function.uncurry_def] using h
  -- the smooth branch `(z,θ) ↦ F_*(z,θ) + g(z,θ)`
  have hP : ∀ θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ContDiffAt ℝ 1 (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2 + g q.1 q.2) (z, θ') := by
    intro θ' hθ'
    have hGam : ContDiffAt ℝ 1
        (fun q : ℝ × ℝ => (Real.sin q.2 * Real.cos q.2 ^ 2) ^ (p / 3)) (z, θ') := by
      apply ContDiffAt.rpow
      · fun_prop
      · fun_prop
      · have h1 : 0 < Real.sin θ' :=
          Real.sin_pos_of_pos_of_lt_pi hθ'.1 (by linarith [hθ'.2, Real.pi_pos])
        have h2 : 0 < Real.cos θ' :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ'.1, Real.pi_pos], hθ'.2⟩
        positivity
    have hGam2 : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => Work.Spaces.Gam p q.2) (z, θ') := by
      simpa [Work.Spaces.Gam] using hGam
    have hFrad : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => Work.FM.Fstar q.1) (z, θ') := by
      apply ContDiffAt.div
      · fun_prop
      · fun_prop
      · have : (1 : ℝ) + z ≠ 0 := by linarith
        positivity
    have hFstar : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2) (z, θ') := by
      have h := (ContDiffAt.const_smul (𝕜 := ℝ) p
        (ContDiffAt.div_const hGam2 (Work.Spaces.c p))).mul hFrad
      simpa [Work.Construction.Fstar, mul_assoc] using h
    exact hFstar.add (hgbox θ' hθ')
  rcases lt_trichotomy (0 : ℝ) θ with hpos | heq | hneg
  · have hev : Function.uncurry (Work.ConstructionInstance.profile p g)
        =ᶠ[nhds (z, θ)] (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2 + g q.1 q.2) := by
      filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const continuous_snd) hpos]
        with q hq
      show Work.ConstructionInstance.profile p g q.1 q.2 = _
      rw [Work.ConstructionInstance.profile_of_nonneg (le_of_lt hq)]
    exact (hP θ ⟨hpos, hθ.2⟩).congr_of_eventuallyEq hev
  · exact absurd heq.symm hθ0
  · have hmem' : -θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨by linarith, by linarith [hθ.1]⟩
    have hev : Function.uncurry (Work.ConstructionInstance.profile p g)
        =ᶠ[nhds (z, θ)]
          (fun q : ℝ × ℝ => -(Work.Construction.Fstar p q.1 (-q.2) + g q.1 (-q.2))) := by
      filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_snd continuous_const) hneg]
        with q hq
      show Work.ConstructionInstance.profile p g q.1 q.2 = _
      rw [Work.ConstructionInstance.profile_of_neg (not_le.mpr hq)]
    have hnegP : ContDiffAt ℝ 1
        (fun q : ℝ × ℝ => -(Work.Construction.Fstar p q.1 (-q.2) + g q.1 (-q.2))) (z, θ) := by
      have hcomp : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => (q.1, -q.2)) (z, θ) := by fun_prop
      have h3 := (hP (-θ) hmem').comp (z, θ) hcomp
      simpa [Function.comp_def] using h3.neg
    exact hnegP.congr_of_eventuallyEq hev

/-! ## Vanishing of the diagonal along coordinate lines on the axis and the plane -/

/-- On the symmetry axis (`radial x = 0`) and on the plane `x₃ = 0` (`axial x = 0`), the `i`-th
coordinate of the cut-off datum vanishes identically along the `i`-th coordinate line through
`x`.  On the axis this is because `e_θ` has vanishing `i`-th coordinate there; on the plane it is
because `e_θ` has vanishing `x₃`-coordinate, and along the two directions *inside* the plane the
angle `θ` is identically `0`, where the profile vanishes (`profile_zero`, using
`VanishTheta g`). -/
theorem omega0_coord_line_eq_zero {p : ℝ} (hp : p ≠ 0) {g : ℝ → ℝ → ℝ}
    (hvt : Work.Spaces.VanishTheta g) (L : ℝ) {x : R3}
    (hx : Work.Cyl.radial x = 0 ∨ Work.Cyl.axial x = 0) (i : Fin 3) (t : ℝ) :
    (Work.ConstructionInstance.omega₀ p g L (x + t • Work.Cyl.basisVec i)) i = 0 := by
  rw [omega₀_apply, omegaS_apply']
  simp only [PiLp.smul_apply, smul_eq_mul]
  rcases hx with hr | ha
  · have hx0 : x 0 = 0 := ((Work.Cyl.radial_eq_zero_iff x).mp hr).1
    have hx1 : x 1 = 0 := ((Work.Cyl.radial_eq_zero_iff x).mp hr).2
    have he : (Work.Cyl.eTheta (x + t • Work.Cyl.basisVec i)) i = 0 := by
      fin_cases i <;>
        simp [Work.Cyl.eTheta, Work.Cyl.angularVec, Work.Cyl.basisVec,
          FiniteTimeSingularity.e, hx0, hx1]
    rw [he, mul_zero, mul_zero]
  · have hx2 : x 2 = 0 := ha
    fin_cases i <;>
      simp [Work.Cyl.theta, Work.Cyl.axial, Work.Cyl.rho, Work.Cyl.eTheta,
        Work.Cyl.angularVec, Work.Cyl.basisVec, FiniteTimeSingularity.e,
        profile_zero hp hvt.1, hx2]

/-! ## The main theorem -/

/-- The cut-off datum `omega₀ p g L = χ(ρ/L)·omegaS p g` is divergence free for **every**
`x : ℝ³`.  Off the axis and off the plane this is `div_cutDatum`; on the two singular sets the
field is not differentiable (the Fréchet quotient along `e₂` resp. `e₀` blows up like
`h^{p/3-1}` resp. `h^{2p/3-1}`, both divergent for `p ≤ 1`), whence `fderiv = 0` by Mathlib's
`fderiv_zero_of_not_differentiableAt`; where `χ(ρ(x)/L) = 0` the datum vanishes on a
neighbourhood of `x` (the cut-off is `0` for `|ρ/L| ≥ 2`), so again `fderiv = 0`.  The
non-differentiability transfers from `omegaS` to the datum because the cut-off factor is smooth
and non-zero where it does not vanish. -/
theorem div_omega0_all {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ}
    (hvt : Work.Spaces.VanishTheta g) (hsmooth : Work.Stability.SmoothFar g) (L : ℝ) :
    ∀ x : Work.ConstructionInstance.R3,
      FiniteTimeSingularity.div (Work.ConstructionInstance.omega₀ p g L) x = 0 := by
  intro x
  by_cases hA : 0 < Work.Cyl.radial x ∧ Work.Cyl.axial x ≠ 0
  · -- off the axis and off the plane: the field is differentiable with the swirl structure
    have hr : 0 < Work.Cyl.radial x := hA.1
    have hθ0 : Work.Cyl.theta x ≠ 0 := by
      intro h
      have hquot : Work.Cyl.axial x / Work.Cyl.radial x = 0 := by
        rw [← Real.arctan_eq_zero_iff]; exact h
      rcases (div_eq_zero_iff.mp hquot) with h' | h'
      · exact hA.2 h'
      · exact absurd h' (ne_of_gt hr)
    have hθmem : Work.Cyl.theta x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
    have hz : -1 < Work.Cyl.rho x ^ p :=
      lt_of_lt_of_le (by norm_num) (Real.rpow_nonneg (Work.Cyl.rho_nonneg x) p)
    exact div_cutDatum (contDiffAt_uncurry_profile hsmooth hz hθmem hθ0) hr
  · -- on the axis or on the plane
    have hcase : Work.Cyl.radial x = 0 ∨ Work.Cyl.axial x = 0 := by
      rcases not_and_or.mp hA with h | h
      · exact Or.inl (le_antisymm (not_lt.mp h) (Work.Cyl.radial_nonneg x))
      · exact Or.inr (not_not.mp h)
    by_cases hd : DifferentiableAt ℝ (Work.ConstructionInstance.omega₀ p g L) x
    · -- the diagonal of the Jacobian is computed along coordinate lines and vanishes
      rw [FiniteTimeSingularity.div, Work.Cyl.trace_fderiv_eq_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [Work.Cyl.fderiv_apply_coord (Work.ConstructionInstance.omega₀ p g L) x i i hd,
        Work.Cyl.pd_eq_deriv_line]
      rw [show (fun t : ℝ =>
            (Work.ConstructionInstance.omega₀ p g L (x + t • Work.Cyl.basisVec i)) i)
          = fun _ => 0
        from funext (omega0_coord_line_eq_zero hp.ne' hvt L hcase i)]
      simp
    · rw [FiniteTimeSingularity.div, fderiv_zero_of_not_differentiableAt hd]
      simp

end

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.exists_omegaSz_low =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The profile's lower bound at a prescribed self-similar scale

The reference profile `F_* = p·(Γ(θ)/c(p))·F_{*,rad}(z)` is maximal in the self-similar variable
at `z = 1`, where `F_{*,rad}(1) = 2·1/(1+1)² = 1/2`, and is maximal in the angle at `θ = π/4`,
where `Γ(π/4) = (sin(π/4)cos²(π/4))^{p/3} > 0`.  Hence at `(z,θ) = (1,π/4)`

  `F_*(1,π/4) = p·Γ(π/4)/(2c(p))`,

and a perturbation `g` with `|g(1,π/4)| ≤ Cg ≤ p·Γ(π/4)/(4c(p))` can lower the absolute value
only down to `p·Γ(π/4)/(4c(p))`.

This file transfers that pointwise bound to the physical vorticity: the ray `x = (t,0,t)`,
`t > 0`, has `ρ(x) = √2·t`, `θ(x) = π/4` and `e_θ(x) = e₁`, so choosing `t` with `(√2 t)^p = s`
(which exists by `exists_sqrt_two_mul_rpow`) gives a point whose self-similar variable is exactly
`ρ(x)^p/s = 1`, where the profile bound applies:

  `p·Γ(π/4)/(4c(p)) ≤ ‖omegaSz p g (ρ(x)^p/s) x‖`.
-/

noncomputable section

open scoped Matrix

namespace Work.ConstructionInstance


end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.exists_rotLE_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- Every point off the symmetry axis is the rotation by some angle of the meridian point
`(r, 0, x₃)` of the same radius `r = radial x` and height `x₃ = axial x`.

Indeed `rotLE φ !₂[r,0,z] = !₂[r cos φ, r sin φ, z]`, so the assertion is that
`(x 0, x 1) = r·(cos φ, sin φ)` for some `φ`, which holds with `φ` the argument of the complex
number `(x 0 + i x 1)/r` since that number has modulus `1` as `r = √(x 0² + x 1²) > 0`. -/
theorem exists_rotLE_eq (x : Work.ConstructionInstance.R3)
    (hr : 0 < Work.Cyl.radial x) :
    ∃ φ : ℝ, Work.ConstructionInstance.rotLE φ
      !₂[Work.Cyl.radial x, 0, Work.Cyl.axial x] = x := by
  have hradSq_pos : 0 < Work.Cyl.radSq x := by
    rw [Work.Cyl.radial, Real.sqrt_pos] at hr
    exact hr
  -- `radial x ^ 2` is the squared distance of `x` to the axis, `x 0 ^ 2 + x 1 ^ 2`
  have h3 : Work.Cyl.radial x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    rw [Work.Cyl.radial, Real.sq_sqrt (le_of_lt hradSq_pos), Work.Cyl.radSq]
  have hpos : 0 < x 0 ^ 2 + x 1 ^ 2 := by rw [← h3]; positivity
  -- the normalised pair `(x 0 / r, x 1 / r)` lies on the unit circle
  have hsq : (x 0 / Work.Cyl.radial x) ^ 2 + (x 1 / Work.Cyl.radial x) ^ 2 = 1 := by
    rw [div_pow, div_pow, ← add_div, h3, div_self (ne_of_gt hpos)]
  obtain ⟨φ, hc, hs⟩ := exists_cos_sin hsq
  refine ⟨φ, ?_⟩
  have hx0 : x 0 = Real.cos φ * Work.Cyl.radial x := by rw [hc]; field_simp
  have hx1 : x 1 = Real.sin φ * Work.Cyl.radial x := by rw [hs]; field_simp
  ext i
  fin_cases i
  · simp [rotCoord, hx0]
  · simp [rotCoord, hx1]
  · simp [rotCoord, Work.Cyl.axial]

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.g_psi_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- Off the symmetry axis `psi` agrees with `|theta|` (`psi_eq_abs_theta`), and on the axis
`psi = π/2` while `|theta| = |arctan (x₃/0)| = 0`; at both `θ = 0` and `θ = π/2` the profile `g`
vanishes on the whole angular boundary by `VanishTheta`.  Hence the composite
`g (ρ^{3α}) (·)` takes the same value at `|theta x|` and at `psi x`. -/
theorem g_psi_eq {α : ℝ} {g : ℝ → ℝ → ℝ} (hquad0 : ∀ θ : ℝ, g 0 θ = 0)
    (hvt : Work.Spaces.VanishTheta g) (x : R3) :
    g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)
      = g (Work.Cyl.rho x ^ (3 * α)) (psi x) := by
  by_cases h : Work.Cyl.radial x = 0
  · -- on the symmetry axis: `psi x = π/2` and `theta x = 0`
    have hθ : Work.Cyl.theta x = 0 := by
      rw [Work.Cyl.theta, h, div_zero, Real.arctan_zero]
    rw [psi, h, zero_div, Real.arccos_zero, hθ, abs_zero, hvt.1, hvt.2]
  · -- off the symmetry axis `psi` is literally `|theta|`
    have hpos : 0 < Work.Cyl.radial x :=
      lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm h)
    rw [psi_eq_abs_theta hpos]

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.g_slice_lipschitz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter
open scoped Topology

namespace Work.ConstructionInstance

set_option maxHeartbeats 1000000

/-- **Differentiability of the `z`-slice.** If `g` is `C²` on the open rectangle
`(-1,∞) × (-1, π/2+1)` then for `(x,θ)` in that rectangle the slice `y ↦ g y θ` is
differentiable at `x`. -/
theorem differentiableAt_slice_z {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)))
    {x θ : ℝ} (hx : -1 < x) (hθ : -1 < θ) (hθ2 : θ < Real.pi / 2 + 1) :
    DifferentiableAt ℝ (fun y => g y θ) x := by
  have hopen : IsOpen (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) : Set (ℝ × ℝ)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hmem : (x, θ) ∈ (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) : Set (ℝ × ℝ)) :=
    ⟨hx, hθ, hθ2⟩
  have hd : DifferentiableAt ℝ (Function.uncurry g) (x, θ) :=
    (hsm.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hmem)
  have hlin : DifferentiableAt ℝ (fun y : ℝ => (y, θ)) x := by fun_prop
  simpa [Function.comp_def, Function.uncurry] using hd.comp x hlin

/-- **Differentiability of the `θ`-slice.** -/
theorem differentiableAt_slice_theta {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)))
    {z x : ℝ} (hz : -1 < z) (hx : -1 < x) (hx2 : x < Real.pi / 2 + 1) :
    DifferentiableAt ℝ (fun s => g z s) x := by
  have hopen : IsOpen (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) : Set (ℝ × ℝ)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hmem : (z, x) ∈ (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) : Set (ℝ × ℝ)) :=
    ⟨hz, hx, hx2⟩
  have hd : DifferentiableAt ℝ (Function.uncurry g) (z, x) :=
    (hsm.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hmem)
  have hlin : DifferentiableAt ℝ (fun s : ℝ => (z, s)) x := by fun_prop
  simpa [Function.comp_def, Function.uncurry] using hd.comp x hlin

/-- **Mean-value inequality in the `z`-direction, uniform in `θ`.**  For `0 ≤ a ≤ b ≤ 2` and
`θ ∈ [0,π/2]`, `|g b θ - g a θ| ≤ K b (b-a)`. -/
theorem slice_z_mvt {g : ℝ → ℝ → ℝ} {K : ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hz : ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz g z θ| ≤ K * z)
    (hK : 0 ≤ K) {a b θ : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |g b θ - g a θ| ≤ K * b * (b - a) := by
  have hθ1 : -1 < θ := by linarith [hθ.1]
  have hθ2 : θ < Real.pi / 2 + 1 := by linarith [hθ.2]
  have hderiv : ∀ x ∈ Set.Icc a b,
      HasDerivWithinAt (fun y => g y θ) (Work.Spaces.pz g x θ) (Set.Icc a b) x := by
    intro x hx
    have hx0 : -1 < x := by linarith [ha, hx.1]
    have hd : DifferentiableAt ℝ (fun y => g y θ) x := differentiableAt_slice_z hsm hx0 hθ1 hθ2
    have h1 : HasDerivAt (fun y => g y θ) (deriv (fun y => g y θ) x) x := hd.hasDerivAt
    simpa [Work.Spaces.pz] using h1.hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico a b, ‖Work.Spaces.pz g x θ‖ ≤ K * b := by
    intro x hx
    have hx0 : 0 ≤ x := le_trans ha hx.1
    have hx2 : x ≤ 2 := le_trans hx.2.le hb
    have hle : |Work.Spaces.pz g x θ| ≤ K * x := hz x θ hx0 hx2 hθ
    have hxb : x ≤ b := hx.2.le
    rw [Real.norm_eq_abs]
    exact le_trans hle (mul_le_mul_of_nonneg_left hxb hK)
  have hMVT := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun y => g y θ) (f' := fun x => Work.Spaces.pz g x θ)
      (a := a) (b := b) (C := K * b) hderiv hbound
  have hfin := hMVT b ⟨hab, le_rfl⟩
  rwa [Real.norm_eq_abs] at hfin

/-- **Mean-value inequality in the `θ`-direction.**  For `0 ≤ z ≤ 2` and
`θ ≤ θ'` in `[0,π/2]`, `|g z θ' - g z θ| ≤ K z (θ' - θ)`. -/
theorem slice_theta_mvt {g : ℝ → ℝ → ℝ} {K : ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hth : ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pth g z θ| ≤ K * z)
    {z θ θ' : ℝ} (hz0 : 0 ≤ z) (hz2 : z ≤ 2)
    (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ) (h : θ ≤ θ') :
    |g z θ' - g z θ| ≤ K * z * (θ' - θ) := by
  have hz1 : -1 < z := by linarith
  have hderiv : ∀ x ∈ Set.Icc θ θ',
      HasDerivWithinAt (fun s => g z s) (Work.Spaces.pth g z x) (Set.Icc θ θ') x := by
    intro x hx
    have hx1 : -1 < x := by linarith [hθ.1, hx.1]
    have hx2 : x < Real.pi / 2 + 1 := by linarith [hθ'.2, hx.2]
    have hd : DifferentiableAt ℝ (fun s => g z s) x :=
      differentiableAt_slice_theta hsm hz1 hx1 hx2
    have h1 : HasDerivAt (fun s => g z s) (deriv (fun s => g z s) x) x := hd.hasDerivAt
    simpa [Work.Spaces.pth] using h1.hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico θ θ', ‖Work.Spaces.pth g z x‖ ≤ K * z := by
    intro x hx
    have hxI : x ∈ Work.Spaces.Iθ := ⟨le_trans hθ.1 hx.1, le_trans hx.2.le hθ'.2⟩
    rw [Real.norm_eq_abs]
    exact hth z x hz0 hz2 hxI
  have hMVT := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun s => g z s) (f' := fun x => Work.Spaces.pth g z x)
      (a := θ) (b := θ') (C := K * z) hderiv hbound
  have hfin := hMVT θ' ⟨h, le_rfl⟩
  rwa [Real.norm_eq_abs] at hfin

theorem g_slice_lipschitz {g : ℝ → ℝ → ℝ} {K : ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hz : ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz g z θ| ≤ K * z)
    (hth : ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pth g z θ| ≤ K * z) :
    (∀ z z' θ : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 → θ ∈ Work.Spaces.Iθ →
        |g z θ - g z' θ| ≤ K * max z z' * |z - z'|) ∧
      (∀ z θ θ' : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
        |g z θ - g z θ'| ≤ K * z * |θ - θ'|) := by
  have h0I : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hK : 0 ≤ K := by
    have h := hz 1 0 (by norm_num) (by norm_num) h0I
    have hnn := abs_nonneg (Work.Spaces.pz g 1 0)
    linarith
  constructor
  · intro z z' θ hz0 hz2 hz'0 hz'2 hθ
    rcases le_total z z' with hzz | hzz
    · have h := slice_z_mvt hsm hz hK hz0 hzz hz'2 hθ
      rw [max_eq_right hzz, abs_sub_comm, abs_of_nonpos (sub_nonpos.mpr hzz), neg_sub]
      exact h
    · have h := slice_z_mvt hsm hz hK hz'0 hzz hz2 hθ
      rw [max_eq_left hzz, abs_of_nonneg (sub_nonneg.mpr hzz)]
      exact h
  · intro z θ θ' hz0 hz2 hθ hθ'
    rcases le_total θ θ' with h | h
    · have hh := slice_theta_mvt hsm hth hz0 hz2 hθ hθ' h
      rw [abs_sub_comm, abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
      exact hh
    · have hh := slice_theta_mvt hsm hth hz0 hz2 hθ' hθ h
      rw [abs_of_nonneg (sub_nonneg.mpr h)]
      exact hh

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.g_taylor_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Taylor bounds for the modulation `g` at `z = 0`

This file proves `Work.ConstructionInstance.g_taylor_bounds`: a function `g` which is `C²` on an
open neighbourhood of the quadrant `[0,∞) × [0,π/2]` and whose `z`-slice at `z = 0` vanishes
together with its `z`-derivative is dominated on the box `[0,2] × [0,π/2]` by a constant,
uniformly in the angle, according to

  `|g z θ| ≤ K z²`,  `|∂_z g z θ| ≤ K z`,  `|∂_θ g z θ| ≤ K z`.

The proof is the mean-value theorem applied to the radial slices of the (finitely many)
second-order partial derivatives of `g`.  The only analytic input is that `g` is `C²` on a
neighbourhood of the closed box: this makes the second Fréchet derivative of `uncurry g`
continuous on the (open) neighbourhood, hence its restriction to the compact box is bounded,
and that bound is exactly the constant in the mean-value estimate.  The values of `g` and
`∂_z g` at `z = 0` are supplied by the hypotheses `hquad0`, `hquad1`, and `∂_θ g z θ` is
controlled starting from its (vanishing) value at `z = 0`.
-/

open Set Filter
open scoped Topology

namespace Work.ConstructionInstance

set_option autoImplicit false

theorem g_taylor_bounds {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hquad0 : ∀ θ : ℝ, g 0 θ = 0)
    (hquad1 : ∀ θ : ℝ, Work.Spaces.pz g 0 θ = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ K * z ^ 2 ∧ |Work.Spaces.pz g z θ| ≤ K * z
        ∧ |Work.Spaces.pth g z θ| ≤ K * z := by
  let G : ℝ × ℝ → ℝ := Function.uncurry g
  let U : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)
  have hopen : IsOpen U := isOpen_Ioi.prod isOpen_Ioo
  -- the closed box `[0,2] × [0,π/2]` sits inside the open neighbourhood `U`
  have hboxU : (Set.Icc (0:ℝ) 2 ×ˢ Work.Spaces.Iθ) ⊆ U := by
    rintro p ⟨hz, hθ⟩
    rw [Work.Spaces.Iθ] at hθ
    exact ⟨by rw [Set.mem_Ioi]; linarith [hz.1],
           by constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]⟩
  have hboxC : IsCompact (Set.Icc (0:ℝ) 2 ×ˢ Work.Spaces.Iθ) :=
    isCompact_Icc.prod (by rw [Work.Spaces.Iθ]; exact isCompact_Icc)
  -- `fderiv G` is `C¹` and `fderiv (fderiv G)` is continuous on `U`
  have hG1 : ContDiffOn ℝ 1 (fderiv ℝ G) U :=
    hsm.fderiv_of_isOpen hopen (by norm_num)
  have hG2 : ContinuousOn (fderiv ℝ (fderiv ℝ G)) U :=
    hG1.continuousOn_fderiv_of_isOpen hopen (by norm_num)
  -- the two second-order partial derivatives `∂_z∂_z g` and `∂_z∂_θ g`, read off the
  -- second Fréchet derivative, are continuous on `U`, hence bounded on the box
  have hcont2 : ContinuousOn (fun p : ℝ × ℝ => ((fderiv ℝ (fderiv ℝ G) p) (1,0)) (1,0)) U := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (fderiv ℝ (fderiv ℝ G) p) (1,0)) U :=
      hG2.clm_apply continuousOn_const
    exact h1.clm_apply continuousOn_const
  have hcont3 : ContinuousOn (fun p : ℝ × ℝ => ((fderiv ℝ (fderiv ℝ G) p) (1,0)) (0,1)) U := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (fderiv ℝ (fderiv ℝ G) p) (1,0)) U :=
      hG2.clm_apply continuousOn_const
    exact h1.clm_apply continuousOn_const
  obtain ⟨B1, hB1⟩ := hboxC.exists_bound_of_continuousOn (hcont2.mono hboxU)
  obtain ⟨B2, hB2⟩ := hboxC.exists_bound_of_continuousOn (hcont3.mono hboxU)
  set M1 : ℝ := max B1 0 with hM1
  set M2 : ℝ := max B2 0 with hM2
  set K : ℝ := max 1 (max M1 M2) with hK
  have hK0 : 0 ≤ K := by rw [hK]; exact le_trans zero_le_one (le_max_left _ _)
  have hK1 : B1 ≤ K := by
    rw [hK, hM1]
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_max_right _ _))
  have hK2 : B2 ≤ K := by
    rw [hK, hM2]
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨K, hK0, ?_⟩
  intro z θ hz0 hz2 hθ
  have hdiff : ∀ x : ℝ, 0 ≤ x → x ≤ 2 → DifferentiableAt ℝ G (x, θ) := fun x hx0 hx2 =>
    (hsm.differentiableOn (by norm_num)).differentiableAt
      (hopen.mem_nhds (hboxU ⟨⟨hx0, hx2⟩, hθ⟩))
  -- the curried partial derivatives are the Fréchet derivatives in the two coordinate directions
  have hpz_fd : ∀ x : ℝ, 0 ≤ x → x ≤ 2 →
      (fderiv ℝ G (x, θ)) (1,0) = Work.Spaces.pz g x θ :=
    fun x hx0 hx2 => (Work.Spaces.pz_eq_fderiv (hdiff x hx0 hx2)).symm
  have hpth_fd : ∀ x : ℝ, 0 ≤ x → x ≤ 2 →
      (fderiv ℝ G (x, θ)) (0,1) = Work.Spaces.pth g x θ :=
    fun x hx0 hx2 => (Work.Spaces.pth_eq_fderiv (hdiff x hx0 hx2)).symm
  -- ## derivatives of the radial slices
  have hdg : ∀ x ∈ Set.Icc (0:ℝ) z,
      HasDerivWithinAt (fun y => g y θ) ((fderiv ℝ G (x, θ)) (1,0)) (Set.Icc 0 z) x := by
    intro x hx
    have hx2 : x ≤ 2 := le_trans hx.2 hz2
    have hd := hdiff x hx.1 hx2
    have hcomp : HasFDerivAt (G ∘ (fun y : ℝ => (y, θ)))
        ((fderiv ℝ G (x, θ)) ∘SL ContinuousLinearMap.inl ℝ ℝ ℝ) x :=
      hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x θ)
    have h1 : HasDerivAt (G ∘ (fun y : ℝ => (y, θ))) ((fderiv ℝ G (x, θ)) (1,0)) x := by
      simpa [ContinuousLinearMap.inl_apply] using hcomp.hasDerivAt
    exact h1.hasDerivWithinAt
  have hdu : ∀ x ∈ Set.Icc (0:ℝ) z,
      HasDerivWithinAt (fun y => (fderiv ℝ G (y, θ)) (1,0))
        (((fderiv ℝ (fderiv ℝ G) (x, θ)) (1,0)) (1,0)) (Set.Icc 0 z) x := by
    intro x hx
    have hx2 : x ≤ 2 := le_trans hx.2 hz2
    have hxU : (x, θ) ∈ U := hboxU ⟨⟨hx.1, hx2⟩, hθ⟩
    have hDdiff : DifferentiableAt ℝ (fderiv ℝ G) (x, θ) :=
      (hG1.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hxU)
    have hE1 : HasFDerivAt (ContinuousLinearMap.apply ℝ ℝ ((1:ℝ),(0:ℝ)))
        (ContinuousLinearMap.apply ℝ ℝ ((1:ℝ),(0:ℝ))) (fderiv ℝ G (x, θ)) :=
      (ContinuousLinearMap.apply ℝ ℝ ((1:ℝ),(0:ℝ))).hasFDerivAt
    have hcomp1 := hE1.comp (x, θ) hDdiff.hasFDerivAt
    have hcurve : HasDerivAt (fun y : ℝ => (y, θ)) ((1:ℝ),(0:ℝ)) x := by
      simpa using (hasDerivAt_id x).prodMk (hasDerivAt_const x θ)
    have hcomp2 := hcomp1.comp_hasDerivAt x hcurve
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply] using hcomp2.hasDerivWithinAt
  have hdw : ∀ x ∈ Set.Icc (0:ℝ) z,
      HasDerivWithinAt (fun y => (fderiv ℝ G (y, θ)) (0,1))
        (((fderiv ℝ (fderiv ℝ G) (x, θ)) (1,0)) (0,1)) (Set.Icc 0 z) x := by
    intro x hx
    have hx2 : x ≤ 2 := le_trans hx.2 hz2
    have hxU : (x, θ) ∈ U := hboxU ⟨⟨hx.1, hx2⟩, hθ⟩
    have hDdiff : DifferentiableAt ℝ (fderiv ℝ G) (x, θ) :=
      (hG1.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hxU)
    have hE1 : HasFDerivAt (ContinuousLinearMap.apply ℝ ℝ ((0:ℝ),(1:ℝ)))
        (ContinuousLinearMap.apply ℝ ℝ ((0:ℝ),(1:ℝ))) (fderiv ℝ G (x, θ)) :=
      (ContinuousLinearMap.apply ℝ ℝ ((0:ℝ),(1:ℝ))).hasFDerivAt
    have hcomp1 := hE1.comp (x, θ) hDdiff.hasFDerivAt
    have hcurve : HasDerivAt (fun y : ℝ => (y, θ)) ((1:ℝ),(0:ℝ)) x := by
      simpa using (hasDerivAt_id x).prodMk (hasDerivAt_const x θ)
    have hcomp2 := hcomp1.comp_hasDerivAt x hcurve
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply] using hcomp2.hasDerivWithinAt
  -- ## the uniform bounds on the second-order partials
  have hbnd_u : ∀ x ∈ Set.Ico (0:ℝ) z,
      ‖((fderiv ℝ (fderiv ℝ G) (x, θ)) (1,0)) (1,0)‖ ≤ K := by
    intro x hx
    have hx2 : x ≤ 2 := le_trans (le_of_lt hx.2) hz2
    have h := hB1 (x, θ) ⟨⟨hx.1, hx2⟩, hθ⟩
    rw [Real.norm_eq_abs] at h
    exact le_trans h hK1
  have hbnd_w : ∀ x ∈ Set.Ico (0:ℝ) z,
      ‖((fderiv ℝ (fderiv ℝ G) (x, θ)) (1,0)) (0,1)‖ ≤ K := by
    intro x hx
    have hx2 : x ≤ 2 := le_trans (le_of_lt hx.2) hz2
    have h := hB2 (x, θ) ⟨⟨hx.1, hx2⟩, hθ⟩
    rw [Real.norm_eq_abs] at h
    exact le_trans h hK2
  -- ## `|∂_z g z θ| ≤ K z`
  have hMVT_u := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun y => (fderiv ℝ G (y, θ)) (1,0))
      (f' := fun y => ((fderiv ℝ (fderiv ℝ G) (y, θ)) (1,0)) (1,0))
      (a := 0) (b := z) (C := K) hdu hbnd_u
  have hpzu : ∀ y ∈ Set.Icc (0:ℝ) z, |Work.Spaces.pz g y θ| ≤ K * y := by
    intro y hy
    have hy2 : y ≤ 2 := le_trans hy.2 hz2
    have h := hMVT_u y hy
    rw [Real.norm_eq_abs] at h
    have h0 : (fderiv ℝ G (0, θ)) (1,0) = 0 := by
      rw [hpz_fd 0 (le_refl (0:ℝ)) (by norm_num), hquad1 θ]
    rw [hpz_fd y hy.1 hy2, h0, sub_zero, sub_zero] at h
    exact h
  -- ## `|g z θ| ≤ K z²`
  have hbnd_g : ∀ x ∈ Set.Ico (0:ℝ) z, ‖(fderiv ℝ G (x, θ)) (1,0)‖ ≤ K * z := by
    intro x hx
    have hx2 : x ≤ 2 := le_trans (le_of_lt hx.2) hz2
    rw [Real.norm_eq_abs, hpz_fd x hx.1 hx2]
    calc |Work.Spaces.pz g x θ| ≤ K * x := hpzu x ⟨hx.1, le_of_lt hx.2⟩
      _ ≤ K * z := mul_le_mul_of_nonneg_left (le_of_lt hx.2) hK0
  have hMVT_g := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun y => g y θ)
      (f' := fun y => (fderiv ℝ G (y, θ)) (1,0))
      (a := 0) (b := z) (C := K * z) hdg hbnd_g
  have hgz : |g z θ| ≤ K * z ^ 2 := by
    have h := hMVT_g z ⟨hz0, le_refl z⟩
    rw [Real.norm_eq_abs, hquad0 θ, sub_zero, sub_zero] at h
    calc |g z θ| ≤ K * z * z := h
      _ = K * z ^ 2 := by ring
  -- ## `|∂_θ g z θ| ≤ K z`
  have hpth0 : Work.Spaces.pth g 0 θ = 0 := by
    rw [Work.Spaces.pth]
    have : (fun θ' => g 0 θ') = fun _ => (0:ℝ) := by funext θ'; exact hquad0 θ'
    rw [this, deriv_const]
  have hMVT_w := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun y => (fderiv ℝ G (y, θ)) (0,1))
      (f' := fun y => ((fderiv ℝ (fderiv ℝ G) (y, θ)) (1,0)) (0,1))
      (a := 0) (b := z) (C := K) hdw hbnd_w
  have hpthz : |Work.Spaces.pth g z θ| ≤ K * z := by
    have h := hMVT_w z ⟨hz0, le_refl z⟩
    rw [Real.norm_eq_abs] at h
    have h0 : (fderiv ℝ G (0, θ)) (0,1) = 0 := by
      rw [hpth_fd 0 (le_refl (0:ℝ)) (by norm_num), hpth0]
    rw [hpth_fd z hz0 hz2, h0, sub_zero, sub_zero] at h
    exact h
  exact ⟨hgz, hpzu z ⟨hz0, le_refl z⟩, hpthz⟩

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.hasDerivAt_profile_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- With the zero perturbation `g = 0`, `profile p 0 (·, θ)` is, on each angular branch, a
constant multiple of `Work.FM.Fstar` (via `Work.Construction.Fstar`); hence it is
differentiable in `z` for `z > 0` and its derivative at `z` is `Work.Spaces.pz (profile p 0) z θ`. -/
theorem hasDerivAt_profile_zero {p θ z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' => Work.ConstructionInstance.profile p (fun _ _ => (0 : ℝ)) z' θ)
      (Work.Spaces.pz (Work.ConstructionInstance.profile p fun _ _ => (0 : ℝ)) z θ) z := by
  have hz1 : -1 < z := by linarith
  rcases le_or_gt 0 θ with hθ | hθ
  · -- positive branch: `profile p 0 z' θ = F_*(z',θ)` identically
    have hEq : (fun z' => Work.ConstructionInstance.profile p (fun _ _ => (0 : ℝ)) z' θ)
        = fun z' => Work.Construction.Fstar p z' θ := by
      funext z'; rw [profile_of_nonneg hθ]; simp
    have hval : Work.Spaces.pz (Work.ConstructionInstance.profile p fun _ _ => (0 : ℝ)) z θ
        = Work.Spaces.pz (Work.Construction.Fstar p) z θ := by
      simp only [Work.Spaces.pz, hEq]
    rw [hEq, hval]
    exact hasDerivAt_Fstar_z (p := p) z θ hz1
  · -- negative branch: `profile p 0 z' θ = -(F_*(z',-θ))` identically
    have hEq : (fun z' => Work.ConstructionInstance.profile p (fun _ _ => (0 : ℝ)) z' θ)
        = fun z' => -(Work.Construction.Fstar p z' (-θ)) := by
      funext z'; rw [profile_of_neg (not_le.mpr hθ)]; simp
    have hF := (hasDerivAt_Fstar_z (p := p) z (-θ) hz1).neg
    have hval : Work.Spaces.pz (Work.ConstructionInstance.profile p fun _ _ => (0 : ℝ)) z θ
        = -(Work.Spaces.pz (Work.Construction.Fstar p) z (-θ)) := by
      rw [Work.Spaces.pz, hEq]
      exact hF.deriv
    rw [hEq, hval]
    exact hF

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.holder_smul_eTheta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

theorem holder_smul_eTheta {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {A : Work.ConstructionInstance.R3 → ℝ} {Ca : ℝ} (hCa : 0 ≤ Ca)
    (hA : Holder ⟨α, hα.le⟩ A)
    (hvanA : ∀ x : Work.ConstructionInstance.R3, |A x| ≤ Ca * (Work.Cyl.radial x) ^ α) :
    Holder ⟨α, hα.le⟩
      (fun x : Work.ConstructionInstance.R3 => A x • Work.Cyl.eTheta x) := by
  obtain ⟨CA, hCA⟩ := hA
  -- the Hölder bound of `A`, as a `dist` estimate
  have hcay : ∀ x y : Work.ConstructionInstance.R3,
      dist (A x) (A y) ≤ (CA : ℝ) * dist x y ^ α := by
    intro x y; exact hCA.dist_le x y
  -- the weighted geometric bound `r(y)^α ‖e_θ x - e_θ y‖ ≤ 2 dist x y ^ α`
  have hw : ∀ x y : Work.ConstructionInstance.R3,
      Work.Cyl.radial y ^ α * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
        ≤ 2 * dist x y ^ α := by
    intro x y
    rw [mul_comm]
    refine Work.Stability.mul_rpow_le (p := ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖)
      (ρ := Work.Cyl.radial y) (d := dist x y) (α := α) hα hα1
      (Work.Cyl.radial_nonneg y) dist_nonneg (norm_nonneg _)
      (Work.Cyl.eTheta_sub_norm_mul_le x y) ?_
    calc ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
        ≤ ‖Work.Cyl.eTheta x‖ + ‖Work.Cyl.eTheta y‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by linarith [norm_eTheta_le_one x, norm_eTheta_le_one y]
      _ = 2 := by norm_num
  refine ⟨⟨(CA : ℝ) + 2 * Ca, add_nonneg CA.coe_nonneg (by linarith)⟩, ?_⟩
  refine Work.Stability.holderWith_of_dist_le (fun x y => ?_)
  rw [dist_eq_norm]
  have hsplit : A x • Work.Cyl.eTheta x - A y • Work.Cyl.eTheta y
      = (A x - A y) • Work.Cyl.eTheta x
        + A y • (Work.Cyl.eTheta x - Work.Cyl.eTheta y) := by
    rw [sub_smul, smul_sub]; abel
  rw [hsplit]
  calc ‖(A x - A y) • Work.Cyl.eTheta x + A y • (Work.Cyl.eTheta x - Work.Cyl.eTheta y)‖
      ≤ ‖(A x - A y) • Work.Cyl.eTheta x‖
        + ‖A y • (Work.Cyl.eTheta x - Work.Cyl.eTheta y)‖ := norm_add_le _ _
    _ = |A x - A y| * ‖Work.Cyl.eTheta x‖
        + |A y| * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (CA : ℝ) * dist x y ^ α
        + Ca * (Work.Cyl.radial y ^ α
            * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖) := by
        apply add_le_add
        · calc |A x - A y| * ‖Work.Cyl.eTheta x‖ ≤ |A x - A y| * 1 :=
              mul_le_mul_of_nonneg_left (norm_eTheta_le_one x) (abs_nonneg _)
            _ = |A x - A y| := mul_one _
            _ = dist (A x) (A y) := by rw [Real.dist_eq]
            _ ≤ (CA : ℝ) * dist x y ^ α := hcay x y
        · calc |A y| * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖
              ≤ (Ca * Work.Cyl.radial y ^ α)
                  * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖ :=
                mul_le_mul_of_nonneg_right (hvanA y) (norm_nonneg _)
            _ = Ca * (Work.Cyl.radial y ^ α
                  * ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖) := by ring
    _ ≤ (CA : ℝ) * dist x y ^ α + Ca * (2 * dist x y ^ α) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (hw x y) hCa)
    _ = ((CA : ℝ) + 2 * Ca) * dist x y ^ α := by ring

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.lam_sq_timeDeriv_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance


end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.rpow_sub_le_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- For `0 < s ≤ 1` the map `t ↦ t^s` is concave on `[0,∞)`, hence for `0 < a ≤ b`
the difference `b^s - a^s` is bounded by the tangent value at `a`:
`s * a^(s-1) * (b - a)`. -/
theorem rpow_sub_le_mul {s a b : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (ha : 0 < a) (hab : a ≤ b) :
    b ^ s - a ^ s ≤ s * a ^ (s - 1) * (b - a) := by
  rcases eq_or_lt_of_le hab with hEq | hlt
  · simp [hEq]
  · have hconc : ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => t ^ s) :=
      Real.concaveOn_rpow (le_of_lt hs) hs1
    have ha' : a ∈ Set.Ici (0 : ℝ) := le_of_lt ha
    have hb' : b ∈ Set.Ici (0 : ℝ) := le_trans (le_of_lt ha) hab
    have hdiff : DifferentiableAt ℝ (fun t : ℝ => t ^ s) a :=
      (Real.hasDerivAt_rpow_const (x := a) (p := s) (Or.inl (ne_of_gt ha))).differentiableAt
    have hslope := hconc.slope_le_deriv ha' hb' hlt hdiff
    rw [Real.deriv_rpow_const a s] at hslope
    rw [slope_def_field] at hslope
    rw [div_le_iff₀ (sub_pos.mpr hlt)] at hslope
    exact hslope

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.vorticity_bound_of_strip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

theorem vorticity_bound_of_strip {α : NNReal}
    {u : Work.ConstructionInstance.R3 → ℝ → Work.ConstructionInstance.R3} {S T : ℝ}
    (hST : T < S)
    (h : IsContDiffHolderOn ℝ α u.uncurry (Set.univ ×ˢ Set.Icc 0 S)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Set.Ico 0 T, ∀ x : Work.ConstructionInstance.R3,
      ‖FiniteTimeSingularity.vorticity (fun y => u y s) x‖ ≤ K := by
  obtain ⟨hcd, hbdd, _⟩ := h
  -- A uniform bound on the joint (within-)derivative over the whole strip.
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ p ∈ Set.univ ×ˢ Set.Icc 0 S,
      ‖fderivWithin ℝ u.uncurry (Set.univ ×ˢ Set.Icc 0 S) p‖ ≤ B := by
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall
      (0 : (Work.ConstructionInstance.R3 × ℝ) →L[ℝ] Work.ConstructionInstance.R3)).1 hbdd
    refine ⟨max r 0, fun p hp => ?_⟩
    have hp' : fderivWithin ℝ u.uncurry (Set.univ ×ˢ Set.Icc 0 S) p ∈
        fderivWithin ℝ u.uncurry (Set.univ ×ˢ Set.Icc 0 S) '' (Set.univ ×ˢ Set.Icc 0 S) :=
      ⟨p, hp, rfl⟩
    have hh := hr hp'
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hh
    exact le_trans hh (le_max_left _ _)
  refine ⟨3 * max B 0, by positivity, fun s hs x => ?_⟩
  -- `s` lies in the closed time interval, so the whole slice `ℝ³ × {s}` is in the strip.
  have hsIcc : s ∈ Set.Icc 0 S := ⟨hs.1, le_of_lt (lt_trans hs.2 hST)⟩
  have hmem : (x, s) ∈ Set.univ ×ˢ Set.Icc 0 S := ⟨trivial, hsIcc⟩
  set L : (Work.ConstructionInstance.R3 × ℝ) →L[ℝ] Work.ConstructionInstance.R3 :=
    fderivWithin ℝ u.uncurry (Set.univ ×ˢ Set.Icc 0 S) (x, s) with hLdef
  have hLbound : ‖L‖ ≤ B := hB (x, s) hmem
  -- The within-derivative of `u.uncurry` at `(x,s)`.
  have hdiff : DifferentiableWithinAt ℝ u.uncurry (Set.univ ×ˢ Set.Icc 0 S) (x, s) :=
    (hcd.differentiableOn (by norm_num)) (x, s) hmem
  have hg : HasFDerivWithinAt u.uncurry L (Set.univ ×ˢ Set.Icc 0 S) (x, s) :=
    hdiff.hasFDerivWithinAt
  -- Chain rule along the slice embedding `y ↦ (y, s)`, whose derivative is `inl`.
  have hf : HasFDerivWithinAt (fun y : Work.ConstructionInstance.R3 => (y, s))
      (ContinuousLinearMap.inl ℝ Work.ConstructionInstance.R3 ℝ) Set.univ x :=
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x s).hasFDerivWithinAt
  have hcomp := hg.comp x hf (fun y _ => hmem)
  have hslice : HasFDerivAt (fun y : Work.ConstructionInstance.R3 => u y s)
      (L ∘SL ContinuousLinearMap.inl ℝ Work.ConstructionInstance.R3 ℝ) x :=
    hcomp.hasFDerivAt Filter.univ_mem
  have hfderiv : fderiv ℝ (fun y : Work.ConstructionInstance.R3 => u y s) x
      = L ∘SL ContinuousLinearMap.inl ℝ Work.ConstructionInstance.R3 ℝ := hslice.fderiv
  -- The spatial block `L ∘SL inl` has norm at most `‖L‖`, since `inl` is an isometry.
  have hnormcomp : ‖L ∘SL ContinuousLinearMap.inl ℝ Work.ConstructionInstance.R3 ℝ‖ ≤ ‖L‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun v => ?_)
    calc ‖(L ∘SL ContinuousLinearMap.inl ℝ Work.ConstructionInstance.R3 ℝ) v‖
        = ‖L (v, (0:ℝ))‖ := rfl
      _ ≤ ‖L‖ * ‖(v, (0:ℝ))‖ := ContinuousLinearMap.le_opNorm L (v, (0:ℝ))
      _ = ‖L‖ * ‖v‖ := by simp
  have hfd : ‖fderiv ℝ (fun y : Work.ConstructionInstance.R3 => u y s) x‖ ≤ B := by
    rw [hfderiv]
    exact le_trans hnormcomp hLbound
  calc ‖FiniteTimeSingularity.vorticity (fun y => u y s) x‖
      ≤ 3 * ‖fderiv ℝ (fun y : Work.ConstructionInstance.R3 => u y s) x‖ :=
        Work.ConstructionInstance.norm_vorticity_le _ _
    _ ≤ 3 * max B 0 := by
        have h2 : ‖fderiv ℝ (fun y : Work.ConstructionInstance.R3 => u y s) x‖ ≤ max B 0 :=
          le_trans hfd (le_max_left _ _)
        linarith

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.z_pz_profile_abs_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-! ## The `z∂_z F_*` box: `|z·∂_zF_*(z,θ)| ≤ 5p`

`F_*(z,θ) = p·(Γ(θ)/c(p))·2z/(1+z)²`, so

  `z·∂_zF_*(z,θ) = p·(Γ(θ)/c(p))·(2z(1-z)/(1+z)³)`.

Here `Γ(θ)/c(p) ≤ 10` on `[0,π/2]` (`Work.Spaces.c_bounds` and `Γ ≤ 1`) and
`|2z(1-z)/(1+z)³| ≤ 1/2`: indeed `|1-z| ≤ 1+z` and `2z(1+z) ≤ (1+z)³/2`, the latter being
`4z ≤ (1+z)²`, i.e. `0 ≤ (1-z)²`. -/

/-- **The `F_*` part of the weighted `z`-derivative box.**  For `0 < p ≤ 1`, `z > 0` and
`θ ∈ [0,π/2]`, `|z·∂_zF_*(z,θ)| ≤ 5p`. -/
theorem z_pz_Fstar_abs_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |z * Work.Spaces.pz (Work.Construction.Fstar p) z θ| ≤ 5 * p := by
  have hc := (Work.Spaces.c_bounds p hp hp1).1
  have hcpos : 0 < Work.Spaces.c p := by linarith
  have hG := Work.Spaces.Gam_bounds p θ hp hθ
  have hq0 : 0 ≤ Work.Spaces.Gam p θ / Work.Spaces.c p := div_nonneg hG.1 hcpos.le
  have hq1 : Work.Spaces.Gam p θ / Work.Spaces.c p ≤ 10 := by
    rw [div_le_iff₀ hcpos]; nlinarith [hG.2]
  have hzden : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  -- `|2z(1-z)| ≤ 2z(1+z)`
  have h1 : |2 * z * (1 - z)| ≤ 2 * z * (1 + z) := by
    have h2z : |2 * z| = 2 * z := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hz.le]
    have h3 : |1 - z| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith
    rw [abs_mul, h2z]
    exact mul_le_mul_of_nonneg_left h3 (by linarith)
  -- `2z(1+z) ≤ (1+z)³/2`
  have h4 : 2 * z * (1 + z) ≤ (1 + z) ^ 3 / 2 := by
    have hpos : 0 < 1 + z := by linarith
    have hsq : 0 ≤ (1 + z) * (1 - z) ^ 2 := mul_nonneg hpos.le (sq_nonneg _)
    have e : (1 + z) ^ 3 / 2 - 2 * z * (1 + z) = (1 + z) * (1 - z) ^ 2 / 2 := by ring
    linarith
  have hfrac : |2 * z * (1 - z) / (1 + z) ^ 3| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hzden, div_le_iff₀ hzden]
    linarith
  have hDz := Work.Construction.Dz_Fstar_eq (α := p) (z := z) (θ := θ) hp (by linarith : (-1 : ℝ) < z)
  rw [Work.Spaces.Dz] at hDz
  rw [hDz, abs_mul, abs_of_nonneg (mul_nonneg hp.le hq0)]
  calc p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * |2 * z * (1 - z) / (1 + z) ^ 3|
      ≤ p * 10 * (1 / 2) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hq1 hp.le
        · exact hfrac
        · exact abs_nonneg _
        · positivity
    _ = 5 * p := by ring

/-- **The weighted `z`-derivative box of the profile.**

Writing `F = F_* + g`, the derivative splits as `∂_zF = ∂_zF_* + ∂_zg` on the branch `θ ≥ 0`
(`pz_profile_eq_of_nonneg`) and as `∂_zF = -(∂_zg + ∂_zF_*)(·,-θ)` on `θ < 0`
(`pz_profile_eq_of_neg`).  The `F_*` part is bounded by `5p` uniformly (`z_pz_Fstar_abs_le`)
and the perturbation by `Cg'` (hypothesis `hg2`), giving `|z∂_zF| ≤ 5p + Cg'` for `z > 0`,
`|θ| ≤ π/2`. -/
theorem z_pz_profile_abs_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ} {Cg' : ℝ}
    (hg2 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |z * Work.Spaces.pz g z θ| ≤ Cg')
    (hgdiff : ∀ z θ : ℝ, 0 < z → HasDerivAt (fun z' => Work.ConstructionInstance.profile p g z' θ)
      (Work.Spaces.pz (Work.ConstructionInstance.profile p g) z θ) z) :
    ∀ z θ : ℝ, 0 < z → |θ| ≤ Real.pi / 2 →
      |z * Work.Spaces.pz (Work.ConstructionInstance.profile p g) z θ| ≤ 5 * p + Cg' := by
  intro z θ hz hθ
  have hz1 : (-1 : ℝ) < z := by linarith
  rcases le_or_gt 0 θ with hθ0 | hθ0
  · -- positive branch
    have hθmem : θ ∈ Work.Spaces.Iθ :=
      ⟨hθ0, by rw [abs_of_nonneg hθ0] at hθ; exact hθ⟩
    have hsplit := pz_profile_eq_of_nonneg (p := p) (g := g) (z := z) (θ := θ) hz1 hθ0
      (hgdiff z θ hz)
    have hkey : z * Work.Spaces.pz (profile p g) z θ
        = z * Work.Spaces.pz g z θ + z * Work.Spaces.pz (Work.Construction.Fstar p) z θ := by
      rw [hsplit]; ring
    rw [hkey]
    calc |z * Work.Spaces.pz g z θ + z * Work.Spaces.pz (Work.Construction.Fstar p) z θ|
        ≤ |z * Work.Spaces.pz g z θ| + |z * Work.Spaces.pz (Work.Construction.Fstar p) z θ| :=
          abs_add_le _ _
      _ ≤ Cg' + 5 * p :=
          add_le_add (hg2 z θ hz.le hθmem) (z_pz_Fstar_abs_le hp hp1 hz hθmem)
      _ = 5 * p + Cg' := by ring
  · -- negative branch: reduce to `-θ > 0`
    have hθmem : -θ ∈ Work.Spaces.Iθ :=
      ⟨by linarith, by rw [abs_of_neg hθ0] at hθ; exact hθ⟩
    have hsplit := pz_profile_eq_of_neg (p := p) (g := g) (z := z) (θ := θ) hz1 hθ0
      (hgdiff z θ hz)
    have hkey : z * Work.Spaces.pz (profile p g) z θ
        = -(z * Work.Spaces.pz g z (-θ)
            + z * Work.Spaces.pz (Work.Construction.Fstar p) z (-θ)) := by
      rw [hsplit]; ring
    rw [hkey, abs_neg]
    calc |z * Work.Spaces.pz g z (-θ) + z * Work.Spaces.pz (Work.Construction.Fstar p) z (-θ)|
        ≤ |z * Work.Spaces.pz g z (-θ)| + |z * Work.Spaces.pz (Work.Construction.Fstar p) z (-θ)| :=
          abs_add_le _ _
      _ ≤ Cg' + 5 * p :=
          add_le_add (hg2 z (-θ) hz.le hθmem) (z_pz_Fstar_abs_le hp hp1 hz hθmem)
      _ = 5 * p + Cg' := by ring

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core.i0Aux

set_option autoImplicit false

/-! ## The weighted square identity -/

/-- The square of `D · (wz / s^{η/2})` equals `D² wz² s^{-η}`; at `s = 0` both sides vanish. -/
theorem mul_div_rpow_sq_eq (D wz s : ℝ) (hs : 0 ≤ s) (hη : Work.Spaces.eta ≠ 0) :
    (D * (wz / s ^ (Work.Spaces.eta / 2))) ^ 2
      = D ^ 2 * wz ^ 2 * s ^ (-(Work.Spaces.eta)) := by
  have hη2 : Work.Spaces.eta / 2 ≠ 0 := by
    intro h
    exact hη (by linarith [h])
  rcases eq_or_lt_of_le hs with h0 | hpos
  · rw [← h0, Real.zero_rpow hη2, Real.zero_rpow (neg_ne_zero.mpr hη)]
    ring
  · have h1 : (s ^ (Work.Spaces.eta / 2)) ^ 2 = s ^ Work.Spaces.eta := by
      rw [← Real.rpow_natCast (s ^ (Work.Spaces.eta / 2)) 2, ← Real.rpow_mul hpos.le]
      norm_num
    rw [mul_pow, div_pow, h1, div_eq_mul_inv, Real.rpow_neg hpos.le]
    ring

/-! ## The angular endpoint values of the iterates -/

/-- Every `D_z`-iterate of a profile vanishing at `θ = 0` still vanishes there. -/
theorem DzIter_zero_theta {V : ℝ → ℝ → ℝ} (h0 : ∀ z : ℝ, V z 0 = 0) (r : ℕ) :
    ∀ z : ℝ, Work.Spaces.DzIter r V z 0 = 0 := by
  induction r with
  | zero => simpa using h0
  | succ r ih =>
      intro z
      have hslice : (fun z' : ℝ => Work.Spaces.DzIter r V z' 0) = fun _ => (0 : ℝ) :=
        funext ih
      show z * Work.Spaces.pz (Work.Spaces.DzIter r V) z 0 = 0
      rw [show Work.Spaces.pz (Work.Spaces.DzIter r V) z 0
          = deriv (fun z' : ℝ => Work.Spaces.DzIter r V z' 0) z from rfl, hslice, deriv_const,
        mul_zero]

/-- Every `D_z`-iterate of a profile vanishing at `θ = π/2` still vanishes there. -/
theorem DzIter_pi_theta {V : ℝ → ℝ → ℝ} (hpi : ∀ z : ℝ, V z (Real.pi / 2) = 0) (r : ℕ) :
    ∀ z : ℝ, Work.Spaces.DzIter r V z (Real.pi / 2) = 0 := by
  induction r with
  | zero => simpa using hpi
  | succ r ih =>
      intro z
      have hslice : (fun z' : ℝ => Work.Spaces.DzIter r V z' (Real.pi / 2)) = fun _ => (0 : ℝ) :=
        funext ih
      show z * Work.Spaces.pz (Work.Spaces.DzIter r V) z (Real.pi / 2) = 0
      rw [show Work.Spaces.pz (Work.Spaces.DzIter r V) z (Real.pi / 2)
          = deriv (fun z' : ℝ => Work.Spaces.DzIter r V z' (Real.pi / 2)) z from rfl, hslice,
        deriv_const, mul_zero]

/-! ## The commutation of `∂_θ²` with the `D_z`-iterates -/

/-- On the open quadrant, `∂_θ² (D_z^r V) = D_z^r (∂_θ² V)`. -/
theorem pthIter2_DzIter_comm {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < Real.pi / 2) (r : ℕ) :
    Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ
      = Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ := by
  have hsq : ∀ θ' : ℝ, 0 < θ' → θ' < Real.pi / 2 →
      Work.Spaces.pth (Work.Spaces.DzIter r V) z θ'
        = Work.Spaces.DzIter r (Work.Spaces.pth V) z θ' := by
    intro θ' h1 h2
    exact Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 ((Work.FTS.EllipticEst.smoothOpen_iff_forall V).mp hV) r
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h1, h2⟩)
  have hsq2 : ∀ θ' : ℝ, 0 < θ' → θ' < Real.pi / 2 →
      Work.Spaces.pth (Work.Spaces.DzIter r (Work.Spaces.pth V)) z θ'
        = Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ' := by
    intro θ' h1 h2
    exact Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.pth V)).mp hV.pth) r
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h1, h2⟩)
  have hloc : (fun θ' : ℝ => Work.Spaces.pth (Work.Spaces.DzIter r V) z θ')
      =ᶠ[𝓝 θ] (fun θ' : ℝ => Work.Spaces.DzIter r (Work.Spaces.pth V) z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ1, hθ2⟩] with θ' hθ'
    exact hsq θ' hθ'.1 hθ'.2
  have hfinal : Work.Spaces.pth (Work.Spaces.DzIter r (Work.Spaces.pth V)) z θ
      = Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ :=
    hsq2 θ hθ1 hθ2
  calc Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ
      = deriv (fun θ' : ℝ => Work.Spaces.pth (Work.Spaces.DzIter r V) z θ') θ := rfl
    _ = deriv (fun θ' : ℝ => Work.Spaces.DzIter r (Work.Spaces.pth V) z θ') θ := by
          rw [hloc.deriv_eq]
    _ = Work.Spaces.pth (Work.Spaces.DzIter r (Work.Spaces.pth V)) z θ := rfl
    _ = Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ := hfinal

/-! ## The three value bounds -/

/-- For `r ≤ k`: `∫_z dIntS (D_z^r V) z ≤ HkSq α k (D_zV)`. -/
theorem dIntS_integral_le_HkSq {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.Dz V)) (hr : r ≤ k) :
    (∫ z in Work.Spaces.Iz, dIntS (Work.Spaces.DzIter r V) z)
      ≤ Work.Spaces.HkSq α k (Work.Spaces.Dz V) := by
  have hstep : (∫ z in Work.Spaces.Iz, dIntS (Work.Spaces.DzIter r V) z)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    rw [dIntS, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [Work.FTS.EllipticEst.thEta,
      mul_div_rpow_sq_eq (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ) (Work.Spaces.w z)
        (Real.sin (2 * θ)) (Work.FTS.EllipticEst.sin_two_nonneg hθ) Work.Spaces.eta_pos.ne']
    ring
  rw [hstep]
  have hfun : ∀ z θ : ℝ, Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ
      = Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ := by
    intro z θ
    have h2 : Work.Spaces.DzIter (r + 1) V = Work.Spaces.DzIter r (Work.Spaces.Dz V) :=
      Work.Spaces.DzIter_add_right r 1 V
    exact congrFun (congrFun h2 z) θ
  have hcongr : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rw [hfun z θ]
  rw [hcongr]
  exact Work.Spaces.L2Sq_DzIter_le_HkSq α k (Work.Spaces.Dz V) hmem r hr

/-- For `r ≤ k`: `∫_z ddIntS (D_z^r V) z ≤ HkSq α k (D_z²V)`. -/
theorem ddIntS_integral_le_HkSq {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V)) (hr : r ≤ k) :
    (∫ z in Work.Spaces.Iz, ddIntS (Work.Spaces.DzIter r V) z)
      ≤ Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V) := by
  have hstep : (∫ z in Work.Spaces.Iz, ddIntS (Work.Spaces.DzIter r V) z)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter r V)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    rw [ddIntS, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [Work.FTS.EllipticEst.thEta,
      mul_div_rpow_sq_eq (Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter r V)) z θ)
        (Work.Spaces.w z) (Real.sin (2 * θ))
        (Work.FTS.EllipticEst.sin_two_nonneg hθ) Work.Spaces.eta_pos.ne']
    ring
  rw [hstep]
  have hfun : ∀ z θ : ℝ, Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter r V)) z θ
      = Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ := by
    intro z θ
    have h2 : Work.Spaces.DzIter (r + 2) V = Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) :=
      Work.Spaces.DzIter_add_right r 2 V
    exact congrFun (congrFun h2 z) θ
  have hcongr : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.DzIter r V)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rw [hfun z θ]
  rw [hcongr]
  exact Work.Spaces.L2Sq_DzIter_le_HkSq α k (Work.Spaces.DzIter 2 V) hmem r hr

/-- For `r ≤ k`: `∫_z ttIntS (D_z^r V) z ≤ HkSq α k (∂_θ²V)`. -/
theorem ttIntS_integral_le_HkSq {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V)) (hr : r ≤ k) :
    (∫ z in Work.Spaces.Iz, ttIntS (Work.Spaces.DzIter r V) z)
      ≤ Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V) := by
  have hstep : (∫ z in Work.Spaces.Iz, ttIntS (Work.Spaces.DzIter r V) z)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    have hA : (∫ z in Work.Spaces.Iz, ttIntS (Work.Spaces.DzIter r V) z)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      rw [ttIntS, ← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
      ring
    rw [hA]
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
      ← MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))]
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
      ← MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
          (b := Real.pi / 2))]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    rw [pthIter2_DzIter_comm hV hz hθ.1 hθ.2 r, Work.FTS.EllipticEst.thEta,
      mul_div_rpow_sq_eq (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ) (Work.Spaces.w z)
        (Real.sin (2 * θ)) hs.le Work.Spaces.eta_pos.ne']
    try ring
  rw [hstep]
  exact Work.Spaces.L2Sq_DzIter_le_HkSq α k (Work.Spaces.pthIter 2 V) hmem r hr

end Work.EllipticEst.Core.i0Aux
end
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.InterpDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core.i0Aux

set_option autoImplicit false

/-- The interpolation inequality of `Core/Defs` with constant `C`, for the *strip* class: `G` is
`C^∞` on `(0,∞) × (-1, π/2+1)`.  The four `IntegrableOn` hypotheses make the four slice
functionals honest, so that the displayed Bochner integrals are the genuine values. -/
def InterpStrip (C : ℝ) : Prop :=
  ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))) →
    (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.mixIntS G z) Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.ddIntS G z) Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.ttIntS G z) Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.dIntS G z) Work.Spaces.Iz →
    α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
      ≤ C * (α ^ 4 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS G z)
          + (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS G z)
          + α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS G z))

/-- **Slicewise honesty of the three right-hand side functionals** for `z > 0`: each of the three
angular slice integrands is integrable against `σ_η = sin(2θ)^{-η}`.  This is what rules out the
*junk-value* case (`¬ Integrable` ⟹ the Bochner integral is `0`), in which the weaker
hypothesis `IntegrableOn (fun z => ttIntS G z) Iz` would be satisfied by the function `0` while
the corresponding slice integral diverges.

Under this hypothesis the slice functionals are honest and the three Bochner integrals in the
statement below are the genuine values. -/
def SliceHonestOpen (G : ℝ → ℝ → ℝ) : Prop :=
  (∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) ∧
  (∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) ∧
  (∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
    Work.Spaces.Iθ)


end Work.EllipticEst.Core.i0Aux
end
end
-- ===== merged: Submission.Work.EllipticEst.logChi_iSup_lintegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst

open MeasureTheory
open Filter

/-- The logarithmic cut-off `logChi n` is measurable: it is the explicit `C^∞` bump
`Work.ChiExplicit.chi` composed with the measurable function `z ↦ log z / log ((n:ℝ)+2)`. -/
lemma measurable_logChi (n : ℕ) :
    Measurable (Work.FTS.EllipticEst.TT.logChi n) :=
  ((Work.ChiExplicit.chi_contDiff 1).continuous.measurable).comp
    (Real.measurable_log.div_const _)

/-- **Monotone convergence along the logarithmic cut-off family**: for a nonnegative
a.e.-measurable `f` on `(0,∞)` (each `f·logChi n²` integrable),

`∫⁻ f = ⨆_n ofReal (∫ f · (logChi n)²)`.

This is Piece 3b of `Submission/Work/EllipticEst/NOTES_AgmonCutoff.md`; it uses
`logChi_mem_Icc`, `logChi_mono_succ`, `logChi_tendsto_one` and monotone convergence. -/
theorem logChi_iSup_lintegral (f : ℝ → ℝ) (hf0 : ∀ z : ℝ, 0 ≤ f z)
    (hfm : AEMeasurable f (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hint : ∀ n : ℕ, MeasureTheory.IntegrableOn
      (fun z : ℝ => f z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2) (Set.Ioi (0 : ℝ))) :
    (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (f z))
      = ⨆ n : ℕ, ENNReal.ofReal
          (∫ z in Set.Ioi (0 : ℝ), f z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2) := by
  -- The truncated integrands are increasing in `n`: `f ≥ 0` and `0 ≤ logChi n ≤ logChi (n+1)`.
  have hmono : ∀ n : ℕ, ∀ z : ℝ,
      f z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2
        ≤ f z * (Work.FTS.EllipticEst.TT.logChi (n + 1) z) ^ 2 := by
    intro n z
    have h0 : 0 ≤ Work.FTS.EllipticEst.TT.logChi n z :=
      (Work.FTS.EllipticEst.TT.logChi_mem_Icc n z).1
    have hle : Work.FTS.EllipticEst.TT.logChi n z
        ≤ Work.FTS.EllipticEst.TT.logChi (n + 1) z :=
      Work.FTS.EllipticEst.Blocks.logChi_mono_succ n z
    have hs : (Work.FTS.EllipticEst.TT.logChi n z) ^ 2
        ≤ (Work.FTS.EllipticEst.TT.logChi (n + 1) z) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self h0 hle
    exact mul_le_mul_of_nonneg_left hs (hf0 z)
  -- Pointwise convergence `f · (logChi n)² → f` on `(0,∞)`.
  have hten : ∀ z : ℝ, 0 < z → Tendsto
      (fun n : ℕ => f z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2) atTop (nhds (f z)) := by
    intro z hz
    have h1 := Work.FTS.EllipticEst.Blocks.logChi_tendsto_one z hz
    have h2 : Tendsto (fun n : ℕ => (Work.FTS.EllipticEst.TT.logChi n z) ^ 2)
        atTop (nhds 1) := by
      simpa using h1.pow 2
    simpa using (tendsto_const_nhds.mul h2)
  -- The pointwise supremum of the (monotone, convergent) family, on `(0,∞)`.
  have hsup : ∀ z : ℝ, 0 < z →
      (⨆ n : ℕ, ENNReal.ofReal (f z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2))
        = ENNReal.ofReal (f z) := by
    intro z hz
    refine iSup_eq_of_tendsto ?_ ?_
    · exact monotone_nat_of_le_succ fun n => ENNReal.ofReal_le_ofReal (hmono n z)
    · exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hten z hz)
  have hae : (fun z : ℝ =>
        (⨆ n : ℕ, ENNReal.ofReal (f z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2)))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] fun z : ℝ => ENNReal.ofReal (f z) :=
    (ae_restrict_iff' isOpen_Ioi.measurableSet).mpr
      (Eventually.of_forall fun z hz => hsup z hz)
  calc (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (f z))
      = ∫⁻ z in Set.Ioi (0 : ℝ),
          (⨆ n : ℕ, ENNReal.ofReal (f z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2)) :=
        (lintegral_congr_ae hae).symm
    _ = ⨆ n : ℕ, ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (f z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2) := by
        refine lintegral_iSup' (fun n => ?_) (Eventually.of_forall fun z => ?_)
        · exact (hfm.mul ((measurable_logChi n).pow_const 2).aemeasurable).ennreal_ofReal
        · exact monotone_nat_of_le_succ fun n => ENNReal.ofReal_le_ofReal (hmono n z)
    _ = ⨆ n : ℕ, ENNReal.ofReal
          (∫ z in Set.Ioi (0 : ℝ), f z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2) :=
        iSup_congr fun n =>
          (ofReal_integral_eq_lintegral_ofReal (hint n)
            (Eventually.of_forall fun z => mul_nonneg (hf0 z) (sq_nonneg _))).symm

end Work.EllipticEst
end
-- ===== merged: Submission.Work.EllipticEst.logChi_second_deriv_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.EllipticEst

/-! ## Piece 1 of `NOTES_AgmonCutoff.md`: the second logarithmic derivative of `logChi n`

`logChi n z = chi (log z / L)` with `L = log ((n : ℝ) + 2)` and
`chi = Work.ChiExplicit.chi = fun t => Real.smoothTransition (2 - |t|)`, the explicit smooth
bump.  The chain rule gives, for `z > 0` and `t = log z / L`,

  `(logChi n)'(z)  = chi'(t) / (z L)`,
  `(logChi n)''(z) = chi''(t) / (z L)² - chi'(t) / (z² L)`,

so that `z² (logChi n)''(z) = chi''(t)/L² - chi'(t)/L`.  Both `chi'` and `chi''` are globally
bounded (they are continuous and vanish outside `[-2,2]`), hence `|z² (logChi n)''(z)|` is
bounded by `K / L` uniformly in `n` and `z`.  This is exactly the statement
`logChi_second_deriv_le` below, the input `δ = δ_n → 0` of the Agmon estimate. -/

/-- **A global bound for the second derivative of the explicit cut-off.**  `deriv (deriv chi)`
is continuous (`chi` is `C^∞`) and vanishes strictly outside `[-2,2]` (where `chi` is locally
`0`, so both its first and its second derivative vanish there); on the compact interval `[-2,2]`
the continuous function `|deriv (deriv chi)|` therefore attains its maximum. -/
theorem exists_bound_deriv_deriv_chi :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, |deriv (deriv Work.ChiExplicit.chi) t| ≤ K := by
  have hcont : Continuous (fun t : ℝ => |deriv (deriv Work.ChiExplicit.chi) t|) := by
    have h1 : Continuous (iteratedDeriv 2 Work.ChiExplicit.chi) :=
      (Work.ChiExplicit.chi_contDiff ⊤).continuous_iteratedDeriv 2 (by simp)
    have h2 : iteratedDeriv 2 Work.ChiExplicit.chi
        = deriv (deriv Work.ChiExplicit.chi) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact (h1.congr (fun t => by rw [h2])).abs
  -- `chi` is locally `0` outside `[-2,2]`, hence so are `chi'` and `chi''`.
  have hzero : ∀ t : ℝ, 2 < |t| → deriv (deriv Work.ChiExplicit.chi) t = 0 := by
    intro t ht
    have hopen : IsOpen {s : ℝ | (2 : ℝ) < |s|} := isOpen_lt continuous_const continuous_abs
    have hev : deriv Work.ChiExplicit.chi =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [hopen.mem_nhds ht] with s hs
      have h0 : Work.ChiExplicit.chi =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
        filter_upwards [hopen.mem_nhds hs] with u hu
        exact Work.ChiExplicit.chi_eq_zero hu.le
      rw [h0.deriv_eq, deriv_const]
    rw [hev.deriv_eq, deriv_const]
  obtain ⟨x₀, -, hmax⟩ :=
    (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_isMaxOn
      (⟨(-2 : ℝ), by norm_num⟩ : (Set.Icc (-2 : ℝ) 2).Nonempty)
      (f := fun t : ℝ => |deriv (deriv Work.ChiExplicit.chi) t|) hcont.continuousOn
  refine ⟨|deriv (deriv Work.ChiExplicit.chi) x₀|, abs_nonneg _, ?_⟩
  intro t
  by_cases ht : |t| ≤ 2
  · exact (isMaxOn_iff.mp hmax) t (Set.mem_Icc.mpr (abs_le.mp ht))
  · rw [hzero t (lt_of_not_ge ht)]
    simp

/-- **The second derivative of `logChi n`** for `z > 0`, by the chain rule:
with `L = log ((n : ℝ) + 2)`, `t = log z / L`,

  `(logChi n)''(z) = (chi''(t) - chi'(t)·L) / (z·L)²`. -/
theorem deriv_deriv_logChi_eq (n : ℕ) {z : ℝ} (hz : 0 < z) :
    deriv (deriv (Work.FTS.EllipticEst.TT.logChi n)) z =
      (deriv (deriv Work.ChiExplicit.chi) (Real.log z / Real.log ((n : ℝ) + 2))
        - deriv Work.ChiExplicit.chi (Real.log z / Real.log ((n : ℝ) + 2))
          * Real.log ((n : ℝ) + 2)) / (z * Real.log ((n : ℝ) + 2)) ^ 2 := by
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hLpos : 0 < L := by
    rw [hL]; exact Work.FTS.EllipticEst.TT.log_two_add_natCast_pos n
  have hL0 : L ≠ 0 := ne_of_gt hLpos
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hdiffchi : Differentiable ℝ (deriv Work.ChiExplicit.chi) := by
    have h2 : ContDiff ℝ 2 Work.ChiExplicit.chi := Work.ChiExplicit.chi_contDiff 2
    exact h2.differentiable_deriv_two
  have hgz : DifferentiableAt ℝ (fun w : ℝ => Real.log w / L) z :=
    (Real.differentiableAt_log hz0).div_const L
  have hchid : DifferentiableAt ℝ (deriv Work.ChiExplicit.chi) (Real.log z / L) :=
    hdiffchi.differentiableAt
  have hAz : DifferentiableAt ℝ
      (fun w : ℝ => deriv Work.ChiExplicit.chi (Real.log w / L)) z := by
    simpa only [Function.comp_def] using hchid.comp z hgz
  have hBz : DifferentiableAt ℝ (fun w : ℝ => w * L) z :=
    differentiableAt_id.mul_const L
  -- On `(0,∞)`, `deriv (logChi n)` is the function used in the chain rule above.
  have hev : deriv (Work.FTS.EllipticEst.TT.logChi n)
      =ᶠ[𝓝 z] (fun w : ℝ => deriv Work.ChiExplicit.chi (Real.log w / L) / (w * L)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
    rw [Work.FTS.EllipticEst.Blocks.deriv_logChi_eq n hw, ← hL, mul_one_div]
  rw [hev.deriv_eq]
  have hderivA : deriv (fun w : ℝ => deriv Work.ChiExplicit.chi (Real.log w / L)) z
      = deriv (deriv Work.ChiExplicit.chi) (Real.log z / L) * (1 / (z * L)) := by
    rw [show (fun w : ℝ => deriv Work.ChiExplicit.chi (Real.log w / L))
        = (deriv Work.ChiExplicit.chi) ∘ (fun w : ℝ => Real.log w / L) from rfl,
      deriv_comp z hchid hgz, deriv_div_const, Real.deriv_log]
    rw [inv_eq_one_div, div_div]
  have hderivB : deriv (fun w : ℝ => w * L) z = L := by
    rw [show (fun w : ℝ => w * L) = fun y : ℝ => id y * L from rfl,
      deriv_mul_const differentiableAt_id L, deriv_id]
    ring
  have hBne : (fun w : ℝ => w * L) z ≠ 0 := by
    show z * L ≠ 0
    exact mul_ne_zero hz0 hL0
  rw [deriv_fun_div hAz hBz hBne, hderivA, hderivB]
  set A := deriv (deriv Work.ChiExplicit.chi) (Real.log z / L) with hA
  set B := deriv Work.ChiExplicit.chi (Real.log z / L) with hB
  field_simp

/-- **The identity behind the estimate**, in the form in which it is bounded:
for `z > 0`, `L = log ((n : ℝ) + 2)` and `t = log z / L`,

  `z² · (logChi n)''(z) = chi''(t)/L² - chi'(t)/L`. -/
theorem logChi_second_deriv_eq (n : ℕ) {z : ℝ} (hz : 0 < z) :
    z ^ 2 * deriv (deriv (Work.FTS.EllipticEst.TT.logChi n)) z =
      deriv (deriv Work.ChiExplicit.chi) (Real.log z / Real.log ((n : ℝ) + 2))
        / Real.log ((n : ℝ) + 2) ^ 2
      - deriv Work.ChiExplicit.chi (Real.log z / Real.log ((n : ℝ) + 2))
        / Real.log ((n : ℝ) + 2) := by
  have hLpos : 0 < Real.log ((n : ℝ) + 2) :=
    Work.FTS.EllipticEst.TT.log_two_add_natCast_pos n
  have hz0 : z ≠ 0 := ne_of_gt hz
  rw [deriv_deriv_logChi_eq n hz]
  set A := deriv (deriv Work.ChiExplicit.chi) (Real.log z / Real.log ((n : ℝ) + 2)) with hA
  set B := deriv Work.ChiExplicit.chi (Real.log z / Real.log ((n : ℝ) + 2)) with hB
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hLpos' : 0 < L := by rw [hL]; exact hLpos
  have hL0' : L ≠ 0 := ne_of_gt hLpos'
  field_simp

/-- Second logarithmic derivative of the cut-off family `logChi n`: on `(0,∞)` the quantity
`z²·(logChi n)''(z) = chi''(t)/L² - chi'(t)/L` (with `t = log z / log ((n:ℝ)+2)`) is bounded by
`K / log ((n:ℝ)+2)`, uniformly in `z`.  See `Submission/Work/EllipticEst/NOTES_AgmonCutoff.md`
(Piece 1). -/
theorem logChi_second_deriv_le : ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (z : ℝ), 0 < z →
    |z ^ 2 * deriv (deriv (Work.FTS.EllipticEst.TT.logChi n)) z|
      ≤ K / Real.log ((n : ℝ) + 2) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := Work.FTS.EllipticEst.Blocks.exists_bound_deriv_chi
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_bound_deriv_deriv_chi
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K₁ + K₂ / Real.log 2 + 1, by positivity, ?_⟩
  intro n z hz
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hLpos : 0 < Real.log ((n : ℝ) + 2) :=
    Work.FTS.EllipticEst.TT.log_two_add_natCast_pos n
  have hLge : Real.log 2 ≤ Real.log ((n : ℝ) + 2) :=
    Work.FTS.EllipticEst.TT.log_two_le_log n
  rw [logChi_second_deriv_eq n hz]
  set A := deriv (deriv Work.ChiExplicit.chi) (Real.log z / Real.log ((n : ℝ) + 2)) with hA
  set B := deriv Work.ChiExplicit.chi (Real.log z / Real.log ((n : ℝ) + 2)) with hB
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hLpos' : 0 < L := by rw [hL]; exact hLpos
  have hLge' : Real.log 2 ≤ L := by rw [hL]; exact hLge
  have hAabs : |A| ≤ K₂ := by rw [hA]; exact hK₂ _
  have hBabs : |B| ≤ K₁ := by rw [hB]; exact hK₁ _
  have htri : |A / L ^ 2 - B / L| ≤ |A| / L ^ 2 + |B| / L := by
    calc |A / L ^ 2 - B / L| = |A / L ^ 2 + -(B / L)| := by rw [sub_eq_add_neg]
      _ ≤ |A / L ^ 2| + |-(B / L)| := abs_add_le _ _
      _ = |A| / L ^ 2 + |B| / L := by
          rw [abs_div, abs_neg, abs_div, abs_of_pos (pow_pos hLpos' 2), abs_of_pos hLpos']
  have hstep : |A| / L ^ 2 + |B| / L ≤ K₂ / L ^ 2 + K₁ / L :=
    add_le_add (div_le_div_of_nonneg_right hAabs (pow_pos hLpos' 2).le)
      (div_le_div_of_nonneg_right hBabs hLpos'.le)
  have hstep2 : K₂ / L ^ 2 ≤ K₂ / (Real.log 2 * L) := by
    refine div_le_div_of_nonneg_left hK₂0 (mul_pos hlog2 hLpos') ?_
    nlinarith
  have hstep3 : K₂ / (Real.log 2 * L) = K₂ / Real.log 2 / L :=
    (div_div K₂ (Real.log 2) L).symm
  have hstep4 : K₂ / L ^ 2 + K₁ / L ≤ (K₁ + K₂ / Real.log 2 + 1) / L := by
    have h : K₂ / L ^ 2 + K₁ / L ≤ K₂ / Real.log 2 / L + K₁ / L :=
      add_le_add (hstep2.trans hstep3.le) le_rfl
    refine h.trans ?_
    have h2 : K₂ / Real.log 2 / L + K₁ / L = (K₁ + K₂ / Real.log 2) / L := by
      rw [add_div]
      ring
    rw [h2]
    exact div_le_div_of_nonneg_right (by linarith) hLpos'.le
  calc |A / L ^ 2 - B / L| ≤ |A| / L ^ 2 + |B| / L := htri
    _ ≤ K₂ / L ^ 2 + K₁ / L := hstep
    _ ≤ (K₁ + K₂ / Real.log 2 + 1) / L := hstep4

end Work.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.ClassCHon.Zpz.Auxiliary.abs_pzIter2_le_sqrt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Zpz.Aux


end Work.FTS.ClassCHon.Zpz.Aux
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.Hardy.slice_sinCos2_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T.Hardy

set_option autoImplicit false

/-! ## Elementary auxiliary facts -/

/-- The angular profile `sinθcos²θ` is continuous. -/
private theorem continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2
  fun_prop

/-- `SmoothQuad f` gives continuity of the uncurried `f` on the smaller open quadrant
`(0,∞) × (0,π/2)`. -/
private theorem continuousOn_uncurry_of_smoothQuad {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  hsm.continuousOn.mono (Set.prod_mono (fun x hx => by
    simp only [Set.mem_Ioi] at hx ⊢
    linarith) (subset_refl _))

/-- The angular factor `θ ↦ w z / sin(2θ)^{η/2}` is measurable. -/
private theorem measurable_angularWeight (z : ℝ) :
    Measurable (fun θ : ℝ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  exact measurable_const.div (hsin.pow_const _)

/-- The angular interval `Iθ = [0,π/2]` has finite Lebesgue measure. -/
private theorem volume_Iθ_lt_top : (volume : Measure ℝ) Work.Spaces.Iθ < ⊤ := by
  rw [Work.Spaces.Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

/-! ## The main statement -/

theorem slice_sinCos2_integrable (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => f z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  intro z hz
  have hu : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    continuousOn_uncurry_of_smoothQuad hsm
  have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- almost everywhere strong measurability of the angular slice of `f`
  have haesm_f : AEStronglyMeasurable (fun θ : ℝ => f z θ) (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry f) hu hz
  -- the weighted square `(f z θ · w z / sin(2θ)^{η/2})²` is the `i = 0` summand of the
  -- `ℋ⁴`-integrand at `z`, hence integrable
  have hterm : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (f z θ * (Work.Spaces.w z
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Work.Spaces.Iθ := by
    refine (hmem.1 z hzIz).mono' ?_ ?_
    · exact (haesm_f.mul (measurable_angularWeight z).aestronglyMeasurable).pow 2
    · refine Eventually.of_forall fun θ => ?_
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ 0 (by norm_num)
  -- the dominating function of the AM–GM bound: the weighted square plus the constant `1`
  have hdom : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (f z θ * (Work.Spaces.w z
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1) Work.Spaces.Iθ :=
    hterm.add (MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ)
      (ne_of_lt volume_Iθ_lt_top))
  refine hdom.mono' ?_ ?_
  · exact haesm_f.mul continuous_sinCos2.measurable.aestronglyMeasurable
  · refine MeasureTheory.ae_restrict_of_forall_mem hIθ fun θ hθ => ?_
    rw [Real.norm_eq_abs]
    exact Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted hz hθ

end Work.FTS.CoercivityFix.Coer1T.Hardy
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.TraceEngine.TraceAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.TraceEngine

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Two angular derivatives -/

/-- `∂_θ sin²(2θ) = 4 sin(2θ) cos(2θ)`. -/
theorem hasDerivAt_sinSq (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2)
      (4 * Real.sin (2 * θ) * Real.cos (2 * θ)) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (2 * Real.cos (2 * θ)) θ := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
    have hfunc : (Real.sin ∘ fun x : ℝ => 2 * x) = fun θ : ℝ => Real.sin (2 * θ) := by
      funext x; rfl
    rw [hfunc] at h
    have hderiv : Real.cos (2 * θ) * (2 * 1) = 2 * Real.cos (2 * θ) := by ring
    rw [hderiv] at h
    exact h
  have h2 : HasDerivAt ((fun θ : ℝ => Real.sin (2 * θ)) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (2 * Real.cos (2 * θ))) θ := h1.pow 2
  have h3 : (2 : ℝ) * (Real.sin (2 * θ)) ^ (2 - 1) * (2 * Real.cos (2 * θ))
      = 4 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    ring
  rw [h3] at h2
  have hfun : ((fun θ : ℝ => Real.sin (2 * θ)) ^ 2)
      = fun θ : ℝ => (Real.sin (2 * θ)) ^ 2 := by
    funext x; rfl
  rw [hfun] at h2
  exact h2

/-- `∂_θ sin(4θ) = 4 cos(4θ)`. -/
theorem hasDerivAt_sinFour (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => Real.sin (4 * θ)) (4 * Real.cos (4 * θ)) θ := by
  have h := (Real.hasDerivAt_sin (4 * θ)).comp θ ((hasDerivAt_id θ).const_mul (4 : ℝ))
  have hfunc : (Real.sin ∘ fun x : ℝ => 4 * x) = fun θ : ℝ => Real.sin (4 * θ) := by
    funext x; rfl
  rw [hfunc] at h
  have hderiv : Real.cos (4 * θ) * (4 * 1) = 4 * Real.cos (4 * θ) := by ring
  rw [hderiv] at h
  exact h

/-! ## Clairaut on the open quadrant -/

/-- On the open quadrant, `∂_θ(D_zG) = D_z(∂_θG)`. -/
theorem pth_Dz_eq_Dz_pth {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pth (Work.Spaces.Dz G) z θ = Work.Spaces.Dz (Work.Spaces.pth G) z θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.mem_Q0).mpr ⟨hz, hθ.1, hθ.2⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry G) (z, θ) :=
    (hG.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).of_le
      (by simp [Work.Stability.smoothOrder])
  have h1 : Work.Spaces.pth (Work.Spaces.Dz G) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz G) z θ := by
    show deriv (fun θ' : ℝ => z * Work.Spaces.pz G z θ') θ
      = z * Work.Spaces.pth (Work.Spaces.pz G) z θ
    rw [deriv_const_mul_field]
    rfl
  have h2 : Work.Spaces.Dz (Work.Spaces.pth G) z θ
      = z * Work.Spaces.pz (Work.Spaces.pth G) z θ := rfl
  rw [h1, h2, Work.Spaces.pz_pth_comm (f := G) hcd]

/-- The two slot-1 integrands agree a.e. on `Iz ×ˢ Iθ`. -/
theorem ae_pth_sq_eq {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)]
    (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.pth (Work.Spaces.Dz G) p.1 p.2) ^ 2) := by
  change ∀ᵐ p ∂(MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)),
    (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2) ^ 2) p
      = (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.pth (Work.Spaces.Dz G) p.1 p.2) ^ 2) p
  rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
    (measurableSet_Ici.prod measurableSet_Icc)]
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ))
    ∪ ((Set.univ : Set ℝ) ×ˢ ({(0 : ℝ), Real.pi / 2} : Set ℝ))) ?_ ?_
  · intro p hp
    obtain ⟨hpS, hpne⟩ := not_imp.mp hp
    obtain ⟨hz, hθ⟩ := Set.mem_prod.mp hpS
    by_cases hz0 : p.1 = 0
    · exact Or.inl ⟨hz0, Set.mem_univ _⟩
    · by_cases hθ0 : p.2 = 0
      · exact Or.inr ⟨Set.mem_univ _, Or.inl hθ0⟩
      · by_cases hθ1 : p.2 = Real.pi / 2
        · exact Or.inr ⟨Set.mem_univ _, Or.inr hθ1⟩
        · exfalso
          have hzpos : 0 < p.1 := lt_of_le_of_ne hz (Ne.symm hz0)
          have hθpos : 0 < p.2 := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
          have hθlt : p.2 < Real.pi / 2 := lt_of_le_of_ne hθ.2 hθ1
          have heq : Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2
              = Work.Spaces.pth (Work.Spaces.Dz G) p.1 p.2 :=
            (pth_Dz_eq_Dz_pth hG hzpos ⟨hθpos, hθlt⟩).symm
          exact hpne (by
            show (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
                * (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2) ^ 2
              = (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
                * (Work.Spaces.pth (Work.Spaces.Dz G) p.1 p.2) ^ 2
            rw [heq])
  · have h1 : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
        (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
      rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, MeasureTheory.Measure.prod_prod,
        MeasureTheory.measure_singleton, zero_mul]
    have hs : (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ({(0 : ℝ), Real.pi / 2} : Set ℝ) = 0 := by
      rw [show ({(0 : ℝ), Real.pi / 2} : Set ℝ) = {0} ∪ {Real.pi / 2} from by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
      exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
        (MeasureTheory.measure_singleton (Real.pi / 2))
    have h2 : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
        ((Set.univ : Set ℝ) ×ˢ ({(0 : ℝ), Real.pi / 2} : Set ℝ)) = 0 := by
      rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, MeasureTheory.Measure.prod_prod, hs,
        mul_zero]
    refine le_antisymm ?_ bot_le
    calc (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
          ((({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ))
            ∪ ((Set.univ : Set ℝ) ×ˢ ({(0 : ℝ), Real.pi / 2} : Set ℝ)))
        ≤ _ + _ := MeasureTheory.measure_union_le _ _
      _ = 0 := by rw [h1, h2, add_zero]

end Work.FTS.EllSol.PkgK5.TraceEngine
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeCrux.AeVLib.Meas =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.EllipticEst.AeCrux

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

set_option linter.unusedSimpArgs false

/-! ## 1. The exponential substitution for `∫⁻` -/

theorem lintegral_Ioi_exp (G : ℝ → ℝ≥0∞) :
    ∫⁻ z, G z ∂((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))
      = ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t) * G (Real.exp t) := by
  have himg : Real.exp '' (Set.univ : Set ℝ) = Set.Ioi 0 := by
    simpa only [Set.image_univ] using Real.range_exp
  have h := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp)
    (f' := Real.exp) (s := Set.univ) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn G
  rw [himg] at h
  rw [show (∫⁻ z, G z ∂((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))))
      = ∫⁻ z in Set.Ioi (0 : ℝ), G z from rfl, h]
  rw [MeasureTheory.setLIntegral_univ]
  exact lintegral_congr fun t => by rw [abs_of_pos (Real.exp_pos t)]

/-! ## 2. The strip substitution -/

theorem lintegral_box_exp {F : ℝ → ℝ → ℝ≥0∞}
    (hAE : AEMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
      ((volume : Measure ℝ).restrict (Set.Ioi 0) |>.prod (volume.restrict Iθ)))
    (hAE₂ : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.1) * F (Real.exp q.1) q.2)
      ((volume : Measure ℝ) |>.prod (volume.restrict Iθ))) :
    ∫⁻ p, F p.1 p.2 ∂((volume : Measure ℝ).restrict (Set.Ioi 0) |>.prod (volume.restrict Iθ))
      = ∫⁻ q, ENNReal.ofReal (Real.exp q.1) * F (Real.exp q.1) q.2
          ∂((volume : Measure ℝ) |>.prod (volume.restrict Iθ)) := by
  have h1 : ∫⁻ p, F p.1 p.2 ∂((volume : Measure ℝ).restrict (Set.Ioi 0) |>.prod (volume.restrict Iθ))
      = ∫⁻ z, (∫⁻ θ, F z θ ∂(volume.restrict Iθ)) ∂(volume.restrict (Set.Ioi (0 : ℝ))) :=
    MeasureTheory.lintegral_prod _ hAE
  have h2 : ∫⁻ z, (∫⁻ θ, F z θ ∂(volume.restrict Iθ))
        ∂(volume.restrict (Set.Ioi (0 : ℝ)))
      = ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t)
          * (∫⁻ θ, F (Real.exp t) θ ∂(volume.restrict Iθ)) :=
    lintegral_Ioi_exp (fun z => ∫⁻ θ, F z θ ∂(volume.restrict Iθ))
  have h3 : ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t)
        * (∫⁻ θ, F (Real.exp t) θ ∂(volume.restrict Iθ))
      = ∫⁻ t : ℝ, ∫⁻ θ, ENNReal.ofReal (Real.exp t) * F (Real.exp t) θ
          ∂(volume.restrict Iθ) := by
    refine lintegral_congr fun t => ?_
    exact (MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
  have h4 : ∫⁻ t : ℝ, ∫⁻ θ, ENNReal.ofReal (Real.exp t) * F (Real.exp t) θ
        ∂(volume.restrict Iθ)
      = ∫⁻ q, ENNReal.ofReal (Real.exp q.1) * F (Real.exp q.1) q.2
          ∂((volume : Measure ℝ) |>.prod (volume.restrict Iθ)) := by
    rw [MeasureTheory.lintegral_prod (f := fun q : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp q.1) * F (Real.exp q.1) q.2) hAE₂]
  rw [h1, h2, h3, h4]

/-! ## 3. The level-zero `HkIntegrand` -/

theorem HkIntegrand_zero (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand, Finset.sum_range_succ, Finset.sum_range_zero,
    Work.Spaces.DzIter_zero, zero_add, add_zero]
  norm_num

theorem HkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
    have hη : 0 ≤ Work.Spaces.eta / 2 := by linarith [Work.Spaces.eta_pos]
    rw [sq, ← Real.rpow_add_of_nonneg hs hη hη,
      show Work.Spaces.eta / 2 + Work.Spaces.eta / 2 = Work.Spaces.eta by ring]
  rw [HkIntegrand_zero, mul_pow, div_pow, h1,
    Work.FTS.EllipticEst.sEta, div_eq_mul_inv, ← Real.rpow_neg hs]
  ring

/-! ## 4. Joint measurability on `univ × Iθ` -/

theorem aesm_prod_univ_Iθ {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable (fun q : ℝ × ℝ => f q.1 q.2)
      (MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)) := by
  have hθ : Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
  have hprod : ((Set.univ : Set ℝ) ×ˢ Iθ : Set (ℝ × ℝ))
      =ᵐ[volume.prod volume] ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ _) hθ
  rw [show MeasureTheory.Measure.prod (volume : Measure ℝ) (volume.restrict Iθ)
      = MeasureTheory.Measure.prod ((volume : Measure ℝ).restrict (Set.univ : Set ℝ))
          (volume.restrict Iθ) from by
    rw [Measure.restrict_univ]]
  rw [MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.Measure.restrict_congr_set hprod]
  exact hf.aestronglyMeasurable (MeasurableSet.univ.prod isOpen_Ioo.measurableSet)

/-! ## 6. Continuity of the slot integrands -/

theorem continuousOn_slot {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.sEta p.2) ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hsinpos : ∀ p ∈ ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)), 0 < Real.sin (2 * p.2) := by
    intro p hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [hfun]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hs : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
        = fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by funext p; rfl
    rw [hfun]
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  exact ((hf.pow 2).mul (hw.pow 2)).mul hs

theorem continuousOn_slotT {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2 * Work.FTS.EllSol.HeavyFlat.omw p.1
      * Work.FTS.EllipticEst.sEta p.2) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hsinpos : ∀ p ∈ ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)), 0 < Real.sin (2 * p.2) := by
    intro p hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  have hΩ : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllSol.HeavyFlat.omw p.1)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.FTS.EllSol.HeavyFlat.omw p.1)
        = fun p : ℝ × ℝ => (1 + Real.exp p.1) ^ 4 * Real.exp (-(3 * p.1)) := by funext p; rfl
    rw [hfun]
    exact ((continuousOn_const.add
        ((Real.continuous_exp.comp continuous_fst).continuousOn)).pow 4).mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_fst).neg).continuousOn)
  have hs : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
        = fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by funext p; rfl
    rw [hfun]
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  exact ((hg.pow 2).mul hΩ).mul hs


end Work.FTS.EllipticEst.AeCrux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.AgmonSmallness =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

open scoped Real Topology
open Set Filter

/-- **The sharp, `n`-dependent commutator bound.**  If `K` bounds `|chi'|` globally then for
`z > 0`
`|z · (logChi n)'(z)| ≤ K / log((n:ℝ)+2)`.

This refines `abs_mul_deriv_logChi_le` (which replaces the denominator `log((n:ℝ)+2)` by the
weaker uniform lower bound `log 2`): the chain rule gives
`z · (logChi n)'(z) = chi'(log z / log((n:ℝ)+2)) / log((n:ℝ)+2)`, so the dependence on `n`
survives in the denominator and tends to `0`. -/
lemma abs_mul_deriv_logChi_le_sharp {K : ℝ}
    (hK : ∀ t : ℝ, |deriv Work.ChiExplicit.chi t| ≤ K) (n : ℕ) {z : ℝ} (hz : 0 < z) :
    |z * deriv (Work.FTS.EllipticEst.TT.logChi n) z| ≤ K / Real.log ((n : ℝ) + 2) := by
  have hc : 0 < Real.log ((n : ℝ) + 2) := Work.FTS.EllipticEst.TT.log_two_add_natCast_pos n
  set t := Real.log z / Real.log ((n : ℝ) + 2) with ht
  have heq : z * (deriv Work.ChiExplicit.chi t * (1 / (z * Real.log ((n : ℝ) + 2)))) =
      deriv Work.ChiExplicit.chi t / Real.log ((n : ℝ) + 2) := by
    field_simp
  rw [deriv_logChi_eq n hz, heq, abs_div, abs_of_pos hc]
  exact div_le_div_of_nonneg_right (hK t) hc.le

/-- **The logarithmic cut-off is eventually a small commutator.**

`logChi n z = chi (log z / log ((n:ℝ)+2))` with `chi = Work.ChiExplicit.chi` the explicit smooth
bump (`= 1` on `[-1,1]`, `= 0` off `(-2,2)`, values in `[0,1]`).  For `z > 0` its derivative is
`chi'(log z / log((n:ℝ)+2)) / (z · log((n:ℝ)+2))` (see `deriv_logChi_eq` in
`Submission.Work.FTS.EllipticEst.Blocks.logChiFamily`), so
`|z · (logChi n)'(z)| ≤ K/log((n:ℝ)+2)` with `K` a global bound of `|chi'|` (available as
`exists_bound_deriv_chi` in the same file), and `log((n:ℝ)+2) → ∞`.  Hence for all large `n` the
commutator `|z χ'|` is at most `1/8`, uniformly in `z > 0`.  (This smallness is what makes the
cut-off error absorbable in the proof of
`Work.FTS.EllipticEst.Blocks.DzAgmonLintegral_of_compact`.) -/
theorem AgmonSmallness :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ z : ℝ, 0 < z →
      |z * deriv (Work.FTS.EllipticEst.TT.logChi n) z| ≤ (1 / 8 : ℝ) := by
  obtain ⟨K, _hK0, hK⟩ := exists_bound_deriv_chi
  -- `log ((n:ℝ)+2) → ∞`, so beyond some `N₀` the denominator is at least `8K`.
  have hden : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_mono (fun n : ℕ => by
        have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith) tendsto_natCast_atTop_atTop)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hden.eventually_ge_atTop (8 * K))
  refine ⟨N₀, fun n hn z hz => ?_⟩
  have hlog : 8 * K ≤ Real.log ((n : ℝ) + 2) := hN₀ n hn
  calc |z * deriv (Work.FTS.EllipticEst.TT.logChi n) z|
      ≤ K / Real.log ((n : ℝ) + 2) := abs_mul_deriv_logChi_le_sharp hK n hz
    _ ≤ 1 / 8 := by
        have hc : 0 < Real.log ((n : ℝ) + 2) :=
          Work.FTS.EllipticEst.TT.log_two_add_natCast_pos n
        rw [div_le_iff₀ hc]
        linarith

end Work.FTS.EllipticEst.Blocks
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeProof.ae.VnWeighted =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted transfer bounds for the shifted cutoff family `Vn`

`Vn n z = ψ((n+1)z - 2)·χ(z/(n+1))` (see `CutSeq`), `w z = (1+z)²/z²` (see `Spaces`).

The theorem `VnWeighted` proved here is the truncation ingredient of the weighted radial
energy identity: the transfer quantities `(z²·Vn n·w²)''` and `(z·Vn n·w²)'` are bounded,
*uniformly in `n`*, by a multiple of `w²`; and they converge, for each fixed `z > 0`, to the
corresponding quantities with `Vn n` replaced by `1`.

The uniform bound is a consequence of the two-scale structure together with the rescaled
derivative bounds `VnRescaledBounds` (`|z ∂_zVn n| ≤ 2M`, `|z² ∂_z²Vn n| ≤ 4M²`, uniform in
`n` and `z`) and of the elementary estimates

* `|deriv (z²w²)| ≤ 2z·w²`,  `|deriv² (z²w²)| ≤ 6·w²`,  `|deriv (zw²)| ≤ 3·w²`  (`z > 0`)

for the weight.  The transfer lemmas `vw_dderiv_bound`, `vw_deriv_bound` below are stated for
an *arbitrary* smooth `V` with such rescaled bounds, and are applied to `V = Vn n`.
-/

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeProof.ae

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Rational bounds for the derivatives of the radial weight -/




/-! ## Differentiability of the weight functions away from `0` -/




/-! ## The two transfer bounds -/



/-! ## `Vn n` is eventually `1` on a neighbourhood of any `z > 0` -/


/-! ## The theorem -/


end Work.FTS.EllipticEst.H2W.AeProof.ae
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.mixedSlotInterpEta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.EllipticEst.Prop.mixedSlotInterpEta`

The mixed-slot interpolation at level `0`, with the **gamma weight** on the left and the **eta
weights** on the right:

`∫∫ (D_z∂_θG)² w² sin(2θ)^{2-γ} ≤ C (HkSq α 0 (D_z²G) + HkSq α 0 (∂_θ²G) + HkSq α 0 (D_zG))`,

for `G` smooth on the open quadrant, vanishing on the two angular boundary lines, and with the three
`ℋ⁰`-slots honest (`HkMem α 0`).

## Status and route

The statement is TRUE, but its proof is the *wild-class* two-integration-by-parts argument of the
paper's §Elliptic estimates, whose two analytic ingredients are the endpoint-flux analyses.  The
complete route, the obstacles (including two refuted candidate flux lemmas), and the delivered
companion lemmas are recorded in `NOTES_mixedSlotInterpEta.md` (same directory).  In short:

* `Work.FTS.EllipticEst.Prop.radialIbpWild` — **PROVED**, the radial IBP with the `w²` weight and the
  flux as an explicit hypothesis (`Submission/Work/FTS/EllipticEst/Prop/radialIbpWild.lean`);
* `Work.FTS.EllipticEst.Prop.angIbpWild` — **PROVED**, the angular IBP with the weight `sin(2θ)^p`,
  `p < 1`, and the endpoint flux as an explicit hypothesis
  (`Submission/Work/FTS/EllipticEst/Prop/angIbpWild.lean`; reviewed twice as correct);
* the *naive* hope that the two endpoint fluxes vanish under the target's hypotheses is **refuted**
  (notes file §5: counterexamples `g ≡ 1`, and bump families of height `x_n^{(1-p)/2}` at `x_n ↓ 0`), so
  the two identities cannot simply be applied slicewise;
* the remaining work is therefore the *case analysis* of the slices whose angular flux fails to vanish
  (flat/spiky slices: there the `cot²`-slot — hence the identity's slack term — degenerates, while the
  left-hand side is small) plus the `∫⁻`-level (junk-free) bookkeeping — see the notes file.

The two lemmas proved below are the elementary inputs of the final assembly (the weight comparison and
the weighted AM–GM closing step).
-/

namespace Work.FTS.EllipticEst.Prop

open scoped Real Topology
open MeasureTheory Filter






end Work.FTS.EllipticEst.Prop
end
-- ===== merged: Submission.Work.FTS.EllipticEst.RPFresh.InterpState =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.RPFresh

set_option autoImplicit false


end Work.FTS.EllipticEst.RPFresh
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.Psi_slice_sinCos2_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular slices of a weak-class datum are `L¹` against `sin θ cos²θ`

For a datum of Elgindi's weak elliptic hypothesis class `EllWeakPos α k F Ψ` (`k ≥ 1`) and every
`z > 0`, the angular slice `θ ↦ Ψ z θ` is integrable against the angular weight `sin θ cos²θ`:

  `∫_{Iθ} |Ψ z θ| sin θ cos²θ dθ < ∞`.

The mathematical content is a one-dimensional bootstrap from the *only* `θ`-derivative control
that the hypothesis class provides, namely the honesty (`ℋ^k`-membership) of `∂_θθΨ`:

* `ℋ^k`-membership of `∂_θθΨ` gives `(∂_θθΨ)² sin(2θ)^{-η} ∈ L¹(Iθ)` (the `i = 0` summand of the
  `ℋ^k`-integrand is `(∂_θθΨ · w/sin(2θ)^{η/2})²`, and the weight is separated by a constant);
* the interval `Iθ` is bounded, so `f'' ∈ L¹(Iθ)` (Cauchy–Schwarz against `1`);
* a `C²` function on `(0, π/2)` with `f'' ∈ L¹` is bounded on `(0, π/2)` (two applications of the
  fundamental theorem of calculus).  The Dirichlet data `Ψ z 0 = Ψ z (π/2) = 0` extend the bound
  to the closed interval, and a bounded function is integrable against the bounded weight
  `sin θ cos²θ` on the finite interval `Iθ`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## Elementary angular facts -/

/-- `sin (2θ)` is nonnegative on the closed angular interval. -/
private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin (2θ)` is positive on the open angular interval. -/
private lemma sin_two_pos_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private lemma measurableSet_Iθ_prv : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact measurableSet_Icc

/-! ## A `C²` slice with integrable second derivative is bounded -/

/-- Fundamental theorem of calculus bound: the integral of `g` over a subinterval of `Iθ` is
bounded by the integral of `|g|` over the whole of `Iθ`. -/
private lemma intervalIntegral_abs_le_setIntegral {g : ℝ → ℝ}
    (hg : IntervalIntegrable (fun x => |g x|) volume 0 (π / 2)) {a b : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ π / 2) (hb : 0 ≤ b) (hb' : b ≤ π / 2) :
    |∫ x in a..b, g x| ≤ ∫ x in Work.Spaces.Iθ, |g x| := by
  have hle : (0 : ℝ) ≤ π / 2 := by linarith [Real.pi_pos]
  have hIeq : (∫ x in (0 : ℝ)..(π / 2), |g x|) = ∫ x in Work.Spaces.Iθ, |g x| := by
    rw [intervalIntegral.integral_of_le hle, Work.Spaces.Iθ,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rcases le_total a b with hab | hba
  · have h1 : |∫ x in a..b, g x| ≤ ∫ x in a..b, |g x| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    have h2 : (∫ x in a..b, |g x|) ≤ ∫ x in Work.Spaces.Iθ, |g x| := by
      rw [← hIeq]
      exact intervalIntegral.integral_mono_interval ha hab hb'
        (Eventually.of_forall (fun x => abs_nonneg _)) hg
    linarith
  · have hsym : (∫ x in a..b, g x) = -(∫ x in b..a, g x) := intervalIntegral.integral_symm b a
    have h1 : |∫ x in b..a, g x| ≤ ∫ x in b..a, |g x| :=
      intervalIntegral.abs_integral_le_integral_abs hba
    have h2 : (∫ x in b..a, |g x|) ≤ ∫ x in Work.Spaces.Iθ, |g x| := by
      rw [← hIeq]
      exact intervalIntegral.integral_mono_interval hb hba ha'
        (Eventually.of_forall (fun x => abs_nonneg _)) hg
    rw [hsym, abs_neg]
    linarith

/-- **A `C²` function on the open angular interval whose second derivative is integrable is
bounded.**

`f'' ∈ L¹(0, π/2)` is integrated twice by the fundamental theorem of calculus: `f'` is the sum of
its value at the midpoint `π/4` and `∫ f''`, hence bounded by `|f'(π/4)| + ∫_{Iθ}|f''|`, and then
`f` is bounded by `|f(π/4)| + (π/2)·(|f'(π/4)| + ∫_{Iθ}|f''|)`. -/
private lemma bdd_of_integrableOn_abs_second_deriv {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (π / 2)))
    (hg : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (π / 2)))
    (hint : MeasureTheory.IntegrableOn (fun θ : ℝ => |deriv (deriv f) θ|) Work.Spaces.Iθ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ C := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hle_half : (0 : ℝ) ≤ π / 2 := by linarith
  set θ₀ : ℝ := π / 4 with hθ₀def
  have hθ₀mem : θ₀ ∈ Set.Ioo (0 : ℝ) (π / 2) :=
    ⟨by rw [hθ₀def]; linarith, by rw [hθ₀def]; linarith⟩
  -- the second derivative is interval integrable over `Iθ`
  have hgi : IntervalIntegrable (fun x => |deriv (deriv f) x|) volume 0 (π / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle_half]
    exact hint
  -- the total mass of `|f''|`
  set M : ℝ := ∫ x in Work.Spaces.Iθ, |deriv (deriv f) x| with hMdef
  have hMnn : 0 ≤ M := integral_nonneg fun x => abs_nonneg (deriv (deriv f) x)
  -- the subinterval `uIcc θ₀ θ` lies inside the open angular interval
  have hsub : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), Set.uIcc θ₀ θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
    intro θ hθ x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hθ₀mem.1 h1, lt_of_le_of_lt h2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 hθ₀mem.2⟩
  -- (1) the first derivative is bounded
  have hbound_deriv : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |deriv f θ| ≤ |deriv f θ₀| + M := by
    intro θ hθ
    have hFTC : (∫ x in θ₀..θ, deriv (deriv f) x) = deriv f θ - deriv f θ₀ :=
      intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hg.mono (hsub θ hθ))
    have hstep : |deriv f θ - deriv f θ₀| ≤ M := by
      rw [← hFTC]
      exact intervalIntegral_abs_le_setIntegral hgi (le_of_lt hθ₀mem.1) (le_of_lt hθ₀mem.2)
        (le_of_lt hθ.1) (le_of_lt hθ.2)
    calc |deriv f θ| = |deriv f θ₀ + (deriv f θ - deriv f θ₀)| := by ring_nf
      _ ≤ |deriv f θ₀| + |deriv f θ - deriv f θ₀| := abs_add_le _ _
      _ ≤ |deriv f θ₀| + M := by linarith
  -- (2) the function itself is bounded
  have hbound_f : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |f θ| ≤ |f θ₀| + (|deriv f θ₀| + M) * (π / 2) := by
    intro θ hθ
    have hFTC : (∫ x in θ₀..θ, deriv f x) = f θ - f θ₀ :=
      intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hf.mono (hsub θ hθ))
    have hc0 : 0 ≤ |deriv f θ₀| + M := by positivity
    have huo : Set.uIoc θ₀ θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
      intro x hx
      rw [Set.uIoc, Set.mem_Ioc] at hx
      obtain ⟨hx1, hx2⟩ := hx
      exact ⟨lt_trans (lt_min hθ₀mem.1 hθ.1) hx1,
        lt_of_le_of_lt hx2 (max_lt hθ₀mem.2 hθ.2)⟩
    have hnb : ‖∫ x in θ₀..θ, deriv f x‖ ≤ (|deriv f θ₀| + M) * |θ - θ₀| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (fun x hx => by
          rw [Real.norm_eq_abs]
          exact hbound_deriv x (huo hx))
    have hdist : |θ - θ₀| ≤ π / 2 := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith [hθ.2, hθ₀mem.1], by linarith [hθ₀mem.2, hθ.1]⟩
    have hstep : ‖∫ x in θ₀..θ, deriv f x‖ ≤ (|deriv f θ₀| + M) * (π / 2) :=
      le_trans hnb (mul_le_mul_of_nonneg_left hdist hc0)
    rw [Real.norm_eq_abs] at hstep
    calc |f θ| = |f θ₀ + (f θ - f θ₀)| := by ring_nf
      _ ≤ |f θ₀| + |f θ - f θ₀| := abs_add_le _ _
      _ = |f θ₀| + |∫ x in θ₀..θ, deriv f x| := by rw [hFTC]
      _ ≤ |f θ₀| + (|deriv f θ₀| + M) * (π / 2) := by linarith
  exact ⟨|f θ₀| + (|deriv f θ₀| + M) * (π / 2),
    by positivity, fun θ hθ => hbound_f θ hθ⟩

/-! ## The weighted square of `∂_θθΨ` is integrable -/

/-- The `i = 0` summand of the `ℋ^k`-integrand of `f` is the weighted square of `f` up to the
constant `(w z)²` on the slice. -/
private lemma weighted_sq_conv {w f s η : ℝ} (hw : w ≠ 0) (hs : 0 < s) :
    (w ^ 2)⁻¹ * (f * (w / s ^ (η / 2))) ^ 2 = f ^ 2 * s ^ (-η) := by
  have hsnn : 0 ≤ s := le_of_lt hs
  have hpow : (s ^ (η / 2)) ^ 2 = s ^ η := by
    rw [← Real.rpow_natCast (s ^ (η / 2)) 2, ← Real.rpow_mul hsnn]
    congr 1
    ring
  have h2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw
  have hsη : s ^ η ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hs η)
  rw [mul_pow, div_pow, hpow, div_eq_mul_inv, Real.rpow_neg hsnn]
  field_simp

/-- **The weighted square of the second angular derivative is integrable on every slice.**

The hypothesis `EllWeakPos α k F Ψ` contains the honesty of `∂_θθΨ` in `ℋ^k`; the `i = 0` summand
of its `ℋ^k`-integrand is `(∂_θθΨ · w/sin(2θ)^{η/2})²`, which differs from
`(∂_θθΨ)² sin(2θ)^{-η}` by the constant `(w z)²` on the slice `z`. -/
private lemma pthIter2_weighted_sq_integrable {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  intro z hz
  have hso : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth).pth.pth
  -- the `ℋ^k`-integrand of `∂_θθΨ` is integrable on the slice
  have hslice : MeasureTheory.Integrable (fun θ : ℝ =>
      Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 Ψ) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    h.memB.1 z (by rw [Work.Spaces.Iz]; exact le_of_lt hz)
  -- hence so is the `i = 0` summand
  have hsummand : MeasureTheory.Integrable (fun θ : ℝ =>
      (Work.Spaces.pthIter 2 Ψ z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' hslice ?_ ?_
    · have hcont : ContinuousOn (fun p : ℝ × ℝ =>
          Work.Spaces.pthIter 2 Ψ p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)))
          Work.FTS.EllipticEst.Q0 :=
        hso.continuousOn.mul Work.FTS.EllipticEst.continuousOn_wdivsin_Q0
      exact (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz).pow 2
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Iθ_prv]
      exact Eventually.of_forall fun θ _ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.pthIter 2 Ψ) z θ 0 (Nat.zero_le k)
  -- separate the constant `(w z)²` from the weight
  refine (hsummand.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  exact weighted_sq_conv (by rw [Work.Spaces.w]; positivity) (sin_two_pos_of_Ioo hθ)

/-! ## An `L²`-function on the finite interval `Iθ` is `L¹` -/

/-- **On the bounded interval `Iθ`, a square-integrable function is integrable.**

With the weight `sin(2θ)^{-η} ≥ 1` (for `η ≥ 0`, away from the two endpoints) the weighted square
integral dominates `∫ f²`, and `|f| ≤ (f² + 1)/2` gives `∫|f| < ∞`. -/
private lemma abs_integrableOn_of_weighted_sq {η : ℝ} (hη : 0 ≤ η) {f : ℝ → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => |f θ|) Work.Spaces.Iθ := by
  -- the unweighted square is integrable
  have hsqi : MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' h (hf.pow 2) ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hspos : 0 < Real.sin (2 * θ) := sin_two_pos_of_Ioo hθ
    have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hsηpos : 0 < (Real.sin (2 * θ)) ^ η := Real.rpow_pos_of_pos hspos η
    have hsηle : (Real.sin (2 * θ)) ^ η ≤ 1 :=
      Real.rpow_le_one (le_of_lt hspos) hsin1 hη
    have hw : 1 ≤ (Real.sin (2 * θ)) ^ (-η) := by
      rw [Real.rpow_neg (le_of_lt hspos), inv_eq_one_div, le_div_iff₀ hsηpos]
      simpa using hsηle
    exact le_mul_of_one_le_right (sq_nonneg _) hw
  -- `|f| ≤ (f² + 1)/2`
  have hvol : (MeasureTheory.volume : Measure ℝ) Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hdom : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (1 / 2) * (f θ) ^ 2 + (1 / 2) * 1) Work.Spaces.Iθ :=
    (hsqi.const_mul (1 / 2)).add
      ((MeasureTheory.integrableOn_const (C := (1 : ℝ)) hvol).const_mul (1 / 2))
  refine (MeasureTheory.Integrable.mono' hdom hf ?_).abs
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Iθ_prv (fun θ _ => ?_)
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|f θ| - 1), sq_abs (f θ), abs_nonneg (f θ)]

/-! ## The main theorem -/

theorem Psi_slice_sinCos2_integrable {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 1 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => |Ψ z θ| * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  intro z hz
  have hso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- the second angular derivative of the slice is a.e. strongly measurable
  have hpth2_aesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.pthIter 2 Ψ z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 Ψ p.1 p.2) (hso.pth.pth).continuousOn hz
  -- the second derivative of the slice is integrable
  have hL1 : MeasureTheory.IntegrableOn (fun θ : ℝ => |Work.Spaces.pthIter 2 Ψ z θ|)
      Work.Spaces.Iθ :=
    abs_integrableOn_of_weighted_sq Work.Spaces.eta_nonneg hpth2_aesm
      (pthIter2_weighted_sq_integrable h z hz)
  -- rewrite in terms of `deriv (deriv ·)`
  have hderiv_eq : ∀ θ : ℝ,
      deriv (deriv (fun t : ℝ => Ψ z t)) θ = Work.Spaces.pthIter 2 Ψ z θ := by
    intro θ
    simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  have hL1' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => |deriv (deriv (fun t : ℝ => Ψ z t)) θ|) Work.Spaces.Iθ :=
    hL1.congr_fun (fun θ _ => by rw [hderiv_eq θ]) measurableSet_Iθ_prv
  -- the slice is `C¹` together with its derivative
  have hf1 : ContDiffOn ℝ 1 (fun θ : ℝ => Ψ z θ) (Set.Ioo 0 (π / 2)) :=
    (hso.curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])
  have hg1 : ContDiffOn ℝ 1 (deriv (fun θ : ℝ => Ψ z θ)) (Set.Ioo 0 (π / 2)) := by
    have h' : ContDiffOn ℝ 1 (fun θ : ℝ => Work.Spaces.pth Ψ z θ)
        (Set.Ioo 0 (π / 2)) :=
      ((hso.pth).curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])
    simpa only [Work.Spaces.pth] using h'
  obtain ⟨C, hCnn, hC⟩ :=
    bdd_of_integrableOn_abs_second_deriv hf1 hg1 hL1'
  -- the Dirichlet data extend the bound to the closed interval
  have hbdd : ∀ θ ∈ Work.Spaces.Iθ, |Ψ z θ| ≤ C := by
    intro θ hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · rw [← h0, h.zero z, abs_zero]; exact hCnn
    rcases eq_or_lt_of_le hθ.2 with hpi | hpi
    · rw [hpi, h.pi_half z, abs_zero]; exact hCnn
    · exact hC θ ⟨h0, hpi⟩
  -- a bounded function is integrable against the bounded weight
  have hvol : (MeasureTheory.volume : Measure ℝ) Work.Spaces.Iθ < ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  refine MeasureTheory.Integrable.mono'
    (MeasureTheory.integrableOn_const (C := C) (ne_of_lt hvol)) ?_ ?_
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => |Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2)
        Work.FTS.EllipticEst.Q0 :=
      hso.continuousOn.abs.mul
        (Continuous.continuousOn (by simp only [Work.Elliptic.sinCos2]; fun_prop :
          Continuous (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)))
    exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Iθ_prv (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_abs]
    have h1 : |Work.Elliptic.sinCos2 θ| ≤ 1 :=
      Work.FTS.EllipticEst.abs_sinCos2_le_one hθ
    have h2 : |Ψ z θ| ≤ C := hbdd θ hθ
    nlinarith [abs_nonneg (Ψ z θ), hCnn]

end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceBoxIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary auxiliary facts -/


/-- **The pointwise domination on the box.**

For `0 < a < z` and `θ ∈ Iθ`,
`|pzIter 2 Ψ z θ · sinθcos²θ| ≤ a⁻⁴ · HkIntegrand α k (z²∂_z²Ψ) z θ + 1`.

This is the combination of `abs_mul_sinCos2_le_weighted` (which absorbs the angular profile
into `(pzIter 2 Ψ · w/sin(2θ)^{η/2})² + 1`) with the single-summand bound
`sq_le_HkIntegrand_z` (applied at `i = 0` to `z²∂_z²Ψ`) and the trivial `z ≥ a`. -/
private lemma pointwise_bound {α : ℝ} {k : ℕ} {Ψ : ℝ → ℝ → ℝ} {a z θ : ℝ}
    (ha : 0 < a) (hz : a < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ|
      ≤ (a ^ 4)⁻¹ * Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ + 1 := by
  have hzpos : 0 < z := lt_trans ha hz
  have h1 := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
    (f := fun θ => Work.Spaces.pzIter 2 Ψ z θ) hzpos hθ
  have hz4 : z ^ 4 ≠ 0 := pow_ne_zero 4 (ne_of_gt hzpos)
  have h2 : (Work.Spaces.pzIter 2 Ψ z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (z ^ 4)⁻¹ * ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [eq_inv_mul_iff_mul_eq₀ hz4]
    ring
  have h3 : (Work.Spaces.HkIntegrand α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ≥
      ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    have hh := Work.Spaces.sq_le_HkIntegrand_z α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ 0 (Nat.zero_le k)
    simpa using hh
  have hcinv : (0 : ℝ) ≤ (a ^ 4)⁻¹ := by positivity
  have hzipow : (z ^ 4)⁻¹ ≤ (a ^ 4)⁻¹ := by
    rw [inv_le_inv₀ (show (0 : ℝ) < z ^ 4 by positivity)
      (show (0 : ℝ) < a ^ 4 by positivity)]
    exact pow_le_pow_left₀ ha.le hz.le 4
  have hX : (0 : ℝ) ≤ ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := sq_nonneg _
  calc |Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ|
      ≤ (Work.Spaces.pzIter 2 Ψ z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := h1
    _ = (z ^ 4)⁻¹ * ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
        rw [h2]
    _ ≤ (a ^ 4)⁻¹ * ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
        have hstep := mul_le_mul_of_nonneg_right hzipow hX
        linarith
    _ ≤ (a ^ 4)⁻¹ * Work.Spaces.HkIntegrand α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ + 1 := by
        have hstep := mul_le_mul_of_nonneg_left h3 hcinv
        linarith

/-! ## The main lemma -/


end

end Work.FTS.EllipticEst.remov.SourceBound
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.pzIter2WeightedSqIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# Honesty of the angular slice `θ ↦ (∂_z²Ψ)² · sin(2θ)^{-η}`

For a datum of the weak hypothesis class `Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ` with
`k ≥ 1`, the angular slice `θ ↦ (∂_z²Ψ z θ)² sin(2θ)^{-η}` is integrable over `Iθ` for every
`z > 0`.

The proof is a direct consequence of the honesty hypothesis
`Work.Spaces.HkMem α k (fun z θ => z² ∂_z²Ψ z θ)` carried by the class: the `i = 0` term of the
first (`D_z`-)sum of `Work.Spaces.HkIntegrand` is the square
`(z²∂_z²Ψ · w z / sin(2θ)^{η/2})²`, which dominates `z⁴ w z² · (∂_z²Ψ)² sin(2θ)^{-η}`
(`Work.FTS.EllipticEst.mul_w_sin_rpow_sq`), and it is integrable on the slice by
`Work.FTS.EllipticEst.integrableOn_zSummand`.  Since `z⁴ w z² ≠ 0` for `z > 0`, the
corresponding factor can be divided out.
-/

/-- **Honesty of a single weighted `z`-slice.**  If `G` is `C^∞` on the open quadrant and
`HkMem α k G`, then for every `z > 0` the angular slice `θ ↦ (G z θ)² sin(2θ)^{-η}` is
integrable over `Iθ`.

The `i = 0` summand of `HkIntegrand` is `(G z θ · w z / sin(2θ)^{η/2})²`, which equals
`(w z)² · (G z θ)² sin(2θ)^{-η}` on `Iθ` (`Work.FTS.EllipticEst.mul_w_sin_rpow_sq`); it is
integrable by `Work.FTS.EllipticEst.integrableOn_zSummand`, and the factor `(w z)²` is nonzero
for `z > 0`. -/
private theorem integrable_sq_rpow_of_HkMem {α : ℝ} {k : ℕ} {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen G) (hmem : Work.Spaces.HkMem α k G)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.Integrable
      (fun θ : ℝ => (G z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hw : Work.Spaces.w z ≠ 0 := by rw [Work.Spaces.w]; positivity
  have hkey : ∀ θ ∈ Work.Spaces.Iθ,
      ((Work.Spaces.w z) ^ 2)⁻¹
          * (G z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (G z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    intro θ hθ
    rw [Work.FTS.EllipticEst.mul_w_sin_rpow_sq (G z θ) (Work.Spaces.w z) hθ]
    field_simp
  have hint := Work.FTS.EllipticEst.integrableOn_zSummand α k hG hmem 0 (Nat.zero_le k) hzIz
  have hI2 : MeasureTheory.Integrable
      (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹
        * (G z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hint.const_mul _
  refine hI2.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  exact hkey θ hθ

theorem pzIter2WeightedSqIntegrable {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z : ℝ, 0 < z → MeasureTheory.Integrable
      (fun θ : ℝ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  intro z hz
  have hz' : z ≠ 0 := ne_of_gt hz
  have hA : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hGs : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
    rw [Work.FTS.EllipticEst.SmoothOpen]
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => p.1 ^ 2) Work.FTS.EllipticEst.Q0 :=
      contDiffOn_fst.pow 2
    have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 Ψ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
      hA.pzIter 2
    exact h1.mul h2
  have key : MeasureTheory.Integrable
      (fun θ : ℝ => ((fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    integrable_sq_rpow_of_HkMem hGs h.memA hz
  refine (key.const_mul (((z ^ 2) ^ 2)⁻¹)).congr ?_
  filter_upwards with θ
  rw [mul_pow, ← mul_assoc,
    inv_mul_cancel_left₀ (pow_ne_zero 2 (pow_ne_zero 2 hz'))]

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.ws_DzIter_three_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology



end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EpsEngine.ZTracesAux.hasDerivAt_zTraces_phi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.FTS.EpsEngine.ZTracesAux

theorem hasDerivAt_zTraces_phi {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (b a : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∀ z : ℝ, 0 < z → HasDerivAt
      (fun z' : ℝ => z' * (Work.Spaces.mixed b a f z' θ * Work.Spaces.w z') ^ 2)
      ((Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2
        + 2 * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z)
          * (Work.Spaces.w z * (Work.Spaces.mixed (b + 1) a f z θ
              - 2 * Work.Spaces.mixed b a f z θ / (1 + z)))) z := by
  intro z hz
  have hz0 : z ≠ 0 := ne_of_gt hz
  -- the `z`-derivative of the slice `z' ↦ D_z^b D_θ^a f z' θ` (an interior angle)
  have hslice : HasDerivAt (fun z' : ℝ => Work.Spaces.mixed b a f z' θ)
      (Work.Spaces.pz (Work.Spaces.mixed b a f) z θ) z :=
    (hf.mixed b a).hasDerivAt_slice hθ hz
  -- product rule with the weight, then the square, then the outer factor `z'`
  have hprod := hslice.mul (hasDerivAt_w z hz0)
  have hsq := hprod.pow 2
  have hmain := (hasDerivAt_id z).mul hsq
  refine hmain.congr_deriv ?_
  have hmix : Work.Spaces.mixed (b + 1) a f z θ
      = z * Work.Spaces.pz (Work.Spaces.mixed b a f) z θ := rfl
  simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
  rw [hmix]
  norm_num
  simp only [Work.Spaces.w]
  field_simp
  ring

end Work.FTS.EpsEngine.ZTracesAux
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.tendsto_HkIntegrand_indicator_theta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc



end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.tendsto_HkIntegrand_indicator_z =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.GalBasis.cc


end Work.FTS.GalBasis.cc
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.wwBasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## 1. Elementary angular facts -/

/-- Jordan's inequality in the shape used below: `4θ/π ≤ sin (2θ)` for `θ ∈ [0,π/4]`. -/
lemma four_div_pi_mul_le_sin_two {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 4) :
    4 / Real.pi * θ ≤ Real.sin (2 * θ) := by
  have h := Real.mul_le_sin (x := 2 * θ) (by linarith) (by linarith)
  have h2 : 2 / Real.pi * (2 * θ) = 4 / Real.pi * θ := by ring
  linarith [h, h2]

lemma sin_two_pos {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

/-- `(s^{-γ/2})^2 = s^{-γ}` for `s > 0`. -/
lemma sq_rpow_neg_half {s γ : ℝ} (hs : 0 < s) : (s ^ (-(γ / 2))) ^ 2 = s ^ (-γ) := by
  rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hs)]
  congr 1
  ring

/-- `(s^{(γ-2)/2})^2 = s^{γ-2}` for `s > 0`. -/
lemma sq_rpow_half {s γ : ℝ} (hs : 0 < s) : (s ^ ((γ - 2) / 2)) ^ 2 = s ^ (γ - 2) := by
  rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hs)]
  congr 1
  ring



/-! ## 2. The derivative of a `θ`-slice of `D_z^b f` -/



/-! ## 3. Extracting the slice from its derivative -/


/-! ## 4. Integrability of the Hardy weight `sin(2θ)^{γ-2}` -/


/-! ## 5. The sharp per-slice bound -/



end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.H2.WPQ.Pointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.WPQ

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.Spaces


end Work.FTS.H2.WPQ
end
end
-- ===== merged: Submission.Work.FTS.LocData.hLoc_hk =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The `ℋ⁴`-derivatives of the separated bump `bumpZ z · Γ(θ)` -/





/-! ## `rpow` bookkeeping and the two "separated square" identities -/

/-- `(b / s^e)² = b²·s^{-2e}`, valid for `s ≥ 0` (both sides vanish at `s = 0`). -/
theorem div_rpow_sq (b s e : ℝ) (hs : 0 ≤ s) : (b / s ^ e) ^ 2 = b ^ 2 * s ^ (-(2 * e)) := by
  rw [div_pow, div_eq_mul_inv]
  have h : (s ^ e) ^ 2 = s ^ (2 * e) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    ring_nf
  rw [h, ← Real.rpow_neg hs]

/-- The square of a `D_z`-summand factorises into its radial and angular blocks. -/
theorem sep_sq1 (B G w s e : ℝ) (hs : 0 ≤ s) :
    (B * G * (w / s ^ (e / 2))) ^ 2 = (B * w) ^ 2 * (G ^ 2 * s ^ (-e)) := by
  rw [show B * G * (w / s ^ (e / 2)) = B * G * w / s ^ (e / 2) by ring, div_rpow_sq _ _ _ hs]
  rw [show -(2 * (e / 2)) = -e by ring]
  ring

/-- The square of a mixed-summand factorises into its radial and angular blocks. -/
theorem sep_sq2 (B G w s g : ℝ) (hs : 0 ≤ s) :
    (B * G * (w * s ^ (-(g / 2)))) ^ 2 = (B * w) ^ 2 * (G ^ 2 * s ^ (-g)) := by
  rw [show B * G * (w * s ^ (-(g / 2))) = (B * G * w) * s ^ (-(g / 2)) by ring, mul_pow]
  rw [show (s ^ (-(g / 2))) ^ 2 = s ^ (-g) from by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]; congr 1; ring]
  ring

/-! ## Angular bounds -/

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  apply Real.sin_nonneg_of_mem_Icc
  exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- The `η`-summand of `angMaj`. -/
theorem Gam_sq_rpow_le_angMaj_eta (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ≤ angMaj α θ := by
  have hs0 := sin_two_nonneg hθ
  rw [angMaj_apply]
  have h1 : 0 ≤ Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  linarith

/-- The `γ`-summand of `angMaj`. -/
theorem Gam_sq_rpow_le_angMaj_gam (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ angMaj α θ := by
  have hs0 := sin_two_nonneg hθ
  rw [angMaj_apply]
  have h1 : 0 ≤ Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  linarith


/-! ## The radial weight on the support of the bump -/


/-! ## The two per-summand bounds -/



/-! ## The pointwise bound on the `ℋ⁴`-integrand of the bump -/


/-! ## Integrability of the majorant -/


/-! ## Membership in `𝓗⁴` -/


/-! ## The `𝓗⁴`-norm of the bump is finite -/


/-! ## The target -/


end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.BumpDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The definitions -/

/-- The smooth cut-off `z ↦ st (z - 1/2) · st (1 - z)`, supported on `[1/2,1]`. -/
def zCut (z : ℝ) : ℝ :=
  Real.smoothTransition (z - (1 / 2 : ℝ)) * Real.smoothTransition (1 - z)

/-- The smooth cut-off `θ ↦ st (θ - π/4) · st (3π/8 - θ)`, supported on `[π/4,3π/8]`. -/
def thCut (θ : ℝ) : ℝ :=
  Real.smoothTransition (θ - Real.pi / 4) *
    Real.smoothTransition (3 * Real.pi / 8 - θ)

/-- The bump profile `bump z θ = zCut z · thCut θ`, supported on `[1/2,1] × [π/4,3π/8]`. -/
def bump (z θ : ℝ) : ℝ := zCut z * thCut θ


/-! ## The two cut-offs -/


theorem zCut_nonneg (z : ℝ) : 0 ≤ zCut z :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem zCut_eq_zero_iff {z : ℝ} : zCut z = 0 ↔ z ≤ 1 / 2 ∨ 1 ≤ z := by
  rw [zCut, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl (by rw [Real.smoothTransition.zero_iff_nonpos] at h; linarith)
    · exact Or.inr (by rw [Real.smoothTransition.zero_iff_nonpos] at h; linarith)
  · rintro (h | h)
    · exact Or.inl (Real.smoothTransition.zero_of_nonpos (by linarith))
    · exact Or.inr (Real.smoothTransition.zero_of_nonpos (by linarith))

theorem zCut_pos_iff {z : ℝ} : 0 < zCut z ↔ z ∈ Set.Ioo (1 / 2) 1 := by
  rw [Set.mem_Ioo]
  constructor
  · intro h
    have hne : ¬ (z ≤ 1 / 2 ∨ 1 ≤ z) := fun hh => (ne_of_gt h) (zCut_eq_zero_iff.mpr hh)
    rcases not_or.mp hne with ⟨h1, h2⟩
    exact ⟨not_le.mp h1, not_le.mp h2⟩
  · rintro ⟨h1, h2⟩
    refine lt_of_le_of_ne (zCut_nonneg z) (Ne.symm fun hh => ?_)
    rcases zCut_eq_zero_iff.mp hh with h | h <;> linarith

theorem thCut_nonneg (θ : ℝ) : 0 ≤ thCut θ :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem thCut_eq_zero_iff {θ : ℝ} :
    thCut θ = 0 ↔ θ ≤ Real.pi / 4 ∨ 3 * Real.pi / 8 ≤ θ := by
  rw [thCut, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl (by rw [Real.smoothTransition.zero_iff_nonpos] at h; linarith)
    · exact Or.inr (by rw [Real.smoothTransition.zero_iff_nonpos] at h; linarith)
  · rintro (h | h)
    · exact Or.inl (Real.smoothTransition.zero_of_nonpos (by linarith))
    · exact Or.inr (Real.smoothTransition.zero_of_nonpos (by linarith))

theorem thCut_pos_iff {θ : ℝ} :
    0 < thCut θ ↔ θ ∈ Set.Ioo (Real.pi / 4) (3 * Real.pi / 8) := by
  rw [Set.mem_Ioo]
  constructor
  · intro h
    have hne : ¬ (θ ≤ Real.pi / 4 ∨ 3 * Real.pi / 8 ≤ θ) :=
      fun hh => (ne_of_gt h) (thCut_eq_zero_iff.mpr hh)
    rcases not_or.mp hne with ⟨h1, h2⟩
    exact ⟨not_le.mp h1, not_le.mp h2⟩
  · rintro ⟨h1, h2⟩
    refine lt_of_le_of_ne (thCut_nonneg θ) (Ne.symm fun hh => ?_)
    rcases thCut_eq_zero_iff.mp hh with h | h <;> linarith

/-! ## The bump profile -/

theorem bump_nonneg (z θ : ℝ) : 0 ≤ bump z θ :=
  mul_nonneg (zCut_nonneg z) (thCut_nonneg θ)

theorem bump_eq_zero_iff {z θ : ℝ} :
    bump z θ = 0 ↔ z ≤ 1 / 2 ∨ 1 ≤ z ∨ θ ≤ Real.pi / 4 ∨ 3 * Real.pi / 8 ≤ θ := by
  rw [bump, mul_eq_zero, zCut_eq_zero_iff, thCut_eq_zero_iff]
  tauto

theorem bump_pos_iff {z θ : ℝ} :
    0 < bump z θ ↔
      z ∈ Set.Ioo (1 / 2) 1 ∧ θ ∈ Set.Ioo (Real.pi / 4) (3 * Real.pi / 8) := by
  rw [show bump z θ = zCut z * thCut θ from rfl]
  constructor
  · intro h
    rcases mul_pos_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨zCut_pos_iff.mp h1, thCut_pos_iff.mp h2⟩
    · exfalso
      have hnn := zCut_nonneg z
      linarith
  · rintro ⟨h1, h2⟩
    exact mul_pos (zCut_pos_iff.mpr h1) (thCut_pos_iff.mpr h2)

theorem bump_ne_zero_iff {z θ : ℝ} :
    bump z θ ≠ 0 ↔
      z ∈ Set.Ioo (1 / 2) 1 ∧ θ ∈ Set.Ioo (Real.pi / 4) (3 * Real.pi / 8) := by
  rw [← bump_pos_iff]
  exact ⟨fun h => lt_of_le_of_ne (bump_nonneg z θ) (Ne.symm h), ne_of_gt⟩

/-- **Support condition**: where `bump` is nonzero both coordinates lie in the open intervals
demanded by the statement of `exists_smooth_supported_HkSq_gt`. -/
theorem bump_support {z θ : ℝ} (h : bump z θ ≠ 0) :
    z ∈ Set.Ioo (1 / 2) 1 ∧ θ ∈ Set.Ioo (Real.pi / 8) (Real.pi / 2) := by
  rw [bump_ne_zero_iff] at h
  exact ⟨h.1, by constructor <;> linarith [h.2.1, h.2.2, Real.pi_pos]⟩

/-! ## Smoothness -/

theorem contDiff_zCut (n : ℕ) : ContDiff ℝ n zCut := by
  have h1 : ContDiff ℝ n (fun z : ℝ => z - (1 / 2 : ℝ)) := contDiff_id.sub contDiff_const
  have h2 : ContDiff ℝ n (fun z : ℝ => (1 : ℝ) - z) := contDiff_const.sub contDiff_id
  exact (Real.smoothTransition.contDiff.comp h1).mul (Real.smoothTransition.contDiff.comp h2)

theorem contDiff_thCut (n : ℕ) : ContDiff ℝ n thCut := by
  have h1 : ContDiff ℝ n (fun θ : ℝ => θ - Real.pi / 4) := contDiff_id.sub contDiff_const
  have h2 : ContDiff ℝ n (fun θ : ℝ => 3 * Real.pi / 8 - θ) := contDiff_const.sub contDiff_id
  exact (Real.smoothTransition.contDiff.comp h1).mul (Real.smoothTransition.contDiff.comp h2)

theorem contDiff_bump (n : ℕ) : ContDiff ℝ n (fun p : ℝ × ℝ => bump p.1 p.2) := by
  have hz : ContDiff ℝ n (fun p : ℝ × ℝ => zCut p.1) := (contDiff_zCut n).comp contDiff_fst
  have hθ : ContDiff ℝ n (fun p : ℝ × ℝ => thCut p.2) := (contDiff_thCut n).comp contDiff_snd
  exact hz.mul hθ

/-- `bump` is `C^∞` on the open quadrant (indeed everywhere). -/
theorem smoothOpen_bump : Work.FTS.EllipticEst.SmoothOpen bump :=
  (Work.FTS.EllipticEst.smoothOpen_iff_forall bump).mpr
    (fun n => (contDiff_bump n).contDiffOn)

/-- Joint continuity of the `ℋ^k`-integrand of `bump` on the open quadrant. -/
theorem continuousOn_HkIntegrand_bump (α : ℝ) (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k bump p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
  smoothOpen_bump.continuousOn_HkIntegrand α k

/-! ## Vanishing of the iterated derivatives off a neighbourhood of the support

The tool is the general Lemma `vanishOn_mixed` below: a function which vanishes on `V ×ˢ W`
(with `V`, `W` open) has all its iterated mixed derivatives vanishing there as well.  Applying
it to `bump` on the four half-plane pieces complementary to `[1/2,1] × [π/4,3π/8]` gives the
vanishing of the whole `ℋ^k`-integrand outside that closed box. -/

theorem vanishOn_pz {g : ℝ → ℝ → ℝ} {V W : Set ℝ} (hV : IsOpen V) (hW : IsOpen W)
    (h : ∀ z' ∈ V, ∀ θ' ∈ W, g z' θ' = 0) :
    ∀ z' ∈ V, ∀ θ' ∈ W, Work.Spaces.pz g z' θ' = 0 := by
  intro z' hz' θ' hθ'
  have he : (fun z'' : ℝ => g z'' θ') =ᶠ[𝓝 z'] fun _ => (0 : ℝ) := by
    filter_upwards [hV.mem_nhds hz'] with z'' hz''
    exact h z'' hz'' θ' hθ'
  simp only [Work.Spaces.pz]
  rw [he.deriv_eq, deriv_const]

theorem vanishOn_pth {g : ℝ → ℝ → ℝ} {V W : Set ℝ} (hV : IsOpen V) (hW : IsOpen W)
    (h : ∀ z' ∈ V, ∀ θ' ∈ W, g z' θ' = 0) :
    ∀ z' ∈ V, ∀ θ' ∈ W, Work.Spaces.pth g z' θ' = 0 := by
  intro z' hz' θ' hθ'
  have he : (fun θ'' : ℝ => g z' θ'') =ᶠ[𝓝 θ'] fun _ => (0 : ℝ) := by
    filter_upwards [hW.mem_nhds hθ'] with θ'' hθ''
    exact h z' hz' θ'' hθ''
  simp only [Work.Spaces.pth]
  rw [he.deriv_eq, deriv_const]

theorem vanishOn_DzIter {g : ℝ → ℝ → ℝ} {V W : Set ℝ} (hV : IsOpen V) (hW : IsOpen W)
    (h : ∀ z' ∈ V, ∀ θ' ∈ W, g z' θ' = 0) (j : ℕ) :
    ∀ z' ∈ V, ∀ θ' ∈ W, Work.Spaces.DzIter j g z' θ' = 0 := by
  induction j with
  | zero => exact h
  | succ j ih =>
    intro z' hz' θ' hθ'
    have hpz := vanishOn_pz hV hW ih z' hz' θ' hθ'
    rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, hpz, mul_zero]

theorem vanishOn_DthIter {g : ℝ → ℝ → ℝ} {V W : Set ℝ} (hV : IsOpen V) (hW : IsOpen W)
    (h : ∀ z' ∈ V, ∀ θ' ∈ W, g z' θ' = 0) (i : ℕ) :
    ∀ z' ∈ V, ∀ θ' ∈ W, Work.Spaces.DthIter i g z' θ' = 0 := by
  induction i with
  | zero => exact h
  | succ i ih =>
    intro z' hz' θ' hθ'
    have hpth := vanishOn_pth hV hW ih z' hz' θ' hθ'
    rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth, hpth, mul_zero]

/-- If `g` vanishes on `V ×ˢ W` with `V`, `W` open, then so does every iterated mixed
derivative `D_z^j D_θ^i g`. -/
theorem vanishOn_mixed {g : ℝ → ℝ → ℝ} {V W : Set ℝ} (hV : IsOpen V) (hW : IsOpen W)
    (h : ∀ z' ∈ V, ∀ θ' ∈ W, g z' θ' = 0) (j i : ℕ) :
    ∀ z' ∈ V, ∀ θ' ∈ W, Work.Spaces.DzIter j (Work.Spaces.DthIter i g) z' θ' = 0 :=
  vanishOn_DzIter hV hW (vanishOn_DthIter hV hW h i) j

theorem bump_zCut_eq_zero_of_lt {z : ℝ} (hz : z < 1 / 2) : zCut z = 0 := by
  rw [zCut, Real.smoothTransition.zero_of_nonpos (by linarith : z - 1 / 2 ≤ 0), zero_mul]

theorem bump_zCut_eq_zero_of_gt {z : ℝ} (hz : 1 < z) : zCut z = 0 := by
  rw [zCut, Real.smoothTransition.zero_of_nonpos (by linarith : 1 - z ≤ 0), mul_zero]

theorem bump_thCut_eq_zero_of_lt {θ : ℝ} (hθ : θ < Real.pi / 4) : thCut θ = 0 := by
  rw [thCut, Real.smoothTransition.zero_of_nonpos (by linarith : θ - Real.pi / 4 ≤ 0), zero_mul]

theorem bump_thCut_eq_zero_of_gt {θ : ℝ} (hθ : 3 * Real.pi / 8 < θ) : thCut θ = 0 := by
  rw [thCut, Real.smoothTransition.zero_of_nonpos (by linarith : 3 * Real.pi / 8 - θ ≤ 0),
    mul_zero]

/-- Every iterated mixed derivative of `bump` vanishes at `(z,θ)` as soon as `z` or `θ` lies
strictly outside the support box `[1/2,1] × [π/4,3π/8]`. -/
theorem bump_iter_eq_zero_of_not_mem {z θ : ℝ}
    (h : z < 1 / 2 ∨ 1 < z ∨ θ < Real.pi / 4 ∨ 3 * Real.pi / 8 < θ) (j i : ℕ) :
    Work.Spaces.DzIter j (Work.Spaces.DthIter i bump) z θ = 0 := by
  rcases h with hz | hz | hθ | hθ
  · exact vanishOn_mixed isOpen_Iio isOpen_univ
      (fun z' hz' θ' _ => by rw [bump, bump_zCut_eq_zero_of_lt hz', zero_mul])
      j i z hz θ (Set.mem_univ θ)
  · exact vanishOn_mixed isOpen_Ioi isOpen_univ
      (fun z' hz' θ' _ => by rw [bump, bump_zCut_eq_zero_of_gt hz', zero_mul])
      j i z hz θ (Set.mem_univ θ)
  · exact vanishOn_mixed isOpen_univ isOpen_Iio
      (fun z' _ θ' hθ' => by rw [bump, bump_thCut_eq_zero_of_lt hθ', mul_zero])
      j i z (Set.mem_univ z) θ hθ
  · exact vanishOn_mixed isOpen_univ isOpen_Ioi
      (fun z' _ θ' hθ' => by rw [bump, bump_thCut_eq_zero_of_gt hθ', mul_zero])
      j i z (Set.mem_univ z) θ hθ

/-- The `ℋ^k`-integrand of `bump` vanishes outside the closed box
`[1/2,1] × [π/4,3π/8]`. -/
theorem HkIntegrand_bump_eq_zero_of_not_mem (α : ℝ) (k : ℕ) {z θ : ℝ}
    (h : z < 1 / 2 ∨ 1 < z ∨ θ < Real.pi / 4 ∨ 3 * Real.pi / 8 < θ) :
    Work.Spaces.HkIntegrand α k bump z θ = 0 := by
  have hz := bump_iter_eq_zero_of_not_mem h
  rw [Work.Spaces.HkIntegrand]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i bump z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      rw [show Work.Spaces.DzIter i bump z θ = 0 from by
        simpa only [Work.Spaces.DthIter_zero] using hz i 0]
      ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i bump z θ * Work.Spaces.Wt α z θ) ^ 2
      else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos hc, show Work.Spaces.mixed j i bump z θ = 0 from hz j i]; ring
      · rw [if_neg hc]
  rw [h1, h2, add_zero]

/-! ## The support box, the inner box, and the corresponding subsets -/

theorem box_subset_Q0 :
    Set.Icc ((1 : ℝ) / 2) 1 ×ˢ Set.Icc (Real.pi / 4) (3 * Real.pi / 8)
      ⊆ Work.FTS.EllipticEst.Q0 := by
  rintro ⟨z, θ⟩ hp
  rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hp
  rw [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
  exact ⟨by linarith [hp.1.1], by linarith [hp.2.1, Real.pi_pos],
    by linarith [hp.2.2, Real.pi_pos]⟩

/-- The integrand of `bump` is bounded by a constant (its maximum on the compact support box);
outside the box it vanishes. -/
theorem exists_bound_HkIntegrand_bump (α : ℝ) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z θ : ℝ, Work.Spaces.HkIntegrand α k bump z θ ≤ M := by
  obtain ⟨p₀, -, hp₀max⟩ :=
    (isCompact_Icc.prod isCompact_Icc :
        IsCompact (Set.Icc ((1 : ℝ) / 2) 1 ×ˢ Set.Icc (Real.pi / 4) (3 * Real.pi / 8)))
      |>.exists_isMaxOn ⟨(3 / 4, Real.pi / 4), by
        rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
        exact ⟨⟨by norm_num, by norm_num⟩, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩⟩⟩
      ((continuousOn_HkIntegrand_bump α k).mono box_subset_Q0)
  refine ⟨Work.Spaces.HkIntegrand α k bump p₀.1 p₀.2,
    Work.Spaces.HkIntegrand_nonneg α k bump p₀.1 p₀.2, fun z θ => ?_⟩
  by_cases h : (z, θ) ∈ Set.Icc ((1 : ℝ) / 2) 1 ×ˢ Set.Icc (Real.pi / 4) (3 * Real.pi / 8)
  · exact hp₀max h
  · have h' : z < 1 / 2 ∨ 1 < z ∨ θ < Real.pi / 4 ∨ 3 * Real.pi / 8 < θ := by
      simp only [Set.mem_prod, Set.mem_Icc, not_and_or, not_le] at h
      tauto
    rw [HkIntegrand_bump_eq_zero_of_not_mem α k h']
    exact Work.Spaces.HkIntegrand_nonneg α k bump p₀.1 p₀.2

/-! ## Strict positivity on the inner box -/






end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.SlotsZeroRest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `SlotsZeroRest` — the three slots vanish along the radial Euler mode

The hypothesis

`hU : Uop α w z θ = 0` on the open quadrant, i.e. `-3 w - α z ∂_z w = 0`,

is the radial (indicial) Euler identity `z ∂_z w = -(3/α) w`: for every fixed `θ` the
`z`-slice of `w` is a multiple of `z^{-3/α}` (`SlotsZeroRepr`).  Differentiating the
representation in `θ` shows that `Vop w = ∂_θ w - tan θ · w` has exactly the same shape,
`Vop w z θ = d θ · z^{-3/α}`.  The weighted integrand of `HkIntegrand α 6 (Vop w)` contains
the level-`0` term `(Vop w · w z / sin(2θ)^{η/2})²`, which on `z ∈ (0,1)` is bounded below
by `const · d θ² sin(2θ)^{-η} z^{-2}`; a single `θ` with `d θ ≠ 0` therefore forces the
`z`-integral to diverge at `z → 0⁺` (`SlotsZeroSliceLB`), contradicting `HkMem α 6 (Vop w)`
via `Work.Coercivity.not_integrableOn_of_lower_rpow`.

Finally, on the open quadrant `Rop α w = Vop w` *identically* once `Uop α w = 0`:
the numerator of `Rop` is `2 sin θ w + sin θ · α z ∂_z w + cos θ ∂_θ w = -sin θ w + cos θ ∂_θ w`.
-/

namespace Work.FTS.StrongEps.EComparison

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## The smoothness of `Vop w` -/

private theorem contDiffOn_tan_snd :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.tan p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Real.tan p.2)
      = fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2 := by
    funext p; rw [Real.tan_eq_sin_div_cos]
  rw [hfun]
  refine ContDiffOn.div ?_ ?_ ?_
  · exact (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  · exact (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  · intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)

private theorem smoothOpen_tan_mul {w : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen w) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * w z θ) := by
  have h := contDiffOn_tan_snd.mul (show ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => w p.1 p.2) Work.FTS.EllipticEst.Q0 from hsm)
  have hgoal : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * w z θ) ↔
      ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.tan p.2 * w p.1 p.2)
        Work.FTS.EllipticEst.Q0 := Iff.rfl
  exact hgoal.mpr h

private theorem smoothOpen_Vop_prv {w : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen w) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop w) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth w) := hsm.pth
  have h2 := h1.sub (smoothOpen_tan_mul hsm)
  have hgoal : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop w) ↔
      ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => deriv (fun θ' => w p.1 θ') p.2 - Real.tan p.2 * w p.1 p.2)
        Work.FTS.EllipticEst.Q0 := Iff.rfl
  exact hgoal.mpr h2

/-! ## The `z`-profile of `w` and of `Vop w` -/

/-- From the radial Euler identity `Uop α w = 0` the `z`-slice of `w` is a multiple of
`z^{-3/α}`. -/
private theorem repr_w {α : ℝ} (hα : 0 < α) {w : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen w)
    (hU : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Uop α w z θ = 0) :
    ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), w z θ = w 1 θ * z ^ (-(3 / α)) := by
  intro z hz θ hθ
  refine SlotsZeroRepr hα (u := w) (θ := θ)
    ((hsm.curry_z hθ).differentiableOn (by simp [Work.Stability.smoothOrder])) ?_ z hz
  intro z' hz'
  have h := hU z' hz' θ hθ
  simp only [Work.Construction.Uop, Work.Spaces.pz] at h
  have hαne : α ≠ 0 := ne_of_gt hα
  have key : z' * deriv (fun z'' => w z'' θ) z' = -3 * w z' θ / α := by
    rw [eq_div_iff hαne]
    linarith [h]
  rw [key]
  ring

/-- `∂_θ` of the representation: the `θ`-derivative of `w (·,θ)` inherits the `z^{-3/α}`-factor
(the two functions agree on a neighbourhood of the interior point `θ`). -/
private theorem pth_repr {α : ℝ} {w : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen w)
    (hrep : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), w z θ = w 1 θ * z ^ (-(3 / α)))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pth w z θ = Work.Spaces.pth w 1 θ * z ^ (-(3 / α)) := by
  have h1 : (fun θ' => w z θ') =ᶠ[nhds θ] (fun θ' => w 1 θ' * z ^ (-(3 / α))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact hrep z hz θ' hθ'
  have h2 := h1.deriv_eq
  have hd : DifferentiableAt ℝ (fun θ' => w 1 θ') θ :=
    ((hsm.curry_θ (z := 1) (by norm_num)).differentiableOn
      (by simp [Work.Stability.smoothOrder])).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  have h3 : deriv (fun θ' => w 1 θ' * z ^ (-(3 / α))) θ
      = deriv (fun θ' => w 1 θ') θ * z ^ (-(3 / α)) := deriv_mul_const hd _
  show deriv (fun θ' => w z θ') θ = deriv (fun θ' => w 1 θ') θ * z ^ (-(3 / α))
  rw [h2, h3]

/-- `Vop w` inherits the `z^{-3/α}`-profile of `w`. -/
private theorem repr_Vop {α : ℝ} (hα : 0 < α) {w : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen w)
    (hU : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Uop α w z θ = 0) :
    ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Construction.Vop w z θ = Work.Construction.Vop w 1 θ * z ^ (-(3 / α)) := by
  intro z hz θ hθ
  have hrep := repr_w hα hsm hU
  have hp := pth_repr hsm hrep hz hθ
  have hw := hrep z hz θ hθ
  simp only [Work.Construction.Vop]
  rw [hp, hw]
  ring

/-! ## The `θ`-slice lower bound for the `H^k`-integrand

The whole point of the `z^{-3/α}`-profile is that the level-`0` summand of
`HkIntegrand α 6 (Vop w)` is `(d θ · z^{-3/α} · w(z)/sin(2θ)^{η/2})²`, which near `z = 0`
behaves like `z^{-6/α}·(w z)² ≥ z^{-2}`: the `θ`-integral blows up like `z^{-2}`.  The
elementary coercivity lemma `Work.Coercivity.theta_integral_lower` extracts exactly this
from the pointwise bound `δ² z² ≤ (Vop w z θ)²` on an angular interval on which `|d| ≥ δ`. -/

private theorem slice_lower_bound {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {d : ℝ → ℝ}
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo 0 (Real.pi / 2)) (hdcont : ContinuousAt d θ₀)
    (hne : d θ₀ ≠ 0)
    (hrep : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), f z θ = d θ * z ^ (-(3 / α)))
    (hHk : ∀ z, 0 < z → MeasureTheory.IntegrableOn (fun θ =>
      Work.Spaces.HkIntegrand α 6 f z θ) Work.Spaces.Iθ) :
    ∃ c : ℝ, 0 < c ∧ ∀ z, 0 < z → z < 1 →
      c / z ^ 2 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ := by
  -- the reference level `δ = |d θ₀|/2` and an angular interval on which `|d| ≥ δ`
  set δ : ℝ := |d θ₀| / 2 with hδdef
  have hδpos : 0 < δ := by
    have : 0 < |d θ₀| := abs_pos.mpr hne
    rw [hδdef]; linarith
  obtain ⟨η, hηpos, hη⟩ :=
    Metric.continuousAt_iff.mp hdcont (|d θ₀| / 2) (by
      have : 0 < |d θ₀| := abs_pos.mpr hne
      linarith)
  have hη' : ∀ θ : ℝ, |θ - θ₀| < η → δ ≤ |d θ| := by
    intro θ hθ
    have h1 : |d θ - d θ₀| < |d θ₀| / 2 := by
      have h := hη (x := θ) (by rw [Real.dist_eq]; exact hθ)
      rwa [Real.dist_eq] at h
    have h2 : |d θ₀| ≤ |d θ| + |d θ - d θ₀| := by
      have h3 : |d θ - (d θ - d θ₀)| ≤ |d θ| + |d θ - d θ₀| := abs_sub _ _
      rwa [show d θ - (d θ - d θ₀) = d θ₀ by ring] at h3
    rw [hδdef]; linarith
  -- the interval `(θ₀-ε, θ₀+ε)`, contained in `(0,π/2)` and in `{|θ-θ₀| < η}`
  set ε : ℝ := min (η / 2) (min (θ₀ / 2) ((Real.pi / 2 - θ₀) / 2)) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min (by linarith) (lt_min (by linarith [hθ₀.1]) (by linarith [hθ₀.2]))
  have hεη : ε ≤ η / 2 := le_trans (min_le_left _ _) le_rfl
  have hε1 : ε ≤ θ₀ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hε2 : ε ≤ (Real.pi / 2 - θ₀) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨δ ^ 2 * (2 * ε), by positivity, fun z hz hz1 => ?_⟩
  -- the pointwise bound `δ² z² ≤ (f z θ)²` on the interval
  have hlow : ∀ θ ∈ Set.Ioo (θ₀ - ε) (θ₀ + ε), (4 * δ) ^ 2 / 16 * z ^ 2 ≤ (f z θ) ^ 2 := by
    intro θ hθ
    have hθmem : θ ∈ Set.Ioo 0 (Real.pi / 2) :=
      ⟨by linarith [hθ.1, hε1, hθ₀.1], by linarith [hθ.2, hε2, hθ₀.2]⟩
    have hdθ : δ ≤ |d θ| := by
      refine hη' θ ?_
      rw [abs_lt]
      constructor <;> linarith [hθ.1, hθ.2, hεη, hηpos]
    have hsq : (z ^ (-(3 / α))) ^ 2 = z ^ (-(6 / α)) := by
      rw [pow_two, ← Real.rpow_add hz (-(3 / α)) (-(3 / α))]
      congr 1
      ring
    have hfe : (f z θ) ^ 2 = (d θ) ^ 2 * z ^ (-(6 / α)) := by
      rw [hrep z hz θ hθmem, mul_pow, hsq]
    have hzp : 1 ≤ z ^ (-(6 / α)) := by
      have h6 : -(6 / α) ≤ 0 := by
        have : 0 < 6 / α := by positivity
        linarith
      have h := Real.rpow_le_rpow_of_nonpos hz (by linarith : z ≤ 1) h6
      simpa using h
    have hz2 : z ^ 2 ≤ 1 := by nlinarith
    have hd2 : δ ^ 2 ≤ (d θ) ^ 2 := by
      have h1 : δ ^ 2 ≤ |d θ| ^ 2 := by
        have := abs_nonneg (d θ)
        nlinarith [hdθ, hδpos]
      rwa [sq_abs] at h1
    rw [hfe]
    have h4 : (4 * δ) ^ 2 / 16 = δ ^ 2 := by ring
    rw [h4]
    calc δ ^ 2 * z ^ 2 ≤ δ ^ 2 * 1 := by
          exact mul_le_mul_of_nonneg_left hz2 (sq_nonneg δ)
      _ = δ ^ 2 := by ring
      _ ≤ (d θ) ^ 2 := hd2
      _ = (d θ) ^ 2 * 1 := by ring
      _ ≤ (d θ) ^ 2 * z ^ (-(6 / α)) :=
          mul_le_mul_of_nonneg_left hzp (sq_nonneg (d θ))
  have hmain := Work.Coercivity.theta_integral_lower α 6 f z hz
    (θ₁ := θ₀ - ε) (θ₂ := θ₀ + ε) (Aref := 4 * δ)
    (by linarith [hε1, hθ₀.1]) (by linarith [hεpos]) (by linarith [hε2, hθ₀.2])
    (hHk z hz) hlow
  have hA : (4 * δ) ^ 2 * ((θ₀ + ε) - (θ₀ - ε)) / 16 = δ ^ 2 * (2 * ε) := by ring
  rw [hA] at hmain
  -- the weight beats `1/z²`
  have hw2 : 1 / z ^ 2 ≤ (Work.Spaces.w z) ^ 2 * z ^ 2 := by
    have h : (Work.Spaces.w z) ^ 2 * z ^ 2 = (1 + z) ^ 4 / z ^ 2 := by
      rw [Work.Spaces.w]
      field_simp
    rw [h, div_le_div_iff_of_pos_right (pow_pos hz 2)]
    exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + z)
  have hc0 : 0 ≤ δ ^ 2 * (2 * ε) := by positivity
  calc δ ^ 2 * (2 * ε) / z ^ 2
      = δ ^ 2 * (2 * ε) * (1 / z ^ 2) := by ring
    _ ≤ δ ^ 2 * (2 * ε) * ((Work.Spaces.w z) ^ 2 * z ^ 2) :=
        mul_le_mul_of_nonneg_left hw2 hc0
    _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ := hmain

/-! ## `Rop w = Vop w` once `Uop w = 0` -/

private theorem Rop_eq_Vop {α : ℝ} {w : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hU : Work.Construction.Uop α w z θ = 0) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Construction.Rop α w z θ = Work.Construction.Vop w z θ := by
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hpz : α * z * Work.Spaces.pz w z θ = -3 * w z θ := by
    have h := hU
    simp only [Work.Construction.Uop] at h
    linarith [h]
  have hnum : 2 * Real.sin θ * w z θ + α * Real.sin θ * z * Work.Spaces.pz w z θ
      + Real.cos θ * Work.Spaces.pth w z θ
      = Real.cos θ * (Work.Spaces.pth w z θ - Real.tan θ * w z θ) := by
    rw [Real.tan_eq_sin_div_cos]
    have hx : α * Real.sin θ * z * Work.Spaces.pz w z θ
        = Real.sin θ * (α * z * Work.Spaces.pz w z θ) := by ring
    rw [hx, hpz]
    field_simp
    ring
  simp only [Work.Construction.Rop, Work.Construction.Vop]
  rw [hnum, div_eq_iff (ne_of_gt hcos)]
  ring

/-! ## The main statement -/

theorem SlotsZeroRest {α : ℝ} (hα : 0 < α) {w : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen w)
    (hU : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Uop α w z θ = 0)
    (hV : Work.Spaces.HkMem α 6 (Work.Construction.Vop w)) :
    (∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Rop α w z θ = 0) ∧
    (∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Uop α w z θ = 0) ∧
    (∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Vop w z θ = 0) := by
  have hsmV : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop w) := smoothOpen_Vop_prv hsm
  have hrepV := repr_Vop hα hsm hU
  -- The third slot vanishes: otherwise the level-`0` term of the weighted integrand blows up.
  have hzero : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Vop w z θ = 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨z₀, hz₀, θ₀, hθ₀, hne₀⟩ := hcon
    -- the `θ`-profile `d = Vop w 1 ·` does not vanish at `θ₀`
    have hne : Work.Construction.Vop w 1 θ₀ ≠ 0 := by
      intro h0
      have h := hrepV z₀ hz₀ θ₀ hθ₀
      rw [h, h0, zero_mul] at hne₀
      exact hne₀ rfl
    have hcont : ContinuousAt (fun θ => Work.Construction.Vop w 1 θ) θ₀ :=
      ((hsmV.curry_θ (z := 1) (by norm_num)).continuousOn).continuousAt
        (isOpen_Ioo.mem_nhds hθ₀)
    have hHk : ∀ z, 0 < z → MeasureTheory.IntegrableOn (fun θ =>
        Work.Spaces.HkIntegrand α 6 (Work.Construction.Vop w) z θ) Work.Spaces.Iθ :=
      fun z hz => hV.1 z (le_of_lt hz)
    obtain ⟨c, hc, hlb⟩ := slice_lower_bound hα hθ₀ hcont hne hrepV hHk
    have hInt : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 (Work.Construction.Vop w) z θ) (Set.Ici 0) := hV.2
    exact (Work.Coercivity.not_integrableOn_of_lower_rpow hc (by norm_num : (0 : ℝ) < 1)
      (fun z hz => hlb z hz.1 hz.2)) hInt
  refine ⟨fun z hz θ hθ => ?_, hU, hzero⟩
  rw [Rop_eq_Vop (hU z hz θ hθ) hθ]
  exact hzero z hz θ hθ

end

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.gPsi_eta_abs_le_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.OClass

/-- **The `η`-slot of the projector correction in the open class `SmoothOpen`.**

This is the open-class (`SmoothOpen`, i.e. genuine `C^∞` on the *open* quadrant
`(0,∞) × (0,π/2)`, the class carried by `RegQo`) twin of
`Work.FTS.CoercivityFix.Coer1T.gPsi_eta_abs_le_Q`, which is stated for the interior class
`Work.FTS.LocData.SmoothQuad`.

Nothing in that proof uses the strip `z > -1` beyond the a.e. strong measurability of `f` on
`Iz ×ˢ Iθ`, which `SmoothOpen` supplies by `Work.Spaces.aesm_of_continuousOn_Qd` (the closed
quadrant differs from the open one by a null set).  The two analytic ingredients
(`etaW_gPsi_integrable_Q` for the joint integrability of the pairing density and
`wip_gPsi_eta_le_aux` for the Cauchy–Schwarz bound with constant `220`) are already stated for
the interior class with `haesm` as an explicit hypothesis, so the port is immediate. -/
theorem gPsi_eta_abs_le_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hF : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ * f z θ * Work.Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Coercivity.T4fun α f z θ * f z θ
          * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ |Work.Coercivity.wip
            (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
            (Work.Coercivity.T4fun α f) f|
          ≤ 220 * |Work.Coercivity.C0 f| * Real.sqrt (Work.Coercivity.EfEta f) := by
  have haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry f) hso.continuousOn
  have haesm' : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2)
      (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [Work.Coercivity.volume_restrict_prod]; exact haesm
  refine ⟨?_, ?_⟩
  · have hg := Work.FTS.CoercivityFix.Coer1T.etaW_gPsi_integrable_Q α hα hα1 f haesm' hF
    refine IntegrableOn.congr_fun (Integrable.const_mul hg (Work.Coercivity.C0 f)) ?_
      (measurableSet_Ici.prod measurableSet_Icc)
    intro p hp
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, Work.Coercivity.T4fun]
    ring
  · rw [show Work.Coercivity.T4fun α f
        = fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)
            * Work.Coercivity.C0 f from rfl]
    exact Work.FTS.CoercivityFix.Coer1T.wip_gPsi_eta_le_aux α hα hα1 f
      (Work.Coercivity.C0 f) haesm hF

end Work.FTS.StrongEps.EpsE4Thr.OClass
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.psiA_eta_abs_le_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.OClass

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The `L₁₂`-correction pairing `⟨T1fun α f, f⟩_{w² sin^{-η}}` in the **open** class

`T1fun α f = (2 z Γ(θ)/(c(1+z)²))·L₁₂(f)(z)` is the `L₁₂`-term of `𝓛_Γ`, and this file proves
the two facts about its `η`-weighted pairing against `f` that the `η`-slot of the level-1
coercivity of `𝓛_Γ^T` needs, **in the open class** `SmoothOpen` (genuine `C^∞` on the *open*
quadrant `(0,∞) × (0,π/2)`, the class carried by `RegQo`) rather than the interior class
`SmoothQuad` (`C^∞` on the strip `z > -1`) of
`Submission/Work/FTS/CoercivityFix/Coer1T/psiA_eta_abs_le_Q.lean` (whose statement is
`Work.FTS.CoercivityFix.Coer1T.psiA_eta_abs_le_Q`):

* the integrand `T1fun α f · f · w² sin(2θ)^{-η}` is jointly integrable on the quadrant;
* the pairing obeys `|⟨T1fun α f, f⟩_{w² sin^{-η}}| ≤ 220 √(EL12z f) √(EfEta f)`.

The proof is Cauchy–Schwarz in `L²(P)` (`P` the product of the restrictions of Lebesgue measure
to `Iz` and `Iθ`) after the pointwise split
`(2zΓ/(c(1+z)²))Λ f w² s^{-η} = 2·[(Γ/c)(Λ/z)s^{-η/2}]·[f w s^{-η/2}]`
(valid because `w = z²w²/(1+z)²`, i.e. `z·w²/(1+z)² = w/z`), which is the *only* place the weight
`w` enters.  The two `L²` norms are `√(EL12z f · ∫_θ (Γ/c)²s^{-η})` and `√(EfEta f)`, and
`∫_θ (Γ/c)²s^{-η} ≤ 12100 = 110²` (`Work.Coercivity.Gam_div_c_sq_eta_integral_le_12100`), giving
`2·110 = 220`.

The two ingredients really used are `HardyHyp f` (which supplies `∫ (L₁₂(f)/z)² < ∞` and the
continuity of `L₁₂(f)` on `(0,∞)`) and the joint integrability `hF` of `f²w² sin^{-η}`; the
a.e. strong measurability of `f` comes from `SmoothOpen` via
`Work.Spaces.aesm_of_continuousOn_Qd` (the open quadrant and `Iz ×ˢ Iθ` differ by a null set).
-/

/-- **The pointwise Cauchy–Schwarz splitting** of the `T1fun` pairing.

For `z ≠ 0` and `0 ≤ s = sin(2θ)` one has
`(2zΓ/(c(1+z)²))Λ·f·w² s^{-η} = 2·[(Γ/c)(Λ/z)s^{-η/2}]·[f w s^{-η/2}]`,
because `w = (1+z)²/z²` gives `z w²/(1+z)² = w/z`. -/
theorem T1fun_eta_split_O (α : ℝ) (hc : Work.Spaces.c α ≠ 0) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : z ≠ 0) (hs : 0 ≤ Real.sin (2 * θ)) :
    Work.Coercivity.T1fun α f z θ * f z θ
        * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      = 2 * (((Work.Spaces.Gam α θ / Work.Spaces.c α)
              * (Work.Coercivity.L12f f z / z)
              * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta / 2))
            * (f z θ * Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta / 2))) := by
  rw [← Work.Coercivity.rpow_half_sq (Real.sin (2 * θ)) hs]
  simp only [Work.Coercivity.T1fun, Work.Spaces.w]
  field_simp

theorem psiA_eta_abs_le_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hfH : Work.Coercivity.HardyHyp f)
    (hF : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ * f z θ * Work.Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Coercivity.T1fun α f z θ * f z θ
          * Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ |Work.Coercivity.wip
            (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
            (Work.Coercivity.T1fun α f) f|
          ≤ 220 * Real.sqrt (Work.Coercivity.EL12z f) * Real.sqrt (Work.Coercivity.EfEta f) := by
  set P : Measure (ℝ × ℝ) :=
    (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) with hP
  set A : ℝ × ℝ → ℝ := fun p => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
      * (Work.Coercivity.L12f f p.1 / p.1)
      * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta / 2) with hA
  set B : ℝ × ℝ → ℝ := fun p => f p.1 p.2 * Work.Spaces.w p.1
      * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta / 2) with hB
  have hsin0 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hc : Work.Spaces.c α ≠ 0 := Work.Coercivity.c_ne_zero hα hα1
  -- ### A.e. strong measurability
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2) P := by
    rw [hP]
    exact Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry f) hso.continuousOn
  have hLesm : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Coercivity.L12f f p.1) P := by
    have h1 := Work.Coercivity.aesm_L12f (Work.Coercivity.L12f_continuousOn f hfH)
    rwa [← Work.Coercivity.prod_restrict_eq] at h1
  have hsinesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta / 2)) P := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hAesm : AEStronglyMeasurable A P := by
    rw [hA]
    have hw : Measurable (fun p : ℝ × ℝ => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
        * (p.1)⁻¹ * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta / 2)) := by
      unfold Work.Spaces.Gam
      fun_prop
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
        * (p.1)⁻¹ * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta / 2)
        * Work.Coercivity.L12f f p.1) P :=
      hw.aestronglyMeasurable.mul hLesm
    refine h1.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [div_eq_mul_inv]
    ring
  have hBesm : AEStronglyMeasurable B P := by
    rw [hB]
    have hw : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.w p.1) P := by
      apply Measurable.aestronglyMeasurable
      unfold Work.Spaces.w
      fun_prop
    exact (haesm.mul hw).mul hsinesm
  -- ### Square-integrability of `A` and `B`
  have ha : IntegrableOn (fun z : ℝ => (Work.Coercivity.L12f f z / z) ^ 2) Work.Spaces.Iz := by
    have h1 := hfH.intA 1 (by norm_num : (1 : ℕ) ≤ 2)
    have h2 : IntegrableOn (fun z : ℝ => (Work.Coercivity.L12f f z / z) ^ 2)
        (Set.Ioi (0 : ℝ)) := by
      refine h1.congr (Filter.Eventually.of_forall fun z => ?_)
      show (Work.Coercivity.L12f f z) ^ 2 / z ^ (2 * ((1 : ℕ) : ℝ))
          = (Work.Coercivity.L12f f z / z) ^ 2
      have hz : (z : ℝ) ^ (2 * ((1 : ℕ) : ℝ)) = z ^ (2 : ℕ) := by
        rw [show (2 * ((1 : ℕ) : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hz, div_pow]
    show Integrable (fun z : ℝ => (Work.Coercivity.L12f f z / z) ^ 2)
      (volume.restrict (Set.Ici (0 : ℝ)))
    rw [← Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact h2
  have hb : IntegrableOn (fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
      * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ := by
    refine Integrable.mono' (Integrable.const_mul (Work.Spaces.sin_two_rpow (-Work.Spaces.eta)
      (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])).1 100) ?_ ?_
    · unfold Work.Spaces.Gam
      fun_prop
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have hs0 := hsin0 θ hθ
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _))]
      have hG : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 :=
        Work.Coercivity.Gam_div_c_bound hα hα1 hθ
      have hsq : (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2 ≤ 100 := by
        nlinarith [hG, abs_nonneg (Work.Spaces.Gam α θ / Work.Spaces.c α),
          sq_abs (Work.Spaces.Gam α θ / Work.Spaces.c α)]
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hs0 _)
  have hA2 : Integrable (fun p => A p ^ 2) P := by
    rw [hP]
    refine ((ha.mul_prod hb).congr ?_)
    filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hs0 := hsin0 θ hθ
    simp only [hA]
    rw [mul_pow, mul_pow, Work.Coercivity.rpow_half_sq _ hs0]
    ring
  have hB2 : Integrable (fun p => B p ^ 2) P := by
    rw [hP]
    refine ((Work.Coercivity.integrableOn_prod hF).congr ?_)
    filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hs0 := hsin0 θ hθ
    simp only [hB]
    rw [mul_pow, mul_pow, Work.Coercivity.rpow_half_sq _ hs0]
    ring
  -- ### Joint integrability of the product
  have hABi : Integrable (fun p : ℝ × ℝ => A p * B p) P := by
    refine Integrable.mono' (hA2.add hB2) (hAesm.mul hBesm) ?_
    filter_upwards with p
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul]
    have h1 : 0 ≤ (|A p| - |B p|) ^ 2 := sq_nonneg _
    have h2 : (|A p| - |B p|) ^ 2
        = (A p) ^ 2 - 2 * (|A p| * |B p|) + (B p) ^ 2 := by
      rw [sub_sq, sq_abs, sq_abs]
      ring
    have h3 : 0 ≤ |A p| * |B p| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    linarith
  have hIntProd : Integrable (fun p : ℝ × ℝ => 2 * (A p * B p)) P := hABi.const_mul 2
  -- ### The weighted pairing as a product-measure integral
  have hIntOn : IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.T1fun α f z θ * f z θ
        * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := hIntProd
    rw [IntegrableOn, ← Work.Coercivity.prod_restrict_eq]
    refine h.congr ?_
    filter_upwards [Work.Coercivity.ae_prod_pos, Work.Coercivity.ae_prod_quadrant] with p hpos hq
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hq
    simp only [Function.uncurry_apply_pair]
    exact (T1fun_eta_split_O α hc f (ne_of_gt hpos) (hsin0 θ hθ)).symm
  have hwip : Work.Coercivity.wip
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      (Work.Coercivity.T1fun α f) f = ∫ p, 2 * (A p * B p) ∂P := by
    rw [Work.Coercivity.wip_eq_integral_prod
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      (Work.Coercivity.T1fun α f) f hIntOn, ← hP]
    refine integral_congr_ae ?_
    filter_upwards [Work.Coercivity.ae_prod_pos, Work.Coercivity.ae_prod_quadrant] with p hpos hq
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hq
    exact T1fun_eta_split_O α hc f (ne_of_gt hpos) (hsin0 θ hθ)
  -- ### Cauchy–Schwarz
  have hCS := Work.Coercivity.sq_integral_mul_le P A B hAesm hBesm hA2 hB2
  have hA2nn : 0 ≤ ∫ p, A p ^ 2 ∂P := integral_nonneg fun p => sq_nonneg _
  have habs : |∫ p, A p * B p ∂P|
      ≤ Real.sqrt (∫ p, A p ^ 2 ∂P) * Real.sqrt (∫ p, B p ^ 2 ∂P) := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hA2nn]
    exact Real.sqrt_le_sqrt hCS
  -- ### The values of the two square-integrals
  have hBval : ∫ p, B p ^ 2 ∂P = Work.Coercivity.EfEta f := by
    have hF' : IntegrableOn (Function.uncurry (fun z θ => f z θ * f z θ
        * (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
      IntegrableOn.congr_fun hF (fun p hp => by
        obtain ⟨z, θ⟩ := p
        simp only [Function.uncurry_apply_pair]
        ring) (measurableSet_Ici.prod measurableSet_Icc)
    rw [Work.Coercivity.EfEta_eq_wip, Work.Coercivity.wip_eq_integral_prod
      (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) f f hF', ← hP]
    refine integral_congr_ae ?_
    filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ⟩ := hp
    have hs0 := hsin0 θ hθ
    simp only [hB]
    rw [mul_pow, mul_pow, Work.Coercivity.rpow_half_sq _ hs0]
    ring
  have hAval : ∫ p, A p ^ 2 ∂P
      = Work.Coercivity.EL12z f
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by
    have hcongr : (fun p : ℝ × ℝ => A p ^ 2)
        =ᵐ[P] (fun p : ℝ × ℝ => (Work.Coercivity.L12f f p.1 / p.1) ^ 2
          * ((Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2
            * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta))) := by
      filter_upwards [Work.Coercivity.ae_prod_quadrant] with p hp
      obtain ⟨z, θ⟩ := p
      obtain ⟨hz, hθ⟩ := hp
      have hs0 := hsin0 θ hθ
      simp only [hA]
      rw [mul_pow, mul_pow, Work.Coercivity.rpow_half_sq _ hs0]
      ring
    rw [MeasureTheory.integral_congr_ae hcongr, hP]
    rw [Work.Coercivity.integral_prod_sep
      (a := fun z : ℝ => (Work.Coercivity.L12f f z / z) ^ 2)
      (b := fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) ha hb]
    rfl
  -- ### Numerical conclusion
  have hX := Work.Coercivity.Gam_div_c_sq_eta_integral_le_12100 α hα hα1
  have hELnn : 0 ≤ Work.Coercivity.EL12z f := by
    rw [Work.Coercivity.EL12z, Work.Coercivity.L2Sqz]
    exact integral_nonneg fun z => sq_nonneg _
  have hsqrt : Real.sqrt (Work.Coercivity.EL12z f)
      * Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      ≤ 110 * Real.sqrt (Work.Coercivity.EL12z f) := by
    have h110 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) ≤ 110 := by
      rw [show (110 : ℝ) = Real.sqrt 12100 by
        rw [show (12100 : ℝ) = 110 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hX
    calc Real.sqrt (Work.Coercivity.EL12z f)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
            * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        ≤ Real.sqrt (Work.Coercivity.EL12z f) * 110 :=
          mul_le_mul_of_nonneg_left h110 (Real.sqrt_nonneg _)
      _ = 110 * Real.sqrt (Work.Coercivity.EL12z f) := by ring
  refine ⟨?_, ?_⟩
  · exact IntegrableOn.congr_fun hIntOn (fun p hp => by
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry_apply_pair]
      ring) (measurableSet_Ici.prod measurableSet_Icc)
  · calc |Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Coercivity.T1fun α f) f|
        = |∫ p, 2 * (A p * B p) ∂P| := by rw [hwip]
      _ = 2 * |∫ p, A p * B p ∂P| := by
          rw [MeasureTheory.integral_const_mul, abs_mul]
          norm_num
      _ ≤ 2 * (Real.sqrt (∫ p, A p ^ 2 ∂P) * Real.sqrt (∫ p, B p ^ 2 ∂P)) :=
          mul_le_mul_of_nonneg_left habs (by norm_num)
      _ = 2 * (Real.sqrt (Work.Coercivity.EL12z f
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
              * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
            * Real.sqrt (Work.Coercivity.EfEta f)) := by
          rw [hAval, hBval]
      _ = 2 * (Real.sqrt (Work.Coercivity.EL12z f)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
              * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
            * Real.sqrt (Work.Coercivity.EfEta f)) := by
          rw [Real.sqrt_mul hELnn]
      _ ≤ 2 * ((110 * Real.sqrt (Work.Coercivity.EL12z f))
            * Real.sqrt (Work.Coercivity.EfEta f)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)
      _ = 220 * Real.sqrt (Work.Coercivity.EL12z f)
            * Real.sqrt (Work.Coercivity.EfEta f) := by ring

end Work.FTS.StrongEps.EpsE4Thr.OClass
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.D5.l1_cauchy_pz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif.D5

set_option linter.unusedVariables false

/-! ## The engine: a small `L¹` bound for `∂_z` from a small sup-bound for `L` and a
uniform `L²` bound for `∂_z²` -/

theorem l1_box_le {a b a₀ b₀ c d h δ M : ℝ}
    (ha : a₀ ≤ a) (hab : a ≤ b) (hbb₀ : b + h ≤ b₀) (hh : 0 < h)
    (hcd : c ≤ d)
    {P G G' : ℝ → ℝ → ℝ}
    (hP : ∀ z ∈ Set.Icc a (b + h), ∀ θ ∈ Set.Icc c d, |P z θ| ≤ δ)
    (hG : ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a (b + h), HasDerivAt (fun z' => P z' θ) (G z θ) z)
    (hG' : ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a (b + h), HasDerivAt (fun z' => G z' θ) (G' z θ) z)
    (hGcont : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (hG'cont : ContinuousOn (fun p : ℝ × ℝ => G' p.1 p.2) (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (hint : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d, (G' p.1 p.2) ^ 2 ≤ M) :
    ∫ p in Set.Icc a b ×ˢ Set.Icc c d, |G p.1 p.2|
      ≤ 2 * (b - a) * (d - c) * δ / h + h * (M + (b - a + h) * (d - c) / 4) := by
  have hab₂ : a ≤ b + h := by linarith
  have hbb : b ≤ b₀ := by linarith
  -- (A) the `L²` hypothesis, moved to the small box and to the θ-outer iterated form
  have hsub : Set.Icc a (b + h) ×ˢ Set.Icc c d ⊆ Set.Icc a₀ b₀ ×ˢ Set.Icc c d :=
    Set.prod_mono (Set.Icc_subset_Icc ha hbb₀) Subset.rfl
  have hFcont : ContinuousOn (fun p : ℝ × ℝ => (G' p.1 p.2) ^ 2)
      (Set.Icc a (b + h) ×ˢ Set.Icc c d) := (hG'cont.mono hsub).pow 2
  have hFint : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (G' p.1 p.2) ^ 2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) (hG'cont.pow 2)
  have hnnF : 0 ≤ᵐ[volume.restrict (Set.Icc a₀ b₀ ×ˢ Set.Icc c d)]
      (fun p : ℝ × ℝ => (G' p.1 p.2) ^ 2) := Filter.Eventually.of_forall fun p => sq_nonneg _
  have hreal_sub : ∫ p in Set.Icc a (b + h) ×ˢ Set.Icc c d, (G' p.1 p.2) ^ 2 ≤ M :=
    (MeasureTheory.setIntegral_mono_set hFint hnnF (Filter.Eventually.of_forall hsub)).trans hint
  have hiter : ∫ θ in c..d, ∫ u in a..(b + h), (G' u θ) ^ 2 ≤ M := by
    rw [box_integral_eq (g := fun z θ => (G' z θ) ^ 2) hab₂ hcd hFcont,
      intervalIntegral_swap (g := fun z θ => (G' z θ) ^ 2) hab₂ hcd hFcont] at hreal_sub
    exact hreal_sub
  -- (B) the pointwise slice inequality, for every θ
  have hsmall : Set.Icc a b ×ˢ Set.Icc c d ⊆ Set.Icc a₀ b₀ ×ˢ Set.Icc c d :=
    Set.prod_mono (Set.Icc_subset_Icc ha hbb) Subset.rfl
  have hslice : ∀ θ ∈ Set.Icc c d, ContinuousOn (fun u : ℝ => G' u θ) (Set.Icc a (b + h)) := by
    intro θ hθ
    have h2 : ContinuousOn (fun u : ℝ => (u, θ)) (Set.Icc a (b + h)) :=
      continuousOn_id.prodMk continuousOn_const
    exact (hG'cont.mono hsub).comp h2 (fun u hu => ⟨hu, hθ⟩)
  have hsliceG : ∀ θ ∈ Set.Icc c d, ContinuousOn (fun u : ℝ => G u θ) (Set.Icc a (b + h)) := by
    intro θ hθ
    have h2 : ContinuousOn (fun u : ℝ => (u, θ)) (Set.Icc a (b + h)) :=
      continuousOn_id.prodMk continuousOn_const
    exact (hGcont.mono hsub).comp h2 (fun u hu => ⟨hu, hθ⟩)
  have hpt : ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a b,
      |G z θ| ≤ 2 * δ / h + ∫ u in z..(z + h), |G' u θ| := by
    intro θ hθ z hz
    exact slice_pointwise_le hab hh (fun x hx => hP x hx θ hθ)
      (fun x hx => hG θ hθ x hx) (fun x hx => hG' θ hθ x hx) (hslice θ hθ) z hz
  -- (C) integrate in `z`, for every θ
  have hzbd : ∀ θ ∈ Set.Icc c d,
      ∫ z in a..b, |G z θ| ≤ 2 * (b - a) * δ / h + h * ∫ u in a..(b + h), |G' u θ| := by
    intro θ hθ
    have hshift : ContinuousOn (fun z => ∫ u in z..(z + h), |G' u θ|) (Set.Icc a b) :=
      continuousOn_intervalIntegral_shift hab hh ((hslice θ hθ).abs)
    have hIL : IntervalIntegrable (fun z => |G z θ|) volume a b := by
      have h : ContinuousOn (fun z => |G z θ|) (Set.uIcc a b) := by
        rw [Set.uIcc_of_le hab]
        exact ((hsliceG θ hθ).abs).mono (Set.Icc_subset_Icc le_rfl (by linarith))
      exact h.intervalIntegrable
    have hIR : IntervalIntegrable (fun z => 2 * δ / h + ∫ u in z..(z + h), |G' u θ|)
        volume a b := by
      have hc : ContinuousOn (fun z => 2 * δ / h + ∫ u in z..(z + h), |G' u θ|)
          (Set.uIcc a b) := by
        rw [Set.uIcc_of_le hab]
        exact continuousOn_const.add hshift
      exact hc.intervalIntegrable
    have hstep : ∫ z in a..b, |G z θ| ≤
        ∫ z in a..b, (2 * δ / h + ∫ u in z..(z + h), |G' u θ|) :=
      intervalIntegral.integral_mono_on hab hIL hIR (fun z hz => hpt θ hθ z hz)
    have hsum : ∫ z in a..b, (2 * δ / h + ∫ u in z..(z + h), |G' u θ|)
        = (b - a) * (2 * δ / h) + ∫ z in a..b, ∫ u in z..(z + h), |G' u θ| := by
      have hc : IntervalIntegrable (fun _ : ℝ => 2 * δ / h) volume a b := by
        have hcc : ContinuousOn (fun _ : ℝ => 2 * δ / h) (Set.uIcc a b) := continuousOn_const
        exact hcc.intervalIntegrable
      have hs : IntervalIntegrable (fun z => ∫ u in z..(z + h), |G' u θ|) volume a b := by
        have hcc : ContinuousOn (fun z => ∫ u in z..(z + h), |G' u θ|) (Set.uIcc a b) := by
          rw [Set.uIcc_of_le hab]
          exact hshift
        exact hcc.intervalIntegrable
      rw [intervalIntegral.integral_add hc hs, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
    have hwin : ∫ z in a..b, ∫ u in z..(z + h), |G' u θ| ≤ h * ∫ u in a..(b + h), |G' u θ| :=
      window_bound hab hh ((hslice θ hθ).abs) (fun u => abs_nonneg _)
    calc ∫ z in a..b, |G z θ|
        ≤ ∫ z in a..b, (2 * δ / h + ∫ u in z..(z + h), |G' u θ|) := hstep
      _ = (b - a) * (2 * δ / h) + ∫ z in a..b, ∫ u in z..(z + h), |G' u θ| := hsum
      _ ≤ (b - a) * (2 * δ / h) + h * ∫ u in a..(b + h), |G' u θ| := by linarith
      _ = 2 * (b - a) * δ / h + h * ∫ u in a..(b + h), |G' u θ| := by ring
  -- (D) integrate in θ
  have hGab : ContinuousOn (Function.uncurry (fun z θ => |G z θ|))
      (Set.Icc a b ×ˢ Set.Icc c d) := (hGcont.mono hsmall).abs
  have habs' : ContinuousOn (Function.uncurry (fun u θ => |G' u θ|))
      (Set.Icc a (b + h) ×ˢ Set.Icc c d) := (hG'cont.mono hsub).abs
  have hGFint : MeasureTheory.IntegrableOn (fun θ => ∫ u in a..(b + h), |G' u θ|)
      (Set.Ioc c d) := (integrableOn_slice_integrals (f := fun u θ => |G' u θ|) hab₂ hcd habs').1
  have hGF2int : MeasureTheory.IntegrableOn (fun θ => ∫ u in a..(b + h), (G' u θ) ^ 2)
      (Set.Ioc c d) :=
    (integrableOn_slice_integrals (f := fun z θ => (G' z θ) ^ 2) hab₂ hcd hFcont).1
  set C : ℝ := 2 * (b - a) * δ / h with hCdef
  have hstepD : ∫ θ in Set.Ioc c d, (∫ z in a..b, |G z θ|) ∂volume
      ≤ ∫ θ in Set.Ioc c d, (C + h * ∫ u in a..(b + h), |G' u θ|) ∂volume := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · exact Filter.Eventually.of_forall
        (fun θ => intervalIntegral.integral_nonneg hab (fun z _ => abs_nonneg _))
    · exact (MeasureTheory.integrable_const C).add (hGFint.const_mul h)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with θ hθ
      exact hzbd θ ⟨hθ.1.le, hθ.2⟩
  have hstepD_eq : ∫ θ in Set.Ioc c d, (C + h * ∫ u in a..(b + h), |G' u θ|) ∂volume
      = (d - c) * C + h * ∫ θ in Set.Ioc c d, (∫ u in a..(b + h), |G' u θ|) ∂volume := by
    rw [MeasureTheory.integral_add (MeasureTheory.integrable_const C) (hGFint.const_mul h),
      MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_const, MeasureTheory.measureReal_restrict_apply_univ,
      Real.volume_real_Ioc_of_le hcd, smul_eq_mul]
  -- (E) the AM–GM step
  have hiterIoc : ∫ θ in Set.Ioc c d, (∫ u in a..(b + h), (G' u θ) ^ 2) ∂volume ≤ M := by
    rw [← intervalIntegral.integral_of_le hcd]
    exact hiter
  have hptE : ∀ θ ∈ Set.Icc c d, ∫ u in a..(b + h), |G' u θ|
      ≤ (∫ u in a..(b + h), (G' u θ) ^ 2) + (b + h - a) * (1 / 4) := by
    intro θ hθ
    have hIL : IntervalIntegrable (fun u => |G' u θ|) volume a (b + h) := by
      have h : ContinuousOn (fun u => |G' u θ|) (Set.uIcc a (b + h)) := by
        rw [Set.uIcc_of_le hab₂]
        exact (hslice θ hθ).abs
      exact h.intervalIntegrable
    have hIR : IntervalIntegrable (fun u => (G' u θ) ^ 2 + 1 / 4) volume a (b + h) := by
      have h : ContinuousOn (fun u => (G' u θ) ^ 2 + 1 / 4) (Set.uIcc a (b + h)) := by
        rw [Set.uIcc_of_le hab₂]
        exact (hslice θ hθ).pow 2 |>.add continuousOn_const
      exact h.intervalIntegrable
    have hstep : ∫ u in a..(b + h), |G' u θ| ≤ ∫ u in a..(b + h), ((G' u θ) ^ 2 + 1 / 4) :=
      intervalIntegral.integral_mono_on hab₂ hIL hIR (fun u _ => by
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg (G' u θ - 1 / 2), sq_nonneg (G' u θ + 1 / 2)])
    have hsum : ∫ u in a..(b + h), ((G' u θ) ^ 2 + 1 / 4)
        = (∫ u in a..(b + h), (G' u θ) ^ 2) + (b + h - a) * (1 / 4) := by
      have hs : IntervalIntegrable (fun u => (G' u θ) ^ 2) volume a (b + h) := by
        have h : ContinuousOn (fun u => (G' u θ) ^ 2) (Set.uIcc a (b + h)) := by
          rw [Set.uIcc_of_le hab₂]
          exact (hslice θ hθ).pow 2
        exact h.intervalIntegrable
      have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / 4) volume a (b + h) :=
        (continuousOn_const (s := Set.uIcc a (b + h)) (c := (1 : ℝ) / 4)).intervalIntegrable
      rw [intervalIntegral.integral_add hs hc, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
    rw [hsum] at hstep
    exact hstep
  have hstepE : ∫ θ in Set.Ioc c d, (∫ u in a..(b + h), |G' u θ|) ∂volume
      ≤ M + (b + h - a) * (d - c) / 4 := by
    have hmono : ∫ θ in Set.Ioc c d, (∫ u in a..(b + h), |G' u θ|) ∂volume
        ≤ ∫ θ in Set.Ioc c d,
          ((∫ u in a..(b + h), (G' u θ) ^ 2) + (b + h - a) * (1 / 4)) ∂volume := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
      · exact Filter.Eventually.of_forall
          (fun θ => intervalIntegral.integral_nonneg hab₂ (fun u _ => abs_nonneg _))
      · exact hGF2int.add (MeasureTheory.integrable_const _)
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with θ hθ
        exact hptE θ ⟨hθ.1.le, hθ.2⟩
    have heq : ∫ θ in Set.Ioc c d,
          ((∫ u in a..(b + h), (G' u θ) ^ 2) + (b + h - a) * (1 / 4)) ∂volume
        = (∫ θ in Set.Ioc c d, (∫ u in a..(b + h), (G' u θ) ^ 2) ∂volume)
          + (d - c) * ((b + h - a) * (1 / 4)) := by
      rw [MeasureTheory.integral_add hGF2int (MeasureTheory.integrable_const _)]
      congr 1
      rw [MeasureTheory.integral_const, MeasureTheory.measureReal_restrict_apply_univ,
        Real.volume_real_Ioc_of_le hcd, smul_eq_mul]
    calc ∫ θ in Set.Ioc c d, (∫ u in a..(b + h), |G' u θ|) ∂volume
        ≤ ∫ θ in Set.Ioc c d,
          ((∫ u in a..(b + h), (G' u θ) ^ 2) + (b + h - a) * (1 / 4)) ∂volume := hmono
      _ = (∫ θ in Set.Ioc c d, (∫ u in a..(b + h), (G' u θ) ^ 2) ∂volume)
          + (d - c) * ((b + h - a) * (1 / 4)) := heq
      _ ≤ M + (d - c) * ((b + h - a) * (1 / 4)) := by linarith [hiterIoc]
      _ = M + (b + h - a) * (d - c) / 4 := by ring
  -- (F) assemble
  calc ∫ p in Set.Icc a b ×ˢ Set.Icc c d, |G p.1 p.2|
      = ∫ θ in c..d, ∫ z in a..b, |G z θ| := by
        rw [box_integral_eq (g := fun z θ => |G z θ|) hab hcd hGab,
          intervalIntegral_swap (g := fun z θ => |G z θ|) hab hcd hGab]
    _ = ∫ θ in Set.Ioc c d, (∫ z in a..b, |G z θ|) ∂volume := by
        rw [intervalIntegral.integral_of_le hcd]
    _ ≤ ∫ θ in Set.Ioc c d, (C + h * ∫ u in a..(b + h), |G' u θ|) ∂volume := hstepD
    _ = (d - c) * C + h * ∫ θ in Set.Ioc c d, (∫ u in a..(b + h), |G' u θ|) ∂volume := hstepD_eq
    _ ≤ (d - c) * C + h * (M + (b + h - a) * (d - c) / 4) := by
        have hstepE' := mul_le_mul_of_nonneg_left hstepE hh.le
        linarith [hstepE']
    _ = 2 * (b - a) * (d - c) * δ / h + h * (M + (b - a + h) * (d - c) / 4) := by
        rw [hCdef]; ring


/-! ## The final theorem (dev version) -/

theorem l1_cauchy_pz {a b a₀ b₀ c d M : ℝ} (ha₀ : 0 < a₀) (ha₀a : a₀ < a) (hab : a < b)
    (hbb₀ : b < b₀) (hc : 0 < c) (hcd : c < d) (hd : d < π / 2) (hM : 0 ≤ M)
    {L : ℕ → ℝ → ℝ → ℝ} {Llim : ℝ → ℝ → ℝ}
    (hsm : ∀ n, Work.FTS.EllipticEst.SmoothOpen (L n))
    (hconv : TendstoUniformlyOn (fun n (p : ℝ × ℝ) => L n p.1 p.2) (fun p => Llim p.1 p.2)
      Filter.atTop (Set.Icc a₀ b₀ ×ˢ Set.Icc c d))
    (h1 : ∀ n, ∫⁻ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (L n) p.1 p.2) ^ 2) ≤ ENNReal.ofReal M)
    (h2 : ∀ n, ∫⁻ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2)
          ≤ ENNReal.ofReal M) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal |Work.Spaces.pz (L n) p.1 p.2 - Work.Spaces.pz (L m) p.1 p.2|
          ≤ ENNReal.ofReal ε := by
  intro ε hε
  have ha_pos : 0 < a := lt_trans ha₀ ha₀a
  have hdc : 0 < d - c := by linarith
  have hba : 0 < b - a := by linarith
  have hbnb : 0 < b₀ - b := by linarith
  -- constants
  set c₁ : ℝ := 2 * (b - a) * (d - c) with hc₁def
  have hc₁pos : 0 < c₁ := by rw [hc₁def]; positivity
  set M₄ : ℝ := 4 * M with hM₄def
  have hM₄nn : 0 ≤ M₄ := by rw [hM₄def]; linarith
  set K₂ : ℝ := M₄ + (b₀ - a) * (d - c) / 4 with hK₂def
  have hK₂nn : 0 ≤ K₂ := by
    rw [hK₂def]
    have h : 0 ≤ (b₀ - a) * (d - c) := by nlinarith [hM₄nn]
    linarith
  set hh : ℝ := min ((b₀ - b) / 2) (ε / (2 * (K₂ + 1))) with hhhdef
  have hhhpos : 0 < hh := by
    rw [hhhdef]
    exact lt_min (by linarith) (by positivity)
  have hhhle₁ : hh ≤ (b₀ - b) / 2 := by rw [hhhdef]; exact min_le_left _ _
  have hhhle₂ : hh ≤ ε / (2 * (K₂ + 1)) := by rw [hhhdef]; exact min_le_right _ _
  have hbhh : b + hh ≤ b₀ := by linarith
  have hK₂hh : hh * K₂ ≤ ε / 2 := by
    have h1 : K₂ ≤ K₂ + 1 := by linarith
    have h3 : hh * K₂ ≤ hh * (K₂ + 1) := mul_le_mul_of_nonneg_left h1 hhhpos.le
    have h4 : hh * (K₂ + 1) ≤ (ε / (2 * (K₂ + 1))) * (K₂ + 1) :=
      mul_le_mul_of_nonneg_right hhhle₂ (by linarith)
    have h5 : (ε / (2 * (K₂ + 1))) * (K₂ + 1) = ε / 2 := by
      field_simp
    linarith
  set δ : ℝ := ε * hh / (2 * c₁) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδeq : c₁ * δ / hh = ε / 2 := by
    have hc₁ne : c₁ ≠ 0 := ne_of_gt hc₁pos
    have hhne : hh ≠ 0 := ne_of_gt hhhpos
    rw [hδdef]
    field_simp
  -- the uniform-convergence threshold
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ p ∈ Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
      dist (Llim p.1 p.2) (L n p.1 p.2) < δ / 2 := by
    have h := (Metric.tendstoUniformlyOn_iff.mp hconv) (δ / 2) (by linarith)
    rw [Filter.eventually_atTop] at h
    obtain ⟨N, hN⟩ := h
    exact ⟨N, fun n hn => hN n hn⟩
  refine ⟨N, fun n m hn hm => ?_⟩
  -- the box inclusions
  have hbox : Set.Icc a₀ b₀ ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := by
    intro p hp
    exact Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha₀ hp.1.1, lt_of_lt_of_le hc hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
  have hsubbox : Set.Icc a (b + hh) ×ˢ Set.Icc c d ⊆ Set.Icc a₀ b₀ ×ˢ Set.Icc c d :=
    Set.prod_mono (Set.Icc_subset_Icc ha₀a.le hbhh) Subset.rfl
  -- the pointwise bound on the difference
  have hPbound : ∀ z ∈ Set.Icc a (b + hh), ∀ θ ∈ Set.Icc c d,
      |L n z θ - L m z θ| ≤ δ := by
    intro z hz θ hθ
    have hz' : (z, θ) ∈ Set.Icc a₀ b₀ ×ˢ Set.Icc c d :=
      ⟨⟨le_trans ha₀a.le hz.1, le_trans hz.2 hbhh⟩, hθ⟩
    have h1 := hN n hn (z, θ) hz'
    have h2 := hN m hm (z, θ) hz'
    have h3 : dist (L n z θ) (L m z θ) < δ := by
      calc dist (L n z θ) (L m z θ)
          ≤ dist (L n z θ) (Llim z θ) + dist (Llim z θ) (L m z θ) := dist_triangle _ _ _
        _ = dist (Llim z θ) (L n z θ) + dist (Llim z θ) (L m z θ) := by
            rw [dist_comm (L n z θ) (Llim z θ)]
        _ < δ / 2 + δ / 2 := add_lt_add h1 h2
        _ = δ := by ring
    rw [Real.dist_eq] at h3
    exact le_of_lt h3
  -- the derivative relations
  have hGderiv : ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a (b + hh),
      HasDerivAt (fun z' => L n z' θ - L m z' θ)
        (Work.Spaces.pz (L n) z θ - Work.Spaces.pz (L m) z θ) z := by
    intro θ hθ z hz
    have hθ' : θ ∈ Set.Ioo 0 (π / 2) :=
      ⟨lt_of_lt_of_le hc hθ.1, lt_of_le_of_lt hθ.2 hd⟩
    have hz' : 0 < z := lt_of_lt_of_le ha_pos hz.1
    exact ((hsm n).hasDerivAt_slice hθ' hz').sub ((hsm m).hasDerivAt_slice hθ' hz')
  have hG'deriv : ∀ θ ∈ Set.Icc c d, ∀ z ∈ Set.Icc a (b + hh),
      HasDerivAt (fun z' => Work.Spaces.pz (L n) z' θ - Work.Spaces.pz (L m) z' θ)
        (Work.Spaces.pz (Work.Spaces.pz (L n)) z θ
          - Work.Spaces.pz (Work.Spaces.pz (L m)) z θ) z := by
    intro θ hθ z hz
    have hθ' : θ ∈ Set.Ioo 0 (π / 2) :=
      ⟨lt_of_lt_of_le hc hθ.1, lt_of_le_of_lt hθ.2 hd⟩
    have hz' : 0 < z := lt_of_lt_of_le ha_pos hz.1
    exact ((hsm n).pz.hasDerivAt_slice hθ' hz').sub ((hsm m).pz.hasDerivAt_slice hθ' hz')
  -- joint continuity
  have hGcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pz (L n) p.1 p.2 - Work.Spaces.pz (L m) p.1 p.2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
    (((hsm n).pz.continuousOn).mono hbox).sub (((hsm m).pz.continuousOn).mono hbox)
  have hG'cont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2
        - Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
    (((hsm n).pz.pz.continuousOn).mono hbox).sub (((hsm m).pz.pz.continuousOn).mono hbox)
  -- the `L²` bound on the difference
  have hIntN : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      ((((hsm n).pz.pz.continuousOn).mono hbox).pow 2)
  have hIntM : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2)
      (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      ((((hsm m).pz.pz.continuousOn).mono hbox).pow 2)
  have hreN : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2 ≤ M := by
    have h := h2 n
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntN
      (Filter.Eventually.of_forall fun p => sq_nonneg _)] at h
    exact (ENNReal.ofReal_le_ofReal_iff hM).mp h
  have hreM : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2 ≤ M := by
    have h := h2 m
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntM
      (Filter.Eventually.of_forall fun p => sq_nonneg _)] at h
    exact (ENNReal.ofReal_le_ofReal_iff hM).mp h
  have hcomb : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2
        - Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2 ≤ M₄ := by
    have hmaj : MeasureTheory.IntegrableOn
        (fun p : ℝ × ℝ => 2 * (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2
          + 2 * (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2)
        (Set.Icc a₀ b₀ ×ˢ Set.Icc c d) :=
      (hIntN.const_mul 2).add (hIntM.const_mul 2)
    have hpt : ∀ᵐ p ∂(volume.restrict (Set.Icc a₀ b₀ ×ˢ Set.Icc c d)),
        (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2
          - Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2
        ≤ 2 * (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2
          + 2 * (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2 :=
      Filter.Eventually.of_forall fun p => by nlinarith [sq_nonneg (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2 + Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2)]
    have hstep : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
          (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2
            - Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2
        ≤ ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
          (2 * (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2
            + 2 * (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2) :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun p => sq_nonneg _) hmaj hpt
    have hsplit : ∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
          (2 * (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2
            + 2 * (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2)
        = 2 * (∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
            (Work.Spaces.pz (Work.Spaces.pz (L n)) p.1 p.2) ^ 2)
          + 2 * (∫ p in Set.Icc a₀ b₀ ×ˢ Set.Icc c d,
            (Work.Spaces.pz (Work.Spaces.pz (L m)) p.1 p.2) ^ 2) := by
      rw [MeasureTheory.integral_add (hIntN.const_mul 2) (hIntM.const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [hsplit] at hstep
    rw [hM₄def]
    linarith
  -- the engine
  have hmain := l1_box_le ha₀a.le (le_of_lt hab) hbhh hhhpos (le_of_lt hcd)
    hPbound hGderiv hG'deriv hGcont hG'cont hcomb
  have hreal : ∫ p in Set.Icc a b ×ˢ Set.Icc c d,
      |Work.Spaces.pz (L n) p.1 p.2 - Work.Spaces.pz (L m) p.1 p.2| ≤ ε := by
    have hK₂' : M₄ + (b - a + hh) * (d - c) / 4 ≤ K₂ := by
      rw [hK₂def]
      have hle : b - a + hh ≤ b₀ - a := by linarith
      have hmul : (b - a + hh) * (d - c) ≤ (b₀ - a) * (d - c) :=
        mul_le_mul_of_nonneg_right hle hdc.le
      have hdiv : (b - a + hh) * (d - c) / 4 ≤ (b₀ - a) * (d - c) / 4 :=
        div_le_div_of_nonneg_right hmul (by norm_num)
      linarith
    have hstep : hh * (M₄ + (b - a + hh) * (d - c) / 4) ≤ hh * K₂ :=
      mul_le_mul_of_nonneg_left hK₂' hhhpos.le
    have hstep' : hh * (M₄ + (b - a + hh) * (d - c) / 4) ≤ ε / 2 := le_trans hstep hK₂hh
    have h1 : 2 * (b - a) * (d - c) * δ / hh = c₁ * δ / hh := by rw [hc₁def]
    rw [h1] at hmain
    linarith [hmain, hstep', hδeq]
  -- convert the real bound into the lower integral
  have hIntabs : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => |Work.Spaces.pz (L n) p.1 p.2 - Work.Spaces.pz (L m) p.1 p.2|)
      (Set.Icc a b ×ˢ Set.Icc c d) := by
    have hsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Set.Icc a₀ b₀ ×ˢ Set.Icc c d :=
      Set.prod_mono (Set.Icc_subset_Icc ha₀a.le (le_of_lt hbb₀)) Subset.rfl
    exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      ((hGcont.mono hsub).abs)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntabs
    (Filter.Eventually.of_forall fun p => abs_nonneg _)]
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mpr hreal

end Work.FTS.StrongEps.LocUnif.D5
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.Degen.DthIterGamGen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Work.FTS.LocData

namespace Work.FTS.StrongPersist.Degen

set_option autoImplicit false

/-! ## Elementary product bounds -/

/-- Product bound from bounds on the two factors. -/
lemma abs_prod2_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hA : 0 ≤ A) :
    |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) hA

/-- Product bound from bounds on the three factors. -/
lemma abs_prod3_le {a b c A B C : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hA : 0 ≤ A) (hB : 0 ≤ B) : |a * b * c| ≤ A * B * C := by
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have h1 : |a * b| ≤ A * B := abs_prod2_le ha hb hA
  calc |a * b * c| = |a * b| * |c| := abs_mul (a * b) c
    _ ≤ (A * B) * C := mul_le_mul h1 hc (abs_nonneg c) hAB
    _ = A * B * C := by ring

/-- Product bound from bounds on the four factors. -/
lemma abs_prod4_le {a b c d A B C D : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    |a * b * c * d| ≤ A * B * C * D := by
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have hABC : 0 ≤ A * B * C := mul_nonneg hAB hC
  have h1 : |a * b * c| ≤ A * B * C := abs_prod3_le ha hb hc hA hB
  calc |a * b * c * d| = |a * b * c| * |d| := abs_mul (a * b * c) d
    _ ≤ (A * B * C) * D := mul_le_mul h1 hd (abs_nonneg d) hABC
    _ = A * B * C * D := by ring

/-- Product bound from bounds on the five factors. -/
lemma abs_prod5_le {a b c d e A B C D E : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) (he : |e| ≤ E) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    |a * b * c * d * e| ≤ A * B * C * D * E := by
  have hABCD : 0 ≤ A * B * C * D := mul_nonneg (mul_nonneg (mul_nonneg hA hB) hC) hD
  have h1 : |a * b * c * d| ≤ A * B * C * D := abs_prod4_le ha hb hc hd hA hB hC
  calc |a * b * c * d * e| = |a * b * c * d| * |e| := abs_mul (a * b * c * d) e
    _ ≤ (A * B * C * D) * E := mul_le_mul h1 he (abs_nonneg e) hABCD
    _ = A * B * C * D * E := by ring

/-- Triangle inequality for a sum of three terms. -/
lemma abs_add3_le {a b c A B C : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) :
    |a + b + c| ≤ A + B + C := by
  have h1 := abs_add_le a b
  have h2 := abs_add_le (a + b) c
  linarith

/-- Triangle inequality for a sum of five terms. -/
lemma abs_add5_le {a b c d e A B C D E : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) (he : |e| ≤ E) : |a + b + c + d + e| ≤ A + B + C + D + E := by
  have h1 := abs_add_le a b
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le (a + b + c) d
  have h4 := abs_add_le (a + b + c + d) e
  linarith

/-! ## Pointwise bounds for `u ∈ [-1,1]` -/

lemma abs_one_sub_sq_le_one_g {u : ℝ} (hu : |u| ≤ 1) : |1 - u ^ 2| ≤ 1 := by
  have h1 : -1 ≤ u := (abs_le.mp hu).1
  have h2 : u ≤ 1 := (abs_le.mp hu).2
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg u]

lemma abs_u_sub_third_le_g {u : ℝ} (hu : |u| ≤ 1) : |u - 1 / 3| ≤ 4 / 3 := by
  rw [abs_le]
  have h1 : -1 ≤ u := (abs_le.mp hu).1
  have h2 : u ≤ 1 := (abs_le.mp hu).2
  constructor <;> linarith

lemma abs_three_u_sub_one_le_four_g {u : ℝ} (hu : |u| ≤ 1) : |3 * u - 1| ≤ 4 := by
  rw [abs_le]
  have h1 : -1 ≤ u := (abs_le.mp hu).1
  have h2 : u ≤ 1 := (abs_le.mp hu).2
  constructor <;> linarith

lemma abs_one_sub_three_sq_le_two_g {u : ℝ} (hu : |u| ≤ 1) : |1 - 3 * u ^ 2| ≤ 2 := by
  rw [abs_le]
  have h1 : -1 ≤ u := (abs_le.mp hu).1
  have h2 : u ≤ 1 := (abs_le.mp hu).2
  have hu2 : u ^ 2 ≤ 1 := by nlinarith
  constructor <;> nlinarith [sq_nonneg u]

/-! ## Monomial bounds in `α` -/

lemma abs_alpha_le_B (α : ℝ) : |α| ≤ 1 + α ^ 2 := by
  nlinarith [sq_nonneg α, abs_nonneg α, sq_abs α]

lemma one_add_sq_le_sq (α : ℝ) : 1 + α ^ 2 ≤ (1 + α ^ 2) ^ 2 := by
  nlinarith [sq_nonneg α]

lemma abs_alpha_le_B2 (α : ℝ) : |α| ≤ (1 + α ^ 2) ^ 2 :=
  (abs_alpha_le_B α).trans (one_add_sq_le_sq α)

lemma abs_alpha_sq_le_B2 (α : ℝ) : |α| ^ 2 ≤ (1 + α ^ 2) ^ 2 := by
  rw [sq_abs]
  exact (by nlinarith [sq_nonneg α] : α ^ 2 ≤ (1 + α ^ 2) ^ 2)

lemma abs_alpha_cube_le_B2 (α : ℝ) : |α| ^ 3 ≤ (1 + α ^ 2) ^ 2 := by
  have h : |α| ^ 3 = |α| * |α| ^ 2 := by ring
  rw [h]
  calc |α| * |α| ^ 2 ≤ (1 + α ^ 2) * (1 + α ^ 2) :=
        mul_le_mul (abs_alpha_le_B α) (by rw [sq_abs]; nlinarith [sq_nonneg α])
          (by positivity) (by positivity)
    _ = (1 + α ^ 2) ^ 2 := by ring

lemma abs_alpha_pow4_le_B2 (α : ℝ) : |α| ^ 4 ≤ (1 + α ^ 2) ^ 2 := by
  have h : |α| ^ 4 = (|α| ^ 2) ^ 2 := by ring
  rw [h]
  have h2 : |α| ^ 2 ≤ 1 + α ^ 2 := by rw [sq_abs]; nlinarith [sq_nonneg α]
  exact pow_le_pow_left₀ (by positivity) h2 2

/-! ## The explicit polynomials in a canonical (sum-of-signed-terms) shape -/

lemma Pf_three_expand (u α : ℝ) :
    Pf 3 u α = α * (((-8) * u * (1 - u ^ 2)) + ((-6) * α * (u - 1 / 3) * (1 - u ^ 2))
      + (α ^ 2 * (u - 1 / 3) ^ 3)) := by
  rw [Pf_three]; ring

lemma Pf_four_expand (u α : ℝ) :
    Pf 4 u α = α * ((16 * (1 - u ^ 2) * (1 - 3 * u ^ 2))
      + (12 * α * (1 - u ^ 2) * (1 - u ^ 2))
      + ((-32) * α * u * (u - 1 / 3) * (1 - u ^ 2))
      + (((-12) * α ^ 2) * (u - 1 / 3) ^ 2 * (1 - u ^ 2))
      + (((α ^ 3) * (u - 1 / 3) ^ 2) * (u - 1 / 3) ^ 2)) := by
  rw [Pf_four]; ring

/-! ## The numerical bound on the angular polynomials -/

/-- `|Pf i u α| ≤ 1000·(1+α²)²` for `|u| ≤ 1` and `i ≤ 4`, for **every** real `α`. -/
theorem Pf_abs_le (i : ℕ) (hi : i ≤ 4) (u α : ℝ) (hu : |u| ≤ 1) :
    |Pf i u α| ≤ 1000 * (1 + α ^ 2) ^ 2 := by
  have hB : (0 : ℝ) ≤ (1 + α ^ 2) ^ 2 := by positivity
  interval_cases i
  · rw [Pf_zero, abs_one]
    nlinarith [one_add_sq_le_sq α, sq_nonneg α]
  · rw [Pf_one]
    have h1 : |u - 1 / 3| ≤ 4 / 3 := abs_u_sub_third_le_g hu
    have h2 : |α| ≤ (1 + α ^ 2) ^ 2 := abs_alpha_le_B2 α
    calc |α * ((3 * u - 1) / 3)|
        = |α| * |u - 1 / 3| := by
          rw [show (3 * u - 1) / 3 = u - 1 / 3 by ring, abs_mul]
      _ ≤ (1 + α ^ 2) ^ 2 * (4 / 3) := mul_le_mul h2 h1 (abs_nonneg _) hB
      _ ≤ 1000 * (1 + α ^ 2) ^ 2 := by nlinarith
  · rw [Pf_two, abs_mul]
    have h1 : |(-2) * (1 - u ^ 2)| ≤ 2 := by
      rw [abs_mul, show |(-2 : ℝ)| = 2 from by norm_num]
      linarith [abs_one_sub_sq_le_one_g hu]
    have h2 : |α * (3 * u - 1) ^ 2 / 9| ≤ (16 / 9) * |α| := by
      rw [abs_div, show |(9 : ℝ)| = 9 from by norm_num, abs_mul]
      have hs : |(3 * u - 1) ^ 2| ≤ 16 := by
        rw [abs_pow]
        have h3 := abs_three_u_sub_one_le_four_g hu
        nlinarith [abs_nonneg (3 * u - 1)]
      have hmul : |α| * |(3 * u - 1) ^ 2| ≤ |α| * 16 :=
        mul_le_mul_of_nonneg_left hs (abs_nonneg α)
      linarith
    have hX : |(-2) * (1 - u ^ 2) + α * (3 * u - 1) ^ 2 / 9| ≤ 2 + (16 / 9) * |α| := by
      have h := abs_add_le ((-2) * (1 - u ^ 2)) (α * (3 * u - 1) ^ 2 / 9)
      linarith
    have hα : |α| ≤ (1 + α ^ 2) ^ 2 := abs_alpha_le_B2 α
    have hα2 : |α| ^ 2 ≤ (1 + α ^ 2) ^ 2 := abs_alpha_sq_le_B2 α
    have hstep : |α| * |(-2) * (1 - u ^ 2) + α * (3 * u - 1) ^ 2 / 9|
        ≤ |α| * (2 + (16 / 9) * |α|) := mul_le_mul_of_nonneg_left hX (abs_nonneg α)
    nlinarith [hstep, hα, hα2, hB]
  · rw [Pf_three_expand, abs_mul]
    have h1 : |1 - u ^ 2| ≤ 1 := abs_one_sub_sq_le_one_g hu
    have h3 : |u - 1 / 3| ≤ 4 / 3 := abs_u_sub_third_le_g hu
    have ht1 : |(-8) * u * (1 - u ^ 2)| ≤ 8 := by
      have h := abs_prod3_le (a := (-8)) (b := u) (c := 1 - u ^ 2) (A := 8) (B := 1) (C := 1)
        (by norm_num) hu h1 (by norm_num) (by norm_num)
      linarith
    have ht2 : |(-6) * α * (u - 1 / 3) * (1 - u ^ 2)| ≤ 8 * |α| := by
      have h := abs_prod4_le (a := (-6)) (b := α) (c := u - 1 / 3) (d := 1 - u ^ 2)
        (A := 6) (B := |α|) (C := 4 / 3) (D := 1)
        (by norm_num) (le_refl |α|) h3 h1 (by norm_num) (abs_nonneg α) (by norm_num)
      linarith
    have ht3 : |α ^ 2 * (u - 1 / 3) ^ 3| ≤ (64 / 27) * |α| ^ 2 := by
      rw [show α ^ 2 * (u - 1 / 3) ^ 3 = α * α * (u - 1 / 3) * (u - 1 / 3) * (u - 1 / 3)
        by ring]
      have h := abs_prod5_le (a := α) (b := α) (c := u - 1 / 3) (d := u - 1 / 3) (e := u - 1 / 3)
        (A := |α|) (B := |α|) (C := 4 / 3) (D := 4 / 3) (E := 4 / 3)
        (le_refl |α|) (le_refl |α|) h3 h3 h3
        (abs_nonneg α) (abs_nonneg α) (by norm_num) (by norm_num)
      linarith
    have hX : |((-8) * u * (1 - u ^ 2)) + ((-6) * α * (u - 1 / 3) * (1 - u ^ 2))
        + (α ^ 2 * (u - 1 / 3) ^ 3)| ≤ 8 + 8 * |α| + (64 / 27) * |α| ^ 2 :=
      abs_add3_le ht1 ht2 ht3
    have hstep := mul_le_mul_of_nonneg_left hX (abs_nonneg α)
    have hα : |α| ≤ (1 + α ^ 2) ^ 2 := abs_alpha_le_B2 α
    have hα2 : |α| ^ 2 ≤ (1 + α ^ 2) ^ 2 := abs_alpha_sq_le_B2 α
    have hα3 : |α| ^ 3 ≤ (1 + α ^ 2) ^ 2 := abs_alpha_cube_le_B2 α
    nlinarith [hstep, hα, hα2, hα3, hB]
  · rw [Pf_four_expand, abs_mul]
    have h1 : |1 - u ^ 2| ≤ 1 := abs_one_sub_sq_le_one_g hu
    have h2 : |1 - 3 * u ^ 2| ≤ 2 := abs_one_sub_three_sq_le_two_g hu
    have h3 : |u - 1 / 3| ≤ 4 / 3 := abs_u_sub_third_le_g hu
    have h3sq : |(u - 1 / 3) ^ 2| ≤ 16 / 9 := by
      rw [abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) h3 2).trans_eq (by norm_num)
    have h12a : |12 * α| ≤ 12 * |α| := by
      rw [abs_mul, show |(12 : ℝ)| = 12 from by norm_num]
    have h12a2 : |(-12) * α ^ 2| ≤ 12 * |α| ^ 2 := by
      rw [abs_mul, abs_pow, show |(-12 : ℝ)| = 12 from by norm_num]
    have h32a : |(-32) * α| ≤ 32 * |α| := by
      rw [abs_mul, show |(-32 : ℝ)| = 32 from by norm_num]
    have ha3 : |α ^ 3| ≤ |α| ^ 3 := by rw [abs_pow]
    have ht1 : |16 * (1 - u ^ 2) * (1 - 3 * u ^ 2)| ≤ 32 := by
      have h := abs_prod3_le (a := 16) (b := 1 - u ^ 2) (c := 1 - 3 * u ^ 2)
        (A := 16) (B := 1) (C := 2) (by norm_num) h1 h2 (by norm_num) (by norm_num)
      linarith
    have ht2 : |12 * α * (1 - u ^ 2) * (1 - u ^ 2)| ≤ 12 * |α| := by
      have h := abs_prod3_le (a := 12 * α) (b := 1 - u ^ 2) (c := 1 - u ^ 2)
        (A := 12 * |α|) (B := 1) (C := 1) h12a h1 h1 (by positivity) (by norm_num)
      linarith
    have ht3 : |(-32) * α * u * (u - 1 / 3) * (1 - u ^ 2)| ≤ (128 / 3) * |α| := by
      have h := abs_prod4_le (a := (-32) * α) (b := u) (c := u - 1 / 3) (d := 1 - u ^ 2)
        (A := 32 * |α|) (B := 1) (C := 4 / 3) (D := 1)
        h32a hu h3 h1 (by positivity) (by norm_num) (by norm_num)
      linarith
    have ht4 : |((-12) * α ^ 2) * (u - 1 / 3) ^ 2 * (1 - u ^ 2)| ≤ (64 / 3) * |α| ^ 2 := by
      have h := abs_prod3_le (a := (-12) * α ^ 2) (b := (u - 1 / 3) ^ 2) (c := 1 - u ^ 2)
        (A := 12 * |α| ^ 2) (B := 16 / 9) (C := 1) h12a2 h3sq h1 (by positivity) (by norm_num)
      linarith
    have ht5 : |((α ^ 3) * (u - 1 / 3) ^ 2) * (u - 1 / 3) ^ 2| ≤ (256 / 81) * |α| ^ 3 := by
      have h := abs_prod3_le (a := α ^ 3) (b := (u - 1 / 3) ^ 2) (c := (u - 1 / 3) ^ 2)
        (A := |α| ^ 3) (B := 16 / 9) (C := 16 / 9) ha3 h3sq h3sq (by positivity) (by norm_num)
      linarith
    have hX : |(16 * (1 - u ^ 2) * (1 - 3 * u ^ 2))
        + (12 * α * (1 - u ^ 2) * (1 - u ^ 2))
        + ((-32) * α * u * (u - 1 / 3) * (1 - u ^ 2))
        + (((-12) * α ^ 2) * (u - 1 / 3) ^ 2 * (1 - u ^ 2))
        + (((α ^ 3) * (u - 1 / 3) ^ 2) * (u - 1 / 3) ^ 2)|
        ≤ 32 + 12 * |α| + (128 / 3) * |α| + (64 / 3) * |α| ^ 2 + (256 / 81) * |α| ^ 3 :=
      abs_add5_le ht1 ht2 ht3 ht4 ht5
    have hstep := mul_le_mul_of_nonneg_left hX (abs_nonneg α)
    have hα : |α| ≤ (1 + α ^ 2) ^ 2 := abs_alpha_le_B2 α
    have hα2 : |α| ^ 2 ≤ (1 + α ^ 2) ^ 2 := abs_alpha_sq_le_B2 α
    have hα3 : |α| ^ 3 ≤ (1 + α ^ 2) ^ 2 := abs_alpha_cube_le_B2 α
    have hα4 : |α| ^ 4 ≤ (1 + α ^ 2) ^ 2 := abs_alpha_pow4_le_B2 α
    nlinarith [hstep, hα, hα2, hα3, hα4, hB]

/-! ## The angular jet bound -/


end Work.FTS.StrongPersist.Degen
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.BslOp_tower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK

theorem BslOp_tower (α : ℝ) {Ψ : ℝ → ℝ → ℝ} {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (h00 : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → Ψ z θ = F 0 0 z θ)
    (hdz : ∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z)
    (hdth : ∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Elliptic.bslOp α Ψ z θ
      = -(α ^ 2) * (F 2 0 z θ - F 1 0 z θ) - (α * (5 + α)) * F 1 0 z θ
        - (F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ) / (Real.sin (2 * θ)) ^ 2
        + Real.tan θ * (F 0 1 z θ / Real.sin (2 * θ))
        + (Real.tan θ ^ 2 - 5) * F 0 0 z θ := by
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  -- the basic local data at `(z,θ)`
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hθmem : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hsin0 : Real.sin (2 * θ) ≠ 0 := by
    have : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    positivity
  have hcos0 : Real.cos θ ≠ 0 := by
    have h := Real.cos_pos_of_mem_Ioo (show θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    positivity
  have hΨ_eq : Ψ z θ = F 0 0 z θ := h00 z θ hzθ
  -- `Ψ` agrees with `F 0 0` near `(z,θ)`, slicewise
  have hnbz : (fun z' : ℝ => Ψ z' θ) =ᶠ[nhds z] (fun z' : ℝ => F 0 0 z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h00 z' θ ⟨hz', hθ0, hθ1⟩
  have hnbt : (fun θ' : ℝ => Ψ z θ') =ᶠ[nhds θ] (fun θ' : ℝ => F 0 0 z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθmem] with θ' hθ'
    exact h00 z θ' ⟨hz, hθ'.1, hθ'.2⟩
  -- first derivatives of `Ψ` from the tower
  have hpzΨ : Work.Spaces.pz Ψ z θ = F 1 0 z θ / z := by
    have h := (hdz 0 0 (by norm_num) z θ hzθ).congr_of_eventuallyEq hnbz
    simpa only [Work.Spaces.pz] using h.deriv
  have hΨθ : HasDerivAt (fun θ' : ℝ => Ψ z θ') (F 0 1 z θ / Real.sin (2 * θ)) θ :=
    (hdth 0 0 (by norm_num) z θ hzθ).congr_of_eventuallyEq hnbt
  -- the neighbourhood form of `∂_zΨ = F 1 0 / z`, used to differentiate once more
  have hpzΨ_nb : (fun z' : ℝ => Work.Spaces.pz Ψ z' θ) =ᶠ[nhds z]
      (fun z' : ℝ => F 1 0 z' θ / z') := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    have hnb : (fun z'' : ℝ => Ψ z'' θ) =ᶠ[nhds z'] (fun z'' : ℝ => F 0 0 z'' θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz'] with z'' hz''
      exact h00 z'' θ ⟨hz'', hθ0, hθ1⟩
    have h := (hdz 0 0 (by norm_num) z' θ ⟨hz', hθ0, hθ1⟩).congr_of_eventuallyEq hnb
    simpa only [Work.Spaces.pz] using h.deriv
  -- `∂_z²Ψ`: differentiate `z' ↦ F 1 0 z' θ / z'`
  have hpz2 : Work.Spaces.pzIter 2 Ψ z θ = (F 2 0 z θ - F 1 0 z θ) / z ^ 2 := by
    have hd : HasDerivAt (fun z' : ℝ => F 1 0 z' θ / z')
        ((F 2 0 z θ / z * z - F 1 0 z θ * 1) / z ^ 2) z :=
      (hdz 1 0 (by norm_num) z θ hzθ).div (hasDerivAt_id z) hz0
    have h2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pz Ψ z' θ)
        ((F 2 0 z θ / z * z - F 1 0 z θ * 1) / z ^ 2) z :=
      hd.congr_of_eventuallyEq hpzΨ_nb
    show deriv (fun z' : ℝ => Work.Spaces.pz Ψ z' θ) z = (F 2 0 z θ - F 1 0 z θ) / z ^ 2
    rw [h2.deriv]
    field_simp
  -- the neighbourhood form of `∂_θΨ = F 0 1 / sin 2θ`
  have hpthΨ_nb : (fun θ' : ℝ => Work.Spaces.pth Ψ z θ') =ᶠ[nhds θ]
      (fun θ' : ℝ => F 0 1 z θ' / Real.sin (2 * θ')) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθmem] with θ' hθ'
    have hnb : (fun θ'' : ℝ => Ψ z θ'') =ᶠ[nhds θ'] (fun θ'' : ℝ => F 0 0 z θ'') := by
      filter_upwards [isOpen_Ioo.mem_nhds (show θ' ∈ Set.Ioo 0 (Real.pi / 2) from hθ')]
        with θ'' hθ''
      exact h00 z θ'' ⟨hz, hθ''.1, hθ''.2⟩
    have h := (hdth 0 0 (by norm_num) z θ' ⟨hz, hθ'.1, hθ'.2⟩).congr_of_eventuallyEq hnb
    simpa only [Work.Spaces.pth] using h.deriv
  -- `∂_θ²Ψ`: differentiate `θ' ↦ F 0 1 z θ' / sin 2θ'`
  have hpth2 : Work.Spaces.pthIter 2 Ψ z θ
      = (F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ) / (Real.sin (2 * θ)) ^ 2 := by
    have hd2 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
      have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
      exact h.congr_deriv (by ring)
    have hd : HasDerivAt (fun θ' : ℝ => F 0 1 z θ' / Real.sin (2 * θ'))
        ((F 0 2 z θ / Real.sin (2 * θ) * Real.sin (2 * θ)
          - F 0 1 z θ * (2 * Real.cos (2 * θ))) / (Real.sin (2 * θ)) ^ 2) θ :=
      (hdth 0 1 (by norm_num) z θ hzθ).div hd2 hsin0
    have h2 : HasDerivAt (fun θ' : ℝ => Work.Spaces.pth Ψ z θ')
        ((F 0 2 z θ / Real.sin (2 * θ) * Real.sin (2 * θ)
          - F 0 1 z θ * (2 * Real.cos (2 * θ))) / (Real.sin (2 * θ)) ^ 2) θ :=
      hd.congr_of_eventuallyEq hpthΨ_nb
    show deriv (fun θ' : ℝ => Work.Spaces.pth Ψ z θ') θ
      = (F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ) / (Real.sin (2 * θ)) ^ 2
    rw [h2.deriv]
    field_simp
  -- `sec²θ = 1 + tan²θ`
  have htan_sq : (1 : ℝ) / Real.cos θ ^ 2 = 1 + Real.tan θ ^ 2 := by
    rw [Real.tan_eq_sin_div_cos, div_pow]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq θ]
  -- the `∂_θ(tan θ · Ψ)` term
  have htan : Work.Spaces.pth (fun a b => Real.tan b * Ψ a b) z θ
      = (1 + Real.tan θ ^ 2) * F 0 0 z θ + Real.tan θ * (F 0 1 z θ / Real.sin (2 * θ)) := by
    have hprod : HasDerivAt (fun b : ℝ => Real.tan b * Ψ z b)
        ((1 + Real.tan θ ^ 2) * F 0 0 z θ + Real.tan θ * (F 0 1 z θ / Real.sin (2 * θ))) θ := by
      have h := (Real.hasDerivAt_tan hcos0).mul hΨθ
      refine h.congr_deriv ?_
      rw [htan_sq, hΨ_eq]
    show deriv (fun b : ℝ => Real.tan b * Ψ z b) θ = _
    rw [hprod.deriv]
  -- the substituted operator identity
  have key : -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
        - (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ
      + (-(Work.Spaces.pthIter 2 Ψ z θ)
        + Work.Spaces.pth (fun a b => Real.tan b * Ψ a b) z θ - 6 * Ψ z θ)
      = -(α ^ 2) * (F 2 0 z θ - F 1 0 z θ) - (α * (5 + α)) * F 1 0 z θ
        - (F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ) / (Real.sin (2 * θ)) ^ 2
        + Real.tan θ * (F 0 1 z θ / Real.sin (2 * θ))
        + (Real.tan θ ^ 2 - 5) * F 0 0 z θ := by
    rw [hpz2, hpzΨ, hpth2, htan, hΨ_eq]
    field_simp
    ring
  rw [Work.Elliptic.bslOp_apply]
  exact key

end Work.FTS_EllLimOK
end
-- ===== merged: Submission.Work.FTS_EllLimOK.LimDefs =====
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

/-- The growth weight of `Closed.LocalBound`:
`(1 + 1/z + 1/(θ(π/2-θ))) / (1+z)`.  It is continuous (hence locally bounded) on the open
quadrant, and decays like `1/z` in the far field. -/
def wt (z θ : ℝ) : ℝ := (1 + 1 / z + 1 / (θ * (π / 2 - θ))) / (1 + z)

/-- The six pairs `(j,i)` with `j + i ≤ 2`, in a fixed order. -/
def P6 : Fin 6 → ℕ × ℕ := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0)]

/-- The `Fin 6`-valued vector of the six mixed jets of order `≤ 2` of `G n` at the point `p`. -/
def fam6 (G : ℕ → ℝ → ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) : Fin 6 → ℝ :=
  fun m => Work.Spaces.mixed (P6 m).1 (P6 m).2 (G n) p.1 p.2




end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.LimDefs10 =====
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

/-- The ten pairs `(j,i)` with `j + i ≤ 3`, in a fixed order. -/
def P10 : Fin 10 → ℕ × ℕ :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (3, 0)]

/-- The `Fin 10`-valued vector of the ten mixed jets of order `≤ 3` of `G n` at the point `p`. -/
def fam10 (G : ℕ → ℝ → ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) : Fin 10 → ℝ :=
  fun m => Work.Spaces.mixed (P10 m).1 (P10 m).2 (G n) p.1 p.2

/-- Every pair occurring in the list `P10` has total order at most `3`. -/
theorem P10_sum_le_three (m : Fin 10) : (P10 m).1 + (P10 m).2 ≤ 3 := by
  fin_cases m <;> decide

/-- Every pair `(c,d)` with `c + d ≤ 3` occurs in the list `P10`. -/
theorem P10_surj (c d : ℕ) (h : c + d ≤ 3) : ∃ m : Fin 10, P10 m = (c, d) := by
  have hc : c ≤ 3 := by omega
  have hd : d ≤ 3 := by omega
  interval_cases c <;> interval_cases d <;> first
    | exact ⟨0, by decide⟩
    | exact ⟨1, by decide⟩
    | exact ⟨2, by decide⟩
    | exact ⟨3, by decide⟩
    | exact ⟨4, by decide⟩
    | exact ⟨5, by decide⟩
    | exact ⟨6, by decide⟩
    | exact ⟨7, by decide⟩
    | exact ⟨8, by decide⟩
    | exact ⟨9, by decide⟩
    | (exfalso; omega)

/-- The index of a pair `(c,d)` with `c + d ≤ 3` in the list `P10`. -/
noncomputable def idx10 (c d : ℕ) : Fin 10 :=
  if h : c + d ≤ 3 then Classical.choose (P10_surj c d h) else 0

/-- The characteristic property of `idx10`. -/
theorem idx10_spec {c d : ℕ} (h : c + d ≤ 3) : P10 (idx10 c d) = (c, d) := by
  rw [idx10, dif_pos h]
  exact Classical.choose_spec (P10_surj c d h)

end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.LimTower_identify =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS_EllLimOK

/-! ## The definitional towers for `mixed`

`mixed (c+1) d X` is `Dz (mixed c d X)` definitionally, so its value at `(z,θ)` is
`z` times the `z`-derivative of the `θ`-slice of `mixed c d X`.  Likewise
`mixed 0 (d+1) X = Dth (mixed 0 d X)`, whose value is `sin(2θ)` times the
`θ`-derivative of the `z`-slice.  These two identities are pure unfolding, and they
are what turns the recurrence hypotheses on `F` into the identification with
`mixed c d (F 0 0)`. -/

theorem mixed_z_succ (X : ℝ → ℝ → ℝ) (c d : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed (c + 1) d X z θ
      = z * deriv (fun z' => Work.Spaces.mixed c d X z' θ) z := by
  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]

theorem mixed_th_succ (X : ℝ → ℝ → ℝ) (d : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed 0 (d + 1) X z θ
      = Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.mixed 0 d X z θ') θ := by
  simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Work.Spaces.DzIter_zero,
    Work.Spaces.Dth, Work.Spaces.pth]

theorem LimTower_identify {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (hdz : ∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z)
    (hdth : ∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ) :
    ∀ (c d : ℕ), c + d ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      F c d z θ = Work.Spaces.mixed c d (F 0 0) z θ := by
  -- The first-order identifications, from the two recurrence hypotheses at `(0,0)`.
  have one_z : ∀ (z' θ' : ℝ), (z', θ') ∈ Work.FTS.EllipticEst.Q0 →
      F 1 0 z' θ' = Work.Spaces.mixed 1 0 (F 0 0) z' θ' := by
    intro z' θ' hz'
    obtain ⟨hzp, hθ'0, hθ'1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hz'
    have hd := (hdz 0 0 (by norm_num) z' θ' hz').deriv
    rw [Work.Spaces.mixed]
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero,
      Work.Spaces.Dz, Work.Spaces.pz]
    rw [hd, mul_comm z' (F 1 0 z' θ' / z'), div_mul_cancel₀ (F 1 0 z' θ') (ne_of_gt hzp)]
  have one_th : ∀ (z' θ' : ℝ), (z', θ') ∈ Work.FTS.EllipticEst.Q0 →
      F 0 1 z' θ' = Work.Spaces.mixed 0 1 (F 0 0) z' θ' := by
    intro z' θ' hz'
    obtain ⟨hzp, hθ'0, hθ'1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hz'
    have hsin' : Real.sin (2 * θ') ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
    have hd := (hdth 0 0 (by norm_num) z' θ' hz').deriv
    rw [Work.Spaces.mixed]
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero,
      Work.Spaces.Dth, Work.Spaces.pth]
    rw [hd, mul_comm (Real.sin (2 * θ')) (F 0 1 z' θ' / Real.sin (2 * θ')),
      div_mul_cancel₀ (F 0 1 z' θ') hsin']
  -- The second-order identifications, by transferring the slice derivative from `F` to
  -- `mixed` along the first-order identification (valid on the open quadrant, hence on a
  -- neighbourhood of the point).
  have two_z : ∀ (z' θ' : ℝ), (z', θ') ∈ Work.FTS.EllipticEst.Q0 →
      F 2 0 z' θ' = Work.Spaces.mixed 2 0 (F 0 0) z' θ' := by
    intro z' θ' hz'
    obtain ⟨hzp, hθ'0, hθ'1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hz'
    have hev : (fun z'' => F 1 0 z'' θ') =ᶠ[𝓝 z']
        (fun z'' => Work.Spaces.mixed 1 0 (F 0 0) z'' θ') := by
      filter_upwards [isOpen_Ioi.mem_nhds hzp] with z'' hz''
      exact one_z z'' θ' (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz'', hθ'0, hθ'1⟩)
    have hd : HasDerivAt (fun z'' => Work.Spaces.mixed 1 0 (F 0 0) z'' θ')
        (F 2 0 z' θ' / z') z' :=
      (hdz 1 0 (by norm_num) z' θ' hz').congr_of_eventuallyEq hev.symm
    rw [mixed_z_succ (F 0 0) 1 0 z' θ', hd.deriv,
      mul_comm z' (F 2 0 z' θ' / z'), div_mul_cancel₀ (F 2 0 z' θ') (ne_of_gt hzp)]
  have one_one : ∀ (z' θ' : ℝ), (z', θ') ∈ Work.FTS.EllipticEst.Q0 →
      F 1 1 z' θ' = Work.Spaces.mixed 1 1 (F 0 0) z' θ' := by
    intro z' θ' hz'
    obtain ⟨hzp, hθ'0, hθ'1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hz'
    have hev : (fun z'' => F 0 1 z'' θ') =ᶠ[𝓝 z']
        (fun z'' => Work.Spaces.mixed 0 1 (F 0 0) z'' θ') := by
      filter_upwards [isOpen_Ioi.mem_nhds hzp] with z'' hz''
      exact one_th z'' θ' (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz'', hθ'0, hθ'1⟩)
    have hd : HasDerivAt (fun z'' => Work.Spaces.mixed 0 1 (F 0 0) z'' θ')
        (F 1 1 z' θ' / z') z' :=
      (hdz 0 1 (by norm_num) z' θ' hz').congr_of_eventuallyEq hev.symm
    rw [mixed_z_succ (F 0 0) 0 1 z' θ', hd.deriv,
      mul_comm z' (F 1 1 z' θ' / z'), div_mul_cancel₀ (F 1 1 z' θ') (ne_of_gt hzp)]
  have two_th : ∀ (z' θ' : ℝ), (z', θ') ∈ Work.FTS.EllipticEst.Q0 →
      F 0 2 z' θ' = Work.Spaces.mixed 0 2 (F 0 0) z' θ' := by
    intro z' θ' hz'
    obtain ⟨hzp, hθ'0, hθ'1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hz'
    have hsin' : Real.sin (2 * θ') ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
    have hev : (fun θ'' => F 0 1 z' θ'') =ᶠ[𝓝 θ']
        (fun θ'' => Work.Spaces.mixed 0 1 (F 0 0) z' θ'') := by
      filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ'0, hθ'1⟩] with θ'' hθ''
      exact one_th z' θ'' (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzp, hθ''.1, hθ''.2⟩)
    have hd : HasDerivAt (fun θ'' => Work.Spaces.mixed 0 1 (F 0 0) z' θ'')
        (F 0 2 z' θ' / Real.sin (2 * θ')) θ' :=
      (hdth 0 1 (by norm_num) z' θ' hz').congr_of_eventuallyEq hev.symm
    rw [mixed_th_succ (F 0 0) 1 z' θ', hd.deriv,
      mul_comm (Real.sin (2 * θ')) (F 0 2 z' θ' / Real.sin (2 * θ')),
      div_mul_cancel₀ (F 0 2 z' θ') hsin']
  -- Since `c + d ≤ 2`, both `c,d ≤ 2`; dispatch on the (at most six) possibilities.
  intro c d hcd z θ hzθ
  have hc2 : c ≤ 2 := by omega
  have hd2 : d ≤ 2 := by omega
  interval_cases c <;> interval_cases d <;> first
    | exact one_z z θ hzθ
    | exact one_th z θ hzθ
    | exact one_one z θ hzθ
    | exact two_z z θ hzθ
    | exact two_th z θ hzθ
    | rfl
    | omega

end Work.FTS_EllLimOK
end
-- ===== merged: Submission.Work.FTS_EllLimOK.Pinning.integrableOn_cos_sq_rpow_tail =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Pinning integrability: the `(η+4)`-weighted `cos²·Ψ²` tail

The pinning argument at the corner `θ = π/2` consumes the integrability of the *tail*

`θ ↦ (cos θ · Ψ z θ)² · sin(2θ)^{-(η+4)}` on `(π/6, π/2)`

from the integrability of the `ℋ`-type integrand `(Ψ z θ / cos θ)² · sin(2θ)^{-η}` on the
closed angular interval.  The two integrands differ pointwise by the factor

`cos⁴θ · sin(2θ)^{-4} = 1 / (16 sin⁴θ)`,

and on `(π/6, π/2)` we have `sin θ ≥ 1/2`, so this factor is `≤ 1`.  Hence the tail is
dominated by the given integrand and integrability transfers by `Integrable.mono'`.
-/

namespace Work.FTS_EllLimOK.Pinning

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-- **Pointwise comparison.**  If `0 < c ≤ S` then the `(η+4)`-weighted square is dominated by
the `η`-weighted one:

`|(c p)² S^{-(η+4)}| ≤ (p/c)² S^{-η}`.

Indeed the quotient of the two sides is `c⁴ S^{-4} ≤ 1`, which is exactly `c⁴ ≤ S⁴`. -/
private lemma abs_cos_mul_sq_rpow_le {η c p S : ℝ} (hc : 0 < c) (hS : 0 < S) (hcs : c ≤ S) :
    |(c * p) ^ 2 * S ^ (-(η + 4))| ≤ (p / c) ^ 2 * S ^ (-η) := by
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have hS4 : (0 : ℝ) < S ^ 4 := by positivity
  have hc4le : c ^ 4 ≤ S ^ 4 := pow_le_pow_left₀ hc.le hcs 4
  have hSinv : S ^ (-4 : ℝ) = (S ^ 4)⁻¹ := by
    rw [Real.rpow_neg hS.le]
    norm_num
  -- `c⁴ / S⁴ ≤ 1`
  have hmain : c ^ 4 * (S ^ 4)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact div_le_one_of_le₀ hc4le hS4.le
  -- `c² / S⁴ ≤ 1 / c²`
  have hratio : c ^ 2 * (S ^ 4)⁻¹ ≤ (c ^ 2)⁻¹ := by
    have h1 : (c ^ 2 * (S ^ 4)⁻¹) * c ^ 2 ≤ ((c ^ 2)⁻¹) * c ^ 2 := by
      rw [show (c ^ 2 * (S ^ 4)⁻¹) * c ^ 2 = c ^ 4 * (S ^ 4)⁻¹ by ring,
        inv_mul_cancel₀ (ne_of_gt hc2)]
      exact hmain
    exact (mul_le_mul_iff_left₀ hc2).mp h1
  have hSpow : S ^ (-(η + 4)) = (S ^ 4)⁻¹ * S ^ (-η) := by
    rw [show -(η + 4) = -η + -4 by ring, Real.rpow_add hS, hSinv]
    ring
  have hnn : 0 ≤ (c * p) ^ 2 * S ^ (-(η + 4)) :=
    mul_nonneg (sq_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hS _))
  rw [abs_of_nonneg hnn, mul_pow, hSpow]
  calc c ^ 2 * p ^ 2 * ((S ^ 4)⁻¹ * S ^ (-η))
      = c ^ 2 * (S ^ 4)⁻¹ * (p ^ 2 * S ^ (-η)) := by ring
    _ ≤ (c ^ 2)⁻¹ * (p ^ 2 * S ^ (-η)) :=
        mul_le_mul_of_nonneg_right hratio
          (mul_nonneg (sq_nonneg p) (le_of_lt (Real.rpow_pos_of_pos hS _)))
    _ = (p / c) ^ 2 * S ^ (-η) := by rw [div_pow, div_eq_mul_inv]; ring

theorem integrableOn_cos_sq_rpow_tail {η : ℝ} {Ψ : ℝ → ℝ → ℝ} {z : ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) (hz : 0 < z)
    (h : MeasureTheory.IntegrableOn
      (fun θ => (Ψ z θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ => (Real.cos θ * Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(η + 4)))
      (Set.Ioo (Real.pi / 6) (Real.pi / 2)) := by
  set s : Set ℝ := Set.Ioo (Real.pi / 6) (Real.pi / 2)
  have hs_meas : MeasurableSet s := measurableSet_Ioo
  -- the interval is contained in the closed angular interval
  have hsub : s ⊆ Work.Spaces.Iθ := fun _ hx =>
    ⟨le_of_lt (by linarith [Real.pi_pos, hx.1]), le_of_lt hx.2⟩
  have hH : IntegrableOn (fun θ : ℝ => (Ψ z θ / Real.cos θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-η)) s := h.mono_set hsub
  -- positivity of `sin 2θ` and `cos θ` on `s`
  have hSpos : ∀ θ ∈ s, 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos]) (by linarith [hθ.2])
  have hcpos : ∀ θ ∈ s, 0 < Real.cos θ := fun θ hθ =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  -- and `cos θ ≤ sin 2θ`, because `sin θ ≥ sin (π/6) = 1/2`
  have hcS : ∀ θ ∈ s, Real.cos θ ≤ Real.sin (2 * θ) := by
    intro θ hθ
    have hsin : (1 : ℝ) / 2 ≤ Real.sin θ := by
      have h1 := Real.sin_le_sin_of_le_of_le_pi_div_two
        (x := Real.pi / 6) (y := θ) (by linarith [Real.pi_pos]) (le_of_lt hθ.2) (le_of_lt hθ.1)
      rwa [Real.sin_pi_div_six] at h1
    rw [Real.sin_two_mul]
    nlinarith [hsin, (hcpos θ hθ).le]
  -- the tail integrand is continuous on `s`
  have hcont : ContinuousOn (fun θ : ℝ => (Real.cos θ * Ψ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(η + 4))) s := by
    have hΨ : ContinuousOn (fun θ : ℝ => Ψ z θ) s :=
      ((hsm.curry_θ hz).continuousOn).mono fun _ hθ =>
        ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    exact ((Real.continuous_cos.continuousOn.mul hΨ).pow 2).mul
      (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        fun _ hθ => Or.inl (ne_of_gt (hSpos _ hθ)))
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => (Real.cos θ * Ψ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(η + 4))) (volume.restrict s) :=
    hcont.aestronglyMeasurable hs_meas
  change Integrable (fun θ : ℝ => (Real.cos θ * Ψ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(η + 4))) (volume.restrict s)
  refine Integrable.mono' hH hmeas ?_
  rw [MeasureTheory.ae_restrict_iff' hs_meas]
  exact Filter.Eventually.of_forall fun θ hθ =>
    abs_cos_mul_sq_rpow_le (hS := hSpos θ hθ) (hc := hcpos θ hθ) (hcs := hcS θ hθ)

end Work.FTS_EllLimOK.Pinning
end
-- ===== merged: Submission.Work.FTS_EllLimOK.Pinning.smoothOpen_div_cos =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.Pinning

open scoped Real Topology
open MeasureTheory Set Filter

/-- **`SmoothOpen` is stable under division by `cos θ`.**  On the open quadrant
`Q0 = (0,∞) × (0,π/2)` one has `cos θ ≠ 0` (`Real.cos_pos_of_mem_Ioo`), so dividing a
function which is `C^∞` on `Q0` by the (globally `C^∞`) angular factor `cos θ` keeps it
`C^∞` on `Q0`.  This is the `cos`-analogue of `Work.Blocks.smoothOpen_div_sin`. -/
theorem smoothOpen_div_cos {f : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ / Real.cos θ) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := h
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.cos p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn.of_le le_top
  exact h1.div h2 (fun p hp => by
    rcases p with ⟨z, θ⟩
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩))

end Work.FTS_EllLimOK.Pinning
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.hkBundleTools =====
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
# Generic `ℋ⁰`-tools: the level-`0` integrand, domination, and slot extraction

The `ℋ⁰`-integrand of `Work.Spaces` collapses to the single square of the weighted function;
this module collects the elementary tools used to *produce* `ℋ⁰`-memberships:

* `hkIntegrand_zero_eq`, `hkIntegrand_zero_of_sin_eq_zero`: the collapse and its vanishing on
  the two angular endpoints;
* `wdivsin_nonneg`, `rpow_eta_le_rpow_gam`, `Wt_nonneg`, `wdivsin_le_Wt`: the comparison of the
  level-`0` weight with the `γ`-weight of the mixed slots (`η ≤ γ`);
* `hkMem_zero_of_majorant` and the domination corollaries `hkMem_zero_of_abs_le{,_two,_three}`:
  `ℋ⁰`-membership from a pointwise domination of the weighted function, with the domination
  required only for `z > 0` (at `z = 0` the integrand vanishes identically);
* `hkMem_zero_of_mem_DzIter`, `hkMem_zero_of_mem_mixed`: the level-`0` honesty of a single
  weighted slot `D_z^iF` resp. `D_z^jD_θ^iF` of an `ℋ^k`-function;
* `smoothOpen_div_cos`: `SmoothOpen`-closure under division by `cos θ`;
* `integrableOn_sq_Lop_iter`: the `θ`-square of an iterate of `Lop = sin(2·)∂_θ` applied to a
  function `C^∞` on an open neighbourhood of `Iθ` is integrable there (via
  `contDiffOn_infty_iff_deriv_of_isOpen`, i.e. `deriv` preserves the honest `C^∞` order on open
  sets — *not* the analytic order `⊤`).
-/

/-! ## §1  Elementary facts about the level-`0` integrand and its weight -/

/-- At level `0` the `ℋ^k`-integrand collapses to the single square of the weighted function. -/
theorem hkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]


/-- A point of `Iθ` where `sin 2θ ≠ 0` is interior. -/
theorem mem_Ioo_of_mem_Iθ_of_sin_ne {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (h : Real.sin (2 * θ) ≠ 0) : θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  refine ⟨lt_of_le_of_ne hθ.1 (Ne.symm ?_), lt_of_le_of_ne hθ.2 ?_⟩
  · intro h0; exact h (by rw [h0]; norm_num)
  · intro h2; exact h (by rw [h2, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi])

/-- `0 ≤ sin 2θ ≤ 1` on `Iθ`. -/
theorem sin_two_mem_Icc {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.sin (2 * θ) ∈ Set.Icc 0 1 :=
  ⟨Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩,
    Real.sin_le_one _⟩



/-- The product weight `W = w · w_θ` is nonnegative on `Iθ`. -/
theorem Wt_nonneg {α : ℝ} (_hα : 0 < α) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Spaces.Wt α z θ := by
  rw [Work.Spaces.Wt, Work.Spaces.w, Work.Spaces.wTheta]
  exact mul_nonneg (by positivity) (Real.rpow_nonneg (sin_two_mem_Icc hθ).1 _)


/-! ## §2  `ℋ⁰`-membership by domination -/







/-! ## §3  `SmoothOpen`-closure under division by `cos θ` -/

theorem smoothOpen_div_cos {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ / Real.cos θ) := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr (fun n => ?_)
  have hnum : ContDiffOn ℝ n (Function.uncurry F) Work.FTS.EllipticEst.Q0 := hF.forall n
  have hden : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 := by
    fun_prop
  have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.cos p.2 ≠ 0 := fun p hp =>
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hp.2.1, Real.pi_pos],
      by linarith [hp.2.2, Real.pi_pos]⟩)
  exact ContDiffOn.div hnum hden hne

/-! ## §4  Integrability of the `θ`-square of an iterated `Lop` -/



end Work.FTS_EllLimOK.PkgJets
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.H2.deriv_pz_pth_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The two second-order angular derivatives of `D_z Ψ` and `∂_z∂_θΨ` at an interior
point of the open quadrant.**

Since `D_z Ψ = z ∂_zΨ` with `z` a constant of the `θ`-differentiation, the `θ`-second
derivative of the `z`-slice of `D_z Ψ` is `z` times the `θ`-derivative of
`θ ↦ pth (pz Ψ) z θ`, and Clairaut's theorem (`Work.Spaces.pz_pth_comm`) identifies that
with the `θ`-derivative of `θ ↦ pz (pth Ψ) z θ`. -/
lemma deriv_second_DzIter_one {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter 1 Ψ z θ'') θ') θ
      = z * deriv (fun θ' => Work.Spaces.pz (Work.Spaces.pth Ψ) z θ') θ := by
  -- The `θ`-derivative of the `z`-slice of `D_z Ψ = z ∂_zΨ` is `z ∂_θ∂_zΨ`.
  have hpt : ∀ θ' : ℝ, deriv (fun θ'' => Work.Spaces.DzIter 1 Ψ z θ'') θ'
      = z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ' := by
    intro θ'
    have h1 : (fun θ'' => Work.Spaces.DzIter 1 Ψ z θ'')
        = fun θ'' => z * Work.Spaces.pz Ψ z θ'' := by
      funext θ''; rfl
    rw [h1, deriv_const_mul_field]
    rfl
  have hB : (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter 1 Ψ z θ'') θ')
      =ᶠ[𝓝 θ] (fun θ' => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ') :=
    Filter.Eventually.of_forall hpt
  -- Clairaut: `∂_θ∂_zΨ = ∂_z∂_θΨ` on the open quadrant.
  have hC : (fun θ' => Work.Spaces.pth (Work.Spaces.pz Ψ) z θ')
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pz (Work.Spaces.pth Ψ) z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    have hmem : (z, θ') ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ'.1, hθ'.2⟩
    have hcd : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ') :=
      (hsm.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
    exact (Work.Spaces.pz_pth_comm hcd).symm
  calc deriv (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter 1 Ψ z θ'') θ') θ
      = deriv (fun θ' => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ') θ := hB.deriv_eq
    _ = z * deriv (fun θ' => Work.Spaces.pth (Work.Spaces.pz Ψ) z θ') θ := by
          rw [deriv_const_mul_field]
    _ = z * deriv (fun θ' => Work.Spaces.pz (Work.Spaces.pth Ψ) z θ') θ := by
          rw [hC.deriv_eq]

theorem deriv_pz_pth_bound {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {A B M : ℝ} (hA : 0 < A) (hM : 0 ≤ M)
    (h : ∀ z ∈ Set.Icc A B, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |deriv (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter 1 Ψ z θ'') θ') θ| ≤ M) :
    ∀ z ∈ Set.Icc A B, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |deriv (fun θ' => Work.Spaces.pz (Work.Spaces.pth Ψ) z θ') θ| ≤ M / A := by
  intro z hz θ hθ
  have hzA : A ≤ z := hz.1
  have hzpos : 0 < z := lt_of_lt_of_le hA hzA
  -- The hypothesis controls `z · ∂_θ(∂_z∂_θΨ)`; divide by `z ≥ A`.
  have hh := h z hz θ hθ
  rw [deriv_second_DzIter_one hsm hzpos hθ, abs_mul, abs_of_pos hzpos] at hh
  have h1 : |deriv (fun θ' => Work.Spaces.pz (Work.Spaces.pth Ψ) z θ') θ| ≤ M / z :=
    (le_div_iff₀ hzpos).mpr (by rw [mul_comm]; exact hh)
  have h2 : M / z ≤ M / A := div_le_div_of_nonneg_left hM hA hzA
  linarith

end Work.FTS_EllLimOK.ProducerH.H2
end
-- ===== merged: Submission.Work.FTS_EllLimOK.Reconstruct =====
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
set_option maxHeartbeats 800000

/-- `cos θ` is positive on the open quadrant's angular range. -/
theorem cos_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩

/-! ## The algebraic identities between the three coefficient operators -/

/-- `cos θ · Vop Ψ = ∂_θ (cos θ · Ψ)`, in the totalised-derivative form
`cos θ · Vop Ψ = cos θ · ∂_θΨ - sin θ · Ψ`. -/
theorem cos_mul_Vop_eq (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Real.cos θ * Work.Construction.Vop Ψ z θ
      = Real.cos θ * Work.Spaces.pth Ψ z θ - Real.sin θ * Ψ z θ := by
  have hc : Real.cos θ ≠ 0 := ne_of_gt (cos_pos_of_mem_Ioo hθ)
  rw [Work.Construction.Vop, Real.tan_eq_sin_div_cos]
  field_simp



/-! ## The `θ`-reconstruction -/

/-- **The reconstruction of `Ψ` from `Vop Ψ`.**  If the slice `s ↦ Ψ z s` has derivative
`∂_θΨ(z,s)` on the open interval `(θ,π/2)`, if `cos s · Vop Ψ(z,s)` is interval-integrable, if
the slice is continuous at `θ` and if the boundary limit `cos s · Ψ(z,s) → 0` holds as
`s → π/2⁻`, then

```
Ψ(z,θ) = -(1/cos θ) · ∫_θ^{π/2} cos s · (Vop Ψ)(z,s) ds .
```

This is the fundamental theorem of calculus applied to `s ↦ cos s · Ψ(z,s)`, whose derivative is
`cos s · Vop Ψ(z,s)` by `cos_mul_Vop_eq`. -/
theorem Vop_reconstruct {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hderiv : ∀ s ∈ Set.Ioo θ (π / 2),
      HasDerivAt (fun s' => Ψ z s') (Work.Spaces.pth Ψ z s) s)
    (hint : IntervalIntegrable (fun s => Real.cos s * Work.Construction.Vop Ψ z s)
      MeasureTheory.volume θ (π / 2))
    (ha : Filter.Tendsto (fun s => Real.cos s * Ψ z s) (𝓝[>] θ) (𝓝 (Real.cos θ * Ψ z θ)))
    (hb : Filter.Tendsto (fun s => Real.cos s * Ψ z s) (𝓝[<] (π / 2)) (𝓝 0)) :
    Ψ z θ = -(1 / Real.cos θ)
      * ∫ s in θ..(π / 2), Real.cos s * Work.Construction.Vop Ψ z s := by
  have hθlt : θ < π / 2 := hθ.2
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (cos_pos_of_mem_Ioo hθ)
  -- the derivative identity on the open interval
  have hderiv' : ∀ s ∈ Set.Ioo θ (π / 2),
      HasDerivAt (fun s' => Real.cos s' * Ψ z s')
        (Real.cos s * Work.Construction.Vop Ψ z s) s := by
    intro s hs
    have hsIoo : s ∈ Set.Ioo 0 (π / 2) := ⟨lt_trans hθ.1 hs.1, hs.2⟩
    have h3 : HasDerivAt (fun s' => Real.cos s' * Ψ z s')
        (-Real.sin s * Ψ z s + Real.cos s * Work.Spaces.pth Ψ z s) s :=
      (Real.hasDerivAt_cos s).mul (hderiv s hs)
    refine h3.congr_deriv ?_
    rw [cos_mul_Vop_eq Ψ hsIoo]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hθlt hderiv' hint ha hb
  -- `∫ = 0 - cos θ * Ψ z θ`
  have h1 : Ψ z θ * Real.cos θ
      = -∫ s in θ..(π / 2), Real.cos s * Work.Construction.Vop Ψ z s := by
    rw [show (∫ s in θ..(π / 2), Real.cos s * Work.Construction.Vop Ψ z s)
        = 0 - Real.cos θ * Ψ z θ from hFTC]
    ring
  have h2 : Ψ z θ
      = (-∫ s in θ..(π / 2), Real.cos s * Work.Construction.Vop Ψ z s) / Real.cos θ := by
    rw [eq_div_iff hcos]
    exact h1
  rw [h2]
  ring


end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ThetaJets.aesm_integral_abs_Ktheta_dzIter =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ThetaJets

open MeasureTheory Set Filter
open scoped Real Topology


end Work.FTS_EllLimOK.ThetaJets
end
-- ===== merged: Submission.Work.FTS_EllLimOK.aemeasurable_uncurry_of_tendsto_Q0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK

open MeasureTheory Set Filter

open scoped Topology

/-- **A pointwise limit on the open quadrant is a.e. strongly measurable** for the measure
`(dz|_{Iz}) × (dθ|_{Iθ})` of the elliptic estimates: continuity of the approximants is only
assumed on the open quadrant `(0,∞) × (0,π/2)` and the convergence only there, but the
boundary of the quadrant is null for the measure, so the (otherwise completely arbitrary)
boundary values of the limit are irrelevant. -/
theorem aemeasurable_uncurry_of_tendsto_Q0 {un : ℕ → ℝ → ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hcont : ∀ n : ℕ, ContinuousOn (Function.uncurry (un n)) Work.FTS.EllipticEst.Q0)
    (hconv : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Filter.Tendsto (fun n => un n z θ) Filter.atTop (nhds (u z θ))) :
    AEMeasurable (Function.uncurry u)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  classical
  set ν := (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ) with hν
  have hQmeas : MeasurableSet Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  -- The limit, restricted to the open quadrant, is the pointwise limit of the continuous
  -- functions `un`, hence Borel measurable there.
  have hlim : Measurable (Work.FTS.EllipticEst.Q0.domRestrict (Function.uncurry u)) := by
    refine measurable_of_tendsto_metrizable
      (f := fun n => Work.FTS.EllipticEst.Q0.domRestrict (Function.uncurry (un n)))
      (fun n => ?_) ?_
    · exact (hcont n).domRestrict.measurable
    · exact tendsto_pi_nhds.mpr (fun p => hconv p.1.1 p.1.2 p.2)
  -- Extend by zero off the quadrant.
  have hG : Measurable (fun p : ℝ × ℝ =>
      if p ∈ Work.FTS.EllipticEst.Q0 then u p.1 p.2 else 0) := by
    refine measurable_of_restrict_of_restrict_compl hQmeas ?_ ?_
    · have heq : (Work.FTS.EllipticEst.Q0.domRestrict
          (fun p : ℝ × ℝ => if p ∈ Work.FTS.EllipticEst.Q0 then u p.1 p.2 else 0))
          = Work.FTS.EllipticEst.Q0.domRestrict (Function.uncurry u) := by
        funext p
        simp only [Set.domRestrict, Function.uncurry]
        exact ite_eq_left p.2
      rw [heq]; exact hlim
    · have heq : (((Work.FTS.EllipticEst.Q0)ᶜ).domRestrict
          (fun p : ℝ × ℝ => if p ∈ Work.FTS.EllipticEst.Q0 then u p.1 p.2 else 0))
          = fun _ => (0 : ℝ) := by
        funext p
        simp only [Set.domRestrict]
        exact ite_eq_right p.2
      rw [heq]; exact measurable_const
  -- `ν` is the planar Lebesgue measure restricted to `Iz × Iθ`.
  have hνeq : ν = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [hν]
    exact Measure.prod_restrict _ _
  -- The complement of the open quadrant inside `Iz × Iθ` is null.
  have hνcompl : ν (Work.FTS.EllipticEst.Q0)ᶜ = 0 := by
    rw [hνeq, Measure.restrict_apply'
      (show MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from
        measurableSet_Ici.prod measurableSet_Icc)]
    refine measure_mono_null (t := (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ))
      ∪ ((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ))
      ∪ ((Set.univ : Set ℝ) ×ˢ ({(Real.pi / 2)} : Set ℝ))) ?_ ?_
    · rintro p ⟨hpQ, hpz, hpθ⟩
      have hz : 0 ≤ p.1 := hpz
      have hθ0 : 0 ≤ p.2 := hpθ.1
      have hθ1 : p.2 ≤ Real.pi / 2 := hpθ.2
      have hnQ : ¬ (0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2) := by
        intro h
        exact hpQ ((Work.FTS.EllipticEst.mem_Q0).mpr h)
      rcases eq_or_lt_of_le hz with hz0 | hzpos
      · exact Or.inl (Or.inl ⟨hz0.symm, trivial⟩)
      · by_cases h2 : p.2 = 0
        · exact Or.inl (Or.inr ⟨trivial, h2⟩)
        · have hθpos : 0 < p.2 := lt_of_le_of_ne hθ0 (Ne.symm h2)
          have hθ2 : p.2 = Real.pi / 2 := by
            rcases eq_or_lt_of_le hθ1 with h | h
            · exact h
            · exact absurd ⟨hzpos, hθpos, h⟩ hnQ
          exact Or.inr ⟨trivial, hθ2⟩
    · have h1 : (MeasureTheory.volume.prod MeasureTheory.volume)
          (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
        rw [Measure.prod_prod, Real.volume_singleton, zero_mul]
      have h2 : (MeasureTheory.volume.prod MeasureTheory.volume)
          ((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ)) = 0 := by
        rw [Measure.prod_prod, Real.volume_singleton, mul_zero]
      have h3 : (MeasureTheory.volume.prod MeasureTheory.volume)
          ((Set.univ : Set ℝ) ×ˢ ({(Real.pi / 2)} : Set ℝ)) = 0 := by
        rw [Measure.prod_prod, Real.volume_singleton, mul_zero]
      refine le_antisymm ?_ (by simp)
      calc (MeasureTheory.volume.prod MeasureTheory.volume)
            ((({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) ∪ ((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ))
              ∪ ((Set.univ : Set ℝ) ×ˢ ({(Real.pi / 2)} : Set ℝ)))
          ≤ (MeasureTheory.volume.prod MeasureTheory.volume)
              ((({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ))
                ∪ ((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ)))
            + (MeasureTheory.volume.prod MeasureTheory.volume)
              ((Set.univ : Set ℝ) ×ˢ ({(Real.pi / 2)} : Set ℝ)) := measure_union_le _ _
        _ ≤ ((MeasureTheory.volume.prod MeasureTheory.volume)
              (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ))
            + (MeasureTheory.volume.prod MeasureTheory.volume)
              ((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ)))
            + (MeasureTheory.volume.prod MeasureTheory.volume)
              ((Set.univ : Set ℝ) ×ˢ ({(Real.pi / 2)} : Set ℝ)) :=
              add_le_add (measure_union_le _ _) le_rfl
        _ = 0 := by rw [h1, h2, h3]; simp
  have hQae : ∀ᵐ p ∂ν, p ∈ Work.FTS.EllipticEst.Q0 := by
    rw [MeasureTheory.ae_iff, show {p : ℝ × ℝ | ¬ p ∈ Work.FTS.EllipticEst.Q0}
      = (Work.FTS.EllipticEst.Q0)ᶜ from rfl]
    exact hνcompl
  refine AEMeasurable.congr hG.aemeasurable ?_
  filter_upwards [hQae] with p hp
  show (if p ∈ Work.FTS.EllipticEst.Q0 then u p.1 p.2 else 0) = u p.1 p.2
  exact ite_eq_left hp

end Work.FTS_EllLimOK
end
-- ===== merged: Submission.Work.FTS_EllLimOK.box_of_compact_inside_Q0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK

/-- A nonempty compact subset of the open quadrant `(0,∞) × (0,π/2)` sits inside a closed
rectangle `[a,b] × [c,d]` with `0 < a ≤ b`, `0 < c ≤ d` and `d < π/2`: take the extrema of
the (compact, hence nonempty) coordinate projections, which therefore stay in the open
quadrant. -/
theorem box_of_compact_inside_Q0 {K : Set (ℝ × ℝ)} (hKc : IsCompact K)
    (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) (hne : K.Nonempty) :
    ∃ a b c d : ℝ, 0 < a ∧ a ≤ b ∧ 0 < c ∧ c ≤ d ∧ d < Real.pi / 2 ∧
      K ⊆ Set.Icc a b ×ˢ Set.Icc c d := by
  have hKc1 : IsCompact (Prod.fst '' K) := hKc.image continuous_fst
  have hKc2 : IsCompact (Prod.snd '' K) := hKc.image continuous_snd
  have hne1 : (Prod.fst '' K).Nonempty := hne.image Prod.fst
  have hne2 : (Prod.snd '' K).Nonempty := hne.image Prod.snd
  obtain ⟨a, ha, hamin⟩ := hKc1.exists_isMinOn hne1 continuousOn_id
  obtain ⟨b, hb, hbmax⟩ := hKc1.exists_isMaxOn hne1 continuousOn_id
  obtain ⟨c, hc, hcmin⟩ := hKc2.exists_isMinOn hne2 continuousOn_id
  obtain ⟨d, hd, hdmax⟩ := hKc2.exists_isMaxOn hne2 continuousOn_id
  have hapos : 0 < a := by
    obtain ⟨p, hp, rfl⟩ := ha
    exact (Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)).1
  have hcpos : 0 < c := by
    obtain ⟨p, hp, rfl⟩ := hc
    exact (Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)).2.1
  have hdlt : d < Real.pi / 2 := by
    obtain ⟨p, hp, rfl⟩ := hd
    exact (Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)).2.2
  obtain ⟨p₀, hp₀⟩ := hne
  have hp₀₁ : p₀.1 ∈ Prod.fst '' K := ⟨p₀, hp₀, rfl⟩
  have hp₀₂ : p₀.2 ∈ Prod.snd '' K := ⟨p₀, hp₀, rfl⟩
  refine ⟨a, b, c, d, hapos, ?_, hcpos, ?_, hdlt, ?_⟩
  · exact le_trans (hamin hp₀₁) (hbmax hp₀₁)
  · exact le_trans (hcmin hp₀₂) (hdmax hp₀₂)
  · intro p hp
    have hp1 : p.1 ∈ Prod.fst '' K := ⟨p, hp, rfl⟩
    have hp2 : p.2 ∈ Prod.snd '' K := ⟨p, hp, rfl⟩
    exact ⟨⟨hamin hp1, hbmax hp1⟩, ⟨hcmin hp2, hdmax hp2⟩⟩

end Work.FTS_EllLimOK
end
-- ===== merged: Submission.Work.FTS_EllLimOK.continuousOn_HkIntegrand =====
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

/-! ## The weights are continuous on the open quadrant -/

private lemma sin_two_pos_of_lt {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

private lemma continuousOn_w_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
    funext p; rfl
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

private lemma continuousOn_sinpow_Q0 (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Work.FTS.EllipticEst.Q0 := by
  refine ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => ?_)
  exact Or.inl (ne_of_gt
    (sin_two_pos_of_lt (Work.FTS.EllipticEst.mem_Q0.mp hp).2.1
      (Work.FTS.EllipticEst.mem_Q0.mp hp).2.2))

/-- The product weight `Wt α = w · sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
private lemma continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  exact continuousOn_w_Q0.mul (continuousOn_sinpow_Q0 (-(Work.Spaces.gam α / 2)))

/-! ## The requested statement -/

theorem continuousOn_HkIntegrand {α : ℝ} {k : ℕ} {X : ℝ → ℝ → ℝ}
    (h : ∀ (j i : ℕ), j + i ≤ k →
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i X p.1 p.2)
        Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k X p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  -- the pure radial slots `D_z^i X = mixed i 0 X`, for `i ≤ k`
  have hDz : ∀ i ≤ k, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i X p.1 p.2)
      Work.FTS.EllipticEst.Q0 := fun i hi =>
    by simpa only [Work.Spaces.mixed_zero_right] using h i 0 (by omega)
  -- the mixed slots `D_z^j D_θ^i X`, for `1 ≤ i`, `i + j ≤ k`
  have hMx : ∀ i j : ℕ, 1 ≤ i → i + j ≤ k → ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i X p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    fun i j _ hij => h j i (by omega)
  simp only [Work.Spaces.HkIntegrand]
  refine ContinuousOn.add ?_ ?_
  · -- the sum of the squared weighted radial derivatives
    refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i hi => ?_)
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact (((hDz i hik).mul Work.FTS.EllipticEst.continuousOn_wdivsin_Q0)).pow 2
  · -- the sum of the squared weighted mixed derivatives
    refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i _hi =>
      continuousOn_finsetSum (Finset.range (k + 1)) (fun j _hj => ?_))
    split_ifs with hcond
    · exact (((hMx i j hcond.1 hcond.2).mul (continuousOn_Wt_Q0 α))).pow 2
    · exact continuousOn_const

end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JetCalc/Defs` — the jet functional of a differential combination

This module fixes the *explicit* expansion of the mixed jets `D_z^j D_θ^i` of a
combination `a(θ)·X + b(θ)·D_zX + c(θ)·∂_θX` of a stream function `X` and its first
derivatives, in terms of the mixed jets `D_z^j D_θ^i X` of `X` itself.

The expansion is the iterated Leibniz rule in the angular variable
`D_θ = sin(2θ)·∂_θ` (which sees the `θ`-dependent coefficients) combined with the
radial Leibniz rule `D_z^j (d(θ)·Y) = d(θ)·D_z^j Y` (the coefficients do not depend on
`z`) and Clairaut's theorem for the two curvilinear derivatives.  Concretely, for
`j + i ≤ 2`,

* `a(θ)·X`      contributes `∑_k C(i,k)·(D_θ^k a)·(D_z^jD_θ^{i-k} X)` (`coefJetS a j i 0`),
* `b(θ)·D_zX`   contributes `∑_k C(i,k)·(D_θ^k b)·(D_z^{j+1}D_θ^{i-k} X)` (`coefJetS b (j+1) i 0`),
* `c(θ)·∂_θX`   contributes `∑_k C(i,k)·(D_θ^k (c/sin 2·))·(D_z^jD_θ^{i-k+1} X)`
  (`coefJetS (c / sin 2·) j i 1`),

the last because `D_θ = sin(2θ)·∂_θ`.  All the jets of `X` occurring have total order at
most `j + i + 1 ≤ 3`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT.Slots.JetCalc

/-- The angular Leibniz sum: the contribution of a `θ`-dependent coefficient `d` times a
function whose `θ`-jets are `D_θ`-iterates of order `i - k` shifted by `s`. -/
def coefJetS (d : ℝ → ℝ) (j i s : ℕ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
    (Work.Spaces.DthIter k (fun _ (θ' : ℝ) => d θ') z θ
      * Work.Spaces.mixed j (i - k + s) X z θ)

/-- The jet functional of the combination `a(θ)·X + b(θ)·D_zX + c(θ)·∂_θX` at the point
`(z,θ)`: the explicit finite linear combination of the mixed jets of `X` into which its
mixed jets of order `(j,i)` expand. -/
def EJet (a b c : ℝ → ℝ) (j i : ℕ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  coefJetS a j i 0 X z θ
    + coefJetS b (j + 1) i 0 X z θ
    + coefJetS (fun θ' : ℝ => c θ' / Real.sin (2 * θ')) j i 1 X z θ

/-- The combination whose jets `EJet` computes. -/
def combo (a b c : ℝ → ℝ) (X : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => a θ * X z θ + b θ * Work.Spaces.Dz X z θ + c θ * Work.Spaces.pth X z θ

@[simp] theorem combo_apply (a b c : ℝ → ℝ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    combo a b c X z θ
      = a θ * X z θ + b θ * Work.Spaces.Dz X z θ + c θ * Work.Spaces.pth X z θ := rfl

end Work.FTS_RegExport.RXT.Slots.JetCalc
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.dthIter_congr_eqOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Slots.JetCalc

/-- `D_θ` is a local operator: if `F` and `G` agree on the open quadrant `Q0`, then so do all
their iterated `D_θ`-derivatives.  The induction step needs the θ-slice congruence of `pth` on
an open set (`Work.Spaces.pth_congr_of_isOpen`), which applies because `Q0` is open (so `F` and
`G` agree in a neighbourhood of every point of `Q0` in the `θ`-direction). -/
theorem dthIter_congr_eqOn {F G : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry F) (Function.uncurry G) Work.FTS.EllipticEst.Q0) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i F))
      (Function.uncurry (Work.Spaces.DthIter i G)) Work.FTS.EllipticEst.Q0 := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
      rintro ⟨z, θ⟩ hz
      show Work.Spaces.Dth (Work.Spaces.DthIter i F) z θ
        = Work.Spaces.Dth (Work.Spaces.DthIter i G) z θ
      simp only [Work.Spaces.Dth]
      rw [Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 ih hz]

end Work.FTS_RegExport.RXT.Slots.JetCalc
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.dzIter_congr_eqOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Slots.JetCalc

/-- The operator `D_z^j` is local: two functions which agree on an open set `V` have the
same iterated `D_z`-jets on `V`.

`D_z f = z ∂_z f` and `∂_z` acts on the `z`-slice `z' ↦ f z' θ`, so this is the
`z`-variable counterpart of `pth_congr_of_isOpen` (`Work.Spaces.pz_congr_of_isOpen`),
iterated; the openness of `V` is used to make the agreeing set a *neighbourhood* of the
`z`-coordinate. -/
theorem dzIter_congr_of_isOpen {F G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry F) (Function.uncurry G) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j F))
      (Function.uncurry (Work.Spaces.DzIter j G)) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
    intro p hp
    simp only [Function.uncurry, Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    rw [Work.Spaces.pz_congr_of_isOpen hV ih hp]

theorem dzIter_congr_eqOn {F G : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry F) (Function.uncurry G) Work.FTS.EllipticEst.Q0) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j F))
      (Function.uncurry (Work.Spaces.DzIter j G)) Work.FTS.EllipticEst.Q0 :=
  dzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 h j

end Work.FTS_RegExport.RXT.Slots.JetCalc
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Slots.v2_Prelim =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Slots

set_option autoImplicit false

/-! ## The pointwise bound hypothesis -/

/-- The pointwise bound of the slot `v2_L12DzIterTendsto`: on the open quadrant the mixed
derivatives of `f` of total order `≤ 2` are bounded by `C0 · z^{3/2}/(1+z)²`. -/
def JetBnd (C0 : ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ (b a : ℕ), a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    |Work.Spaces.mixed b a f z θ| ≤ C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)

theorem JetBnd.apply {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hb : JetBnd C0 f) {b a : ℕ} (h : a + b ≤ 2)
    {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    |Work.Spaces.mixed b a f z θ| ≤ C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) :=
  hb b a h z θ hz h0 h1

/-- The `a = 0` case: a bound on `f` itself. -/
theorem JetBnd.self_le {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hb : JetBnd C0 f) {z θ : ℝ}
    (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    |f z θ| ≤ C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) :=
  hb 0 0 (by norm_num) z θ hz h0 h1

/-- The order-one case: a bound on `D_z f = z ∂_z f`. -/
theorem JetBnd.DzIter_le {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hb : JetBnd C0 f) {z θ : ℝ}
    (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    |Work.Spaces.DzIter 1 f z θ| ≤ C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) :=
  hb 1 0 (by norm_num) z θ hz h0 h1

/-! ## Elementary facts about the angular interval -/

/-- `λ(Iθ) = π/2`. -/
theorem real_univ_restrict_Iθ :
    (volume.restrict Work.Spaces.Iθ).real Set.univ = Real.pi / 2 := by
  rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Work.Spaces.Iθ, Real.volume_Icc]
  rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

/-- `volume` restricted to `Iθ` is a finite measure. -/
theorem isFiniteMeasure_restrict_Iθ : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := by
  rw [isFiniteMeasure_restrict, Work.Spaces.Iθ]
  exact isCompact_Icc.measure_ne_top

/-- `volume` restricted to `Iθ` and to the open interval `(0,π/2)` agree. -/
theorem restrict_Iθ_eq_restrict_Ioo :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  rw [Work.Spaces.Iθ]
  exact MeasureTheory.Measure.restrict_congr_set
    (Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)).symm

/-- The angular slice of a function continuous on the open quadrant is a.e. strongly
measurable on `Iθ`. -/
theorem aesm_slice_Q0 {g : ℝ → ℝ → ℝ} (hg : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0) {x : ℝ}
    (hx : 0 < x) :
    AEStronglyMeasurable (fun θ => g x θ) (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry g) hg hx

/-! ## Differentiation under the angular integral, for open-quadrant data -/

/-- **Differentiation under the angular integral** for a parametric integrand which is only
continuous on the *open* quadrant.  If `V` is a neighbourhood of `x₀` consisting of positive
reals, `g` and its candidate derivative `g'` are continuous on `(0,∞) × (0,π/2)`, `θ ↦ g x₀ θ`
is integrable on `Iθ`, `g'` is uniformly bounded on `V × Iθ`, and for every interior angle
`x ↦ g x θ` has derivative `g' x θ`, then

  `∂_x (∫_θ g x θ) = ∫_θ g' x₀ θ`   at `x = x₀`. -/
theorem hasDerivAt_integral_Itheta_Q0 {g g' : ℝ → ℝ → ℝ} {V : Set ℝ} (hV : IsOpen V)
    {x₀ B : ℝ} (hx₀ : x₀ ∈ V) (hVpos : ∀ x ∈ V, 0 < x)
    (hg : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hg' : ContinuousOn (Function.uncurry g') Work.FTS.EllipticEst.Q0)
    (hgint : Integrable (fun θ => g x₀ θ) (volume.restrict Work.Spaces.Iθ))
    (hbound : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ∀ x ∈ V, ‖g' x θ‖ ≤ B)
    (hdiff : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ x ∈ V, HasDerivAt (fun y => g y θ) (g' x θ) x) :
    HasDerivAt (fun x => ∫ θ in Work.Spaces.Iθ, g x θ) (∫ θ in Work.Spaces.Iθ, g' x₀ θ) x₀ := by
  have haesm : ∀ (h : ℝ → ℝ → ℝ), ContinuousOn (Function.uncurry h) Work.FTS.EllipticEst.Q0 →
      ∀ x ∈ V, AEStronglyMeasurable (fun θ => h x θ) (volume.restrict Work.Spaces.Iθ) :=
    fun h hh x hx => aesm_slice_Q0 hh (hVpos x hx)
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ∀ x ∈ V,
      HasDerivAt (fun y => g y θ) (g' x θ) x := by
    rw [restrict_Iθ_eq_restrict_Ioo]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => hdiff θ hθ)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict Work.Spaces.Iθ) (𝕜 := ℝ)
    (F := fun x θ => g x θ) (F' := fun x θ => g' x θ) (bound := fun _ => B)
    (x₀ := x₀) (s := V) (hV.mem_nhds hx₀)
    (by filter_upwards [hV.mem_nhds hx₀] with x hx; exact haesm g hg x hx)
    hgint
    (haesm g' hg' x₀ hx₀)
    hbound
    (integrable_const B)
    hae
  exact key.2

/-! ## Real-variable bounds -/

/-- `√x/(1+x)² ≤ a^{-3/2} + 1` for `x ≥ a > 0`. -/
theorem rpow_half_div_sq_le {a x : ℝ} (ha : 0 < a) (hx : a ≤ x) :
    x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2 ≤ a ^ (-(3 : ℝ) / 2) + 1 := by
  have hx0 : 0 < x := lt_of_lt_of_le ha hx
  rcases le_or_gt 1 x with h1 | h1
  · have hstep : x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2 ≤ x ^ (-(3 : ℝ) / 2) := by
      rw [div_le_iff₀ (by positivity)]
      have hxx : x ^ (-(3 : ℝ) / 2) * x ^ (2 : ℕ) = x ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_natCast x 2, ← Real.rpow_add hx0]
        norm_num
      calc x ^ ((1 : ℝ) / 2) = x ^ (-(3 : ℝ) / 2) * x ^ (2 : ℕ) := hxx.symm
        _ ≤ x ^ (-(3 : ℝ) / 2) * (1 + x) ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hx0.le _)
            nlinarith
    have hmono : x ^ (-(3 : ℝ) / 2) ≤ a ^ (-(3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos ha hx (by norm_num)
    linarith
  · have hstep : x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      have hxa : x ^ ((1 : ℝ) / 2) ≤ 1 := Real.rpow_le_one hx0.le (le_of_lt h1) (by norm_num)
      nlinarith [hxa, sq_nonneg (1 + x), hx0]
    have hpos : 0 ≤ a ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg ha.le _
    linarith

/-- `x^{3/2} = x · x^{1/2}` for `x > 0`. -/
theorem rpow_three_halves {x : ℝ} (hx : 0 < x) :
    x ^ ((3 : ℝ) / 2) = x * x ^ ((1 : ℝ) / 2) := by
  rw [show ((3 : ℝ) / 2) = (1 : ℝ) / 2 + 1 by norm_num, Real.rpow_add hx, Real.rpow_one]
  ring

/-- `|K(θ)| ≤ 3` for every `θ`. -/
theorem abs_Ktheta_le (θ : ℝ) : |Work.Elliptic.Ktheta θ| ≤ 3 := by
  have hfun : Work.Elliptic.Ktheta θ = 3 * (Real.sin θ * Real.cos θ ^ 2) := by
    rw [Work.Elliptic.Ktheta]; ring
  rw [hfun, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  have h1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have h2 : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_sq]; nlinarith [sq_nonneg (Real.sin θ), Real.sin_sq_add_cos_sq θ]
  calc 3 * |Real.sin θ * Real.cos θ ^ 2| = 3 * (|Real.sin θ| * |Real.cos θ ^ 2|) := by
        rw [abs_mul]
    _ ≤ 3 * (1 * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num))
          (by norm_num)
    _ = 3 := by norm_num

/-! ## Consequences of `JetBnd` -/

/-- The bound on `∂_z` of the `D_z`-iterates, `k ≤ 1`. -/
theorem JetBnd.pz_DzIter_le {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hb : JetBnd C0 f)
    {k : ℕ} (hk : k ≤ 1) {x θ : ℝ} (hx : 0 < x) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    |Work.Spaces.pz (Work.Spaces.DzIter k f) x θ|
      ≤ C0 * (x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2) := by
  have hkey : Work.Spaces.pz (Work.Spaces.DzIter k f) x θ
      = Work.Spaces.DzIter (k + 1) f x θ / x := by
    show Work.Spaces.pz (Work.Spaces.DzIter k f) x θ
      = x * Work.Spaces.pz (Work.Spaces.DzIter k f) x θ / x
    rw [mul_div_cancel_left₀ _ (ne_of_gt hx)]
  rw [hkey, abs_div, abs_of_pos hx]
  have hbd := hb (k + 1) 0 (by omega) x θ hx h0 h1
  rw [rpow_three_halves hx] at hbd
  refine le_trans (div_le_div_of_nonneg_right hbd hx.le) ?_
  rw [show C0 * (x * x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2) / x
      = C0 * (x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2) from by
    field_simp]

/-- The angular density of `JetBnd`-data is bounded by `6 C0 s^{-3/2}`. -/
theorem JetBnd.dens_bound {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hC0 : 0 ≤ C0) (hb : JetBnd C0 f)
    {s : ℝ} (hs : 0 < s) :
    ‖Work.Elliptic.L12dens f s‖ ≤ 6 * C0 * s ^ (-(3 : ℝ) / 2) := by
  have hbd : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖Work.Elliptic.Ktheta θ * f s θ / s‖
        ≤ 3 * C0 * (s ^ ((3 : ℝ) / 2) / (1 + s) ^ 2) / s := by
    rw [restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hs, abs_mul, div_le_div_iff_of_pos_right hs]
    calc |Work.Elliptic.Ktheta θ| * |f s θ|
        ≤ 3 * (C0 * (s ^ ((3 : ℝ) / 2) / (1 + s) ^ 2)) :=
          mul_le_mul (abs_Ktheta_le θ) (hb.self_le hs hθ.1 hθ.2) (abs_nonneg _) (by norm_num)
      _ = 3 * C0 * (s ^ ((3 : ℝ) / 2) / (1 + s) ^ 2) := by ring
  have hstep := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := volume.restrict Work.Spaces.Iθ) hbd
  rw [real_univ_restrict_Iθ] at hstep
  have hkey : Work.Elliptic.L12dens f s
      = ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * f s θ / s := rfl
  rw [hkey]
  refine le_trans hstep ?_
  have hMle : 3 * C0 * (s ^ ((3 : ℝ) / 2) / (1 + s) ^ 2) / s ≤ 3 * C0 * s ^ (-(3 : ℝ) / 2) := by
    have h1 : s ^ ((3 : ℝ) / 2) / s = s ^ ((1 : ℝ) / 2) := by
      rw [rpow_three_halves hs, mul_div_cancel_left₀ _ (ne_of_gt hs)]
    rw [show 3 * C0 * (s ^ ((3 : ℝ) / 2) / (1 + s) ^ 2) / s
        = 3 * C0 * (s ^ ((3 : ℝ) / 2) / s / (1 + s) ^ 2) from by ring, h1]
    have h2 : s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 ≤ s ^ (-(3 : ℝ) / 2) := by
      rw [div_le_iff₀ (by positivity)]
      have h3 : s ^ (-(3 : ℝ) / 2) * s ^ (2 : ℕ) = s ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_natCast s 2, ← Real.rpow_add hs]; norm_num
      calc s ^ ((1 : ℝ) / 2) = s ^ (-(3 : ℝ) / 2) * s ^ (2 : ℕ) := h3.symm
        _ ≤ s ^ (-(3 : ℝ) / 2) * (1 + s) ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hs.le _)
            nlinarith
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  refine le_trans (mul_le_mul_of_nonneg_right hMle (by positivity)) ?_
  have hpi : Real.pi / 2 ≤ 2 := by linarith [Real.pi_lt_four]
  have hspos : 0 ≤ 3 * C0 * s ^ (-(3 : ℝ) / 2) := by positivity
  nlinarith [mul_nonneg hC0 hspos]

/-- `L₁₂dens` of `JetBnd`-data is integrable on `(a,∞)`, `a > 0`, as soon as it is continuous
there. -/
theorem JetBnd.dens_integrable {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hC0 : 0 ≤ C0) (hb : JetBnd C0 f)
    (hcont : ContinuousOn (fun s => Work.Elliptic.L12dens f s) (Set.Ioi 0)) {a : ℝ}
    (ha : 0 < a) :
    IntegrableOn (fun s => Work.Elliptic.L12dens f s) (Set.Ioi a) := by
  have hmaj : IntegrableOn (fun s : ℝ => 6 * C0 * s ^ (-(3 : ℝ) / 2)) (Set.Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 : ℝ) / 2) < -1) ha).const_mul _
  refine Integrable.mono' hmaj ((hcont.mono (Set.Ioi_subset_Ioi ha.le)).aestronglyMeasurable
    measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact hb.dens_bound hC0 (lt_of_lt_of_le ha (le_of_lt hs))

end Work.FTS_RegExport.RXT.Slots
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Slots.v2_thetaJetsTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Slots

/-!
## Factorisation of the mixed jets of `Θ = (1/(4α)) sin(2θ) L₁₂(F)`

The function `Θ α F` depends on `F` only through the radial function `L₁₂ F` and splits as a
product `(z,θ) ↦ B θ · A z` of a function of `θ` alone and a function of `z` alone.  Since
`D_z` acts only on `z` and `D_θ` only on `θ`, every mixed jet of `Θ` factors as the product of
the `θ`-jet of `B` and the `z`-jet of `A`:

  `D_z^j D_θ^i (B ⊗ A) = (Lop^i B) ⊗ (Zop^j A)`.

The only point needing care is that `deriv` in Lean is totalised, so the "constant multiple"
rules `deriv (c · f) = c · deriv f`, `deriv (f · c) = deriv f · c` must be used in their
*unconditional* forms `deriv_const_mul_field`, `deriv_mul_const_field`; no differentiability
hypothesis on `F` is available (and none is needed).
-/

/-- `D_θ^i` applied to a product of a `z`-function and a `θ`-function. -/
private lemma theta_mixed_DthIter_sep (i : ℕ) (A B : ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => A z * B θ) = fun z θ => A z * (Work.Spaces.Lop^[i] B) θ := by
  induction i with
  | zero =>
      funext z θ
      rfl
  | succ i ih =>
      rw [show Work.Spaces.DthIter (i + 1) (fun z θ => A z * B θ)
            = Work.Spaces.Dth (Work.Spaces.DthIter i (fun z θ => A z * B θ)) from rfl, ih]
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' => A z * (Work.Spaces.Lop^[i] B) θ') θ
          = A z * (Work.Spaces.Lop^[i + 1] B) θ
      rw [deriv_const_mul_field (x := θ) (v := Work.Spaces.Lop^[i] B) (A z)]
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.Lop]
      ring

/-- `D_z^j` applied to a product of a `z`-function and a `θ`-function. -/
private lemma theta_mixed_DzIter_sep (j : ℕ) (A C : ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => A z * C θ) = fun z θ => (Work.Spaces.Zop^[j] A z) * C θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [show Work.Spaces.DzIter (j + 1) (fun z θ => A z * C θ)
            = Work.Spaces.Dz (Work.Spaces.DzIter j (fun z θ => A z * C θ)) from rfl, ih]
      funext z θ
      show z * deriv (fun z' => Work.Spaces.Zop^[j] A z' * C θ) z
          = (Work.Spaces.Zop^[j + 1] A z) * C θ
      rw [deriv_mul_const_field (v := C θ) (u := Work.Spaces.Zop^[j] A) (x := z)]
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.Zop]
      ring

/-- The hypothesis of the theorem is about `DzIter` at `θ = 0`; for a `θ`-independent function
this is the same as `Zop^[j]` evaluated at `z`. -/
private lemma theta_mixed_Zop_eq_DzIter (j : ℕ) (A : ℝ → ℝ) (z : ℝ) :
    Work.Spaces.Zop^[j] A z = Work.Spaces.DzIter j (fun z _ => A z) z 0 := by
  have h := congrFun (Work.Spaces.Zop_slice j (fun z _ => A z) 0) z
  exact h.symm

/-- Every mixed jet of a product `A z · B θ` is the product of the `θ`-jet of `B` and the
`z`-jet of `A` (in the `DzIter` form that occurs in the hypothesis). -/
private lemma theta_mixed_sep (j i : ℕ) (A B : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => A z * B θ) z θ
      = (Work.Spaces.Lop^[i] B) θ * Work.Spaces.DzIter j (fun z _ => A z) z 0 := by
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => A z * B θ)) z θ = _
  rw [theta_mixed_DthIter_sep i A B, theta_mixed_DzIter_sep j A (Work.Spaces.Lop^[i] B)]
  show Work.Spaces.Zop^[j] A z * (Work.Spaces.Lop^[i] B) θ = _
  rw [theta_mixed_Zop_eq_DzIter j A z]
  ring

/-- The same factorisation with the two factors in the order in which `Theta` presents them. -/
private lemma theta_mixed_sep' (j i : ℕ) (A B : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => B θ * A z) z θ
      = (Work.Spaces.Lop^[i] B) θ * Work.Spaces.DzIter j (fun z _ => A z) z 0 := by
  have hfun : (fun z θ => B θ * A z) = (fun z θ => A z * B θ) := by
    funext z θ
    exact mul_comm _ _
  rw [hfun]
  exact theta_mixed_sep j i A B z θ

theorem v2_thetaJetsTendsto {α : ℝ} {F : ℕ → ℝ → ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hL12 : ∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun n : ℕ =>
          Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 (F n) z) z 0)
        Filter.atTop
        (nhds (Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 G z) z 0))) :
    ∀ (j i : ℕ), j + i ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (Work.Construction.Theta α (F n)) z θ)
        Filter.atTop
        (nhds (Work.Spaces.mixed j i (Work.Construction.Theta α G) z θ)) := by
  intro j i hji z θ hz hθ hθ2
  have hj : j ≤ 3 := by omega
  -- `Θ α H = B ⊗ L₁₂(H)` with `B θ = (1/(4α)) sin(2θ)`.
  set B : ℝ → ℝ := fun θ => (1 / (4 * α)) * Real.sin (2 * θ) with hB
  have hkey : ∀ H : ℝ → ℝ → ℝ,
      Work.Spaces.mixed j i (Work.Construction.Theta α H) z θ
        = (Work.Spaces.Lop^[i] B) θ
            * Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 H z) z 0 := by
    intro H
    rw [show Work.Construction.Theta α H
          = fun z θ => B θ * Work.Construction.L12 H z from rfl]
    exact theta_mixed_sep' j i (Work.Construction.L12 H) B z θ
  rw [show (fun n : ℕ => Work.Spaces.mixed j i (Work.Construction.Theta α (F n)) z θ)
        = (fun n : ℕ => (Work.Spaces.Lop^[i] B) θ
            * Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 (F n) z) z 0)
        from funext (fun n => hkey (F n)), hkey G]
  exact (hL12 j hj z hz).const_mul ((Work.Spaces.Lop^[i] B) θ)

end Work.FTS_RegExport.RXT.Slots
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.StarVopAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false

/-! ## Part 1 — the elementary factor `A(z) = z/(1+z)` and its derivatives -/

/-- `A'(z) = 1/(1+z)²` for `A(z) = z/(1+z)`. -/
theorem hasDerivAt_affine {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun y : ℝ => y / (1 + y)) (1 / (1 + z) ^ 2) z := by
  have hne : (1 + z) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => y) (1 : ℝ) z := hasDerivAt_id z
  have h2 : HasDerivAt (fun y : ℝ => (1 : ℝ) + y) (1 : ℝ) z :=
    (hasDerivAt_const_add_iff (1 : ℝ)).mpr (hasDerivAt_id z)
  have h := h1.div h2 hne
  rw [show ((fun y : ℝ => y) / (fun y : ℝ => (1 : ℝ) + y))
      = (fun y : ℝ => y / (1 + y)) from rfl] at h
  rw [show (1 : ℝ) * (1 + z) - z * 1 = 1 by ring] at h
  exact h

/-- `B'(z) = (1-z)/(1+z)³` for `B(z) = z/(1+z)²`. -/
theorem hasDerivAt_quad {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun y : ℝ => y / (1 + y) ^ 2) ((1 - z) / (1 + z) ^ 3) z := by
  have hne : ((1 : ℝ) + z) ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => y) (1 : ℝ) z := hasDerivAt_id z
  have h2 : HasDerivAt (fun y : ℝ => ((1 : ℝ) + y) ^ 2) (2 * (1 + z) ^ (2 - 1) * 1) z :=
    ((hasDerivAt_const_add_iff (1 : ℝ)).mpr (hasDerivAt_id z)).pow 2
  have h := h1.div h2 hne
  rw [show ((fun y : ℝ => y) / (fun y : ℝ => ((1 : ℝ) + y) ^ 2))
      = (fun y : ℝ => y / (1 + y) ^ 2) from rfl] at h
  rw [show (2 : ℕ) - 1 = 1 by norm_num, pow_one, mul_one] at h
  rw [show (1 * (1 + z) ^ 2 - z * (2 * (1 + z))) / ((1 + z) ^ 2) ^ 2
      = (1 - z) / (1 + z) ^ 3 by
    field_simp
    ring] at h
  exact h

/-- `|A(z)| = |z/(1+z)| ≤ min z 1` for `z > 0`. -/
theorem affine_bound {z : ℝ} (hz : 0 < z) : |z / (1 + z)| ≤ min z 1 := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ z / (1 + z))]
  refine le_min ?_ ?_
  · rw [div_le_iff₀ h1]; nlinarith
  · rw [div_le_one h1]; linarith

/-- `|z/(1+z)²| ≤ min z 1` for `z > 0`. -/
theorem quad_bound {z : ℝ} (hz : 0 < z) : |z / (1 + z) ^ 2| ≤ min z 1 := by
  have h2 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ z / (1 + z) ^ 2)]
  refine le_min ?_ ?_
  · rw [div_le_iff₀ h2]; nlinarith [sq_nonneg z, hz]
  · rw [div_le_one h2]; nlinarith [sq_nonneg z, hz]

/-- `|z(1-z)/(1+z)³| ≤ min z 1` for `z > 0`. -/
theorem cubic_bound {z : ℝ} (hz : 0 < z) : |z * (1 - z) / (1 + z) ^ 3| ≤ min z 1 := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have h2 : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  have hzabs : |1 - z| ≤ 1 + z := by
    rw [abs_le]; constructor <;> linarith
  have hcube : (1 + z) ≤ (1 + z) ^ 3 := by nlinarith [sq_nonneg (1 + z)]
  have hsq : z ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg (1 + z), hz]
  have hval : |z * (1 - z) / (1 + z) ^ 3| = z * |1 - z| / (1 + z) ^ 3 := by
    rw [abs_div, abs_mul, abs_of_nonneg hz.le, abs_of_pos h2]
  rw [hval]
  refine le_min ?_ ?_
  · rw [div_le_iff₀ h2]
    nlinarith [hzabs, hcube, hz]
  · rw [div_le_one h2]
    nlinarith [hzabs, hsq, hz, mul_le_mul_of_nonneg_left hzabs hz.le]

/-! ## Part 2 — the Leibniz rules for `D_θ^i` and `D_z^j` against the z-only factor -/


/-- `D_z (A·X) = (z/(1+z)²)·X + A·D_z X` for `A = A(z)`. -/
theorem DzIter_one_mul_zonly {X : ℝ → ℝ → ℝ} (hX : Work.FTS.EllipticEst.SmoothOpen X) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter 1 (fun z θ => z / (1 + z) * X z θ) z θ
        = z / (1 + z) ^ 2 * X z θ + z / (1 + z) * Work.Spaces.DzIter 1 X z θ := by
  intro z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hX' : HasDerivAt (fun z' : ℝ => X z' θ) (Work.Spaces.pzIter 1 X z θ) z :=
    hX.hasDerivAt_slice hθ hz
  have hmul := (hasDerivAt_affine hz).mul hX'
  have hder : deriv (fun z' : ℝ => z' / (1 + z') * X z' θ) z
      = (1 / (1 + z) ^ 2) * X z θ + z / (1 + z) * Work.Spaces.pzIter 1 X z θ := hmul.deriv
  show z * deriv (fun z' : ℝ => z' / (1 + z') * X z' θ) z
      = z / (1 + z) ^ 2 * X z θ + z / (1 + z) * (z * Work.Spaces.pzIter 1 X z θ)
  rw [hder]
  ring_nf

/-- `D_z²(A·X) = (z(1-z)/(1+z)³)·X + 2(z/(1+z)²)·D_z X + A·D_z²X` for `A = A(z)`. -/
theorem DzIter_two_mul_zonly {X : ℝ → ℝ → ℝ} (hX : Work.FTS.EllipticEst.SmoothOpen X) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter 2 (fun z θ => z / (1 + z) * X z θ) z θ
        = z * (1 - z) / (1 + z) ^ 3 * X z θ
          + 2 * (z / (1 + z) ^ 2) * Work.Spaces.DzIter 1 X z θ
          + z / (1 + z) * Work.Spaces.DzIter 2 X z θ := by
  intro z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hev : (fun z' : ℝ => Work.Spaces.DzIter 1 (fun z θ => z / (1 + z) * X z θ) z' θ)
      =ᶠ[𝓝 z] (fun z' : ℝ => z' / (1 + z') ^ 2 * X z' θ
        + z' / (1 + z') * Work.Spaces.DzIter 1 X z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact DzIter_one_mul_zonly hX z' θ hz' hθ0 hθ1
  have h1 : deriv (fun z' : ℝ => z' / (1 + z') ^ 2 * X z' θ) z
      = ((1 - z) / (1 + z) ^ 3) * X z θ + z / (1 + z) ^ 2 * Work.Spaces.pzIter 1 X z θ :=
    ((hasDerivAt_quad hz).mul (hX.hasDerivAt_slice hθ hz)).deriv
  have h2 : deriv (fun z' : ℝ => z' / (1 + z') * Work.Spaces.DzIter 1 X z' θ) z
      = (1 / (1 + z) ^ 2) * (z * Work.Spaces.pzIter 1 X z θ)
          + z / (1 + z) * Work.Spaces.pzIter 1 (Work.Spaces.DzIter 1 X) z θ :=
    ((hasDerivAt_affine hz).mul ((hX.DzIter 1).hasDerivAt_slice hθ hz)).deriv
  have hd1 : DifferentiableAt ℝ (fun z' : ℝ => z' / (1 + z') ^ 2 * X z' θ) z :=
    ((hasDerivAt_quad hz).mul (hX.hasDerivAt_slice hθ hz)).differentiableAt
  have hd2 : DifferentiableAt ℝ
      (fun z' : ℝ => z' / (1 + z') * Work.Spaces.DzIter 1 X z' θ) z :=
    ((hasDerivAt_affine hz).mul ((hX.DzIter 1).hasDerivAt_slice hθ hz)).differentiableAt
  have hder : deriv (fun z' : ℝ => z' / (1 + z') ^ 2 * X z' θ
        + z' / (1 + z') * Work.Spaces.DzIter 1 X z' θ) z
      = ((1 - z) / (1 + z) ^ 3) * X z θ + z / (1 + z) ^ 2 * Work.Spaces.pzIter 1 X z θ
        + ((1 / (1 + z) ^ 2) * (z * Work.Spaces.pzIter 1 X z θ)
            + z / (1 + z) * Work.Spaces.pzIter 1 (Work.Spaces.DzIter 1 X) z θ) := by
    rw [show deriv (fun z' : ℝ => z' / (1 + z') ^ 2 * X z' θ
          + z' / (1 + z') * Work.Spaces.DzIter 1 X z' θ) z
        = deriv ((fun z' : ℝ => z' / (1 + z') ^ 2 * X z' θ)
            + (fun z' : ℝ => z' / (1 + z') * Work.Spaces.DzIter 1 X z' θ)) z from rfl,
      deriv_add hd1 hd2, h1, h2]
  show z * deriv (fun z' : ℝ => Work.Spaces.DzIter 1
        (fun z θ => z / (1 + z) * X z θ) z' θ) z
      = z * (1 - z) / (1 + z) ^ 3 * X z θ
        + 2 * (z / (1 + z) ^ 2) * (z * Work.Spaces.pzIter 1 X z θ)
        + z / (1 + z) * (z * Work.Spaces.pzIter 1 (Work.Spaces.DzIter 1 X) z θ)
  rw [hev.deriv_eq, hder]
  ring_nf

/-! ## Part 3 — transfer of the Leibniz rules to `𝒱 = A·W`

The three lemmas below state the identities for a pair `(V, W)` related by the algebraic
identity `V = A(z)·W` (on the open quadrant).  They are used with `(V, W) = (𝒱(Φ̃_*), W)`
and with `(V, W) = (D_θ^i 𝒱(Φ̃_*), D_θ^i W)`. -/

/-- `D_θ^i V = A·D_θ^i W` for `i ≤ 2`, when `V = A·W` on the open quadrant. -/
theorem DthIter_eq_mul {V W : ℝ → ℝ → ℝ}
    (hid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → V z θ = z / (1 + z) * W z θ)
    (hW : Work.FTS.EllipticEst.SmoothOpen W) :
    ∀ i : ℕ, i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i V z θ = z / (1 + z) * Work.Spaces.DthIter i W z θ := by
  intro i hi z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  interval_cases i
  · exact hid z θ hz hθ0 hθ1
  · have hev : (fun θ' : ℝ => V z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => z / (1 + z) * W z θ') := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
      exact hid z θ' hz hθ'.1 hθ'.2
    have hdiff : DifferentiableAt ℝ (fun θ' : ℝ => W z θ') θ :=
      ((hW.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
    show Real.sin (2 * θ) * deriv (fun θ' : ℝ => V z θ') θ
        = z / (1 + z) * (Real.sin (2 * θ) * deriv (fun θ' : ℝ => W z θ') θ)
    rw [hev.deriv_eq, deriv_const_mul (z / (1 + z)) hdiff]
    ring
  · have hev : (fun θ' : ℝ => Work.Spaces.DthIter 1 V z θ')
        =ᶠ[𝓝 θ] (fun θ' : ℝ => z / (1 + z) * Work.Spaces.DthIter 1 W z θ') := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
      exact DthIter_eq_mul hid hW 1 (by norm_num) z θ' hz hθ'.1 hθ'.2
    have hdiff : DifferentiableAt ℝ (fun θ' : ℝ => Work.Spaces.DthIter 1 W z θ') θ :=
      (((hW.DthIter 1).curry_θ hz).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds hθ)
    have hL : Work.Spaces.DthIter 2 V z θ
        = Real.sin (2 * θ) * (z / (1 + z)
            * deriv (fun θ' : ℝ => Work.Spaces.DthIter 1 W z θ') θ) := by
      rw [show Work.Spaces.DthIter 2 V z θ
          = Real.sin (2 * θ) * deriv (fun θ' : ℝ => Work.Spaces.DthIter 1 V z θ') θ from rfl]
      rw [hev.deriv_eq, deriv_const_mul (z / (1 + z)) hdiff]
    have hR : Work.Spaces.DthIter 2 W z θ
        = Real.sin (2 * θ) * deriv (fun θ' : ℝ => Work.Spaces.DthIter 1 W z θ') θ := rfl
    rw [hL, hR]; ring

/-- `D_z V = (z/(1+z)²)·W + A·D_z W` when `V = A·W` on the open quadrant. -/
theorem DzIter_one_eq_mul {V W : ℝ → ℝ → ℝ}
    (hid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → V z θ = z / (1 + z) * W z θ)
    (hW : Work.FTS.EllipticEst.SmoothOpen W) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter 1 V z θ
        = z / (1 + z) ^ 2 * W z θ + z / (1 + z) * Work.Spaces.DzIter 1 W z θ := by
  intro z θ hz hθ0 hθ1
  have hA := DzIter_one_mul_zonly hW z θ hz hθ0 hθ1
  have hev : (fun z' : ℝ => V z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => z' / (1 + z') * W z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact hid z' θ hz' hθ0 hθ1
  rw [show Work.Spaces.DzIter 1 V z θ = z * Work.Spaces.pz V z θ from rfl]
  rw [show Work.Spaces.pz V z θ
      = Work.Spaces.pz (fun z θ => z / (1 + z) * W z θ) z θ from hev.deriv_eq]
  rw [← show Work.Spaces.DzIter 1 (fun z θ => z / (1 + z) * W z θ) z θ
      = z * Work.Spaces.pz (fun z θ => z / (1 + z) * W z θ) z θ from rfl]
  exact hA

/-- `D_z² V = (z(1-z)/(1+z)³)·W + 2(z/(1+z)²)·D_z W + A·D_z² W` when `V = A·W`. -/
theorem DzIter_two_eq_mul {V W : ℝ → ℝ → ℝ}
    (hid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → V z θ = z / (1 + z) * W z θ)
    (hW : Work.FTS.EllipticEst.SmoothOpen W) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter 2 V z θ
        = z * (1 - z) / (1 + z) ^ 3 * W z θ
          + 2 * (z / (1 + z) ^ 2) * Work.Spaces.DzIter 1 W z θ
          + z / (1 + z) * Work.Spaces.DzIter 2 W z θ := by
  intro z θ hz hθ0 hθ1
  have hgen := DzIter_two_mul_zonly hW z θ hz hθ0 hθ1
  have hev : (fun z' : ℝ => Work.Spaces.DzIter 1 V z' θ)
      =ᶠ[𝓝 z] (fun z' : ℝ => Work.Spaces.DzIter 1
        (fun z θ => z / (1 + z) * W z θ) z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    rw [DzIter_one_eq_mul hid hW z' θ hz' hθ0 hθ1,
      DzIter_one_mul_zonly hW z' θ hz' hθ0 hθ1]
  rw [show Work.Spaces.DzIter 2 V z θ
      = z * Work.Spaces.pz (Work.Spaces.DzIter 1 V) z θ from rfl]
  rw [show Work.Spaces.pz (Work.Spaces.DzIter 1 V) z θ
      = Work.Spaces.pz (Work.Spaces.DzIter 1 (fun z θ => z / (1 + z) * W z θ)) z θ
      from hev.deriv_eq]
  rw [← show Work.Spaces.DzIter 2 (fun z θ => z / (1 + z) * W z θ) z θ
      = z * Work.Spaces.pz (Work.Spaces.DzIter 1 (fun z θ => z / (1 + z) * W z θ)) z θ
      from rfl]
  exact hgen

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.EPCDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.EPCDefs` — the datum interface of `explicit_pieces_coeff`

The target `Work.FTS_RegExport.RXT.Sys.explicit_pieces_coeff` bounds the `mixed`-jets
(`j + i ≤ 2`) of the four explicit pieces built from the profile
`F(τ) = Ftau (pExp α) (GR α g) τ = F_* + gS α (tauExt g)(τ)`:

* `L₁₂(F)(z) · c2m θ`, `L₁₂(F)(z)`, `sin²θ · 𝔽K(F)(z)`, and `Uop α (Θ α F) / sin 2θ`
  (which on the open quadrant is the radial combination `-(3/(4β))·L₁₂(F) + (1/4)·𝔽K(F)`).

Everything reduces to bounds for the iterated `z∂_z`-jets (order `≤ 2`) of the two radial
transforms `L₁₂(F)` and `𝔽K(F)` of the datum `F`.  This module fixes the interface used to
state that reduction:

* `DatumBnd F C` — `|F|`, `|D_zF|`, `|D_z²F| ≤ C` on the open quadrant;
* `DatumHyp F C` — the `C²`-smoothness of `F` on the open quadrant, the pointwise bound
  `DatumBnd F C`, and the `L¹`-control of the `L₁₂`-density which makes `L₁₂(F)` a primitive.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false

/-- **Pointwise bounds of the first three `D_z`-jets of a datum** on the open quadrant. -/
def DatumBnd (F : ℝ → ℝ → ℝ) (C : ℝ) : Prop :=
  ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    |F z θ| ≤ C ∧ |Work.Spaces.Dz F z θ| ≤ C ∧ |Work.Spaces.DzIter 2 F z θ| ≤ C

/-- **The hypotheses of the `𝔽K`/`L₁₂` jet package**: `C²`-smoothness of the datum on the
open quadrant, the pointwise jet bounds `DatumBnd`, and the `L¹`-control of the `L₁₂`-density
(with the total mass bounded by the same constant `C`). -/
def DatumHyp (F : ℝ → ℝ → ℝ) (C : ℝ) : Prop :=
  ContDiffOn ℝ 2 (Function.uncurry F) Work.FTS.EllipticEst.Q0 ∧
    DatumBnd F C ∧
    MeasureTheory.IntegrableOn (Work.Construction.L12dens F) (Set.Ioi 0) ∧
    (∫ s in Set.Ioi 0, |Work.Construction.L12dens F s|) ≤ C

theorem DatumHyp.smooth {F : ℝ → ℝ → ℝ} {C : ℝ} (h : DatumHyp F C) :
    ContDiffOn ℝ 2 (Function.uncurry F) Work.FTS.EllipticEst.Q0 := h.1

theorem DatumHyp.bnd {F : ℝ → ℝ → ℝ} {C : ℝ} (h : DatumHyp F C) : DatumBnd F C := h.2.1

theorem DatumHyp.integrable {F : ℝ → ℝ → ℝ} {C : ℝ} (h : DatumHyp F C) :
    MeasureTheory.IntegrableOn (Work.Construction.L12dens F) (Set.Ioi 0) := h.2.2.1

theorem DatumHyp.mass {F : ℝ → ℝ → ℝ} {C : ℝ} (h : DatumHyp F C) :
    (∫ s in Set.Ioi 0, |Work.Construction.L12dens F s|) ≤ C := h.2.2.2

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.SysAux.Theta_ops =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.SysAux

/-- `(sin (2·))' = 2 cos (2·)`, the only calculus input of the closed forms below. -/
private lemma deriv_sin_two (θ : ℝ) : deriv (fun θ' => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ) := by
  have h1 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ (hasDerivAt_const_mul (x := θ) (2 : ℝ))
  rw [h1.deriv]; ring

/-- The three closed forms of the operators `V`, `U`, `R` (of `Work.Construction`) applied to the
singular part `Θ αG F = (1/(4αG))·sin 2θ·L₁₂(F)(z)`, on the open quadrant
`z > 0, 0 < θ < π/2` (where `cos θ ≠ 0`), given the index-raising identity
`z ∂_z L₁₂(F) = -𝔽K(F)` (hypothesis `hL12d`, which the callers supply from the integral form of
`L₁₂`).  These are the identities that let `Vz7`, `Vθ7`, `cs7` be written with the `Θ`-part in
closed form. -/
theorem Theta_ops {αG : ℝ} (hα : 0 < αG) {F : ℝ → ℝ → ℝ}
    (hL12d : ∀ z : ℝ, 0 < z →
      z * deriv (fun z' => Work.Construction.L12 F z') z = -Work.Construction.FK F z) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (2 * αG * Work.Construction.Vop (Work.Construction.Theta αG F) z θ
          = Work.Construction.c2m θ * Work.Construction.L12 F z) ∧
      (2 * Work.Construction.Uop αG (Work.Construction.Theta αG F) z θ
          = -(3 / (2 * αG)) * Real.sin (2 * θ) * Work.Construction.L12 F z
            + (1 / 2) * Real.sin (2 * θ) * Work.Construction.FK F z) ∧
      (-2 * Work.Construction.Rop αG (Work.Construction.Theta αG F) z θ
          = -(Work.Construction.L12 F z) / αG + (Real.sin θ) ^ 2 * Work.Construction.FK F z) := by
  intro z θ hz hθ hθ2
  -- `cos θ ≠ 0` on the open quadrant, so `tan θ = sin θ / cos θ` may be used.
  have hcos : Real.cos θ ≠ 0 := by
    have h := Real.cos_pos_of_mem_Ioo (show θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    exact ne_of_gt h
  have hzne : z ≠ 0 := ne_of_gt hz
  -- `hL12d` in the form `∂_z L₁₂(F)(z) = -𝔽K(F)(z)/z`, in which every occurrence of the
  -- radial derivative can be eliminated.
  have hLd : deriv (fun z' => Work.Construction.L12 F z') z
      = -Work.Construction.FK F z / z := by
    rw [eq_div_iff hzne, mul_comm]
    exact hL12d z hz
  -- `∂_θ Θ = (1/(4αG))·L₁₂(F)·2cos 2θ`
  have hpth : Work.Spaces.pth (Work.Construction.Theta αG F) z θ
      = (1 / (4 * αG)) * (2 * Real.cos (2 * θ)) * Work.Construction.L12 F z := by
    show deriv (fun θ' => Work.Construction.Theta αG F z θ') θ = _
    have h1 : (fun θ' => Work.Construction.Theta αG F z θ')
        = fun θ' => ((1 / (4 * αG)) * Work.Construction.L12 F z) * Real.sin (2 * θ') := by
      funext θ'
      simp only [Work.Construction.Theta, Work.Construction.s2]
      ring
    rw [h1, deriv_const_mul_field, deriv_sin_two]
    ring
  -- `∂_z Θ = (1/(4αG))·sin 2θ·∂_z L₁₂(F)`, and the hypothesis removes `∂_z L₁₂(F)`.
  have hpz : Work.Spaces.pz (Work.Construction.Theta αG F) z θ
      = (1 / (4 * αG)) * Real.sin (2 * θ) * (-Work.Construction.FK F z / z) := by
    show deriv (fun z' => Work.Construction.Theta αG F z' θ) z = _
    have h1 : (fun z' => Work.Construction.Theta αG F z' θ)
        = fun z' => ((1 / (4 * αG)) * Real.sin (2 * θ)) * Work.Construction.L12 F z' := by
      funext z'
      simp only [Work.Construction.Theta, Work.Construction.s2]
    rw [h1, deriv_const_mul_field, hLd]
  refine ⟨?_, ?_, ?_⟩
  -- `V(Θ) = ∂_θΘ - tan θ·Θ`: `2αG·V(Θ) = L₁₂(F)·(cos 2θ - sin²θ) = c2m θ·L₁₂(F)`.
  · simp only [Work.Construction.Vop, hpth, Work.Construction.Theta, Work.Construction.s2,
      Work.Construction.c2m, Real.tan_eq_sin_div_cos]
    rw [Real.sin_two_mul, Real.cos_two_mul']
    field_simp
    ring
  -- `U(Θ) = -3Θ - αG·z·∂_zΘ`; substituting `z ∂_z L₁₂(F) = -𝔽K(F)` gives the second form.
  · simp only [Work.Construction.Uop, hpz, Work.Construction.Theta, Work.Construction.s2]
    field_simp
    ring
  -- `ℛ(Θ) = (2 sin θ·Θ + αG sin θ·z ∂_zΘ + cos θ·∂_θΘ)/cos θ`, and
  -- `sin θ·sin 2θ + cos θ·cos 2θ = cos θ`, whence `-2ℛ(Θ) = -L₁₂(F)/αG + sin²θ·𝔽K(F)`.
  · simp only [Work.Construction.Rop, hpth, hpz, Work.Construction.Theta, Work.Construction.s2]
    rw [Real.sin_two_mul, Real.cos_two_mul']
    field_simp
    rw [Real.sin_sq]
    ring

end Work.FTS_RegExport.RXT.SysAux
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.starUopAux.Afun_mixed_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.starUopAux

noncomputable section

open Set Filter
open scoped Real Topology

/-! ## The `z`-only factor `A(z) = z/(1+z)` and its first two `D_z`-derivatives

`D_z = z·∂_z`, so `D_z A = z·A' = B` and `D_z B = z·B' = C` with

  `A(z) = z/(1+z)`,  `B(z) = z/(1+z)²`,  `C(z) = z·(1-z)/(1+z)³`,

and all three have absolute value `≤ min z 1` for `z > 0`. -/

/-- `A(z) = z/(1+z)`. -/
private def zA (z : ℝ) : ℝ := z / (1 + z)

/-- `B(z) = z/(1+z)² = D_z A`. -/
private def zB (z : ℝ) : ℝ := z / (1 + z) ^ 2

/-- `C(z) = z·(1-z)/(1+z)³ = D_z B`. -/
private def zC (z : ℝ) : ℝ := z * ((1 - z) / (1 + z) ^ 3)

/-- The two-variable function used throughout is the `θ`-independent `A`. -/
private lemma zA_fun_eq : (fun z θ : ℝ => zA z) = (fun z θ : ℝ => z / (1 + z)) := rfl

private lemma hasDerivAt_zA {z : ℝ} (hz : 0 < z) : HasDerivAt zA (1 / (1 + z) ^ 2) z := by
  have hne : (1 + z) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => y) (1 : ℝ) z := hasDerivAt_id z
  have h2 : HasDerivAt (fun y : ℝ => (1 : ℝ) + y) (1 : ℝ) z :=
    (hasDerivAt_const_add_iff (1 : ℝ)).mpr (hasDerivAt_id z)
  have h := h1.div h2 hne
  rw [show ((fun y : ℝ => y) / (fun y : ℝ => (1 : ℝ) + y)) = zA from rfl] at h
  rw [show (1 : ℝ) * (1 + z) - z * 1 = 1 by ring] at h
  exact h

private lemma hasDerivAt_zB {z : ℝ} (hz : 0 < z) :
    HasDerivAt zB ((1 - z) / (1 + z) ^ 3) z := by
  have hne : ((1 : ℝ) + z) ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => y) (1 : ℝ) z := hasDerivAt_id z
  have h2 : HasDerivAt (fun y : ℝ => ((1 : ℝ) + y) ^ 2) (2 * (1 + z) ^ (2 - 1) * 1) z :=
    ((hasDerivAt_const_add_iff (1 : ℝ)).mpr (hasDerivAt_id z)).pow 2
  have h := h1.div h2 hne
  rw [show ((fun y : ℝ => y) / (fun y : ℝ => ((1 : ℝ) + y) ^ 2)) = zB from rfl] at h
  rw [show (2 : ℕ) - 1 = 1 by norm_num, pow_one, mul_one] at h
  rw [show (1 * (1 + z) ^ 2 - z * (2 * (1 + z))) / ((1 + z) ^ 2) ^ 2
      = (1 - z) / (1 + z) ^ 3 by
    field_simp
    ring] at h
  exact h

private lemma zA_abs_le {z : ℝ} (hz : 0 < z) : |zA z| ≤ min z 1 := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  rw [zA, abs_of_nonneg (div_nonneg hz.le (by linarith))]
  refine le_min ?_ ?_
  · rw [div_le_iff₀ h1]; nlinarith
  · rw [div_le_one h1]; linarith

private lemma zB_abs_le {z : ℝ} (hz : 0 < z) : |zB z| ≤ min z 1 := by
  have h2 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
  rw [zB, abs_div, abs_of_pos hz, abs_of_pos h2]
  refine le_min ?_ ?_
  · rw [div_le_iff₀ h2]; nlinarith [sq_nonneg z, hz]
  · rw [div_le_one h2]; nlinarith [sq_nonneg z]

private lemma zC_abs_le {z : ℝ} (hz : 0 < z) : |zC z| ≤ min z 1 := by
  have h2 : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  have hzabs : |1 - z| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith
  have hcube : (1 + z) ≤ (1 + z) ^ 3 := by nlinarith [sq_nonneg (1 + z)]
  have hsq : z ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg z]
  have hval : |zC z| = z * |1 - z| / (1 + z) ^ 3 := by
    rw [zC, abs_mul, abs_of_nonneg hz.le, abs_div, abs_of_pos h2]
    ring
  rw [hval]
  refine le_min ?_ ?_
  · rw [div_le_iff₀ h2]; nlinarith [mul_le_mul_of_nonneg_left hzabs hz.le]
  · rw [div_le_one h2]; nlinarith [mul_le_mul_of_nonneg_left hzabs hz.le]

/-- `z·A'(z) = B(z)` (the `z`-multiple of the derivative). -/
private lemma zB_eq (z : ℝ) : z * (1 / (1 + z) ^ 2) = zB z := by
  rw [zB, one_div, div_eq_mul_inv]

/-! ## The mixed `D`-derivatives

`A` does not depend on `θ`, so `D_θ^a A = 0` for `a ≥ 1` and hence `D_z^b D_θ^a A = 0` for all
`b`.  For `a = 0` and `b ≤ 2` the values are `A`, `B`, `C`. -/

private lemma pth_zA_fun : Work.Spaces.pth (fun z θ : ℝ => zA z) = 0 := by
  funext z θ
  simp [Work.Spaces.pth]

private lemma Dth_zero_fun : Work.Spaces.Dth (0 : ℝ → ℝ → ℝ) = 0 := by
  funext z θ
  simp [Work.Spaces.Dth, Work.Spaces.pth]

private lemma Dth_zA_fun : Work.Spaces.Dth (fun z θ : ℝ => zA z) = 0 := by
  funext z θ
  simp [Work.Spaces.Dth, pth_zA_fun]

private lemma DthIter_zA_succ (a : ℕ) :
    Work.Spaces.DthIter (a + 1) (fun z θ : ℝ => zA z) = 0 := by
  induction a with
  | zero =>
      show Work.Spaces.DthIter 1 (fun z θ : ℝ => zA z) = 0
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
      exact Dth_zA_fun
  | succ a ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      exact Dth_zero_fun

private lemma Dz_zero_fun : Work.Spaces.Dz (0 : ℝ → ℝ → ℝ) = 0 := by
  funext z θ
  simp [Work.Spaces.Dz, Work.Spaces.pz]

private lemma DzIter_zero_fun : ∀ b : ℕ, Work.Spaces.DzIter b (0 : ℝ → ℝ → ℝ) = 0
  | 0 => rfl
  | b + 1 => by
      rw [Work.Spaces.DzIter_succ, DzIter_zero_fun b]
      exact Dz_zero_fun

private lemma mixed_zA_succ (b a : ℕ) :
    Work.Spaces.mixed b (a + 1) (fun z θ : ℝ => zA z) = 0 := by
  rw [Work.Spaces.mixed, DthIter_zA_succ a, DzIter_zero_fun b]

/-- For `a = 0` and `b ≤ 2`, the mixed derivative of `A` is `A`, `B` or `C`. -/
private lemma mixed_zA_b0_le (b : ℕ) (hb : b ≤ 2) (z θ : ℝ) (hz : 0 < z) :
    |Work.Spaces.mixed b 0 (fun z θ : ℝ => zA z) z θ| ≤ min z 1 := by
  rw [Work.Spaces.mixed_zero_right]
  interval_cases b
  · simpa using zA_abs_le hz
  · show |Work.Spaces.Dz (fun z θ : ℝ => zA z) z θ| ≤ min z 1
    rw [Work.Spaces.Dz]
    have hpz : Work.Spaces.pz (fun z θ : ℝ => zA z) z θ = 1 / (1 + z) ^ 2 :=
      (hasDerivAt_zA hz).deriv
    rw [hpz, zB_eq z]
    exact zB_abs_le hz
  · show |Work.Spaces.Dz (Work.Spaces.Dz (fun z θ : ℝ => zA z)) z θ| ≤ min z 1
    rw [Work.Spaces.Dz]
    have hdz : Work.Spaces.pz (Work.Spaces.Dz (fun z θ : ℝ => zA z)) z θ
        = (1 - z) / (1 + z) ^ 3 := by
      rw [Work.Spaces.pz]
      have h1 : (fun z' : ℝ => Work.Spaces.Dz (fun z θ : ℝ => zA z) z' θ)
          = (fun z' : ℝ => z' * deriv zA z') := by
        funext z'
        rw [Work.Spaces.Dz, Work.Spaces.pz]
      rw [h1]
      have hev : (fun z' : ℝ => z' * deriv zA z') =ᶠ[𝓝 z] zB := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        rw [(hasDerivAt_zA hz').deriv, zB_eq z']
      rw [Filter.EventuallyEq.deriv_eq hev, (hasDerivAt_zB hz).deriv]
    rw [hdz]
    exact zC_abs_le hz

/-- The mixed `D`-derivatives of the `z`-only factor `A(z) = z/(1+z)` of order `≤ 2` are bounded
by `min z 1` on `z > 0`: `A`, `D_z A = z/(1+z)^2`, `D_z^2 A = z(1-z)/(1+z)^3` all have absolute
value `≤ min z 1`, and `D_z^b D_θ^a A = 0` for `a ≥ 1` (no `θ`-dependence).  Prove it locally
from `Work.Spaces.Dz`, `Work.Spaces.Dth`, `Work.Spaces.mixed`; do not import
`Submission.Work.FTS_RegExport.RXT.StarVopDefs` (a sibling agent owns that file). -/
theorem Afun_mixed_le (b a : ℕ) (hab : a + b ≤ 2) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a (fun z θ : ℝ => z / (1 + z)) z θ| ≤ min z 1 := by
  intro z θ hz _hθ _hπ
  rcases a with _ | a
  · have hb : b ≤ 2 := by omega
    have h := mixed_zA_b0_le b hb z θ hz
    rwa [zA_fun_eq] at h
  · have h : |Work.Spaces.mixed b (a + 1) (fun z θ : ℝ => zA z) z θ| ≤ min z 1 := by
      rw [mixed_zA_succ b a]
      simpa using le_min hz.le zero_le_one
    rwa [zA_fun_eq] at h

end

end Work.FTS_RegExport.RXT.starUopAux
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT0.RXJets.slabDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.RXJets.slabDefs` — the slab of the coefficient-jet statements

The slab `(0,∞) × (0,π/2) × [0,S]` on which the order-`≤ 2` mixed jets of the three transport
coefficients `VR`, `bR`, `cR` are jointly continuous, together with its membership
characterisation and the projections used to pull a slab statement back to
`(0,∞) × [0,S]`, to the open quadrant `Q0`, and to `(0,π/2)` / `[0,S]`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT0.RXJets

set_option autoImplicit false

/-- **The slab** `(0,∞) × (0,π/2) × [0,S]` of the coefficient-jet statements. -/
def slb (S : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Set.Ioi (0 : ℝ) ×ˢ (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Icc (0 : ℝ) S)

/-- Membership in the slab, in the conjunction shape used by `intro`/`obtain`. -/
theorem mem_slb {S : ℝ} {p : ℝ × ℝ × ℝ} :
    p ∈ slb S ↔ 0 < p.1 ∧ 0 < p.2.1 ∧ p.2.1 < Real.pi / 2 ∧ 0 ≤ p.2.2 ∧ p.2.2 ≤ S := by
  simp only [slb, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc]
  tauto


/-- The `(z,τ)`-projection of the slab lies in `(0,∞) × [0,S]`. -/
theorem mapsTo_slab_zτ {S : ℝ} :
    Set.MapsTo (fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) (slb S)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) S) := by
  intro p hp
  obtain ⟨h1, -, -, h4, h5⟩ := mem_slb.mp hp
  exact ⟨h1, h4, h5⟩

/-- The `τ`-projection of the slab lies in `[0,S]`. -/
theorem mapsTo_slab_τ {S : ℝ} :
    Set.MapsTo (fun p : ℝ × ℝ × ℝ => p.2.2) (slb S) (Set.Icc (0 : ℝ) S) := by
  intro p hp
  obtain ⟨-, -, -, h4, h5⟩ := mem_slb.mp hp
  exact ⟨h4, h5⟩

/-- The `θ`-projection of the slab lies in `(0,π/2)`. -/
theorem mapsTo_slab_θ {S : ℝ} :
    Set.MapsTo (fun p : ℝ × ℝ × ℝ => p.2.1) (slb S) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  intro p hp
  obtain ⟨-, h2, h3, -, -⟩ := mem_slb.mp hp
  exact ⟨h2, h3⟩

end Work.FTS_RegExport.RXT0.RXJets
end
end
-- ===== merged: Submission.Work.H2.WPQ.z_term_le_smoothQuad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2.WPQ

open scoped Real

set_option autoImplicit false
set_option maxHeartbeats 0


end Work.H2.WPQ
end
-- ===== merged: Submission.Work.H2W.PsiSlices.pzIter_dilate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2W.PsiSlices


end Work.H2W.PsiSlices
end
-- ===== merged: Submission.Work.R1G.DecayInZ_gA =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Topology

namespace Work.R1G

/-! ## A monomial decay estimate -/


/-! ## Decay of the radial factor and its first two derivatives -/








end Work.R1G
end
end
