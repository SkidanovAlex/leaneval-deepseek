import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Coercivity.HkMem_mono
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.wsSliceRight
import Submission.Work.FTS.H2.ModalSol.Defs
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.LWP.VorticityAPI
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.SolutionDelivery.Scaling.vorticityDecay_rescaleDatum
import Submission.Work.SolutionDelivery.Scaling.vorticity_rescale
import Submission.Work.SolutionDelivery.Slices
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.mixed_sq_integrableOn
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.OmegaCutSupport
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.FTS.BSSwirl.weakDivFree_swirlField =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The swirl field is weakly divergence free

A swirl field `ω = f(r,z) • e_θ` (see `Work.FTS.BSSwirl.swirlField`) is divergence free in the
distributional sense: the only nonvanishing component is tangential and the scalar prefactor is
invariant under the rotations about the `x₃`-axis whose generator is `e_θ`.

The proof is the standard "the distributional angular derivative of a rotation invariant weight
vanishes": for a rotation invariant, measurable, bounded weight `w` and a smooth compactly supported
test function `φ`, `∫ x, w x * (fderiv ℝ φ x) (angularVec x) = 0`
(`Work.FTS.BSSwirl.integral_invariant_weight_fderiv_angularVec`).  Applying this to the bounded
approximations `wₙ x = ⟪ω x, e_θ x⟫ * (r x + 1/(n+1))⁻¹` of the weight `⟪ω x, e_θ x⟫ / r` and
passing to the limit with the dominated convergence theorem gives `∫ x, (fderiv ℝ k x) (ω x) = 0`
for every smooth compactly supported `k`, i.e. `WeakDivFree ω`.
-/

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Work.FTS.BSSwirl

/-- Rotation equivariance of the swirl field. -/
theorem swirlField_rotLE (f : ℝ → ℝ → ℝ) (t : ℝ) (x : R3) :
    swirlField f (Work.ConstructionInstance.rotLE t x)
      = Work.ConstructionInstance.rotLE t (swirlField f x) := by
  rw [swirlField_apply, swirlField_apply, Work.ConstructionInstance.radial_rotLE,
    Work.ConstructionInstance.axial_rotLE, Work.ConstructionInstance.eTheta_rotLE]
  exact (map_smul _ _ _).symm

/-- The angular component `⟪ω x, e_θ x⟫` of a swirl field is rotation invariant. -/
theorem inner_swirlField_eTheta_rotLE (f : ℝ → ℝ → ℝ) (t : ℝ) (x : R3) :
    inner ℝ (swirlField f (Work.ConstructionInstance.rotLE t x))
        (Work.Cyl.eTheta (Work.ConstructionInstance.rotLE t x))
      = inner ℝ (swirlField f x) (Work.Cyl.eTheta x) := by
  rw [swirlField_rotLE, Work.ConstructionInstance.eTheta_rotLE]
  exact LinearIsometryEquiv.inner_map_map _ _ _

/-- `|⟪ω x, e_θ x⟫| ≤ M` for a swirl field bounded by `M`. -/
theorem abs_inner_swirlField_eTheta_le (f : ℝ → ℝ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ x, ‖swirlField f x‖ ≤ M) (x : R3) :
    |inner ℝ (swirlField f x) (Work.Cyl.eTheta x)| ≤ M := by
  calc |inner ℝ (swirlField f x) (Work.Cyl.eTheta x)|
      ≤ ‖swirlField f x‖ * ‖Work.Cyl.eTheta x‖ := abs_real_inner_le_norm _ _
    _ ≤ M * 1 := mul_le_mul (hbdd x) (norm_eTheta_le_one x) (norm_nonneg _) hM
    _ = M := mul_one M

/-- **The weight identity.**  For a swirl field `ω = f • e_θ`, the angular derivative of a test
function `k`, weighted by the radial weight `⟪ω x, e_θ x⟫ / r`, is the derivative of `k` in the
direction `ω x`. -/
theorem inner_swirlField_eTheta_div_radial_mul_fderiv_angularVec
    (f : ℝ → ℝ → ℝ) (k : R3 → ℝ) (x : R3) :
    (inner ℝ (swirlField f x) (Work.Cyl.eTheta x) / Work.Cyl.radial x)
        * (fderiv ℝ k x) (Work.Cyl.angularVec x)
      = (fderiv ℝ k x) (swirlField f x) := by
  by_cases hr : Work.Cyl.radial x = 0
  · have he : Work.Cyl.eTheta x = 0 := by
      rw [Work.Cyl.eTheta, hr, one_div, inv_zero, zero_smul]
    have ha : Work.Cyl.angularVec x = 0 := by
      have h := Work.Cyl.norm_angularVec x
      rw [hr] at h
      exact norm_eq_zero.mp h
    rw [he, ha, inner_zero_right, hr, div_zero, zero_mul, swirlField_apply, he, smul_zero,
      map_zero]
  · have hang : Work.Cyl.angularVec x = Work.Cyl.radial x • Work.Cyl.eTheta x := by
      rw [Work.Cyl.eTheta, smul_smul, one_div, mul_inv_cancel₀ hr, one_smul]
    have hinn : inner ℝ (swirlField f x) (Work.Cyl.eTheta x)
        = f (Work.Cyl.radial x) (Work.Cyl.axial x) := by
      rw [swirlField_apply, real_inner_smul_left, Work.Cyl.inner_eTheta_eTheta x hr, mul_one]
    calc (inner ℝ (swirlField f x) (Work.Cyl.eTheta x) / Work.Cyl.radial x)
          * (fderiv ℝ k x) (Work.Cyl.angularVec x)
        = (f (Work.Cyl.radial x) (Work.Cyl.axial x) / Work.Cyl.radial x)
          * (Work.Cyl.radial x * (fderiv ℝ k x) (Work.Cyl.eTheta x)) := by
            rw [hinn, hang, map_smul, smul_eq_mul]
      _ = f (Work.Cyl.radial x) (Work.Cyl.axial x) * (fderiv ℝ k x) (Work.Cyl.eTheta x) := by
            field_simp
      _ = (fderiv ℝ k x) (swirlField f x) := by
            rw [swirlField_apply, map_smul, smul_eq_mul]

/-- The angular vector `e_θ` is a.e. strongly measurable. -/
theorem aestronglyMeasurable_eTheta :
    AEStronglyMeasurable (Work.Cyl.eTheta) (volume : Measure R3) := by
  have hrad : Continuous (Work.Cyl.radial) := by
    unfold Work.Cyl.radial Work.Cyl.radSq
    fun_prop
  have h1 : AEStronglyMeasurable (fun x : R3 => 1 / Work.Cyl.radial x) volume := by
    have hinv : Measurable (Work.Cyl.radial⁻¹) := hrad.measurable.inv
    have hfun : (Work.Cyl.radial⁻¹ : R3 → ℝ) = fun x => 1 / Work.Cyl.radial x := by
      funext x
      rw [Pi.inv_apply, one_div]
    rw [hfun] at hinv
    exact hinv.aestronglyMeasurable
  have h2 : AEStronglyMeasurable (Work.Cyl.angularVec) volume := by
    unfold Work.Cyl.angularVec
    fun_prop
  change AEStronglyMeasurable
    (fun x : R3 => (1 / Work.Cyl.radial x) • Work.Cyl.angularVec x) volume
  exact h1.smul h2


/-- A bounded a.e.-strongly-measurable real function whose support is contained in a closed ball
is integrable for the Lebesgue measure on `ℝ³`. -/
theorem integrable_of_bdd_of_support_subset_closedBall {g : R3 → ℝ} {C r : ℝ}
    (hg : AEStronglyMeasurable g (volume : Measure R3)) (hbdd : ∀ x, ‖g x‖ ≤ C)
    (hsupp : Function.support g ⊆ Metric.closedBall (0 : R3) r) :
    Integrable g volume := by
  refine (integrableOn_iff_integrable_of_support_subset hsupp).mp ?_
  exact IntegrableOn.of_bound measure_closedBall_lt_top
    (hg.mono_measure Measure.restrict_le_self) C (Eventually.of_forall hbdd)

/-- **The distributional angular derivative of a rotation invariant weight vanishes.**

For `w : ℝ³ → ℝ` measurable, bounded and invariant under the rotations `rotLE t` about the `x₃`-axis,
and every smooth compactly supported `φ`, the integral of `w` against the angular derivative
`x ↦ (fderiv ℝ φ x) (angularVec x)` of `φ` vanishes.

Proof: for every `h` the change of variables `x ↦ rotLE h x` (`MeasureTheory.integral_comp`, a
measure preserving linear isometry) together with the invariance of `w` gives
`∫ x, w x * (φ (rotLE h x) - φ x) = 0`.  Dividing by `h` and letting `h → 0` along `hₙ = 1/(n+1)`
computes the limit by dominated convergence, the pointwise limit being the derivative of
`s ↦ φ (rotLE s x)` at `0`. -/
theorem integral_invariant_weight_fderiv_angularVec_local
    {w : R3 → ℝ} {Cw : ℝ}
    (hw_meas : AEStronglyMeasurable w (volume : Measure R3))
    (hw_bdd : ∀ x, |w x| ≤ Cw)
    (hw_inv : ∀ (t : ℝ) (x : R3), w (Work.ConstructionInstance.rotLE t x) = w x)
    {φ : R3 → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n φ) (hφc : HasCompactSupport φ) :
    ∫ x, w x * (fderiv ℝ φ x) (Work.Cyl.angularVec x) = 0 := by
  have hCwnn : 0 ≤ Cw := le_trans (abs_nonneg _) (hw_bdd 0)
  have hrot0 : ∀ x : R3, Work.ConstructionInstance.rotLE 0 x = x := by
    intro x
    ext i
    fin_cases i <;>
      simp [Work.ConstructionInstance.rotLE_apply, Work.ConstructionInstance.rotCoord]
  obtain ⟨Cφ, hCφnn, hCφ⟩ : ∃ C, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ φ x‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hφc.fderiv ℝ).exists_bound_of_continuous
      ((hφ 1).continuous_fderiv (by norm_num))
    exact ⟨C, le_trans (norm_nonneg _) (hC 0), hC⟩
  obtain ⟨Bφ, hBφnn, hBφ⟩ : ∃ B, 0 ≤ B ∧ ∀ x, ‖φ x‖ ≤ B := by
    obtain ⟨B, hB⟩ := ((hφ 0).continuous).bounded_above_of_compact_support hφc
    exact ⟨B, le_trans (norm_nonneg _) (hB 0), hB⟩
  obtain ⟨Rφ, hRφnn, hRφ⟩ : ∃ R, 0 ≤ R ∧ Function.support φ ⊆ Metric.closedBall (0 : R3) R := by
    obtain ⟨R, hR⟩ := (show Bornology.IsBounded (tsupport φ) from
      (show IsCompact (tsupport φ) from hφc).isBounded).subset_closedBall (0 : R3)
    exact ⟨|R|, abs_nonneg R, fun x hx =>
      Metric.closedBall_subset_closedBall (le_abs_self R) (hR (subset_tsupport φ hx))⟩
  have hφdiff : ∀ x ∈ (Set.univ : Set R3), DifferentiableAt ℝ φ x :=
    fun x _ => ((hφ 1).differentiable (by norm_num)) x
  have hlip : ∀ y z : R3, ‖φ y - φ z‖ ≤ Cφ * ‖y - z‖ := fun y z =>
    Convex.norm_image_sub_le_of_norm_fderiv_le hφdiff (fun x _ => hCφ x) convex_univ
      (Set.mem_univ y) (Set.mem_univ z)
  have hwφ_int : Integrable (fun x : R3 => w x * φ x) volume := by
    refine integrable_of_bdd_of_support_subset_closedBall (C := Cw * Bφ) (r := Rφ)
      (hw_meas.mul ((hφ 0).continuous.aestronglyMeasurable)) ?_ ?_
    · intro x
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hw_bdd x) (hBφ x) (abs_nonneg _) hCwnn
    · intro x hx
      exact hRφ (Function.mem_support.mpr fun hzero =>
        (Function.mem_support.mp hx) (by rw [hzero, mul_zero]))
  set hh : ℕ → ℝ := fun n => 1 / (n + 1) with hhh
  have hh_pos : ∀ n, 0 < hh n := fun n => by rw [hhh]; positivity
  have hh_ne : ∀ n, hh n ≠ 0 := fun n => ne_of_gt (hh_pos n)
  have hh_lim : Tendsto hh atTop (𝓝 (0 : ℝ)) := by
    rw [hhh]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  set G : ℕ → R3 → ℝ := fun n x =>
    (hh n)⁻¹ * (w x * (φ (Work.ConstructionInstance.rotLE (hh n) x) - φ x)) with hG
  have hrot_cont : ∀ n, Continuous fun x : R3 =>
      φ (Work.ConstructionInstance.rotLE (hh n) x) :=
    fun n => (hφ 0).continuous.comp (Work.ConstructionInstance.rotLE (hh n)).continuous
  have hG_meas : ∀ n, AEStronglyMeasurable (G n) volume := by
    intro n
    simp only [hG]
    refine AEStronglyMeasurable.const_mul ?_ _
    exact hw_meas.mul
      ((hrot_cont n).aestronglyMeasurable.sub ((hφ 0).continuous.aestronglyMeasurable))
  have hcurve : ∀ x, Tendsto (fun t : ℝ =>
      (φ (Work.ConstructionInstance.rotLE t x) - φ x) / t)
      (𝓝[≠] (0 : ℝ)) (𝓝 ((fderiv ℝ φ x) (Work.Cyl.angularVec x))) := by
    intro x
    have h1 : HasDerivAt (fun s : ℝ => Work.ConstructionInstance.rotLE s x)
        (Work.Cyl.angularVec (Work.ConstructionInstance.rotLE 0 x)) 0 :=
      hasDerivAt_rotLE 0 x
    have h2 : HasFDerivAt φ (fderiv ℝ φ x) (Work.ConstructionInstance.rotLE 0 x) := by
      rw [hrot0 x]
      exact (((hφ 1).differentiable (by norm_num)) x).hasFDerivAt
    have hsl := (hasDerivAt_iff_tendsto_slope).mp (h2.comp_hasDerivAt 0 h1)
    rw [hrot0 x] at hsl
    have hsl1 : Tendsto (fun b : ℝ => (φ (Work.ConstructionInstance.rotLE b x)
        - φ (Work.ConstructionInstance.rotLE 0 x)) / b) (𝓝[≠] (0 : ℝ))
        (𝓝 ((fderiv ℝ φ x) (Work.Cyl.angularVec x))) := by
      simpa [slope_fun_def_field, Function.comp_apply] using hsl
    exact hsl1.congr' (Eventually.of_forall fun b => by rw [hrot0 x])
  have hconv : ∀ᵐ x ∂volume, Tendsto (fun n => G n x) atTop
      (𝓝 (w x * (fderiv ℝ φ x) (Work.Cyl.angularVec x))) := by
    refine Eventually.of_forall fun x => ?_
    have hhw : Tendsto hh atTop (𝓝[≠] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hh_lim, Eventually.of_forall hh_ne⟩
    have hc : Tendsto (fun n => (φ (Work.ConstructionInstance.rotLE (hh n) x) - φ x)
        / (hh n)) atTop (𝓝 ((fderiv ℝ φ x) (Work.Cyl.angularVec x))) :=
      (hcurve x).comp hhw
    have hfun : ∀ n, G n x = w x * ((φ (Work.ConstructionInstance.rotLE (hh n) x) - φ x)
        / (hh n)) := by
      intro n
      simp only [hG]
      rw [div_eq_mul_inv]
      ring
    simp only [hfun]
    exact tendsto_const_nhds.mul hc
  set bound : R3 → ℝ := fun x =>
    (Cw * Cφ * Rφ) * (Metric.closedBall (0 : R3) Rφ).indicator (fun _ => (1 : ℝ)) x with hbound
  have hbound_int : Integrable bound volume := by
    have hIntOn : IntegrableOn (fun _ : R3 => (1 : ℝ)) (Metric.closedBall (0 : R3) Rφ) volume :=
      IntegrableOn.of_bound measure_closedBall_lt_top aestronglyMeasurable_const 1
        (Eventually.of_forall fun x => by simp)
    have hInt := IntegrableOn.integrable_indicator hIntOn measurableSet_closedBall
    simp only [hbound]
    exact hInt.const_mul (Cw * Cφ * Rφ)
  have hdom : ∀ n, ∀ᵐ x ∂volume, ‖G n x‖ ≤ bound x := by
    intro n
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ Metric.closedBall (0 : R3) Rφ
    · simp only [hbound, Set.indicator_of_mem hx, mul_one, hG, Real.norm_eq_abs, abs_mul]
      have h1 : |φ (Work.ConstructionInstance.rotLE (hh n) x) - φ x|
          ≤ Cφ * (|hh n| * Work.Cyl.radial x) := by
        have h := hlip (Work.ConstructionInstance.rotLE (hh n) x) x
        rw [Real.norm_eq_abs] at h
        calc |φ (Work.ConstructionInstance.rotLE (hh n) x) - φ x|
            ≤ Cφ * ‖Work.ConstructionInstance.rotLE (hh n) x - x‖ := h
          _ ≤ Cφ * (|hh n| * Work.Cyl.radial x) :=
              mul_le_mul_of_nonneg_left (norm_rotLE_sub_le (hh n) x) hCφnn
      have h3 : Work.Cyl.radial x ≤ Rφ := by
        have h4 : Work.Cyl.radial x ≤ ‖x‖ := by
          rw [← Work.Cyl.rho_eq_norm]
          exact Work.Cyl.radial_le_rho x
        have h5 : ‖x‖ ≤ Rφ := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hx
        linarith
      calc |(hh n)⁻¹| * (|w x| * |φ (Work.ConstructionInstance.rotLE (hh n) x) - φ x|)
          ≤ |(hh n)⁻¹| * (Cw * (Cφ * (|hh n| * Work.Cyl.radial x))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul (hw_bdd x) h1 (abs_nonneg _) hCwnn) (abs_nonneg _)
        _ = Cw * Cφ * Work.Cyl.radial x := by
            have habs : |hh n| ≠ 0 := abs_ne_zero.mpr (hh_ne n)
            calc |(hh n)⁻¹| * (Cw * (Cφ * (|hh n| * Work.Cyl.radial x)))
                = Cw * Cφ * Work.Cyl.radial x * (|hh n|⁻¹ * |hh n|) := by
                  rw [abs_inv]
                  ring
              _ = Cw * Cφ * Work.Cyl.radial x := by
                  rw [inv_mul_cancel₀ habs, mul_one]
        _ ≤ Cw * Cφ * Rφ :=
            mul_le_mul_of_nonneg_left h3 (mul_nonneg hCwnn hCφnn)
    · simp only [hbound, Set.indicator_of_notMem hx, mul_zero, hG, Real.norm_eq_abs]
      have hφx : φ x = 0 := by
        by_contra h
        exact hx (hRφ (Function.mem_support.mpr h))
      have hφRx : φ (Work.ConstructionInstance.rotLE (hh n) x) = 0 := by
        by_contra h
        have hmem : Work.ConstructionInstance.rotLE (hh n) x ∈ Metric.closedBall (0 : R3) Rφ :=
          hRφ (Function.mem_support.mpr h)
        have hnorm : ‖Work.ConstructionInstance.rotLE (hh n) x‖ = ‖x‖ :=
          (Work.ConstructionInstance.rotLE (hh n)).norm_map x
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hnorm] at hmem
        exact hx (by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hmem)
      rw [hφx, hφRx, sub_zero, mul_zero, mul_zero, abs_zero]
  have hzero : ∀ n, ∫ x, G n x = 0 := by
    intro n
    have hInt1 : Integrable (fun x => w (Work.ConstructionInstance.rotLE (hh n) x)
        * φ (Work.ConstructionInstance.rotLE (hh n) x)) volume :=
      (MeasureTheory.integrable_comp (Work.ConstructionInstance.rotLE (hh n))
        (fun y => w y * φ y)).mpr hwφ_int
    have hstep : (∫ x, (hh n)⁻¹ * (w x * (φ (Work.ConstructionInstance.rotLE (hh n) x) - φ x)))
        = (hh n)⁻¹ * (∫ x, w x * (φ (Work.ConstructionInstance.rotLE (hh n) x) - φ x)) :=
      integral_const_mul _ _
    have hcongr : (∫ x, w x * (φ (Work.ConstructionInstance.rotLE (hh n) x) - φ x))
        = (∫ x, (w (Work.ConstructionInstance.rotLE (hh n) x)
            * φ (Work.ConstructionInstance.rotLE (hh n) x) - w x * φ x)) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show w x * (φ (Work.ConstructionInstance.rotLE (hh n) x) - φ x)
        = w (Work.ConstructionInstance.rotLE (hh n) x)
            * φ (Work.ConstructionInstance.rotLE (hh n) x) - w x * φ x
      rw [hw_inv (hh n) x]
      ring
    have hsub : (∫ x, (w (Work.ConstructionInstance.rotLE (hh n) x)
          * φ (Work.ConstructionInstance.rotLE (hh n) x) - w x * φ x))
        = (∫ x, w (Work.ConstructionInstance.rotLE (hh n) x)
            * φ (Work.ConstructionInstance.rotLE (hh n) x)) - (∫ x, w x * φ x) :=
      integral_sub hInt1 hwφ_int
    have hcv : (∫ x, w (Work.ConstructionInstance.rotLE (hh n) x)
        * φ (Work.ConstructionInstance.rotLE (hh n) x)) = ∫ x, w x * φ x :=
      MeasureTheory.integral_comp (Work.ConstructionInstance.rotLE (hh n))
        (fun y => w y * φ y)
    simp only [hG]
    rw [hstep, hcongr, hsub, hcv, sub_self, mul_zero]
  have hdct := tendsto_integral_of_dominated_convergence bound hG_meas hbound_int hdom hconv
  rw [show (fun n => ∫ x, G n x) = fun _ => (0 : ℝ) from funext hzero] at hdct
  exact (tendsto_nhds_unique tendsto_const_nhds hdct).symm

/-- Main auxiliary form: assuming the invariant-weight identity, the swirl field is weakly
divergence free. -/
theorem weakDivFree_swirlField_of_invariantWeight
    (hInvW : ∀ (w : R3 → ℝ) (Cw : ℝ),
      AEStronglyMeasurable w (volume : Measure R3) → (∀ x, |w x| ≤ Cw) →
        (∀ (t : ℝ) (x : R3), w (Work.ConstructionInstance.rotLE t x) = w x) →
        ∀ (φ : R3 → ℝ), (∀ n : ℕ, ContDiff ℝ n φ) → HasCompactSupport φ →
          ∫ x, w x * (fderiv ℝ φ x) (Work.Cyl.angularVec x) = 0)
    {f : ℝ → ℝ → ℝ} {M R : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ x, ‖swirlField f x‖ ≤ M)
    (hmeas : AEStronglyMeasurable (swirlField f) (volume : Measure R3))
    (hsupp : ∀ x, swirlField f x ≠ 0 → x ∈ Metric.closedBall (0 : R3) R) :
    WeakDivFree (swirlField f) := by
  rw [weakDivFree_iff]
  intro k hk hksupp
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖fderiv ℝ k x‖ ≤ C :=
    (hksupp.fderiv ℝ).exists_bound_of_continuous ((hk 1).continuous_fderiv (by norm_num))
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hrad : Continuous (Work.Cyl.radial) := by
    unfold Work.Cyl.radial Work.Cyl.radSq
    fun_prop
  have hfd : Continuous (fun x : R3 => (fderiv ℝ k x) (Work.Cyl.angularVec x)) :=
    ((hk 1).continuous_fderiv (by norm_num)).clm_apply (by
      unfold Work.Cyl.angularVec
      fun_prop)
  set eps : ℕ → ℝ := fun n => 1 / (n + 1) with heps
  have heps_pos : ∀ n, 0 < eps n := by
    intro n
    rw [heps]
    positivity
  set W : ℕ → R3 → ℝ := fun n x =>
    inner ℝ (swirlField f x) (Work.Cyl.eTheta x) * (Work.Cyl.radial x + eps n)⁻¹ with hW
  set Fn : ℕ → R3 → ℝ := fun n x => W n x * (fderiv ℝ k x) (Work.Cyl.angularVec x) with hFn
  set bound : R3 → ℝ := fun x =>
    (M * C) * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) x with hbound
  have hinner_aesm : AEStronglyMeasurable
      (fun x : R3 => inner ℝ (swirlField f x) (Work.Cyl.eTheta x)) volume :=
    hmeas.inner aestronglyMeasurable_eTheta
  have hWm : ∀ n, AEStronglyMeasurable (W n) volume := by
    intro n
    have hden : AEStronglyMeasurable (fun x : R3 => (Work.Cyl.radial x + eps n)⁻¹) volume := by
      have hcont : Continuous (fun x : R3 => (Work.Cyl.radial x + eps n)⁻¹) := by
        apply Continuous.inv₀ _ (fun x => ?_)
        · exact hrad.add continuous_const
        · exact ne_of_gt (by linarith [Work.Cyl.radial_nonneg x, heps_pos n])
      exact hcont.aestronglyMeasurable
    simp only [hW]
    exact hinner_aesm.mul hden
  have hWbd : ∀ n, ∀ x, |W n x| ≤ M / eps n := by
    intro n x
    simp only [hW]
    have hpos : 0 < (Work.Cyl.radial x + eps n)⁻¹ :=
      inv_pos.mpr (by linarith [Work.Cyl.radial_nonneg x, heps_pos n])
    rw [abs_mul, abs_of_pos hpos]
    calc |inner ℝ (swirlField f x) (Work.Cyl.eTheta x)| * (Work.Cyl.radial x + eps n)⁻¹
        ≤ M * (Work.Cyl.radial x + eps n)⁻¹ :=
          mul_le_mul_of_nonneg_right (abs_inner_swirlField_eTheta_le f hM hbdd x) (le_of_lt hpos)
      _ ≤ M * (eps n)⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ hM
          exact (inv_le_inv₀ (by linarith [Work.Cyl.radial_nonneg x, heps_pos n])
            (heps_pos n)).mpr (by linarith [Work.Cyl.radial_nonneg x])
      _ = M / eps n := div_eq_mul_inv M (eps n)
  have hWinv : ∀ n, ∀ (t : ℝ) (x : R3), W n (Work.ConstructionInstance.rotLE t x) = W n x := by
    intro n t x
    show inner ℝ (swirlField f (Work.ConstructionInstance.rotLE t x))
          (Work.Cyl.eTheta (Work.ConstructionInstance.rotLE t x))
        * (Work.Cyl.radial (Work.ConstructionInstance.rotLE t x) + eps n)⁻¹
      = inner ℝ (swirlField f x) (Work.Cyl.eTheta x) * (Work.Cyl.radial x + eps n)⁻¹
    rw [inner_swirlField_eTheta_rotLE f t x, Work.ConstructionInstance.radial_rotLE]
  have hbound_int : Integrable bound volume := by
    have hIntOn : IntegrableOn (fun _ : R3 => (1 : ℝ)) (Metric.closedBall (0 : R3) R) volume :=
      IntegrableOn.of_bound measure_closedBall_lt_top aestronglyMeasurable_const 1
        (Eventually.of_forall fun x => by simp)
    have hInt : Integrable ((Metric.closedBall (0 : R3) R).indicator (fun _ : R3 => (1 : ℝ)))
        volume := IntegrableOn.integrable_indicator hIntOn measurableSet_closedBall
    simp only [hbound]
    exact hInt.const_mul (M * C)
  have hbd : ∀ n, ∀ᵐ x ∂volume, ‖Fn n x‖ ≤ bound x := by
    intro n
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ Metric.closedBall (0 : R3) R
    · simp only [hbound, Set.indicator_of_mem hx, mul_one, hFn, hW, Real.norm_eq_abs, abs_mul]
      have h1 : |inner ℝ (swirlField f x) (Work.Cyl.eTheta x)|
          * |(Work.Cyl.radial x + eps n)⁻¹| ≤ M * (Work.Cyl.radial x + eps n)⁻¹ := by
        have hpos : 0 < (Work.Cyl.radial x + eps n)⁻¹ :=
          inv_pos.mpr (by linarith [Work.Cyl.radial_nonneg x, heps_pos n])
        rw [abs_of_pos hpos]
        exact mul_le_mul_of_nonneg_right (abs_inner_swirlField_eTheta_le f hM hbdd x) (le_of_lt hpos)
      have h2 : |(fderiv ℝ k x) (Work.Cyl.angularVec x)| ≤ C * Work.Cyl.radial x := by
        have h3 : |(fderiv ℝ k x) (Work.Cyl.angularVec x)|
            ≤ ‖fderiv ℝ k x‖ * ‖Work.Cyl.angularVec x‖ := by
          simpa [Real.norm_eq_abs] using
            ContinuousLinearMap.le_opNorm (fderiv ℝ k x) (Work.Cyl.angularVec x)
        calc |(fderiv ℝ k x) (Work.Cyl.angularVec x)|
            ≤ ‖fderiv ℝ k x‖ * ‖Work.Cyl.angularVec x‖ := h3
          _ ≤ C * Work.Cyl.radial x := by
              rw [Work.Cyl.norm_angularVec]
              exact mul_le_mul_of_nonneg_right (hC x) (Work.Cyl.radial_nonneg x)
      calc |inner ℝ (swirlField f x) (Work.Cyl.eTheta x)| * |(Work.Cyl.radial x + eps n)⁻¹|
            * |(fderiv ℝ k x) (Work.Cyl.angularVec x)|
          ≤ (M * (Work.Cyl.radial x + eps n)⁻¹) * (C * Work.Cyl.radial x) :=
            mul_le_mul h1 h2 (abs_nonneg _)
              (mul_nonneg hM (le_of_lt (inv_pos.mpr
                (by linarith [Work.Cyl.radial_nonneg x, heps_pos n]))))
        _ = (M * C) * (Work.Cyl.radial x * (Work.Cyl.radial x + eps n)⁻¹) := by ring
        _ ≤ (M * C) * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hM hCnn)
            rw [← div_eq_mul_inv,
              div_le_one (by linarith [Work.Cyl.radial_nonneg x, heps_pos n])]
            linarith [heps_pos n]
        _ = M * C := mul_one _
    · simp only [hbound, Set.indicator_of_notMem hx, mul_zero, hFn, hW]
      have hzero : inner ℝ (swirlField f x) (Work.Cyl.eTheta x) = 0 := by
        by_contra h
        exact hx (hsupp x (fun hω => h (by rw [hω, inner_zero_left])))
      rw [hzero, zero_mul, zero_mul, norm_zero]
  have hconv : ∀ᵐ x ∂volume, Tendsto (fun n => Fn n x) atTop
      (𝓝 ((fderiv ℝ k x) (swirlField f x))) := by
    refine Eventually.of_forall fun x => ?_
    by_cases hr : Work.Cyl.radial x = 0
    · have he : Work.Cyl.eTheta x = 0 := by
        rw [Work.Cyl.eTheta, hr, one_div, inv_zero, zero_smul]
      have hFn0 : ∀ n, Fn n x = 0 := by
        intro n
        simp only [hFn, hW]
        rw [he, inner_zero_right, zero_mul, zero_mul]
      have hFl0 : (fderiv ℝ k x) (swirlField f x) = 0 := by
        rw [swirlField_apply, he, smul_zero, map_zero]
      rw [hFl0]
      simp only [hFn0]
      exact tendsto_const_nhds
    · have hrpos : 0 < Work.Cyl.radial x :=
        lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm hr)
      have hden : Tendsto (fun n : ℕ => Work.Cyl.radial x + eps n) atTop
          (𝓝 (Work.Cyl.radial x)) := by
        have hbase : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have hsum : Tendsto (fun n : ℕ => Work.Cyl.radial x + (1 : ℝ) / (n + 1)) atTop
            (𝓝 (Work.Cyl.radial x + 0)) := tendsto_const_nhds.add hbase
        rw [add_zero] at hsum
        have hfun : (fun n : ℕ => Work.Cyl.radial x + eps n)
            = fun n : ℕ => Work.Cyl.radial x + (1 : ℝ) / (n + 1) := by
          funext n
          rw [heps]
        rw [hfun]
        exact hsum
      have hinv : Tendsto (fun n : ℕ => (Work.Cyl.radial x + eps n)⁻¹) atTop
          (𝓝 ((Work.Cyl.radial x)⁻¹)) := hden.inv₀ hr
      have hWlim : Tendsto (fun n => W n x) atTop
          (𝓝 (inner ℝ (swirlField f x) (Work.Cyl.eTheta x) * (Work.Cyl.radial x)⁻¹)) := by
        simp only [hW]
        exact tendsto_const_nhds.mul hinv
      have hconst : Tendsto (fun _ : ℕ => (fderiv ℝ k x) (Work.Cyl.angularVec x)) atTop
          (𝓝 ((fderiv ℝ k x) (Work.Cyl.angularVec x))) := tendsto_const_nhds
      have hlim := hWlim.mul hconst
      simp only [hFn]
      have heq : (inner ℝ (swirlField f x) (Work.Cyl.eTheta x) * (Work.Cyl.radial x)⁻¹)
          * (fderiv ℝ k x) (Work.Cyl.angularVec x) = (fderiv ℝ k x) (swirlField f x) := by
        rw [← div_eq_mul_inv]
        exact inner_swirlField_eTheta_div_radial_mul_fderiv_angularVec f k x
      rw [heq] at hlim
      exact hlim
  have hzero : ∀ n, ∫ x, Fn n x = 0 := by
    intro n
    have h1 := hInvW (W n) (M / eps n) (hWm n) (hWbd n) (hWinv n) k hk hksupp
    simp only [hFn]
    exact h1
  have hmeasFn : ∀ n, AEStronglyMeasurable (Fn n) volume := by
    intro n
    simp only [hFn]
    exact (hWm n).mul hfd.aestronglyMeasurable
  have hdct := tendsto_integral_of_dominated_convergence bound hmeasFn hbound_int hbd hconv
  rw [show (fun n => ∫ x, Fn n x) = fun _ => (0 : ℝ) from funext hzero] at hdct
  exact (tendsto_nhds_unique tendsto_const_nhds hdct).symm

theorem weakDivFree_swirlField {f : ℝ → ℝ → ℝ} {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hbdd : ∀ x, ‖Work.FTS.BSSwirl.swirlField f x‖ ≤ M)
    (hmeas : MeasureTheory.AEStronglyMeasurable (Work.FTS.BSSwirl.swirlField f)
      MeasureTheory.volume)
    (hsupp : ∀ x, Work.FTS.BSSwirl.swirlField f x ≠ 0 → x ∈ Metric.closedBall 0 R) :
    Work.FTS.BSSwirl.WeakDivFree (Work.FTS.BSSwirl.swirlField f) :=
  weakDivFree_swirlField_of_invariantWeight
    (fun w Cw h1 h2 h3 _φ h4 h5 =>
      integral_invariant_weight_fderiv_angularVec_local h1 h2 h3 h4 h5)
    hM hbdd hmeas hsupp

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.HardyAlt.l12dens_continuousAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T.HardyAlt

set_option maxHeartbeats 1000000

/-! ## Auxiliary facts for `l12dens_continuousAt`

Since `K θ = 3 sin θ cos²θ` and `Elliptic.sinCos2 θ = sin θ cos²θ`, we have

  `L12dens K f s = 3 · F_*(f)(s) / s`,

where `F_*(f)(s) = ∫_θ f(s,θ) sinθcos²θ dθ` is the angular moment (`Work.Elliptic.Fstar`), and
`s ↦ 1/s` is continuous at `z > 0`.  So it suffices to prove that `F_*(f)` is continuous at `z`.

`Work.FTS.EllipticEst.Blocks.moment_relation` exhibits `F_*(f)` as the primitive of the angular
moment `M(r) = ∫_θ ∂_z f(r,θ) sinθcos²θ dθ` of the radial derivative, and the pointwise bound
`|M(r)| ≤ √(π/2) · √(B(r))`, where `B(r) = ∫_θ HkIntegrand α 4 f r θ`, shows that the increment of
`F_*(f)` is dominated by the primitive of `√B`.  The latter is continuous at `z` because `B` is
integrable (`HkMem.2`) and `√B ≤ |B| + 1`. -/

/-- `√x ≤ |x| + 1`. -/
private lemma sqrt_le_abs_add_one (x : ℝ) : Real.sqrt x ≤ |x| + 1 := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [le_abs_self x, abs_nonneg x, sq_abs x, sq_nonneg x]

/-- **`L12dens` in terms of the angular moment.**  `L12dens K f s = 3 · F_*(f)(s) / s`. -/
theorem L12dens_eq_three_Fstar (f : ℝ → ℝ → ℝ) (s : ℝ) :
    Work.FM.L12dens Work.Spaces.K f s = 3 * Work.Elliptic.Fstar f s / s := by
  have hpt : ∀ θ : ℝ, Work.Spaces.K θ * f s θ = 3 * (f s θ * Work.Elliptic.sinCos2 θ) := by
    intro θ
    simp only [Work.Spaces.K, Work.Elliptic.sinCos2]
    ring
  rw [Work.FM.L12dens, Work.Elliptic.Fstar, MeasureTheory.integral_div]
  congr 1
  calc ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f s θ
      = ∫ θ in Work.Spaces.Iθ, 3 * (f s θ * Work.Elliptic.sinCos2 θ) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = 3 * ∫ θ in Work.Spaces.Iθ, f s θ * Work.Elliptic.sinCos2 θ :=
        MeasureTheory.integral_const_mul 3 _



end Work.FTS.CoercivityFix.Coer1T.HardyAlt
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.GbarSin.FstarDzIter_chain_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.GbarSin

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## A predicate holding on `(0,π/2)` holds almost everywhere on `Iθ` -/

/-- A predicate which holds on the open interval `(0, π/2)` holds almost everywhere on `Iθ`
(the two endpoints `0` and `π/2` form a null set). -/
theorem ae_imp_of_mem_Ioo {p : ℝ → Prop} (h : ∀ θ ∈ Set.Ioo 0 (π / 2), p θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume), θ ∈ Work.Spaces.Iθ → p θ := by
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({0, π / 2} : Set ℝ)) ?_ ?_
  · intro θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := by
      by_contra hc
      exact hθ (fun h' => absurd h' hc)
    have hpθ : ¬ p θ := fun hp => hθ (fun _ => hp)
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hcon
    have hcon1 : θ ≠ 0 := fun h => hcon (Or.inl h)
    have hcon2 : θ ≠ π / 2 := fun h => hcon (Or.inr h)
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθI
    exact hpθ (h θ ⟨lt_of_le_of_ne hθI.1 (Ne.symm hcon1), lt_of_le_of_ne hθI.2 hcon2⟩)
  · have hset : ({0, π / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {π / 2} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    rw [hset]
    exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
      (MeasureTheory.measure_singleton (π / 2))

/-! ## Integrability of the angular slices of the moment's integrands -/

/-- The angular slice of `D_z^i F` against the weight `sinθcos²θ` is integrable on `Iθ`.
(Specialisation of the Cauchy--Schwarz bound `integrableOn_zSummand` to the bounded angular
weight `sinθcos²θ` of the moment `F_*`.) -/
theorem integrableOn_DzIter_mul_sinCos2 (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    {i : ℕ} (hi : i ≤ k) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ : ℝ => Work.Spaces.DzIter i F z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hz
  have hsq := Work.FTS.EllipticEst.integrableOn_zSummand α k hF hmem i hi hzI
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hsum : IntegrableOn (fun θ : ℝ => (Work.Spaces.DzIter i F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1)
      Work.Spaces.Iθ := hsq.add hconst
  refine Integrable.mono' hsum ?_ ?_
  · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.DzIter i F p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      (((hF.DzIter i).continuousOn).mul (by unfold Work.Elliptic.sinCos2; fun_prop)) hz
  · rw [Work.Spaces.Iθ, ae_restrict_iff' measurableSet_Icc]
    refine Eventually.of_forall fun θ hθ => ?_
    have hb := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
      (f := fun θ => Work.Spaces.DzIter i F z θ) hz hθ
    simpa only [Real.norm_eq_abs] using hb

/-- The uncurried function `(r,θ) ↦ ∂_z(D_z^j F)(r,θ)·sinθcos²θ` is integrable on
`(s,z] × Iθ`: this is the Fubini hypothesis for the chain rule. -/
theorem integrable_uncurry_pz_mul_sinCos2 (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ)
    (hj : j + 1 ≤ k) {s z : ℝ} (hs : 0 < s) :
    MeasureTheory.Integrable
      (Function.uncurry (fun r θ : ℝ => Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
        * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc s z)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have h2 := Work.FTS.EllipticEst.integrable_prod_sq_restrict_open α k F hF hmem (j + 1) hj
    (a := s) (b := z) (le_of_lt hs)
  have hD : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (1 / s) * ((Work.Spaces.DzIter (j + 1) F p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1))
      ((MeasureTheory.volume.restrict (Set.Ioc s z)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (h2.add (MeasureTheory.integrable_const (1 : ℝ))).const_mul (1 / s)
  refine Integrable.mono' hD ?_ ?_
  · exact Work.FTS.EllipticEst.aesm_uncurry_restrict_open
      (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2
        * Work.Elliptic.sinCos2 p.2)
      ((((hF.DzIter j).pz).continuousOn).mul (by unfold Work.Elliptic.sinCos2; fun_prop))
      (le_of_lt hs)
  · have hprod : (MeasureTheory.volume.restrict (Set.Ioc s z)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
        = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
            (Set.Ioc s z ×ˢ Work.Spaces.Iθ) := MeasureTheory.Measure.prod_restrict _ _
    rw [hprod]
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ioc.prod measurableSet_Icc) fun p hp => ?_
    obtain ⟨hp1, hp2⟩ := hp
    have hr : 0 < p.1 := lt_of_lt_of_le hs (le_of_lt hp1.1)
    have hDz : Work.Spaces.DzIter (j + 1) F p.1 p.2
        = p.1 * Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2 := by
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    have hb := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
      (f := fun θ => Work.Spaces.DzIter (j + 1) F p.1 θ) hr hp2
    have hstep : |Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2
          * Work.Elliptic.sinCos2 p.2|
        = |Work.Spaces.DzIter (j + 1) F p.1 p.2 * Work.Elliptic.sinCos2 p.2| / p.1 := by
      rw [eq_div_iff hr.ne']
      calc |Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2 * Work.Elliptic.sinCos2 p.2| * p.1
          = |Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2 * Work.Elliptic.sinCos2 p.2|
              * |p.1| := by rw [abs_of_pos hr]
        _ = |(Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2
              * Work.Elliptic.sinCos2 p.2) * p.1| := (abs_mul _ _).symm
        _ = |Work.Spaces.DzIter (j + 1) F p.1 p.2 * Work.Elliptic.sinCos2 p.2| := by
            rw [hDz]; congr 1; ring
    have hle : |Work.Spaces.DzIter (j + 1) F p.1 p.2 * Work.Elliptic.sinCos2 p.2| / p.1
        ≤ |Work.Spaces.DzIter (j + 1) F p.1 p.2 * Work.Elliptic.sinCos2 p.2| / s :=
      div_le_div_of_nonneg_left (abs_nonneg _) hs (le_of_lt hp1.1)
    calc ‖Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2 * Work.Elliptic.sinCos2 p.2‖
        = |Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2 * Work.Elliptic.sinCos2 p.2| :=
          Real.norm_eq_abs _
      _ = |Work.Spaces.DzIter (j + 1) F p.1 p.2 * Work.Elliptic.sinCos2 p.2| / p.1 := hstep
      _ ≤ |Work.Spaces.DzIter (j + 1) F p.1 p.2 * Work.Elliptic.sinCos2 p.2| / s := hle
      _ ≤ (1 / s) * ((Work.Spaces.DzIter (j + 1) F p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1) := by
          rw [show |Work.Spaces.DzIter (j + 1) F p.1 p.2 * Work.Elliptic.sinCos2 p.2| / s
              = (1 / s) * |Work.Spaces.DzIter (j + 1) F p.1 p.2
                  * Work.Elliptic.sinCos2 p.2| by ring]
          exact mul_le_mul_of_nonneg_left hb (by positivity)

/-! ## The chain rule -/

/-- **The chain rule for the angular moment along `D_z`.**  For `F` smooth on the open
quadrant with `F ∈ ℋ^k` and `j + 1 ≤ k`, the moment `F_*(D_z^j F)` is an antiderivative of
`F_*(D_z^{j+1} F)/r`: `F_*(D_z^j F)(z) - F_*(D_z^j F)(s) = ∫_s^z F_*(D_z^{j+1} F)(r)/r dr`
for `0 < s ≤ z`. -/
theorem FstarDzIter_chain_open (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ)
    (hj : j + 1 ≤ k) {s z : ℝ} (hs : 0 < s) (hsz : s ≤ z) :
    Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z
        - Work.Elliptic.Fstar (Work.Spaces.DzIter j F) s
      = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) F) r / r := by
  rcases eq_or_lt_of_le hsz with hsz0 | hszlt
  · rw [← hsz0, sub_self, intervalIntegral.integral_same]
  have hzpos : 0 < z := lt_of_lt_of_le hs (le_of_lt hszlt)
  have hjle : j ≤ k := Nat.le_of_succ_le hj
  have hIz := integrableOn_DzIter_mul_sinCos2 α k F hF hmem hjle hzpos
  have hIs := integrableOn_DzIter_mul_sinCos2 α k F hF hmem hjle hs
  have hFub := integrable_uncurry_pz_mul_sinCos2 α k F hF hmem j hj (s := s) (z := z) hs
  -- Step 1: the difference of the two moments as a single angular integral
  have h1 : Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z
        - Work.Elliptic.Fstar (Work.Spaces.DzIter j F) s
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j F z θ
          - Work.Spaces.DzIter j F s θ) * Work.Elliptic.sinCos2 θ := by
    simp only [Work.Elliptic.Fstar]
    rw [show (fun θ : ℝ => (Work.Spaces.DzIter j F z θ - Work.Spaces.DzIter j F s θ)
          * Work.Elliptic.sinCos2 θ)
        = fun θ => Work.Spaces.DzIter j F z θ * Work.Elliptic.sinCos2 θ
            - Work.Spaces.DzIter j F s θ * Work.Elliptic.sinCos2 θ from by
      funext θ; ring]
    rw [MeasureTheory.integral_sub hIz hIs]
  -- Step 2: the radial FTC on the angular slice, for a.e. angle
  have h2 : ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j F z θ
        - Work.Spaces.DzIter j F s θ) * Work.Elliptic.sinCos2 θ
      = ∫ θ in Work.Spaces.Iθ, (∫ r in s..z, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ)
          * Work.Elliptic.sinCos2 θ := by
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
    refine ae_imp_of_mem_Ioo fun θ hθ => ?_
    rw [Work.FTS.EllipticEst.DzIter_slice_FTC_open hF j hs hsz hθ]
  -- Step 3: pull the angular weight out of the radial integral
  have h3 : ∫ θ in Work.Spaces.Iθ, (∫ r in s..z, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ)
        * Work.Elliptic.sinCos2 θ
      = ∫ θ in Work.Spaces.Iθ, ∫ r in s..z, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
          * Work.Elliptic.sinCos2 θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
    exact (intervalIntegral.integral_mul_const (Work.Elliptic.sinCos2 θ)
      (fun r => Work.Spaces.pz (Work.Spaces.DzIter j F) r θ)).symm
  -- Step 4: Fubini
  have h4 : ∫ θ in Work.Spaces.Iθ, ∫ r in s..z, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
          * Work.Elliptic.sinCos2 θ
      = ∫ r in s..z, ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
          * Work.Elliptic.sinCos2 θ := by
    refine (MeasureTheory.intervalIntegral_integral_swap (a := s) (b := z)
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun r θ => Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
        * Work.Elliptic.sinCos2 θ) ?_).symm
    rwa [Set.uIoc_of_le hsz]
  -- Step 5: identify `F_*(D_z^{j+1} F)(r)/r` with the angular integral, for `r ∈ [s,z]`
  have h5 : ∫ r in s..z, (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
          * Work.Elliptic.sinCos2 θ)
      = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) F) r / r := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    have hsr : s ≤ r := le_trans (le_of_eq (min_eq_left hsz).symm) hr.1
    have hr0 : 0 < r := lt_of_lt_of_le hs hsr
    have hval : Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) F) r
        = r * ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
            * Work.Elliptic.sinCos2 θ := by
      rw [Work.Elliptic.Fstar]
      rw [show (fun θ : ℝ => Work.Spaces.DzIter (j + 1) F r θ * Work.Elliptic.sinCos2 θ)
          = fun θ => r * (Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
              * Work.Elliptic.sinCos2 θ) from by
        funext θ; simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz]; ring]
      rw [MeasureTheory.integral_const_mul]
    rw [hval, mul_div_cancel_left₀ _ hr0.ne']
  calc Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z
        - Work.Elliptic.Fstar (Work.Spaces.DzIter j F) s
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j F z θ
          - Work.Spaces.DzIter j F s θ) * Work.Elliptic.sinCos2 θ := h1
    _ = ∫ θ in Work.Spaces.Iθ, (∫ r in s..z, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ)
          * Work.Elliptic.sinCos2 θ := h2
    _ = ∫ θ in Work.Spaces.Iθ, ∫ r in s..z, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
          * Work.Elliptic.sinCos2 θ := h3
    _ = ∫ r in s..z, ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz (Work.Spaces.DzIter j F) r θ
          * Work.Elliptic.sinCos2 θ := h4
    _ = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) F) r / r := h5

end Work.FTS.EllipticEst.GbarSin
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.thetaPoincare_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Rewriting the `k = 0` integrand -/

theorem HkIntegrand_zero_eq_Wf (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ = (f z θ * Wf z θ) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand, Wf]
  norm_num

theorem HkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : 0 ≤ Real.sin (2 * θ)) :
    Work.Spaces.HkIntegrand α 0 f z θ = (f z θ) ^ 2 * ((Work.Spaces.w z) ^ 2 * rho θ) := by
  rw [HkIntegrand_zero_eq_Wf, mul_pow, Wf_sq_eq h]







theorem HkIntegrand_zero_fst (α : ℝ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f 0 θ = 0 := by
  rw [HkIntegrand_zero_eq_Wf]
  have h : Wf 0 θ = 0 := by simp [Wf, Work.Spaces.w]
  rw [h, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]




end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.SliceIbpThetaHonest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.Step1G.AeClear.HonEtaFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The angular weight `σ = sin(2θ)^{-η}` on the slices

Two facts about `σ`, copied from `Honest/HonEnergy.lean` (which cannot be imported here: that
module imports `Step1G/EnergyG.lean`, so importing it from the `EnergyG` cone would create a
module cycle).  They are the only two declarations of that module used by the `Ae`-energy chain
(`AngAWeak/aeEnergyWAux.lean`), which is re-routed through the clean copies in this directory. -/

/-- `σ = sin(2θ)^{-η}` is `≥ 1` on the open angular interval. -/
theorem one_le_sEta_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  have hs : 0 < Real.sin (2 * θ) := by
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_ <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hη0 : (0 : ℝ) ≤ Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  have hl : Real.log (Real.sin (2 * θ)) ≤ 0 := Real.log_nonpos hs.le hs1
  have hmain : (0 : ℝ) ≤ Real.log (Real.sin (2 * θ)) * (-(Work.Spaces.eta)) := by
    have h := mul_nonpos_of_nonpos_of_nonneg hl hη0
    nlinarith [h]
  have h := Real.exp_le_exp.mpr hmain
  rw [Work.FTS.EllipticEst.sEta, Real.rpow_def_of_pos hs]
  simpa only [Real.exp_zero] using h

/-- Almost every point of `Iθ` (for the restricted measure) lies in the *open* interval: the two
endpoints are a null set. -/
theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc, ae_iff]
  refine measure_mono_null (t := ({0, Real.pi / 2} : Set ℝ)) ?_ ?_
  · intro θ hθ
    simp only [Set.mem_setOf_eq, not_imp] at hθ
    obtain ⟨hθI, hne⟩ := hθ
    rcases eq_or_lt_of_le (Set.mem_Icc.mp hθI).1 with h | h
    · exact Or.inl h.symm
    · rcases eq_or_lt_of_le (Set.mem_Icc.mp hθI).2 with h2 | h2
      · exact Or.inr h2
      · exact absurd ⟨h, h2⟩ hne
  · have : ({0, Real.pi / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {Real.pi / 2} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    rw [this]
    exact measure_union_null (measure_singleton 0) (measure_singleton (Real.pi / 2))

end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.sliceBarSq2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "σ" => Work.FTS.EllipticEst.AngSecond.sig

/-- `σ = sin(2θ)^{-η}` is continuous on the open angular interval `(0, π/2)`. -/
theorem continuousOn_sig_Ioo :
    ContinuousOn σ (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  refine (Real.continuous_sin.comp_continuousOn (continuousOn_id.const_mul 2)).rpow_const ?_
  intro θ hθ
  have h1 : (0 : ℝ) < 2 * θ := by linarith [hθ.1]
  have h2 : 2 * θ < Real.pi := by linarith [hθ.2]
  exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2))

/-- `ρ θ = sin θ · cos θ · σ θ` is nonnegative on the open angular interval. -/
theorem wrho_nonneg_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 ≤ Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have h1 : (0 : ℝ) < 2 * θ := by linarith [hθ.1]
  have h2 : 2 * θ < Real.pi := by linarith [hθ.2]
  have hs2 : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi h1 h2
  rw [Work.FTS.EllipticEst.TanTheta.wrho]
  exact mul_nonneg (mul_nonneg hs.le hc.le) (Real.rpow_nonneg hs2.le _)

/-- The integrals over `(0, π/2)` and over `Iθ` agree. -/
theorem integral_Ioo_eq_Iθ' (f : ℝ → ℝ) :
    (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), f θ) = ∫ θ in Work.Spaces.Iθ, f θ := by
  have h : (Set.Ioo (0 : ℝ) (Real.pi / 2)) =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)]
      (Set.Icc (0 : ℝ) (Real.pi / 2)) := MeasureTheory.Ioo_ae_eq_Icc
  rw [Work.Spaces.Iθ]
  rw [show (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), f θ)
      = ∫ θ, f θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
          (Set.Ioo (0 : ℝ) (Real.pi / 2))) from rfl]
  rw [MeasureTheory.Measure.restrict_congr_set h]

/-- `σ` is nonnegative on the open angular interval. -/
private theorem sig_nonneg_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 0 ≤ σ θ :=
  Work.FTS.EllipticEst.AngSecond.sig_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩

/-- **The slice integrand is locally integrable.**  If `u²σ` is integrable on `Iθ` then
`(u/cos)²σ` is integrable on every `(0, b)` with `b < π/2`: on `(0,b)` one has
`cos²θ ≥ cos²b > 0`, so the integrand is dominated by the constant multiple
`(1/cos²b)·u²σ`. -/
private theorem local_integrable_local (u : ℝ → ℝ)
    (h0 : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * σ θ) Work.Spaces.Iθ) :
    ∀ b ∈ Set.Ioo 0 (Real.pi / 2),
      MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 * σ θ) (Set.Ioo 0 b) := by
  intro b hb
  have hbpos : 0 < b := hb.1
  have hbpi : b < Real.pi / 2 := hb.2
  have hcosb : 0 < Real.cos b :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hbpos, Real.pi_pos], hbpi⟩
  have h0b : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * σ θ) (Set.Ioo 0 b) :=
    h0.mono_set (fun x hx => ⟨le_of_lt hx.1, le_of_lt (lt_trans hx.2 hbpi)⟩)
  refine (h0b.const_mul (1 / (Real.cos b) ^ 2)).mono' ?_ ?_
  · have h1 : AEStronglyMeasurable (fun θ : ℝ => (u θ) ^ 2 * σ θ)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioo 0 b)) :=
      h0b.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun θ : ℝ => (1 : ℝ) / (Real.cos θ) ^ 2)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioo 0 b)) :=
      (ContinuousOn.div continuousOn_const (Real.continuous_cos.continuousOn.pow 2)
        (fun θ hθ => pow_ne_zero 2 (ne_of_gt (Real.cos_pos_of_mem_Ioo
          ⟨by linarith [Real.pi_pos, hθ.1], by linarith [hθ.2, hbpi]⟩)))).aestronglyMeasurable
        measurableSet_Ioo
    have h3 := h1.mul h2
    convert h3 using 1
    ext θ
    simp only [Pi.mul_apply]
    ring
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hcθ : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, hθ.1], by linarith [hθ.2, hbpi]⟩
    have hσ : 0 ≤ σ θ := sig_nonneg_Ioo ⟨hθ.1, lt_trans hθ.2 hbpi⟩
    have hcb_le : Real.cos b ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi (x := θ) (y := b) hθ.1.le
        (by linarith [hbpi, Real.pi_pos]) hθ.2.le
    have hsq : Real.cos b ^ 2 ≤ Real.cos θ ^ 2 := by nlinarith [hcosb, hcθ, hcb_le]
    have hkey : (u θ / Real.cos θ) ^ 2 ≤ (1 / (Real.cos b) ^ 2) * (u θ) ^ 2 := by
      have hdiv : (1 : ℝ) / (Real.cos θ) ^ 2 ≤ 1 / (Real.cos b) ^ 2 :=
        one_div_le_one_div_of_le (pow_pos hcosb 2) hsq
      calc (u θ / Real.cos θ) ^ 2 = (u θ) ^ 2 * (1 / (Real.cos θ) ^ 2) := by
            rw [div_pow]; ring
        _ ≤ (u θ) ^ 2 * (1 / (Real.cos b) ^ 2) := mul_le_mul_of_nonneg_left hdiv (sq_nonneg _)
        _ = (1 / (Real.cos b) ^ 2) * (u θ) ^ 2 := by ring
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hσ)]
    calc (u θ / Real.cos θ) ^ 2 * σ θ
        ≤ ((1 / (Real.cos b) ^ 2) * (u θ) ^ 2) * σ θ := mul_le_mul_of_nonneg_right hkey hσ
      _ = (1 / (Real.cos b) ^ 2) * ((u θ) ^ 2 * σ θ) := by ring

/-- **Monotone limit of set integrals with a moving bound.**  If `F ≥ 0` is integrable on each
member `s n` of an increasing sequence of sets covering `(0, β)`, and `∫_{s n} F ≤ K n` where
`K n → K0`, then `F` is integrable on `(0, β)` and `∫_{(0,β)} F ≤ K0`. -/
private theorem lintegral_le_of_directed_local {F : ℝ → ℝ} {s : ℕ → Set ℝ} {β K0 : ℝ}
    (hβ : 0 < β) (hmeas : ∀ n, MeasurableSet (s n)) (hmono : Monotone s)
    (hsub : ∀ n, s n ⊆ Set.Ioo 0 β) (hcov : Set.Ioo 0 β ⊆ ⋃ n, s n)
    (hint : ∀ n, MeasureTheory.IntegrableOn F (s n))
    (haesm : MeasureTheory.AEStronglyMeasurable F
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioo 0 β)))
    (hnn : ∀ x ∈ Set.Ioo 0 β, 0 ≤ F x)
    {K : ℕ → ℝ} (hK : ∀ n, (∫ x in s n, F x) ≤ K n)
    (hKlim : Filter.Tendsto K Filter.atTop (nhds K0)) :
    MeasureTheory.IntegrableOn F (Set.Ioo 0 β) ∧
      (∫ x in Set.Ioo 0 β, F x) ≤ K0 := by
  have hunion : (⋃ n, s n) = Set.Ioo 0 β :=
    Set.Subset.antisymm (Set.iUnion_subset hsub) hcov
  have hdir : Directed (· ⊆ ·) s := fun m n =>
    ⟨max m n, hmono (le_max_left m n), hmono (le_max_right m n)⟩
  have hterm : ∀ n, (∫⁻ x in s n, ENNReal.ofReal (F x)) = ENNReal.ofReal (∫ x in s n, F x) := by
    intro n
    refine (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint n) ?_).symm
    filter_upwards [MeasureTheory.ae_restrict_mem (hmeas n)] with x hx
    exact hnn x (hsub n hx)
  have hKnn : 0 ≤ K0 := by
    refine ge_of_tendsto hKlim (Eventually.of_forall fun n => ?_)
    exact le_trans (setIntegral_nonneg (hmeas n) (fun x hx => hnn x (hsub n hx))) (hK n)
  have hbound : ∀ ε : NNReal, 0 < ε → (∫⁻ x in Set.Ioo 0 β, ENNReal.ofReal (F x))
      ≤ ENNReal.ofReal K0 + (ε : ENNReal) := by
    intro ε hε
    have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    have hev : ∀ᶠ n in Filter.atTop, K n < K0 + (ε : ℝ) :=
      hKlim.eventually (isOpen_Iio.mem_nhds (lt_add_of_pos_right K0 hεR))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    have hsup : (∫⁻ x in Set.Ioo 0 β, ENNReal.ofReal (F x))
        = ⨆ n, ∫⁻ x in s n, ENNReal.ofReal (F x) := by
      rw [← hunion]
      exact MeasureTheory.setLIntegral_iUnion_of_directed (fun x => ENNReal.ofReal (F x)) hdir
    rw [hsup]
    refine iSup_le fun n => ?_
    calc (∫⁻ x in s n, ENNReal.ofReal (F x))
        ≤ ∫⁻ x in s (max n N), ENNReal.ofReal (F x) :=
          MeasureTheory.lintegral_mono_set (hmono (le_max_left n N))
      _ = ENNReal.ofReal (∫ x in s (max n N), F x) := hterm (max n N)
      _ ≤ ENNReal.ofReal (K (max n N)) := ENNReal.ofReal_le_ofReal (hK (max n N))
      _ ≤ ENNReal.ofReal (K0 + (ε : ℝ)) :=
          ENNReal.ofReal_le_ofReal (le_of_lt (hN (max n N) (le_max_right n N)))
      _ = ENNReal.ofReal K0 + (ε : ENNReal) := by
          rw [ENNReal.ofReal_add hKnn (le_of_lt hεR), ENNReal.ofReal_coe_nnreal]
  exact Work.FTS.EllipticEst.remov.integrable_of_lintegral_ofReal_le' measurableSet_Ioo hKnn haesm
    hnn (ENNReal.le_of_forall_pos_le_add fun ε hε _ => hbound ε hε)

/-- The pointwise algebra behind `core_local`: with `u = v·cos θ`, `u' = w·cos θ − v·sin θ`,
`ρ = σ·sin θ·cos θ` and `cos²θ + sin²θ = 1`,

`100 (u² + u'²) σ − v² σ = 100 σ (w cos θ)² − 200 ρ v w + 99 v² σ`. -/
private theorem core_pt_identity (u D V W c s sg r : ℝ) (hV : u = V * c)
    (hD : D = W * c - V * s) (hr : r = sg * s * c) (hcs : c ^ 2 + s ^ 2 = 1) :
    100 * (u ^ 2 * sg) + 100 * (D ^ 2 * sg) - V ^ 2 * sg
      = 100 * (W ^ 2 * c ^ 2 * sg) - 200 * (r * V * W) + 99 * (V ^ 2 * sg) := by
  rw [hV, hD, hr]
  linear_combination (100 * sg * V ^ 2) * hcs


/-- **The core identity of `sliceBarSq2`, on a compact sub-interval `(a,b) ⊂ (0, π/2)`.**

With `σ = sin(2θ)^{-η}` and `ρ θ = sin θ · cos θ · σ θ`, for `u` of class `C²` on the open
quadrant,

```
∫_{(a,b)} [100 (u² + u'²) σ − (u/cos)² σ]
  = 100 ∫_{(a,b)} σ (∂_θ(u/cos))² cos²θ
    + ∫_{(a,b)} (u/cos)² σ (99 + cos 2θ)
    − 100 [ρ · (u/cos)²]  at `a` and `b` .
```

Route: with `v = u/cos` the pointwise identity
`100(u²+u'²)σ − v²σ = 100 σ (v'cos θ)² − 200 ρ v v' + 99 v²σ`, then the integration by parts
`∫ ρ v v' = (1/2)[ρ v²] − (1/2)∫ ρ' v²` (the FTC applied to `(1/2)ρv²` on `[a,b]`), and
`ρ' = (1−η) cos 2θ · σ` with `100 (1 − η) = 1` because `η = 99/100`. -/
private theorem core_local (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < Real.pi / 2) :
    (∫ θ in Set.Ioo a b, (100 * ((u θ) ^ 2 * σ θ) + 100 * ((deriv u θ) ^ 2 * σ θ)
        - (u θ / Real.cos θ) ^ 2 * σ θ))
      = 100 * (∫ θ in Set.Ioo a b, (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
              * (Real.cos θ) ^ 2 * σ θ)
        + (∫ θ in Set.Ioo a b, (u θ / Real.cos θ) ^ 2 * σ θ * (99 + Real.cos (2 * θ)))
        - 100 * (Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta b
              * (u b / Real.cos b) ^ 2
            - Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta a
              * (u a / Real.cos a) ^ 2) := by
  have hsub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hIoo_sub : Set.Ioo a b ⊆ Set.Icc a b := fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hcospos : ∀ θ ∈ Set.Icc a b, 0 < Real.cos θ := fun θ hθ =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, (hsub hθ).1], (hsub hθ).2⟩
  -- ## notation
  set ρ : ℝ → ℝ := Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta with hρ
  set ρ' : ℝ → ℝ := Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta with hρ'
  have hρeq : ∀ θ : ℝ, ρ θ = σ θ * Real.sin θ * Real.cos θ := by
    intro θ
    rw [hρ]
    dsimp only [Work.FTS.EllipticEst.TanTheta.wrho, Work.FTS.EllipticEst.AngSecond.sig]
    ring
  have hρDeq : ∀ θ : ℝ, ρ' θ = (1 - Work.Spaces.eta) * Real.cos (2 * θ) * σ θ := by
    intro θ
    rw [hρ']
    dsimp only [Work.FTS.EllipticEst.TanTheta.wrhoD, Work.FTS.EllipticEst.AngSecond.sig]
  have heta100 : (1 : ℝ) - Work.Spaces.eta = 1 / 100 := by
    rw [Work.Spaces.eta]; norm_num
  -- ## continuity on the compact interval
  have hσcont : ContinuousOn σ (Set.Icc a b) := continuousOn_sig_Ioo.mono hsub
  have hρcont : ContinuousOn ρ (Set.Icc a b) := by
    have hc : ContinuousOn (fun θ : ℝ => σ θ * Real.sin θ * Real.cos θ) (Set.Icc a b) :=
      ((hσcont.mul Real.continuous_sin.continuousOn).mul Real.continuous_cos.continuousOn)
    exact hc.congr (fun x _ => hρeq x)
  have hρ'cont : ContinuousOn ρ' (Set.Icc a b) := by
    have hc : ContinuousOn (fun θ : ℝ => (1 - Work.Spaces.eta) * Real.cos (2 * θ) * σ θ)
        (Set.Icc a b) :=
      ((continuousOn_const.mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).mul hσcont)
    exact hc.congr (fun x _ => hρDeq x)
  have hVcont : ContinuousOn (fun t : ℝ => u t / Real.cos t) (Set.Icc a b) :=
    (hu.continuousOn.mono hsub).div Real.continuous_cos.continuousOn
      (fun θ hθ => ne_of_gt (hcospos θ hθ))
  have hVcd : ContDiffOn ℝ 2 (fun t : ℝ => u t / Real.cos t) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.div (Real.contDiff_cos.contDiffOn.of_le le_top)
      (fun θ hθ => ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩))
  have hV'cont : ContinuousOn (deriv (fun t : ℝ => u t / Real.cos t)) (Set.Icc a b) :=
    (hVcd.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsub
  -- ## differentiability on the compact interval
  have hVD : ∀ θ ∈ Set.Icc a b,
      HasDerivAt (fun t : ℝ => u t / Real.cos t) (deriv (fun t : ℝ => u t / Real.cos t) θ) θ := by
    intro θ hθ
    exact ((hVcd.contDiffAt (isOpen_Ioo.mem_nhds (hsub hθ))).differentiableAt (by norm_num)).hasDerivAt
  have hrel : ∀ θ ∈ Set.Icc a b, deriv u θ
      = deriv (fun t : ℝ => u t / Real.cos t) θ * Real.cos θ
        - (u θ / Real.cos θ) * Real.sin θ := by
    intro θ hθ
    have hmul : HasDerivAt (fun y : ℝ => (u y / Real.cos y) * Real.cos y)
        (deriv (fun t : ℝ => u t / Real.cos t) θ * Real.cos θ
          - (u θ / Real.cos θ) * Real.sin θ) θ := by
      have h := (hVD θ hθ).mul (Real.hasDerivAt_cos θ)
      convert h using 1
      ring
    have hev : u =ᶠ[𝓝 θ] fun y : ℝ => (u y / Real.cos y) * Real.cos y := by
      filter_upwards [isOpen_Ioo.mem_nhds (hsub hθ)] with y hy
      exact (div_mul_cancel₀ (u y) (ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos, hy.1], hy.2⟩))).symm
    exact (hmul.congr_of_eventuallyEq hev).deriv
  -- ## the pointwise identity
  have hpt : ∀ θ ∈ Set.Icc a b,
      100 * ((u θ) ^ 2 * σ θ) + 100 * ((deriv u θ) ^ 2 * σ θ) - (u θ / Real.cos θ) ^ 2 * σ θ
        = 100 * ((deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2 * (Real.cos θ) ^ 2 * σ θ)
          - 200 * (ρ θ * (u θ / Real.cos θ) * deriv (fun t : ℝ => u t / Real.cos t) θ)
          + 99 * ((u θ / Real.cos θ) ^ 2 * σ θ) := by
    intro θ hθ
    have hc : Real.cos θ ≠ 0 := ne_of_gt (hcospos θ hθ)
    have hu_eq : u θ = (u θ / Real.cos θ) * Real.cos θ := (div_mul_cancel₀ _ hc).symm
    have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    exact core_pt_identity (u θ) (deriv u θ) (u θ / Real.cos θ)
      (deriv (fun t : ℝ => u t / Real.cos t) θ) (Real.cos θ) (Real.sin θ) (σ θ) (ρ θ)
      hu_eq (hrel θ hθ) (hρeq θ) hcs
  -- ## the antiderivative `(1/2) ρ v²`
  have hPD : ∀ x ∈ Set.Icc a b, HasDerivAt (fun y : ℝ => (1 / 2) * (ρ y * (u y / Real.cos y) ^ 2))
      (ρ x * (u x / Real.cos x) * deriv (fun t : ℝ => u t / Real.cos t) x
        + (1 / 2) * (ρ' x * (u x / Real.cos x) ^ 2)) x := by
    intro x hx
    have h1 : HasDerivAt ρ (ρ' x) x := by
      rw [hρ, hρ']
      exact Work.FTS.EllipticEst.TanTheta.wrho_deriv Work.Spaces.eta (hsub hx)
    have h2 : HasDerivAt (fun y : ℝ => (u y / Real.cos y) ^ 2)
        (2 * (u x / Real.cos x) ^ (2 - 1) * deriv (fun t : ℝ => u t / Real.cos t) x) x :=
      (hVD x hx).pow 2
    have h3 := (h1.mul h2).const_mul (1 / 2)
    convert h3 using 1
    ring
  have hdcont : ContinuousOn (fun x : ℝ => ρ x * (u x / Real.cos x)
      * deriv (fun t : ℝ => u t / Real.cos t) x
      + (1 / 2) * (ρ' x * (u x / Real.cos x) ^ 2)) (Set.Icc a b) :=
    ((hρcont.mul hVcont).mul hV'cont).add
      (continuousOn_const.mul (hρ'cont.mul (hVcont.pow 2)))
  have hFTCint : (∫ θ in a..b, (ρ θ * (u θ / Real.cos θ)
        * deriv (fun t : ℝ => u t / Real.cos t) θ
      + (1 / 2) * (ρ' θ * (u θ / Real.cos θ) ^ 2)))
      = (1 / 2) * (ρ b * (u b / Real.cos b) ^ 2)
        - (1 / 2) * (ρ a * (u a / Real.cos a) ^ 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hPD x (by rw [Set.uIcc_of_le hab.le] at hx; exact hx))
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr hdcont.integrableOn_Icc)
  have hFTC : (∫ θ in Set.Ioo a b, (ρ θ * (u θ / Real.cos θ)
        * deriv (fun t : ℝ => u t / Real.cos t) θ
      + (1 / 2) * (ρ' θ * (u θ / Real.cos θ) ^ 2)))
      = (1 / 2) * (ρ b * (u b / Real.cos b) ^ 2)
        - (1 / 2) * (ρ a * (u a / Real.cos a) ^ 2) := by
    have h := hFTCint
    rw [intervalIntegral.integral_of_le hab.le, MeasureTheory.integral_Ioc_eq_integral_Ioo] at h
    exact h
  -- ## splitting the FTC identity
  have hint1 : MeasureTheory.IntegrableOn (fun θ : ℝ => ρ θ * (u θ / Real.cos θ)
      * deriv (fun t : ℝ => u t / Real.cos t) θ) (Set.Ioo a b) :=
    (((hρcont.mul hVcont).mul hV'cont).integrableOn_Icc).mono_set hIoo_sub
  have hint2 : MeasureTheory.IntegrableOn (fun θ : ℝ => ρ' θ * (u θ / Real.cos θ) ^ 2)
      (Set.Ioo a b) :=
    ((hρ'cont.mul (hVcont.pow 2)).integrableOn_Icc).mono_set hIoo_sub
  have hsplit : (∫ θ in Set.Ioo a b, ρ θ * (u θ / Real.cos θ)
        * deriv (fun t : ℝ => u t / Real.cos t) θ)
      = (1 / 2) * (ρ b * (u b / Real.cos b) ^ 2) - (1 / 2) * (ρ a * (u a / Real.cos a) ^ 2)
        - (1 / 2) * (∫ θ in Set.Ioo a b, ρ' θ * (u θ / Real.cos θ) ^ 2) := by
    have hsum : (∫ θ in Set.Ioo a b, (ρ θ * (u θ / Real.cos θ)
          * deriv (fun t : ℝ => u t / Real.cos t) θ
        + (1 / 2) * (ρ' θ * (u θ / Real.cos θ) ^ 2)))
        = (∫ θ in Set.Ioo a b, ρ θ * (u θ / Real.cos θ)
            * deriv (fun t : ℝ => u t / Real.cos t) θ)
          + (1 / 2) * (∫ θ in Set.Ioo a b, ρ' θ * (u θ / Real.cos θ) ^ 2) := by
      rw [MeasureTheory.integral_add hint1 (hint2.const_mul (1 / 2)),
        MeasureTheory.integral_const_mul]
    linarith [hFTC, hsum]
  -- ## replacing `ρ'` by `(1/100) cos 2θ σ`
  have hcos2int : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      Real.cos (2 * θ) * σ θ * (u θ / Real.cos θ) ^ 2) (Set.Ioo a b) :=
    ((((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn.mul hσcont).mul
      (hVcont.pow 2)).integrableOn_Icc).mono_set hIoo_sub
  have hcon2 : (∫ θ in Set.Ioo a b, ρ' θ * (u θ / Real.cos θ) ^ 2)
      = (1 / 100) * (∫ θ in Set.Ioo a b,
          Real.cos (2 * θ) * σ θ * (u θ / Real.cos θ) ^ 2) := by
    rw [show (∫ θ in Set.Ioo a b, ρ' θ * (u θ / Real.cos θ) ^ 2)
        = ∫ θ in Set.Ioo a b,
            (1 / 100) * (Real.cos (2 * θ) * σ θ * (u θ / Real.cos θ) ^ 2) from by
      refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      rw [hρDeq θ, heta100]
      ring]
    rw [MeasureTheory.integral_const_mul]
  -- ## integrability on the pieces
  have hUUint : MeasureTheory.IntegrableOn (fun θ : ℝ => (u θ) ^ 2 * σ θ) (Set.Ioo a b) :=
    ((((hu.continuousOn.mono hsub).pow 2).mul hσcont).integrableOn_Icc).mono_set hIoo_sub
  have hVVint : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv u θ) ^ 2 * σ θ) (Set.Ioo a b) :=
    (((((hu.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsub).pow 2).mul
      hσcont).integrableOn_Icc).mono_set hIoo_sub
  have hWWint : MeasureTheory.IntegrableOn (fun θ : ℝ => (u θ / Real.cos θ) ^ 2 * σ θ)
      (Set.Ioo a b) :=
    (((hVcont.pow 2).mul hσcont).integrableOn_Icc).mono_set hIoo_sub
  have hW1int : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2 * (Real.cos θ) ^ 2 * σ θ) (Set.Ioo a b) :=
    ((((hV'cont.pow 2).mul (Real.continuous_cos.continuousOn.pow 2)).mul hσcont).integrableOn_Icc).mono_set
      hIoo_sub
  have hW2int : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (u θ / Real.cos θ) ^ 2 * σ θ * (99 + Real.cos (2 * θ))) (Set.Ioo a b) :=
    ((((hVcont.pow 2).mul hσcont).mul (continuousOn_const.add
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn)).integrableOn_Icc).mono_set
      hIoo_sub
  -- ## the left-hand side, split
  have hL1 : (∫ θ in Set.Ioo a b, (100 * ((u θ) ^ 2 * σ θ) + 100 * ((deriv u θ) ^ 2 * σ θ)
        - (u θ / Real.cos θ) ^ 2 * σ θ))
      = 100 * (∫ θ in Set.Ioo a b, (u θ) ^ 2 * σ θ)
        + 100 * (∫ θ in Set.Ioo a b, (deriv u θ) ^ 2 * σ θ)
        - (∫ θ in Set.Ioo a b, (u θ / Real.cos θ) ^ 2 * σ θ) := by
    rw [MeasureTheory.integral_sub
      (f := fun θ : ℝ => 100 * ((u θ) ^ 2 * σ θ) + 100 * ((deriv u θ) ^ 2 * σ θ))
      (g := fun θ : ℝ => (u θ / Real.cos θ) ^ 2 * σ θ)
      ((hUUint.const_mul 100).add (hVVint.const_mul 100)) hWWint]
    rw [MeasureTheory.integral_add
      (f := fun θ : ℝ => 100 * ((u θ) ^ 2 * σ θ))
      (g := fun θ : ℝ => 100 * ((deriv u θ) ^ 2 * σ θ))
      (hUUint.const_mul 100) (hVVint.const_mul 100)]
    rw [MeasureTheory.integral_const_mul (100 : ℝ), MeasureTheory.integral_const_mul (100 : ℝ)]
  -- ## the left-hand side, pointwise rewritten
  have hL2 : (∫ θ in Set.Ioo a b, (100 * ((u θ) ^ 2 * σ θ) + 100 * ((deriv u θ) ^ 2 * σ θ)
        - (u θ / Real.cos θ) ^ 2 * σ θ))
      = 100 * (∫ θ in Set.Ioo a b, (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
            * (Real.cos θ) ^ 2 * σ θ)
        - 200 * (∫ θ in Set.Ioo a b, ρ θ * (u θ / Real.cos θ)
            * deriv (fun t : ℝ => u t / Real.cos t) θ)
        + 99 * (∫ θ in Set.Ioo a b, (u θ / Real.cos θ) ^ 2 * σ θ) := by
    rw [setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => hpt θ (hIoo_sub hθ))]
    rw [MeasureTheory.integral_add
      (f := fun θ : ℝ => 100 * ((deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
            * (Real.cos θ) ^ 2 * σ θ)
          - 200 * (ρ θ * (u θ / Real.cos θ) * deriv (fun t : ℝ => u t / Real.cos t) θ))
      (g := fun θ : ℝ => 99 * ((u θ / Real.cos θ) ^ 2 * σ θ))
      ((hW1int.const_mul 100).sub (hint1.const_mul 200)) (hWWint.const_mul 99)]
    rw [MeasureTheory.integral_sub
      (f := fun θ : ℝ => 100 * ((deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
            * (Real.cos θ) ^ 2 * σ θ))
      (g := fun θ : ℝ => 200 * (ρ θ * (u θ / Real.cos θ)
            * deriv (fun t : ℝ => u t / Real.cos t) θ))
      (hW1int.const_mul 100) (hint1.const_mul 200)]
    rw [MeasureTheory.integral_const_mul (100 : ℝ), MeasureTheory.integral_const_mul (200 : ℝ),
      MeasureTheory.integral_const_mul (99 : ℝ)]
  -- ## the last piece
  have hW2 : (∫ θ in Set.Ioo a b, (u θ / Real.cos θ) ^ 2 * σ θ * (99 + Real.cos (2 * θ)))
      = 99 * (∫ θ in Set.Ioo a b, (u θ / Real.cos θ) ^ 2 * σ θ)
        + (∫ θ in Set.Ioo a b, Real.cos (2 * θ) * σ θ * (u θ / Real.cos θ) ^ 2) := by
    rw [show (∫ θ in Set.Ioo a b, (u θ / Real.cos θ) ^ 2 * σ θ * (99 + Real.cos (2 * θ)))
        = ∫ θ in Set.Ioo a b, (99 * ((u θ / Real.cos θ) ^ 2 * σ θ)
            + Real.cos (2 * θ) * σ θ * (u θ / Real.cos θ) ^ 2) from by
      refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      ring]
    rw [MeasureTheory.integral_add (hWWint.const_mul 99) hcos2int,
      MeasureTheory.integral_const_mul (99 : ℝ)]
  -- ## assembly
  linarith [hL1, hL2, hsplit, hcon2, hW2]

theorem sliceBarSq2 (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hlim : ∃ c : ℝ, Filter.Tendsto (fun θ => u θ / Real.cos θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c))
    (h0 : MeasureTheory.IntegrableOn
      (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ)
    (h1 : MeasureTheory.IntegrableOn
      (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ => (u θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ,
        (u θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      ≤ 100 * ((∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2
              * Work.FTS.EllipticEst.AngSecond.sig θ)) := by
  have hπ2 : (0 : ℝ) < Real.pi / 2 := Real.pi_div_two_pos
  obtain ⟨c, hc⟩ := hlim
  -- ## abbreviations
  let H : ℝ → ℝ := fun x => (u x) ^ 2 * σ x + (deriv u x) ^ 2 * σ x
  let F : ℝ → ℝ := fun x => (u x / Real.cos x) ^ 2 * σ x
  let q : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ (n + 2)
  let a_ : ℕ → ℝ := fun n => (Real.pi / 2) * q n
  let b_ : ℕ → ℝ := fun n => (Real.pi / 2) * (1 - q n)
  let s : ℕ → Set ℝ := fun n => Set.Ioo (a_ n) (b_ n)
  -- ## elementary facts about the weight
  have hσnn_Iθ : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ :=
    fun θ hθ => Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ
  have hσnn_Ioo : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ σ θ := fun θ hθ =>
    hσnn_Iθ θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hcospos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.cos θ := fun θ hθ =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  -- ## elementary facts about the two sequences
  have hq_pos : ∀ n, 0 < q n := by
    intro n
    simp only [q]
    positivity
  have hq_le : ∀ n, q n ≤ 1 / 4 := by
    intro n
    have h2 : (2 : ℕ) ≤ n + 2 := by omega
    calc q n ≤ (1 / 2 : ℝ) ^ 2 := by
          simp only [q]
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h2
      _ = 1 / 4 := by norm_num
  have hq_lt_one : ∀ n, q n < 1 := fun n => lt_of_le_of_lt (hq_le n) (by norm_num)
  have hq_anti : Antitone q := by
    intro m n hmn
    simp only [q]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hq_tend : Filter.Tendsto q Filter.atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    have h2 : Filter.Tendsto (fun n => (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ 2) Filter.atTop
        (nhds ((0 : ℝ) * (1 / 2 : ℝ) ^ 2)) := h.mul_const _
    rw [zero_mul] at h2
    refine h2.congr' ?_
    filter_upwards with n
    simp only [q]
    rw [pow_add]
  have ha_pos : ∀ n, 0 < a_ n := fun n => by
    simp only [a_]
    exact mul_pos hπ2 (hq_pos n)
  have ha_lt_b : ∀ n, a_ n < b_ n := fun n => by
    have h : q n < 1 - q n := by have := hq_le n; linarith
    have h2 := mul_lt_mul_of_pos_left h hπ2
    simpa only [a_, b_] using h2
  have hb_lt : ∀ n, b_ n < Real.pi / 2 := fun n => by
    have h : 1 - q n < 1 := by have := hq_pos n; linarith
    have h2 := mul_lt_mul_of_pos_left h hπ2
    simpa only [b_, mul_one] using h2
  have hb_pos : ∀ n, 0 < b_ n := fun n => by
    have h : 0 < 1 - q n := by have := hq_lt_one n; linarith
    simp only [b_]
    exact mul_pos hπ2 h
  have ha_lt_pi2 : ∀ n, a_ n < Real.pi / 2 := fun n => by
    have h : q n < 1 := hq_lt_one n
    have h2 := mul_lt_mul_of_pos_left h hπ2
    simpa only [a_, mul_one] using h2
  have hsub : ∀ n, s n ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro n x hx
    simp only [s] at hx
    exact ⟨lt_trans (ha_pos n) hx.1, lt_of_lt_of_le hx.2 (le_of_lt (hb_lt n))⟩
  have hs_meas : ∀ n, MeasurableSet (s n) := fun n => by
    simp only [s]
    exact measurableSet_Ioo
  have hs_mono : Monotone s := by
    intro m n hmn
    refine Set.Ioo_subset_Ioo ?_ ?_
    · simp only [a_]
      exact mul_le_mul_of_nonneg_left (hq_anti hmn) hπ2.le
    · have h : q n ≤ q m := hq_anti hmn
      simp only [b_]
      exact mul_le_mul_of_nonneg_left (by linarith) hπ2.le
  have ha_tend : Filter.Tendsto a_ Filter.atTop (nhds 0) := by
    simpa only [a_, mul_zero] using hq_tend.const_mul (Real.pi / 2)
  have hb_tend : Filter.Tendsto b_ Filter.atTop (nhds (Real.pi / 2)) := by
    have h : Filter.Tendsto (fun n => (Real.pi / 2) * (1 - q n)) Filter.atTop
        (nhds ((Real.pi / 2) * (1 - 0))) :=
      (tendsto_const_nhds.sub hq_tend).const_mul (Real.pi / 2)
    simpa only [b_, sub_zero, mul_one] using h
  have hs_cov : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ ⋃ n, s n := by
    intro x hx
    have h1 : ∀ᶠ n in Filter.atTop, a_ n < x := ha_tend.eventually (Iio_mem_nhds hx.1)
    have h2 : ∀ᶠ n in Filter.atTop, x < b_ n := hb_tend.eventually (Ioi_mem_nhds hx.2)
    obtain ⟨n, hn⟩ := (h1.and h2).exists
    exact Set.mem_iUnion.mpr ⟨n, hn.1, hn.2⟩
  have hs_union : (⋃ n, s n) = Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    Set.Subset.antisymm (Set.iUnion_subset hsub) hs_cov
  -- ## integrability on the pieces
  have hs_sub_Iθ : ∀ n, s n ⊆ Work.Spaces.Iθ := by
    intro n x hx
    simp only [s] at hx
    exact ⟨le_of_lt (lt_trans (ha_pos n) hx.1),
      le_of_lt (lt_of_lt_of_le hx.2 (le_of_lt (hb_lt n)))⟩
  have h_UX : ∀ n, MeasureTheory.IntegrableOn (fun x => (u x) ^ 2 * σ x) (s n) :=
    fun n => h0.mono_set (hs_sub_Iθ n)
  have h_VX : ∀ n, MeasureTheory.IntegrableOn (fun x => (deriv u x) ^ 2 * σ x) (s n) :=
    fun n => h1.mono_set (hs_sub_Iθ n)
  have hloc := local_integrable_local u h0
  have h_FX : ∀ n, MeasureTheory.IntegrableOn F (s n) := by
    intro n
    have hmem : s n ⊆ Set.Ioo (0 : ℝ) (b_ n) := by
      intro x hx
      simp only [s] at hx
      exact ⟨lt_trans (ha_pos n) hx.1, hx.2⟩
    have h := (hloc (b_ n) ⟨hb_pos n, hb_lt n⟩).mono_set hmem
    simpa only [F] using h
  have h_FX' : ∀ n, MeasureTheory.IntegrableOn (fun x => (u x / Real.cos x) ^ 2 * σ x) (s n) :=
    fun n => by simpa only [F] using h_FX n
  -- ## the core inequality, piecewise
  have hcore : ∀ n, (∫ x in s n, F x)
      ≤ 100 * (∫ x in s n, H x)
        + 100 * (Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta (b_ n)
            * (u (b_ n) / Real.cos (b_ n)) ^ 2) := by
    intro n
    have hU := h_UX n
    have hV := h_VX n
    have hF := h_FX n
    have hF' := h_FX' n
    -- the core identity, as an identity of set integrals over `s n`
    have hid : (∫ x in s n, (100 * ((u x) ^ 2 * σ x) + 100 * ((deriv u x) ^ 2 * σ x)
          - (u x / Real.cos x) ^ 2 * σ x))
        = 100 * (∫ x in s n, (deriv (fun t : ℝ => u t / Real.cos t) x) ^ 2
              * (Real.cos x) ^ 2 * σ x)
          + (∫ x in s n, (u x / Real.cos x) ^ 2 * σ x * (99 + Real.cos (2 * x)))
          - 100 * (Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta (b_ n)
                * (u (b_ n) / Real.cos (b_ n)) ^ 2
              - Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta (a_ n)
                * (u (a_ n) / Real.cos (a_ n)) ^ 2) := by
      simp only [s]
      exact core_local u hu (ha_pos n) (ha_lt_b n) (hb_lt n)
    -- splitting the left-hand side
    have e1 : (∫ x in s n, (100 * ((u x) ^ 2 * σ x) + 100 * ((deriv u x) ^ 2 * σ x)
          - (u x / Real.cos x) ^ 2 * σ x))
        = (∫ x in s n, (100 * ((u x) ^ 2 * σ x) + 100 * ((deriv u x) ^ 2 * σ x)))
          - ∫ x in s n, (u x / Real.cos x) ^ 2 * σ x :=
      MeasureTheory.integral_sub
        (f := fun x => 100 * ((u x) ^ 2 * σ x) + 100 * ((deriv u x) ^ 2 * σ x))
        (g := fun x => (u x / Real.cos x) ^ 2 * σ x)
        ((hU.const_mul 100).add (hV.const_mul 100)) hF'
    have e2 : (∫ x in s n, (100 * ((u x) ^ 2 * σ x) + 100 * ((deriv u x) ^ 2 * σ x)))
        = 100 * (∫ x in s n, (u x) ^ 2 * σ x)
          + 100 * (∫ x in s n, (deriv u x) ^ 2 * σ x) := by
      rw [MeasureTheory.integral_add
        (f := fun x => 100 * ((u x) ^ 2 * σ x)) (g := fun x => 100 * ((deriv u x) ^ 2 * σ x))
        (hU.const_mul 100) (hV.const_mul 100)]
      rw [MeasureTheory.integral_const_mul (100 : ℝ), MeasureTheory.integral_const_mul (100 : ℝ)]
    have hL : (∫ x in s n, (100 * ((u x) ^ 2 * σ x) + 100 * ((deriv u x) ^ 2 * σ x)
          - (u x / Real.cos x) ^ 2 * σ x))
        = 100 * (∫ x in s n, (u x) ^ 2 * σ x)
          + 100 * (∫ x in s n, (deriv u x) ^ 2 * σ x)
          - ∫ x in s n, (u x / Real.cos x) ^ 2 * σ x := by
      rw [e1, e2]
    have hH : (∫ x in s n, H x)
        = (∫ x in s n, (u x) ^ 2 * σ x) + (∫ x in s n, (deriv u x) ^ 2 * σ x) := by
      rw [show (∫ x in s n, H x)
          = ∫ x in s n, ((u x) ^ 2 * σ x + (deriv u x) ^ 2 * σ x) from by simp only [H]]
      exact MeasureTheory.integral_add (f := fun x => (u x) ^ 2 * σ x)
        (g := fun x => (deriv u x) ^ 2 * σ x) hU hV
    -- nonnegativity of the discarded terms
    have hI1nn : 0 ≤ ∫ x in s n, (deriv (fun t : ℝ => u t / Real.cos t) x) ^ 2
        * (Real.cos x) ^ 2 * σ x := by
      refine setIntegral_nonneg (hs_meas n) (fun x hx => ?_)
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hσnn_Ioo x (hsub n hx))
    have hI2nn : 0 ≤ ∫ x in s n, (u x / Real.cos x) ^ 2 * σ x * (99 + Real.cos (2 * x)) := by
      refine setIntegral_nonneg (hs_meas n) (fun x hx => ?_)
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (hσnn_Ioo x (hsub n hx)))
        (by linarith [Real.neg_one_le_cos (2 * x)])
    have hAnn : 0 ≤ Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta (a_ n)
        * (u (a_ n) / Real.cos (a_ n)) ^ 2 :=
      mul_nonneg (wrho_nonneg_Ioo ⟨ha_pos n, ha_lt_pi2 n⟩) (sq_nonneg _)
    rw [hL] at hid
    rw [hH]
    simp only [F] at hid ⊢
    linarith [hid, hI1nn, hI2nn, hAnn]
  -- ## the monotone-limit step
  have hint : ∀ n, MeasureTheory.IntegrableOn F (s n) := h_FX
  have hnn : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ F x := by
    intro x hx
    simp only [F]
    exact mul_nonneg (sq_nonneg _) (hσnn_Ioo x hx)
  have hFcont : ContinuousOn F (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h1c : ContinuousOn (fun x : ℝ => u x / Real.cos x)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hu.continuousOn.div Real.continuous_cos.continuousOn
        (fun θ hθ => ne_of_gt (hcospos θ hθ))
    simp only [F]
    exact (h1c.pow 2).mul continuousOn_sig_Ioo
  have haesm : AEStronglyMeasurable F
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
        (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hFcont.aestronglyMeasurable measurableSet_Ioo
  have hHint_Ioo : MeasureTheory.IntegrableOn H (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h : MeasureTheory.IntegrableOn
        (fun x : ℝ => (u x) ^ 2 * σ x + (deriv u x) ^ 2 * σ x)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (h0.mono_set (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)).add
        (h1.mono_set (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
    simpa only [H] using h
  have hHlim : Filter.Tendsto (fun n => ∫ x in s n, H x) Filter.atTop
      (nhds (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), H x)) := by
    have hHInt : MeasureTheory.IntegrableOn H (⋃ n, s n) := by
      rw [hs_union]
      exact hHint_Ioo
    simpa only [hs_union] using
      MeasureTheory.tendsto_setIntegral_of_monotone hs_meas hs_mono hHInt
  have hb_within : Filter.Tendsto b_ Filter.atTop
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within b_ hb_tend
      (Eventually.of_forall fun n => hb_lt n)
  have hbdlim : Filter.Tendsto (fun n => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta (b_ n)
      * (u (b_ n) / Real.cos (b_ n)) ^ 2) Filter.atTop (nhds 0) :=
    (sliceBarSq2_boundary_tendsto u ⟨c, hc⟩).comp hb_within
  have hKlim : Filter.Tendsto (fun n => 100 * (∫ x in s n, H x)
      + 100 * (Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta (b_ n)
        * (u (b_ n) / Real.cos (b_ n)) ^ 2)) Filter.atTop
      (nhds (100 * (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), H x))) := by
    have h := (hHlim.const_mul 100).add (hbdlim.const_mul 100)
    simpa using h
  obtain ⟨hFint, hFle⟩ := lintegral_le_of_directed_local (F := F) (s := s)
    (K := fun n => 100 * (∫ x in s n, H x)
      + 100 * (Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta (b_ n)
        * (u (b_ n) / Real.cos (b_ n)) ^ 2))
    hπ2 hs_meas hs_mono hsub hs_cov hint haesm hnn hcore hKlim
  -- ## conclusion
  refine ⟨?_, ?_⟩
  · rw [Work.Spaces.Iθ]
    exact hFint.congr_set_ae MeasureTheory.Ioo_ae_eq_Icc.symm
  · rw [← integral_Ioo_eq_Iθ' (fun x => (u x / Real.cos x) ^ 2 * σ x)]
    have hFle' : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (u x / Real.cos x) ^ 2 * σ x)
        ≤ 100 * (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), H x) := by
      simpa only [F] using hFle
    have hHval : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), H x)
        = (∫ x in Work.Spaces.Iθ, (u x) ^ 2 * σ x)
          + (∫ x in Work.Spaces.Iθ, (deriv u x) ^ 2 * σ x) := by
      rw [show (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), H x)
          = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ((u x) ^ 2 * σ x + (deriv u x) ^ 2 * σ x) from by simp only [H]]
      rw [MeasureTheory.integral_add
        (f := fun x => (u x) ^ 2 * σ x) (g := fun x => (deriv u x) ^ 2 * σ x)
        (h0.mono_set (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
        (h1.mono_set (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩))]
      rw [integral_Ioo_eq_Iθ' (fun x => (u x) ^ 2 * σ x),
        integral_Ioo_eq_Iθ' (fun x => (deriv u x) ^ 2 * σ x)]
    calc (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), F x)
        ≤ 100 * (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), H x) := hFle
      _ = 100 * ((∫ x in Work.Spaces.Iθ, (u x) ^ 2 * σ x)
            + (∫ x in Work.Spaces.Iθ, (deriv u x) ^ 2 * σ x)) := by rw [hHval]

end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.Top.Integrable.intervalIntegrable_vortLInf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Filter Topology
open scoped Topology NNReal Matrix ENNReal

namespace Work.FTS.Top.Integrable

/-
The Beale--Kato--Majda integrand `s ↦ Work.LWP.vortLInf B.u s = ⨆ x, ‖vorticity (B.u · s) x‖` is
interval-integrable on `[0,t]` for every `t < T`, for a blow-up datum
`B : Work.FTS.Top.BlowupAt α T`.

Route:
* `B.strip` gives `IsContDiffHolderOn ℝ α B.u.uncurry (univ ×ˢ Icc 0 S)` for every `S ∈ Ioo 0 T`;
  pick `S` with `t < S < T` and apply the *proved* workspace result
  `Work.ConstructionInstance.vorticity_bound_of_strip` (a joint `C^{1,α}` strip bound transfers to
  a uniform bound `‖vorticity (u · s) x‖ ≤ K` on the strictly shorter strip `s ∈ Ico 0 t`); then
  `vortLInf B.u s ≤ K` on `Ico 0 t` by `ciSup_le`.  Prove this as a helper
  `exists_bound_vortLInf_on_Ico` first: for `t ∈ Ico 0 T` there is `K ≥ 0` with
  `vortLInf B.u s ≤ K` for all `s ∈ Ico 0 t`.  (This is the honest "compaction" statement for
  `BlowupAt`: the bound is only on closed sub-strips `[0,t]`, `t < T`, which is exactly why the
  interface is not vacuous, unlike `Work.StabilityFar.AssemblyInputs`.)
* the slices `s ↦ ‖vorticity (B.u · s) x‖` are continuous at every `s ∈ Ioo 0 S` for each fixed
  `x`: at such a point `(x,s)` is an interior point of the strip `univ ×ˢ Ico 0 T`, so
  `ContDiffWithinAt` upgrades to `ContDiffAt` (`ContDiffWithinAt.contDiffAt`) and
  `fderiv ℝ B.u.uncurry` is continuous there (`ContDiffAt.continuousAt_fderiv`); combine with the
  description of `vorticity` through `fderiv` at a differentiable point (see
  `Submission/Work/SolutionDelivery/Measurable/continuousOn_vorticity_of_contDiffOn.lean` for the
  technique, or prove it directly using `fderiv_slice_eq`-style lemmas and
  `hasFDerivAt_prodMk_left`).  You may READ files under `Submission/Work/SolutionDelivery/` for
  technique, but do NOT import them.
* hence `s ↦ vortLInf B.u s` is lower semicontinuous on the open set `Ioo 0 t`: given
  `a < ⨆ x, θ x s` there is `x` with `a < θ x s` (use `lt_ciSup_iff` when the range is bounded
  above and `Real.iSup_of_not_bddAbove` otherwise), and `θ x` is continuous at `s`; so
  `{s | a < vortLInf B.u s}` is open there (equivalently use
  `lowerSemicontinuous_iSup`/`lowerSemicontinuous_ciSup`, or a countable dense subset of `R3`);
* a function which is lower semicontinuous on the open set `Ioo 0 t` is Borel measurable there
  (`LowerSemicontinuousOn`/`LowerSemicontinuous.measurable`); `Ioc 0 t` differs from `Ioo 0 t` by
  the null set `{t}`, so `vortLInf B.u` is a.e. strongly measurable on `Ioc 0 t`;
* with a.e. strong measurability on the finite measure space `volume.restrict (Ioc 0 t)` and the
  bound `K` on `Ico 0 t`, `IntegrableOn (vortLInf B.u) (Ioc 0 t) volume` follows from
  `MeasureTheory.Integrable.of_bound` (or `Integrable.mono'` against a constant majorant); finally
  `intervalIntegrable_iff` identifies `IntervalIntegrable f volume 0 t` with
  `IntegrableOn f (uIoc 0 t) volume`, and for `t = 0` the interval is empty (`uIoc 0 0 = ∅`), so
  that case is trivial.  Namespace `Work.FTS.Top`.
-/

/-- **The uniform vorticity bound on a closed sub-strip.**  By
`Work.ConstructionInstance.vorticity_bound_of_strip` applied to the joint `C^{1,α}` strip bound
`B.strip S₂` with `t < S₁ < S₂ < T`, the vorticity of every slice `B.u · s`, `s ∈ (0,t]`, is
bounded by a single constant `K ≥ 0`. -/
theorem exists_bound_vorticity_Ioc {α : NNReal} {T : ℝ} (B : BlowupAt α T) {t : ℝ}
    (ht : t ∈ Set.Ico 0 T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Set.Ioc 0 t, ∀ x : R3, ‖vorticity (B.u · s) x‖ ≤ K := by
  obtain ⟨S₁, htS₁, hS₁T⟩ := exists_between ht.2
  obtain ⟨S₂, hS₁S₂, hS₂T⟩ := exists_between hS₁T
  have hS₁pos : 0 < S₁ := lt_of_le_of_lt ht.1 htS₁
  have hS₂pos : 0 < S₂ := lt_trans hS₁pos hS₁S₂
  obtain ⟨K, hKnn, hK⟩ := Work.ConstructionInstance.vorticity_bound_of_strip (u := B.u)
    (S := S₂) (T := S₁) hS₁S₂ (B.strip S₂ ⟨hS₂pos, hS₂T⟩)
  exact ⟨K, hKnn, fun s hs x => hK s ⟨le_of_lt hs.1, lt_of_le_of_lt hs.2 htS₁⟩ x⟩

/-- **Joint continuity of the vorticity on an open strip.**  For `t ∈ Ico 0 T` there is `S` with
`t < S < T`; on the open strip `ℝ³ × (0,S)` — which contains `ℝ³ × (0,t]` — the map
`(x,s) ↦ ‖vorticity (B.u · s) x‖` is continuous (`continuousOn_vorticity_joint`). -/
theorem exists_continuousOn_vorticity {α : NNReal} {T : ℝ} (B : BlowupAt α T) {t : ℝ}
    (ht : t ∈ Set.Ico 0 T) :
    ∃ S : ℝ, t < S ∧
      ContinuousOn (fun p : R3 × ℝ => ‖vorticity (B.u · p.2) p.1‖) (Set.univ ×ˢ Set.Ioo 0 S) := by
  obtain ⟨S, htS, hST⟩ := exists_between ht.2
  have hSpos : 0 < S := lt_of_le_of_lt ht.1 htS
  exact ⟨S, htS, continuousOn_vorticity_joint (B.strip S ⟨hSpos, hST⟩).1⟩

/-- **A supremum over a separable family is a.e. strongly measurable on a right interval.**

Let `θ : ℝ³ → ℝ → ℝ` be such that `(y,s) ↦ θ y s` is continuous on the open strip `ℝ³ × (0,S)` and
such that for every `s ∈ (0,t]` the family `y ↦ θ y s` is bounded above.  Then `s ↦ ⨆ y, θ y s` is
a.e. strongly measurable on `(0,t]`.

Indeed, on `(0,t]` the function `s ↦ ⨆ y, θ y s` coincides with the supremum over a countable dense
subset `J ⊆ ℝ³` of the functions `s ↦ θ j s`, which are continuous on `(0,S) ⊇ (0,t]` and hence
a.e. strongly measurable; a countable supremum of such functions is a.e. strongly measurable
(`AEMeasurable.iSup`).  The two suprema agree at `s ∈ (0,t]` because the slice `y ↦ θ y s` is
continuous and bounded above: `≤` is `le_ciSup`, while for `≥` one uses that `{y | c < θ y s}` is a
neighbourhood of any `x` with `c < θ x s`, and the dense `J` meets it. -/
theorem aemeasurable_ciSup_of_continuousOn {θ : R3 → ℝ → ℝ} {S t : ℝ}
    (ht : 0 ≤ t) (htS : t < S)
    (hcont : ContinuousOn (fun p : R3 × ℝ => θ p.1 p.2) (Set.univ ×ˢ Set.Ioo 0 S))
    (hbdd : ∀ s ∈ Set.Ioc 0 t, BddAbove (Set.range fun y : R3 => θ y s)) :
    AEMeasurable (fun s => ⨆ y, θ y s) (volume.restrict (Set.Ioc 0 t)) := by
  obtain ⟨J, hJc, hJd⟩ := TopologicalSpace.exists_countable_dense R3
  haveI : Countable J := hJc.to_subtype
  haveI : Nonempty J := ⟨hJd.nonempty.some, hJd.nonempty.some_mem⟩
  have hopen : IsOpen (Set.univ ×ˢ Set.Ioo 0 S : Set (R3 × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hsub : Set.Ioc 0 t ⊆ Set.Ioo 0 S := fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 htS⟩
  -- each `s ↦ θ j s` is continuous on the open strip
  have hslice : ∀ j : J, ContinuousOn (fun s => θ (j : R3) s) (Set.Ioo 0 S) := by
    intro j
    have hmap : Set.MapsTo (fun s : ℝ => ((j : R3), s)) (Set.Ioo 0 S)
        (Set.univ ×ˢ Set.Ioo 0 S) := fun s hs => ⟨trivial, hs⟩
    exact hcont.comp' ((continuous_const.prodMk continuous_id).continuousOn) hmap
  have hmeas : ∀ j : J, AEMeasurable (fun s => θ (j : R3) s)
      (volume.restrict (Set.Ioc 0 t)) := fun j =>
    ((hslice j).aemeasurable measurableSet_Ioo).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  have hsup : AEMeasurable (fun s => ⨆ j : J, θ (j : R3) s)
      (volume.restrict (Set.Ioc 0 t)) := AEMeasurable.iSup hmeas
  refine AEMeasurable.congr hsup ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
  have hsS : s ∈ Set.Ioo 0 S := hsub hs
  have hbddJ : BddAbove (Set.range fun j : J => θ (j : R3) s) := by
    obtain ⟨c, hc⟩ := hbdd s hs
    exact ⟨c, by rintro y ⟨j, rfl⟩; exact hc ⟨(j : R3), rfl⟩⟩
  refine le_antisymm (ciSup_le fun j => le_ciSup (hbdd s hs) (j : R3)) (ciSup_le fun x => ?_)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hxcont : ContinuousAt (fun y : R3 => θ y s) x := by
    have hF : Tendsto (fun p : R3 × ℝ => θ p.1 p.2) (𝓝 (x, s)) (𝓝 (θ x s)) :=
      (hcont.continuousWithinAt ⟨trivial, hsS⟩).continuousAt (hopen.mem_nhds ⟨trivial, hsS⟩)
    have h2 : Tendsto (fun y : R3 => (y, s)) (𝓝 x) (𝓝 (x, s)) :=
      (continuous_id.prodMk continuous_const).continuousAt
    have h3 : Tendsto ((fun p : R3 × ℝ => θ p.1 p.2) ∘ fun y : R3 => (y, s)) (𝓝 x) (𝓝 (θ x s)) :=
      hF.comp h2
    change Tendsto ((fun p : R3 × ℝ => θ p.1 p.2) ∘ fun y : R3 => (y, s)) (𝓝 x) (𝓝 (θ x s))
    exact h3
  have hmem : {y : R3 | θ x s - ε < θ y s} ∈ 𝓝 x := by
    have hlt : θ x s - ε < θ x s := by linarith
    have h1 : (fun y : R3 => θ y s) ⁻¹' Set.Ioi (θ x s - ε) ∈ 𝓝 x :=
      hxcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds (s := Set.Ioi (θ x s - ε)) hlt)
    have h2 : (fun y : R3 => θ y s) ⁻¹' Set.Ioi (θ x s - ε) = {y : R3 | θ x s - ε < θ y s} := by
      ext y
      simp
    rw [h2] at h1
    exact h1
  have hj := hJd.inter_nhds_nonempty hmem
  have hjJ : hj.some ∈ J := mem_of_mem_inter_left hj.some_mem
  have hjmem : hj.some ∈ {y : R3 | θ x s - ε < θ y s} := mem_of_mem_inter_right hj.some_mem
  have hjval : θ x s - ε < θ hj.some s := hjmem
  have hle : θ hj.some s ≤ ⨆ j : J, θ (j : R3) s := le_ciSup hbddJ ⟨hj.some, hjJ⟩
  linarith

theorem intervalIntegrable_vortLInf {α : NNReal} {T : ℝ} (B : Work.FTS.Top.BlowupAt α T) :
    ∀ t ∈ Set.Ico 0 T, IntervalIntegrable (Work.LWP.vortLInf B.u) volume 0 t := by
  intro t ht
  obtain ⟨K, hKnn, hK⟩ := exists_bound_vorticity_Ioc B ht
  obtain ⟨S, htS, hcont⟩ := exists_continuousOn_vorticity B ht
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1]
  change IntegrableOn (fun s => ⨆ x, ‖vorticity (B.u · s) x‖) (Set.Ioc 0 t) volume
  have hbdd : ∀ s ∈ Set.Ioc 0 t, BddAbove (Set.range fun x : R3 => ‖vorticity (B.u · s) x‖) :=
    fun s hs => ⟨K, by rintro y ⟨x, rfl⟩; exact hK s hs x⟩
  refine IntegrableOn.of_bound measure_Ioc_lt_top ?_ K ?_
  · exact (aemeasurable_ciSup_of_continuousOn ht.1 htS hcont hbdd).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
    have hle : (⨆ x, ‖vorticity (B.u · s) x‖) ≤ K := ciSup_le fun x => hK s hs x
    have hnn : 0 ≤ ⨆ x, ‖vorticity (B.u · s) x‖ :=
      le_trans (norm_nonneg _) (le_ciSup (hbdd s hs) (0 : R3))
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith, hle⟩

end Work.FTS.Top.Integrable
end
-- ===== merged: Submission.Work.R1G.HkMem_gA =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.R1G

/-- A general membership criterion: a `SmoothNbhd` function whose `H^k`-integrand is dominated
on the quadrant by an integrable function `M` lies in `H^k`. -/
theorem HkMem_of_majorant (α : ℝ) (k : ℕ) {f M : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f)
    (hMslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ : ℝ => M z θ) Work.Spaces.Iθ)
    (hMz : IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f z θ ≤ M z θ) :
    Work.Spaces.HkMem α k f := by
  have hslice := Work.Coercivity.aesm_HkIntegrand_slice α k hsm
  have hjoint := Work.Coercivity.aesm_uncurry_HkIntegrand α k hsm
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  constructor
  · intro z hz
    refine Integrable.mono' (hMslice z hz) (hslice z hz) ?_
    filter_upwards [ae_restrict_mem hmesθ] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k f z θ)]
    exact hle z hz θ hθ
  · refine Integrable.mono' hMz hjoint.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem hmesz] with z hz
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ :=
      integral_nonneg_of_ae (ae_restrict_of_forall_mem hmesθ
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k f z θ))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem hmesθ (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k f z θ))
      (hMslice z hz)
      (ae_restrict_of_forall_mem hmesθ (fun θ hθ => hle z hz θ hθ))


theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity



end Work.R1G
end
end
-- ===== merged: Submission.Work.R1G.gTest_hkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.R1G

/-! ## The exponential decay beats every polynomial factor -/


/-! ## The three radial estimates -/




/-! ## The bounded angular factors -/

private lemma sin_two_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) ∧ Real.sin (2 * θ) ≤ 1 := by
  have h1 : 0 ≤ 2 * θ := by linarith [hθ.1]
  have h2 : 2 * θ ≤ Real.pi := by linarith [hθ.2, Real.pi_pos]
  exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi h1 h2, Real.sin_le_one _⟩





/-! ## The six weighted summands -/


/-! ## The pointwise bound on the `H²`-integrand, and the theorem -/

/-- If `|A| ≤ C` then `A² ≤ C²`. -/
private lemma sq_le_sq_of_abs_le {A C : ℝ} (h : |A| ≤ C) : A ^ 2 ≤ C ^ 2 := by
  rw [sq_le_sq, abs_of_nonneg (le_trans (abs_nonneg A) h)]
  exact h




end Work.R1G
end
end
-- ===== merged: Submission.Work.SolutionDelivery.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

namespace ConstructedSolution

variable {α : NNReal} (C : ConstructedSolution α)








end ConstructedSolution

end Work.SolutionDelivery
end
end
-- ===== merged: Submission.Work.SolutionDelivery.Scaling.Main =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery


end Work.SolutionDelivery
end
end
