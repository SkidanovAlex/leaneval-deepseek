import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.ConstructionInstance.AxiNoSwirlSymm
import Submission.Work.Cyl.norm_angularVec
import Submission.Work.FTS.BSSwirl.hasDerivAt_rotLE
import Submission.Work.FTS.BSSwirl.norm_rotLE_sub_le

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
