import Mathlib
import Submission.Work.SSGRoute.PTW.RegularRep
import Submission.Work.SSGRoute.PTW.AvgOpNeZero
import Submission.Work.SSGRoute.PTW.avgOp_regRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The kernel of the averaging operator is orthogonal to the orbit of `ξ`

For a compact Hausdorff topological group `Q` with a left-invariant probability measure `μ`
(the Haar probability measure), and the averaging operator

`avgOp ξ = ∫ g, |regRep g ξ⟩⟨regRep g ξ| dμ(g)`

on `L²(Q, μ)`, we show that any `η` killed by `avgOp ξ` is orthogonal to the whole orbit
`{regRep g ξ | g : Q}` of `ξ`:

`avgOp ξ η = 0 → ∀ g, ⟪regRep g ξ, η⟫ = 0`.

This is the positivity input for the spectral argument in `NontrivialEigenspace.lean`.

## Proof

`avgOp ξ` is positive semidefinite: evaluating the identity `avgOp ξ = ∫ g, |regRep g ξ⟩⟨regRep g ξ|`
against `η` and commuting `innerSL ℂ η` with the Bochner integral gives

`⟪η, avgOp ξ η⟫ = ∫ g, ⟪η, ⟪regRep g ξ, η⟫ • regRep g ξ⟫ = ∫ g, ‖⟪regRep g ξ, η⟫‖²`,

a continuous nonnegative real function whose integral is `0` when `avgOp ξ η = 0`.  As `μ` is
positive on nonempty opens, an a.e. vanishing continuous function vanishes identically.  Hence
`‖⟪regRep g ξ, η⟫‖² = 0` for all `g`, i.e. `⟪regRep g ξ, η⟫ = 0`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.PTW

open MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]
  [T2Space Q] [MeasurableSpace Q] [BorelSpace Q] {μ : Measure Q}
  [Measure.IsMulLeftInvariant μ] [IsProbabilityMeasure μ] [IsLocallyFiniteMeasure μ]
  [μ.InnerRegularCompactLTTop]

/-- The function `g ↦ ⟪regRep g ξ, η⟫` is continuous. -/
theorem continuous_inner_regRep (ξ η : Lp ℂ 2 μ) :
    Continuous fun g : Q => inner ℂ (regRep (μ := μ) g ξ) η :=
  continuous_inner.comp ((continuous_regRep_apply (μ := μ) ξ).prodMk
    (continuous_const : Continuous fun _ : Q => (η : Lp ℂ 2 μ)))

/-- Evaluating the averaging operator against `η` moves `innerSL ℂ η` inside the Bochner
integral: `⟪η, avgOp ξ η⟫ = ∫ g, ⟪η, |regRep g ξ⟩⟨regRep g ξ| η⟫`. -/
theorem inner_avgOp_apply (ξ η : Lp ℂ 2 μ) :
    inner ℂ η ((avgOp (μ := μ) ξ) η) =
      ∫ g, inner ℂ η
        (rankOneOp (μ := μ) (regRep (μ := μ) g ξ) (regRep (μ := μ) g ξ) η) ∂μ := by
  rw [avgOp]
  have h := ContinuousLinearMap.integral_comp_comm
    ((innerSL ℂ η).comp (ContinuousLinearMap.apply ℂ (Lp ℂ 2 μ) η))
    (integrable_rankOneOp_regRep (μ := μ) ξ)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    innerSL_apply_apply] at h
  exact h.symm

/-- The integrand of `inner_avgOp_apply` is integrable (it is continuous on the compact space
`Q`). -/
theorem integrable_inner_rankOneOp_regRep (ξ η : Lp ℂ 2 μ) :
    Integrable (fun g : Q => inner ℂ η
      (rankOneOp (μ := μ) (regRep (μ := μ) g ξ) (regRep (μ := μ) g ξ) η)) μ := by
  refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
  have h2 : Continuous fun g : Q => inner ℂ η (regRep (μ := μ) g ξ) :=
    continuous_inner.comp ((continuous_const : Continuous fun _ : Q => (η : Lp ℂ 2 μ)).prodMk
      (continuous_regRep_apply (μ := μ) ξ))
  have hfun : (fun g : Q =>
      inner ℂ η (rankOneOp (μ := μ) (regRep (μ := μ) g ξ) (regRep (μ := μ) g ξ) η))
      = fun g : Q => inner ℂ (regRep (μ := μ) g ξ) η * inner ℂ η (regRep (μ := μ) g ξ) := by
    funext g; rw [rankOneOp_apply, inner_smul_right]
  rw [hfun]
  exact (continuous_inner_regRep (μ := μ) ξ η).mul h2

/-- Pointwise, the real part of `⟪η, |a⟩⟨a| η⟫` is `‖⟪a, η⟫‖²`. -/
theorem re_inner_rankOneOp (a η : Lp ℂ 2 μ) :
    RCLike.re (inner ℂ η (rankOneOp (μ := μ) a a η)) = ‖inner ℂ a η‖ ^ 2 := by
  rw [rankOneOp_apply, inner_smul_right]
  have hc : inner ℂ η a = starRingEnd ℂ (inner ℂ a η) :=
    (inner_conj_symm (x := η) (y := a)).symm
  rw [hc, RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- **Kernel of the averaging operator vs. the orbit.**  If `η` is annihilated by `avgOp ξ`, then
`η` is orthogonal to every element `regRep g ξ` of the orbit of `ξ` under the regular
representation. -/
theorem avgOp_ker_le_orthogonal_orbit {Q : Type*} [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [CompactSpace Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
    {μ : MeasureTheory.Measure Q} [MeasureTheory.Measure.IsMulLeftInvariant μ]
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsLocallyFiniteMeasure μ]
    [MeasureTheory.Measure.InnerRegularCompactLTTop μ] (ξ : MeasureTheory.Lp ℂ 2 μ) :
    ∀ η : MeasureTheory.Lp ℂ 2 μ, Work.SSGRoute.PTW.avgOp (μ := μ) ξ η = 0 →
      ∀ g : Q, inner ℂ (Work.SSGRoute.PTW.regRep (μ := μ) g ξ) η = 0 := by
  intro η hη g
  -- `⟪η, avgOp ξ η⟫` is the integral of the real, nonnegative integrand `‖⟪regRep g ξ, η⟫‖²`
  have hre : RCLike.re (inner ℂ η ((avgOp (μ := μ) ξ) η)) = ∫ g, RCLike.re (inner ℂ η
      (rankOneOp (μ := μ) (regRep (μ := μ) g ξ) (regRep (μ := μ) g ξ) η)) ∂μ := by
    rw [inner_avgOp_apply]
    exact (Complex.reCLM.integral_comp_comm (integrable_inner_rankOneOp_regRep (μ := μ) ξ η)).symm
  have hre0 : RCLike.re (inner ℂ η ((avgOp (μ := μ) ξ) η)) = 0 := by rw [hη]; simp
  have hcontR : Continuous fun g : Q => ‖inner ℂ (regRep (μ := μ) g ξ) η‖ ^ 2 :=
    (continuous_inner_regRep (μ := μ) ξ η).norm.pow 2
  have hintR : Integrable (fun g : Q => ‖inner ℂ (regRep (μ := μ) g ξ) η‖ ^ 2) μ :=
    Continuous.integrable_of_hasCompactSupport hcontR (HasCompactSupport.of_compactSpace _)
  have hnonneg : 0 ≤ᵐ[μ] fun g : Q => ‖inner ℂ (regRep (μ := μ) g ξ) η‖ ^ 2 :=
    Eventually.of_forall fun g => sq_nonneg _
  have hcongr : (∫ g, RCLike.re (inner ℂ η
        (rankOneOp (μ := μ) (regRep (μ := μ) g ξ) (regRep (μ := μ) g ξ) η)) ∂μ)
      = ∫ g, ‖inner ℂ (regRep (μ := μ) g ξ) η‖ ^ 2 ∂μ :=
    integral_congr_ae
      (Eventually.of_forall fun g => re_inner_rankOneOp (μ := μ) (regRep (μ := μ) g ξ) η)
  have hint_eq : ∫ g, ‖inner ℂ (regRep (μ := μ) g ξ) η‖ ^ 2 ∂μ = 0 := by
    rw [← hcongr, ← hre, hre0]
  -- a nonnegative function with vanishing integral is zero a.e.
  have hae : (fun g : Q => ‖inner ℂ (regRep (μ := μ) g ξ) η‖ ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hintR).mp hint_eq
  -- `μ` is positive on nonempty opens, so an a.e. vanishing continuous function is identically 0
  have hzero : (fun g : Q => ‖inner ℂ (regRep (μ := μ) g ξ) η‖ ^ 2) = 0 := by
    haveI : μ.IsOpenPosMeasure :=
      isOpenPosMeasure_of_isMulLeftInvariant_of_isProbabilityMeasure (μ := μ)
    exact (Continuous.ae_eq_iff_eq μ hcontR
      (continuous_const : Continuous fun _ : Q => (0 : ℝ))).mp hae
  have hval : ‖inner ℂ (regRep (μ := μ) g ξ) η‖ ^ 2 = 0 := by
    have := congr_fun hzero g; simpa using this
  have hnorm : ‖inner ℂ (regRep (μ := μ) g ξ) η‖ = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hval
  rwa [norm_eq_zero] at hnorm

end Work.SSGRoute.PTW
