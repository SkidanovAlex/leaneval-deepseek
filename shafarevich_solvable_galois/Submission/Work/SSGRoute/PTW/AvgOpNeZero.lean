import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.SSGRoute.PTW.RegularRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Positivity input: a left-invariant probability measure on a compact group is open-positive

`MeasureTheory.Measure.IsOpenPosMeasure μ` ("every non-empty open set has positive measure") is *not*
an instance for an abstract left-invariant probability measure, and both the sibling files
(`openIndexPSubgroup.lean` and friends) and the `avgOp`-positivity arguments need it.

Proof: if an open neighbourhood `V ∋ 1` had measure zero, the preimages
`W_g := (fun x => g * x) ⁻¹' V` would cover the compact group (`y ∈ W_{y⁻¹}`), so finitely many cover
it, and each has measure `μ W_g = μ V = 0`; then `1 = μ univ ≤ ∑ μ W_g = 0`.  For a general non-empty
open `U ∋ x`, the preimage `(fun u => x * u) ⁻¹' U` is an open neighbourhood of `1` of the same
measure.

DONE in this file (sorry-free): `isOpenPosMeasure_of_isMulLeftInvariant_of_isProbabilityMeasure`.

Next step in this lane (separate, not yet done): `avgOp ξ ≠ 0` for `ξ ≠ 0`, via
`re ⟪ξ, avgOp ξ ξ⟫ = ∫ g, ‖⟪regRep g ξ, ξ⟫‖² ∂μ ≥ 0`, the integrand being `‖ξ‖⁴ > 0` at `g = 1`;
the positivity input for that is exactly the lemma proved here.

Lessons from the first attempt at that expansion (all verified against Mathlib):
* `ContinuousLinearMap.integral_comp_comm (L) (hint) : ∫ x, L (φ x) = L (∫ x, φ x)`, so to rewrite
  `(∫ g, T g) ξ = ∫ g, T g ξ` one uses it with `L := ContinuousLinearMap.apply ℂ (Lp ℂ 2 μ) ξ`
  in the `.symm` direction;
* `ContinuousLinearMap.apply ℂ F : E →L[ℂ] ((E →L[ℂ] F) →L[ℂ] F)` is the evaluation `T ↦ T ξ`;
* integrability of the integrand `g ↦ rankOneOp (regRep g ξ) (regRep g ξ)` follows from the uniform
  bound `‖rankOneOp a a‖ ≤ ‖a‖ * ‖a‖ = ‖ξ‖ ^ 2` (via `LinearMap.mkContinuous_norm_le`) together
  with measurability; note `Integrable.of_bound` needs extra instances
  (`SecondCountableTopologyEither` showed up as a blocker in the naive attempt), so `hint` is best
  taken from a continuity lemma for `g ↦ rankOneOp (regRep g ξ) (regRep g ξ)` — `Continuous.clm_comp`
  does *not* apply directly (it is for composition of CLM-valued functions); instead write
  `rankOneOp a b = (innerSL ℂ a).smulRight b` and use continuity of `innerSL` and of `smulRight`.
* The last step is `IsOpenPosMeasure.open_pos` on `{g | ‖ξ‖ ^ 4 / 2 < ‖⟪regRep g ξ, ξ⟫‖}`.

DONE in this file: `rankOneOp_eq_smulRight`, `continuous_rankOneOp_regRep`,
`integrable_rankOneOp_regRep` — i.e. steps 1, 2 and 5 of route (a) below.  Also worth knowing:
`Integrable.of_bound` and `Integrable.mono'` are *unusable* for the operator-valued integrand
(arraying of `H →L[ℂ] H`) because they demand `SecondCountableTopologyEither Q (H →L[ℂ] H)`, which
is false here; `Continuous.integrable_of_hasCompactSupport` +
`HasCompactSupport.of_compactSpace` has no such requirement and works.

Remaining for `avgOp_ne_zero`: the two commutation steps, namely
`(avgOp ξ) ξ = ∫ g, T g ξ` via `(ContinuousLinearMap.integral_comp_comm
(ContinuousLinearMap.apply ℂ (Lp ℂ 2 μ) ξ) (integrable_rankOneOp_regRep ξ)).symm`, and
`re ⟪ξ, (avgOp ξ) ξ⟫ = ∫ g, re ⟪ξ, T g ξ⟫` via `integral_comp_comm` with `Complex.reCLM` composed
with `innerSL ℂ ξ`; then `IsOpenPosMeasure.open_pos` on `{g | ‖ξ‖⁴/2 < ‖⟪regRep g ξ, ξ⟫‖}`.

Route (a) for the *continuity* of the integrand, with the API verified by `#check`:
* `rankOneOp a b = (innerSL ℂ a).smulRight b` (`ContinuousLinearMap.smulRight_apply :
  (c.smulRight f) x = c x • f`); equivalently `(ContinuousLinearMap.smulRightL ℂ H H) f c`, where
  `smulRightL (𝕜) (E) (Fₗ) : StrongDual 𝕜 E →L[𝕜] Fₗ →L[𝕜] (E →L[𝕜] Fₗ)` is a *continuous linear*
  map in both variables;
* `g ↦ regRep g ξ` is continuous (`continuous_regRep_apply` in `RegularRep.lean`);
* the remaining input is continuity of `a ↦ innerSL ℂ a : H → StrongDual ℂ H`; Mathlib has
  `toDualMap 𝕜 E` with `(toDualMap 𝕜 E).toContinuousLinearMap = innerSL 𝕜`
  (`Analysis/InnerProductSpace/Dual.lean:73`), and `toDualMap` is a linear isometry equivalence, so
  composing with it gives the required continuity.
Then `Integrable.of_bound` with the uniform bound `‖rankOneOp a a‖ ≤ ‖ξ‖ ^ 2` (already checked) gives
`hint`.
-/

namespace Work.SSGRoute.PTW

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]
  [T2Space Q] [MeasurableSpace Q] [BorelSpace Q] {μ : Measure Q}
  [Measure.IsMulLeftInvariant μ] [IsProbabilityMeasure μ]

/-- **A left-invariant probability measure on a compact group is open-positive**: every non-empty
open set has positive measure. -/
theorem isOpenPosMeasure_of_isMulLeftInvariant_of_isProbabilityMeasure :
    Measure.IsOpenPosMeasure μ := by
  constructor
  intro U hU hUne
  -- an open neighbourhood of `1` has positive measure
  have key : ∀ V : Set Q, IsOpen V → (1 : Q) ∈ V → 0 < μ V := by
    intro V hVo h1V
    by_contra hcon
    have hzero : μ V = 0 := le_antisymm (not_lt.mp hcon) zero_le
    have hcover : (Set.univ : Set Q) ⊆ ⋃ g : Q, (fun x => g * x) ⁻¹' V := by
      intro y _
      exact Set.mem_iUnion.mpr ⟨y⁻¹, by simpa using h1V⟩
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover _
      (fun g => hVo.preimage (continuous_const_mul g)) hcover
    have hmeasure : ∀ g : Q, μ ((fun x => g * x) ⁻¹' V) = μ V := fun g => by
      rw [← Measure.map_apply (measurable_const_mul g) hVo.measurableSet]
      rw [map_mul_left_eq_self μ g]
    have hle : (1 : ℝ≥0∞) ≤ ∑ g ∈ s, μ V := by
      calc (1 : ℝ≥0∞) = μ (Set.univ : Set Q) := by rw [measure_univ]
        _ ≤ μ (⋃ g ∈ s, (fun x => g * x) ⁻¹' V) := measure_mono hs
        _ ≤ ∑ g ∈ s, μ ((fun x => g * x) ⁻¹' V) := measure_biUnion_finset_le s _
        _ = ∑ g ∈ s, μ V := Finset.sum_congr rfl (fun g _ => hmeasure g)
    rw [Finset.sum_const, nsmul_eq_mul, hzero, mul_zero] at hle
    exact absurd hle (by norm_num)
  -- transfer to an arbitrary non-empty open set
  obtain ⟨x, hxU⟩ := hUne
  have hVopen : IsOpen ((fun u : Q => x * u) ⁻¹' U) := hU.preimage (continuous_const_mul x)
  have h1V : (1 : Q) ∈ (fun u : Q => x * u) ⁻¹' U := by simpa using hxU
  have hpos : 0 < μ ((fun u : Q => x * u) ⁻¹' U) := key _ hVopen h1V
  have hmap : Measure.map (fun u : Q => x * u) μ = μ := map_mul_left_eq_self μ x
  have hm : μ ((fun u : Q => x * u) ⁻¹' U) = μ U := by
    rw [← Measure.map_apply (measurable_const_mul x) hU.measurableSet]
    rw [hmap]
  rw [← hm]
  exact hpos.ne'

section Integrand

/-- `rankOneOp a b` is `(innerSL ℂ a).smulRight b`. -/
theorem rankOneOp_eq_smulRight (a b : Lp ℂ 2 μ) :
    rankOneOp (μ := μ) a b = (innerSL ℂ a).smulRight b := by
  ext η
  rw [rankOneOp_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

/-- Continuity of the integrand of `avgOp ξ`. -/
theorem continuous_rankOneOp_regRep (ξ : Lp ℂ 2 μ) :
    Continuous fun g : Q =>
      rankOneOp (μ := μ) (regRep (μ := μ) g ξ) (regRep (μ := μ) g ξ) := by
  have hf : Continuous fun g : Q =>
      (innerSL ℂ (regRep (μ := μ) g ξ) : Lp ℂ 2 μ →L[ℂ] ℂ) := by
    have h := (InnerProductSpace.toDualMap ℂ (Lp ℂ 2 μ)).continuous.comp
      (continuous_regRep_apply (μ := μ) ξ)
    exact h
  have hT : Continuous fun g : Q =>
      (ContinuousLinearMap.smulRightL ℂ (Lp ℂ 2 μ) (Lp ℂ 2 μ))
        (innerSL ℂ (regRep (μ := μ) g ξ)) :=
    (ContinuousLinearMap.smulRightL ℂ (Lp ℂ 2 μ) (Lp ℂ 2 μ)).continuous.comp hf
  have h := hT.clm_apply (continuous_regRep_apply (μ := μ) ξ)
  exact h.congr (fun g => (rankOneOp_eq_smulRight (μ := μ) (regRep (μ := μ) g ξ)
    (regRep (μ := μ) g ξ)).symm)

/-- The integrand of `avgOp ξ` is integrable, with uniform bound `‖ξ‖ ^ 2`. -/
theorem integrable_rankOneOp_regRep (ξ : Lp ℂ 2 μ) :
    Integrable (fun g : Q =>
      rankOneOp (μ := μ) (regRep (μ := μ) g ξ) (regRep (μ := μ) g ξ)) μ :=
  Continuous.integrable_of_hasCompactSupport (continuous_rankOneOp_regRep (μ := μ) ξ)
    (HasCompactSupport.of_compactSpace _)

/-- First commutation step: evaluating `avgOp ξ` at `ξ` moves the evaluation inside the
Bochner integral. -/
theorem avgOp_self_apply (ξ : Lp ℂ 2 μ) :
    (avgOp (μ := μ) ξ) ξ =
      ∫ g, rankOneOp (μ := μ) (regRep (μ := μ) g ξ) (regRep (μ := μ) g ξ) ξ ∂μ := by
  rw [avgOp]
  exact (ContinuousLinearMap.integral_comp_comm
    (ContinuousLinearMap.apply ℂ (Lp ℂ 2 μ) ξ)
    (integrable_rankOneOp_regRep (μ := μ) ξ)).symm

/-- Second commutation step: `⟪ξ, (avgOp ξ) ξ⟫` is the integral of the inner products. -/
theorem inner_avgOp_self (ξ : Lp ℂ 2 μ) :
    inner ℂ ξ ((avgOp (μ := μ) ξ) ξ) =
      ∫ g, inner ℂ ξ (rankOneOp (μ := μ) (regRep (μ := μ) g ξ) (regRep (μ := μ) g ξ) ξ) ∂μ := by
  rw [avgOp]
  have h := ContinuousLinearMap.integral_comp_comm
    ((innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ (Lp ℂ 2 μ) ξ))
    (integrable_rankOneOp_regRep (μ := μ) ξ)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    innerSL_apply_apply] at h
  exact h.symm

/-- **`avgOp ξ` is nonzero for `ξ ≠ 0`.**  Indeed
`re ⟪ξ, avgOp ξ ξ⟫ = ∫ g, ‖⟪regRep g ξ, ξ⟫‖² ∂μ`, and the integrand is positive at `g = 1`. -/
theorem avgOp_ne_zero (ξ : Lp ℂ 2 μ) (hξ : ξ ≠ 0) : avgOp (μ := μ) ξ ≠ 0 := by
  intro h0
  -- the integrand of the second commutation step is integrable
  have hint2 : Integrable (fun g : Q => inner ℂ ξ
      (rankOneOp (μ := μ) (regRep (μ := μ) g ξ) (regRep (μ := μ) g ξ) ξ)) μ :=
    Continuous.integrable_of_hasCompactSupport
      (continuous_inner.comp
        ((continuous_const : Continuous fun _ : Q => (ξ : Lp ℂ 2 μ)).prodMk
          ((continuous_rankOneOp_regRep (μ := μ) ξ).clm_apply
            (continuous_const : Continuous fun _ : Q => (ξ : Lp ℂ 2 μ)))))
      (HasCompactSupport.of_compactSpace _)
  have hre : RCLike.re (inner ℂ ξ ((avgOp (μ := μ) ξ) ξ))
      = ∫ g, RCLike.re (inner ℂ ξ
          (rankOneOp (μ := μ) (regRep (μ := μ) g ξ) (regRep (μ := μ) g ξ) ξ)) ∂μ := by
    rw [inner_avgOp_self]
    exact (Complex.reCLM.integral_comp_comm hint2).symm
  have hzero : RCLike.re (inner ℂ ξ ((avgOp (μ := μ) ξ) ξ)) = 0 := by rw [h0]; simp
  -- pointwise the integrand is the square of the norm of an inner product
  have hpt : ∀ g : Q, RCLike.re (inner ℂ ξ
      (rankOneOp (μ := μ) (regRep (μ := μ) g ξ) (regRep (μ := μ) g ξ) ξ))
      = ‖inner ℂ (regRep (μ := μ) g ξ) ξ‖ ^ 2 := by
    intro g
    have hc : inner ℂ ξ (regRep (μ := μ) g ξ)
        = starRingEnd ℂ (inner ℂ (regRep (μ := μ) g ξ) ξ) :=
      (inner_conj_symm (x := ξ) (y := regRep (μ := μ) g ξ)).symm
    rw [rankOneOp_apply, inner_smul_right, hc, RCLike.mul_conj, ← RCLike.ofReal_pow,
      RCLike.ofReal_re]
  have hcontR : Continuous fun g : Q => ‖inner ℂ (regRep (μ := μ) g ξ) ξ‖ ^ 2 :=
    ((continuous_inner.comp ((continuous_regRep_apply (μ := μ) ξ).prodMk
      (continuous_const : Continuous fun _ : Q => (ξ : Lp ℂ 2 μ))))).norm.pow 2
  have hintR : Integrable (fun g : Q => ‖inner ℂ (regRep (μ := μ) g ξ) ξ‖ ^ 2) μ :=
    Continuous.integrable_of_hasCompactSupport hcontR (HasCompactSupport.of_compactSpace _)
  have hnonneg : 0 ≤ᵐ[μ] fun g : Q => ‖inner ℂ (regRep (μ := μ) g ξ) ξ‖ ^ 2 :=
    Eventually.of_forall fun g => sq_nonneg _
  have hsupp : 0 < μ (Function.support fun g : Q => ‖inner ℂ (regRep (μ := μ) g ξ) ξ‖ ^ 2) := by
    have hf : Continuous fun g : Q => inner ℂ (regRep (μ := μ) g ξ) ξ :=
      continuous_inner.comp ((continuous_regRep_apply (μ := μ) ξ).prodMk
        (continuous_const : Continuous fun _ : Q => (ξ : Lp ℂ 2 μ)))
    have hU : IsOpen {g : Q | inner ℂ (regRep (μ := μ) g ξ) ξ ≠ 0} :=
      (isClosed_singleton.isOpen_compl).preimage hf
    have h1 : (1 : Q) ∈ {g : Q | inner ℂ (regRep (μ := μ) g ξ) ξ ≠ 0} := by
      have hone : regRep (μ := μ) (1 : Q) ξ = ξ := by rw [regRep_one]; rfl
      rw [Set.mem_ofPred_eq, hone]
      exact fun h => hξ (inner_self_eq_zero.mp h)
    have hne : μ {g : Q | inner ℂ (regRep (μ := μ) g ξ) ξ ≠ 0} ≠ 0 :=
      (isOpenPosMeasure_of_isMulLeftInvariant_of_isProbabilityMeasure (μ := μ)).open_pos
        _ hU ⟨1, h1⟩
    have hle : μ {g : Q | inner ℂ (regRep (μ := μ) g ξ) ξ ≠ 0}
        ≤ μ (Function.support fun g : Q => ‖inner ℂ (regRep (μ := μ) g ξ) ξ‖ ^ 2) :=
      measure_mono fun g hg => pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)
    exact lt_of_lt_of_le (lt_of_le_of_ne zero_le (Ne.symm hne)) hle
  have hposint : 0 < ∫ g, ‖inner ℂ (regRep (μ := μ) g ξ) ξ‖ ^ 2 ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae hnonneg hintR).mpr hsupp
  have hcongr : (∫ g, RCLike.re (inner ℂ ξ
      (rankOneOp (μ := μ) (regRep (μ := μ) g ξ) (regRep (μ := μ) g ξ) ξ)) ∂μ)
      = ∫ g, ‖inner ℂ (regRep (μ := μ) g ξ) ξ‖ ^ 2 ∂μ :=
    integral_congr_ae (Eventually.of_forall fun g => hpt g)
  rw [hzero] at hre
  rw [← hcongr, ← hre] at hposint
  exact absurd hposint (lt_irrefl 0)

end Integrand


end Work.SSGRoute.PTW
