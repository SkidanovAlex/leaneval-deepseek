import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
import Submission.Work.SSGRoute.PTW.AvgOpNeZero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTW

open MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal Pointwise

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]
  [T2Space Q] [MeasurableSpace Q] [BorelSpace Q] {μ : MeasureTheory.Measure Q}
  [MeasureTheory.Measure.IsMulLeftInvariant μ] [MeasureTheory.IsProbabilityMeasure μ]
  [MeasureTheory.IsLocallyFiniteMeasure μ] [MeasureTheory.Measure.InnerRegularCompactLTTop μ]

/-- There is a symmetric open neighbourhood `W ∋ 1` whose `y`-translate is disjoint from `W`. -/
theorem exists_open_symm_nhds_one_disjoint_translate (y : Q) (hy : y ≠ 1) :
    ∃ W : Set Q, IsOpen W ∧ (1 : Q) ∈ W ∧ W⁻¹ = W ∧ y ∉ W * W := by
  have hy1 : (1 : Q) ≠ y := hy.symm
  have hUne : ({y}ᶜ : Set Q) ∈ 𝓝 (1 : Q) :=
    (isClosed_singleton : IsClosed ({y} : Set Q)).isOpen_compl.mem_nhds (by simpa using hy1)
  obtain ⟨V, hVopen, hV1, hVV⟩ := exists_open_nhds_one_mul_subset hUne
  refine ⟨V ∩ V⁻¹, hVopen.inter hVopen.inv, ⟨hV1, by rw [Set.mem_inv]; simpa using hV1⟩, ?_, ?_⟩
  · rw [Set.inter_inv, inv_inv, Set.inter_comm]
  · intro h
    have hmem : y ∈ ({y}ᶜ : Set Q) := hVV (Set.mul_subset_mul Set.inter_subset_left
      Set.inter_subset_left h)
    simp at hmem

/-- Route: for `y ≠ 1` pick a symmetric open neighbourhood `W ∋ 1` with `y * W ∩ W = ∅` (T2/T3
group), and take `ξ := 1_W` as an element of `Lp ℂ 2 μ` (`MeasureTheory.indicatorConstLp` or
`ContinuousMap.toLp`-style construction); `regRep y ξ = 1_{y W} ≠ 1_W` because the two indicators
differ on the positive measure set `W` (`isOpenPosMeasure_of_isMulLeftInvariant_of_isProbabilityMeasure`,
proved in `AvgOpNeZero.lean`). -/
theorem exists_regRep_ne_self {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q] {μ : MeasureTheory.Measure Q}
    [MeasureTheory.Measure.IsMulLeftInvariant μ] [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.IsLocallyFiniteMeasure μ] [MeasureTheory.Measure.InnerRegularCompactLTTop μ]
    (y : Q) (hy : y ≠ 1) :
    ∃ ξ : MeasureTheory.Lp ℂ 2 μ, Work.SSGRoute.PTW.regRep (μ := μ) y ξ ≠ ξ := by
  obtain ⟨W, hWopen, hW1, hWinv, hyWW⟩ := exists_open_symm_nhds_one_disjoint_translate y hy
  -- `W` has positive measure and is measurable of finite measure
  have hWpos : μ W ≠ 0 :=
    (isOpenPosMeasure_of_isMulLeftInvariant_of_isProbabilityMeasure (μ := μ)).open_pos W hWopen
      ⟨1, hW1⟩
  have hWfin : μ W ≠ ⊤ := measure_ne_top μ W
  have hWmeas : MeasurableSet W := hWopen.measurableSet
  -- the candidate vector: the indicator of `W`
  let ξ : Lp ℂ 2 μ := indicatorConstLp 2 hWmeas hWfin (1 : ℂ)
  refine ⟨ξ, ?_⟩
  -- `y⁻¹ * x ∉ W` for `x ∈ W`, i.e. `x` is not in the `y`-translate of `W`
  have hdisj : ∀ x : Q, x ∈ W → y⁻¹ * x ∉ W := by
    intro x hx hx2
    refine hyWW ?_
    have h1 : (y⁻¹ * x)⁻¹ ∈ W := by
      have h2 : (y⁻¹ * x)⁻¹ ∈ W⁻¹ := Set.inv_mem_inv.mpr hx2
      rwa [hWinv] at h2
    have h3 : x * (y⁻¹ * x)⁻¹ ∈ W * W := Set.mul_mem_mul hx h1
    rwa [show x * (y⁻¹ * x)⁻¹ = y by group] at h3
  intro hcon
  -- `regRep y ξ` is the indicator of the translate `(y⁻¹ ·) ⁻¹' W`
  have hcon' : (DomMulAct.mk y⁻¹ : Qᵈᵐᵃ) • ξ = ξ := hcon
  have hcoeξ : ((ξ : Lp ℂ 2 μ) : Q → ℂ) =ᵐ[μ] W.indicator (fun _ => (1 : ℂ)) :=
    indicatorConstLp_coeFn
  have hraw := DomMulAct.mk_smul_indicatorConstLp (μ := μ) (p := 2) (y⁻¹) hWmeas hWfin (1 : ℂ)
  have hcoeA : ((((DomMulAct.mk y⁻¹ : Qᵈᵐᵃ) • ξ) : Lp ℂ 2 μ) : Q → ℂ) =ᵐ[μ]
      ((fun x : Q => y⁻¹ • x) ⁻¹' W).indicator (fun _ => (1 : ℂ)) := by
    rw [show (DomMulAct.mk y⁻¹ : Qᵈᵐᵃ) • ξ = _ from hraw]
    exact indicatorConstLp_coeFn
  have hcoeeq : ((((DomMulAct.mk y⁻¹ : Qᵈᵐᵃ) • ξ) : Lp ℂ 2 μ) : Q → ℂ) =ᵐ[μ] (ξ : Q → ℂ) := by
    rw [hcon']
  -- hence the two indicators agree almost everywhere
  have hae : ((fun x : Q => y⁻¹ • x) ⁻¹' W).indicator (fun _ => (1 : ℂ)) =ᵐ[μ]
      W.indicator (fun _ => (1 : ℂ)) := hcoeA.symm.trans (hcoeeq.trans hcoeξ)
  have hnull := MeasureTheory.ae_iff.mp hae
  -- but they differ on all of `W`, a positive measure set
  have hsub : W ⊆ {x : Q | ¬ (((fun x : Q => y⁻¹ • x) ⁻¹' W).indicator (fun _ => (1 : ℂ)) x
      = W.indicator (fun _ => (1 : ℂ)) x)} := by
    intro x hx
    have hxA : x ∉ (fun x : Q => y⁻¹ • x) ⁻¹' W := by
      intro hx'
      have hx'' : y⁻¹ • x ∈ W := hx'
      rw [smul_eq_mul] at hx''
      exact hdisj x hx hx''
    simp only [Set.mem_ofPred_eq]
    rw [Set.indicator_of_notMem hxA (fun _ => (1 : ℂ)),
      Set.indicator_of_mem hx (fun _ => (1 : ℂ))]
    exact zero_ne_one
  have hle : μ W ≤ μ {x : Q | ¬ (((fun x : Q => y⁻¹ • x) ⁻¹' W).indicator (fun _ => (1 : ℂ)) x
      = W.indicator (fun _ => (1 : ℂ)) x)} := measure_mono hsub
  rw [hnull] at hle
  exact hWpos (nonpos_iff_eq_zero.mp hle)

end Work.SSGRoute.PTW
