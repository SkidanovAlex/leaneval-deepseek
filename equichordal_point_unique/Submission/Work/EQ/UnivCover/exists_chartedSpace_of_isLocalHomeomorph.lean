import Mathlib
import Submission.Work.EQ.UnivCover.Defs

/-!
# Pulling back a complex charted space structure along a local homeomorphism

Given a complex manifold `X` and a local homeomorphism `φ : S → X` out of a topological space `S`,
the space `S` inherits a charted space structure: the chart at `s : S` is obtained by reading
`φ` through the chart of `X` at `φ s`.  Because `φ` agrees with an open partial homeomorphism on a
neighbourhood of `s`, this is a genuine chart, and the transition maps between two such charts are
exactly the transition maps of the atlas of `X` (the local inverses of `φ` cancel), so `S` becomes
a complex manifold and `φ` is holomorphic.

The main result is `exists_chartedSpace_of_isLocalHomeomorph`.
-/

set_option warn.classDefReducibility false
set_option linter.style.haveILetI false

namespace Work.EQ.UnivCover

open Set OpenPartialHomeomorph
open scoped Manifold Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {S : Type*} [TopologicalSpace S]

/-- The chart on `S` at `s`, obtained by transporting the chart of `X` at `φ s` along the local
homeomorphism `φ`.  Here `(hφ s).choose` is one of the open partial homeomorphisms agreeing with
`φ` near `s`. -/
def pullChart (φ : S → X) (hφ : IsLocalHomeomorph φ) (s : S) : OpenPartialHomeomorph S ℂ :=
  (hφ s).choose.trans (chartAt ℂ (φ s))

/-- The charted space structure on `S` induced by a local homeomorphism `φ : S → X` into a complex
charted space. -/
def pullChartedSpace (φ : S → X) (hφ : IsLocalHomeomorph φ) : ChartedSpace ℂ S where
  atlas := Set.range (pullChart φ hφ)
  chartAt := pullChart φ hφ
  mem_chart_source s := by
    rw [pullChart, trans_source]
    exact ⟨(hφ s).choose_spec.1, by
      rw [← (hφ s).choose_spec.2]; exact mem_chart_source ℂ (φ s)⟩
  chart_mem_atlas s := ⟨s, rfl⟩

/-- The pulled back charted space structure on `S` is a complex manifold, whenever `X` is. -/
theorem isManifold_pullChartedSpace [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {φ : S → X} (hφ : IsLocalHomeomorph φ) :
    letI := pullChartedSpace φ hφ
    IsManifold (modelWithCornersSelf ℂ ℂ) 1 S := by
  letI := pullChartedSpace φ hφ
  refine { compatible := ?_ }
  intro e e' he he'
  simp only [atlas] at he he'
  obtain ⟨s, rfl⟩ := he
  obtain ⟨s', rfl⟩ := he'
  simp only [pullChart]
  let es := (hφ s).choose
  let es' := (hφ s').choose
  let Cs := chartAt ℂ (φ s)
  let Cs' := chartAt ℂ (φ s')
  -- `es` and `es'` are two open partial homeomorphisms which agree with `φ`, hence with each
  -- other, as functions.
  have hes : (es : S → X) = es' :=
    ((hφ s).choose_spec.2.symm).trans ((hφ s').choose_spec.2)
  -- the inverse of the chart at `s`, as a function
  have hsymm : ∀ y : ℂ, (((es.trans Cs).symm : OpenPartialHomeomorph ℂ S) y) =
      es.symm (Cs.symm y) := by
    intro y
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_apply]
  have htarget : (es.trans Cs).target = Cs.target ∩ Cs.symm ⁻¹' es.target :=
    OpenPartialHomeomorph.trans_target es Cs
  -- the key point: on the target of `es`, the local homeomorphism `es'` is the inverse of `es`
  have hkey_gen : ∀ z ∈ es.target, ((es' : S → X) (es.symm z)) = z := by
    intro z hz
    rw [← hes]
    exact OpenPartialHomeomorph.right_inv es hz
  -- the transition map of the atlas of `X`, which lies in the groupoid since `X` is a manifold
  have hg : Cs.symm.trans Cs' ∈ contDiffGroupoid 1 (modelWithCornersSelf ℂ ℂ) :=
    StructureGroupoid.compatible (contDiffGroupoid 1 (modelWithCornersSelf ℂ ℂ))
      (chart_mem_atlas ℂ (φ s)) (chart_mem_atlas ℂ (φ s'))
  -- the source of the transition on `S` is contained in the source of that of `X`
  have hsub : (((es.trans Cs).symm.trans (es'.trans Cs')).source : Set ℂ) ⊆
      (Cs.symm.trans Cs').source := by
    intro x hx
    rw [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage] at hx
    obtain ⟨hxA, hxB⟩ := hx
    rw [OpenPartialHomeomorph.symm_source, htarget, Set.mem_inter_iff, Set.mem_preimage] at hxA
    obtain ⟨hx1, hz⟩ := hxA
    rw [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage] at hxB
    obtain ⟨_, hs2⟩ := hxB
    rw [hsymm x, hkey_gen _ hz] at hs2
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hx1, hs2⟩
  -- and the two transition maps agree on that source
  have heq : EqOn (((es.trans Cs).symm.trans (es'.trans Cs')) : ℂ → ℂ)
      ((Cs.symm.trans Cs') : ℂ → ℂ) ((es.trans Cs).symm.trans (es'.trans Cs')).source := by
    intro x hx
    rw [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage] at hx
    obtain ⟨hxA, hxB⟩ := hx
    rw [OpenPartialHomeomorph.symm_source, htarget, Set.mem_inter_iff, Set.mem_preimage] at hxA
    obtain ⟨hx1, hz⟩ := hxA
    simp only [OpenPartialHomeomorph.trans_apply]
    rw [hsymm x, hkey_gen _ hz]
  refine StructureGroupoid.mem_of_eqOnSource (contDiffGroupoid 1 (modelWithCornersSelf ℂ ℂ))
    (closedUnderRestriction' hg
      (OpenPartialHomeomorph.open_source ((es.trans Cs).symm.trans (es'.trans Cs')))) ?_
  refine ⟨?_, ?_⟩
  · rw [OpenPartialHomeomorph.restr_source,
      (OpenPartialHomeomorph.open_source _).interior_eq]
    exact Subset.antisymm (fun x hx => ⟨hsub hx, hx⟩) Set.inter_subset_right
  · intro x hx
    exact heq hx

/-- The local homeomorphism `φ` is holomorphic for the pulled back complex structure on `S` (and
the given complex structure on `X`). -/
theorem mdifferentiable_pullChartedSpace [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {φ : S → X} (hφ : IsLocalHomeomorph φ) :
    letI := pullChartedSpace φ hφ
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) φ := by
  letI := pullChartedSpace φ hφ
  haveI hman : IsManifold (modelWithCornersSelf ℂ ℂ) 1 S := isManifold_pullChartedSpace hφ
  intro s
  let es := (hφ s).choose
  let Cs := chartAt ℂ (φ s)
  have hes : (es : S → X) = φ := (hφ s).choose_spec.2.symm
  -- the chart at `s`, as a map to `ℂ`, is differentiable
  have hA : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (chartAt ℂ s) s :=
    mdifferentiableAt_atlas (chart_mem_atlas ℂ s) (mem_chart_source ℂ s)
  -- so is the inverse of the chart of `X` at `φ s`
  have hC' : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (chartAt ℂ (φ s)).symm ((chartAt ℂ (φ s)) (φ s)) :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ (φ s)) (mem_chart_target ℂ (φ s))
  have hpt : (chartAt ℂ s) s = (chartAt ℂ (φ s)) (φ s) := by
    show (pullChart φ hφ s) s = _
    rw [pullChart, OpenPartialHomeomorph.trans_apply]
    rw [← (hφ s).choose_spec.2]
  have hC : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (chartAt ℂ (φ s)).symm ((chartAt ℂ s) s) := by
    simpa only [hpt] using hC'
  have hcomp : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      ((chartAt ℂ (φ s)).symm ∘ (chartAt ℂ s)) s := hC.comp s hA
  -- `φ` coincides with that composition near `s`
  have hs_mem : s ∈ (pullChart φ hφ s).source := mem_chart_source ℂ s
  have hev : φ =ᶠ[𝓝 s] (fun x => (chartAt ℂ (φ s)).symm ((chartAt ℂ s) x)) := by
    refine Filter.eventually_of_mem
      ((OpenPartialHomeomorph.open_source (pullChart φ hφ s)).mem_nhds hs_mem) ?_
    intro x hx
    have hx2 : es x ∈ Cs.source := hx.2
    have hcx : (chartAt ℂ s) x = Cs (es x) := by
      show (pullChart φ hφ s) x = _
      rw [pullChart, OpenPartialHomeomorph.trans_apply]
    show φ x = Cs.symm ((chartAt ℂ s) x)
    rw [hcx, OpenPartialHomeomorph.left_inv Cs hx2]
    exact (congrFun hes x).symm
  exact MDifferentiableAt.congr_of_eventuallyEq hcomp hev

/-- **Every space locally homeomorphic to a complex manifold is a complex manifold, in such a way
that the local homeomorphism is holomorphic.** -/
theorem exists_chartedSpace_of_isLocalHomeomorph {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {S : Type} [TopologicalSpace S]
    {φ : S → X} (hφ : IsLocalHomeomorph φ) :
    ∃ _ : ChartedSpace ℂ S,
      IsManifold (modelWithCornersSelf ℂ ℂ) 1 S ∧
        MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) φ := by
  letI := pullChartedSpace φ hφ
  exact ⟨pullChartedSpace φ hφ, isManifold_pullChartedSpace hφ,
    mdifferentiable_pullChartedSpace hφ⟩

end

end Work.EQ.UnivCover
