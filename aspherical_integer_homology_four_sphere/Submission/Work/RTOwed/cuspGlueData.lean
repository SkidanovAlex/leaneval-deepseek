/-
# The gluing datum of the `v`-th cusp: `Work.Cusp.CuspGlueData` for the concrete chart

This file assembles the *one* missing inhabitant of the whole construction:
`Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf Work.RTOwed.glueData) v` for each of the five
cusps, from

* the chart fields of the cusp chart of `M̄` (`Work.RTOwed.mbarLow`): continuity, injectivity,
  openness of the image, the chart (open embedding) property and `mbarLow_not_Tset`, on the slabbed
  and on the unslabbed collar box — these are the theorems
  `Work.RTOwed.mbarLow_cont`, `mbarLow_inj`, `mbarLow_open`, `mbarLow_isEmbedding`,
  `mbarLow_not_Tset`, taken here as hypotheses so that the *assembly* can be checked before them;
* the ceiling map `Work.RTOwed.mbarPtC v` in the cusp coordinates of the chart, with
  `Work.RTOwed.mbarPtC_eq_field` (it *is* the chart at the ceiling) and `Work.RTOwed.mbarPtC_mem_field`
  (it lands in `Tset`);
* the gluing itself: `Work.RTOwed.glueData_apply`, the coordinate formula of the concrete gluing
  `Work.RTOwed.glueData : Work.RTInstance.GlueHomeo` built in `instGlue.lean`.

Once the five mbarLow theorems are proved, `Work.RTOwed.cuspGlueData` is the unconditional inhabitant
and `Work.Cusp.cuspChart`, `Work.Cusp.polarChart`, `Work.Cusp.coreChart` (hence items 2 and 3 of the
contract) become available for the concrete `M̄`.
-/
import Mathlib
import Submission.Work.RTOwed.instGlue
import Submission.Work.Cusp.Assembly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.RTOwed

open Work.RTInstance

/-- The chart region of the slabbed collar box, below the ceiling. -/
abbrev ChartReg (v : Fin 5) (c : Work.Cusp.E3) (δ : ℝ) : Set Work.Cusp.E4 :=
  {q | q ∈ Work.Cusp.cuspChartBox v c δ ∧ q 3 ≤ Work.Cusp.beta (Work.Cusp.xOf q)}

/-- The chart region of the unslabbed collar box, below the ceiling. -/
abbrev ChartRegTop (v : Fin 5) (c : Work.Cusp.E3) (δ : ℝ) : Set Work.Cusp.E4 :=
  {q | q ∈ Work.Cusp.cuspBoxTop v c δ ∧ q 3 ≤ Work.Cusp.beta (Work.Cusp.xOf q)}

/-- **The gluing datum of the `v`-th cusp for the concrete chart and the concrete gluing**: the
inhabitant of `Work.Cusp.CuspGlueData`, from the chart fields of `Work.RTOwed.mbarLow` (taken as
hypotheses in the shape proved by the modules `mbarLow_cont`/`_inj`/`_open`/`_isEmbedding`/`_not_Tset`)
and the coordinate formula `Work.RTOwed.glueData_apply` of the gluing. -/
noncomputable def cuspGlueDataOf (v : Fin 5)
    (hcont : ∀ (c : Work.Cusp.E3) (δ : ℝ),
      ContinuousOn (mbarLow v) (ChartReg v c δ) ∧ ContinuousOn (mbarLow v) (ChartRegTop v c δ))
    (hinj : ∀ (c : Work.Cusp.E3) (δ : ℝ), δ ≤ 1/2 →
      Set.InjOn (mbarLow v) (ChartReg v c δ) ∧ Set.InjOn (mbarLow v) (ChartRegTop v c δ))
    (hopen : ∀ (c : Work.Cusp.E3) (δ : ℝ),
      IsOpen (mbarLow v '' ChartReg v c δ) ∧ IsOpen (mbarLow v '' ChartRegTop v c δ))
    (hemb : ∀ (c : Work.Cusp.E3) (δ : ℝ), δ ≤ 1/2 →
      Topology.IsOpenEmbedding (fun q : {q : Work.Cusp.E4 // q ∈ ChartReg v c δ} => mbarLow v q) ∧
      Topology.IsOpenEmbedding (fun q : {q : Work.Cusp.E4 // q ∈ ChartRegTop v c δ} =>
        mbarLow v q))
    (hnt : ∀ (c : Work.Cusp.E3) (δ : ℝ),
      (∀ {q : Work.Cusp.E4}, q ∈ Work.Cusp.cuspChartBox v c δ → q 3 < Work.Cusp.beta (Work.Cusp.xOf q) →
        mbarLow v q ∉ Work.FoldInst.Tset) ∧
      (∀ {q : Work.Cusp.E4}, q ∈ Work.Cusp.cuspBoxTop v c δ → q 3 < Work.Cusp.beta (Work.Cusp.xOf q) →
        mbarLow v q ∉ Work.FoldInst.Tset)) :
    Work.Cusp.CuspGlueData (assemblyOf glueData) v where
  tor := Homeomorph.refl _
  mbarLow := mbarLow v
  mbarLow_cont := fun c δ => (hcont c δ).1
  mbarLow_inj := fun c δ hδ => (hinj c δ hδ).1
  mbarLow_open := fun c δ => (hopen c δ).1
  mbarLow_isEmbedding := fun c δ hδ => (hemb c δ hδ).1
  mbarLow_not_Tset := fun c δ => (hnt c δ).1
  mbarLow_contTop := fun c δ => (hcont c δ).2
  mbarLow_injTop := fun c δ hδ => (hinj c δ hδ).2
  mbarLow_openTop := fun c δ => (hopen c δ).2
  mbarLow_isEmbeddingTop := fun c δ hδ => (hemb c δ hδ).2
  mbarLow_not_TsetTop := fun c δ => (hnt c δ).2
  mbarPt := mbarPtC v
  mbarPt_eq := fun x => mbarPtC_eq_field v x
  mbarPt_mem := fun x => mbarPtC_mem_field v x
  ceiling_mem := fun c δ q hq hqs => Work.RTOwed.ceiling_mem v c δ hq hqs
  glue_eq := fun u y => by
    have h := glueData_apply v u y (mbarPtC_mem_field v (Work.Cusp.cuspX v u y))
    exact h

end Work.RTOwed
