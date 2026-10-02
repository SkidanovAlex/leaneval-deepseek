import Mathlib
import Submission.Work.Serre.SPC.B1Propagate
import Submission.Work.Serre.SPC.B1Skeleton
import Submission.Work.Serre.SPC.piOne_killStep
import Submission.Work.Serre.SPC.skeleton_pathConnected
import Submission.Work.Serre.SPC.attachFibreData
import Submission.Work.Serre.Assembly.pullbackFst_serre

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The base stage (`StA B b₀ 0`) of the `b = 1` model

From the `1`-skeleton `Work.Serre.SPC.Skeleton B b₀` (with its structure map
`Work.Serre.SPC.skeletonMap B b₀`, on which `π₁` is surjective and `GoodN` holds) we attach `2`-cells
along `Work.RatHurewicz.killFamily 0` over the kernel of `π₁ (skeletonMap)`, extending the structure
map by null-homotopies.  The result is a stage of the model with `π₁` *bijective* and `GoodN` still
holding.  This is the input of the cellular tower (`Work.Serre.CWModel.genStep`/`killStep`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.SPC

noncomputable section

/-- The index type of the `2`-cells killing the kernel of `π₁` of the skeleton map. -/
def KillIdx (B : Type) [TopologicalSpace B] (b₀ : B) : Type :=
  {α : HomotopyGroup (Fin 1) (Skeleton B b₀) (skeletonBase B b₀) //
    Work.Serre.piMapN (skeletonMap B b₀) 1 (skeletonBase B b₀) α = 1}

/-- Their attaching maps. -/
def killFam (B : Type) [TopologicalSpace B] (b₀ : B) :
    KillIdx B b₀ → C(Work.RatHurewicz.cellSphere 0, Skeleton B b₀) :=
  fun k => Work.RatHurewicz.killFamily 0 (Skeleton B b₀) (skeletonBase B b₀) k.1

/-- **The base stage of the `b = 1` model.** -/
theorem stage0 {B : Type} [TopologicalSpace B] (b₀ : B) {E : Type} [TopologicalSpace E]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (e₀ : E) (he₀ : p e₀ = b₀) (f : ℕ)
    (hfib0 : Subsingleton (HomotopyGroup (Fin 0) (Work.StemsB.fibre p b₀) ⟨e₀, he₀⟩))
    (hfib : ∀ j : ℕ, 0 < j → j < f → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p b₀))).homology j))
    (hcell : CellStepHyp) (htr : FibreTransport)
    (hprop : Propagate b₀ p (1 + f))
    (hskel : GoodN b₀ p (1 + f) (skeletonBase B b₀) (skeletonMap B b₀)) :
    ∃ s : Work.Serre.CWModel.StA B b₀ 0, GoodN b₀ p (1 + f) s.y₀ s.g := by
  haveI hpc : PathConnectedSpace (Skeleton B b₀) := skeleton_pathConnected B b₀
  obtain ⟨G, hG, hbij⟩ := piOne_killStep b₀ (skeletonBase B b₀) (skeletonMap B b₀) rfl
    (skeletonMap_piOne_surjective B b₀)
  set g₂ : C(Work.RatHurewicz.attachCells 0 (Skeleton B b₀) (KillIdx B b₀) (killFam B b₀), B) :=
    Work.Serre.CWModel.attachG 0 (Skeleton B b₀) (KillIdx B b₀) (killFam B b₀)
      (skeletonMap B b₀) G hG with hg₂
  set γ₂ : Work.RatHurewicz.attachCells 0 (Skeleton B b₀) (KillIdx B b₀) (killFam B b₀) :=
    Work.RatHurewicz.attachIncl 0 (Skeleton B b₀) (KillIdx B b₀) (killFam B b₀)
      (skeletonBase B b₀) with hγ₂
  haveI hconn₂ : PathConnectedSpace
      (Work.RatHurewicz.attachCells 0 (Skeleton B b₀) (KillIdx B b₀) (killFam B b₀)) :=
    Work.Serre.CWModel.pathConnectedSpace_attachCells 0 (Skeleton B b₀) (KillIdx B b₀) (killFam B b₀)
  have hbase₂ : g₂ γ₂ = b₀ := rfl
  -- the connectivity data of the pullback fibration over the whole new base
  have hdata := attachFibreData p hp b₀ e₀ he₀ f htr hfib hfib0 γ₂ g₂ hbase₂
  -- the cell step, from the (strengthened) hypothesis
  have hstep : ∀ i : ℕ, i < (1 + f) + 1 → CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.cellStepAttachMap 2 (Skeleton B b₀) (KillIdx B b₀) (killFam B b₀)
        (Work.StemsB.Pullback g₂ p) (Work.StemsB.pullbackFst g₂ p)) i) := by
    intro i hi
    exact (hcell 2 (by norm_num) (Skeleton B b₀) (KillIdx B b₀) (killFam B b₀)
      (Work.StemsB.Pullback g₂ p)
      (Work.StemsB.pullbackFst g₂ p)
      (fun n => Work.Serre.Assembly.hasHLP_pullbackFst g₂ p (hp n)) f hdata.1 hdata.2).1 i
      (by omega)
  have hgood₂ : GoodN b₀ p (1 + f) γ₂ g₂ :=
    hprop (skeletonBase B b₀) (skeletonMap B b₀) hskel (D := 2) (by norm_num)
      (KillIdx B b₀) (killFam B b₀) G hG hstep
  refine ⟨{ Y := Work.RatHurewicz.attachCells 0 (Skeleton B b₀) (KillIdx B b₀) (killFam B b₀)
            inst := inferInstance
            y₀ := γ₂
            g := g₂
            gbase := hbase₂
            conn := hconn₂
            bij := ?_ }, hgood₂⟩
  intro j hj
  have hj0 : j = 0 := by omega
  subst hj0
  exact hbij

end

end Work.Serre.SPC
