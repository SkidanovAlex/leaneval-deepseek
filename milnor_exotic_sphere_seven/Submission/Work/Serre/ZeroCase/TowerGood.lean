import Mathlib
import Submission.Work.Serre.SPC.attachGood
import Submission.Work.Serre.SPC.B1Tower
import Submission.Work.Serre.SPC.B1Setup
import Submission.Work.Serre.SPC.Setup
import Submission.Work.RatHurewicz.AttachCells

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `b = 1` cellular tower, with the cell step from `attachGood`

`Work.Serre.SPC.attachGood` proves the cell-attachment step of the tower induction for the
`GoodMap` invariant `GoodMap p b f g γ₀` (the comparison map of the pullback of `p` along `g` is an
isomorphism in degrees `< b + f` and an epimorphism in degree `b + f`), but only under the
hypothesis `2 ≤ b`.  For the case `b = 1` of the Serre pair comparison the invariant needed is
`GoodN b₀ p (1 + f) γ₀ g`, which is the *same* condition with `b = 1` (the two definitions agree
definitionally, `Work.Serre.SPC.stagePairMap_eq_relPairMap`).

This file re-proves the cell-attachment step with `b` *hard-wired* to `1`
(`Work.Serre.SPC.attachGoodOne`), which requires only `1 ≤ f` (used to get `2 ≤ 1 + f` for the five
lemma `Work.Serre.SPC.tauTwoRange`), and then runs the tower induction of
`Work.Serre.CWModel.towerB` with it (`Work.Serre.SPC.towerGoodN`).  This bypasses
`Work.Serre.SPC.Propagate2`, whose proof for an *arbitrary* subspace inclusion is a separate (and
expensive) piece of work.

The proof of `attachGoodOne` is the proof of `attachGood` with `b := 1`, `b + f := 1 + f`, and the
hypotheses `2 ≤ b` / `b ≤ n + 2` replaced by `1 ≤ f` (the latter being automatic).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

namespace Work.Serre.SPC

noncomputable section

variable {E B Γ : Type} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Γ]

/-- **The cell-attachment step of the `b = 1` tower induction.**  This is
`Work.Serre.SPC.attachGood` with the parameter `b` specialised to `1`: the only use of `2 ≤ b` in
its proof is the inequality `2 ≤ b + f` needed by the five lemma
`Work.Serre.SPC.tauTwoRange`, and with `b = 1` that is `2 ≤ 1 + f`, which follows from `1 ≤ f`. -/
theorem attachGoodOne
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B) (e₀ : E) (he₀ : p e₀ = b₀)
    (f : ℕ) (hf : 1 ≤ f) (hcell : CellStepHyp) (htr : FibreTransport)
    (hfib : ∀ j : ℕ, 0 < j → j < f → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p b₀))).homology j))
    (hfib0 : Subsingleton (HomotopyGroup (Fin 0) (Work.StemsB.fibre p b₀) ⟨e₀, he₀⟩))
    (g : C(Γ, B)) (γ₀ : Γ) (gbase : g γ₀ = b₀) [PathConnectedSpace Γ]
    (n : ℕ) (ι : Type) (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B))
    (hg' : ∀ x : Γ, g' (Work.RatHurewicz.attachIncl n Γ ι fr x) = g x)
    (hgood : GoodMap p 1 f g γ₀) :
    GoodMap p 1 f g' (Work.RatHurewicz.attachIncl n Γ ι fr γ₀) := by
  classical
  haveI hpc : PathConnectedSpace (Work.RatHurewicz.attachCells n Γ ι fr) :=
    Work.Serre.CWModel.pathConnectedSpace_attachCells n Γ ι fr
  have hserre := Work.Serre.Assembly.pullbackFst_serre g' p hp
  obtain ⟨hfiber, h0⟩ := attachFibreData p hp b₀ e₀ he₀ f htr hfib hfib0
    (Work.RatHurewicz.attachIncl n Γ ι fr γ₀) g' ((hg' γ₀).trans gbase)
  have hcs := hcell (n + 2) (by omega) Γ ι fr (Work.StemsB.Pullback g' p)
    (Work.StemsB.pullbackFst g' p) hserre f hfiber h0
  have hτeq : tauOneMap p n ι fr g' γ₀
      = (sourceIso p g n ι fr g' hg' γ₀).inv ≫ Work.Serre.CWModel.stagePairMap g p γ₀
        ≫ (targetIso p g n ι fr g' hg' γ₀).hom := by
    rw [← sq1 p g n ι fr g' hg' γ₀, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have h₁ : ∀ i : ℕ, i < 1 + f → CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (tauOneMap p n ι fr g' γ₀) i) := by
    intro i hi
    rw [hτeq, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
    haveI := hgood.1 i hi
    infer_instance
  have h₁N : Epi (HomologicalComplex.homologyMap (tauOneMap p n ι fr g' γ₀) (1 + f)) := by
    rw [hτeq, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
    haveI := hgood.2
    infer_instance
  have h₃ : ∀ i : ℕ, i < 1 + f → CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Serre.cellStepAttachMap (n + 2) Γ ι fr
        (Work.StemsB.Pullback g' p) (Work.StemsB.pullbackFst g' p)) i) :=
    fun i hi => hcs.1 i (by omega)
  have h₃N : Epi (HomologicalComplex.homologyMap (Work.Serre.cellStepAttachMap (n + 2) Γ ι fr
      (Work.StemsB.Pullback g' p) (Work.StemsB.pullbackFst g' p)) (1 + f)) := by
    rcases lt_or_eq_of_le (show 1 + f ≤ (n + 2) + f by omega) with h | h
    · haveI := hcs.1 (1 + f) h
      infer_instance
    · rw [h]
      exact (ModuleCat.epi_iff_surjective _).mpr (by simpa using hcs.2)
  have hkey := tauTwoRange (stageMorphism p g n ι fr g' hg' γ₀)
    (Work.Cohomology.relChains_triple_shortExact _ _ _ _)
    (Work.Cohomology.relChains_triple_shortExact _ _ _ _)
    (1 + f) (by omega) h₁ h₃ h₁N h₃N
  exact ⟨hkey.1, hkey.2⟩

/-- **The `GoodN` form of the `b = 1` cell-attachment step.**  Since
`Work.Serre.SPC.stagePairMap_eq_relPairMap` is `rfl`, `GoodMap p 1 f g γ₀` and
`GoodN b₀ p (1 + f) γ₀ g` are the same proposition up to `Epi ↔ Function.Surjective`. -/
theorem attachGoodOneN
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B) (e₀ : E) (he₀ : p e₀ = b₀)
    (f : ℕ) (hf : 1 ≤ f) (hcell : CellStepHyp) (htr : FibreTransport)
    (hfib : ∀ j : ℕ, 0 < j → j < f → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p b₀))).homology j))
    (hfib0 : Subsingleton (HomotopyGroup (Fin 0) (Work.StemsB.fibre p b₀) ⟨e₀, he₀⟩))
    (g : C(Γ, B)) (γ₀ : Γ) (gbase : g γ₀ = b₀) [PathConnectedSpace Γ]
    (n : ℕ) (ι : Type) (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B))
    (hg' : ∀ x : Γ, g' (Work.RatHurewicz.attachIncl n Γ ι fr x) = g x)
    (hgood : GoodN b₀ p (1 + f) γ₀ g) :
    GoodN b₀ p (1 + f) (Work.RatHurewicz.attachIncl n Γ ι fr γ₀) g' := by
  have hm : GoodMap p 1 f g γ₀ :=
    ⟨hgood.1, (ModuleCat.epi_iff_surjective _).mpr hgood.2⟩
  obtain ⟨h1, h2⟩ := attachGoodOne p hp b₀ e₀ he₀ f hf hcell htr hfib hfib0 g γ₀ gbase
    n ι fr g' hg' hm
  exact ⟨h1, (ModuleCat.epi_iff_surjective _).mp h2⟩

open Work.Serre.CWModel

/-- **The `b = 1` cellular tower.**  `GoodN` propagates along the tower
`Work.Serre.CWModel.towerB` starting from a stage with `π₁` bijective.  Every attachment of that
tower is a genuine cell attachment (`genStep` then `killStep`), so the cell step is available
through `Work.Serre.SPC.attachGoodOneN`; no `Propagate2` is needed. -/
theorem towerGoodN {B : Type} [TopologicalSpace B] (b₀ : B) {E : Type} [TopologicalSpace E]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (e₀ : E) (he₀ : p e₀ = b₀) (f : ℕ)
    (hf : 1 ≤ f)
    (hfib0 : Subsingleton (HomotopyGroup (Fin 0) (Work.StemsB.fibre p b₀) ⟨e₀, he₀⟩))
    (hfib : ∀ j : ℕ, 0 < j → j < f → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p b₀))).homology j))
    (hcell : CellStepHyp) (htr : FibreTransport)
    (s₀ : Work.Serre.CWModel.StA B b₀ 0) (h₀ : GoodN b₀ p (1 + f) s₀.y₀ s₀.g) (k : ℕ) :
    GoodN b₀ p (1 + f) (towerB b₀ s₀ k).y₀ (towerB b₀ s₀ k).g := by
  induction k with
  | zero => exact h₀
  | succ k ih =>
    haveI hpc : PathConnectedSpace (towerB b₀ s₀ k).Y := (towerB b₀ s₀ k).conn
    -- the generator step
    have hgoodG : GoodN b₀ p (1 + f) (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).y₀
        (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).g :=
      attachGoodOneN p hp b₀ e₀ he₀ f hf hcell htr hfib hfib0
        (towerB b₀ s₀ k).g (towerB b₀ s₀ k).y₀ (towerB b₀ s₀ k).gbase
        k (HomotopyGroup (Fin (k + 2)) B ((towerB b₀ s₀ k).g (towerB b₀ s₀ k).y₀))
        (fun _ => ContinuousMap.const (Work.RatHurewicz.cellSphere k) (towerB b₀ s₀ k).y₀)
        (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).g (fun x => rfl) ih
    -- the killing step
    haveI hpcG : PathConnectedSpace (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).Y :=
      (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).conn
    have hgoodK : GoodN b₀ p (1 + f)
        (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep (towerB b₀ s₀ k))).y₀
        (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep (towerB b₀ s₀ k))).g :=
      attachGoodOneN p hp b₀ e₀ he₀ f hf hcell htr hfib hfib0
        (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).g
        (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).y₀
        (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).gbase
        (k + 1)
        {α : HomotopyGroup (Fin (k + 2)) (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).Y
            (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).y₀ //
          Work.Serre.piMapN (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).g (k + 2)
            (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).y₀ α = 1}
        (fun α => Work.RatHurewicz.killFamily (k + 1)
          (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).Y
          (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)).y₀ α.1)
        (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep (towerB b₀ s₀ k))).g
        (fun x => rfl) hgoodG
    have : towerB b₀ s₀ (k + 1)
        = Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep (towerB b₀ s₀ k)) := rfl
    rw [this]
    exact hgoodK

end

end Work.Serre.SPC
