import Mathlib
import Submission.Work.Serre.ZeroCase.cellStepHyp
import Submission.Work.Serre.ZeroCase.Propagate
import Submission.Work.Serre.ZeroCase.TowerGood
import Submission.Work.Serre.SPC.B1Stage0
import Submission.Work.Serre.SPC.B1Skeleton
import Submission.Work.Serre.SPC.B1Tower
import Submission.Work.Serre.SPC.fibreTransport
import Submission.Work.Serre.SPC.skeleton_Good
import Submission.Work.Serre.SPC.oneCellStepX
import Submission.Work.Serre.SPC.skeleton_pathConnected

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `b = 1` case of the Serre pair comparison

For a Serre fibration `p : E → B` over a *path connected* base `B` and a fibre which is
`(f-1)`-connected with `1 ≤ f`, the pair comparison `(E, p⁻¹b₀) → (B, {b₀})` is an isomorphism on
integral homology in degrees `< 1 + f` (and an epimorphism in degree `1 + f`), provided the model
of the base is a CW complex built from `1`-cells:

* the base stage is the `1`-skeleton of `B` (a wedge of one circle per based loop), on which `π₁`
  is surjective (`Work.Serre.SPC.skeletonMap_piOne_surjective`), with the `GoodN` invariant
  transferred across the `1`-cell attachments by the proved `Work.Serre.SPC.oneCellStepX`
  (`Work.Serre.SPC.skeleton_Good`);
* one `2`-cell per element of the kernel of `π₁` kills `π₁`
  (`Work.Serre.SPC.stage0`, which uses the cell-attachment propagation
  `Work.Serre.ZeroCase.propagate`);
* then the tower `Work.Serre.SPC.towerB` of `Work.Serre.CWModel.genStep`/`killStep` makes
  `π`-bijective up to any degree, and the invariant is propagated along it by
  `Work.Serre.SPC.towerGoodN` (the `b = 1` cell-attachment step `Work.Serre.SPC.attachGoodOneN`).

This is the assembly `Work.Serre.SPC.b1Comparison_of` (`Submission/Work/Serre/SPC/B1Assembly.lean`)
with the propagation across an arbitrary subspace inclusion (`Work.Serre.SPC.Propagate2`) replaced
by the `b = 1` cell-attachment step, which is available in proved form.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.ZeroCase

/-- **The `b = 1` model of the Serre pair comparison.** -/
theorem b1Comparison {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B) (e₀ : E) (he₀ : p e₀ = b₀)
    (f N : ℕ) (hf : 1 ≤ f) (hB : PathConnectedSpace B)
    (hfib0 : Subsingleton (HomotopyGroup (Fin 0) (Work.StemsB.fibre p b₀) ⟨e₀, he₀⟩))
    (hfib : ∀ j : ℕ, 0 < j → j < f → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p b₀))).homology j)) :
    ∃ (Γ : Type) (_ : TopologicalSpace Γ) (γ₀ : Γ) (g : C(Γ, B)),
      g γ₀ = b₀ ∧ PathConnectedSpace Γ ∧
      (∀ i : ℕ, i ≤ N → ∀ x : Γ, Function.Bijective (Work.Serre.piMapN g i x)) ∧
      (∀ i : ℕ, i < 1 + f → CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.StemsB.relPairMap (Work.StemsB.pullbackFst g p) γ₀) i)) ∧
      Function.Surjective (HomologicalComplex.homologyMap
        (Work.StemsB.relPairMap (Work.StemsB.pullbackFst g p) γ₀) (1 + f)).hom := by
  haveI : PathConnectedSpace (Work.Serre.SPC.Skeleton B b₀) :=
    Work.Serre.SPC.skeleton_pathConnected B b₀
  obtain ⟨s₀, h₀⟩ := Work.Serre.SPC.stage0 b₀ p hp e₀ he₀ f hfib0 hfib
    Work.Serre.ZeroCase.cellStepHyp Work.Serre.SPC.fibreTransport
    (Work.Serre.SPC.propagate b₀ p (1 + f))
    (Work.Serre.SPC.skeleton_Good Work.Serre.SPC.oneCellStepX b₀ p hp e₀ he₀ f hfib0 hfib
      Work.Serre.SPC.fibreTransport)
  refine ⟨(Work.Serre.SPC.towerB b₀ s₀ (N + 1)).Y, (Work.Serre.SPC.towerB b₀ s₀ (N + 1)).inst,
    (Work.Serre.SPC.towerB b₀ s₀ (N + 1)).y₀, (Work.Serre.SPC.towerB b₀ s₀ (N + 1)).g,
    (Work.Serre.SPC.towerB b₀ s₀ (N + 1)).gbase, (Work.Serre.SPC.towerB b₀ s₀ (N + 1)).conn,
    Work.Serre.SPC.towerB_piMapN_bijective b₀ s₀ N, ?_, ?_⟩
  · exact (Work.Serre.SPC.towerGoodN b₀ p hp e₀ he₀ f hf hfib0 hfib
      Work.Serre.ZeroCase.cellStepHyp Work.Serre.SPC.fibreTransport s₀ h₀ (N + 1)).1
  · exact (Work.Serre.SPC.towerGoodN b₀ p hp e₀ he₀ f hf hfib0 hfib
      Work.Serre.ZeroCase.cellStepHyp Work.Serre.SPC.fibreTransport s₀ h₀ (N + 1)).2

end Work.Serre.ZeroCase
