import Mathlib
import Submission.Work.Serre.SPC.B1Setup
import Submission.Work.Serre.SPC.B1Skeleton
import Submission.Work.Serre.SPC.FibreData
import Submission.Work.Serre.CWModel.Tower

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The propagation of `Work.Serre.SPC.GoodN` across a cell attachment, as a `Prop`

`Work.Serre.SPC.Propagate b₀ p r` is the statement proved (for `r = 1 + f`) by the delegated lemma
`Work.Serre.SPC.goodN_attachCells`: an attachment of cells of dimension `D ≥ 2` whose cell step is
an isomorphism in degrees `≤ r` preserves `GoodN` at level `r`.  Keeping it as a hypothesis lets the
`b = 1` construction be assembled before that lemma is available.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.SPC

noncomputable section

/-- **The comparison map of a pair of spaces over `B` `Γ ⊆ Γ'`**: the map of relative chain
complexes `(Γ' ×_B E, (Γ' ×_B E)|_Γ) → (Γ', Γ)` induced by the first projection of the pullback.
Its relative part is `Set.range incl`, the old part of the base. -/
def pairStepMap {B : Type} [TopologicalSpace B] {E : Type} [TopologicalSpace E]
    {Γ : Type} [TopologicalSpace Γ] {Γ' : Type} [TopologicalSpace Γ']
    (p : C(E, B)) (incl : C(Γ, Γ')) (g' : C(Γ', B)) (g : C(Γ, B))
    (hrel : ∀ x, g' (incl x) = g x) :
    Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback g' p))
        ((Work.StemsB.pullbackFst g' p) ⁻¹' (Set.range incl)) ⟶
      Work.Cohomology.relChains (TopCat.of Γ') (Set.range incl) :=
  Work.Cohomology.relChainsMapOf (TopCat.of (Work.StemsB.Pullback g' p)) (TopCat.of Γ')
    ((Work.StemsB.pullbackFst g' p) ⁻¹' (Set.range incl)) (Set.range incl)
    (TopCat.ofHom (Work.StemsB.pullbackFst g' p))
    (TopCat.ofHom ⟨fun x => ⟨Work.StemsB.pullbackFst g' p x.1, x.2⟩,
      Continuous.subtype_mk
        ((Work.StemsB.pullbackFst g' p).continuous.comp continuous_subtype_val)
        (fun x => x.2)⟩)
    (by ext x; rfl)

/-- **The propagation of `GoodN` across a subspace inclusion `Γ ⊆ Γ'` whose relative part is a cell
attachment**: if the comparison map `Work.Serre.SPC.pairStepMap p incl g' g hrel` is an isomorphism
in degrees `≤ r`, then `GoodN` transfers from `g` to `g'`.  This is the form used along the
cellular tower `Work.Serre.SPC.towerB`, where the attaching data of
`Work.Serre.CWModel.genStep`/`killStep` is not accessible by name.

The hypothesis `Topology.IsEmbedding incl` is necessary: without it (e.g. for a surjective but
non-injective `incl`) the relative part `Set.range incl` carries no information about `Γ` and the
statement is false. -/
def Propagate2 {B : Type} [TopologicalSpace B] (b₀ : B) {E : Type} [TopologicalSpace E]
    (p : C(E, B)) (r : ℕ) : Prop :=
  ∀ {Γ : Type} [TopologicalSpace Γ] (γ₀ : Γ) (g : C(Γ, B)), GoodN b₀ p r γ₀ g →
    ∀ {Γ' : Type} [TopologicalSpace Γ'] [PathConnectedSpace Γ'] (incl : C(Γ, Γ'))
      (hincl : Topology.IsEmbedding incl) (g' : C(Γ', B)) (hrel : ∀ x, g' (incl x) = g x),
      (∀ i : ℕ, i < r + 1 → CategoryTheory.IsIso
        (HomologicalComplex.homologyMap (pairStepMap p incl g' g hrel) i)) →
      GoodN b₀ p r (incl γ₀) g' 


/-- **The propagation of `GoodN` across a cell attachment of dimension `D ≥ 2`.** -/
def Propagate {B : Type} [TopologicalSpace B] (b₀ : B) {E : Type} [TopologicalSpace E]
    (p : C(E, B)) (r : ℕ) : Prop :=
  ∀ {Γ : Type} [TopologicalSpace Γ] (γ₀ : Γ) (g : C(Γ, B)), GoodN b₀ p r γ₀ g →
    ∀ {D : ℕ} (hD : 2 ≤ D) (ι : Type)
      (fr : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
      (G : ι → C(Work.RatHurewicz.cellDisk (D - 2), B))
      (hG : ∀ (i : ι) (z : Work.RatHurewicz.cellSphere (D - 2)),
        G i (Work.RatHurewicz.cellSphereToDisk (D - 2) z) = g (fr i z)),
      (∀ i : ℕ, i < r + 1 → CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.Serre.cellStepAttachMap D Γ ι fr
          (Work.StemsB.Pullback (Work.Serre.CWModel.attachG (D - 2) Γ ι fr g G hG) p)
          (Work.StemsB.pullbackFst (Work.Serre.CWModel.attachG (D - 2) Γ ι fr g G hG) p)) i)) →
      GoodN b₀ p r (Work.RatHurewicz.attachIncl (D - 2) Γ ι fr γ₀)
        (Work.Serre.CWModel.attachG (D - 2) Γ ι fr g G hG)

end

end Work.Serre.SPC
