import Mathlib
import Submission.Work.EMFG.sphereMap_homotopy
import Submission.Work.Serre.CWModel.Gen
import Submission.Work.Serre.CWModel.sphereExtend

open scoped Topology

namespace Work.EMFG

noncomputable section

/-!
# Extension of maps over the "kill everything" attachment

`Work.Serre.KillCells m Y` is `Y` with an `(m+2)`-cell attached along *every* continuous map
`S^{m+1} → Y` (`Work.Serre.KillIdx m Y = C(cellSphere m, Y)`, `cellSphere m = S^{m+1}`), and
`Work.Serre.killIncl m Y : Y → KillCells m Y` is the inclusion of the old space.

The lemma below is the universal property of that attachment in the only case needed for the
Postnikov tower of the Serre finiteness theorem: **any** map `φ : Y → Z` whose target has vanishing
`π_{m+1}` extends over `KillCells m Y`.

The construction is the one-step Postnikov argument:

* for an attaching map `g : S^{m+1} → Y`, the composite `φ ∘ g : S^{m+1} → Z` has trivial class at
  every base point (hypothesis `hZ`), hence is *freely* null-homotopic
  (`Work.EMFG.sphereMap_homotopic_const_of_subsingleton`, the cube ↔ sphere dictionary);
* a freely null-homotopic map of the model sphere extends over the model cell
  (`Work.Serre.CWModel.sphereExtend`, the cone construction), producing `G g : D^{m+2} → Z`
  restricting to `φ ∘ g` on the boundary;
* the universal property of the attachment
  (`Work.RatHurewicz.attachCells_extension`) glues these into `φ' : KillCells m Y → Z`.

Note that the "based" hypothesis `hZ` is enough, and it is needed at the *image* points
`φ (g z) ∈ Z` only; quantifying over all `z : Z` (as the statement does) keeps the lemma
independent of the index set of attaching maps.
-/

/-- **Extension over the "kill everything" attachment.**  A map `φ : Y → Z` into a space `Z` with
`π_{m+1}(Z) = 0` (at every base point) factors through the inclusion
`killIncl m Y : Y → KillCells m Y`. -/
theorem killCellsExtend (m : ℕ) {Y : Type} [TopologicalSpace Y] {Z : Type} [TopologicalSpace Z]
    (φ : C(Y, Z)) (hZ : ∀ z : Z, Subsingleton (HomotopyGroup (Fin (m + 1)) Z z)) :
    ∃ φ' : C(Work.Serre.KillCells m Y, Z), φ'.comp (Work.Serre.killIncl m Y) = φ := by
  classical
  have hk : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
  -- each attaching map becomes null-homotopic after composition with `φ`, hence extends over the cell
  have hex : ∀ g : Work.Serre.KillIdx m Y,
      ∃ G : C(Work.RatHurewicz.cellDisk m, Z),
        G.comp (Work.RatHurewicz.cellSphereToDisk m) = φ.comp g := by
    intro g
    have hnull := Work.EMFG.sphereMap_homotopic_const_of_subsingleton (m + 1) hk (φ.comp g)
      (hZ ((φ.comp g) (Work.Stems.collapseMap (m + 1) hk 0)))
    exact Work.Serre.CWModel.sphereExtend (φ.comp g) hnull.some.toContinuousMap
      ((φ.comp g) (Work.Stems.collapseMap (m + 1) hk 0))
      hnull.some.map_zero_left hnull.some.map_one_left
  -- the chosen extensions agree with `φ` on the boundary of every cell
  let G : Work.Serre.KillIdx m Y → C(Work.RatHurewicz.cellDisk m, Z) := fun g => Classical.choose (hex g)
  have hG : ∀ (g : Work.Serre.KillIdx m Y) (z : Work.RatHurewicz.cellSphere m),
      G g (Work.RatHurewicz.cellSphereToDisk m z) = φ (g z) := by
    intro g z
    exact congrFun (congrArg DFunLike.coe (Classical.choose_spec (hex g))) z
  obtain ⟨φ', hφ', _⟩ := Work.RatHurewicz.attachCells_extension m Y (Work.Serre.KillIdx m Y)
    (fun g => g) φ G hG
  exact ⟨φ', hφ'⟩

end

end Work.EMFG
