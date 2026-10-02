import Mathlib
import Submission.Work.Serre.CWModel.Kill
import Submission.Work.StemsB.killToFgModel

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Extending a map over the cells of the killing step

`Work.Serre.CWModel.killStep` attaches, for every element `k` of the kernel of
`π_{n+2}(s.g)`, one `(n+3)`-cell along the sphere map `killFamily (n+1) s.Y s.y₀ k.1`
representing `k.1`.  If the target `B'` has trivial `π_{n+2}` at `b'`, then any based map
`h : s.Y → B'` extends over the new cells: on the cell attached along a representative of a class
`α` that dies in `B'`, the composite `h ∘ killFamily (n+1) s.Y s.y₀ α` is null-homotopic, so it
extends over the disc by `Work.Serre.CWModel.sphereExtend`, and the universal property of the cell
attachment (`Work.Serre.CWModel.attachG`) glues these extensions to the old map.

The proof is the general-index version `Work.Serre.killFamily_extend_gen` of
`Work.StemsB.killFamily_extend` (there the index type is the *whole* homotopy group; here it is an
arbitrary index set with a prescribed family of classes), specialised to the kernel of
`π_{n+2}(s.g)`.
-/

open scoped Topology Topology.Homotopy unitInterval
open Work.RatHurewicz

namespace Work.Serre

noncomputable section

/-- **Extension over a prescribed family of killing cells.**  If `π_{m+1}` of the target `Z` at
`g y₀` is trivial, then `g` extends over the space obtained from `Y` by attaching, for `i : ι`, a
`(m+2)`-cell along the sphere map `Work.RatHurewicz.killFamily m Y y₀ (sv i)` representing the
class `sv i`.

This is `Work.StemsB.killFamily_extend` with the index type `HomotopyGroup (Fin (m+1)) Y y₀`
replaced by an arbitrary type `ι` carrying a family `sv` of classes (the proof never uses that `sv`
is surjective: for a class lying in the kernel of `π_{m+1}(g)` the composite attaching map is
null-homotopic). -/
theorem killFamily_extend_gen (m : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y)
    (Z : Type) [TopologicalSpace Z] (g : C(Y, Z))
    (h : Subsingleton (HomotopyGroup (Fin (m + 1)) Z (g y₀)))
    (ι : Type) (sv : ι → HomotopyGroup (Fin (m + 1)) Y y₀) :
    ∃ (g' : C(Work.RatHurewicz.attachCells m Y ι
        (fun i => Work.RatHurewicz.killFamily m Y y₀ (sv i)), Z)),
      g'.comp (Work.RatHurewicz.attachIncl m Y ι
        (fun i => Work.RatHurewicz.killFamily m Y y₀ (sv i))) = g := by
  classical
  have hnull : ∀ i : ι, (g.comp (Work.RatHurewicz.killFamily m Y y₀ (sv i))).Homotopic
      (ContinuousMap.const (Work.RatHurewicz.cellSphere m) (g y₀)) := by
    intro i
    have hker : Work.Serre.piMapN g (m + 1) y₀ (sv i) = 1 := Subsingleton.elim _ _
    have hn : 1 ≤ m + 1 := by omega
    have hcube : GenLoop.Homotopic (Work.StemsB.genLoopMap g (m + 1) (Quotient.out (sv i)))
        (GenLoop.const (N := Fin (m + 1)) (X := Z) (x := g y₀)) := by
      have h1 : (Quotient.mk _ (Work.StemsB.genLoopMap g (m + 1) (Quotient.out (sv i))) :
            HomotopyGroup (Fin (m + 1)) Z (g y₀))
          = Quotient.mk (GenLoop.Homotopic.setoid (Fin (m + 1)) (g y₀))
              (GenLoop.const (N := Fin (m + 1)) (X := Z) (x := g y₀)) := by
        rw [← Work.Serre.piMapN_apply_mk, Quotient.out_eq (sv i), hker]
        exact HomotopyGroup.one_def (N := Fin (m + 1)) (X := Z) (x := g y₀)
      exact Quotient.exact h1
    have h2 := Work.Serre.CWModel.cubeLift_homotopic hn hcube
    rw [Work.RatHurewicz.cubeLift_genLoopMap, Work.Serre.CWModel.cubeLift_const] at h2
    exact h2
  let G : (i : ι) → C(Work.RatHurewicz.cellDisk m, Z) := fun i =>
    Classical.choose (Work.Serre.CWModel.sphereExtend
      (g.comp (Work.RatHurewicz.killFamily m Y y₀ (sv i)))
      (hnull i).some.toContinuousMap (g y₀) (hnull i).some.map_zero_left
      (hnull i).some.map_one_left)
  have hG : ∀ (i : ι) (z : Work.RatHurewicz.cellSphere m),
      G i (Work.RatHurewicz.cellSphereToDisk m z) =
        g (Work.RatHurewicz.killFamily m Y y₀ (sv i) z) := by
    intro i z
    have hspec := Classical.choose_spec (Work.Serre.CWModel.sphereExtend
      (g.comp (Work.RatHurewicz.killFamily m Y y₀ (sv i)))
      (hnull i).some.toContinuousMap (g y₀) (hnull i).some.map_zero_left
      (hnull i).some.map_one_left)
    exact congrFun (congrArg DFunLike.coe hspec) z
  refine ⟨Work.Serre.CWModel.attachG m Y ι
    (fun i => Work.RatHurewicz.killFamily m Y y₀ (sv i)) g G hG, ?_⟩
  ext y
  exact Work.Serre.CWModel.attachG_incl m Y ι
    (fun i => Work.RatHurewicz.killFamily m Y y₀ (sv i)) g G hG y

theorem killStepExtension {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StG B b₀ n) {B' : Type} [TopologicalSpace B'] (b' : B')
    (h : C(s.Y, B')) (hb' : h s.y₀ = b')
    (hsub : Subsingleton (HomotopyGroup (Fin (n + 2)) B' b')) :
    ∃ h' : C((Work.Serre.CWModel.killStep s).Y, B'),
      ∀ y : s.Y, h' (Work.RatHurewicz.attachIncl (n + 1) s.Y
        {α : HomotopyGroup (Fin (n + 2)) s.Y s.y₀ //
          Work.Serre.piMapN s.g (n + 2) s.y₀ α = 1}
        (fun k => Work.RatHurewicz.killFamily (n + 1) s.Y s.y₀ k.1) y) = h y := by
  classical
  have hsub' : Subsingleton (HomotopyGroup (Fin (n + 1 + 1)) B' (h s.y₀)) := hb'.symm ▸ hsub
  obtain ⟨h', hh'⟩ := killFamily_extend_gen (n + 1) s.Y s.y₀ B' h hsub'
    {α : HomotopyGroup (Fin (n + 2)) s.Y s.y₀ //
      Work.Serre.piMapN s.g (n + 2) s.y₀ α = 1}
    (fun k => k.1)
  exact ⟨h', fun y => congrFun (congrArg DFunLike.coe hh') y⟩

end

end Work.Serre
