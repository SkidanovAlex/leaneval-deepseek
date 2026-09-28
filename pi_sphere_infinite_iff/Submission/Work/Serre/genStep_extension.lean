import Mathlib
import Submission.Work.Serre.CWModel.Gen

/-!
# Extending a map along the generator step

`Work.Serre.CWModel.genStep s` attaches `(n+2)`-cells to `s.Y` along the *constant* attaching maps at
the base point `s.y₀` (one cell per element of `π_{n+2}(B)`).  Consequently *every* continuous map
`h : s.Y → B'` extends over the attachment: on the old space it is `h`, and on every new cell it is
the constant map at `h s.y₀`, which glues with `h` because the attaching map is constant.

This is the "extend along the inclusion" half of the homotopy-invariance of the model tower: a map
`B → B'` transports the whole tower, and this lemma produces the compatible extension of `h`
itself (the extension is *not* the one coming from `B → B'`; it is the trivial constant extension).
-/

open scoped Topology Topology.Homotopy unitInterval
open Work.RatHurewicz

namespace Work.Serre

/-- **A map out of `s.Y` extends over the generator step attachment.**  The attaching maps of
`genStep` are the constant maps at `s.y₀`, so sending each attached cell to the constant map at
`h s.y₀` glues with `h` and produces a genuine extension of `h`. -/
theorem genStep_extension {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StA B b₀ n) {B' : Type} [TopologicalSpace B'] (h : C(s.Y, B')) :
    ∃ h' : C((Work.Serre.CWModel.genStep s).Y, B'),
      ∀ y : s.Y, h' (Work.RatHurewicz.attachIncl n s.Y
        (HomotopyGroup (Fin (n + 2)) B (s.g s.y₀))
        (fun _ => ContinuousMap.const (Work.RatHurewicz.cellSphere n) s.y₀) y) = h y := by
  classical
  -- The index type and the attaching maps of `genStep`, spelled out.
  let ι := HomotopyGroup (Fin (n + 2)) B (s.g s.y₀)
  let f : ι → C(cellSphere n, s.Y) := fun _ => ContinuousMap.const (cellSphere n) s.y₀
  -- On every cell, extend by the constant map at `h s.y₀`.
  let G : ι → C(cellDisk n, B') := fun _ => ContinuousMap.const (cellDisk n) (h s.y₀)
  have hG : ∀ (i : ι) (z : cellSphere n), G i (cellSphereToDisk n z) = h (f i z) := by
    intro i z
    simp [G, f]
  obtain ⟨h', h'1, -⟩ := attachCells_extension n s.Y ι f h G hG
  exact ⟨h', fun y => congrFun (congrArg DFunLike.coe h'1) y⟩

end Work.Serre
