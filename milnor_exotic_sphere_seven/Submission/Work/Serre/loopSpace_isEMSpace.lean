import Mathlib
import Submission.Work.Serre.Models
import Submission.Work.Stems.homotopyGroup_loop

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The loop space of a `K(A,n+1)` is a `K(A,n)`

`Work.Serre.IsEMSpace A m hm X pt` says that `X` is a model of the Eilenberg–MacLane space
`K(A,m)`: `π_m(X,pt) ≃* A` and `π_i(X,pt) = 0` for `i ≠ m`.

The loop space `Ω Y = Path qt qt` of a model of `K(A,n+1)` is a model of `K(A,n)`, because the
currying homeomorphism of cubes `I^{n+1} ≅ I^n × I` induces the loop-space shift
`π_{n+1}(Y,qt) ≃* π_n(ΩY, refl)` (the geometric input of the path–loop fibration).  The two
ingredients are therefore:

* `Work.Stems.homotopyGroup_loop` — the group isomorphism `π_{n+1}(Y) ≃* π_n(ΩY)` for `n ≥ 1`
  (which is the case here, `hn : 0 < n`), used for the isomorphism `π_n(ΩY) ≃* A`;
* `Work.Stems.curryEquivGroup` — the underlying bijection of the currying, available in *every*
  degree, used for the vanishing of `π_i(ΩY) = π_{i+1}(Y)` for `i ≠ n` (including the case `i = 0`,
  where no group structure exists and the group isomorphism of the previous item is unavailable).
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre

noncomputable section

/-- **`Ω K(A,n+1)` is a `K(A,n)`.**  The `n`-th homotopy group of the loop space `Path qt qt` at the
constant loop is `π_{n+1}(Y,qt) ≃* A`, and all other homotopy groups of the loop space are those of
`Y` shifted by one, hence trivial. -/
theorem loopSpace_isEMSpace {A : Type} [AddCommGroup A] {n : ℕ} (hn : 0 < n) {Y : Type}
    [TopologicalSpace Y] {qt : Y} (h : Work.Serre.IsEMSpace A (n + 1) (by omega : 0 < n + 1) Y qt) :
    Work.Serre.IsEMSpace A n hn (Path qt qt) (Path.refl qt) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  constructor
  · -- the isomorphism `π_n(ΩY) ≃* A`, from the loop-space shift and the model structure of `Y`.
    obtain ⟨e⟩ := Work.Stems.homotopyGroup_loop (n := n) qt
    obtain ⟨iso⟩ := h.1
    exact ⟨e.symm.trans iso⟩
  · -- the vanishing of `π_i(ΩY) = π_{i+1}(Y)` for `i ≠ n`, via the currying bijection.
    intro i hi
    have hsub : Subsingleton (HomotopyGroup (Fin (i + 1)) Y qt) :=
      h.2 (i + 1) (by omega)
    exact @Equiv.subsingleton _ _ (Work.Stems.curryEquivGroup (X := Y) (x := qt) i).symm hsub

end

end Work.Serre
