import Mathlib
import Submission.Work.Serre.Models
import Submission.Work.Stems.basepoint_iso
import Submission.Work.Stems.subsingleton_homotopyGroup_change_basepoint

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Basepoint change for `K(A,m)` models

`Work.Serre.IsEMSpace A m hm X pt` says that `X` is a model of the Eilenberg–MacLane space
`K(A,m)`, based at `pt`: `π_m(X,pt) ≃* A` and `π_i(X,pt) = 1` for `i ≠ m`.  Being a model of
`K(A,m)` only depends on the path component of the base point, and here we prove it:

if `γ : Path pt x` and `X` is a model of `K(A,m)` at `pt`, then `X` is a model of `K(A,m)` at `x`.

The two halves of the definition are transported separately.

* The `π_m`-half is transported along the group isomorphism
  `Work.Stems.basepoint_iso γ : π_m(X,pt) ≃* π_m(X,x)`, which is built from the collar of the cube
  (`Submission/Work/Stems/basepoint_iso.lean`).
* The vanishing half uses
  `Work.Stems.subsingleton_homotopyGroup_change_basepoint`, the basepoint-independence of
  triviality of `π_N`.
-/

namespace Work.Stems

theorem isEMSpace_change_basepoint {A : Type} [AddCommGroup A] {m : ℕ} (hm : 0 < m)
    {X : Type} [TopologicalSpace X] {pt x : X} (γ : Path pt x)
    (h : Work.Serre.IsEMSpace A m hm X pt) : Work.Serre.IsEMSpace A m hm X x := by
  have hne : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  refine ⟨?_, ?_⟩
  · -- the `π_m`-half, along the basepoint change isomorphism
    obtain ⟨e⟩ := h.1
    obtain ⟨e'⟩ := @basepoint_iso (Fin m) X _ _ hne pt x γ
    exact ⟨e'.symm.trans e⟩
  · -- the vanishing half, pointwise at every degree `i ≠ m`
    intro i hi
    exact subsingleton_homotopyGroup_change_basepoint γ (h.2 i hi)

end Work.Stems
