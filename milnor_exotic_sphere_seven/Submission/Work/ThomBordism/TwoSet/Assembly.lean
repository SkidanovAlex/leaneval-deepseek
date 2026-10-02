import Mathlib
import Submission.Work.ThomBordism.TwoSet.Basic
import Submission.Work.ThomBordism.TwoSet.CompressBasic
import Submission.Work.ThomBordism.TwoSet.Push
import Submission.Work.RatHurewicz.ConnectivityBridge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# From connectivity hypotheses to the compression of the pieces

`Compress.ofSubsingleton` derives the compression of a pair `(Y, Z)` in dimension `e ≥ 1` from
the triviality of `π_e(Y)` and of `π_{e-1}(Z)` (via `push_into_Z`), and `Compress.ofSubsingletonZero`
is the case `e = 0` (path connectedness and a point of `Z`).
-/

open scoped Topology unitInterval

namespace Work.ThomBordism.TwoSet

/-- **The compression property from connectivity, `e ≥ 1`.** -/
theorem Compress.ofSubsingleton {Y : Type*} [TopologicalSpace Y] {Z : Set Y} {e : ℕ}
    (he : 1 ≤ e) (hY : ∀ y, Subsingleton (HomotopyGroup (Fin e) Y y))
    (hZ : ∀ z : ↥Z, Subsingleton (HomotopyGroup (Fin (e - 1)) ↥Z z)) : Compress Y Z e := by
  intro f hf
  obtain ⟨g, K, hK0, hKbd, hgZ, _hgsig, hK1⟩ := push_into_Z he hY hZ f hf
  exact ⟨K, hK0, hKbd, fun x => by rw [hK1]; exact hgZ x⟩

/-- **The compression property from connectivity, `e = 0`.** -/
theorem Compress.ofSubsingletonZero {Y : Type*} [TopologicalSpace Y] {Z : Set Y}
    (hY : ∀ y, Subsingleton (HomotopyGroup (Fin 0) Y y)) (hZ : Z.Nonempty) :
    Compress Y Z 0 := by
  intro f _hf
  obtain ⟨z, hz⟩ := hZ
  haveI := hY (f default)
  have hsub : Subsingleton (ZerothHomotopy Y) :=
    (HomotopyGroup.pi0EquivZerothHomotopy (X := Y) (x := f default)).surjective.subsingleton
  haveI : PathConnectedSpace Y :=
    pathConnectedSpace_iff_zerothHomotopy.mpr ⟨⟨ZerothHomotopy.mk (f default)⟩, hsub⟩
  let γ : Path (f default) z := PathConnectedSpace.somePath _ _
  let G : C(IC 0 × I, Y) := ⟨fun q => γ q.2, γ.continuous.comp continuous_snd⟩
  refine ⟨G, ?_, ?_, ?_⟩
  · intro x
    show γ 0 = f x
    have hx : x = default := Subsingleton.elim _ _
    rw [hx]
    exact γ.source
  · intro x hx t
    exact absurd hx (by simp [Cube.boundary])
  · intro x
    show γ 1 ∈ Z
    rw [γ.target]
    exact hz

end Work.ThomBordism.TwoSet
