import Mathlib
import Submission.Work.Serre.Models
import Submission.Work.Stems.homotopyGroup_loop

/-!
# The loop space of a `K(A,n)`-model is a `K(A,n-1)`-model

`Work.Stems.isEMSpace_loop`: for `k ≥ 1`, if `X` is a model of `K(A,k+1)` at `pt`
(`Work.Serre.IsEMSpace A (k+1) _ X pt`, i.e. `π_{k+1}(X,pt) ≃* Multiplicative A` and every other
homotopy group trivial), then the loop space `ΩX = Path pt pt` at the constant loop is a model of
`K(A,k)`.

This is the loop shift of the path–loop fibration (`Work.Stems.homotopyGroup_loop`, the `MulEquiv`
`π_{k+1}(X,pt) ≃* π_k(ΩX)`), and it is the identification that the **odd step of the `C2` layer**
needs: the fibre of the cover `Eₙ → Sⁿ` of a `K(ℤ,n)`-model is the loop space `ΩX`, and the
vanishing of its rational homology in the range is what `Work.Stems.Engine.C2evenRange` supplies.

(The case `k = 0` is excluded because `IsEMSpace A 0` carries the impossible hypothesis `0 < 0`;
this is harmless: `C2evenRange`'s index `k = (n-1)/2` is `≥ 1` whenever `n ≥ 3`.)
-/

open scoped Topology Topology.Homotopy

set_option linter.style.haveILetI false

namespace Work.Stems

noncomputable section

/-- **The loop space of a `K(A,k+1)`-model is a `K(A,k)`-model.** -/
theorem isEMSpace_loop {A : Type} [AddCommGroup A] {k : ℕ} (hk : 1 ≤ k) {X : Type}
    [TopologicalSpace X] (pt : X) (h : Work.Serre.IsEMSpace A (k + 1) (Nat.succ_pos k) X pt) :
    Work.Serre.IsEMSpace A k (by omega) (Path pt pt) (Path.refl pt) := by
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  refine ⟨?_, ?_⟩
  · -- `π_k(ΩX) ≃* Multiplicative A`: the loop shift composed with `π_{k+1}(X,pt) ≃* A`.
    obtain ⟨e⟩ := Work.Stems.homotopyGroup_loop (X := X) (n := k) pt
    exact ⟨e.symm.trans h.1.some⟩
  · -- every other homotopy group of `ΩX` is trivial
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · -- `π₀(ΩX) ≃ π₁(X,pt) = 0` (the currying bijection, in degree `0`)
      let e := Work.Stems.curryEquivGroup (X := X) (x := pt) 0

      have h1 : ∀ x y : HomotopyGroup (Fin 1) X pt, x = y := fun x y => h.2 1 (by omega) |>.elim x y
      exact ⟨fun a b => by
        obtain ⟨x, rfl⟩ := e.surjective a
        obtain ⟨y, rfl⟩ := e.surjective b
        rw [h1 x y]⟩
    · -- `π_i(ΩX) ≃* π_{i+1}(X,pt) = 0` for `i ≥ 1`
      haveI : Nonempty (Fin i) := ⟨⟨0, hipos⟩⟩
      obtain ⟨e⟩ := Work.Stems.homotopyGroup_loop (X := X) (n := i) pt
      have h1 : ∀ x y : HomotopyGroup (Fin (i + 1)) X pt, x = y :=
        fun x y => (h.2 (i + 1) (by omega)).elim x y
      exact ⟨fun a b => by
        obtain ⟨x, rfl⟩ := e.surjective a
        obtain ⟨y, rfl⟩ := e.surjective b
        rw [h1 x y]⟩

end

end Work.Stems
