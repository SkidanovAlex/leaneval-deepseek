import Mathlib
import Submission.Work.EMFG.killChain
import Submission.Work.Serre.serrePostnikovTower

namespace Work.EMFG

/-- **Triviality of a homotopy group transports along a path** (arbitrary index `i ≥ 1`).

`Work.Serre.subsingleton_homotopyGroup_of_joined` is stated for the shifted index `Fin (k+1)`; this
is the same statement in the exact degree `i`, obtained by writing `i = (i-1)+1`. -/
theorem subsingleton_homotopyGroup_of_joined' {X : Type} [TopologicalSpace X] {x y : X}
    (h : Joined x y) (i : ℕ) (hi : 1 ≤ i) :
    Subsingleton (HomotopyGroup (Fin i) X x) → Subsingleton (HomotopyGroup (Fin i) X y) := by
  intro hx
  have h' : Subsingleton (HomotopyGroup (Fin (i - 1 + 1)) X x) := by
    rwa [Nat.sub_add_cancel hi]
  have h'' := Work.Serre.subsingleton_homotopyGroup_of_joined h (i - 1) h'
  rwa [Nat.sub_add_cancel hi] at h''

/-- **The iterated "kill everything" chain has no homotopy in degrees `2, …, k+1`.**

`killChain Y k` is `KillCells k (⋯ (KillCells 1 Y))`; the `j`-th step attaches `(j+2)`-cells along
*every* map `S^{j+1} → ·`, killing `π_{j+1}` while leaving `π_i` for `i ≤ j` unchanged
(`Work.Serre.killCells_step`).  Inducting on `k`:

* in degree `i ≤ k+1` the last attachment `KillCells (k+1)` induces a bijection on `π_i` with the
  previous stage, where `π_i` already vanished by the inductive hypothesis; and every point of the
  new space is joined to a point of the previous stage, so the vanishing transports;
* in the top degree `i = k+2` the last attachment kills `π_{k+2}` outright.

The case `k = 0` is vacuous (`2 ≤ i ≤ 1` is impossible). -/
theorem killChain_pi_subsingleton {Y : Type} [TopologicalSpace Y] (k : ℕ) :
    ∀ (p : Work.EMFG.killChain Y k) (i : ℕ), 2 ≤ i → i ≤ k + 1 →
      Subsingleton (HomotopyGroup (Fin i) (Work.EMFG.killChain Y k) p) := by
  induction k with
  | zero =>
    intro p i hi hik
    omega
  | succ k ih =>
    intro p i hi hik
    -- `killChain Y (k+1)` is `KillCells (k+1) (killChain Y k)`, definitionally.
    have hstep := Work.Serre.killCells_step (k + 1) (Work.EMFG.killChain Y k)
    by_cases hle : i ≤ k + 1
    · -- the degree is below the one killed by the last step: transfer along the inclusion
      obtain ⟨y, hy⟩ := hstep.2.2 p
      have hbij := hstep.1 i hle y
      have hsubY : Subsingleton (HomotopyGroup (Fin i) (Work.EMFG.killChain Y k) y) :=
        ih y i hi hle
      have hsub : Subsingleton (HomotopyGroup (Fin i)
          (Work.Serre.KillCells (k + 1) (Work.EMFG.killChain Y k))
          (Work.Serre.killIncl (k + 1) (Work.EMFG.killChain Y k) y)) :=
        ⟨fun a b => by
          obtain ⟨a', rfl⟩ := hbij.surjective a
          obtain ⟨b', rfl⟩ := hbij.surjective b
          exact congrArg (Work.Serre.piMapN (Work.Serre.killIncl (k + 1) (Work.EMFG.killChain Y k)) i y)
            (hsubY.allEq a' b')⟩
      exact subsingleton_homotopyGroup_of_joined' hy.symm i (by omega) hsub
    · -- the top degree, killed by the last step
      have hik' : i = k + 2 := by omega
      subst hik'
      exact hstep.2.1 p

end Work.EMFG
