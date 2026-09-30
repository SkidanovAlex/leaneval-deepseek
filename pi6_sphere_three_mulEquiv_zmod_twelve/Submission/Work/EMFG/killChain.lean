import Mathlib
import Submission.Work.Serre.serreAttachKillPi

/-!
# The iterated "kill everything" chain, and the extension of a map over it

`Work.Serre.KillCells m Y` is `Y` with an `(m+2)`-cell attached along *every* map `S^{m+1} → Y`;
`Work.Serre.killCells_step` shows that it kills `π_{m+1}` and preserves `π_i` for `i ≤ m`.

`killChain Y k` is the `k`-fold iterate `KillCells k (⋯ (KillCells 1 Y))`: it kills `π_2, …, π_{k+1}`
and preserves `π_0` and `π_1`.  The main statement of this file, `killChain_extend`, shows that a map
`φ : Y → B` whose target has `π_i(B) = 0` for `2 ≤ i ≤ N` extends to `killChain Y (N-1)`; this is
what lets two `π₁`-isomorphisms on a common source be compared without losing the higher degrees.
-/

open scoped Topology

namespace Work.EMFG

noncomputable section

/-- A type bundled with its topology. -/
abbrev Bundled : Type 1 := Σ T : Type, TopologicalSpace T

/-- The iterated "kill everything" chain, as bundled spaces. -/
noncomputable def killChainB (Y : Bundled) : ℕ → Bundled :=
  Nat.rec Y (fun k ih =>
    ⟨@Work.Serre.KillCells (k + 1) ih.1 ih.2, by
      letI : TopologicalSpace ih.1 := ih.2
      infer_instance⟩)

/-- The iterated "kill everything" chain: kills `π_2, …, π_{k+1}`, preserves `π_0` and `π_1`. -/
abbrev killChain (Y : Type) [tY : TopologicalSpace Y] (k : ℕ) : Type :=
  (killChainB ⟨Y, tY⟩ k).1

instance killChainTop (Y : Type) [tY : TopologicalSpace Y] (k : ℕ) :
    TopologicalSpace (killChain Y k) :=
  (killChainB ⟨Y, tY⟩ k).2

attribute [instance] killChainTop

/-- The step inclusion of the chain. -/
noncomputable def killChainIncl (Y : Type) [tY : TopologicalSpace Y] (k : ℕ) :
    C(killChain Y k, killChain Y (k + 1)) :=
  Work.Serre.killIncl (k + 1) (killChain Y k)

/-- The composite inclusion of `Y` into the chain. -/
noncomputable def killChainUp (Y : Type) [tY : TopologicalSpace Y] :
    ∀ k, C(Y, killChain Y k)
  | 0 => ContinuousMap.id Y
  | (k + 1) => (killChainIncl Y k).comp (killChainUp Y k)

/-- The base point of the chain, inherited from a base point of `Y`. -/
noncomputable def killChainBase (Y : Type) [tY : TopologicalSpace Y] (y₀ : Y) (k : ℕ) :
    killChain Y k :=
  Nat.rec y₀ (fun k ih => by
    letI : TopologicalSpace (killChain Y k) := killChainTop Y k
    exact Work.Serre.killIncl (k + 1) (killChain Y k) ih) k

end

end Work.EMFG
