import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Topology.Jordan

/-- Points of the closure of a connected component `K` of the complement `Sᶜ` of a closed
set `S` which are not interior to `K` must lie in `S`.

Proof idea: `Sᶜ` is open, so (in the locally connected space `ℂ`) its connected
components are open; in particular `K` is open, hence `interior K = K`.  For
`z ∈ closure K` with `z ∉ interior K` we have `z ∉ K`.  If moreover `z ∉ S` then
`z ∈ Sᶜ` and `K' := connectedComponentIn Sᶜ z` is an open neighbourhood of `z`;
since `z ∈ closure K`, the open set `K'` meets `K`.  Any common point `w` lies in
both components, forcing `K' = K` and contradicting `z ∉ K`. -/
theorem frontier_connectedComponentIn_subset {S : Set ℂ} (hS : IsClosed S) (c : ℂ) :
    ∀ z ∈ closure (connectedComponentIn Sᶜ c), z ∉ interior (connectedComponentIn Sᶜ c) → z ∈ S := by
  intro z hzcl hzint
  by_contra hzS
  have hzC : z ∈ Sᶜ := by simpa using hzS
  have hCopen : IsOpen Sᶜ := hS.isOpen_compl
  have hKopen : IsOpen (connectedComponentIn Sᶜ c) := hCopen.connectedComponentIn
  have hzK : z ∉ connectedComponentIn Sᶜ c := by
    intro h
    exact hzint (by rw [hKopen.interior_eq]; exact h)
  have hK'open : IsOpen (connectedComponentIn Sᶜ z) := hCopen.connectedComponentIn
  have hzK' : z ∈ connectedComponentIn Sᶜ z := mem_connectedComponentIn hzC
  have hne : (connectedComponentIn Sᶜ z ∩ connectedComponentIn Sᶜ c).Nonempty :=
    mem_closure_iff.mp hzcl _ hK'open hzK'
  obtain ⟨w, hwK', hwK⟩ := hne
  have h1 : connectedComponentIn Sᶜ c = connectedComponentIn Sᶜ w := connectedComponentIn_eq hwK
  have h2 : connectedComponentIn Sᶜ z = connectedComponentIn Sᶜ w := connectedComponentIn_eq hwK'
  have : z ∈ connectedComponentIn Sᶜ c := by
    rw [h1, ← h2]
    exact hzK'
  exact hzK this

end Commons.Topology.Jordan