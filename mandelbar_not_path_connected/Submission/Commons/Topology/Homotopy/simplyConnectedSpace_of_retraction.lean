import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped ContinuousMap

namespace Commons.Topology.Homotopy

/-- Any self-map of a contractible space is homotopic to the identity. -/
theorem homotopic_id_of_contractible {Y : Type*} [TopologicalSpace Y] [ContractibleSpace Y]
    (f : ContinuousMap Y Y) : ContinuousMap.Homotopic f (ContinuousMap.id Y) := by
  obtain ⟨p, hp⟩ := id_nullhomotopic Y
  have hfp : ContinuousMap.Homotopic f (ContinuousMap.const Y p) := by
    have h := hp.comp (ContinuousMap.Homotopic.refl f)
    simpa using h
  exact hfp.trans hp.symm

/-- **A retract of a contractible space is simply connected**: if `i : C(X, Y)` and `ρ : C(Y, X)`
satisfy `ρ ∘ i = id_X` (i.e. `X` is a retract of `Y`) and `Y` is contractible, then `X` is simply
connected.  Indeed `i` is a homotopy equivalence with homotopy inverse `ρ`, so `X` is itself
contractible. -/
theorem simplyConnectedSpace_of_retraction {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (i : ContinuousMap X Y) (ρ : ContinuousMap Y X) (h : ρ.comp i = ContinuousMap.id X)
    [ContractibleSpace Y] : SimplyConnectedSpace X := by
  have hright : ContinuousMap.Homotopic (i.comp ρ) (ContinuousMap.id Y) :=
    homotopic_id_of_contractible (i.comp ρ)
  let e : X ≃ₕ Y :=
    { toFun := i
      invFun := ρ
      left_inv := by rw [h]
      right_inv := hright }
  have hc : ContractibleSpace X := e.contractibleSpace
  exact @SimplyConnectedSpace.ofContractible X _ hc

end Commons.Topology.Homotopy