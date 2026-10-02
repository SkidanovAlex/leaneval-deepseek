import Mathlib
import Submission.Work.StemsB.Fibrations

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Covering maps are Serre fibrations

A covering map `p : E → B` has the homotopy lifting property with respect to every space
(Proposition 1.30 of [hatcher02]): it is a Hurewicz fibration, hence in particular a Serre
fibration in the sense of `Work.StemsB.IsSerreFibration`.

Mathlib already provides `IsCoveringMap.liftHomotopy` (`Mathlib/Topology/Homotopy/Lifting.lean`),
which lifts a homotopy `I × A → B` starting from a lift of its `0`-face.  Composing the lifted
homotopy with the evaluation at `1 : I` produces the required homotopy between maps on the cube
`Z = I^n`.
-/

open scoped Topology unitInterval

namespace Work.StemsB

/-- **A covering map is a Serre fibration.**  Given `H : (p ∘ f).Homotopy b` for maps on a cube
`Z = Fin n → I`, the lift of `H` through the covering map `p`, started at the lift `f` of `H₀`, is
obtained from `IsCoveringMap.liftHomotopy` and evaluated at `1 : I` to get the target map. -/
theorem isSerreFibration_of_isCoveringMap {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : IsCoveringMap p) : Work.StemsB.IsSerreFibration p := by
  intro n f b H
  -- The `0`-face of `H` is a lift of `p ∘ f`.
  have H0 : ∀ a, H.toContinuousMap (0, a) = p (f a) := fun a => H.apply_zero a
  -- Lift the homotopy `H` in the base, starting from `f`.
  let L : C(I × (Fin n → I), E) := hp.liftHomotopy H.toContinuousMap f H0
  have hL : p.comp L = H.toContinuousMap := by
    ext z
    exact congr_fun (hp.liftHomotopy_lifts H.toContinuousMap f H0) z
  refine ⟨L.comp (ContinuousMap.prodMk (ContinuousMap.const _ (1 : I)) (ContinuousMap.id _)),
    ⟨L, ?_, ?_⟩, ?_⟩
  · intro a
    exact hp.liftHomotopy_zero H.toContinuousMap f H0 a
  · intro a
    rfl
  · simpa using hL

end Work.StemsB
