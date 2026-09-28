import Mathlib
import Submission.Work.Stems.Cubical.CubeFace

/-!
# Small cubical helpers for the Hurewicz development

Definitions shared by the lemmas delegated by the prover of
`Work.RatHurewicz.hurewiczKerTorsionFirstDegree`:

* `cval : Fin 2 → unitInterval` — the two face values `0`, `1`;
* `cconst n x` — the constant `n`-cube at `x`;
* `ConstChain n X x₀` — the `ℤ`-span of the constant cube at `x₀` (the degenerate correction that
  the simplicial/cubical comparison produces in the bridge `cubicalBridge`).
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

/-- The two face values `0` and `1` of a cube, indexed by `Fin 2`. -/
def cval : Fin 2 → unitInterval := ![0, 1]

@[simp] theorem cval_zero : cval 0 = (0 : unitInterval) := rfl

@[simp] theorem cval_one : cval 1 = (1 : unitInterval) := rfl

/-- The constant `n`-cube at `x`. -/
abbrev cconst (n : ℕ) {X : Type} [TopologicalSpace X] (x : X) : C(IC n, X) :=
  ContinuousMap.const (IC n) x

/-- The degenerate cubical `n`-chains: spanned by the cubes which are **independent of** one
coordinate, i.e. `f` factors through the projection dropping the coordinate `i`.

NOTE (session 3): the first version of this definition imposed the *opposite* condition
`t i = t' i → f t = f t'` ("`f` depends only on the `i`-th coordinate").  That is not the
degenerate subcomplex that the simplicial/cubical comparison produces (the two agree only for
`n ≤ 2`); the condition below is the standard one, and it is closed under taking faces.  Reported
by the prover of `Work.RatHurewicz.cubicalBridgeDeg`, who showed the earlier one made the bridge
false for `n ≥ 3`. -/
def Deg (n : ℕ) (X : Type) [TopologicalSpace X] : Submodule ℤ (Cub n X) :=
  iSup fun i : Fin n => Submodule.span ℤ
    {x : Cub n X | ∃ f : C(IC n, X),
      (∀ t t' : IC n, (∀ j : Fin n, j ≠ i → t j = t' j) → f t = f t') ∧
        x = Finsupp.single f (1 : ℤ)}

/-- The `ℤ`-submodule of the cubical `n`-chains spanned by the constant cube at `x₀`. -/
def ConstChain (n : ℕ) (X : Type) [TopologicalSpace X] (x₀ : X) : Submodule ℤ (Cub n X) :=
  Submodule.span ℤ {Finsupp.single (cconst n x₀) (1 : ℤ)}

end

end Work.RatHurewicz
