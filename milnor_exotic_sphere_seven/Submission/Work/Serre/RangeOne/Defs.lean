import Mathlib
import Submission.Work.Serre.Engine

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The comparison input of the `1`-type range form of C3

`Work.Serre.RangeEMVanOne` (the range form of the acyclicity of `K(A,1)` for torsion `A`) is proved
from `SerreC0`/`SerreC3` by comparing the range model `W` with a *genuine* model of `K(π₁W,1)`.
This file fixes the interface of that comparison (see `Submission/Work/Serre/serreRangeEMVanOne.lean`
for the reduction, and `Submission/Work/Serre/RangeOne/Comparison.lean` for the range-Whitehead
input).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-- **The comparison input of the `1`-type range form of C3.**  A space `W` with base point `w₀`
admits a *genuine* model `Z` of `K(π₁(W,w₀), 1)` (its `π₁` is isomorphic to `π₁(W,w₀)` and all its
other homotopy groups are trivial) together with a map `W → Z` which is a bijection on `πᵢ` at
*every* base point for `i ≤ N`.

Such a `Z` is the colimit of the infinite truncation tower of `W`
(`Work.RatHurewicz.towerState`, available at every stage `s : ℕ`): the colimit has
`π₁ ≅ π₁(W)` and vanishing higher homotopy groups (a cube into the colimit factors through a
stage), and the map `W → colimit` is a `π`-isomorphism in every degree. -/
def RangeModelComparison (N : ℕ) (W : Type) [TopologicalSpace W] (w₀ : W) : Prop :=
  ∃ (Z : Type) (_ : TopologicalSpace Z) (pt : Z) (f : C(W, Z)),
    (Nonempty (HomotopyGroup (Fin 1) Z pt ≃* HomotopyGroup (Fin 1) W w₀) ∧
      (∀ i : ℕ, i ≠ 1 → Subsingleton (HomotopyGroup (Fin i) Z pt))) ∧
    (∀ i : ℕ, i ≤ N → ∀ x : W, Function.Bijective (piMapN f i x))

end

end Work.Serre
