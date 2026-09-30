import Mathlib
import ChallengeDeps
import Submission.Work.HomologyExtra.Basic
import Submission.Work.HomologyExtra.CycleClass
import Submission.Work.HomologyExtra.simplexBoundaryChain_d
import Submission.Work.HomologyExtra.simplexRelChain_d

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The fundamental class of the sphere `∂Δⁿ⁺¹` and the generator of `Hₙ(Δⁿ, ∂Δⁿ)`

* `simplexBoundaryClass n : ℤ ⟶ Hₙ(∂Δⁿ⁺¹; ℤ)` — the class of the alternating sum of the
  codimension-one faces of the identity `(n+1)`-simplex (the fundamental class of the sphere
  `∂Δⁿ⁺¹ ≅ Sⁿ`);
* `simplexGenMap n : ℤ ⟶ Hₙ(Δⁿ, ∂Δⁿ; ℤ)` — the class of the identity simplex, i.e. the
  morphism `1 ↦ [ιₙ]`.

The main theorem of the chapter is that `simplexGenMap n` is an isomorphism (the identity simplex
generates the top relative homology of the simplex pair, Hatcher's computation underlying
Theorem 2.27), together with the companion computation `H_k(Δⁿ,∂Δⁿ) = 0` for `k ≠ n`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.HomologyExtra

noncomputable section

/-- **The fundamental class of the sphere `∂Δⁿ⁺¹`**: the class of the fundamental cycle
`∑ᵢ (-1)ⁱ (i-th face)` of the identity `(n+1)`-simplex, viewed in `Hₙ(∂Δⁿ⁺¹; ℤ)`. -/
noncomputable def simplexBoundaryClass (n : ℕ) :
    Work.Homology.ZMod ⟶
      Work.Homology.singHomology Work.Homology.ZMod n (boundarySpace (n + 1)) :=
  cycleClass (simplexBoundaryChain n) (simplexBoundaryChain_d n)

/-- **The generator of `Hₙ(Δⁿ, ∂Δⁿ; ℤ)`**: the class of the identity singular simplex `ιₙ`, as a
morphism `ℤ ⟶ Hₙ(Δⁿ,∂Δⁿ)`, i.e. `1 ↦ [ιₙ]`. -/
noncomputable def simplexGenMap (n : ℕ) :
    Work.Homology.ZMod ⟶
      Work.Homology.relHomology Work.Homology.ZMod n (simplex n) (simplexBoundary n) :=
  cycleClass (simplexRelChain n) (simplexRelChain_d n)

end

end Work.HomologyExtra
