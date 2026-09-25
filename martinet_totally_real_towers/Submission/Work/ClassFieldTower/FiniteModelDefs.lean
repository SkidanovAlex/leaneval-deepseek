import Mathlib
import Submission.Work.ClassFieldTower.WallShrunk

/-!
# `Work.ClassFieldTower.FiniteModelDefs` -- the explicit finite model of `(𝔽₂)^5`

`Work.ClassFieldTower.KcRelationBound` (`WallShrunk.lean`) is the **universally quantified**
form of the Shafarevich--Koch deficiency bound: it is a statement about *every* finite
presentation whose finite `2`-quotients look like unramified extensions of `Kc`.  This module
fixes the explicit test model against which that statement is refuted in
`Work.ClassFieldTower.RefuteRelationBound`:

* `relF` -- the relators of the "free `(𝔽₂)^5`" presentation of the elementary abelian group of
  order `2 ^ 5` on five generators: the squares of the generators and all commutators;
* `GF` -- the quotient `FreeGroup (Fin 5) ⧸ normalClosure relF`.

The group `GF` is an explicit *finite* group (order `32`) presented by five minimal generators
and relators, with a canonical surjection onto `(𝔽₂)^5 = F2five`; it has the same finite
`2`-quotients as the genus group of `Kc = ℚ(√-30030)` (indeed it is isomorphic to it), so the
unramified subfields of the genus field of `Kc` realize all of them
(`Work.ClassFieldTower.RealizedByUnramifiedExtensions`).  Hence `GF` satisfies *all* the
hypotheses of `KcRelationBound`, while no finite `2`-group can satisfy its conclusion
(Golod--Shafarevich, Chapter B) -- see `Work.ClassFieldTower.not_kcRelationBound`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped commutatorElement

noncomputable section

namespace Work.ClassFieldTower

/-- **The relators of the finite model.**  On the five free generators `x₀,…,x₄`: their squares
`xᵢ ^ 2` (so that the generators are involutions) and all commutators `⁅xᵢ, xⱼ⁆` (so that they
commute).  The quotient is therefore the elementary abelian `2`-group of rank `5`. -/
def relF : Finset (FreeGroup (Fin 5)) :=
  (Finset.univ.image fun i : Fin 5 => FreeGroup.of i ^ 2) ∪
  (Finset.univ.image fun p : Fin 5 × Fin 5 =>
    FreeGroup.of p.1 * FreeGroup.of p.2 * (FreeGroup.of p.1)⁻¹ * (FreeGroup.of p.2)⁻¹)

/-- **The explicit finite model**: the presentation `⟨x₀,…,x₄ | xᵢ² , [xᵢ,xⱼ]⟩`, whose group is
the elementary abelian `2`-group `(𝔽₂)^5` (iso `Work.ClassFieldTower.mulEquiv_GF_f2five`). -/
abbrev GF : Type := FreeGroup (Fin 5) ⧸ Subgroup.normalClosure (relF : Set (FreeGroup (Fin 5)))

end Work.ClassFieldTower

end
