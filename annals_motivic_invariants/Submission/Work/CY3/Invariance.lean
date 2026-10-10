import Submission.Work.CY3.Defs
import Submission.Work.CY3.isoOver_stronglyBirational

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3.Invariance` — `Work.CY3.StronglyBirational` under isomorphism, and (L2) consequences

The notation of an L-link is only defined up to isomorphism of its constituents (`G/P` is "*a*"
model of the `G₂`-Grassmannian, `ℙ⁴` "*a*" model of projective space, …).  This file collects the
invariance statements that make that harmless:

* `Work.CY3.isoOver_stronglyBirational` (proved by a colleague in
  `Submission/Work/CY3/isoOver_stronglyBirational.lean`): an isomorphism over `𝕜` is a strong
  birationality;
* `Work.CY3.StronglyBirational.congr` — strong birationality is invariant under replacing either
  side by an isomorphic `𝕜`-scheme;
* `Work.CY3.IsStronglyRational.of_isoOver` (in `Submission/Work/CY3/StronglyRational.lean`) —
  strong rationality is invariant under isomorphism over `𝕜`, so the layer-1 input
  `IsStronglyRational 𝕜 (G/P) 5` may be used with any model of `G/P`;
* `Work.CY3.cInv_symm_trans_eq` (in `Submission/Work/CY3/Defs.lean`) — item (L2) in the form the
  paper uses for `c(φ) = c(ψ)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.CY3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {𝕜 : Type} [Field 𝕜]
variable {X Y X' Y' : Scheme.{0}}

namespace StronglyBirational

variable [Variety 𝕜 X] [Variety 𝕜 Y] [Variety 𝕜 X'] [Variety 𝕜 Y']

/-- **Strong birationality is invariant under isomorphisms over `𝕜`**: replacing either side by an
isomorphic `𝕜`-scheme does not change the relation.  (Uses that an isomorphism over `𝕜` is itself a
strong birationality, `Work.CY3.isoOver_stronglyBirational`, and that strong birationality is an
equivalence relation, `Work.CY3.StronglyBirational.symm`/`trans`.) -/
theorem congr (h : StronglyBirational 𝕜 X Y) (e : IsoOver 𝕜 X X') (e' : IsoOver 𝕜 Y Y') :
    StronglyBirational 𝕜 X' Y' :=
  ((isoOver_stronglyBirational e).symm.trans h).trans (isoOver_stronglyBirational e')

end StronglyBirational

end

end Work.CY3
