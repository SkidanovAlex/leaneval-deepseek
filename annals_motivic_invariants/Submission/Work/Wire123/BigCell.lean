import Submission.Work.CY3.Projective
import Submission.Work.CrauderKatz.BlowUp.exists_birationalMap_exDiv_singleton_of_openImmersion

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Wire123.BigCell` — the paper's `lem:GP-strongly-rational` as a structure

The paper's Lemma (`lem:GP-strongly-rational`) reads: if `X` is a smooth projective variety
containing an irreducible rational divisor `D` such that `U := X ∖ D` is isomorphic to `𝔸ⁿ`, then
`X` is **strongly rational** (strongly birational to `ℙⁿ`); the proof is

  `φ : X ⤳ U ≅ 𝔸ⁿ ↪ ℙⁿ`,  with  `c(φ) = [ℙⁿ⁻¹] - [D] = 0`,

the two contributions cancelling because `D` is rational, i.e. because its generic point has the
same birational class as the hyperplane at infinity.

`BigCell 𝕜 n` is that hypothesis in the vocabulary of this workspace:

* an open immersion `j : U ⟶ X` over `𝕜` with dense range, whose complement contains exactly one
  codimension-one point `x` (`uniq`), i.e. `X ∖ U` is a single divisor with generic point `x`;
* an isomorphism `e : U ≅ 𝔸ⁿ` over `𝕜` (the *big cell*);
* the chart `𝔸ⁿ ⤳ ℙⁿ` with its unique exceptional point `y` (the hyperplane at infinity), whose
  existence is `Work.Wire123.exists_affineToProjective`;
* the rationality of the complement divisor, as `ResEquiv 𝕜 x y` (the generic point of `X ∖ U` has
  the class of a hyperplane).

`Work.Wire123.BigCell.stronglyBirational` (delegated) is then exactly the paper's Lemma: the
composite has vanishing coefficient, so `X` is strongly rational.  In particular, with it, the
`stronglyBirational` field of `Work.Wire123.TransLink`/`MinLink` is *derivable* from this concrete
geometric hypothesis; the remaining input of the `n ≥ 5` case is then the paper's `thm:CY3`
geometry (two `G₂`-Grassmannians `G/P`, `G/P'` with their Bruhat big cells, an L-link between them
and the non-stably-birational threefolds), i.e. exactly the missing chapter.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Wire123

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **An `n`-fold with a big cell ≅ `𝔸ⁿ` whose complement is one rational divisor** — the
hypothesis of the paper's `lem:GP-strongly-rational`. -/
structure BigCell (𝕜 : Type) [Field 𝕜] (n : ℕ) where
  /-- the variety. -/
  X : Scheme.{0}
  [varietyX : Variety 𝕜 X]
  /-- the generic point of the complement divisor. -/
  x : X
  /-- it is codimension one. -/
  hx : Order.coheight x = 1
  /-- the big cell. -/
  U : Scheme.{0}
  [varietyU : Variety 𝕜 U]
  /-- the open immersion of the big cell. -/
  j : U ⟶ X
  [isOpenImmersion : IsOpenImmersion j]
  /-- it is a map over `𝕜`. -/
  isOver_j : j.IsOver (Spec (.of 𝕜))
  /-- its range is dense. -/
  dense : DenseRange j
  /-- the complement is **nonempty**: `U` is a proper open subset, i.e. `X ∖ U` really is a
  (nonempty) divisor.  Without this the hypotheses are vacuous for `j = 𝟙` (`Set.range j = univ`),
  and the conclusion would be false: `𝔸ⁿ` is *not* strongly rational. -/
  x_notMem : x ∉ Set.range j
  /-- the complement has exactly one codimension-one point. -/
  uniq : ∀ z : X, Order.coheight z = 1 → z ∉ Set.range j → z = x
  /-- the identification of the big cell with affine `n`-space. -/
  e : U ≅ Work.CY3.Affine 𝕜 n
  /-- it is an isomorphism over `𝕜`. -/
  isOver_e : e.hom.IsOver (Spec (.of 𝕜))
  /-- the point at infinity of the chart. -/
  y : Work.CY3.ProjectiveSpace 𝕜 n
  /-- it is codimension one. -/
  hy : Order.coheight y = 1
  /-- the chart `𝔸ⁿ ⇢ ℙⁿ` has no other exceptional point
  (`Work.Wire123.exists_affineToProjective`). -/
  chart : ∃ γ : (Work.CY3.Affine 𝕜 n).BirationalMap (Work.CY3.ProjectiveSpace 𝕜 n),
    γ.IsOver (Spec (.of 𝕜)) ∧ exDiv γ = ∅ ∧ exDiv γ.symm = {y}
  /-- the complement divisor is rational: its generic point has the class of a hyperplane. -/
  resEquiv : ResEquiv 𝕜 x y

attribute [instance] BigCell.varietyX BigCell.varietyU BigCell.isOpenImmersion

end

end Work.Wire123
