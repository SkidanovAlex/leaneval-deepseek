import Submission.Work.CY3.Projective
import Submission.Work.CY3.isoOver_stronglyBirational

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3.StronglyRational` — strong rationality (paper `def:strong-birat`)

The paper's notion (`def:strong-birat`): a variety `X` is **strongly rational** if it is strongly
birational to `ℙⁿ`, i.e. if there is a birational map `γ : X ⤏ ℙⁿ` all of whose invariant
coefficients vanish (equivalently `c(γ) = 0` in `ℤ[Bir/𝕜]`).

This is the notion that the paper's `lem:GP-strongly-rational` establishes for the two
`G₂`-Grassmannians:

> If `X` is a smooth projective variety containing an irreducible rational divisor `D ⊂ X` such
> that `U := X ∖ D` is isomorphic to `𝔸ⁿ`, then `X` is strongly rational. In particular, if `G` is
> a split reductive algebraic group over `𝕜`, then every homogeneous space `X = G/P` of Picard rank
> `ρ(X) = 1` is strongly rational.
> *Proof.* Consider the birational map `φ : X ⤏ ℙⁿ` induced by the isomorphism `U ≃ 𝔸ⁿ`. We have
> `φ : X ← U ≃ 𝔸ⁿ ↪ ℙⁿ`, so `c(φ) = [ℙ^{n-1}] − [D] = 0`.

**Why strong rationality is *not* stated with affine space.**  `ℙ¹` and `𝔸¹` are birational but
*not* strongly birational: any birational map `ε : 𝔸¹ ⤏ ℙ¹` is an isomorphism on its source
(`exDiv ε = ∅`), while `ε⁻¹` is undefined at the point at infinity, so
`cInv 𝕜 pt ε = 0 − 1 = −1 ≠ 0`.  Hence `X` strongly rational to `ℙⁿ` does *not* mean that `X` has
transports `𝔸ⁿ ⤏ X` and `X ⤏ 𝔸ⁿ` with vanishing coefficients for every base point; the transports
to *affine* space (needed by the challenge, whose `Cr 𝕜 n` is `Bir(𝔸ⁿ/𝕜)`) have to be supplied with
the base point at which they are used — that is how the CY3 link consumes them (see
`Work.CY3.CY3Data.eps` and the discussion in `NOTES.md` §5).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.CY3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **Strong rationality** (paper `def:strong-birat`): `X` is strongly birational to `ℙⁿ`, i.e.
there is a birational map `X ⤏ ℙⁿ` over `𝕜` all of whose invariant coefficients vanish.

This is a *strengthening* of the paper's notion in one direction (all coefficients rather than the
class `c(γ)`, exactly as for `StronglyBirational`) and is what `lem:GP-strongly-rational` provides
for `G/P`, `G/P'` with `n = 5`. -/
def IsStronglyRational (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [Variety 𝕜 X] (n : ℕ) : Prop :=
  StronglyBirational 𝕜 X (ProjectiveSpace 𝕜 n)

namespace IsStronglyRational

variable {𝕜 : Type} [Field 𝕜] {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y]

/-- **`ℙⁿ` is strongly rational** (with itself), via the identity. -/
theorem projectiveSpace (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    IsStronglyRational 𝕜 (ProjectiveSpace 𝕜 n) n :=
  Work.CY3.StronglyBirational.refl _

/-- **Two strongly rational `n`-folds are strongly birational to each other** — this is item (L2)
of the definition of an L-link when the two sides are `G/P`, `G/P'` and both are strongly rational
(paper `lem:GP-strongly-rational`).  The birational map is produced by transporting through `ℙⁿ`
and all its coefficients vanish, by additivity of the invariant. -/
theorem stronglyBirational {n : ℕ} (h : IsStronglyRational 𝕜 X n)
    (h' : IsStronglyRational 𝕜 Y n) : StronglyBirational 𝕜 X Y :=
  Work.CY3.StronglyBirational.trans h (Work.CY3.StronglyBirational.symm h')

/-- **Strong rationality is preserved by a strong birationality**: a variety strongly birational
to a strongly rational one, with vanishing coefficients, is strongly rational. -/
theorem of_stronglyBirational {n : ℕ} (h : IsStronglyRational 𝕜 X n)
    (γ : StronglyBirational 𝕜 X Y) : IsStronglyRational 𝕜 Y n :=
  Work.CY3.StronglyBirational.trans (Work.CY3.StronglyBirational.symm γ) h

/-- Strong rationality is invariant under isomorphisms over `𝕜` (a special case of
`of_stronglyBirational`, since an isomorphism over `𝕜` is a strong birationality —
`Work.CY3.isoOver_stronglyBirational`). -/
theorem of_isoOver {n : ℕ} (h : IsStronglyRational 𝕜 X n) (e : IsoOver 𝕜 X Y) :
    IsStronglyRational 𝕜 Y n := by
  obtain ⟨γ, hγ, h0⟩ := isoOver_stronglyBirational e
  exact h.of_stronglyBirational ⟨γ, hγ, h0⟩

end IsStronglyRational

end

end Work.CY3
