import Mathlib
import Submission.Work.ClassFieldTower.Defs

/-!
# `Work.ClassFieldTower.ProTwoDefs` -- the SOUND arithmetic interface for the tower

## Why this file exists

`G_∅ = Gal(F_∅/F)` for an INFINITE extension `F_∅/F` is an infinite profinite group, hence
**uncountable**, while a finitely presented abstract group is **countable**.  Consequently
`Work.ClassFieldTower.HasMinimalPresentation (galoisGroup M) d r` is **UNSATISFIABLE** whenever
`M.K/F` is infinite -- so the certificate built on it in `Defs.lean`/`Main.lean` is vacuous
(the same failure mode as `Commons.GroupTheory.ProPGroup.infinite_of_presentation_of_algebra_data`,
refuted in `Submission/GroupTheory/GolodShafarevichCriterion`).  Do **not** use
`GolodShafarevichCertificate`, `ShafarevichKochInput`, `GeneratorRankInput`,
`DeficiencyBoundInput` or the old `InfiniteHilbertTwoClassFieldTower` as an arithmetic input.

The correct (classical) formulation of Golod--Shafarevich for a pro-`p` group is in terms of a
presentation of the **abstract** group given by the pro-`p` presentation, together with the
statement that its finite `p`-quotients are realized by unramified extensions of the field.
That is what this file sets up; it is the pattern used by
`Submission.NumberField.GolodShafarevichArithmeticInput` in the seed.

## The sound interface

* `ResiduallyFiniteTwoGroup G` -- every `g ≠ 1` survives in a finite `2`-group quotient;
* `RealizedByUnramifiedExtensions F G` -- every finite `2`-group quotient of `G` is the Galois
  group of a finite unramified Galois extension of `F`;
* `ProTwoPresentationData F` -- a finite presentation `⟨α | rel⟩` of `G` with
  `#α = rank₂ Cl(F)` generators, `#rel ≤ rank₂ Cl(F) + d₂(O_F^×)` relators, `α` minimal,
  plus `ResiduallyFiniteTwoGroup G` and `RealizedByUnramifiedExtensions F G`;
* `ProTwoTowerInput F` -- `ProTwoPresentationData F` together with the numerical certificate
  `5 ≤ rank₂ Cl(F)` and `d₂(O_F^×) ≤ 1`;
* `InfiniteProTwoExtension F` -- the conclusion: `G_∅` is infinite.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- **`G` is residually a finite `2`-group**: every nontrivial element has nontrivial image in
some finite `2`-group quotient.  Equivalently, `G` embeds in its pro-`2` completion. -/
def ResiduallyFiniteTwoGroup (G : Type*) [Group G] : Prop :=
  ∀ g : G, g ≠ 1 → ∃ (N : Subgroup G) (_ : N.Normal), Finite (G ⧸ N) ∧
    IsPGroup 2 (G ⧸ N) ∧ (QuotientGroup.mk' N g) ≠ 1

/-- **Every finite `2`-group quotient of `G` is realized by an unramified extension of `F`**:
each such quotient is isomorphic to `Gal(L/F)` for a finite unramified Galois `L/F`. -/
def RealizedByUnramifiedExtensions (F : Type*) [Field F] [NumberField F] (G : Type*)
    [Group G] : Prop :=
  ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N) →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L)
      (_ : FiniteDimensional F L) (_ : IsGalois F L),
      differentIdeal (𝓞 F) (𝓞 L) = ⊤ ∧ Nonempty ((L ≃ₐ[F] L) ≃* (G ⧸ N))

/-- **The Shafarevich--Koch presentation datum for `G_∅`** (see the module docstring).

`G` is presented by `α` generators and `rel` relators; `α` is minimal; the generator number is
the `2`-rank of the class group and the relator number satisfies the Shafarevich--Koch
deficiency bound `#rel ≤ rank₂ Cl(F) + d₂(O_F^×)`.  In addition `G` is residually a finite
`2`-group and its finite `2`-quotients are realized by unramified extensions of `F` (so that
`G`'s pro-`2` completion is `G_∅`).

This is the arithmetic content of the classical Golod--Shafarevich theorem for imaginary
quadratic fields; it is NOT provable from the workspace as it needs the Artin correspondence
and the Shafarevich--Koch relation bound.  Unlike the certificate of `Defs.lean` it is
SATISFIABLE: take `G` to be the abstract finitely presented group of a pro-`2` presentation of
`G_∅`. -/
def ProTwoPresentationData (F : Type*) [Field F] [NumberField F] : Prop :=
  ∃ (α : Type) (_ : Fintype α) (_ : DecidableEq α) (rel : Finset (FreeGroup α)),
    let G := FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))
    Fintype.card α = classGroupTwoRank F ∧
    rel.card ≤ classGroupTwoRank F + unitTwoRank F ∧
    (∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card) ∧
    ResiduallyFiniteTwoGroup G ∧
    RealizedByUnramifiedExtensions F G

/-- **The full arithmetic input**: `ProTwoPresentationData F` together with the numerical
certificate `5 ≤ rank₂ Cl(F)` and `unitTwoRank F ≤ 1` (true for imaginary quadratic `F`). -/
def ProTwoTowerInput (F : Type*) [Field F] [NumberField F] : Prop :=
  ProTwoPresentationData F ∧ 5 ≤ classGroupTwoRank F ∧ unitTwoRank F ≤ 1

/-- **The conclusion: the maximal unramified pro-`2` extension of `F` is infinite.** -/
def InfiniteProTwoExtension (F : Type*) [Field F] [NumberField F] : Prop :=
  ∃ M : MaximalUnramifiedProP.{0} F 2, Infinite (MaximalUnramifiedProP.galoisGroup M)

end Work.ClassFieldTower
