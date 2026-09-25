import Mathlib
import Submission.Work.ClassFieldTower.ProTwoGenus
import Submission.Work.ClassFieldTower.ProTwoGeneratorRank

/-!
# `proTwoShafarevichKochInput_of_no_unramified`

From the arithmetic hypothesis

> every finite unramified Galois extension `L/F` whose Galois group `Gal(L/F)` is a `2`-group is
> trivial

we derive the Shafarevich--Koch input `Work.ClassFieldTower.ProTwoShafarevichKochInput F` of
`ProTwoGenus.lean`.

Under the hypothesis the maximal unramified pro-`2` extension of `F` is `F` itself, so the abstract
group `G` describing `G_∅` may be taken to be the trivial group.  Concretely we present it by the
empty generating set: `α = Empty`, `rel = ∅`, so that

`G = FreeGroup Empty ⧸ Subgroup.normalClosure (∅ : Set (FreeGroup Empty))`

is a subsingleton.  Every clause of `ProTwoShafarevichKochInput` is then immediate, the only
non-formal input being that the trivial extension `F/F` is unramified, i.e.
`differentIdeal (𝓞 F) (𝓞 F) = ⊤` (`differentIdeal_self_eq_top` below).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- The relative different of the trivial extension `F/F` is the unit ideal: the extension has no
ramification, so no prime ideal divides its different. -/
theorem differentIdeal_self_eq_top {F : Type} [Field F] [NumberField F] :
    differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers F) = ⊤ := by
  refine Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_ramificationIdx ?_
  intro Q hQ
  exact Ideal.ramificationIdx_eq_one Q (NumberField.RingOfIntegers F)

/-- Any two subsingleton monoids are isomorphic (with the trivial multiplicative equivalence). -/
private noncomputable def mulEquivOfSubsingleton {M N : Type*} [Monoid M] [Monoid N]
    [Subsingleton M] [Subsingleton N] : M ≃* N where
  toFun := fun _ => 1
  invFun := fun _ => 1
  left_inv := fun x => Subsingleton.elim _ _
  right_inv := fun x => Subsingleton.elim _ _
  map_mul' := fun x y => by simp

/-- **From "there is no nontrivial unramified `2`-extension of `F`" to the Shafarevich--Koch
input.**  The maximal unramified pro-`2` extension is then trivial, so the abstract group `G`
witnessing `ProTwoShafarevichKochInput F` is the trivial group, presented by no generators and no
relations. -/
theorem proTwoShafarevichKochInput_of_no_unramified {F : Type} [Field F] [NumberField F]
    (h : ∀ (L : Type) [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L]
          [IsGalois F L], differentIdeal (NumberField.RingOfIntegers F)
            (NumberField.RingOfIntegers L) = ⊤ →
          IsPGroup 2 (L ≃ₐ[F] L) → Subsingleton (L ≃ₐ[F] L)) :
    Work.ClassFieldTower.ProTwoShafarevichKochInput F := by
  refine ⟨Empty, inferInstance, inferInstance, (∅ : Finset (FreeGroup Empty)), ?_, ?_, ?_, ?_⟩
  -- the trivial presentation has `0` generators and `0 ≤ 0 + 1` relators
  · simp
  -- the generator set is minimal
  · intro S _
    simp
  -- `G` is trivial, hence residually a finite `2`-group
  · intro g hg
    exact absurd (Subsingleton.elim g 1) hg
  · refine ⟨?_, ?_⟩
    · -- every finite `2`-quotient of the trivial group is realized by `F/F`
      intro N hN hfin hpg
      refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        differentIdeal_self_eq_top, ?_⟩
      exact ⟨mulEquivOfSubsingleton⟩
    · -- conversely every unramified `2`-extension `L/F` has trivial Galois group (`h`)
      intro L hL hNL hAL hfd hgal hunr hpg
      haveI : Subsingleton (L ≃ₐ[F] L) := h L hunr hpg
      refine ⟨⊤, inferInstance, inferInstance, ?_, ?_⟩
      · exact IsPGroup.of_subsingleton 2 _
      · exact ⟨mulEquivOfSubsingleton⟩

end Work.ClassFieldTower
