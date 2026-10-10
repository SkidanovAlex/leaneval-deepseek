import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Commons.NumberTheory.NumberField.Valuation.le_eq_top_of_comap_ne_top_of_ne
import Submission.Commons.RingTheory.Valuation.isSepClosed_of_two_independent_henselian
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Valuation

/-- **F. K. Schmidt: at most one indecomposable prime.**

Let `K` be a number field, `K'` a separable closure and `L ≠ K'` an intermediate field.  Then
there cannot be two distinct valuation subrings `A₁ ≠ A₂` of `K'` which both restrict
nontrivially to `L` and are the *unique* extensions of their restrictions to `L`.

Equivalently: `L` carries at most one place whose extension to the separable closure is unique.

The proof is F. K. Schmidt's theorem: a field which carries two *independent* nontrivial
Henselian valuations is separably closed.  Indeed `A₁, A₂` give two distinct places
`C₁ ≠ C₂` of `L` which are both Henselian (their extensions to `K'` are unique, hence their
valuation rings are Henselian local rings), and distinct places lying over finite primes of a
number field are independent.  Since `L ≠ K'` it cannot be separably closed. -/
theorem atMostOne_indecomposable_prime {K K' : Type*} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K']
    (L : IntermediateField K K') (hL : L ≠ ⊤)
    (A₁ A₂ : ValuationSubring K') (hne : A₁ ≠ A₂)
    (h₁ : A₁.comap (algebraMap ↥L K') ≠ ⊤) (h₂ : A₂.comap (algebraMap ↥L K') ≠ ⊤)
    (hA₁ : ∀ B : ValuationSubring K', B.comap (algebraMap ↥L K') = A₁.comap (algebraMap ↥L K') → B = A₁)
    (hA₂ : ∀ B : ValuationSubring K', B.comap (algebraMap ↥L K') = A₂.comap (algebraMap ↥L K') → B = A₂) :
    False := by
  -- `K'` is a separable closure of `L` as well
  have : IsSepClosure ↥L K' := ⟨IsSepClosure.sep_closed K, inferInstance⟩
  -- the two places of `L` cut out by `A₁` and `A₂` are distinct
  have hne' : A₁.comap (algebraMap ↥L K') ≠ A₂.comap (algebraMap ↥L K') := by
    intro h
    exact hne (hA₁ A₂ h.symm).symm
  -- each of them has a unique extension to the separable closure, hence is Henselian
  have hhen₁ : HenselianLocalRing (A₁.comap (algebraMap ↥L K')) :=
    Commons.RingTheory.Valuation.henselianLocalRing_of_unique_extension
      (A₁.comap (algebraMap ↥L K')) A₁ rfl fun W' hW' => hA₁ W' hW'
  have hhen₂ : HenselianLocalRing (A₂.comap (algebraMap ↥L K')) :=
    Commons.RingTheory.Valuation.henselianLocalRing_of_unique_extension
      (A₂.comap (algebraMap ↥L K')) A₂ rfl fun W' hW' => hA₂ W' hW'
  -- distinct places of an algebraic extension of a number field are independent
  have hind := Commons.NumberTheory.NumberField.Valuation.le_eq_top_of_comap_ne_top_of_ne
    L A₁ A₂ h₁ h₂ hne'
  -- F. K. Schmidt's theorem: `L` is separably closed
  have hsc : IsSepClosed ↥L :=
    Commons.RingTheory.Valuation.isSepClosed_of_two_independent_henselian _ _ h₁ h₂ hind
      hhen₁ hhen₂
  -- hence `L = K'`, contradicting the properness of `L`
  have hsurj : Function.Surjective (algebraMap ↥L K') :=
    (IsSepClosed.algebraMap_bijective ↥L K').2
  have htop : L = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨y, hy⟩ := hsurj x
    exact hy ▸ y.2
  exact hL htop

end Commons.NumberTheory.NumberField.Valuation
