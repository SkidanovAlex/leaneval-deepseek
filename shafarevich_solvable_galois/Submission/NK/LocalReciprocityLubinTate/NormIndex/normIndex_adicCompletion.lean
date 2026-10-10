import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.NK.LocalArtin.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u

/-!
# The norm index theorem for the `p`-adic completion of a number field at a finite place

Let `K` be a number field and `Q` a finite place of `K` (a height-one prime of the ring of
integers `𝓞 K`).  The completion `F = Q.adicCompletion K` is a nonarchimedean local field of
characteristic `0` — a finite extension of `ℚ_p` — and this file proves the **norm index theorem**

  `[Fˣ : N_{L/F} Lˣ] = [L : F]`

at every finite abelian Galois level `L ≤ F^{ab}` of its maximal abelian extension, i.e.
`NK.LocalArtin.NormIndex F (SeparableClosure F)`.

This is the local norm index theorem (a form of the Herbrand quotient / Brauer computation
`Ĥ⁰(Gal(L/F), Lˣ) ≅ ℤ/[L:F]`), and it is one of the two inputs of the reduction
`KernelCondition + NormIndex ⟹ ReciprocityMap` of `NK.LocalArtin.Reduction`.

## Route

The mathematics is entirely contained in the shared commons lemma

`Commons.NumberTheory.NumberField.Completion.abelian_local_norm_index_at_base`,

which computes `Nat.card (Bˣ ⧸ N_{E/B} Eˣ) = Nat.card Gal(E/B)` for a finite extension `B` of
`Q.adicCompletion K` and a finite *abelian* Galois extension `E/B`.  Here `Q.adicCompletion K`
plays the role of the base field `B` and the level `L` the role of `E`; the two further inputs are

* `NK.LocalCFT.NormGroup.normGroup_eq_iff_commutative_gal L`: the Galois group of any normal
  level `L` of `F^{ab}` is commutative (it is a quotient of the commutative group
  `Gal(F^{ab}/F)`), which is exactly the `hcomm` hypothesis of the commons lemma;
* `NK.LocalCFT.NormGroup.instIsGaloisLevelOfMaxAbelian L`: a normal level of `F^{ab}` is a
  *Galois* extension of `F`, since `F^{ab}/F` is separable.

Finally `IsGalois.card_aut_eq_finrank` turns `Nat.card Gal(L/F)` into `[L : F]`, and
`Subgroup.index_eq_card` turns the index of the norm group into the cardinality of the quotient.
-/

set_option linter.style.haveILetI false

open scoped Classical

namespace NK.LocalReciprocityLubinTate.NormIndex

/-- **The norm index theorem for the `p`-adic completion of a number field.**

For a number field `K` and a finite place `Q` of `K`, at every finite abelian Galois level
`L` of the maximal abelian subextension of a separable closure of `F = Q.adicCompletion K`, the
norm group `N_{L/F} Lˣ` has index `[L : F]` in `Fˣ`. -/
theorem normIndex_adicCompletion {K : Type u} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    NK.LocalArtin.NormIndex (Q.adicCompletion K) (SeparableClosure (Q.adicCompletion K)) := by
  intro L hfd hnorm
  haveI : FiniteDimensional (Q.adicCompletion K) L := hfd
  haveI : Normal (Q.adicCompletion K) L := hnorm
  rw [Subgroup.index_eq_card]
  change Nat.card ((Q.adicCompletion K)ˣ ⧸
      (MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) : ↥L →* (Q.adicCompletion K)))))
    = Module.finrank (Q.adicCompletion K) ↥L
  rw [Commons.NumberTheory.NumberField.Completion.abelian_local_norm_index_at_base (K := K) Q
        (B := Q.adicCompletion K) (E := ↥L)
        (NK.LocalCFT.NormGroup.normGroup_eq_iff_commutative_gal L)]
  exact IsGalois.card_aut_eq_finrank (Q.adicCompletion K) ↥L

end NK.LocalReciprocityLubinTate.NormIndex
