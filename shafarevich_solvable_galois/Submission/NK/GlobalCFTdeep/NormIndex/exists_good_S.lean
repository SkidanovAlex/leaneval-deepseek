import Mathlib
import Submission.NK.GlobalCFTdeep.NormIndex.Defs
import Submission.NK.GlobalCFTdeep.Herbrand.top_eq_principal_sup_TIdeles
import Submission.NK.GlobalCFTdeep.Herbrand.exists_finset_TIdeles_surjective
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
import Submission.NK.GlobalCFT.Norm.globalCFT_abs_normIdeleHom
import Submission.Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A finite set of places `S` adapted to the finiteness of the idèlic norm index

For a finite extension `L / K` of number fields this file produces a finite set `S` of places
of `K` which

* contains every archimedean place of `K`,
* contains every finite place of `K` which ramifies in `L`, and
* is large enough that `⊤ = Kˣ · 𝕀_{K,S}`.

The last condition is the one used to run the group-theoretic step
`NK.GlobalCFTdeep.finiteIndex_sup_of_sup_eq_top`: the `S`-idèles are large (they surject onto
the class group by `NK.GlobalCFTdeep.Herbrand.exists_finset_TIdeles_surjective`), which is
exactly `⊤ = Kˣ · 𝕀_{K,S}` by `NK.GlobalCFTdeep.Herbrand.top_eq_principal_sup_TIdeles`.

The mathematical content is finiteness: finitely many archimedean places, finitely many ramified
primes (`Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one`), and a finite
support for the class group.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.NormIndex

open NK.GlobalCFT

theorem exists_good_S {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] : ∃ S : Finset (NK.GlobalCFT.Place K), (∀ v : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite v ∈ S) ∧ (∀ (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), q.asIdeal.LiesOver Q.asIdeal → NK.GlobalCFT.Place.ofFinite Q ∉ S → q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) ∧ (⊤ : Subgroup (NK.GlobalCFT.Idele K)) = NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.GlobalCFTdeep.TIdeles (L := K) (S : Set (NK.GlobalCFT.Place K)) := by
  classical
  -- a finite set of places whose `T`-idèles surject onto the class group of `𝓞 K`
  obtain ⟨T₀, hT₀⟩ :=
    NK.GlobalCFTdeep.Herbrand.exists_finset_TIdeles_surjective (L := K)
  -- the primes of `𝓞 L` ramifying over `𝓞 K`
  have hramfin : {q : HeightOneSpectrum (𝓞 L) | q.asIdeal.ramificationIdx (𝓞 K) ≠ 1}.Finite :=
    Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one (K := K) (L := L)
  -- the archimedean places of `K`
  let A : Finset (Place K) := Finset.univ.image Place.ofInfinite
  -- the places of `K` below a ramified prime of `𝓞 L`
  let D : Finset (Place K) := hramfin.toFinset.image
    (fun q => Norm.globalCFT_placeUnder (K := K) (L := L) (Place.ofFinite q))
  let S : Finset (Place K) := A ∪ D ∪ T₀
  have memA : ∀ x ∈ A, x ∈ S := fun x hx =>
    Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have memD : ∀ x ∈ D, x ∈ S := fun x hx =>
    Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have memT : ∀ x ∈ T₀, x ∈ S := fun x hx => Finset.mem_union_right _ hx
  refine ⟨S, ?_, ?_, ?_⟩
  · -- all archimedean places are in `S`
    intro v
    exact memA _ (Finset.mem_image_of_mem _ (Finset.mem_univ v))
  · -- every finite place of `K` below a ramified prime of `𝓞 L` lies in `S`
    intro q Q hLie hQnot
    by_contra hram
    have hq : q ∈ hramfin.toFinset := hramfin.mem_toFinset.mpr hram
    have hDmem : Norm.globalCFT_placeUnder (K := K) (L := L) (Place.ofFinite q) ∈ D :=
      Finset.mem_image_of_mem _ hq
    have heq : Norm.globalCFT_placeUnder (K := K) (L := L) (Place.ofFinite q) = Place.ofFinite Q :=
      NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
        (Norm.liesOver_globalCFT_placeUnder (K := K) (L := L) (Place.ofFinite q))
        (Place.liesOver_ofFinite hLie)
    exact hQnot (by rw [← heq]; exact memD _ hDmem)
  · -- the `S`-idèles together with the principal idèles generate everything
    refine NK.GlobalCFTdeep.Herbrand.top_eq_principal_sup_TIdeles (L := K)
      (S : Set (Place K)) ?_
    intro c
    obtain ⟨u, hu, hc⟩ := hT₀ c
    exact ⟨u, fun v hv => hu v (fun hmem => hv (memT v hmem)), hc⟩

end NK.GlobalCFTdeep.NormIndex
