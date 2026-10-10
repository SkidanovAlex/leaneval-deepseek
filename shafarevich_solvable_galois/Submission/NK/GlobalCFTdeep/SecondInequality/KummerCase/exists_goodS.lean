import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.exists_finset_TIdeles_surjective
import Submission.NK.GlobalCFTdeep.Herbrand.top_eq_principal_sup_TIdeles
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A finite set of places `S` adapted to the Kummer case of the second inequality

Given a finite Galois extension `L / K` of number fields, a rational prime `p` and a
nonzero `a ∈ K`, this file produces a finite set `S` of places of `K` which

* contains every archimedean place of `K`,
* contains every finite place of `K` above `p`,
* contains every finite place of `K` which ramifies in `L`,
* is large enough that `a` is an `S`-unit: `a ∈ U(S)`, and
* is large enough that the `S`-idèles together with the principal idèles generate the
  whole idèle group: `⊤ = Kˣ · 𝕀_{K,S}`.

The mathematical content is that the sets in question are finite: there are finitely many
archimedean places, finitely many primes above the rational prime `p` (a nonzero ideal of the
Dedekind domain `𝓞 K` has finitely many prime divisors), finitely many ramified primes
(`Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one`), and the unit `a` is a
local unit at all but finitely many places (the restricted-product condition).  The last
condition is the one used for the Herbrand-quotient computation; it is achieved by enlarging an
arbitrary finite set with the class-group support produced by
`NK.GlobalCFTdeep.Herbrand.exists_finset_TIdeles_surjective`, since `𝕀_{K,S}` is monotone in
`S` and the class group is always captured (equivalently: `⊤ = Kˣ · 𝕀_{K,S}`
for `S` such that the primes of `S` generate the class group).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

open NK.GlobalCFT

/-- Only finitely many finite places of `K` lie above the rational prime `p`: they are among the
prime divisors of the nonzero ideal `(p) ⊆ 𝓞 K`, and a nonzero ideal of a Dedekind domain has
only finitely many prime divisors. -/
theorem finite_setOf_prime_mem_ringOfIntegers {K : Type} [Field K] [NumberField K]
    {p : ℕ} (hp : p.Prime) :
    {q : HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ q.asIdeal}.Finite := by
  have hD : (Ideal.span {(p : 𝓞 K)} : Ideal (𝓞 K)) ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hinj : Function.Injective (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal) :=
    fun x y h => by
      have h' : x.asIdeal = y.asIdeal := h
      ext z; rw [h']
  -- the prime divisors of `(p)` are finite
  have hfin : (((fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal) ⁻¹'
      ((UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span {(p : 𝓞 K)})).toFinset : Set (Ideal (𝓞 K))))).Finite :=
    Set.Finite.preimage (fun _ _ _ _ h => hinj h) (Finset.finite_toSet _)
  refine Set.Finite.subset hfin ?_
  intro q hq
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
  exact (Ideal.mem_normalizedFactors_iff hD).mpr
    ⟨q.isPrime, Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hq)⟩

theorem exists_goodS {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} (hp : p.Prime) {a : K} (ha : a ≠ 0) :
    ∃ S : Finset (NK.GlobalCFT.Place K),
      (∀ w : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite w ∈ S) ∧
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), (p : NumberField.RingOfIntegers K) ∈ q.asIdeal → NK.GlobalCFT.Place.ofFinite q ∈ S) ∧
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        (∃ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L), Q.asIdeal.LiesOver q.asIdeal ∧
          Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1) → NK.GlobalCFT.Place.ofFinite q ∈ S) ∧
      (Units.mk0 a ha ∈ NK.GlobalCFTdeep.TUnits (L := K) (S : Set (NK.GlobalCFT.Place K))) ∧
      ((⊤ : Subgroup (NK.GlobalCFT.Idele K)) = NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.GlobalCFTdeep.TIdeles (S : Set (NK.GlobalCFT.Place K))) := by
  classical
  -- a finite set of places whose `T`-idèles surject onto the class group of `𝓞 K`
  obtain ⟨T₀, hT₀⟩ :=
    NK.GlobalCFTdeep.Herbrand.exists_finset_TIdeles_surjective (L := K)
  -- the places at which `a` is not a local unit
  have hbad : {v : Place K | Units.map (algebraMap K (Place.localField K v))
      (Units.mk0 a ha) ∉ Place.localUnits K v}.Finite :=
    Filter.eventually_cofinite.mp
      (Idele.eventually_localUnits_principal (K := K) (Units.mk0 a ha))
  -- the finite places of `K` above `p`
  have hpfin : {q : HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ q.asIdeal}.Finite :=
    finite_setOf_prime_mem_ringOfIntegers hp
  -- the primes of `𝓞 L` ramifying over `𝓞 K`
  have hramfin : {q : HeightOneSpectrum (𝓞 L) | q.asIdeal.ramificationIdx (𝓞 K) ≠ 1}.Finite :=
    Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one (K := K) (L := L)
  -- the place of `K` below a place of `L`, as `Norm.globalCFT_placeUnder`
  let A : Finset (Place K) := Finset.univ.image Place.ofInfinite
  let B : Finset (Place K) := hpfin.toFinset.image Place.ofFinite
  let C : Finset (Place K) := hbad.toFinset
  let D : Finset (Place K) :=
    hramfin.toFinset.image
      (fun Q => Norm.globalCFT_placeUnder (K := K) (L := L) (Place.ofFinite Q))
  let S : Finset (Place K) := A ∪ B ∪ C ∪ D ∪ T₀
  have memA : ∀ x, x ∈ A → x ∈ S := by
    intro x hx
    show x ∈ A ∪ B ∪ C ∪ D ∪ T₀
    exact Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hx)))
  have memB : ∀ x, x ∈ B → x ∈ S := by
    intro x hx
    show x ∈ A ∪ B ∪ C ∪ D ∪ T₀
    exact Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hx)))
  have memC : ∀ x, x ∈ C → x ∈ S := by
    intro x hx
    show x ∈ A ∪ B ∪ C ∪ D ∪ T₀
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
  have memD : ∀ x, x ∈ D → x ∈ S := by
    intro x hx
    show x ∈ A ∪ B ∪ C ∪ D ∪ T₀
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have memT : ∀ x, x ∈ T₀ → x ∈ S := by
    intro x hx
    show x ∈ A ∪ B ∪ C ∪ D ∪ T₀
    exact Finset.mem_union_right _ hx
  refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
  · -- all archimedean places are in `S`
    intro w
    exact memA _ (Finset.mem_image_of_mem _ (Finset.mem_univ w))
  · -- all places above `p` are in `S`
    intro q hq
    exact memB _ (Finset.mem_image_of_mem _ (hpfin.mem_toFinset.mpr hq))
  · -- all places of `K` which ramify in `L` are in `S`
    intro q h
    obtain ⟨Q, hLie, hram⟩ := h
    have hQ : Q ∈ hramfin.toFinset := hramfin.mem_toFinset.mpr hram
    have hDmem : Norm.globalCFT_placeUnder (K := K) (L := L) (Place.ofFinite Q) ∈ D :=
      Finset.mem_image_of_mem _ hQ
    have heq : Norm.globalCFT_placeUnder (K := K) (L := L) (Place.ofFinite Q) =
        Place.ofFinite q :=
      NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
        (Norm.liesOver_globalCFT_placeUnder (K := K) (L := L) (Place.ofFinite Q))
        (Place.liesOver_ofFinite hLie)
    rw [← heq]
    exact memD _ hDmem
  · -- `a` is an `S`-unit
    rw [NK.GlobalCFTdeep.mem_TUnits]
    intro w hw
    by_contra hcon
    exact hw (memC _ (hbad.mem_toFinset.mpr hcon))
  · -- the `S`-idèles generate the class group
    refine NK.GlobalCFTdeep.Herbrand.top_eq_principal_sup_TIdeles (S : Set (Place K)) ?_
    intro c
    obtain ⟨u, hu, hc⟩ := hT₀ c
    exact ⟨u, fun v hv => hu v (fun hmem => hv (memT v hmem)), hc⟩

end NK.GlobalCFTdeep.SecondInequality.KummerCase
