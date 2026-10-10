import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Submission.NK.FrobeniusBridge.Core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The map `D_A → D_{P_L}` on finite levels is surjective

Let `K` be a number field with separable closure `K'`, let `A` be a place of `K'` over a finite
prime of `K`, and let `L ⊆ K'` be a finite normal intermediate field with prime `P_L` below `A`.
Write `D_A` for the decomposition group of `A` and `D_{P_L}` for the decomposition group of `P_L`
in `Gal(L/K)`.

The point of this file is the (easy) half of the local–global dictionary at a place: **every
element of `Gal(K'/K)` which acts trivially on the residue field of `L` at `P_L` agrees on `L`
with an element of `D_A`.**  The two ingredients are

* *trivial on the residue field of the level ⟹ lies in the level decomposition group*: the induced
  automorphism `f` of `𝓞 L` satisfies `f x - x ∈ P_L` for all `x`; hence `f` preserves `P_L`
  (`x ∈ P_L ↔ f x ∈ P_L`, using `x = f x - (f x - x)` and `f x = (f x - x) + x`) and therefore
  stabilises the valuation ring `𝒪_{L,P_L}` of `L` at `P_L`; this is
  `Commons.NumberTheory.RamificationInertia.smul_valuationSubringAtPrime_eq_map_galRestrict`;
* *surjectivity of `D_A → D_{P_L}`*: this is
  `Commons.FieldTheory.Galois.exists_mem_stabilizer_restrictNormalHom_eq`, whose proof uses the
  transitivity of the Galois action on the prolongations of a place
  (`Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq_isGalois`) plus
  `Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul`, and which is stated in the
  precise form needed here.

Convention: `NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A L g` is the residue-field triviality
at the level, phrased exactly through `𝓞 L`, `galRestrict` and the prime
`NK.Reconstruct.primeOfLevel`.
-/

namespace NK.ResidueFrob

open scoped Pointwise Classical

/-- **The level inertia lifts to the decomposition group of the place.**  If `g : Gal(K'/K)` acts
trivially on the residue field of the finite normal level `L` at the prime `P_L` below the place
`A`, then there is `h ∈ D_A` with `h = g` on `L`.

This is the field `inertia_surjective` of `NK.FrobeniusBridge.PlaceLevelBridgeCore`, stripped of
the local-inertia statement about the image under `D_A ≃* Gal(κ̄/κ)`: what remains is the
surjectivity of the restriction map `D_A → D_{P_L}`, i.e. the transitivity of the Galois action on
the places above `P_L`. -/
theorem exists_mem_decompositionGroup_restrictNormalHom_eq {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']
    (A : NK.FrobeniusBridge.FinitePlaceOf K K') (L : IntermediateField K K')
    [FiniteDimensional K L] [Normal K L] [NumberField ↥L] {g : Gal(K'/K)}
    (hg : NK.FrobeniusBridge.IsTrivialOnResidueAtLevel A L g) :
    ∃ h : Gal(K'/K),
      h ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1 ∧
        AlgEquiv.restrictNormalHom L h = AlgEquiv.restrictNormalHom L g := by
  -- The prime of `𝓞 L` below `A`, and its valuation ring in `L`.
  have hAne : A.1.comap (algebraMap ↥L K') ≠ ⊤ :=
    NK.Reconstruct.comap_level_ne_top A.2 L
  set P := NK.Reconstruct.primeOfLevel A.1 L hAne with hP
  have hPspec : A.1.comap (algebraMap ↥L K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L P :=
    NK.Reconstruct.primeOfLevel_spec A.1 L hAne
  -- The level automorphism `τ = g|_L` and its action on `𝓞 L`.
  set τ : ↥L ≃ₐ[K] ↥L := AlgEquiv.restrictNormalHom L g with hτ
  set e : NumberField.RingOfIntegers ↥L ≃ₐ[NumberField.RingOfIntegers K]
      NumberField.RingOfIntegers ↥L :=
    galRestrict (NumberField.RingOfIntegers K) K ↥L (NumberField.RingOfIntegers ↥L) τ with he
  have hg' : ∀ x : NumberField.RingOfIntegers ↥L, e x - x ∈ P.asIdeal := fun x => hg x
  -- `e` is trivial modulo `P`, hence preserves `P`.
  have hmem : ∀ x : NumberField.RingOfIntegers ↥L, e x ∈ P.asIdeal ↔ x ∈ P.asIdeal := by
    intro x
    constructor
    · intro hx
      have h := hg' x
      rw [show x = e x - (e x - x) from by ring]
      exact sub_mem hx h
    · intro hx
      have h := hg' x
      rw [show e x = (e x - x) + x from by ring]
      exact add_mem h hx
  have hmap : Ideal.map e P.asIdeal = P.asIdeal := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      exact (hmem x).mpr hx
    · intro x hx
      have hy : e.symm x ∈ P.asIdeal := (hmem (e.symm x)).mp (by simpa using hx)
      have h := Ideal.mem_map_of_mem e hy
      rwa [AlgEquiv.apply_symm_apply] at h
  -- Hence `τ` stabilises the valuation ring of `L` at `P`.
  have hstab : τ • IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L P =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L P :=
    Commons.NumberTheory.RamificationInertia.smul_valuationSubringAtPrime_eq_map_galRestrict
      P P τ hmap.symm
  -- i.e. `τ` lies in the level decomposition group `D_{P_L} = D_{A ∩ L}`.
  have hτmem : τ ∈ MulAction.stabilizer (↥L ≃ₐ[K] ↥L) (A.1.comap (algebraMap ↥L K')) := by
    rw [MulAction.mem_stabilizer_iff, hPspec]
    exact hstab
  -- The restriction map on the decomposition groups is surjective.
  obtain ⟨σ, hσmem, hσres⟩ :=
    Commons.FieldTheory.Galois.exists_mem_stabilizer_restrictNormalHom_eq
      (F := K) (K' := K') A.1 A.2 L τ hτmem
  exact ⟨σ, hσmem, by rw [hσres, hτ]⟩

end NK.ResidueFrob
