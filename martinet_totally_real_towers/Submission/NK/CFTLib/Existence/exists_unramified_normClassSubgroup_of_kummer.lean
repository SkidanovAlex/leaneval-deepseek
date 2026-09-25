import Mathlib
import Submission.NK.CFTLib.ArtinIdeal
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.CFTLib.Existence.exists_galois_normClassSubgroup_le_of_kummer
import Submission.NK.CFTLib.Existence.exists_intermediateField_normClassSubgroup_eq_of_index_prime
import Submission.NK.CFTLib.Existence.unramifiedOfIntegralIdeles

/-!
# The existence theorem at prime index, in the Kummer case

Over a number field `K` containing a primitive `p`-th root of unity, every open finite-index
subgroup `V ≤ C_K` of index `p` containing the image of the integral idèles is the norm class
subgroup of an everywhere unramified Galois extension of degree `p`.

The three ingredients are

* `NK.CFTLib.Existence.exists_galois_normClassSubgroup_le_of_kummer` (Milne 9.3): `V` contains the
  norm class subgroup of a finite abelian extension `L₀/K`;
* `NK.CFTLib.Existence.exists_intermediateField_normClassSubgroup_eq_of_index_prime` (Milne 9.1,
  the norm-group correspondence at index `p`): a subfield `E ⊆ L₀` of degree `p` with
  `N_{E/K}C_E = V`;
* `NK.CFTLib.Existence.isUnramified_of_normClassSubgroup_le_integralIdeles_safe`: a degree-`p`
  Galois extension whose norm class subgroup contains the image of the integral idèles is unramified
  (its arithmetic input, Hilbert reciprocity in the one-place form, is the hypothesis `hgap`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Existence

open NK.GlobalCFT

theorem exists_unramified_normClassSubgroup_of_kummer
    (hARL : NK.CFTLib.ArtinReciprocityIdeal) (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    {K : Type} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup (IdeleClassGroup K)) (hV : V.FiniteIndex)
    (hopen : IsOpen (V : Set (IdeleClassGroup K))) (hidx : V.index = p)
    (hray : (Idele.integralIdeles K).map (IdeleClassGroup.mk K) ≤ V)
    (hgap : HasseNormOnePlace) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      IsGalois K L ∧ Idele.normClassSubgroup K L = V ∧ Module.finrank K L = p ∧
      differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) = ⊤ ∧
      IsUnramifiedAtInfinitePlaces K L := by
  classical
  obtain ⟨L₀, hF₀, hN₀, hA₀, hfd₀, hgal₀, hcomm₀, hle₀⟩ :=
    exists_galois_normClassSubgroup_le_of_kummer (K := K) hARL hFC p hζ V hV hopen hidx
  letI : Field L₀ := hF₀
  letI : NumberField L₀ := hN₀
  letI : Algebra K L₀ := hA₀
  letI : FiniteDimensional K L₀ := hfd₀
  haveI : IsGalois K L₀ := hgal₀
  haveI : IsMulCommutative (L₀ ≃ₐ[K] L₀) := hcomm₀
  obtain ⟨E, hEgal, hEnorm, hEfin⟩ :=
    exists_intermediateField_normClassSubgroup_eq_of_index_prime (K := K) (L := L₀) hARL hFC
      V hidx hle₀
  have hray' : (Idele.integralIdeles K).map (IdeleClassGroup.mk K) ≤
      Idele.normClassSubgroup K ↥E := by
    rw [hEnorm]; exact hray
  obtain ⟨hdiff, hinf⟩ :=
    isUnramified_of_normClassSubgroup_le_integralIdeles_safe (K := K) (L := ↥E) p hEfin hgap hray'
  exact ⟨↥E, inferInstance, inferInstance, inferInstance, inferInstance,
    hEgal, hEnorm, hEfin, hdiff, hinf⟩

end NK.CFTLib.Existence
