import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Topology.Algebra.Group.Quotient
import Submission.NK.CFTLib.ArtinReciprocityIdealProved
import Submission.NK.CFTLib.Existence.exists_galois_normClassSubgroup_eq_of_cyclotomic_descent_deg
import Submission.NK.CFTLib.Existence.exists_galois_normClassSubgroup_le_of_kummer
import Submission.NK.CFTLib.Existence.index_comap_normClassHom_eq_prime
import Submission.NK.CFTLib.HR.TransferAux.localLevelMap_injective_vanishing
import Submission.NK.CFTLib.HRdescent.localConditionCyclotomicPrime
import Submission.NK.CFTLib.fundamentalClassElement
import Submission.NK.NUV2.ARL.HR.locUnits_inflation_eq_zero_iff
import Submission.NK.NUV2.ArtinBridge.isOpen_comap_normClassHom
import Submission.NK.NUV2.ChebAux.Transfer.cycClassOf_translation
import Submission.NK.NUV2.ChebAux.Transfer.locUnits_res_inflation_eq_zero
import Submission.NK.NUV2.LC.localNormFinite_range_iff_val_pow
import Submission.NK.NUV2.kernelCondition_all

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute

/-- **The existence theorem at prime index, Kummer case.**

Over a number field `K` containing a primitive `p`-th root of unity, every open finite-index
subgroup `V ≤ C_K` of index `p` is the norm class subgroup `N_{L/K} C_L` of a finite Galois
extension `L/K` of degree `p`.

The argument is Milne's: first find a finite abelian extension `L₀/K` with
`N_{L₀/K} C_{L₀} ≤ V` (the Kummer-field construction, `exists_galois_normClassSubgroup_le_of_kummer`),
then extract the intermediate field `E ≤ L₀` cut out by the image of `V` under the Artin
isomorphism `C_K ⧸ N_{L₀/K}C_{L₀} ≃* Gal(L₀/K)`; the Galois correspondence at prime index
(`exists_intermediateField_normClassSubgroup_eq_of_index_prime`) identifies its norm group with
`V` and its degree with `p`. -/
theorem exists_normClassSubgroup_eq_of_kummer
    (hARL : NK.CFTLib.ArtinReciprocityIdeal) (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    {K : Type} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup (NK.GlobalCFT.IdeleClassGroup K)) (hV : V.FiniteIndex)
    (hopen : IsOpen (V : Set (NK.GlobalCFT.IdeleClassGroup K))) (hidx : V.index = p) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      IsGalois K L ∧ NK.GlobalCFT.Idele.normClassSubgroup K L = V ∧ Module.finrank K L = p := by
  classical
  -- Step 1: a finite abelian (hence Galois) extension `L₀/K` whose norm class subgroup lies in `V`.
  obtain ⟨L₀, hF₀, hN₀, hA₀, hfd₀, hgal₀, hcomm₀, hle₀⟩ :=
    NK.CFTLib.Existence.exists_galois_normClassSubgroup_le_of_kummer (K := K) hARL hFC p hζ V hV
      hopen hidx
  letI : Algebra K L₀ := hA₀
  letI : FiniteDimensional K L₀ := hfd₀
  haveI : IsGalois K L₀ := hgal₀
  haveI : IsMulCommutative (L₀ ≃ₐ[K] L₀) := hcomm₀
  -- Step 2: cut out the intermediate field `E` with norm class subgroup exactly `V`, degree `p`.
  obtain ⟨E, hEgal, hEnorm, hEfin⟩ :=
    NK.CFTLib.Existence.exists_intermediateField_normClassSubgroup_eq_of_index_prime
      (K := K) (L := L₀) hARL hFC V hidx hle₀
  exact ⟨↥E, inferInstance, inferInstance, inferInstance, inferInstance, hEgal, hEnorm, hEfin⟩

end Work.SSGRoute
