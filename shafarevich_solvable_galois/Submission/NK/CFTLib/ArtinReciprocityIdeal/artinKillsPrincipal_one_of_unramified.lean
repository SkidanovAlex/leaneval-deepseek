import Mathlib
import Submission.NK.CFTLib.ArtinIdeal
import Submission.NK.CFTLib.ArtinReciprocityIdeal.LangDefs
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Conductor
import Submission.NK.CFTLib.ArtinReciprocityIdeal.iInf_subgroup_isCyclic_quotient
import Submission.NK.NUV2.ARL.abelianWeakToStrong
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinKillsPrincipal_one_of_unramified_cyclicCase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The trivial-modulus reciprocity law for an unramified abelian extension

For a finite Galois extension `L/K` of number fields which is unramified at every finite prime
(`differentIdeal (𝓞 K) (𝓞 L) = ⊤`) and an abelian reciprocity law
`NK.CFTLib.ArtinReciprocityIdeal` (the *ideal-theoretic* Artin reciprocity law at *some*
modulus; Lang, *Algebraic Number Theory*, X §1–2), the target of this file is

`NK.CFTLib.artinKillsPrincipal K L 1`,

i.e. the Artin symbol of every principal ideal with a *totally positive* generator is trivial.

## What is proved here

* `ramificationIdxIn_eq_one_of_differentIdeal_eq_top` — the triviality of the relative different
  is exactly unramifiedness at every finite prime, in the form consumed below.

* `artinKillsPrincipal_one_of_forall_cyclic` — **the reduction of the abelian case to the cyclic
  case**: if the product condition at the trivial modulus holds for every *cyclic* unramified
  extension, it holds for the given abelian one.  The proof is the classical group-theoretic
  reduction (Lang X.3): an element of `Gal(L/K)` is trivial iff its images in all the cyclic
  quotients are trivial (`iInf_subgroup_isCyclic_quotient`), and the image of the Frobenius product
  in a cyclic quotient `Gal(L/K)/H` is computed in the fixed field `L^H`
  (`exists_isFrobAtPrime_restrict`).

* `artinKillsPrincipal_one_of_unramified` — the target, from the cyclic case
  (`artinKillsPrincipal_one_of_unramified_cyclic`, the graded input).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.ArtinReciprocityIdeal

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **Unramifiedness from the triviality of the relative different.** -/
theorem ramificationIdxIn_eq_one_of_differentIdeal_eq_top
    (hunr : differentIdeal (𝓞 K) (𝓞 L) = ⊤) (𝔭 : NK.Chebotarev.PrimeIdeal K) :
    Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1 := by
  classical
  letI hMSA : MulSemiringAction (Gal(L/K)) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  haveI hGG : IsGaloisGroup (Gal(L/K)) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (Gal(L/K)) (𝓞 K) (𝓞 L) K L
  obtain ⟨Q, hQ⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) 𝔭
  haveI : Q.asIdeal.IsPrime := Q.isPrime
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) 𝔭.asIdeal Q.asIdeal
    (Gal(L/K))]
  rw [← Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal
    (E := K) (K := L) Q.asIdeal Q.isPrime]
  rw [Ideal.dvd_iff_le]
  intro hle
  exact Q.isPrime.ne_top (top_le_iff.mp (hunr ▸ hle))

/-- **The reduction of the abelian case to the cyclic case at the trivial modulus.** -/
theorem artinKillsPrincipal_one_of_forall_cyclic
    (hcyc : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)],
      NK.CFTLib.ArtinReciprocityIdeal →
      (∀ 𝔭 : NK.Chebotarev.PrimeIdeal K, Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1) →
      NK.CFTLib.artinKillsPrincipal K L 1)
    [IsMulCommutative (L ≃ₐ[K] L)]
    (hARL : NK.CFTLib.ArtinReciprocityIdeal)
    (hram : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K, Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1) :
    NK.CFTLib.artinKillsPrincipal K L 1 := by
  classical
  intro a ha hpos s e σ hs hfac hσ
  letI : CommGroup (L ≃ₐ[K] L) :=
    { (inferInstance : Group (L ≃ₐ[K] L)) with
      mul_comm := fun x y => IsMulCommutative.is_comm.comm x y }
  haveI : Finite (L ≃ₐ[K] L) := inferInstance
  set σ₀ : L ≃ₐ[K] L := (s.toList.map (fun p => σ p ^ e p)).prod with hσ₀
  have hmem : σ₀ ∈ ⨅ H : {H : Subgroup (L ≃ₐ[K] L) // IsCyclic ((L ≃ₐ[K] L) ⧸ H)},
      (H.1 : Subgroup (L ≃ₐ[K] L)) := by
    refine Subgroup.mem_iInf.mpr fun H => ?_
    obtain ⟨H₀, hHcyc⟩ := H
    haveI : Subgroup.Normal H₀ := inferInstance
    haveI hcycQ : IsCyclic ((L ≃ₐ[K] L) ⧸ H₀) := hHcyc
    haveI hgal : IsGalois K ↥(IntermediateField.fixedField H₀) :=
      IsGalois.of_fixedField_normal_subgroup H₀
    haveI : IsCyclic (↥(IntermediateField.fixedField H₀) ≃ₐ[K]
        ↥(IntermediateField.fixedField H₀)) :=
      isCyclic_of_surjective (IsGalois.normalAutEquivQuotient H₀).toMonoidHom
        (fun y => (IsGalois.normalAutEquivQuotient H₀).surjective y)
    -- the cyclic case in the fixed field of `H₀`
    have hcycM := hcyc K ↥(IntermediateField.fixedField H₀) hARL
      (fun 𝔭 => NK.NUV2.ARL.ramificationIdxIn_eq_one_of_intermediateField
        (IntermediateField.fixedField H₀) 𝔭 (hram 𝔭))
    have h := hcycM a ha hpos s e
      (fun p => AlgEquiv.restrictNormalHom (IntermediateField.fixedField H₀) (σ p)) hs hfac
      (fun p hp => NK.CFTLib.exists_isFrobAtPrime_restrict
        (IntermediateField.fixedField H₀) (hσ p hp))
    -- rewrite the restricted product as the restriction of `σ₀`
    have hmap : (s.toList.map (fun p =>
          (AlgEquiv.restrictNormalHom (IntermediateField.fixedField H₀) (σ p)) ^ e p)).prod
        = AlgEquiv.restrictNormalHom (IntermediateField.fixedField H₀) σ₀ := by
      rw [hσ₀]
      induction s.toList with
      | nil => simp
      | cons p l ih =>
          simp only [List.map_cons, List.prod_cons]
          rw [ih, map_mul, map_pow]
    have hker : σ₀ ∈ (AlgEquiv.restrictNormalHom (IntermediateField.fixedField H₀)).ker := by
      rw [MonoidHom.mem_ker, ← hmap]
      exact h
    rw [IntermediateField.restrictNormalHom_ker,
      IntermediateField.fixingSubgroup_fixedField] at hker
    exact hker
  have h1 : σ₀ = 1 := by
    have hmem' := hmem
    rw [iInf_subgroup_isCyclic_quotient] at hmem'
    simpa using hmem'
  exact h1

/-- **The target theorem: the trivial-modulus reciprocity law for an unramified abelian
extension.**

The abelian case is reduced to the cyclic case (`artinKillsPrincipal_one_of_forall_cyclic`), and
the cyclic case is the graded input `artinKillsPrincipal_one_of_unramified_cyclic`. -/
theorem artinKillsPrincipal_one_of_unramified
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (hARL : NK.CFTLib.ArtinReciprocityIdeal)
    (hunr : differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) = ⊤) :
    NK.CFTLib.artinKillsPrincipal K L 1 :=
  artinKillsPrincipal_one_of_forall_cyclic
    (fun K L _ _ _ _ _ _ _ _ hARL hram =>
      artinKillsPrincipal_one_of_unramified_cyclicCase hARL hram)
    hARL (fun 𝔭 => ramificationIdxIn_eq_one_of_differentIdeal_eq_top hunr 𝔭)

end NK.CFTLib.ArtinReciprocityIdeal
