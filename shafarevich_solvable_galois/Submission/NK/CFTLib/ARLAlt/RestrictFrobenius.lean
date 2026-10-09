import Mathlib
import Submission.NK.CFTLib.ARLAlt.Setup
import Submission.NK.CFTLib.Arl.prod_frobAtPrime_ramificationIdx_eq_one
import Submission.NK.CFTLib.ArtinReciprocityIdeal.langX2KernelLe
import Submission.NK.CFTLib.ARL.isGalois_cyclotomicField_over_base
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Frobenius elements under restriction of the ambient field

Two elementary consistencies of chosen Frobenius elements, used by the transfer:

* `restrictNormalHom_frobAtPrime_ofLe`: restricting a Frobenius at a prime `𝔮` of the auxiliary
  field `E` from the cyclotomic ambient `Ω = L(ζ_M)` to the composite `E·L` gives (the chosen)
  Frobenius at `𝔮` for the extension `E·L/E`;
* `restrictGalEquiv_frobAtPrime`: the image of a Frobenius at `𝔮` (for `Ω/E`) under the restriction
  map `Gal(Ω/E) →* Gal(L/K)` is the `f(𝔮 | 𝔮 ∩ K)`-th power of the Frobenius at `𝔮 ∩ 𝓞 K` for
  `L/K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.CFTLib.ARLAlt

/-- **Restriction of a Frobenius from `Ω` to the composite `E·L`.** -/
theorem restrictNormalHom_frobAtPrime_ofLe (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (M : ℕ) [NeZero M] (E LE : IntermediateField K (CyclotomicField M L)) (h : E ≤ LE)
    (hLΩ : LImage (K := K) (L := L) M ≤ LE) (hsup : E ⊔ LImage (K := K) (L := L) M = LE)
    [IsGalois ↥E ↥(ofLe E LE h)]
    [IsMulCommutative (↥(ofLe E LE h) ≃ₐ[↥E] ↥(ofLe E LE h))]
    (𝔮 : NK.Chebotarev.PrimeIdeal ↥E)
    (hunr : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E)
      (L := ↥(ofLe E LE h)) 𝔮) :
    AlgEquiv.restrictNormalHom (F := ↥E) (K₁ := CyclotomicField M L) ↥(ofLe E LE h)
        (NK.Chebotarev.frobAtPrime (K := ↥E) (L := CyclotomicField M L) 𝔮)
      = NK.Chebotarev.frobAtPrime (K := ↥E) (L := ↥(ofLe E LE h)) 𝔮 := by
  classical
  haveI hGalΩ : IsGalois K (CyclotomicField M L) :=
    NK.CFTLib.ARL.isGalois_cyclotomicField_over_base (K := K) (L := L) M
  -- the chosen Frobenius at `𝔮` for `Ω/E`
  have hσ : NK.Chebotarev.IsFrobAtPrime (K := ↥E) (L := CyclotomicField M L) 𝔮
      (NK.Chebotarev.frobAtPrime (K := ↥E) (L := CyclotomicField M L) 𝔮) := by
    rw [NK.Chebotarev.frobAtPrime,
      dif_pos (NK.Chebotarev.exists_isFrobAtPrime (K := ↥E) (L := CyclotomicField M L) 𝔮)]
    exact (NK.Chebotarev.exists_isFrobAtPrime (K := ↥E) (L := CyclotomicField M L) 𝔮).choose_spec
  obtain ⟨𝔔, h𝔔lies, h𝔔frob⟩ := hσ
  -- its restriction to `E·L` is a Frobenius at `𝔮`
  have hres : NK.Chebotarev.IsFrobAtPrime (K := ↥E) (L := ↥(ofLe E LE h)) 𝔮
      (AlgEquiv.restrictNormalHom (F := ↥E) (K₁ := CyclotomicField M L) ↥(ofLe E LE h)
        (NK.Chebotarev.frobAtPrime (K := ↥E) (L := CyclotomicField M L) 𝔮)) := by
    set P : NK.Chebotarev.PrimeIdeal ↥(ofLe E LE h) :=
      𝔔.under (NumberField.RingOfIntegers ↥(ofLe E LE h)) with hP
    have hPlies : P.asIdeal.LiesOver 𝔮.asIdeal := by
      refine ⟨?_⟩
      show 𝔮.asIdeal = (𝔔.asIdeal.under (NumberField.RingOfIntegers ↥(ofLe E LE h))).under
        (NumberField.RingOfIntegers ↥E)
      rw [Ideal.under_under]
      exact h𝔔lies.over
    refine ⟨P, hPlies, ?_⟩
    rw [NK.Chebotarev.isFrobAt_def]
    intro x
    rw [show Nat.card (NumberField.RingOfIntegers ↥E ⧸
        P.asIdeal.under (NumberField.RingOfIntegers ↥E)) =
        Nat.card (NumberField.RingOfIntegers ↥E ⧸ 𝔮.asIdeal) from by rw [hPlies.over]]
    refine (Ideal.mem_under (NumberField.RingOfIntegers ↥(ofLe E LE h)) 𝔔.asIdeal).mpr ?_
    have h1 : galRestrict (NumberField.RingOfIntegers ↥E) ↥E (CyclotomicField M L)
        (NumberField.RingOfIntegers (CyclotomicField M L))
        (NK.Chebotarev.frobAtPrime (K := ↥E) (L := CyclotomicField M L) 𝔮)
        (algebraMap (NumberField.RingOfIntegers ↥(ofLe E LE h))
          (NumberField.RingOfIntegers (CyclotomicField M L)) x)
        - (algebraMap (NumberField.RingOfIntegers ↥(ofLe E LE h))
          (NumberField.RingOfIntegers (CyclotomicField M L)) x)
            ^ Nat.card (NumberField.RingOfIntegers ↥E ⧸ 𝔮.asIdeal) ∈ 𝔔.asIdeal := by
      have h2 := h𝔔frob (algebraMap (NumberField.RingOfIntegers ↥(ofLe E LE h))
        (NumberField.RingOfIntegers (CyclotomicField M L)) x)
      rwa [show Nat.card (NumberField.RingOfIntegers ↥E ⧸
          (𝔔.asIdeal.under (NumberField.RingOfIntegers ↥E))) =
          Nat.card (NumberField.RingOfIntegers ↥E ⧸ 𝔮.asIdeal)
        from by rw [h𝔔lies.over]] at h2
    rw [map_sub, map_pow, NK.CFTLib.Arl.galRestrict_restrictNormalHom_apply (K := ↥E)
      (E' := CyclotomicField M L) (ofLe E LE h) _ x]
    exact h1
  -- uniqueness of the Frobenius at `𝔮` in the abelian extension `E·L/E`
  have huniq := (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq
    (K := ↥E) (L := ↥(ofLe E LE h))
    (fun a b => IsMulCommutative.is_comm.comm a b) 𝔮 hunr
    (AlgEquiv.restrictNormalHom (F := ↥E) (K₁ := CyclotomicField M L) ↥(ofLe E LE h)
      (NK.Chebotarev.frobAtPrime (K := ↥E) (L := CyclotomicField M L) 𝔮))).mp hres
  exact huniq.symm

end NK.CFTLib.ARLAlt
