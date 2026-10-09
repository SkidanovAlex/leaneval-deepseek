import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.CoreId
import Submission.Work.SSGRoute.ZDataMup.ZDataMupClean.SurjId
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.normKerId
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.cycloPrincipalId
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.indexLeId
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.mem_idealCoprimeGroupId_iff
import Submission.Work.SSGRoute.ZDataMup.IdealModulusContainmentProved
import Submission.Work.SSGRoute.ZDataMup.LTRecFamCrux.productFormula_cyclotomic_aux
import Submission.NK.GlobalCFTdeep.secondInequality_unconditional
import Submission.NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.ThetaRange
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cyclotomic cell for an ideal modulus

For a cyclotomic extension `Ω = k(ζ_n)`, a Galois intermediate field `M ⊆ Ω` with commutative Galois
group, and an ideal modulus `𝔪` of `k` whose support contains the primes dividing `(n)` at a level at
least that of `(n)` and which contains all the primes ramified in `M/k`, every fractional ideal
coprime to `𝔪` whose Artin symbol is trivial lies in `P(𝔪)·𝔑(𝔪)`.

The proof is the group-theoretic assembly of four leaf results:

* `cycloPrincipalId` (`P(𝔪) ⊆ ker` in the cyclotomic extension `Ω/k`, restricted to `M`),
* `normKerId` (`𝔑(𝔪) ⊆ ker`),
* `surjId_clean` (surjectivity of the Artin symbol on `I(𝔪)`),
* `indexLeId` (`[I(𝔪) : P(𝔪)·𝔑(𝔪)] ≤ [C_k : N C_M]`) and the second inequality
  `[C_k : N C_M] ≤ [M : k]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus

open NK.CFTLib.ArtinReciprocityIdeal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- **The cyclotomic cell with an ideal modulus.** -/
theorem cyclotomicCellKernelLeId_clean (k Ω : Type) [Field k] [NumberField k] [Field Ω] [NumberField Ω]
    [Algebra k Ω] [FiniteDimensional k Ω] [IsGalois k Ω] (n : ℕ) [NeZero n]
    [IsCyclotomicExtension {n} k Ω]
    (M : IntermediateField k Ω) [FiniteDimensional k M] [NumberField ↥M] [IsGalois k ↥M]
    [IsMulCommutative ((↥M) ≃ₐ[k] (↥M))]
    (𝔪 : Ideal (𝓞 k)) (h𝔪 : 𝔪 ≠ ⊥)
    (hsupp : ∀ 𝔭 : HeightOneSpectrum (𝓞 k), (n : 𝓞 k) ∈ 𝔭.asIdeal → DvdPrime 𝔪 𝔭)
    (hlev : ∀ 𝔭 : HeightOneSpectrum (𝓞 k), (n : 𝓞 k) ∈ 𝔭.asIdeal →
      (WithZero.exp (-(FractionalIdeal.count k 𝔭 (𝔪 : FractionalIdeal (𝓞 k)⁰ k) : ℤ)) :
        WithZero (Multiplicative ℤ))
        ≤ Valued.v (R := 𝔭.adicCompletion k) (Γ₀ := WithZero (Multiplicative ℤ))
            (((n : ℕ) : 𝔭.adicCompletion k)))
    (hram : ∀ p : HeightOneSpectrum (𝓞 k),
      Ideal.ramificationIdxIn p.asIdeal (𝓞 ↥M) ≠ 1 → DvdPrime 𝔪 p) :
    ∀ A : Frac k, FracCoprimeId 𝔪 A →
      NK.CFTLib.Arl.artinSym (K := k) (L := ↥M)
        (fun a b : ↥M ≃ₐ[k] ↥M => IsMulCommutative.is_comm.comm a b) A = 1 →
      A ∈ principalRayId 𝔪 ⊔ normRayId (K := k) (L := ↥M) 𝔪 := by
  classical
  haveI habelΩ : IsAbelianGalois k Ω := IsCyclotomicExtension.isAbelianGalois {n} k Ω
  haveI hcommΩI : IsMulCommutative (Ω ≃ₐ[k] Ω) := habelΩ.toIsMulCommutative
  let hcomm : ∀ a b : ↥M ≃ₐ[k] ↥M, a * b = b * a := IsMulCommutative.is_comm.comm
  let f : Frac k →* (↥M ≃ₐ[k] ↥M) :=
    NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := k) (L := ↥M) hcomm
  let I : Subgroup (Frac k) := idealCoprimeGroupId 𝔪
  let PN : Subgroup (Frac k) := principalRayId 𝔪 ⊔ normRayId (K := k) (L := ↥M) 𝔪
  -- ### `P(𝔪)` is killed by the Artin symbol of `M/k`
  have hPker_aux : ∀ A : Frac k, A ∈ principalRayId 𝔪 →
      NK.CFTLib.Arl.artinSym (K := k) (L := ↥M) hcomm A = 1 := by
    intro A hA
    -- `A` is coprime to `𝔪`, hence to `(n)`
    have hAI : A ∈ idealCoprimeGroupId 𝔪 :=
      Work.SSGRoute.ZDataMup.principalRayId_le_idealCoprimeGroupId (K := k) 𝔪 h𝔪 hA
    have hcop𝔪 : FracCoprimeId 𝔪 A :=
      (Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.mem_idealCoprimeGroupId_iff
        𝔪 A).mp hAI
    have hcopn : FracCoprime (K := k) n A := fun 𝔭 h𝔭 => hcop𝔪 𝔭 (hsupp 𝔭 h𝔭)
    -- the symbol of `A` in the big cyclotomic extension is trivial
    have hΩ : NK.CFTLib.Arl.artinSym (K := k) (L := Ω)
        (fun a b : Ω ≃ₐ[k] Ω => IsMulCommutative.is_comm.comm a b) A = 1 :=
      cycloPrincipalId k Ω n 𝔪 h𝔪 hsupp hlev A hA
    -- restriction to `M`
    have hramn : ∀ p : NK.Chebotarev.PrimeIdeal k,
        ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := k) (L := Ω) p →
        (n : 𝓞 k) ∈ p.asIdeal := by
      intro p hp
      by_contra hnp
      exact hp ((NK.CFTLib.ArtinReciprocityIdeal.isUnramified_iff_ramificationIdxIn_eq_one
          (K := k) (L := Ω) p).mpr
        (Work.SSGRoute.ZDataMup.ArtinReciprocity.ramificationIdxIn_eq_one_of_notMem_span_cyclotomic
          (K := k) (L := Ω) n p hnp))
    have hres := NK.CFTLib.ARL.artinSym_restrictNormalHom (k := k) (M := Ω) M
      (fun a b : Ω ≃ₐ[k] Ω => IsMulCommutative.is_comm.comm a b) hcomm n hramn A hcopn
    rw [← hres, hΩ, map_one]
  have hPker : principalRayId 𝔪 ≤ f.ker := fun A hA => by
    show f A = 1
    simpa only [f, NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply] using hPker_aux A hA
  -- ### `𝔑(𝔪)` is killed
  have hNker : normRayId (K := k) (L := ↥M) 𝔪 ≤ f.ker := by
    intro A hA
    simpa only [MonoidHom.mem_ker, f, hcomm,
      NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply] using
      Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.normKerId k ↥M 𝔪 h𝔪 hram A hA
  have hPNker : PN ≤ f.ker := sup_le hPker hNker
  -- ### the Artin symbol is surjective on `I(𝔪)`
  have hmap : I.map f = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    obtain ⟨A, hA, hAσ⟩ := NK.CFTLib.ArtinReciprocityIdeal.surjId_clean k ↥M 𝔪 h𝔪 hram σ
    exact Subgroup.mem_map.mpr ⟨A, hA, by
      simpa only [f, hcomm, NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply]
        using hAσ⟩
  have hcardI : f.ker.relIndex I = Nat.card (↥M ≃ₐ[k] ↥M) := by
    rw [Subgroup.relIndex_ker I f, hmap]
    exact Nat.card_congr (Subgroup.topEquiv (G := ↥M ≃ₐ[k] ↥M)).toEquiv
  have hIdxKerInf : (f.ker ⊓ I).relIndex I = Module.finrank k ↥M := by
    rw [Subgroup.inf_relIndex_right f.ker I, hcardI, IsGalois.card_aut_eq_finrank k ↥M]
  have hle : PN ⊓ I ≤ f.ker ⊓ I := fun x hx => ⟨hPNker hx.1, hx.2⟩
  have hIdxPNInf : (PN ⊓ I).relIndex I ≤ (f.ker ⊓ I).relIndex I := by
    rw [Subgroup.inf_relIndex_right PN I, Subgroup.inf_relIndex_right f.ker I, hcardI,
      IsGalois.card_aut_eq_finrank k ↥M]
    exact le_trans (Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.indexLeId k ↥M 𝔪 h𝔪)
      (NK.GlobalCFTdeep.index_le_finrank_of_isGalois (K := k) (L := ↥M))
  have hrelIndex_ne : PN.relIndex I ≠ 0 := by
    haveI hVfin : (NK.GlobalCFT.Idele.principalSubgroup k ⊔
        NK.GlobalCFT.Idele.normImage k ↥M).FiniteIndex :=
      Subgroup.finiteIndex_iff.mpr (by
        rw [index_principalSubgroup_sup_normImage (K := k) (L := ↥M)]
        exact NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero (K := k) (L := ↥M))
    haveI hkerfin : (thetaId k ↥M 𝔪 h𝔪).ker.FiniteIndex :=
      Subgroup.finiteIndex_of_le
        (principalSubgroup_sup_normImage_le_ker_thetaId (K := k) (L := ↥M) h𝔪)
    rw [show PN.relIndex I
        = ((rayNormClId k ↥M 𝔪).subgroupOf (idealCoprimeGroupId 𝔪)).index from by
      show ((principalRayId 𝔪 ⊔ normRayId (K := k) (L := ↥M) 𝔪).subgroupOf
          (idealCoprimeGroupId 𝔪)).index
        = ((rayNormClId k ↥M 𝔪).subgroupOf (idealCoprimeGroupId 𝔪)).index
      rw [rayNormClId,
        NK.CFTLib.ArtinReciprocityIdeal.principalRayClId_eq_principalRayId h𝔪]]
    rw [index_rayNormId_eq_ker_index (K := k) (L := ↥M) h𝔪]
    exact Subgroup.FiniteIndex.index_ne_zero
  have hEqPN : (PN ⊓ I).relIndex I = (f.ker ⊓ I).relIndex I :=
    le_antisymm hIdxPNInf (Subgroup.relIndex_le_of_le_left hle (by
      rwa [Subgroup.inf_relIndex_right PN I]))
  have hker_le_PN : f.ker ⊓ I ≤ PN ⊓ I := by
    have h1 : (PN ⊓ I).relIndex (f.ker ⊓ I) = 1 := by
      have hpos : 0 < (f.ker ⊓ I).relIndex I := by
        rw [hIdxKerInf]
        exact Module.finrank_pos
      refine Nat.eq_of_mul_eq_mul_right hpos ?_
      rw [Subgroup.relIndex_mul_relIndex (PN ⊓ I) (f.ker ⊓ I) I hle inf_le_right, hEqPN,
        one_mul]
    exact Subgroup.relIndex_eq_one.mp h1
  -- ### conclusion
  intro A hcop hsym
  have hAI : A ∈ I :=
    (Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.mem_idealCoprimeGroupId_iff
      𝔪 A).mpr hcop
  have hAker : A ∈ f.ker := by
    simpa only [MonoidHom.mem_ker, f, hcomm,
      NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply] using hsym
  exact (hker_le_PN ⟨hAker, hAI⟩).1

end Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus
