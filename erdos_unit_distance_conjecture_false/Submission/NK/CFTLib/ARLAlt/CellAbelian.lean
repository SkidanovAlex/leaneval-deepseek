import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.cyclotomicKernelLe

/-!
# The cyclotomic cell: `ker ⊆ P·𝔑` **without the admissibility or cyclicity hypotheses**

This is a verbatim copy of the proof of `NK.CFTLib.ARL.cyclotomicCellKernelLe_B` with the
hypothesis `IsCyclic (Gal(↥M/k'))` deleted: the proof never uses it (only commutativity of the
Galois group, via the Artin symbol and the norm index inequality, is needed).  The base field here
is an auxiliary field `E𝔭` of Artin's lemma, over which the composite `E𝔭·L` is *cyclic* — but the
cell applies to the larger abelian extension `Ω/E𝔭`, hence the removal.

`NK.CFTLib.ArtinReciprocityIdeal.cyclotomicKernelLe` (on disk, sorry-free) proves

  `ker ψ ∩ I(m) ⊆ P(m)·𝔑(m)`

for an intermediate field `M` of a cyclotomic extension `k'(ζ_n)/k'`, with an *unused* hypothesis
`hadm : IsAdmissible k' ↥M m`.  This module removes it: the proof below is the proof of
`cyclotomicKernelLe` with `hadm` deleted (it was never used — the weak form `P(m) ≤ ker` comes from
the cyclotomic base case `NK.CFTLib.ARL.artinReciprocity_cyclotomic`, the index inequality from
`indexPrincipalRaySupNormRayLe` and the finiteness of the index from the idèle–idèle dictionary,
none of which needs admissibility).  The result is what the transfer
(`NK.CFTLib.ARL.kernelLe_of_auxField_B`) applies to the cells `L·E_𝔭/E_𝔭`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open NK.Chebotarev
open NumberField
open scoped NumberField IsMulCommutative nonZeroDivisors

namespace NK.CFTLib.ARLAlt

theorem cyclotomicCellKernelLe_abelian (k' E' : Type) [Field k'] [NumberField k'] [Field E']
    [NumberField E'] [Algebra k' E'] [FiniteDimensional k' E'] [IsGalois k' E'] (n : ℕ)
    [NeZero n] [IsCyclotomicExtension {n} k' E']
    (M : IntermediateField k' E') [FiniteDimensional k' M] [NumberField ↥M] [IsGalois k' ↥M]
    [IsMulCommutative (Gal(↥M/k'))]
    (m : ℕ) (hm : 0 < m) (hn : n ∣ m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal k',
        ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := k') (L := ↥M) p →
        (m : NumberField.RingOfIntegers k') ∈ p.asIdeal) :
    ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac k',
      NK.CFTLib.ArtinReciprocityIdeal.FracCoprime m A →
      NK.CFTLib.Arl.artinSym (K := k') (L := ↥M) IsMulCommutative.is_comm.comm A = 1 →
      A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay k' m ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRay k' ↥M m := by
  classical
  let hcomm : ∀ a b : Gal(↥M/k'), a * b = b * a := IsMulCommutative.is_comm.comm
  let f : NK.CFTLib.ArtinReciprocityIdeal.Frac k' →* Gal(↥M/k') :=
    NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom hcomm
  let I : Subgroup (NK.CFTLib.ArtinReciprocityIdeal.Frac k') :=
    NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup k' m
  let PN : Subgroup (NK.CFTLib.ArtinReciprocityIdeal.Frac k') :=
    NK.CFTLib.ArtinReciprocityIdeal.principalRay k' m ⊔
      NK.CFTLib.ArtinReciprocityIdeal.normRay k' ↥M m
  have hPker : NK.CFTLib.ArtinReciprocityIdeal.principalRay k' m ≤ f.ker :=
    NK.CFTLib.ArtinReciprocityIdeal.cyclotomicKernelLe_principalRay_le_ker
      (k' := k') (E' := E') M n m hm hn hram
  have hNker : NK.CFTLib.ArtinReciprocityIdeal.normRay k' ↥M m ≤ f.ker :=
    fun A hA => NK.CFTLib.ArtinReciprocityIdeal.normRayLeKer k' ↥M m hm hram A hA
  have hPNker : PN ≤ f.ker := sup_le hPker hNker
  have hmap : I.map f = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    obtain ⟨A, hAσ⟩ := NK.CFTLib.ArtinReciprocityIdeal.artinSymSurjectiveOnCoprime
      k' ↥M m hm hram σ
    refine Subgroup.mem_map.mpr ⟨(A : NK.CFTLib.ArtinReciprocityIdeal.Frac k'), A.2, ?_⟩
    simpa only [f, hcomm, NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply] using hAσ
  have hcardI : f.ker.relIndex I = Nat.card (Gal(↥M/k')) := by
    rw [Subgroup.relIndex_ker I f, hmap]
    exact Nat.card_congr (Subgroup.topEquiv (G := Gal(↥M/k'))).toEquiv
  have hIdxKerInf : (f.ker ⊓ I).relIndex I = Module.finrank k' ↥M := by
    rw [Subgroup.inf_relIndex_right f.ker I, hcardI, IsGalois.card_aut_eq_finrank k' ↥M]
  have hIdxPNInf : (PN ⊓ I).relIndex I ≤ (f.ker ⊓ I).relIndex I := by
    rw [Subgroup.inf_relIndex_right PN I, Subgroup.inf_relIndex_right f.ker I, hcardI,
      IsGalois.card_aut_eq_finrank k' ↥M]
    exact NK.CFTLib.ArtinReciprocityIdeal.indexPrincipalRaySupNormRayLe k' ↥M m hm
  have hle : PN ⊓ I ≤ f.ker ⊓ I := fun x hx => ⟨hPNker hx.1, hx.2⟩
  have hrelIndex_ne : PN.relIndex I ≠ 0 := by
    have hidx : (NK.GlobalCFT.Idele.principalSubgroup k'
        ⊔ NK.GlobalCFT.Idele.normImage k' ↥M).index
        = (NK.GlobalCFT.Idele.normClassSubgroup k' ↥M).index :=
      NK.CFTLib.ArtinReciprocityIdeal.index_principalSubgroup_sup_normImage (K := k') (L := ↥M) m
    haveI hfin : (NK.GlobalCFT.Idele.principalSubgroup k'
        ⊔ NK.GlobalCFT.Idele.normImage k' ↥M).FiniteIndex :=
      Subgroup.finiteIndex_iff.mpr (by
        rw [hidx]
        exact NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero)
    haveI hkerfin : (NK.CFTLib.ArtinReciprocityIdeal.theta k' ↥M m hm).ker.FiniteIndex :=
      Subgroup.finiteIndex_of_le
        (NK.CFTLib.ArtinReciprocityIdeal.principalSubgroup_sup_normImage_le_ker
          (K := k') (L := ↥M) m hm)
    rw [show PN.relIndex I
        = ((NK.CFTLib.ArtinReciprocityIdeal.rayNorm k' ↥M m).subgroupOf
            (NK.CFTLib.ARL.Icoprime k' m)).index from by
      show ((NK.CFTLib.ArtinReciprocityIdeal.principalRay k' m ⊔
            NK.CFTLib.ArtinReciprocityIdeal.normRay k' ↥M m).subgroupOf
          (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup k' m)).index
        = ((NK.CFTLib.ArtinReciprocityIdeal.rayNorm k' ↥M m).subgroupOf
            (NK.CFTLib.ARL.Icoprime k' m)).index
      rw [NK.CFTLib.ArtinReciprocityIdeal.principalRay_eq_ARL,
        NK.CFTLib.ArtinReciprocityIdeal.normRay_eq_normIdeals,
        NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup_eq_Icoprime]
      rfl]
    rw [NK.CFTLib.ArtinReciprocityIdeal.index_rayNorm_eq_ker_index (K := k') (L := ↥M) m hm]
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
  intro A hcop hsym
  have hAI : A ∈ I :=
    (NK.CFTLib.ArtinReciprocityIdeal.mem_idealCoprimeGroup_iff (K := k') m A).mpr hcop
  have hAker : A ∈ f.ker := hsym
  exact (hker_le_PN ⟨hAker, hAI⟩).1

end NK.CFTLib.ARLAlt
