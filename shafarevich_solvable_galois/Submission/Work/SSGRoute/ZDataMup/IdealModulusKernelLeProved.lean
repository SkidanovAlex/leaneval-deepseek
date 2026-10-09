import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.NKImports
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.surjId
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.CoreId
import Submission.Work.SSGRoute.ZDataMup.CycleDefs
import Submission.Work.SSGRoute.ZDataMup.CycleBaseChangeExists
import Submission.Work.SSGRoute.ZDataMup.IdealModulusKernel.TransferId
import Submission.Work.SSGRoute.ZDataMup.MupAux.Base
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

/-- **The cycle of an ideal modulus**: support the primes dividing `𝔪`, level the `𝔭`-adic exponent
of `𝔪`.  This is the dictionary through which the ideal-modulus vocabulary of
`…/IdealModulus/Defs.lean` is read off from the cycle vocabulary of `CycleDefs.lean`. -/
noncomputable def idealModulusCycle {K : Type} [Field K] [NumberField K]
    (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) : Cycle K where
  supp := (NK.CFTLib.ArtinReciprocityIdeal.finite_setOf_dvdPrime 𝔪 h𝔪).toFinset
  lev 𝔭 := (FractionalIdeal.count K 𝔭 (𝔪 : FractionalIdeal (𝓞 K)⁰ K)).toNat

variable {K : Type} [Field K] [NumberField K]

lemma mem_supp_idealModulusCycle {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥)
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    𝔭 ∈ (idealModulusCycle 𝔪 h𝔪).supp ↔ NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 𝔭 :=
  (NK.CFTLib.ArtinReciprocityIdeal.finite_setOf_dvdPrime 𝔪 h𝔪).mem_toFinset

lemma one_le_lev_idealModulusCycle {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥)
    {𝔭 : HeightOneSpectrum (𝓞 K)} (h𝔭 : 𝔭 ∈ (idealModulusCycle 𝔪 h𝔪).supp) :
    1 ≤ (idealModulusCycle 𝔪 h𝔪).lev 𝔭 := by
  have h := NK.CFTLib.ArtinReciprocityIdeal.dvdPrime_count_pos (K := K) h𝔪
    ((mem_supp_idealModulusCycle h𝔪 𝔭).mp h𝔭)
  have h0 : 0 ≤ FractionalIdeal.count K 𝔭 (𝔪 : FractionalIdeal (𝓞 K)⁰ K) :=
    FractionalIdeal.count_coe_nonneg K 𝔭 𝔪
  simp only [idealModulusCycle]
  exact (Int.le_toNat h0).mpr h

lemma lev_idealModulusCycle_eq {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥)
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    ((((idealModulusCycle 𝔪 h𝔪).lev 𝔭 : ℕ)) : ℤ)
      = FractionalIdeal.count K 𝔭 (𝔪 : FractionalIdeal (𝓞 K)⁰ K) := by
  have h0 : 0 ≤ FractionalIdeal.count K 𝔭 (𝔪 : FractionalIdeal (𝓞 K)⁰ K) :=
    FractionalIdeal.count_coe_nonneg K 𝔭 𝔪
  simp only [idealModulusCycle]
  exact Int.toNat_of_nonneg h0

lemma fracCoprime_idealModulusCycle_iff {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥)
    (A : NK.CFTLib.ArtinReciprocityIdeal.Frac K) :
    (idealModulusCycle 𝔪 h𝔪).FracCoprime A ↔
      NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId 𝔪 A := by
  constructor
  · intro h 𝔭 h𝔭
    exact h 𝔭 ((mem_supp_idealModulusCycle h𝔪 𝔭).mpr h𝔭)
  · intro h 𝔭 h𝔭
    exact h 𝔭 ((mem_supp_idealModulusCycle h𝔪 𝔭).mp h𝔭)

lemma congrOne_idealModulusCycle_iff {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) (a : Kˣ) :
    (idealModulusCycle 𝔪 h𝔪).CongrOne a ↔
      NK.CFTLib.ArtinReciprocityIdeal.CongrOneId 𝔪 a := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun 𝔭 h𝔭 => ?_, h2⟩
    have hmem : 𝔭 ∈ (idealModulusCycle 𝔪 h𝔪).supp :=
      (mem_supp_idealModulusCycle h𝔪 𝔭).mpr h𝔭
    have h := h1 𝔭 hmem
    rwa [lev_idealModulusCycle_eq h𝔪 𝔭] at h
  · rintro ⟨h1, h2⟩
    refine ⟨fun 𝔭 h𝔭 => ?_, h2⟩
    have h := h1 𝔭 ((mem_supp_idealModulusCycle h𝔪 𝔭).mp h𝔭)
    rwa [lev_idealModulusCycle_eq h𝔪 𝔭]

lemma principalRay_idealModulusCycle {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    (idealModulusCycle 𝔪 h𝔪).principalRay =
      NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 := by
  have h : {A : NK.CFTLib.ArtinReciprocityIdeal.Frac K |
        ∃ a : Kˣ, (idealModulusCycle 𝔪 h𝔪).CongrOne a
          ∧ A = NK.CFTLib.ArtinReciprocityIdeal.spanUnit a}
      = {A : NK.CFTLib.ArtinReciprocityIdeal.Frac K |
        ∃ a : Kˣ, NK.CFTLib.ArtinReciprocityIdeal.CongrOneId 𝔪 a
          ∧ A = NK.CFTLib.ArtinReciprocityIdeal.spanUnit a} := by
    ext A
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, (congrOne_idealModulusCycle_iff h𝔪 a).mp ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, (congrOne_idealModulusCycle_iff h𝔪 a).mpr ha, rfl⟩
  unfold Cycle.principalRay NK.CFTLib.ArtinReciprocityIdeal.principalRayId
  rw [h]

variable {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

/-- **The support of the base change of `idealModulusCycle 𝔪` is the set of primes containing
`𝔪·𝓞 L`.** -/
lemma mem_supp_baseChange_iff {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) {cL : Cycle L}
    (hbc : Cycle.IsBaseChange K L (idealModulusCycle 𝔪 h𝔪) cL)
    (𝓠 : HeightOneSpectrum (𝓞 L)) :
    𝓠 ∈ cL.supp ↔ Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔪 ≤ 𝓠.asIdeal := by
  rw [hbc 𝓠]
  constructor
  · rintro ⟨𝔭, h𝔭, hlies⟩
    have h1 : 𝔪 ≤ 𝔭.asIdeal := (mem_supp_idealModulusCycle h𝔪 𝔭).mp h𝔭
    exact le_trans (Ideal.map_mono h1) (liesOver_map_le 𝔭 𝓠 hlies)
  · intro hmap
    haveI hQprime : 𝓠.asIdeal.IsPrime := 𝓠.isPrime
    haveI hQmax : 𝓠.asIdeal.IsMaximal :=
      Ring.DimensionLEOne.maximalOfPrime 𝓠.ne_bot 𝓠.isPrime
    have hqprime : (𝓠.asIdeal.under (𝓞 K)).IsPrime := inferInstance
    haveI hqmax : (𝓠.asIdeal.under (𝓞 K)).IsMaximal :=
      Ring.DimensionLEOne.maximalOfPrime (Ideal.under_ne_bot (𝓞 K) 𝓠.ne_bot) hqprime
    refine ⟨⟨𝓠.asIdeal.under (𝓞 K), hqprime, Ideal.under_ne_bot (𝓞 K) 𝓠.ne_bot⟩, ?_, ?_⟩
    · refine (mem_supp_idealModulusCycle h𝔪 _).mpr ?_
      exact (Ideal.map_le_iff_le_comap).mp hmap
    · exact ⟨rfl⟩

lemma normRay_idealModulusCycle {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) {cL : Cycle L}
    (hbc : Cycle.IsBaseChange K L (idealModulusCycle 𝔪 h𝔪) cL) :
    Cycle.normRay K L (idealModulusCycle 𝔪 h𝔪) cL =
      NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 := by
  have h : {A : NK.CFTLib.ArtinReciprocityIdeal.Frac K |
        ∃ (I : Ideal (𝓞 L)) (hI : I ≠ ⊥),
          cL.FracCoprime (NK.CFTLib.ArtinReciprocityIdeal.idealUnit I hI)
            ∧ A = NK.CFTLib.ArtinReciprocityIdeal.idealUnit (Ideal.relNorm (𝓞 K) I)
                (fun h => hI ((Ideal.relNorm_eq_bot_iff).mp h))}
      = {A : NK.CFTLib.ArtinReciprocityIdeal.Frac K |
        ∃ (I : Ideal (𝓞 L)) (hI : I ≠ ⊥),
          NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId (K := L)
            (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔪)
            (NK.CFTLib.ArtinReciprocityIdeal.idealUnit I hI)
            ∧ A = NK.CFTLib.ArtinReciprocityIdeal.idealUnit (Ideal.relNorm (𝓞 K) I)
                (fun h => hI ((Ideal.relNorm_eq_bot_iff).mp h))} := by
    ext A
    constructor
    · rintro ⟨I, hI, hcop, hA⟩
      refine ⟨I, hI, ?_, hA⟩
      intro 𝓠 h𝓠
      exact hcop 𝓠 ((mem_supp_baseChange_iff h𝔪 hbc 𝓠).mpr h𝓠)
    · rintro ⟨I, hI, hcop, hA⟩
      refine ⟨I, hI, ?_, hA⟩
      intro 𝓠 h𝓠
      exact hcop 𝓠 ((mem_supp_baseChange_iff h𝔪 hbc 𝓠).mp h𝓠)
  unfold Cycle.normRay NK.CFTLib.ArtinReciprocityIdeal.normRayId
  rw [h]

/-- **Lang's transfer (`ker ψ ∩ I(𝔪) ⊆ P(𝔪)·𝔑(𝔪)`) for an *ideal* modulus.**

This is Lang, *Algebraic Number Theory*, Chapter X §2, Theorem 2 (Childress, *CFT*, Chapter 5 §2,
Proposition 2.2) — the containment proved in `NK.NUV2.ChebAux.kernelLe_of_auxField` for a
*principal* modulus `(m)` — stated for an arbitrary ideal modulus `𝔪 : Ideal (𝓞 K)` with `𝔪 ≠ ⊥`.

The vocabulary is that of `…/IdealModulus/Defs.lean`: `DvdPrime`, `FracCoprimeId`, `principalRayId`,
`idealCoprimeGroupId`, `normRayId`, `IsAdmissibleId`, `ContainsRamified`.

The proof reduces the statement to the corresponding statement for the **cycle**
`idealModulusCycle 𝔪` (support the primes dividing `𝔪`, levels its exponents), which is the form in
which the transfer is available in the cycle lane
(`Work.SSGRoute.ZDataMup.CycleKernelLe`): the cycle vocabulary is translated back by
`fracCoprime_idealModulusCycle_iff`, `principalRay_idealModulusCycle` and
`normRay_idealModulusCycle`. -/
theorem IdealModulusKernelLeProved
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ ⊥)
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissibleId (K := K) (L := L) 𝔪)
    (hram : NK.CFTLib.ArtinReciprocityIdeal.ContainsRamified (K := K) (L := L) 𝔪) :
    ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac K,
      NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId 𝔪 A →
      NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm A = 1 →
      A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪 :=
  -- The containment is the ideal-modulus Lang transfer, proved in the
  -- `…/IdealModulusKernel/TransferId.lean` lane by the transplant of the natural-number
  -- transfer `NK.NUV2.ARL.SC.kernelLeOfAuxFieldSC` to an ideal modulus: Artin's auxiliary
  -- field (`MupAux.auxFieldHypId`), the cyclotomic cell (`cyclotomicCellKernelLeIdB`), the
  -- two descents along the relative norm (`MupAux.principalRayId_map_relNormUnit_le`,
  -- `transfer.normRayId_map_relNormUnit_le`) and the transport/restriction lemmas
  -- (`MupAux.artinSymId_algEquiv`, `MupAux.artinSymId_restrict_relNorm`,
  -- `MupAux.restrictNormalHom_artinSymId_eq_ofLe`).
  Work.SSGRoute.ZDataMup.IdealModulusKernel.kernelLeIdTransfer hcomm 𝔪 h𝔪 hadm hram

end Work.SSGRoute.ZDataMup
