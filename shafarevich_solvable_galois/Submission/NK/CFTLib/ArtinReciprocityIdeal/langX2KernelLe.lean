import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.NK.CFTLib.Arl.artinSym_spanSingleton_eq_one
import Submission.NK.CFTLib.ArtinReciprocityIdeal.auxFieldExists
import Submission.NK.CFTLib.ArtinReciprocityIdeal.transferOfAuxField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lang, ANT, Chapter X §2, Theorem 2: the kernel containment for a fixed modulus

This module proves the target `NK.CFTLib.ArtinReciprocityIdeal.langX2KernelLe` — Lang's
Theorem 2, the containment `ker Ψ ∩ I(m) ⊆ P(m)·𝔑(m)` for a fixed **admissible** modulus `m` in a
cyclic extension `L/K` — and reduces it to the *product condition* at the same modulus `m`, i.e. to
`NK.CFTLib.artinKillsPrincipal K L m` ("the Artin symbol kills the principal ray").

The reduction is the classical index argument, and it needs no mathematics beyond what is already
on disk:

* the Artin symbol `Ψ = artinSym` is a homomorphism `Frac K →* Gal(L/K)`;
* `P(m)·𝔑(m) ⊆ ker Ψ`: the norm ray by `normRayLeKer` (property A4) and the principal ray by the
  product condition (this is the hypothesis);
* `[I(m) : ker Ψ ∩ I(m)] = [L:K]`, because `Ψ` is surjective on `I(m)`
  (`artinSymSurjectiveOnCoprime`);
* `[I(m) : P(m)·𝔑(m) ∩ I(m)] ≤ [L:K]` (`indexPrincipalRaySupNormRayLe`), and
  `[I(m) : P(m)·𝔑(m) ∩ I(m)] ≠ 0` (`indexIdealCoprimeLeNormClassIndex` and the finiteness of the
  idèle-class norm index);
* hence the two nested subgroups of `I(m)` have the same finite index, so they are equal, and the
  containment `ker Ψ ∩ I(m) ⊆ P(m)·𝔑(m)` follows from the reverse inclusion.

The hypothesis `hram` ("every ramified prime divides `(m)`") is used only to transfer between the
two formulations of "unramified" (`IsUnramified` and `Ideal.ramificationIdxIn = 1`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField nonZeroDivisors IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.ArtinReciprocityIdeal

/-- **Unramifiedness in the `ramificationIdxIn` form.**  If every ramified prime of `L/K` divides
`(m)`, then every prime `p` with `(m) ∉ p` has ramification index one in `L/K`. -/
theorem ramificationIdxIn_eq_one_of_notMem {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {m : ℕ}
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : 𝓞 K) ∈ p.asIdeal)
    {p : NK.Chebotarev.PrimeIdeal K} (hp : (m : 𝓞 K) ∉ p.asIdeal) :
    p.asIdeal.ramificationIdxIn (𝓞 L) = 1 := by
  by_contra hcon
  obtain ⟨P, hP⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
    (K := K) (L := L) p
  haveI : P.asIdeal.IsPrime := P.isPrime
  haveI : P.asIdeal.LiesOver p.asIdeal := hP
  have hm : (m : 𝓞 K) ∈ p.asIdeal := hram p (fun hunr => hcon (by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) p.asIdeal P.asIdeal
      (Gal(L/K))]
    exact hunr P hP))
  exact hp hm

/-- **The principal ray is killed by the Artin symbol, given the product condition.** -/
theorem principalRay_le_ker_of_artinKillsPrincipal {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (Gal(L/K))] (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : 𝓞 K) ∈ p.asIdeal)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m) :
    principalRay K m ≤ (artinSymFracHom (K := K) (L := L)
      (fun a b : Gal(L/K) => IsMulCommutative.is_comm.comm a b)).ker := by
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  rw [principalRay, Subgroup.closure_le]
  rintro A ⟨b, hb, rfl⟩
  show NK.CFTLib.Arl.artinSym hcomm
      ((spanUnit b : Frac K) : FractionalIdeal (𝓞 K)⁰ K) = 1
  rw [coe_spanUnit]
  exact NK.CFTLib.Arl.artinSym_spanSingleton_eq_one (K := K) (L := L) hcomm m hm
    (fun 𝔭 h𝔭 => ramificationIdxIn_eq_one_of_notMem (K := K) (L := L) hram h𝔭)
    hprinc b hb.1 hb.2

/-- **The kernel containment from the product condition** (Lang, *Algebraic Number Theory*, Ch. X
§2, Theorem 2, for a fixed modulus): if the Artin symbol kills the principal ray `P(m)`, then its
kernel on the ideals `I(m)` coprime to `(m)` is contained in `P(m)·𝔑(m)`.

The proof is the index argument: `P(m)·𝔑(m) ⊆ ker Ψ` (product condition and `normRayLeKer`),
`[I(m) : ker Ψ] = [L:K]` (surjectivity), `[I(m) : P(m)·𝔑(m)] ≤ [L:K]` and finite
(`indexPrincipalRaySupNormRayLe`, `indexIdealCoprimeLeNormClassIndex`); two nested subgroups of
equal finite index are equal. -/
theorem langX2KernelLe_of_artinKillsPrincipal (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] [IsMulCommutative (L ≃ₐ[K] L)] (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : 𝓞 K) ∈ p.asIdeal)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m) :
    ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac K,
      NK.CFTLib.ArtinReciprocityIdeal.FracCoprime m A →
      NK.CFTLib.Arl.artinSym (K := K) (L := L)
        (fun a b : L ≃ₐ[K] L => IsMulCommutative.is_comm.comm a b) A = 1 →
      A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRay K L m := by
  classical
  let hcomm : ∀ a b : Gal(L/K), a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  let f : Frac K →* Gal(L/K) := artinSymFracHom hcomm
  let I : Subgroup (Frac K) := idealCoprimeGroup K m
  let PN : Subgroup (Frac K) := principalRay K m ⊔ normRay K L m
  have hPker : principalRay K m ≤ f.ker :=
    principalRay_le_ker_of_artinKillsPrincipal (K := K) (L := L) m hm hram hprinc
  have hNker : normRay K L m ≤ f.ker := fun A hA => normRayLeKer K L m hm hram A hA
  have hPNker : PN ≤ f.ker := sup_le hPker hNker
  have hmap : I.map f = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    obtain ⟨A, hAσ⟩ := artinSymSurjectiveOnCoprime (K := K) (L := L) m hm hram σ
    refine Subgroup.mem_map.mpr ⟨(A : Frac K), A.2, ?_⟩
    simpa only [f, hcomm, artinSymFracHom_apply] using hAσ
  have hcardI : f.ker.relIndex I = Nat.card (Gal(L/K)) := by
    rw [Subgroup.relIndex_ker I f, hmap]
    exact Nat.card_congr (Subgroup.topEquiv (G := Gal(L/K))).toEquiv
  have hIdxKerInf : (f.ker ⊓ I).relIndex I = Module.finrank K L := by
    rw [Subgroup.inf_relIndex_right f.ker I, hcardI, IsGalois.card_aut_eq_finrank K L]
  have hIdxPNInf : (PN ⊓ I).relIndex I ≤ (f.ker ⊓ I).relIndex I := by
    rw [Subgroup.inf_relIndex_right PN I, Subgroup.inf_relIndex_right f.ker I, hcardI,
      IsGalois.card_aut_eq_finrank K L]
    exact indexPrincipalRaySupNormRayLe K L m hm
  have hle : PN ⊓ I ≤ f.ker ⊓ I := fun x hx => ⟨hPNker hx.1, hx.2⟩
  have hrelIndex_ne : PN.relIndex I ≠ 0 := by
    have hidx : (NK.GlobalCFT.Idele.principalSubgroup K
        ⊔ NK.GlobalCFT.Idele.normImage K L).index
        = (NK.GlobalCFT.Idele.normClassSubgroup K L).index :=
      index_principalSubgroup_sup_normImage (K := K) (L := L) m
    haveI hfin : (NK.GlobalCFT.Idele.principalSubgroup K
        ⊔ NK.GlobalCFT.Idele.normImage K L).FiniteIndex :=
      Subgroup.finiteIndex_iff.mpr (by
        rw [hidx]
        exact NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero)
    haveI hkerfin : (theta K L m hm).ker.FiniteIndex :=
      Subgroup.finiteIndex_of_le (principalSubgroup_sup_normImage_le_ker (K := K) (L := L) m hm)
    rw [show PN.relIndex I
        = ((rayNorm K L m).subgroupOf (NK.CFTLib.ARL.Icoprime K m)).index from by
      show ((principalRay K m ⊔ normRay K L m).subgroupOf
          (idealCoprimeGroup K m)).index
        = ((rayNorm K L m).subgroupOf (NK.CFTLib.ARL.Icoprime K m)).index
      rw [principalRay_eq_ARL, normRay_eq_normIdeals, idealCoprimeGroup_eq_Icoprime]
      rfl]
    rw [index_rayNorm_eq_ker_index (K := K) (L := L) m hm]
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
  have hAI : A ∈ I := (mem_idealCoprimeGroup_iff (K := K) m A).mpr hcop
  have hAker : A ∈ f.ker := hsym
  exact (hker_le_PN ⟨hAker, hAI⟩).1

end NK.CFTLib.ArtinReciprocityIdeal


/-!
## Notes on the remaining input (state of the proof, for the next stretch)

`langX2KernelLe_of_artinKillsPrincipal` reduces the target to the **product condition**

  `NK.CFTLib.artinKillsPrincipal K L m`,

at the *same* modulus `m`: "the Artin symbol kills every principal ideal `(a)` with `a ≡ 1 mod m`
totally positive".  That condition is the exact content of Lang's Theorem 2 (`ker Ψ = P(m)·𝔑(m)`
together with the two index inequalities) and of Artin reciprocity; the two inputs that remain on
the Lang route are

1. **the auxiliary field** ("Artin's lemma", van der Waerden's lemmas): for each prime `𝔭 ∤ m` one
   needs `N` and a field `E` with `𝔭` splitting completely in `E/K`, `E ∩ L = K` and
   `L·E ⊆ E(ζ_N)`, so that the cyclotomic case
   (`NK.CFTLib.ArtinReciprocityIdeal.cyclotomicKernelLe`, on disk) applies to `L·E/E`;
   the statement drafted as `langAuxiliaryField` below is the workspace's own on-disk form
   (`NK.CFTLib.ARL.exists_auxiliary_field`) with `E ⊆ L(ζ_N)`;
2. **the transfer/norm bookkeeping**: `ψ_{M/E}(𝔠)|_L = ψ_{L/K}(N_{E/K}𝔠)` for the tower
   `K ⊆ E ⊆ L ⊆ M` (the easy norm direction, `NK.CFTLib.Arl.prod_frobAtPrime_ramificationIdx_eq_one`
   has the prime-level input `frobAtPrime_restrict_eq_pow`), the norm of a `CongrOne` unit is
   `CongrOne` (`norm_principalRay_le`, on disk), and the transitivity of `𝔑`.

## A warning about the shape of Artin's lemma (analysis, not a theorem)

In the case `L ∩ K(ζ_N) = K` and `K ∩ ℚ(ζ_N) = ℚ` one has
`Gal(L(ζ_N)/K) ≅ Gal(L/K) × Gal(K(ζ_N)/K)`, and the conditions `E ∩ L = K`,
`E·ℚ(ζ_N) = L(ζ_N)`, `Frob_𝔭 ∈ Gal(L(ζ_N)/E)` force `Gal(L(ζ_N)/E)` to be the *graph* of an
injective homomorphism `f : Gal(L/K) ↪ Gal(K(ζ_N)/K)` with `f(Frob_𝔭) = Frob_𝔭(K(ζ_N)/K)`, i.e.
they force the existence of `x` of order `n = [L:K]` in `Gal(K(ζ_N)/K)` with

  `x^{s_𝔭} ≡ N𝔭  (mod N)`,   where `Frob_𝔭(L/K) = σ^{s_𝔭}`.

Taking `N`-th powers, `N ∣ N𝔭^{n/gcd(n,s_𝔭)} − 1` is necessary.  For the data
`n = 4`, `s_𝔭 = 2`, `N𝔭 = 3` this gives `N ∣ 8`, hence `Gal(K(ζ_N)/K) ⊆ (ℤ/8)^×`, an elementary
abelian group of exponent `2` — which has no element of order `4`.  So for such data and for every
`N` with `L ∩ K(ζ_N) = K`, no such `E ⊆ L(ζ_N)` exists; the auxiliary field has to be sought
outside `L(ζ_N)` (equivalently one must allow `L ∩ K(ζ_N) ⊋ K`, where
`Gal(L(ζ_N)/K) = Gal(L/(L∩K(ζ_N))) × Gal(K(ζ_N)/(L∩K(ζ_N)))` and the "graph" condition relaxes to
`f : Gal(L/(L∩K(ζ_N))) ↪ ⋯`).  This is worth checking before investing in the construction of
`langAuxiliaryField` as stated.
-/


/-
## Update: the global fundamental class IS available (axiom-clean)

`NK.GlobalCFTdeep.FundamentalClassElement` is *proved* in this workspace, axiom-clean: the chain

  `NK.CFTLib.primePowerReciprocity` (proved, `Submission/Work/CFTLib/fundamentalClassInputs.lean`)
  + `NK.GFC.normImage_of_auxiliary_cyclotomic` (the H⁰ norm-limitation statement for the
    auxiliary tower; its proof is sorry-free and does *not* use the sorry'd
    `NK.CFTLib.Existence.rep_invariants_le_range_norm_of_auxiliary`)
  ⇒ `NK.GFC.fundamentalClassElement_of_cyclotomicTower`

gives `FundamentalClassElement`, and hence (via
`NK.GlobalCFTdeep.artinReciprocity_of_fundamentalClassElement`) the *abstract* reciprocity
isomorphism `C_K ⧸ N_{L/K}C_L ≃* Gal(L/K)` for abelian `L/K`.

What is still missing for the target `langX2KernelLe` is the **canonicity** of that isomorphism at
the level of ideals: the identification `Ψ(A) = θ(Φ(A))` of the ideal-theoretic Artin symbol with
the reciprocity map (`Φ(A) = [x_A]` is the dictionary map of
`indexIdealCoprimeLeNormClassIndex`), i.e. the *Frobenius normalisation* `θ(𝔭) = Frob_𝔭`.  This
is Milne, *CFT*, V.5.3(a) / Lemma 8.5, and it is the same wall as `NK.NUV2.ArtinBridge`'s
`CanonicalArtinDatum`.  Two routes from the fundamental class:

* the *local* route (Milne): the local invariant maps `NK.NUV2.LC.localInvariant` together with
  the Hasse principle `0 → Br(K) → ⊕_v Br(K_v) → ℚ/ℤ → 0` (Hilbert reciprocity for quadratic
  levels is on disk, `NK.NUV2.LC.HilbertReciprocityTwo`);
* the *transfer* route (Lang X.2): the auxiliary tower of `NK.GFC` with the cyclotomic case of
  the reciprocity law — exactly the machinery of `NK.GFC.normImage_of_auxiliary_cyclotomic`
  (there used for the H⁰ norm-limitation, not for the Frobenius normalisation).

Given the canonicity in the form `Ψ(A) = θ(Φ(A))`, the target follows from
`langX2KernelLe_of_artinKillsPrincipal` below together with the equality
`ker Φ ∩ I(m) = P(m)·𝔑(m) ∩ I(m)` (the dictionary facts
`NK.CFTLib.ARL.idealOf_mem_principalRay_sup_normIdeals`,
`principalRay_eq_ARL`, `normRay_eq_normIdeals`, `idealCoprimeGroup_eq_Icoprime`).
-/

namespace NK.CFTLib.ArtinReciprocityIdeal

/-- **Lang, *Algebraic Number Theory*, Chapter X §2, Theorem 2, for a fixed admissible modulus**
(the requested statement): for a cyclic extension `L/K` of number fields, an admissible modulus
`m` divisible by every prime ramified in `L/K`, and a fractional ideal `A` coprime to `m` whose
Artin symbol is trivial, one has `A ∈ P(m)·𝔑(m)`.

See `langX2KernelLe_of_artinKillsPrincipal` (the reduction to the product condition) and the notes
in this file for the state of the remaining input.

The proof is by the *transfer* `NK.CFTLib.ArtinReciprocityIdeal.transferOfAuxField` (the
norm/restriction transfer of Lang, *Algebraic Number Theory*, Ch. X §2, Theorem 2) applied to the
*auxiliary field* `NK.CFTLib.ArtinReciprocityIdeal.auxFieldExists` (Artin's lemma, the corrected
per-prime auxiliary cyclotomic field), both of which are proved in this directory; as soon as those
two are proved this file is sorry-free and axiom-clean with no further edit (see
`NOTES_langX2KernelLe.md`).

An alternative proof of the same statement from the *product condition* `artinKillsPrincipal K L m`
is `langX2KernelLe_of_artinKillsPrincipal` below (equivalently
`NK.CFTLib.ArtinReciprocityIdeal.artinKillsPrincipal_of_artinSymbolKillsPrincipal` for the other
form); either finishes the file as soon as the corresponding input lands. -/
theorem langX2KernelLe (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    [IsMulCommutative (L ≃ₐ[K] L)] (m : ℕ) (hm : 0 < m)
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal) :
    ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac K,
      NK.CFTLib.ArtinReciprocityIdeal.FracCoprime m A →
      NK.CFTLib.Arl.artinSym (K := K) (L := L)
        (fun a b : L ≃ₐ[K] L => IsMulCommutative.is_comm.comm a b) A = 1 →
      A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRay K L m :=
  NK.CFTLib.ArtinReciprocityIdeal.transferOfAuxField K L m hm
    (NK.CFTLib.ArtinReciprocityIdeal.auxFieldExists K L m hm) hram

end NK.CFTLib.ArtinReciprocityIdeal
