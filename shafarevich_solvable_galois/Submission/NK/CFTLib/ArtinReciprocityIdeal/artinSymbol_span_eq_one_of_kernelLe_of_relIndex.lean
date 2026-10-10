import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSymSurjectiveOnCoprime
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSymbol_span_eq_artinSym_spanSingleton
import Submission.NK.CFTLib.ArtinReciprocityIdeal.congrOne_of_exists_mul
import Submission.NK.CFTLib.ArtinReciprocityIdeal.mem_idealCoprimeGroup_iff
import Submission.NK.CFTLib.ArtinReciprocityIdeal.normRayLeKer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField nonZeroDivisors

open NumberField IsDedekindDomain

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.CFTLib.ArtinReciprocityIdeal

/-- **Assembly of the product condition from the two halves of Lang's Theorem 2** (Lang,
*Algebraic Number Theory*, Chapter X §2; Childress, *Class Field Theory*, Chapter 5 §2).

For a finite **cyclic** extension `L/K` of number fields, suppose

* `hker` (Childress's Proposition 2.2, the crux, whose proof uses Artin's Lemma): there is an
  admissible modulus `m > 0` containing all ramified primes such that every fractional ideal `A`
  coprime to `(m)` with trivial Artin symbol lies in `principalRay K m ⊔ normRay K L m`;
* `hidx` (the idèle–ideal dictionary plus the universal norm index inequality, Milne CFT 4.9):
  for every admissible modulus `m > 0` containing the ramified primes,
  `principalRay K m ⊔ normRay K L m ≤ idealCoprimeGroup K m` and
  `[idealCoprimeGroup K m : principalRay K m ⊔ normRay K L m] ≥ [L : K]`.

Then the Artin symbol of every principal ideal `(a)` with `a - 1 ∈ (m)` and `a` totally positive
is trivial, for the modulus `m` supplied by `hker`.

Proof: for that `m` one has `ker(artinSym) ⊓ I(m) ⊆ (P(m) ⊔ 𝔑(m)) ⊓ I(m)` by `hker`, while
`[I(m) : ker(artinSym) ⊓ I(m)] = |Gal(L/K)| = [L:K]` (the Artin symbol on `I(m)` is surjective,
`NK.CFTLib.ArtinReciprocityIdeal.artinSymSurjectiveOnCoprime`) and
`[I(m) : (P(m) ⊔ 𝔑(m)) ⊓ I(m)] ≥ [L:K]` by `hidx`; hence the two subgroups are equal and every
element of the principal ray is killed.  A principal ideal `(a)` with `a ≡ 1 mod (m)` totally
positive is in the principal ray and coprime to `(m)`, so its Artin symbol is trivial; the
compatibility of the ideal-theoretic and fractional-ideal symbols is
`NK.CFTLib.ArtinReciprocityIdeal.artinSymbol_span_eq_artinSym_spanSingleton`. -/
theorem artinSymbol_span_eq_one_of_kernelLe_of_relIndex (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (Gal(L/K))] [IsMulCommutative (Gal(L/K))]
    (hker : ∃ m : ℕ, 0 < m ∧ NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m ∧
      (∀ p : NK.Chebotarev.PrimeIdeal K,
        ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
        (m : NumberField.RingOfIntegers K) ∈ p.asIdeal) ∧
      ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac K,
        NK.CFTLib.ArtinReciprocityIdeal.FracCoprime m A →
        NK.CFTLib.Arl.artinSym (K := K) (L := L)
          (fun a b : Gal(L/K) => IsMulCommutative.is_comm.comm a b) A = 1 →
        A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
            NK.CFTLib.ArtinReciprocityIdeal.normRay K L m)
    (hidx : ∀ m : ℕ, 0 < m →
      (∀ p : NK.Chebotarev.PrimeIdeal K,
        ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
        (m : NumberField.RingOfIntegers K) ∈ p.asIdeal) →
      NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m →
      NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRay K L m ≤
        NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup K m ∧
      Module.finrank K L ≤ (NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRay K L m).relIndex
        (NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup K m)) :
    ∃ m : ℕ, 0 < m ∧
      (∀ p : NK.Chebotarev.PrimeIdeal K,
        ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
        (m : NumberField.RingOfIntegers K) ∈ p.asIdeal) ∧
      ∀ a : NumberField.RingOfIntegers K,
        a - 1 ∈ Ideal.span {(m : NumberField.RingOfIntegers K)} →
        (∀ φ : K →+* ℝ, 0 < φ (a : K)) →
        NK.CFTLib.ArtinReciprocityIdeal.artinSymbol (K := K) (L := L) (Ideal.span {a}) = 1 := by
  classical
  obtain ⟨m, hm, hadm, hram, hkerK⟩ := hker
  obtain ⟨hPNI, hIdx⟩ := hidx m hm hram hadm
  refine ⟨m, hm, hram, ?_⟩
  -- ## The Artin symbol as a homomorphism of the group of fractional ideals
  let hcomm : ∀ a b : Gal(L/K), a * b = b * a := IsMulCommutative.is_comm.comm
  let f : Frac K →* Gal(L/K) := artinSymFracHom (K := K) (L := L) hcomm
  let I : Subgroup (Frac K) := idealCoprimeGroup K m
  let PN : Subgroup (Frac K) := principalRay K m ⊔ normRay K L m
  let J : Subgroup (Frac K) := f.ker ⊓ I
  -- ## The kernel of the Artin symbol on `I(m)` is contained in `P(m)·𝔑(m)`
  have hJPN : J ≤ PN := by
    intro A hA
    have hmem : A ∈ f.ker ⊓ I := hA
    have hAJ : A ∈ f.ker := (Subgroup.mem_inf.mp hmem).1
    have hAI : A ∈ I := (Subgroup.mem_inf.mp hmem).2
    have hkerA : f A = 1 := MonoidHom.mem_ker.mp hAJ
    have hcop : FracCoprime m A := (mem_idealCoprimeGroup_iff (K := K) m A).mp hAI
    refine hkerK A hcop ?_
    rw [artinSymFracHom_apply] at hkerA
    exact hkerA
  -- ## The Artin symbol is surjective on `I(m)`
  have hmap : I.map f = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    obtain ⟨A, hAσ⟩ := artinSymSurjectiveOnCoprime (K := K) (L := L) m hm hram σ
    refine Subgroup.mem_map.mpr ⟨(A : Frac K), A.2, ?_⟩
    simpa only [f, artinSymFracHom_apply] using hAσ
  have hcardI : f.ker.relIndex I = Nat.card (Gal(L/K)) := by
    rw [Subgroup.relIndex_ker I f, hmap]
    exact Nat.card_congr (Subgroup.topEquiv (G := Gal(L/K))).toEquiv
  -- ## Hence `[I(m) : ker ∩ I(m)] = [L : K]`
  have hJrelI : J.relIndex I = Module.finrank K L := by
    rw [show J.relIndex I = f.ker.relIndex I from Subgroup.inf_relIndex_right f.ker I, hcardI,
      IsGalois.card_aut_eq_finrank K L]
  have hJI_ne : J.relIndex I ≠ 0 := by
    rw [hJrelI]
    exact (Module.finrank_pos (R := K) (M := L)).ne'
  -- ## `[I(m) : P(m)·𝔑(m)] = [L : K]` as well, so `ker ∩ I(m) = P(m)·𝔑(m)`
  have hPNrelI : PN.relIndex I = Module.finrank K L := by
    refine le_antisymm ?_ hIdx
    rw [← hJrelI]
    exact Subgroup.relIndex_le_of_le_left hJPN hJI_ne
  have hJrelPN : J.relIndex PN = 1 := by
    have h' : J.relIndex PN * PN.relIndex I = 1 * PN.relIndex I := by
      rw [Subgroup.relIndex_mul_relIndex J PN I hJPN hPNI, hJrelI, hPNrelI, one_mul]
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (by rw [hPNrelI, ← hJrelI]; exact hJI_ne)) h'
  have hPNJ : PN ≤ J := Subgroup.relIndex_eq_one.mp hJrelPN
  -- ## Consequently the Artin symbol kills the principal ray
  have hPker : principalRay K m ≤ f.ker := by
    intro A hA
    have hAPN : A ∈ PN := Subgroup.mem_sup_left hA
    have hmem : A ∈ f.ker ⊓ I := hPNJ hAPN
    exact (Subgroup.mem_inf.mp hmem).1
  -- ## Translation into the ideal-theoretic Artin symbol
  intro a ha hpos
  rw [artinSymbol_span_eq_artinSym_spanSingleton (K := K) (L := L)
    (hcomm := IsMulCommutative.is_comm.comm) m hram a ha]
  by_cases ha0 : a = 0
  · subst ha0
    have h0 : ((0 : 𝓞 K) : K) = 0 := by simp
    rw [h0, FractionalIdeal.spanSingleton_eq_zero_iff.mpr rfl]
    exact artinSymFrac_zero IsMulCommutative.is_comm.comm
  · have haK : (a : K) ≠ 0 := by
      intro h
      exact ha0 (RingOfIntegers.coe_injective (by simpa [RingOfIntegers.coe_eq_algebraMap] using h))
    set u : Kˣ := Units.mk0 (a : K) haK with hu
    have huK : (u : K) = (a : K) := by rw [hu, Units.val_mk0]
    -- the congruence `a ≡ 1 mod m` and the total positivity give `CongrOne`
    obtain ⟨c, hc⟩ : ∃ c : 𝓞 K, a - 1 = (m : 𝓞 K) * c := Ideal.mem_span_singleton.mp ha
    have hcu : (u : K) - 1 = (m : K) * (c : K) := by
      have h2 : (((a - 1 : 𝓞 K)) : K) = ((a : 𝓞 K) : K) - 1 := by push_cast; ring
      have h3 : (((a - 1 : 𝓞 K)) : K) = (((m : 𝓞 K)) : K) * ((c : 𝓞 K) : K) := by
        rw [hc]; push_cast; ring
      rw [huK, ← h2, h3]
      push_cast
      ring
    have hposu : ∀ (w : InfinitePlace K) (hw : w.IsReal),
        0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
              (algebraMap K w.Completion (u : K)) := by
      intro w hw
      have h1 := hpos ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom.comp
        (algebraMap K w.Completion))
      rw [huK]
      exact h1
    have hcong : CongrOne m u := congrOne_of_exists_mul m u c hcu hposu
    have hmemP : spanUnit u ∈ principalRay K m := Subgroup.subset_closure ⟨u, hcong, rfl⟩
    have hf1 : f (spanUnit u) = 1 := MonoidHom.mem_ker.mp (hPker hmemP)
    rw [artinSymFracHom_apply] at hf1
    have hcoe : ((spanUnit u : Frac K) : FractionalIdeal (𝓞 K)⁰ K)
        = FractionalIdeal.spanSingleton (𝓞 K)⁰ ((a : K)) := by
      rw [coe_spanUnit, huK]
    rw [hcoe] at hf1
    exact hf1

end NK.CFTLib.ArtinReciprocityIdeal
