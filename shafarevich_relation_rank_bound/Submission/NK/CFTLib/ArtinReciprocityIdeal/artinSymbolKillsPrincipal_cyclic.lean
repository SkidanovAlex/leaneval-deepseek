import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinKillsPrincipal_cyclic
import Submission.NK.CFTLib.ArtinReciprocityIdeal.langCyclicKernelLe
import Submission.NK.CFTLib.ArtinReciprocityIdeal.langCyclicRelIndex
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSymbolKillsPrincipal_cyclic_of_lang


/-! ## STATUS (2026-09-24)

The target statement of this module is proved by the three-line assembly

* `NK.CFTLib.ArtinReciprocityIdeal.artinSymbolKillsPrincipal_cyclic_of_lang` — the assembly: from
  the kernel containment `ker Ψ ⊆ P(m)·𝔑(m)` and the index inequality
  `[I(m) : P(m)·𝔑(m)] ≥ [L:K]` one deduces `P(m) ⊆ ker Ψ`, which is the product condition
  `artinSymbol K L (Ideal.span {a}) = 1` for totally positive `a` with `a - 1 ∈ (m)`;
* `NK.CFTLib.ArtinReciprocityIdeal.langCyclicKernelLe` — there is `m > 0`, admissible
  (`IsAdmissible`) and divisible by all the primes ramified in `L/K`, with
  `ker Ψ ∩ I(m) ⊆ P(m)·𝔑(m)` (Lang, *Algebraic Number Theory*, Chapter X §2, Theorem 2, proved by
  Artin's lemma together with the per-prime transfer and the cyclotomic case);
* `NK.CFTLib.ArtinReciprocityIdeal.langCyclicRelIndex` — `P(m)·𝔑(m) ≤ I(m)` and
  `[I(m) : P(m)·𝔑(m)] ≥ [L:K]` for such a modulus (Lang's Theorem 8 of Chapter VII §4, the
  idèle–ideal dictionary, combined with `NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic`).

The statement has been left exactly as requested; only the proof has been filled in.
-/

namespace NK.CFTLib.ArtinReciprocityIdeal

/-- **The Artin symbol kills the principal ray of a cyclic extension** (Lang, *Algebraic Number
Theory*, Chapter X §2, Theorem 2, product condition; Childress, *Class Field Theory*, Chapter 5,
Theorem 2.1(ii)): for a cyclic extension `L/K` of number fields there is a modulus `m > 0`,
divisible by all the primes ramified in `L/K`, such that `artinSymbol K L (Ideal.span {a}) = 1`
for every `a : 𝓞 K` with `a - 1 ∈ Ideal.span {(m : 𝓞 K)}` which is totally positive (positive under
every real embedding); here `artinSymbol` is the product of the Frobenius elements at the prime
factors with multiplicity.

`NK.CFTLib.ArtinReciprocityIdeal.ArtinSymbolKillsPrincipal K L m` is exactly this last condition;
`Submission.NK.CFTLib.ArtinReciprocityIdeal.artinKillsPrincipal_cyclic` (already on disk) shows
that it implies the requested product condition `NK.CFTLib.artinKillsPrincipal K L m`.

Proof route (Childress, *Class Field Theory*, Chapter 5 §2; write `n = [L:K]`):
1. `[I(m) : ker A] = n` for the Artin map `A` on the ideals prime to `m`, because the Frobenius
   elements at all but finitely many primes generate `Gal(L/K)`
   (`NK.GlobalCFTdeep.SecondInequality.frobeniusGenerateTop_of_notMem`).
2. `N_{L/K}(m) ⊆ ker A`: norm ideals have trivial Artin symbol
   (`NK.CFTLib.ArtinReciprocityIdeal.artinSymbol_relNorm_eq_one`).
3. `[I(m) : P⁺_m · N_{L/K}(m)] ≥ [C_K : N_{L/K} C_L] = n`: map the ideals prime to `m` to the idèle
   class group modulo the norm subgroup; the principal ray (via Hasse's idèlic norm theorem
   `NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm`, the congruence units at ramified primes
   being local norms for large `m`) and the norms are killed, the map is surjective, and
   `NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic` gives the index `n`.
4. `ker A ⊆ P⁺_m·N_{L/K}(m)`: Childress's Proposition 2.2, whose only non-elementary input is
   Artin's Lemma (Childress Lemma 2.8): for a cyclic `K/F` of degree `n`, a finite set `S` of
   rational primes and a prime `𝔭` of `F` there are `m ∈ ℕ` coprime to `S` and to `𝔭` and a field
   `E ⊆ K(ζ_m)` with `E ∩ K = F`, `E(ζ_m) = K(ζ_m)`, `E/F` finite Galois, and `𝔭` splitting
   completely in `E/F` (van der Waerden's elementary lemmas 2.3–2.6 plus the cyclotomic Galois
   group `Gal(F(ζ_m)/F) ≅ (ℤ/m)^×`). The cyclotomic case for the subextensions of `E(ζ_m)/E`
   (`NK.CFTLib.ArtinReciprocityIdeal.artinKillsPrincipal_of_le_isCyclotomicExtension`) together
   with steps 1–3 for those auxiliary cyclic extensions gives the conclusion.
5. Hence `ker A = P⁺_m·N_{L/K}(m)`, so `P⁺_m ⊆ ker A`, i.e. the statement. -/
theorem artinSymbolKillsPrincipal_cyclic (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (Gal(L/K))] [IsMulCommutative (Gal(L/K))] :
    ∃ m : ℕ, 0 < m ∧
      (∀ p : NK.Chebotarev.PrimeIdeal K,
        ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
        (m : NumberField.RingOfIntegers K) ∈ p.asIdeal) ∧
      NK.CFTLib.ArtinReciprocityIdeal.ArtinSymbolKillsPrincipal K L m :=
  artinSymbolKillsPrincipal_cyclic_of_lang K L (langCyclicKernelLe K L)
    (fun m hm hram hadm => langCyclicRelIndex K L m hm hram hadm)

end NK.CFTLib.ArtinReciprocityIdeal
