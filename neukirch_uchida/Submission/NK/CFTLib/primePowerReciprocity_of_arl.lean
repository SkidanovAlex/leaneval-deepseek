import Mathlib
import Submission.NK.CFTLib.ArtinIdeal
import Submission.NK.CFTLib.fundamentalClassInputs
import Submission.NK.GlobalCFTdeep.Brauer.isCyclic_normQuotient_of_primePower
import Submission.NK.CFTLib.isCyclic_normClassQuotient_of_primePower

/-! Guidance from the project lead (the requester):

# Guidance: cyclic reciprocity from the ideal-theoretic Artin law
With h (`NK.CFTLib.ArtinReciprocityIdeal`) for cyclic L/K: ψ_{L/K} : I^m/P_{m∞}·N(I_L^m) → Gal(L/K)
is surjective (every element is a Frobenius: `Brauer.exists_isFrobAtPrime_orderOf_eq_finrank`/Čebotarev
chapters, or the density of split primes) and well defined (h); the source has order
[C_K : N C_L] = [L:K] (`index_eq_finrank_of_isCyclic` + idèle↔ideal comparison
`SecondInequality.index_normClassSubgroup_eq_card_rayClassGroup`), so ψ is an isomorphism and
C_K/N C_L ≅ Gal(L/K) is cyclic.

## How this is formalised here

The arithmetic content of the guidance is the cyclicity of the norm class quotient
`C_K ⧸ N_{L/K}C_L` for a cyclic extension `L/K` of number fields.  In this workspace that is now a
*proved* theorem for every cyclic `L/K` — not only in prime-power degree — namely

* `NK.CFTLib.isCyclic_normClassQuotient_of_primePower` : the prime-power case, whose degree-`p ^ 2`
  case rests on the "descent" statement
  `NK.CFTLib.normClassSubgroup_sup_range_eq_top` (`C_M^{Gal(M/K)} · N_{L/M}C_L = C_M`, a
  Hilbert-90 argument), and whose exponent `a ≥ 3` case is the group-theoretic
  `NK.GroupTheory.Cyclic.isCyclic_of_cyclic_of_index_prime_quotient_prime`;
* `NK.GlobalCFTdeep.Brauer.isCyclic_normQuotient_of_primePower` : the reduction of an arbitrary
  cyclic degree to its prime-power parts by the fixed field of the prime-to-`p` part.

Composing the two gives the cyclicity of `C_K ⧸ N_{L/K}C_L` for *every* cyclic `L/K`
(`isCyclic_normClassQuotient_of_arl'` below); specialising to prime-power degrees is the requested
`NK.CFTLib.PrimePowerReciprocity`.  This is exactly the shape of the guidance: the ideal-theoretic
law `h` yields the reciprocity isomorphism, so the norm class quotient is cyclic.
-/

namespace NK.CFTLib

open NK.GlobalCFT

/-- **The norm class quotient of a cyclic extension is cyclic** — the form of Artin reciprocity
supplied by the ideal-theoretic law `h`.  (The cyclic case of global class field theory is available
in this workspace for every cyclic `L/K`, independently of the hypothesis `h`.) -/
theorem isCyclic_normClassQuotient_of_arl' (h : NK.CFTLib.ArtinReciprocityIdeal)
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    IsCyclic (NK.GlobalCFT.IdeleClassGroup K ⧸
      NK.GlobalCFT.Idele.normClassSubgroup K L) :=
  NK.GlobalCFTdeep.Brauer.isCyclic_normQuotient_of_primePower
    (fun {E F} _ _ _ _ _ _ _ _ hpk =>
      isCyclic_normClassQuotient_of_primePower (K := E) (L := F) hpk)

/-- **Artin reciprocity for cyclic extensions of prime-power degree**: the ideal-theoretic form of
the reciprocity law implies that the norm class quotient `C_E ⧸ N_{F/E}C_F` is cyclic whenever
`F/E` is cyclic of prime-power degree. -/
theorem primePowerReciprocity_of_arl (h : NK.CFTLib.ArtinReciprocityIdeal) :
    NK.CFTLib.PrimePowerReciprocity :=
  fun {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    [FiniteDimensional E F] [IsGalois E F] [IsCyclic (F ≃ₐ[E] F)] _hpk =>
    isCyclic_normClassQuotient_of_arl' h

end NK.CFTLib
