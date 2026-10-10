import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
import Submission.NK.UchidaKummer.SplitPrimes
import Submission.Work.SSGRoute.place_basics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A splitting place avoiding a prescribed finite set of places

`Work.SSGRoute.exists_split_place_avoiding`: for a finite Galois extension `Λ/k` of number fields
(inside an algebraic closure `Ω`) and a finite set `S` of finite places of `Ω`, there is a finite
place `P` of `Ω` which splits completely in `Λ`, and which lies over a prime of `k` different from
all the primes below the elements of `S` (equivalently `P` is not a `G_k`-conjugate of any element
of `S`).

This is the prime `P₁` of Schmidt--Wingberg §4 (and, in the odd-`p` construction, the prime
`P_{n+1}`): Chebotarev's density theorem provides a completely split prime outside any prescribed
finite set of primes of `k` (`NK.UchidaKummer.exists_splitsCompletely_notMem`), and the primes of
`k` below the elements of `S` are fed into that finite set via `Submission.NeukirchUchida.primeOf`.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.style.haveILetI false

theorem exists_split_place_avoiding (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
    (S : Finset (ValuationSubring Ω)) (hS : ∀ A ∈ S, SSGRoute.IsFinPlace k A) :
    ∃ P : ValuationSubring Ω, SSGRoute.IsFinPlace k P ∧ SSGRoute.IsSplitIn k Λ P ∧
      ∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A P := by
  classical
  -- the finitely many primes of `k` below the elements of `S`
  have hfin : ∀ A ∈ S, A.comap (algebraMap k Ω) ≠ ⊤ := fun A hA => hS A hA
  set T : Finset (NK.Chebotarev.PrimeIdeal k) :=
    S.attach.image (fun A => Submission.NeukirchUchida.primeOf A.1 (hfin A.1 A.2)) with hT
  obtain ⟨p, hpT, hpsplit⟩ := NK.UchidaKummer.exists_splitsCompletely_notMem (K := k) (L := Λ) T
  -- a place of `Ω` above the completely split prime `p`
  obtain ⟨P, hPcomap⟩ :=
    Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime (K := k) (K' := Ω) p
  have hPne : P.comap (algebraMap k Ω) ≠ ⊤ := by
    rw [hPcomap]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top (K := k) p
  haveI : NumberField ↥Λ := Commons.NumberTheory.NumberField.numberField_of_intermediateField Λ
  have hsplit : SSGRoute.IsSplitIn k Λ P :=
    (NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely (K := k) (K' := Ω) (N := Λ)
      p P hPcomap).mpr hpsplit
  refine ⟨P, hPne, hsplit, ?_⟩
  intro A hA hconj
  -- `A` and `P` lie over the same prime of `k`, which is then one of the primes of `T`
  obtain ⟨σ, hσ⟩ := hconj
  have hcomap : A.comap (algebraMap k Ω) = P.comap (algebraMap k Ω) := by
    rw [← comap_algebraMap_smul A σ, hσ]
  have hPq : Submission.NeukirchUchida.primeOf P hPne = p :=
    Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (by rw [← Submission.NeukirchUchida.primeOf_spec P hPne, hPcomap])
  have hAq : Submission.NeukirchUchida.primeOf A (hfin A hA) = p := by
    rw [Submission.NeukirchUchida.primeOf_eq_of_comap_eq (hfin A hA) hPne hcomap, hPq]
  have hmem : Submission.NeukirchUchida.primeOf A (hfin A hA) ∈ T := by
    rw [hT]
    exact Finset.mem_image.mpr ⟨⟨A, hA⟩, Finset.mem_attach S ⟨A, hA⟩, rfl⟩
  rw [hAq] at hmem
  exact hpT hmem

end Work.SSGRoute
