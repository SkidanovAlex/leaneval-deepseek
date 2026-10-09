/-
Work of the Neukirch–Uchida team: the general Čebotarev density theorem.

# The Čebotarev input of the Neukirch–Uchida development

This file assembles the chapter into the form consumed by
`Submission/Work/WeakNU/Defs.lean`:

* `NK.ChebotarevGeneral.chebotarevFrobeniusInput_of_infinite` — the existence form
  `ChebotarevInfinite` gives `NK.WeakNU.ChebotarevFrobeniusInput`;
* `NK.ChebotarevGeneral.chebotarevFrobeniusInput_of_abelian` — the abelian case of Čebotarev in
  density form over an arbitrary number field base gives `NK.WeakNU.ChebotarevFrobeniusInput`;
* `NK.ChebotarevGeneral.chebotarevFrobeniusInput_of_lfunctions` — the same, starting from the
  Hecke `L`-function input `NK.Chebotarev.AbelianLFunctions` of every abelian extension.
-/
import Mathlib
import Submission.NK.ChebotarevGeneral.Infinity
import Submission.NK.ChebotarevGeneral.RatLevel
import Submission.NK.ChebotarevGeneral.card_isFrobAt_liesOver_mul_orderOf
import Submission.NK.ChebotarevGeneral.decompositionSubgroup_eq_zpowers_of_isFrobAt
import Submission.NK.ChebotarevGeneral.isFrobAtPrime_under_of_isFrobAt
import Submission.NK.ChebotarevGeneral.deuringTransfer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.ChebotarevGeneral

noncomputable section

open NK.Chebotarev

/-- **The existence form of Čebotarev's theorem gives `NK.WeakNU.ChebotarevFrobeniusInput`.**

Infinitely many rational primes are Frobenius elements for `σ`; discarding the ramified primes and
the finitely many primes in the prescribed finite set `T` leaves a prime `p` at which `σ` is a
Frobenius element. -/
theorem chebotarevFrobeniusInput_of_infinite (h : ChebotarevInfinite) :
    NK.WeakNU.ChebotarevFrobeniusInput := by
  classical
  intro N _ _ _ _ σ T
  have hinf : (frobSet (K := ℚ) (N := N) σ).Infinite := h ℚ N σ
  -- discard the ramified primes
  have hinf' : (frobSet (K := ℚ) (N := N) σ ∩
      {𝔭 | IsUnramifiedAt (K := ℚ) (N := N) 𝔭}).Infinite := by
    have h' := hinf.sdiff (finite_setOf_not_isUnramified (K := ℚ) (N := N))
    convert h' using 1
    ext 𝔭
    simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_inter_iff, not_not]
  -- pass to rational primes
  have hPinf : (ratPrimeOf '' (frobSet (K := ℚ) (N := N) σ ∩
      {𝔭 | IsUnramifiedAt (K := ℚ) (N := N) 𝔭})).Infinite :=
    Set.Infinite.image (fun _ _ _ _ hxy => ratPrimeOf_injective hxy) hinf'
  have hnotT : ∃ 𝔭 ∈ (frobSet (K := ℚ) (N := N) σ ∩
      {𝔭 | IsUnramifiedAt (K := ℚ) (N := N) 𝔭}), ratPrimeOf 𝔭 ∉ (T : Set ℕ) := by
    obtain ⟨q, hqimg, hqT⟩ := (hPinf.sdiff T.finite_toSet).nonempty
    obtain ⟨𝔮, h𝔮mem, h𝔮q⟩ := hqimg
    exact ⟨𝔮, h𝔮mem, by rwa [← h𝔮q] at hqT⟩
  obtain ⟨𝔭, h𝔭mem, h𝔭T⟩ := hnotT
  refine ⟨ratPrimeOf 𝔭, ratPrimeOf_prime 𝔭, h𝔭T, ?_, ?_⟩
  · intro P hP
    exact h𝔭mem.2 P ((liesOver_span_ratPrimeOf_iff 𝔭 P).mp hP)
  · obtain ⟨P, hP, hσ⟩ := h𝔭mem.1
    exact ⟨P, (liesOver_span_ratPrimeOf_iff 𝔭 P).mpr hP, hσ⟩

/-- **The abelian case of Čebotarev in density form, from the Hecke `L`-function input.**

This is `NK.Chebotarev.AbelianChebotarevOfLFunctions` packaged as the single statement
`NK.ChebotarevGeneral.AbelianChebotarevDensity`. -/
theorem abelianChebotarevDensity_of_lfunctions
    (h : ∀ (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
      [FiniteDimensional K N] [IsGalois K N], (∀ a b : Gal(N/K), a * b = b * a) →
      NK.Chebotarev.AbelianLFunctions K N) : AbelianChebotarevDensity := by
  intro K N _ _ _ _ _ _ _ hcomm σ
  exact NK.Chebotarev.AbelianChebotarevOfLFunctions hcomm (h K N hcomm) σ

/-- **Čebotarev's theorem for the Neukirch–Uchida development, from its abelian case.**

The abelian case of Čebotarev's density theorem, over an arbitrary number field base
(`AbelianChebotarevDensity`), implies the input `NK.WeakNU.ChebotarevFrobeniusInput` of the
Neukirch–Uchida development:  for every finite Galois extension `N/ℚ`, every `σ : Gal(N/ℚ)` and
every finite set `T` of rational primes there are `p ∉ T` unramified in `N` and a prime `P` of
`𝓞 N` above `p` with `NK.Chebotarev.IsFrobAt P σ`.

No Čebotarev input of the general (non-abelian) case is used: the reduction to the abelian case
(Deuring's transfer, in the existence form) is carried out in
`NK.ChebotarevGeneral.infinite_frobSet_of_abelian`. -/
theorem chebotarevFrobeniusInput_of_abelian (h_ab : AbelianChebotarevDensity) :
    NK.WeakNU.ChebotarevFrobeniusInput :=
  chebotarevFrobeniusInput_of_infinite (infinite_frobSet_of_abelian h_ab)

/-- **Čebotarev's theorem for the Neukirch–Uchida development, from the Hecke `L`-function input.**

The analytic input `NK.Chebotarev.AbelianLFunctions` of every abelian extension — discharged from
the global Artin reciprocity law in `Submission/Work/HeckeL/` — implies
`NK.WeakNU.ChebotarevFrobeniusInput`. -/
theorem chebotarevFrobeniusInput_of_lfunctions
    (h : ∀ (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
      [FiniteDimensional K N] [IsGalois K N], (∀ a b : Gal(N/K), a * b = b * a) →
      NK.Chebotarev.AbelianLFunctions K N) : NK.WeakNU.ChebotarevFrobeniusInput :=
  chebotarevFrobeniusInput_of_abelian (abelianChebotarevDensity_of_lfunctions h)

theorem chebotarevDensity_of_abelian (h_ab : AbelianChebotarevDensity) : ChebotarevDensity :=
  chebotarevDensity_of_abelian_of_transfer h_ab deuringTransfer

/-- **Čebotarev's theorem for the Neukirch–Uchida development, from its abelian case, via the
density form.**

The general Čebotarev density theorem follows from the abelian case alone, because the transfer step
`NK.ChebotarevGeneral.DeuringTransfer` is proved in `NK.ChebotarevGeneral.deuringTransfer`.  This
is the same conclusion as `NK.ChebotarevGeneral.chebotarevFrobeniusInput_of_abelian`, obtained
through the density form of the theorem. -/
theorem chebotarevFrobeniusInput_of_abelian_density (h_ab : AbelianChebotarevDensity) :
    NK.WeakNU.ChebotarevFrobeniusInput :=
  chebotarevFrobeniusInput_of_density (chebotarevDensity_of_abelian h_ab)

end

end NK.ChebotarevGeneral
