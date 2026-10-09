/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Completely split primes and freeness of the Galois action

Reference: the LaTeX sources of arXiv:2601.01251, §5 (*Full Neukirch–Uchida*), where the passage
from a prime-level statement ("`σ` matches `α` on the primes of a full-density set") to a
group-level statement ("`σ` matches `α` on the Galois group") is made with the help of a prime
which splits completely in the relevant finite Galois level, and the observation that the Galois
group acts *freely* on the primes above such a prime.

The results here are unconditional: the existence of completely split primes is
`Commons.NumberTheory.NumberField.exists_prime_splitsCompletely`, obtained from the Dirichlet
density `1 / [L : K]` of the completely split primes
(`Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely`), together with
the fact that a finite set of primes has Dirichlet density `0`.

## Main results

* `exists_splitsCompletely_notMem` — a completely split prime outside a prescribed finite set;
* `exists_splitsCompletely_mem_of_hasFullDensity` — a completely split prime inside a prescribed
  full-density set (and outside a finite set): this is the form in which §5 uses it;
* `eq_one_of_smul_eq_of_splitsCompletely` — **freeness**: if `p` splits completely in the finite
  Galois extension `L / K`, then the only element of `Gal(L/K)` fixing a prime above `p` is the
  identity;
* `eq_of_forall_smul_eq_of_splitsCompletely` — two elements of `Gal(L/K)` agreeing on all primes
  above a completely split prime are equal.
-/

import Submission.NK.UchidaKummer.Defs
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_of_density_zero
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_of_disjoint
import Submission.Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open Filter

namespace NK.UchidaKummer

open IsDedekindDomain

section SplitPrimes

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The set of primes of `K` splitting completely in `L` is exactly the set cut out by
`SplitsCompletely`, definitionally. -/
theorem splitsCompletelySet_eq :
    {p : NK.Chebotarev.PrimeIdeal K | SplitsCompletely (K := K) (L := L) p} =
      {p : NK.Chebotarev.PrimeIdeal K |
        (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard = Module.finrank K L} :=
  rfl

/-- **A completely split prime outside a prescribed finite set of primes.**

The completely split primes of `K` in `L` have Dirichlet density `1 / [L : K] > 0`, while a finite
set of primes has density `0`; a set of positive density therefore cannot be contained in a finite
set. -/
theorem exists_splitsCompletely_notMem [FiniteDimensional K L] [IsGalois K L]
    (T : Finset (NK.Chebotarev.PrimeIdeal K)) :
    ∃ p : NK.Chebotarev.PrimeIdeal K, p ∉ T ∧ SplitsCompletely (K := K) (L := L) p := by
  by_contra h
  simp only [not_exists, not_and] at h
  have hsub : {p : NK.Chebotarev.PrimeIdeal K | SplitsCompletely (K := K) (L := L) p} ⊆
      (T : Set (NK.Chebotarev.PrimeIdeal K)) := by
    intro p hp
    by_contra hpT
    exact h p hpT hp
  have h0 : NumberField.Set.HasDirichletDensity
      {p : NK.Chebotarev.PrimeIdeal K | SplitsCompletely (K := K) (L := L) p} 0 :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_subset
      (Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite T.finite_toSet)
      hsub
  have h1 : NumberField.Set.HasDirichletDensity
      {p : NK.Chebotarev.PrimeIdeal K | SplitsCompletely (K := K) (L := L) p}
      (1 / (Module.finrank K L : ℝ)) :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
  have heq : (0 : ℝ) = 1 / (Module.finrank K L : ℝ) := tendsto_nhds_unique h0 h1
  have hpos : (0 : ℝ) < (Module.finrank K L : ℝ) := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := L))
  have hne : (1 : ℝ) / (Module.finrank K L : ℝ) ≠ 0 := by positivity
  exact hne heq.symm

/-- **A completely split prime inside a full-density set**, outside a prescribed finite set.

This is the form in which §5 consumes the density of the completely split primes: the
prime-identification of `lem:alpha identifies with sigma on primes` holds at all the places over
a full-density set of primes of `K`, and the argument needs one such prime which additionally
splits completely in the level at hand. -/
theorem exists_splitsCompletely_mem_of_hasFullDensity [FiniteDimensional K L] [IsGalois K L]
    {R : Set (NK.Chebotarev.PrimeIdeal K)} (hR : HasFullDensity K R)
    (T : Finset (NK.Chebotarev.PrimeIdeal K)) :
    ∃ p : NK.Chebotarev.PrimeIdeal K, p ∉ T ∧ p ∈ R ∧
      SplitsCompletely (K := K) (L := L) p := by
  by_contra h
  have hsub : R ∩ {p : NK.Chebotarev.PrimeIdeal K | SplitsCompletely (K := K) (L := L) p} ⊆
      (T : Set (NK.Chebotarev.PrimeIdeal K)) := by
    intro p hp
    by_contra hpT
    exact h ⟨p, hpT, hp.1, hp.2⟩
  -- `S ∩ R` is finite, hence of density `0`
  have h0 : NumberField.Set.HasDirichletDensity
      (R ∩ {p : NK.Chebotarev.PrimeIdeal K | SplitsCompletely (K := K) (L := L) p}) 0 :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_subset
      (Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite T.finite_toSet)
      hsub
  have h0' : NumberField.Set.HasDirichletDensity
      ({p : NK.Chebotarev.PrimeIdeal K | SplitsCompletely (K := K) (L := L) p} ∩ R) 0 := by
    rw [Set.inter_comm]; exact h0
  -- `S \ R ⊆ Rᶜ` is of density `0`
  have h0'' : NumberField.Set.HasDirichletDensity
      ({p : NK.Chebotarev.PrimeIdeal K | SplitsCompletely (K := K) (L := L) p} \ R) 0 :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_subset
      (K := K) hR (by intro p hp; exact hp.2)
  -- `S` is the union of the two
  have hS0 : NumberField.Set.HasDirichletDensity
      {p : NK.Chebotarev.PrimeIdeal K | SplitsCompletely (K := K) (L := L) p} 0 := by
    have h := Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_of_density_zero
      (K := K) h0'' h0'
    have hset : ({p : NK.Chebotarev.PrimeIdeal K | SplitsCompletely (K := K) (L := L) p} \ R) ∪
        ({p : NK.Chebotarev.PrimeIdeal K | SplitsCompletely (K := K) (L := L) p} ∩ R) =
        {p : NK.Chebotarev.PrimeIdeal K | SplitsCompletely (K := K) (L := L) p} := by
      ext q; simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_setOf_eq]
      tauto
    rwa [hset] at h
  have h1 : NumberField.Set.HasDirichletDensity
      {p : NK.Chebotarev.PrimeIdeal K | SplitsCompletely (K := K) (L := L) p}
      (1 / (Module.finrank K L : ℝ)) :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
  have heq : (0 : ℝ) = 1 / (Module.finrank K L : ℝ) := tendsto_nhds_unique hS0 h1
  have hpos : (0 : ℝ) < (Module.finrank K L : ℝ) := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := L))
  have hne : (1 : ℝ) / (Module.finrank K L : ℝ) ≠ 0 := by positivity
  exact hne heq.symm

end SplitPrimes

/-! ## Freeness of the Galois action -/

section Freeness

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The `Commons` action of `Gal(L/K)` on the finite places of `L` agrees with the `SMul`
instance of `NK.Chebotarev`. -/
theorem placeSmul_eq_smul (σ : Gal(L/K)) (P : NK.Chebotarev.PrimeIdeal L) :
    Commons.NumberTheory.NumberField.Completion.placeSmul σ P = σ • P := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [Commons.NumberTheory.NumberField.Completion.placeSmul_asIdeal,
    NK.Chebotarev.smul_primeIdeal_asIdeal]

/-- **Freeness of the Galois action above a completely split prime**, in the `placeSmul`
formulation of `Commons.NumberTheory.NumberField.Completion`.

If `p` splits completely in the finite Galois extension `L / K` of number fields, then the
decomposition group of any prime `P` of `𝓞 L` above `p` is trivial (its order is the local degree
`e · f = 1`), so the only element of `Gal(L/K)` fixing `P` is the identity.  This is the step
which, in §5, converts the prime-level agreement of `σ` and `α` into a group-level agreement. -/
theorem eq_one_of_placeSmul_eq_of_splitsCompletely {p : NK.Chebotarev.PrimeIdeal K}
    (hp : SplitsCompletely (K := K) (L := L) p) {P : NK.Chebotarev.PrimeIdeal L}
    (hP : P.asIdeal.LiesOver p.asIdeal) {σ : Gal(L/K)}
    (hσ : Commons.NumberTheory.NumberField.Completion.placeSmul σ P = P) : σ = 1 := by
  have hef : p.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) = 1 ∧
      p.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L) = 1 :=
    (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
      (K := K) (L := L) p).mp hp
  have hbot : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) P = ⊥ :=
    (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
      (K := K) (L := L) p P hP).mpr hef
  have hmem : σ ∈ Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) P := by
    rw [Commons.NumberTheory.NumberField.Completion.mem_decompositionSubgroup]
    exact hσ
  rw [hbot] at hmem
  simpa using hmem

/-- **Freeness of the Galois action above a completely split prime**, for the `SMul` instance of
`NK.Chebotarev`. -/
theorem eq_one_of_smul_eq_of_splitsCompletely {p : NK.Chebotarev.PrimeIdeal K}
    (hp : SplitsCompletely (K := K) (L := L) p) {P : NK.Chebotarev.PrimeIdeal L}
    (hP : P.asIdeal.LiesOver p.asIdeal) {σ : Gal(L/K)} (hσ : σ • P = P) : σ = 1 :=
  eq_one_of_placeSmul_eq_of_splitsCompletely hp hP (by rw [placeSmul_eq_smul]; exact hσ)

/-- **Two Galois elements agreeing on the primes above a completely split prime are equal**,
in the `placeSmul` formulation. -/
theorem eq_of_forall_placeSmul_eq_of_splitsCompletely {p : NK.Chebotarev.PrimeIdeal K}
    (hp : SplitsCompletely (K := K) (L := L) p) {σ τ : Gal(L/K)}
    (h : ∀ P : NK.Chebotarev.PrimeIdeal L, P.asIdeal.LiesOver p.asIdeal →
      Commons.NumberTheory.NumberField.Completion.placeSmul σ P =
        Commons.NumberTheory.NumberField.Completion.placeSmul τ P) :
    σ = τ := by
  obtain ⟨P₀, hP₀⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) p
  have h1 := h P₀ hP₀
  haveI : P₀.asIdeal.LiesOver p.asIdeal := hP₀
  have hτ : Commons.NumberTheory.NumberField.Completion.placeSmul τ⁻¹
      (Commons.NumberTheory.NumberField.Completion.placeSmul τ P₀) = P₀ := by
    rw [← Commons.NumberTheory.NumberField.Completion.placeSmul_mul τ⁻¹ τ P₀, inv_mul_cancel,
      Commons.NumberTheory.NumberField.Completion.placeSmul_one]
  have h2 : Commons.NumberTheory.NumberField.Completion.placeSmul (σ * τ⁻¹)
      (Commons.NumberTheory.NumberField.Completion.placeSmul τ P₀) =
      Commons.NumberTheory.NumberField.Completion.placeSmul τ P₀ :=
    calc Commons.NumberTheory.NumberField.Completion.placeSmul (σ * τ⁻¹)
          (Commons.NumberTheory.NumberField.Completion.placeSmul τ P₀)
        = Commons.NumberTheory.NumberField.Completion.placeSmul σ
            (Commons.NumberTheory.NumberField.Completion.placeSmul τ⁻¹
              (Commons.NumberTheory.NumberField.Completion.placeSmul τ P₀)) :=
          Commons.NumberTheory.NumberField.Completion.placeSmul_mul σ τ⁻¹ _
      _ = Commons.NumberTheory.NumberField.Completion.placeSmul σ P₀ := by rw [hτ]
      _ = Commons.NumberTheory.NumberField.Completion.placeSmul τ P₀ := h1
  exact mul_inv_eq_one.mp
    (eq_one_of_placeSmul_eq_of_splitsCompletely hp
      (Commons.NumberTheory.NumberField.Completion.liesOver_placeSmul p P₀ τ) h2)

/-- **Two Galois elements agreeing on the primes above a completely split prime are equal**, for
the `SMul` instance of `NK.Chebotarev`. -/
theorem eq_of_forall_smul_eq_of_splitsCompletely {p : NK.Chebotarev.PrimeIdeal K}
    (hp : SplitsCompletely (K := K) (L := L) p) {σ τ : Gal(L/K)}
    (h : ∀ P : NK.Chebotarev.PrimeIdeal L, P.asIdeal.LiesOver p.asIdeal → σ • P = τ • P) :
    σ = τ :=
  eq_of_forall_placeSmul_eq_of_splitsCompletely hp fun P hP => by
    rw [placeSmul_eq_smul, placeSmul_eq_smul]; exact h P hP

end Freeness

end NK.UchidaKummer
