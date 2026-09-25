import Mathlib
import Submission.NK.Chebotarev.Basic
import Submission.NK.Mine.FrobeniusGenerateTopUnramified
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_compl
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_of_density_zero
import Submission.Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one

/-!
# Frobenius elements away from a finite set generate, in every universe

The lemma `NK.GlobalCFTdeep.SecondInequality.frobeniusGenerateTop_of_notMem` proves that, for a
finite Galois extension `L / K` of number fields and a finite set `T` of primes of `K`, the
Frobenius elements at the primes `p ∉ T` generate `Gal(L/K)`.  It is however stated for
`K L : Type` (universe `0`), so it cannot be applied to number fields living in an arbitrary
universe.  Here we reproduce its density-theoretic proof verbatim with `K L : Type*`, and deduce
the requested form: a subgroup containing every Frobenius at every prime outside `T` is everything.

* `closure_isFrobAtPrime_of_notMem_eq_top` — the polymorphic "generation" statement;
* `eq_top_of_forall_isFrobAtPrime_of_notMem` — the requested corollary: if `H ≤ Gal(L/K)` contains
  all Frobenius elements at all primes `p ∉ T`, then `H = ⊤`.

The mathematical content is unchanged from the `Type`-version: let `S` be the set of Frobenius
elements at primes outside `T` and `H = closure S`; `S` is conjugation invariant, so `H` is normal
and `F := fixedField H` is Galois over `K`.  At a prime `p ∉ T`, any prime `q` of `F` above `p` is
covered by a prime `P` of `L`; a Frobenius `σ` at `P` lies in `S ⊆ H`, hence acts trivially on `F`,
and restricting it to the normal intermediate field `F` (`IsFrobAtRestrictNormalHom`) shows that
`1` is a Frobenius at `q`.  If `p` is unramified in `F`, the order of a Frobenius equals the
inertia degree (`IsFrobAtOrderOfEqInertiaDeg`), so `q` has residue degree `1` and the fundamental
identity forces `p` to split completely in `F`.  Hence the complement of the completely split
primes of `F / K` is contained in the finite set `T ∪ {p ramified in F}`, giving density `0` for the
complement, while the completely split primes have density `1 / [F : K]`; thus `[F : K] = 1`,
`F = K` and `H = ⊤`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open IsDedekindDomain

namespace NK.CFTLib.Arl

open NK.Chebotarev

/-- **Frobenius elements away from a finite set generate the Galois group** (universe-polymorphic
form of `NK.GlobalCFTdeep.SecondInequality.frobeniusGenerateTop_of_notMem`). -/
theorem closure_isFrobAtPrime_of_notMem_eq_top {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (T : Finset (PrimeIdeal K)) :
    Subgroup.closure {σ : Gal(L/K) | ∃ p : PrimeIdeal K, p ∉ T ∧
      IsFrobAtPrime (K := K) (L := L) p σ} = ⊤ := by
  classical
  set S : Set Gal(L/K) := {σ : Gal(L/K) | ∃ p : PrimeIdeal K, p ∉ T ∧
    IsFrobAtPrime (K := K) (L := L) p σ} with hSdef
  set H : Subgroup Gal(L/K) := Subgroup.closure S with hHdef
  -- ## `S` is conjugation invariant, so `H` is normal
  have hconj : ∀ ⦃σ : Gal(L/K)⦄, σ ∈ S → ∀ τ : Gal(L/K), τ * σ * τ⁻¹ ∈ S := by
    intro σ hσ τ
    obtain ⟨p, hpT, hfrob⟩ := hσ
    exact ⟨p, hpT, isFrobAtPrime_conj hfrob τ⟩
  have hconj_sub : Group.conjugatesOfSet S ⊆ S := by
    intro x hx
    obtain ⟨y, hy, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, hc'⟩ := isConj_iff.mp hc
    rw [← hc']
    exact hconj hy c
  have hclosure_eq : Subgroup.normalClosure S = Subgroup.closure S :=
    le_antisymm (Subgroup.closure_mono hconj_sub) Subgroup.closure_le_normalClosure
  have hHnormal : H.Normal := by
    rw [hHdef]
    have hnorm : (Subgroup.normalClosure S).Normal := inferInstance
    rwa [hclosure_eq] at hnorm
  haveI : H.Normal := hHnormal
  set F : IntermediateField K L := IntermediateField.fixedField H with hFdef
  haveI hFgal : IsGalois K F := by rw [hFdef]; infer_instance
  -- ## At a prime `p ∉ T` every prime of `F` above `p` has trivial Frobenius
  have key : ∀ (p : PrimeIdeal K) (q : PrimeIdeal F),
      p ∉ T → q.asIdeal.LiesOver p.asIdeal → IsFrobAt (K := K) (L := F) q 1 := by
    intro p q hpT hq
    obtain ⟨P0⟩ := (inferInstance : Nonempty (q.asIdeal.primesOver
      (NumberField.RingOfIntegers L)))
    let P : PrimeIdeal L :=
      ⟨P0.1, P0.2.1, Ideal.ne_bot_of_mem_primesOver q.ne_bot P0.2⟩
    have hPq : P.asIdeal.LiesOver q.asIdeal := P0.2.2
    have hPp : P.asIdeal.LiesOver p.asIdeal := liesOver_trans hPq hq
    obtain ⟨σ, hσ⟩ := exists_isFrobAt (K := K) (L := L) p P hPp
    have hσS : σ ∈ S := by
      rw [hSdef]
      exact ⟨p, hpT, P, hPp, hσ⟩
    have hσH : σ ∈ H := Subgroup.subset_closure hσS
    have hσfix : σ ∈ (IntermediateField.fixedField H).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_fixedField H]
      exact hσH
    have hone : AlgEquiv.restrictNormalHom (K₁ := L) F σ = 1 := by
      rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
      exact hσfix
    have hfrob := IsFrobAtRestrictNormalHom (K := K) (M := L) F hPp hσ
    have hq_eq : P.under (NumberField.RingOfIntegers F) = q :=
      IsDedekindDomain.HeightOneSpectrum.ext
        (by rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]; exact hPq.over.symm)
    rw [hq_eq, hone] at hfrob
    simpa using hfrob
  -- ## Primes outside `T` which are unramified in `F` split completely in `F`
  have hsplit : ∀ p : PrimeIdeal K, p ∉ T →
      p.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers F) = 1 →
      (p.asIdeal.primesOver (NumberField.RingOfIntegers F)).ncard = Module.finrank K F := by
    intro p hpT heIn
    obtain ⟨q0⟩ := (inferInstance : Nonempty (p.asIdeal.primesOver
      (NumberField.RingOfIntegers F)))
    let q : PrimeIdeal F :=
      ⟨q0.1, q0.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot q0.2⟩
    have hq : q.asIdeal.LiesOver p.asIdeal := q0.2.2
    haveI := hq
    have he1 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
      rw [Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal q.asIdeal (F ≃ₐ[K] F)] at heIn
      exact heIn
    have hf1 : q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1 := by
      have h := IsFrobAtOrderOfEqInertiaDeg (K := K) (L := F) hq he1
        (key p q hpT hq)
      rw [orderOf_one] at h
      exact h.symm
    rw [Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely p]
    refine ⟨?_, ?_⟩
    · rw [Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal q.asIdeal (F ≃ₐ[K] F)]
      exact he1
    · rw [Ideal.inertiaDegIn_eq_inertiaDeg p.asIdeal q.asIdeal (F ≃ₐ[K] F)]
      exact hf1
  -- ## Density comparison
  set splitSet : Set (PrimeIdeal K) := {p |
    (p.asIdeal.primesOver (NumberField.RingOfIntegers F)).ncard = Module.finrank K F}
    with hsplitdef
  set Ram : Set (PrimeIdeal K) := {p |
    p.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers F) ≠ 1} with hRamdef
  have hRamFin : Ram.Finite := by
    rw [hRamdef]
    have hF : ({Q : PrimeIdeal F |
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1}).Finite :=
      Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
    refine (hF.image (fun Q : PrimeIdeal F =>
      IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) Q)).subset ?_
    rintro p hp
    obtain ⟨q0⟩ := (inferInstance : Nonempty (p.asIdeal.primesOver
      (NumberField.RingOfIntegers F)))
    let q : PrimeIdeal F :=
      ⟨q0.1, q0.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot q0.2⟩
    have hq : q.asIdeal.LiesOver p.asIdeal := q0.2.2
    refine ⟨q, ?_, ?_⟩
    · haveI := hq
      simp only [Set.mem_ofPred_eq] at hp
      rw [Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal q.asIdeal (F ≃ₐ[K] F)] at hp
      simp only [Set.mem_ofPred_eq]
      exact hp
    · exact IsDedekindDomain.HeightOneSpectrum.ext (by
        rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]; exact hq.over.symm)
  have hTFin : (T : Set (PrimeIdeal K)).Finite := T.finite_toSet
  have hcomplSub : splitSetᶜ ⊆ (T : Set (PrimeIdeal K)) ∪ Ram := by
    intro p hp
    by_contra hmem
    rw [Set.mem_union, not_or] at hmem
    obtain ⟨hpT, hpRam⟩ := hmem
    refine hp ?_
    have heIn : p.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers F) = 1 := by
      by_contra hne
      exact hpRam hne
    rw [hsplitdef]
    exact hsplit p hpT heIn
  have hcomplDens0 : NumberField.Set.HasDirichletDensity splitSetᶜ 0 :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_subset
      (Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite
        (hTFin.union hRamFin)) hcomplSub
  have hcomplDens : NumberField.Set.HasDirichletDensity splitSetᶜ
      (1 - 1 / (Module.finrank K F : ℝ)) :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_compl
      (Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
        (K := K) (L := F))
  have heq : 1 - 1 / (Module.finrank K F : ℝ) = 0 := tendsto_nhds_unique hcomplDens hcomplDens0
  have hfpos : (0 : ℝ) < (Module.finrank K F : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := K) (M := F)
  have hf1 : (Module.finrank K F : ℝ) = 1 := by
    field_simp at heq
    linarith
  have hfin1 : Module.finrank K F = 1 := by exact_mod_cast hf1
  -- ## Hence `F = K` and `H = ⊤`
  have hFbot : F = ⊥ := IntermediateField.finrank_eq_one_iff.mp hfin1
  have hfixed : IntermediateField.fixedField H = ⊥ := by rw [← hFdef]; exact hFbot
  have h1 : (IntermediateField.fixedField H).fixingSubgroup = ⊤ := by
    rw [hfixed, IntermediateField.fixingSubgroup_bot]
  rw [IntermediateField.fixingSubgroup_fixedField H] at h1
  exact h1

-- Take the subgroup `H ≤ Gal(L/K)` and let `F := IntermediateField.fixedField H`.  Every `p ∉ T` picks a Frobenius
-- `σ` (`NK.Chebotarev.exists_isFrobAtPrime`), which lies in `H` and hence acts trivially on `F`; restricting it
-- (`NK.Chebotarev.IsFrobAtRestrictNormalHom`) exhibits `1` as a Frobenius at a prime of `F` over `p`, so for `p ∉ T`
-- unramified in `L` (hence in `F`) `IsFrobAtOrderOfEqInertiaDeg` gives inertia degree `1`, and the fundamental identity
-- gives that `p` splits completely in `F`.  Hence the completely split primes of `F/K` contain the complement of the
-- finite set `T ∪ {p ramified in L}`, so their complement has Dirichlet density `0`, while they themselves have density
-- `1 / [F : K]`; therefore `[F : K] = 1`, `F = ⊥` and `H = ⊤`.
-- WARNING: prove this for `K L : Type*`; the existing `NK.GlobalCFTdeep.SecondInequality.frobeniusGenerateTop_of_notMem`
-- (identical statement but for `Type`, universe `0`) CANNOT be applied here (application is a universe mismatch).  Adapt the
-- sorry-free polymorphic proof of `NK.Mine.FrobeniusGenerateTopUnramified` (same Dedekind-density argument, unramified
-- primes only) with the extra finite set `T`; the density lemmas in `Commons.NumberTheory.NumberField.Set` are `Type*`.
theorem eq_top_of_forall_isFrobAtPrime_of_notMem {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (T : Finset (NK.Chebotarev.PrimeIdeal K)) (H : Subgroup Gal(L/K))
    (hH : ∀ (p : NK.Chebotarev.PrimeIdeal K), p ∉ T → ∀ σ : Gal(L/K),
      NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) p σ → σ ∈ H) :
    H = ⊤ := by
  -- The set of Frobenius elements at primes outside `T` is contained in `H`, hence so is the
  -- subgroup it generates; that subgroup is everything.
  have hSsub : {σ : Gal(L/K) | ∃ p : PrimeIdeal K, p ∉ T ∧
      IsFrobAtPrime (K := K) (L := L) p σ} ⊆ (H : Set Gal(L/K)) := by
    rintro σ ⟨p, hpT, hfrob⟩
    exact hH p hpT σ hfrob
  have hle : Subgroup.closure {σ : Gal(L/K) | ∃ p : PrimeIdeal K, p ∉ T ∧
      IsFrobAtPrime (K := K) (L := L) p σ} ≤ H := (Subgroup.closure_le H).mpr hSsub
  have htop := closure_isFrobAtPrime_of_notMem_eq_top (K := K) (L := L) T
  exact top_le_iff.mp (htop ▸ hle)

end NK.CFTLib.Arl
