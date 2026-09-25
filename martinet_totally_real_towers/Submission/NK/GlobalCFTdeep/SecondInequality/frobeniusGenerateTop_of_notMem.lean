import Mathlib
import Submission.NK.Chebotarev.FrobeniusGenerateTop

/-!
# Frobenius elements away from a finite set of primes generate the Galois group

For a finite Galois extension `L / K` of number fields and any finite set `T` of primes of `K`,
the Frobenius elements at the primes `p ∉ T` already generate `Gal(L/K)`:

`Subgroup.closure {σ | ∃ p ∉ T, IsFrobAtPrime p σ} = ⊤`.

The proof follows the scheme of `NK.Chebotarev.FrobeniusGenerateTop`.  Let `S` be the set of
Frobenius elements at primes outside `T` and `H = closure S`, which is normal because `S` is
conjugation invariant.  Let `F` be the fixed field of `H`.  For `p ∉ T` and any prime `q` of `F`
over `p`, a Frobenius `σ` at a prime of `L` over `q` lies in `S ⊆ H`, hence acts trivially on `F`;
restricting to the normal intermediate field `F` (`IsFrobAtRestrictNormalHom`) shows that `1` is a
Frobenius at `q`.  If in addition `p` is unramified in `F`, the order of a Frobenius equals the
inertia degree (`IsFrobAtOrderOfEqInertiaDeg`), so the inertia degree is `1`, and the fundamental
identity forces `p` to split completely in `F`.

Hence the complement of the set of completely split primes of `F / K` is contained in the union of
`T` and the finite set of primes ramifying in `F`.  By Dedekind's density theorem for the
completely split primes (`hasDirichletDensity_primes_splitsCompletely`, the trivial conjugacy
class case, available unconditionally) the completely split primes of `F / K` have Dirichlet
density `1 / [F : K]`, whence their complement has density `1 - 1 / [F : K]`; being contained in a
finite set it also has density `0`.  Thus `1 / [F : K] = 1`, i.e. `F = K` and `H = ⊤`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open IsDedekindDomain

namespace NK.GlobalCFTdeep.SecondInequality

theorem frobeniusGenerateTop_of_notMem {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (T : Finset (NK.Chebotarev.PrimeIdeal K)) :
    Subgroup.closure {σ : Gal(L/K) | ∃ p : NK.Chebotarev.PrimeIdeal K, p ∉ T ∧
      NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) p σ} = ⊤ := by
  classical
  set S : Set Gal(L/K) := {σ : Gal(L/K) | ∃ p : NK.Chebotarev.PrimeIdeal K, p ∉ T ∧
    NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) p σ} with hSdef
  set H : Subgroup Gal(L/K) := Subgroup.closure S with hHdef
  -- ## `S` is conjugation invariant, so `H` is normal
  have hconj : ∀ ⦃σ : Gal(L/K)⦄, σ ∈ S → ∀ τ : Gal(L/K), τ * σ * τ⁻¹ ∈ S := by
    intro σ hσ τ
    obtain ⟨p, hpT, hfrob⟩ := hσ
    exact ⟨p, hpT, NK.Chebotarev.isFrobAtPrime_conj hfrob τ⟩
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
  have key : ∀ (p : NK.Chebotarev.PrimeIdeal K) (q : NK.Chebotarev.PrimeIdeal F),
      p ∉ T → q.asIdeal.LiesOver p.asIdeal →
      NK.Chebotarev.IsFrobAt (K := K) (L := F) q 1 := by
    intro p q hpT hq
    obtain ⟨P0⟩ := (inferInstance : Nonempty (q.asIdeal.primesOver
      (NumberField.RingOfIntegers L)))
    let P : NK.Chebotarev.PrimeIdeal L :=
      ⟨P0.1, P0.2.1, Ideal.ne_bot_of_mem_primesOver q.ne_bot P0.2⟩
    have hPq : P.asIdeal.LiesOver q.asIdeal := P0.2.2
    have hPp : P.asIdeal.LiesOver p.asIdeal := NK.Chebotarev.liesOver_trans hPq hq
    obtain ⟨σ, hσ⟩ := NK.Chebotarev.exists_isFrobAt (K := K) (L := L) p P hPp
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
    have hfrob := NK.Chebotarev.IsFrobAtRestrictNormalHom (K := K) (M := L) F hPp hσ
    have hq_eq : P.under (NumberField.RingOfIntegers F) = q :=
      IsDedekindDomain.HeightOneSpectrum.ext
        (by rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]; exact hPq.over.symm)
    rw [hq_eq, hone] at hfrob
    simpa using hfrob
  -- ## Primes outside `T` which are unramified in `F` split completely in `F`
  have hsplit : ∀ p : NK.Chebotarev.PrimeIdeal K, p ∉ T →
      p.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers F) = 1 →
      (p.asIdeal.primesOver (NumberField.RingOfIntegers F)).ncard = Module.finrank K F := by
    intro p hpT heIn
    obtain ⟨q0⟩ := (inferInstance : Nonempty (p.asIdeal.primesOver
      (NumberField.RingOfIntegers F)))
    let q : NK.Chebotarev.PrimeIdeal F :=
      ⟨q0.1, q0.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot q0.2⟩
    have hq : q.asIdeal.LiesOver p.asIdeal := q0.2.2
    haveI := hq
    have he1 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
      rw [Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal q.asIdeal (F ≃ₐ[K] F)] at heIn
      exact heIn
    have hf1 : q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1 := by
      have h := NK.Chebotarev.IsFrobAtOrderOfEqInertiaDeg (K := K) (L := F) hq he1
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
  set splitSet : Set (NK.Chebotarev.PrimeIdeal K) := {p |
    (p.asIdeal.primesOver (NumberField.RingOfIntegers F)).ncard = Module.finrank K F}
    with hsplitdef
  set Ram : Set (NK.Chebotarev.PrimeIdeal K) := {p |
    p.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers F) ≠ 1} with hRamdef
  have hRamFin : Ram.Finite := by
    rw [hRamdef]
    have hF : ({Q : NK.Chebotarev.PrimeIdeal F |
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1}).Finite :=
      Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
    refine (hF.image (fun Q : NK.Chebotarev.PrimeIdeal F =>
      IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) Q)).subset ?_
    rintro p hp
    obtain ⟨q0⟩ := (inferInstance : Nonempty (p.asIdeal.primesOver
      (NumberField.RingOfIntegers F)))
    let q : NK.Chebotarev.PrimeIdeal F :=
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
  have hTFin : (T : Set (NK.Chebotarev.PrimeIdeal K)).Finite := T.finite_toSet
  have hcomplSub : splitSetᶜ ⊆ (T : Set (NK.Chebotarev.PrimeIdeal K)) ∪ Ram := by
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

end NK.GlobalCFTdeep.SecondInequality
