/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uchida's Kummer-theoretic embedding problem

`NK.UchidaKummer.IsKummerEmbeddingProblem ℓ` (nu2d §6, Lemma `lem:embedding problem`, the
case `n = 1`): for a finite Galois extension `L / ℚ` containing `μ_ℓ` and a finite set `S` of
primes of `L`, there is a finite Galois extension `M / L` of degree `ℓ ^ [L : ℚ]` in which every
prime of `S` splits completely.

The construction is Uchida's: choose `[L : ℚ]` primes `P` of `L` outside `S`, and for each one a
unit `b_P ∈ Lˣ` whose `ℓ`-power class is nontrivial at `P` and trivial at all the other chosen
primes and at `S` (Kummer local surjection = weak approximation + openness of the `ℓ`-th power
subgroups).  Kummer theory then gives that the compositum `M = ∏_P L(b_P^{1/ℓ})` has degree
`ℓ ^ [L : ℚ]` over `L` (the local conditions make the classes independent), and that every prime of
`S` splits completely in `M`.

## Main results

* `exists_pow_eq_of_localPowClass_eq_one`, `localPowClass_eq_one_of_exists_pow_eq` — the dictionary
  between `localPowClass = 1` and being a local `ℓ`-th power;
* `isKummerEmbeddingProblem` — the embedding problem.

The local Kummer surjection, the splitting of the compositum and its degree are
`NK.UchidaKummer.Embedding.exists_localPowClass_family`,
`NK.UchidaKummer.Embedding.localDeg_eq_one_of_kummerSup` and
`NK.UchidaKummer.Embedding.finrank_kummerSup`.
-/
import Mathlib
import Submission.NK.UchidaKummer.Defs
import Submission.NK.UchidaKummer.Embedding.KummerSup
import Submission.NK.UchidaKummer.Embedding.localDeg_eq_one_of_kummerSup
import Submission.NK.UchidaKummer.Embedding.exists_localPowClass_family
import Submission.NK.UchidaKummer.Embedding.transfer_ellPow_adicCompletion
import Submission.NK.UchidaKummer.Embedding.finrank_kummerSup
import Submission.NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff
import Submission.NK.UchidaKummer.Kummer.isKummerLocalDichotomy_of_exists_isPrimitiveRoot
import Submission.NK.UchidaKummer.Differentiation.exists_kummerField_localDeg_eq_of_surjective
import Submission.NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one
import Submission.NK.UchidaKummer.API.localDeg_tower
import Submission.NK.UchidaKummer.SplitPrimes
import Submission.NK.UchidaKummer.Approximation.isWeakApproximation
import Submission.NK.UchidaKummer.Approximation.isOpenEllPowSubgroup
import Submission.NK.UchidaKummer.Approximation.isKummerSurjective_of_weakApproximation
import Submission.NK.UchidaKummer.Approximation.exists_not_ellPow_unit_adicCompletion
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver

import Mathlib
import Submission.NK.UchidaKummer.Defs
import Submission.NK.UchidaKummer.Embedding.KummerSup
import Submission.NK.UchidaKummer.Embedding.localDeg_eq_one_of_kummerSup
import Submission.NK.UchidaKummer.Embedding.exists_localPowClass_family
import Submission.NK.UchidaKummer.Embedding.transfer_ellPow_adicCompletion
import Submission.NK.UchidaKummer.Embedding.finrank_kummerSup
import Submission.NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff
import Submission.NK.UchidaKummer.Kummer.isKummerLocalDichotomy_of_exists_isPrimitiveRoot
import Submission.NK.UchidaKummer.Differentiation.exists_kummerField_localDeg_eq_of_surjective
import Submission.NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one
import Submission.NK.UchidaKummer.API.localDeg_tower
import Submission.NK.UchidaKummer.SplitPrimes
import Submission.NK.UchidaKummer.Approximation.isWeakApproximation
import Submission.NK.UchidaKummer.Approximation.isOpenEllPowSubgroup
import Submission.NK.UchidaKummer.Approximation.isKummerSurjective_of_weakApproximation
import Submission.NK.UchidaKummer.Approximation.exists_not_ellPow_unit_adicCompletion
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver

open scoped Classical
open IntermediateField
namespace NK.UchidaKummer.Embedding

/-- `localPowClass = 1` says exactly that `b` is a local `ℓ`-th power. -/
lemma exists_pow_eq_of_localPowClass_eq_one {L : Type*} [Field L] [NumberField L] (ℓ : ℕ)
    (𝔮 : NK.Chebotarev.PrimeIdeal L) (b : Lˣ)
    (h : NK.UchidaKummer.localPowClass L ℓ 𝔮 b = 1) :
    ∃ c : (𝔮.adicCompletion L)ˣ,
      algebraMap L (𝔮.adicCompletion L) (b : L) = (c : 𝔮.adicCompletion L) ^ ℓ := by
  have hmem : Units.map (algebraMap L (𝔮.adicCompletion L)).toMonoidHom b ∈
      NK.UchidaKummer.ellPowSubgroup (𝔮.adicCompletion L) ℓ := by
    rw [← QuotientGroup.eq_one_iff]
    simpa [NK.UchidaKummer.localPowClass, MonoidHom.comp_apply] using h
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hmem
  exact ⟨c, by
    have h2 := congrArg (fun z : (𝔮.adicCompletion L)ˣ => (z : 𝔮.adicCompletion L)) hc
    simpa using h2.symm⟩

lemma localPowClass_eq_one_of_exists_pow_eq {L : Type*} [Field L] [NumberField L] (ℓ : ℕ)
    (𝔮 : NK.Chebotarev.PrimeIdeal L) (b : Lˣ)
    (h : ∃ c : (𝔮.adicCompletion L)ˣ,
      algebraMap L (𝔮.adicCompletion L) (b : L) = (c : 𝔮.adicCompletion L) ^ ℓ) :
    NK.UchidaKummer.localPowClass L ℓ 𝔮 b = 1 := by
  obtain ⟨c, hc⟩ := h
  have hmem : Units.map (algebraMap L (𝔮.adicCompletion L)).toMonoidHom b ∈
      NK.UchidaKummer.ellPowSubgroup (𝔮.adicCompletion L) ℓ :=
    ⟨c, (Units.ext (by simpa using hc)).symm⟩
  rw [NK.UchidaKummer.localPowClass, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  exact hmem


set_option linter.style.haveILetI false

theorem isKummerEmbeddingProblem (ℓ : ℕ) (hℓ : ℓ.Prime) :
    NK.UchidaKummer.IsKummerEmbeddingProblem ℓ := by
  classical
  intro L _ _ _ _ _ hμ S
  obtain ⟨ζ, hζ⟩ := hμ
  -- Step 1: a finite set `T` of primes of `L` of cardinality `[L : ℚ]`, disjoint from `S`.
  have hT : ∃ T : Finset (NK.Chebotarev.PrimeIdeal L),
      T.card = Module.finrank ℚ L ∧ ∀ 𝔮 ∈ S, 𝔮 ∉ T := by
    have hiter : ∀ n : ℕ, ∃ T : Finset (NK.Chebotarev.PrimeIdeal L),
        T.card = n ∧ ∀ 𝔮 ∈ S, 𝔮 ∉ T := by
      intro n
      induction n with
      | zero => exact ⟨∅, by simp⟩
      | succ k ih =>
          obtain ⟨T, hcard, hdisj⟩ := ih
          obtain ⟨P, hPnot, -⟩ :=
            NK.UchidaKummer.exists_splitsCompletely_notMem (K := L) (L := L) (T ∪ S)
          refine ⟨insert P T, ?_, ?_⟩
          · rw [Finset.card_insert_of_notMem]
            · omega
            · exact fun h => hPnot (Finset.mem_union_left _ h)
          · intro 𝔮 h𝔮 hmem
            rw [Finset.mem_insert] at hmem
            rcases hmem with h | h
            · subst h; exact hPnot (Finset.mem_union_right _ h𝔮)
            · exact hdisj 𝔮 h𝔮 h
    exact hiter (Module.finrank ℚ L)
  obtain ⟨T, hTcard, hTdisj⟩ := hT
  -- Step 2: the family `b`.
  obtain ⟨b, hbnot, hbtriv⟩ := exists_localPowClass_family (L := L) ℓ hℓ T S hTdisj
  have hnot : ∀ P ∈ T, ¬ ∃ c : (P.adicCompletion L)ˣ,
      algebraMap L (P.adicCompletion L) (b P : L) = (c : P.adicCompletion L) ^ ℓ := by
    intro P hP hc
    exact hbnot P hP (localPowClass_eq_one_of_exists_pow_eq ℓ P (b P) hc)
  have htriv : ∀ P ∈ T, ∀ Q ∈ T, Q ≠ P → ∃ c : (Q.adicCompletion L)ˣ,
      algebraMap L (Q.adicCompletion L) (b P : L) = (c : Q.adicCompletion L) ^ ℓ := by
    intro P hP Q hQ hne
    exact exists_pow_eq_of_localPowClass_eq_one ℓ Q (b P)
      (hbtriv P hP Q (Finset.mem_union_right _ hQ) hne)
  -- Step 3: the field `M`.
  set M : IntermediateField L (AlgebraicClosure L) := kummerSup (K' := AlgebraicClosure L) ℓ T b with hMdef
  -- Step 4: the degree.
  have hdeg : Module.finrank L ↥M = ℓ ^ T.card := finrank_kummerSup (K' := AlgebraicClosure L) ℓ hℓ hζ T b hnot htriv
  haveI : FiniteDimensional L ↥M := FiniteDimensional.of_finrank_pos (by rw [hdeg]; exact pow_pos hℓ.pos _)
  haveI : NumberField ↥M :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := L) M
  -- Step 5: `M / L` is Galois.
  haveI hGal : IsGalois L ↥M := by
    have hM : M = ⨆ P : ↥T, NK.LocalAnabelian.kummerField (K' := AlgebraicClosure L) ℓ (b P.1) := by
      rw [hMdef, kummerSup, Finset.sup_eq_iSup]
      exact le_antisymm
        (iSup_le fun i => iSup_le fun h => le_iSup_of_le ⟨i, h⟩ le_rfl)
        (iSup_le fun P => le_iSup_of_le P.1 (le_iSup_of_le P.2 le_rfl))
    have hnotmem : ∀ P : ↥T, b P.1 ∉ NK.LocalAnabelian.powSubgroup ℓ L := by
      intro P hmem
      obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hmem
      rw [powMonoidHom_apply] at hc
      refine hnot P.1 P.2 ⟨Units.map (algebraMap L (P.1.adicCompletion L)).toMonoidHom c, ?_⟩
      have hc' : ((c ^ ℓ : Lˣ) : L) = (b P.1 : L) := congrArg (fun u : Lˣ => (u : L)) hc
      rw [Units.val_pow_eq_pow_val] at hc'
      show algebraMap L (P.1.adicCompletion L) (b P.1 : L)
        = (algebraMap L (P.1.adicCompletion L) (c : L)) ^ ℓ
      rw [← hc', map_pow]
    haveI : ∀ P : ↥T, Normal L ↥(NK.LocalAnabelian.kummerField (K' := AlgebraicClosure L) ℓ (b P.1)) := by
      intro P
      exact (NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (k := L) (K' := AlgebraicClosure L)
        ℓ hℓ hζ (b P.1) (hnotmem P)).1.to_normal
    haveI : Normal L ↥M := by
      rw [hM]
      exact IntermediateField.normal_iSup L (AlgebraicClosure L) _
    exact IsGalois.mk
  -- Step 6: the primes of `S` split completely.
  have hsplit : ∀ 𝔮 : S, SplitsCompletely (K := L) (L := ↥M) 𝔮.1 := by
    intro 𝔮
    rw [NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one]
    intro P hP
    have hpow : ∀ Q ∈ T, ∃ c : (𝔮.1.adicCompletion L)ˣ,
        algebraMap L (𝔮.1.adicCompletion L) (b Q : L) = (c : 𝔮.1.adicCompletion L) ^ ℓ := by
      intro Q hQ
      have hne : 𝔮.1 ≠ Q := fun h => hTdisj 𝔮.1 𝔮.2 (h ▸ hQ)
      exact exists_pow_eq_of_localPowClass_eq_one ℓ 𝔮.1 (b Q)
        (hbtriv Q hQ 𝔮.1 (Finset.mem_union_left _ 𝔮.2) hne)
    exact localDeg_eq_one_of_kummerSup (K' := AlgebraicClosure L) ℓ hℓ hζ T b 𝔮.1 hpow P hP
  -- Step 7: assemble.
  refine ⟨↥M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hsplit, ?_⟩
  rw [IsGalois.card_aut_eq_finrank L ↥M, hdeg, hTcard, ← IsGalois.card_aut_eq_finrank ℚ L]

end NK.UchidaKummer.Embedding
