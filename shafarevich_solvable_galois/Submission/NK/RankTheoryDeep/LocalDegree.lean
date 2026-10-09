import Submission.NK.RankTheoryDeep.IdeleRankDefs
import Submission.NK.ReconstructField.finrank_eq_of_localCorrespondence
import Submission.NK.LocalInputs.Defs
import Submission.Commons.NumberTheory.NumberField.Completion.sumFinrank_completions_eq_finrank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local degree, the primes above `ℓ`, and their sum

Three elementary number-theoretic inputs of the idèle-side rank computation:

* `NK.RankTheoryDeep.primesOver_span_iff_mem` — `q` lies over `(ℓ)` iff `ℓ ∈ q`;
* `NK.RankTheoryDeep.exists_prime_charP_quotient_of_notMem` — the residue characteristic of a
  finite prime `q ∌ ℓ` is a prime `p ≠ ℓ` (this is what feeds the vanishing
  `NK.RankTheoryDeep.dual_localUnits_eq_zero_of_residueChar_ne`);
* `NK.RankTheoryDeep.sum_localDeg_eq_finrank` — `∑_{q | ℓ} e_q f_q = [K : ℚ]`, the global
  fundamental identity, so that the sum of the local degrees over the places above `ℓ` is the
  global degree.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField

namespace NK.RankTheoryDeep

universe u

/-- A nonzero prime `q` of `𝓞 K` lies over the rational prime `ℓ` if and only if `ℓ ∈ q`. -/
theorem primesOver_span_iff_mem (K : Type u) [Field K] [NumberField K] {ℓ : ℕ} [Fact ℓ.Prime]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    q.asIdeal ∈ (Ideal.span {(ℓ : ℤ)}).primesOver (NumberField.RingOfIntegers K) ↔
      (ℓ : NumberField.RingOfIntegers K) ∈ q.asIdeal := by
  constructor
  · intro h
    have hover : q.asIdeal.LiesOver (Ideal.span {(ℓ : ℤ)}) := h.2
    have h1 : (ℓ : ℤ) ∈ q.asIdeal.under ℤ := by
      rw [← hover.over]
      exact Ideal.subset_span (Set.mem_singleton _)
    have h2 : (algebraMap ℤ (NumberField.RingOfIntegers K)) (ℓ : ℤ) ∈ q.asIdeal := h1
    simpa using h2
  · intro h
    refine ⟨q.isPrime, Ideal.LiesOver.mk ?_⟩
    refine Ideal.IsMaximal.eq_of_le ?_ ?_ ?_
    · rw [← Ideal.irreducible_iff_isMaximal_span_singleton (p := (ℓ : ℤ))
        (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)]
      exact (Nat.prime_iff_prime_int.mp (Fact.out : ℓ.Prime)).irreducible
    · intro htop
      have h1 : (1 : ℤ) ∈ q.asIdeal.under ℤ := by rw [htop]; exact Submodule.mem_top
      have h2 : (algebraMap ℤ (NumberField.RingOfIntegers K)) 1 ∈ q.asIdeal := h1
      refine q.isPrime.ne_top (Ideal.eq_top_iff_one _ |>.mpr ?_)
      simpa using h2
    · intro x hx
      rw [Ideal.mem_under]
      obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton.mp hx
      rw [map_mul]
      exact Ideal.mul_mem_right _ _ (by simpa using h)

/-- **The residue characteristic of a finite prime not containing `ℓ`.** -/
theorem exists_prime_charP_quotient_of_notMem (K : Type u) [Field K] [NumberField K]
    {ℓ : ℕ} [Fact ℓ.Prime]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h : (ℓ : NumberField.RingOfIntegers K) ∉ q.asIdeal) :
    ∃ p : ℕ, p.Prime ∧ p ≠ ℓ ∧
      CharP (NumberField.RingOfIntegers K ⧸ q.asIdeal) p := by
  refine ⟨(Rat.HeightOneSpectrum.primesEquiv (NK.LocalInputs.primeBelow K q)).1,
    (Rat.HeightOneSpectrum.primesEquiv (NK.LocalInputs.primeBelow K q)).2, ?_, ?_⟩
  · intro hp
    have hch : CharP (NumberField.RingOfIntegers K ⧸ q.asIdeal) ℓ :=
      hp ▸ NK.ReconstructField.charP_of_liesOver q (NK.LocalInputs.primeBelow K q)
        (NK.LocalInputs.primeBelow_liesOver K q)
    exact h ((NK.ReconstructField.charP_quotient_iff_mem q (Fact.out : ℓ.Prime)).mp hch)
  · exact NK.ReconstructField.charP_of_liesOver q (NK.LocalInputs.primeBelow K q)
      (NK.LocalInputs.primeBelow_liesOver K q)

/-- **The sum of the local degrees over the places above `ℓ` is the global degree**:
`∑_{q | ℓ} e_q f_q = [K : ℚ]`. -/
theorem sum_localDeg_eq_finrank (K : Type u) [Field K] [NumberField K] {ℓ : ℕ} [Fact ℓ.Prime] :
    (∑ q : ↑((Ideal.span {(ℓ : ℤ)}).primesOver (NumberField.RingOfIntegers K)),
        (q : Ideal (NumberField.RingOfIntegers K)).ramificationIdx ℤ *
          (q : Ideal (NumberField.RingOfIntegers K)).inertiaDeg ℤ)
      = Module.finrank ℚ K := by
  haveI hp : ((Ideal.span {(ℓ : ℤ)}) : Ideal ℤ).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)]
    exact Nat.prime_iff_prime_int.mp (Fact.out : ℓ.Prime)
  have h := Ideal.sum_ramification_inertia_eq_finrank (R := ℤ)
    (p := (Ideal.span {(ℓ : ℤ)} : Ideal ℤ)) (S := NumberField.RingOfIntegers K)
  rw [NumberField.RingOfIntegers.rank] at h
  exact h

end NK.RankTheoryDeep
