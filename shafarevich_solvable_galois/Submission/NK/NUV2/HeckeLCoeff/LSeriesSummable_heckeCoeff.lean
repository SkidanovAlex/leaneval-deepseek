import Mathlib
import Submission.NK.HeckeL.Basic
import Submission.Commons.NumberTheory.NumberField.DedekindZeta.log_eulerProduct_primeIdeal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.NUV2.HeckeLCoeff

open Filter Finset
open scoped Topology BigOperators Classical

open NK.GlobalCFT (Idele IdeleClassGroup)

noncomputable section

/-- The subtype of ideals indexing the sum which defines `NK.HeckeL.heckeCoeff`: the nonzero
integral ideals of `𝓞 K` of absolute norm `n` which are coprime to all primes in `S`.  It is
definitionally equal to the index type appearing in the definition of `heckeCoeff`. -/
abbrev heckeFiber (K : Type*) [Field K] [NumberField K] (S : Finset (NK.HeckeL.PrimeIdeal K))
    (n : ℕ) : Type _ :=
  {𝔞 : Ideal (NumberField.RingOfIntegers K) //
    𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧ Ideal.absNorm 𝔞 = n}

/-- Only finitely many ideals of `𝓞 K` have a given absolute norm, so the index type of
`heckeCoeff` is finite. -/
instance heckeFiberFinite (K : Type*) [Field K] [NumberField K]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (n : ℕ) : Finite (heckeFiber K S n) := by
  haveI : Finite {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  refine Finite.of_injective
    (fun a : heckeFiber K S n =>
      (⟨a.1, a.2.2.2⟩ : {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n})) ?_
  intro a b h
  have h' : a.1 = b.1 := by simpa using h
  exact Subtype.ext h'

/-- The coefficient `heckeCoeff K U S χ n` is a finite sum of characters (all of modulus `1`), one
for each ideal of norm `n` coprime to `S`; hence its modulus is at most the number of integral
ideals of norm `n`. -/
lemma norm_heckeCoeff_le_card (K : Type*) [Field K] [NumberField K]
    (U : Subgroup (NK.GlobalCFT.Idele K))
    [Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U)]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (χ : NK.HeckeL.RayChar K U) (n : ℕ) :
    ‖NK.HeckeL.heckeCoeff K U S χ n‖ ≤
      (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} : ℝ) := by
  haveI : Fintype (heckeFiber K S n) := Fintype.ofFinite _
  have h1 : ‖NK.HeckeL.heckeCoeff K U S χ n‖ ≤
      ∑' a : heckeFiber K S n, ‖χ.atIdeal (a : Ideal (NumberField.RingOfIntegers K))‖ := by
    show ‖∑' a : heckeFiber K S n, χ.atIdeal (a : Ideal (NumberField.RingOfIntegers K))‖ ≤ _
    exact norm_tsum_le_tsum_norm (Summable.of_finite)
  have h2 : (∑' a : heckeFiber K S n, ‖χ.atIdeal (a : Ideal (NumberField.RingOfIntegers K))‖)
      = (Nat.card (heckeFiber K S n) : ℝ) := by
    rw [tsum_fintype]
    simp only [NK.HeckeL.RayChar.norm_atIdeal_eq_one]
    rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
    simp
  have hcard : Nat.card (heckeFiber K S n) ≤
      Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} := by
    haveI : Finite {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
    exact Nat.card_le_card_of_injective
      (fun a : heckeFiber K S n =>
        (⟨a.1, a.2.2.2⟩ : {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n}))
      (fun a b h => by
        have h' : a.1 = b.1 := by simpa using h
        exact Subtype.ext h')
  have h3 : (Nat.card (heckeFiber K S n) : ℝ) ≤
      (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} : ℝ) := by
    exact_mod_cast hcard
  linarith

/-- For `s > 1`, the `L`-series of the coefficient sequence `heckeCoeff K U S χ` converges
absolutely.  Reason: `‖heckeCoeff n‖` is at most the number of integral ideals of norm `n`, so the
series is dominated by the Dedekind-zeta series `∑_n #{I | N I = n} n^{-s}`, which converges for
`s > 1`. -/
theorem LSeriesSummable_heckeCoeff (K : Type) [Field K] [NumberField K]
    (U : Subgroup (NK.GlobalCFT.Idele K))
    [Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U)]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (χ : NK.HeckeL.RayChar K U) {s : ℝ} (hs : 1 < s) :
    LSeriesSummable (NK.HeckeL.heckeCoeff K U S χ) (s : ℂ) := by
  have hZ : LSeriesSummable
      (fun n : ℕ =>
        ((Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} : ℕ) : ℂ))
      (s : ℂ) :=
    Commons.NumberTheory.NumberField.DedekindZeta.logEuler_LSeriesSummable_idealCount (K := K) hs
  have hZ' : Summable
      (fun n : ℕ => ‖LSeries.term
        (fun n : ℕ =>
          ((Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} : ℕ) : ℂ))
        (s : ℂ) n‖) := by
    rw [LSeriesSummable, ← summable_norm_iff] at hZ
    exact hZ
  have hstep : ∀ n : ℕ, ‖LSeries.term (NK.HeckeL.heckeCoeff K U S χ) (s : ℂ) n‖ ≤
      ‖LSeries.term
        (fun n : ℕ =>
          ((Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} : ℕ) : ℂ))
        (s : ℂ) n‖ :=
    fun n => LSeries.norm_term_le (s : ℂ) (by simpa using norm_heckeCoeff_le_card K U S χ n)
  have hmain : Summable
      (fun n : ℕ => ‖LSeries.term (NK.HeckeL.heckeCoeff K U S χ) (s : ℂ) n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hstep hZ'
  rw [LSeriesSummable, ← summable_norm_iff]
  exact hmain

end

end NK.NUV2.HeckeLCoeff
