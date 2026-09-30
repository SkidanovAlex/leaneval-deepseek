import Mathlib
import Submission.Work.BW.powSum_eq_of_small_house
import Submission.Work.BW.multiset_eq_of_powSum_eq
import Submission.Work.BW.exists_prime_house_condition
import Submission.Work.BW.exists_pow_eq_one_of_multiset_map_pow_eq_self

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The quantitative Kronecker lemma for a small house

If `β ≠ 0` is an algebraic integer in a number field `K` all of whose archimedean conjugates
satisfy `|log ‖σ β‖| ≤ 1/(9 [K : ℚ]²)`, then `β` is a root of unity.

The proof is the elementary "Frobenius" argument.  Let `P = minpoly ℤ β` have degree `n ≤ d`,
let `z ↦ z ^ p` act on the multiset of complex roots of `P` (`p` a prime chosen so that
`n H^{kp} + n H^k < p` for every `k ≤ n`, `H = exp (1/(9d²))` the house bound).  Then the
`kp`-th power sum of the roots equals the `k`-th one, so Newton's identities (Mathlib:
`Work.BW.powSum_eq_of_small_house` + `Work.BW.multiset_eq_of_powSum_eq`) show that the multiset
of roots is invariant under `z ↦ z ^ p`; hence every root is a root of unity.  Applying this to
`σ β` for an embedding `σ` and pulling back along the injective `σ` gives the claim.
-/

namespace Work.BW

open Polynomial

section Helpers

variable {K : Type*} [Field K] [NumberField K]

/-- The `ℤ`-minimal polynomial and the `ℚ`-minimal polynomial of `β` have the same image in
`ℂ[X]`. -/
private lemma map_minpoly_int_eq_map_minpoly_rat (β : K) (hint : IsIntegral ℤ β) :
    (minpoly ℤ β).map (Int.castRingHom ℂ) = (minpoly ℚ β).map (algebraMap ℚ ℂ) := by
  have hQ : minpoly ℚ β = (minpoly ℤ β).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
  rw [hQ, Polynomial.map_map]
  congr 1

/-- Membership of a complex number in the root multiset of the `ℤ`-minimal polynomial of `β` is
the same as being a root of the `ℚ`-minimal polynomial. -/
private lemma isRoot_map_minpoly_int_iff (β : K) (hint : IsIntegral ℤ β) (z : ℂ) :
    ((minpoly ℤ β).map (Int.castRingHom ℂ)).IsRoot z ↔
      (Polynomial.aeval z) (minpoly ℚ β) = 0 := by
  rw [map_minpoly_int_eq_map_minpoly_rat β hint, Polynomial.IsRoot.def, Polynomial.eval_map,
    ← Polynomial.aeval_def]

/-- `σ β` is a root of the image of the `ℤ`-minimal polynomial for every embedding
`σ : K →+* ℂ`. -/
private lemma isRoot_map_minpoly_int_of_embedding (β : K) (hint : IsIntegral ℤ β)
    (σ : K →+* ℂ) :
    ((minpoly ℤ β).map (Int.castRingHom ℂ)).IsRoot (σ β) := by
  rw [isRoot_map_minpoly_int_iff β hint]
  have hmem : σ β ∈ (minpoly ℚ β).rootSet ℂ := by
    rw [← NumberField.Embeddings.range_eval_eq_rootSet_minpoly K ℂ β]
    exact ⟨σ, rfl⟩
  exact (Polynomial.mem_rootSet.mp hmem).2

/-- Every complex root of the image of the `ℤ`-minimal polynomial of `β` is `σ β` for some
embedding `σ`. -/
private lemma exists_embedding_of_isRoot_map_minpoly_int (β : K) (hint : IsIntegral ℤ β) {z : ℂ}
    (hz : ((minpoly ℤ β).map (Int.castRingHom ℂ)).IsRoot z) : ∃ σ : K →+* ℂ, σ β = z := by
  have haz : (Polynomial.aeval z) (minpoly ℚ β) = 0 :=
    (isRoot_map_minpoly_int_iff β hint z).mp hz
  have hintQ : IsIntegral ℚ β := IsIntegral.of_finite ℚ β
  have hmem : z ∈ (minpoly ℚ β).rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    exact ⟨(minpoly.monic hintQ).ne_zero, haz⟩
  rw [← NumberField.Embeddings.range_eval_eq_rootSet_minpoly K ℂ β] at hmem
  exact hmem

/-- The degree of the `ℤ`-minimal polynomial is at most the degree of the number field. -/
private lemma natDegree_minpoly_int_le_finrank (β : K) (hint : IsIntegral ℤ β) :
    (minpoly ℤ β).natDegree ≤ Module.finrank ℚ K := by
  have h := minpoly.isIntegrallyClosed_eq_field_fractions' (R := ℤ) (S := K) ℚ hint
  rw [← Polynomial.natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int (minpoly ℤ β),
    ← h]
  exact minpoly.natDegree_le β

end Helpers

/-- Finiteness of order is detected by an injective ring homomorphism. -/
private lemma isOfFinOrder_of_isOfFinOrder_map {K : Type*} [Field K] (σ : K →+* ℂ) {x : K}
    (h : IsOfFinOrder (σ x)) : IsOfFinOrder x := by
  obtain ⟨m, hm0, hm⟩ := isOfFinOrder_iff_pow_eq_one.mp h
  exact isOfFinOrder_iff_pow_eq_one.mpr
    ⟨m, hm0, σ.injective (by rw [map_pow, hm, map_one])⟩

theorem isOfFinOrder_of_forall_abs_log_le {K : Type*} [Field K] [NumberField K] (β : K)
    (hβ : β ≠ 0) (hint : IsIntegral ℤ β)
    (hlog : ∀ σ : K →+* ℂ,
      |Real.log ‖σ β‖| ≤ 1 / (9 * (Module.finrank ℚ K : ℝ) ^ 2)) :
    IsOfFinOrder β := by
  classical
  obtain ⟨σ₀⟩ := (inferInstance : Nonempty (K →+* ℂ))
  -- Notation for the degree `n` of `minpoly ℤ β` and the field degree `D`.
  set n : ℕ := (minpoly ℤ β).natDegree with hn_def
  have hn : (minpoly ℤ β).natDegree = n := hn_def.symm
  have hnpos : 0 < n := minpoly.natDegree_pos hint
  set D : ℕ := Module.finrank ℚ K with hD_def
  have hDcast : (D : ℝ) = (Module.finrank ℚ K : ℝ) := by rw [hD_def]
  have hDpos : 0 < D := by rw [hD_def]; exact Module.finrank_pos
  have hnD : n ≤ D := natDegree_minpoly_int_le_finrank β hint
  -- The house bound `H = exp (1/(9D²))`.
  set ε : ℝ := 1 / (9 * (D : ℝ) ^ 2) with hε_def
  have hε : ε = 1 / (9 * (Module.finrank ℚ K : ℝ) ^ 2) := by rw [hε_def, hDcast]
  set H : ℝ := Real.exp ε with hH_def
  -- Every complex root of `P = minpoly ℤ β` has norm at most `H`.
  have hroot : ∀ z : ℂ, ((minpoly ℤ β).map (Int.castRingHom ℂ)).IsRoot z → ‖z‖ ≤ H := by
    intro z hz
    obtain ⟨σ, rfl⟩ := exists_embedding_of_isRoot_map_minpoly_int β hint hz
    have hne : σ β ≠ 0 := fun h => hβ (σ.injective (by rw [h, map_zero]))
    have hle : Real.log ‖σ β‖ ≤ ε := by
      have h := (abs_le.mp (hlog σ)).2
      rwa [hε] at h
    rw [hH_def]
    exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr hne)).mp hle
  -- The auxiliary prime.
  obtain ⟨p, hpprime, hpc⟩ := exists_prime_house_condition D n hDpos hnpos hnD
  have hp1 : 1 < p := hpprime.one_lt
  -- Power sums of the roots agree at `k` and `k * p` for all `k ≤ n`.
  have hpow : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      (((minpoly ℤ β).map (Int.castRingHom ℂ)).roots.map (fun z => z ^ (k * p))).sum =
        (((minpoly ℤ β).map (Int.castRingHom ℂ)).roots.map (fun z => z ^ k)).sum := by
    intro k hk1 hkn
    have hbig : ((minpoly ℤ β).natDegree : ℝ) * H ^ (k * p)
        + ((minpoly ℤ β).natDegree : ℝ) * H ^ k < (p : ℝ) := by
      rw [hn, hH_def, hε_def]
      exact hpc k hk1 hkn
    obtain ⟨c, hc1, hc2⟩ :=
      powSum_eq_of_small_house (minpoly ℤ β) (minpoly.monic hint) p hpprime k (H := H) hroot hbig
    rw [hc1, hc2]
  -- Hence the multiset of roots is invariant under `z ↦ z ^ p`.
  have hinv : (((minpoly ℤ β).map (Int.castRingHom ℂ)).roots.map (fun z => z ^ p)) =
      ((minpoly ℤ β).map (Int.castRingHom ℂ)).roots := by
    have hcard : (((minpoly ℤ β).map (Int.castRingHom ℂ)).roots.card) = n := by
      rw [IsAlgClosed.card_roots_map_eq_natDegree_of_injective (minpoly ℤ β)
        (RingHom.injective_int (Int.castRingHom ℂ)), hn]
    apply multiset_eq_of_powSum_eq (t := ((minpoly ℤ β).map (Int.castRingHom ℂ)).roots)
    · simp
    · intro m hm1 hmcard
      have hmn : m ≤ n := by
        rw [Multiset.card_map] at hmcard
        rwa [hcard] at hmcard
      rw [Multiset.map_map]
      have h := hpow m hm1 hmn
      simpa only [Function.comp_apply, pow_mul, Nat.mul_comm] using h
  -- `σ₀ β` is a root of `minpoly ℤ β`, hence a root of unity; pull back along `σ₀`.
  have hmem : σ₀ β ∈ ((minpoly ℤ β).map (Int.castRingHom ℂ)).roots :=
    (Polynomial.mem_roots ((minpoly.monic hint).map (Int.castRingHom ℂ)).ne_zero).mpr
      (isRoot_map_minpoly_int_of_embedding β hint σ₀)
  have hne : σ₀ β ≠ 0 := fun h => hβ (σ₀.injective (by rw [h, map_zero]))
  obtain ⟨m, hm0, hm⟩ := exists_pow_eq_one_of_multiset_map_pow_eq_self hp1 hinv hmem hne
  exact isOfFinOrder_of_isOfFinOrder_map σ₀
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm0, hm⟩)

end Work.BW
