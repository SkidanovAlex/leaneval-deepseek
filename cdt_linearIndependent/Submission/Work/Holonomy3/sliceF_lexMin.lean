import Mathlib
import Submission.Work.Holonomy3.mv_lex_defs

/-!
# Slicing preserves lexicographic minimality

Let `c` be a finitely supported family of complex coefficients indexed by multi-indices in
`Fin (d+1) →₀ ℕ`, and let `n` be the lexicographically minimal element of the support of `c`
(lexicographic order with the *first* coordinate the most significant, encoded by `LexMinF`).

The lemma below records the two elementary consequences for the slice `sliceF c t`, the family of
coefficients of the `t`-th power of the first variable:

* no slice below `n 0` is non-zero (`sliceF c t = 0` for `t < n 0`), because a nonzero entry of
  such a slice would produce an element of the support of `c` with strictly smaller first
  coordinate, hence strictly smaller in the lexicographic order;
* the slice at level `n 0` is non-zero and its lexicographically minimal element is exactly the
  tail `tailIdx n` of `n`.

The only order-theoretic input is that prepending a fixed first coordinate to an index is
strictly monotone for the lexicographic order, and that an index with a strictly smaller first
coordinate is strictly smaller.
-/

namespace Work.Holonomy3

open scoped BigOperators

noncomputable section

/-- If the first coordinate of `p` is strictly smaller than the first coordinate of `n`, then `p`
is strictly smaller than `n` in the lexicographic order. -/
lemma toLex_lt_of_zero_lt {d : ℕ} {p n : Fin (d + 1) →₀ ℕ} (h : p 0 < n 0) :
    toLex p < toLex n := by
  rw [Finsupp.Lex.lt_iff]
  exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by simpa using h⟩

/-- Prepending a fixed first coordinate `t` to a multi-index is strictly monotone with respect to
the lexicographic order. -/
lemma toLex_consIdx_lt {d : ℕ} (t : ℕ) {m m' : Fin d →₀ ℕ} (h : toLex m < toLex m') :
    toLex (consIdx t m) < toLex (consIdx t m') := by
  rw [Finsupp.Lex.lt_iff] at h ⊢
  obtain ⟨j, hj, hlt⟩ := h
  simp only [ofLex_toLex] at hj hlt
  refine ⟨j.succ, ?_, ?_⟩
  · intro i hi
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · simp
    · simp only [ofLex_toLex, consIdx_succ]
      exact hj k (Fin.succ_lt_succ_iff.mp hi)
  · simp only [ofLex_toLex, consIdx_succ]
    exact hlt

theorem sliceF_lexMin {d : ℕ} (c : (Fin (d+1) →₀ ℕ) →₀ ℂ) {n : Fin (d+1) →₀ ℕ} (hlex : LexMinF c n) :
    (∀ t : ℕ, t < n 0 → sliceF c t = 0) ∧ LexMinF (sliceF c (n 0)) (tailIdx n) := by
  obtain ⟨hnmem, hmin⟩ := hlex
  have hn0 : c n ≠ 0 := Finsupp.mem_support_iff.mp hnmem
  constructor
  · -- no slice strictly below `n 0` can be non-zero
    intro t ht
    ext m
    simp only [sliceF_apply, Finsupp.coe_zero, Pi.zero_apply]
    by_contra hne
    have hmem : consIdx t m ∈ c.support := Finsupp.mem_support_iff.mpr hne
    have hlt : toLex (consIdx t m) < toLex n := toLex_lt_of_zero_lt (by rwa [consIdx_zero])
    exact absurd (lt_of_lt_of_le hlt (hmin _ hmem)) (lt_irrefl _)
  · -- the slice at level `n 0` is non-zero with lexicographic minimum the tail of `n`
    refine ⟨?_, ?_⟩
    · rw [Finsupp.mem_support_iff, sliceF_apply, consIdx_tailIdx]
      exact hn0
    · intro m hm
      have hm0 : sliceF c (n 0) m ≠ 0 := Finsupp.mem_support_iff.mp hm
      rw [sliceF_apply] at hm0
      have hmem : consIdx (n 0) m ∈ c.support := Finsupp.mem_support_iff.mpr hm0
      have h1 : toLex n ≤ toLex (consIdx (n 0) m) := hmin _ hmem
      by_contra hcon
      have h2 : toLex m < toLex (tailIdx n) := lt_of_not_ge hcon
      have h3 : toLex (consIdx (n 0) m) < toLex (consIdx (n 0) (tailIdx n)) :=
        toLex_consIdx_lt _ h2
      rw [← consIdx_tailIdx n] at h1
      exact absurd h1 (not_le_of_gt h3)

end

end Work.Holonomy3
