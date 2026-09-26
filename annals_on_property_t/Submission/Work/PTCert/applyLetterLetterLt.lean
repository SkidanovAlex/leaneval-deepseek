import Mathlib
import Submission.Work.PTCert.LetterEval

/-!
# `PTCert`: the letter action `applyLetter 5 k` preserves the bound `< 10`

`applyLetter r k` acts on a word by applying `letterImg r k` to each (signed) letter, inverting
where the exponent bit is set, and finally free-reducing (`redW`).  If every letter of `w` is
`< 10` and `k < 81 = NB1 5`, then every letter of `applyLetter 5 k w` is again `< 10`.

This is the closure property of `B_1(5)` used by the finite model: words of letters `< 10`
(i.e. of the free group `F_5` in the `2 * i`/`2 * i + 1` encoding) stay in that model under the
letter action.  The proof splits into three independent facts:

* `redW` only deletes letters, hence never increases the bound;
* `invW` flips the exponent bit, which preserves the bound for an even modulus;
* `letterImg r k i` has all letters `< 2 * r` for `k < NB1 r` and `i < r`.
-/

set_option autoImplicit false

namespace Work.PTCert

open Submission.PTCert

/-- A single reduction step produces letters of `acc` or the new letter `c`. -/
private theorem al_lt_mem_redStep (acc : List ℕ) (c x : ℕ)
    (h : x ∈ Submission.PTCert.redStep acc c) : x ∈ acc ∨ x = c := by
  cases acc with
  | nil => simp [Submission.PTCert.redStep] at h; exact Or.inr h
  | cons d t =>
    simp only [Submission.PTCert.redStep] at h
    rw [Submission.PTCert.cond_natbeq d (c ^^^ 1) t (c :: d :: t)] at h
    by_cases hb : d = c ^^^ 1
    · rw [if_pos hb] at h
      exact Or.inl (List.mem_cons_of_mem d h)
    · rw [if_neg hb] at h
      rw [List.mem_cons] at h
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl h

/-- A letter of a reduction accumulator comes from the accumulator or from the word. -/
private theorem al_lt_mem_foldl_redStep (w : List ℕ) (acc : List ℕ) (x : ℕ)
    (h : x ∈ w.foldl Submission.PTCert.redStep acc) : x ∈ acc ∨ x ∈ w := by
  induction w generalizing acc with
  | nil => exact Or.inl h
  | cons c w ih =>
    rw [List.foldl_cons] at h
    rcases ih (Submission.PTCert.redStep acc c) h with h' | h'
    · rcases al_lt_mem_redStep acc c x h' with h'' | h''
      · exact Or.inl h''
      · exact Or.inr (List.mem_cons.mpr (Or.inl h''))
    · exact Or.inr (List.mem_cons.mpr (Or.inr h'))

/-- `redW` only deletes letters: it preserves any bound valid on the input word. -/
theorem redW_letterLt (m : ℕ) (w : List ℕ) (hw : ∀ c ∈ w, c < m) :
    ∀ c ∈ Submission.PTCert.redW w, c < m := by
  intro c hc
  simp only [Submission.PTCert.redW] at hc
  rw [List.mem_reverse] at hc
  rcases al_lt_mem_foldl_redStep w [] c hc with h' | h'
  · simp at h'
  · exact hw c h'

/-- `invW` flips exponent bits; for an even modulus this preserves the bound. -/
theorem invW_letterLt (m : ℕ) (hm : Even m) (w : List ℕ) (hw : ∀ c ∈ w, c < m) :
    ∀ c ∈ Submission.PTCert.invW w, c < m := by
  intro c hc
  unfold Submission.PTCert.invW at hc
  rw [List.mem_reverse, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  have hdlt := hw d hd
  rcases Nat.even_or_odd d with h | h
  · rw [Nat.xor_one_of_even h]
    rcases hm with ⟨t, ht⟩
    obtain ⟨s, hs⟩ := h
    omega
  · rw [Nat.xor_one_of_odd h]
    omega

/-- `letterImg r k i` stays in the `2r`-letter alphabet for `k < NB1 r` and `i < r`. -/
theorem letterImg_letterLt (r k i : ℕ) (hk : k < Submission.PTCert.NB1 r) (hi : i < r) :
    ∀ c ∈ Submission.PTCert.letterImg r k i, c < 2 * r := by
  by_cases hk0 : k = 0
  · subst k
    rw [Submission.PTCert.letterImg_zero]
    intro c hc
    rw [List.mem_singleton] at hc
    omega
  · have h1 : 1 ≤ k := by omega
    have hq : (k - 1) / 4 < r * (r - 1) := Submission.PTCert.q_lt r k h1 hk
    obtain ⟨hPi, hPj, _⟩ := Work.PTCert.pairOf_bounds hq
    by_cases hii : i = (Submission.PTCert.pairOf r ((k - 1) / 4)).1
    · rcases (by omega : (k - 1) % 4 = 0 ∨ (k - 1) % 4 = 1 ∨ (k - 1) % 4 = 2
          ∨ (k - 1) % 4 = 3) with h4 | h4 | h4 | h4
      · rw [Submission.PTCert.letterImg_k0 r k i hk0 hii h4]
        intro c hc
        rw [List.mem_cons, List.mem_singleton] at hc
        rcases hc with rfl | rfl <;> omega
      · rw [Submission.PTCert.letterImg_k1 r k i hk0 hii h4]
        intro c hc
        rw [List.mem_cons, List.mem_singleton] at hc
        rcases hc with rfl | rfl <;> omega
      · rw [Submission.PTCert.letterImg_k2 r k i hk0 hii h4]
        intro c hc
        rw [List.mem_cons, List.mem_singleton] at hc
        rcases hc with rfl | rfl <;> omega
      · rw [Submission.PTCert.letterImg_k3 r k i hk0 hii h4]
        intro c hc
        rw [List.mem_cons, List.mem_singleton] at hc
        rcases hc with rfl | rfl <;> omega
    · rw [Submission.PTCert.letterImg_ne r k i hii]
      intro c hc
      rw [List.mem_singleton] at hc
      omega

/-- **The letter `b1 5 k` (`k < 81 = NB1 5`) preserves words over the alphabet `< 10`.** -/
theorem applyLetterLetterLt (k : ℕ) (hk : k < 81) (w : List ℕ) (hw : ∀ c ∈ w, c < 10) :
    ∀ c ∈ Submission.PTCert.applyLetter 5 k w, c < 10 := by
  have hk81 : k < Submission.PTCert.NB1 5 := by
    simp only [Submission.PTCert.NB1] at hk ⊢; omega
  intro c hc
  simp only [Submission.PTCert.applyLetter] at hc
  refine redW_letterLt 10 _
    (fun b hb => ?_) c hc
  rw [List.mem_flatMap] at hb
  obtain ⟨a, ha, hb⟩ := hb
  have ha10 := hw a ha
  have ha5 : a / 2 < 5 := by omega
  have hLI := letterImg_letterLt 5 k (a / 2) hk81 ha5
  rw [Submission.PTCert.cond_natbeq (a % 2) 0 _ _] at hb
  by_cases he : a % 2 = 0
  · rw [if_pos he] at hb
    exact hLI b hb
  · rw [if_neg he] at hb
    exact invW_letterLt 10 (by norm_num) _ hLI b hb

end Work.PTCert
