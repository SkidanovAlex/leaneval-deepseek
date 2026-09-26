import Mathlib
import Submission.Work.SG.SellStabDefs

namespace Work.SG

/-! # The `full` case of `SellData.chkJoin`, as a `Prop`

`Work.SG.Data.SellData.chkJoin` (`Submission/Work/SG/Data/SellCheck.lean`) checks a join
certificate for the listed subgroup `K = S.subs.getD s 0` (a bitmask over `S.stab`) and an
element `g ∉ K`.  In the `full t cos` case it checks, with `T = S.subs.getD t 0` and
`rs = cos.foldl (fun rs p => rs ++ [(S.mul.getD (rs.getD p.1 0) []).getD p.2 0]) [S.one]`
(= `Work.SG.CZ.joinReps S cos`), that

* `g ∉ K`, `t < S.subs.length`, `K ∪ {g} ⊆ T`,
* every `p ∈ cos` has `p.2 ∈ K ∪ {g}`, and `(cos q).1 ≤ q` for every in-range `q`,
* `T ⊆ ⋃_{k ∈ K, r ∈ rs} {k · r}` (the last `==` of the checker, with `cosetMask`).

The claim converts this into usable `Prop` form.  `rs` is the list of coset representatives,
each a positive word in `K ∪ {g}`; the last conclusion says every bit of `T` is `k · r` with
`k ∈ K` and `r` one of those representatives.  Any auxiliary facts needed (e.g. a fold-induction
showing that if `(l.foldl (fun acc r => acc ||| cosetMask S K r) 0).testBit a = true` then some
`r ∈ l` has `(cosetMask S K r).testBit a = true`, and one showing
`(cosetMask S K r).testBit a = true → ∃ k < S.stab.length, K.testBit k = true ∧
gmul S k r = a`) may be stated and proved locally in the file. -/

/-! ## Two bit-manipulation fold inductions -/

/-- If the bit `a` survives a left fold that only ever ORs on functions of the list
elements, then it was either already set in the seed, or is the image of some element of
the list. -/
lemma chkJoinFull_foldl_lor_testBit (l : List ℕ) (f : ℕ → ℕ) (acc a : ℕ)
    (h : (l.foldl (fun acc r => acc ||| f r) acc).testBit a = true) :
    acc.testBit a = true ∨ ∃ r ∈ l, (f r).testBit a = true := by
  induction l generalizing acc with
  | nil => simp at h; exact Or.inl h
  | cons x xs ih =>
    simp only [List.foldl_cons] at h
    rcases ih (acc ||| f x) h with h1 | h2
    · rw [Nat.testBit_lor] at h1
      rcases Bool.or_eq_true_iff.mp h1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨x, by simp, h1⟩
    · exact Or.inr (let ⟨r, hr, hf⟩ := h2; ⟨r, by simp [hr], hf⟩)

/-- If the bit `a` survives a left fold of the shape used by `cosetMask` — at each step
either the accumulator is kept, or the single bit `f k` is ORed on when `K.testBit k` holds —
then it was either already set in the seed, or is `f k` for some list element `k` with
`K.testBit k = true`. -/
lemma chkJoinFull_foldl_ite_testBit (l : List ℕ) (K : ℕ) (f : ℕ → ℕ) (acc a : ℕ)
    (h : (l.foldl (fun acc k => if K.testBit k then acc ||| (1 <<< f k) else acc) acc).testBit a
        = true) :
    acc.testBit a = true ∨ ∃ k ∈ l, K.testBit k = true ∧ f k = a := by
  induction l generalizing acc with
  | nil => simp at h; exact Or.inl h
  | cons x xs ih =>
    simp only [List.foldl_cons] at h
    rcases ih (if K.testBit x then acc ||| (1 <<< f x) else acc) h with h1 | h2
    · by_cases hk : K.testBit x = true
      · have h1a : (acc ||| (1 <<< f x)).testBit a = true := by
          simp only [hk, reduceIte] at h1 ⊢; exact h1
        rw [Nat.testBit_lor] at h1a
        rcases Bool.or_eq_true_iff.mp h1a with h1a | h1a
        · exact Or.inl h1a
        · have hfa : f x = a := by
            rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at h1a
            exact decide_eq_true_eq.mp h1a
          exact Or.inr ⟨x, by simp, hk, hfa⟩
      · have h1a : acc.testBit a = true := by
          simp only [hk] at h1 ⊢; exact h1
        exact Or.inl h1a
    · exact Or.inr (let ⟨r, hr, hf⟩ := h2; ⟨r, by simp [hr], hf⟩)

theorem chkJoin_full {S : Work.SG.Data.SellData} {s g t : ℕ} {cos : List (ℕ × ℕ)}
    (h : S.chkJoin s g (some (Work.SG.Data.JoinCert.full t cos)) = true) :
    (S.subs.getD s 0).testBit g = false ∧
    t < S.subs.length ∧
    ((S.subs.getD s 0 ||| (1 <<< g) ||| S.subs.getD t 0) = S.subs.getD t 0) ∧
    (∀ p ∈ cos, p.2 = g ∨ (S.subs.getD s 0).testBit p.2 = true) ∧
    (∀ q, q < cos.length → (cos.getD q (0, 0)).1 ≤ q) ∧
    (∀ a, (S.subs.getD t 0).testBit a = true →
      ∃ r ∈ Work.SG.CZ.joinReps S cos, ∃ k, k < S.stab.length ∧
        (S.subs.getD s 0).testBit k = true ∧ Work.SG.CZ.gmul S k r = a) := by
  -- the checker's `rs` accumulator is `Work.SG.CZ.joinReps S cos`
  have hrs : Work.SG.CZ.joinReps S cos
      = List.foldl (fun rs p => rs ++ [(S.mul.getD (rs.getD p.1 0) []).getD p.2 0])
          [S.one] cos := rfl
  have h' := h
  simp only [Work.SG.Data.SellData.chkJoin, Bool.and_eq_true, List.all_eq_true,
    beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩, hF⟩ := h'
  refine ⟨?_, hB, hC, hD, ?_, ?_⟩
  · simpa using hA
  · intro q hq
    exact hE q (List.mem_range.mpr hq)
  · -- the last check `T ||| X == X`: every bit of `T` is a `k · r`
    intro a ha
    rw [← hrs] at hF
    have hX : (List.foldl (fun acc r => acc ||| Work.SG.Data.cosetMask S (S.subs.getD s 0) r) 0
        (Work.SG.CZ.joinReps S cos)).testBit a = true := by
      rw [← hF, Nat.testBit_lor, ha]; rfl
    rcases chkJoinFull_foldl_lor_testBit (Work.SG.CZ.joinReps S cos)
        (fun r => Work.SG.Data.cosetMask S (S.subs.getD s 0) r) 0 a hX with h0 | ⟨r, hr, hcm⟩
    · simp at h0
    · have hcm' : ((List.range S.stab.length).foldl (fun acc k =>
          if (S.subs.getD s 0).testBit k then acc ||| (1 <<< Work.SG.CZ.gmul S k r) else acc)
          0).testBit a = true := by
        simpa [Work.SG.Data.cosetMask, Work.SG.CZ.gmul] using hcm
      rcases chkJoinFull_foldl_ite_testBit (List.range S.stab.length) (S.subs.getD s 0)
          (fun k => Work.SG.CZ.gmul S k r) 0 a hcm' with h0 | ⟨k, hk, hK, hgmk⟩
      · simp at h0
      · exact ⟨r, hr, k, List.mem_range.mp hk, hK, hgmk⟩

end Work.SG
