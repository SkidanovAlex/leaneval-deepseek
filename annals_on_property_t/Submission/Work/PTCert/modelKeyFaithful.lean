import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.lprodProdImg
import Submission.Work.PTCert.letterImgLetterLt
import Submission.Work.PTCert.invWLetterLt
import Submission.Work.PTCert.applyLetterLetterLt

/-! # Faithfulness of the model key

`modelKey c` (KernelShared.lean) is a number computed from the five words
`prodImg 5 [c / 128, c % 128] i`, `i < 5`.  Hence it suffices to show that
`b1 5 a * b1 5 b = b1 5 a' * b1 5 b'` forces `prodImg 5 [a, b] i = prodImg 5 [a', b'] i`
(an equality of *words*, not only of the free-group elements they evaluate to).

The words `prodImg 5 [a, b] i` are `redW (w)` for the "raw" words `w` obtained by splicing in
the letter images (`rawImg` below), and their letters stay `< 10` (`= 2 * 5`).  Two raw words
whose evaluations agree therefore have equal `redW` — this is exactly the hypothesis
`RedWCanonical`.  The evaluation agreement follows from `lprodProdImg`
(`evalW (prodImg r ks i) = (lprod r ks) (of i)`, `lprod 5 [a,b] = b1 5 a * b1 5 b`).
-/

namespace Work.PTCert

open Submission.PTCert

/-- `NB1 5 = 81`: the number of letters of rank 5. -/
theorem NB1_five_modelKeyFaithful : Submission.PTCert.NB1 5 = 81 := by rfl

/-! ## The raw words -/

/-- The "raw" word whose free reduction is `applyLetter r k w`: the letter images spliced in
without reducing. -/
def rawImg (r k : ℕ) (w : List ℕ) : List ℕ :=
  w.flatMap (fun c => bif Nat.beq (c % 2) 0 then Submission.PTCert.letterImg r k (c / 2)
    else Submission.PTCert.invW (Submission.PTCert.letterImg r k (c / 2)))

/-- `applyLetter` is the reduction of the raw word. -/
theorem applyLetter_eq_redW (r k : ℕ) (w : List ℕ) :
    Submission.PTCert.applyLetter r k w = Submission.PTCert.redW (rawImg r k w) := rfl

/-- `prodImg 5 [a,b] i` is the reduction of the raw word. -/
theorem prodImg_eq_redW (a b i : ℕ) :
    Submission.PTCert.prodImg 5 [a, b] i
      = Submission.PTCert.redW (rawImg 5 a (Submission.PTCert.applyLetter 5 b [2 * i])) := by
  simp [Submission.PTCert.prodImg, applyLetter_eq_redW]

/-- A bound on the letters of a `flatMap`, from a bound on the letters of each image. -/
theorem flatMap_letter_lt {f : ℕ → List ℕ} (hf : ∀ c < 10, ∀ d ∈ f c, d < 10)
    (w : List ℕ) (hw : ∀ c ∈ w, c < 10) : ∀ d ∈ w.flatMap f, d < 10 := by
  intro d hd
  rw [List.mem_flatMap] at hd
  obtain ⟨c, hc, hdc⟩ := hd
  exact hf c (hw c hc) d hdc

/-- The letters of a raw image word stay `10`-bounded. -/
theorem rawImg_letter_lt (k : ℕ) (hk : k < 81) (w : List ℕ) (hw : ∀ c ∈ w, c < 10) :
    ∀ c ∈ rawImg 5 k w, c < 10 := by
  rw [rawImg]
  refine flatMap_letter_lt ?_ w hw
  intro d hd
  have hd5 : d / 2 < 5 := by omega
  have hk' : k < Submission.PTCert.NB1 5 := by rw [NB1_five_modelKeyFaithful]; exact hk
  by_cases hp : d % 2 = 0
  · have hb : Nat.beq (d % 2) 0 = true := by rw [Nat.beq_eq]; exact hp
    simp only [hb, cond_true]
    exact letterImgLetterLt 5 k (d / 2) hk' hd5
  · have hb : Nat.beq (d % 2) 0 = false := by
      rw [Bool.eq_false_iff]
      intro hh
      exact hp (by rwa [Nat.beq_eq] at hh)
    simp only [hb, cond_false]
    exact invWLetterLt 10 (by norm_num) _ (letterImgLetterLt 5 k (d / 2) hk' hd5)

/-- The letters of the raw words of `prodImg 5 [a,b] i` stay `10`-bounded for `a,b < 81`. -/
theorem prodImg_raw_letter_lt (a b i : ℕ) (ha : a < 81) (hb : b < 81) (hi : i < 5) :
    ∀ c ∈ rawImg 5 a (Submission.PTCert.applyLetter 5 b [2 * i]), c < 10 := by
  refine rawImg_letter_lt a ha _ ?_
  refine applyLetterLetterLt b hb [2 * i] ?_
  intro c hc
  rw [List.mem_singleton] at hc
  subst hc
  omega

/-! ## The main theorem -/

theorem modelKeyFaithful (hred : RedWCanonical) : ModelKeyFaithful := by
  intro a b a' b' ha hb ha' hb' h
  -- the two products of letters agree on the generators
  have hAB : Submission.PTCert.lprod 5 [a, b] = Submission.PTCert.lprod 5 [a', b'] := by
    simpa [Submission.PTCert.lprod] using h
  have hks : ∀ k ∈ [a, b], k < Submission.PTCert.NB1 5 := by
    intro k hk
    rw [NB1_five_modelKeyFaithful]
    rcases List.mem_cons.mp hk with hk | hk
    · exact hk ▸ ha
    · rw [List.mem_singleton] at hk
      exact hk ▸ hb
  have hks' : ∀ k ∈ [a', b'], k < Submission.PTCert.NB1 5 := by
    intro k hk
    rw [NB1_five_modelKeyFaithful]
    rcases List.mem_cons.mp hk with hk | hk
    · exact hk ▸ ha'
    · rw [List.mem_singleton] at hk
      exact hk ▸ hb'
  -- the words `prodImg 5 [a,b] i` agree for `i < 5`
  have hwords : ∀ i < 5, Submission.PTCert.prodImg 5 [a, b] i
      = Submission.PTCert.prodImg 5 [a', b'] i := by
    intro i hi
    have h1 := lprodProdImg 5 [a, b] hks (⟨i, hi⟩ : Fin 5)
    have h2 := lprodProdImg 5 [a', b'] hks' (⟨i, hi⟩ : Fin 5)
    have he : Submission.PTCert.evalW (r := 5) (Submission.PTCert.prodImg 5 [a, b] i)
        = Submission.PTCert.evalW (r := 5) (Submission.PTCert.prodImg 5 [a', b'] i) := by
      rw [← h1, ← h2, hAB]
    have hu : Submission.PTCert.evalW (r := 5)
          (rawImg 5 a (Submission.PTCert.applyLetter 5 b [2 * i]))
        = Submission.PTCert.evalW (r := 5)
          (rawImg 5 a' (Submission.PTCert.applyLetter 5 b' [2 * i])) := by
      rw [← Submission.PTCert.evalW_redW (r := 5)
            (rawImg 5 a (Submission.PTCert.applyLetter 5 b [2 * i])),
          ← Submission.PTCert.evalW_redW (r := 5)
            (rawImg 5 a' (Submission.PTCert.applyLetter 5 b' [2 * i])),
          ← prodImg_eq_redW a b i, ← prodImg_eq_redW a' b' i, he]
    have hred' := hred 5 (rawImg 5 a (Submission.PTCert.applyLetter 5 b [2 * i]))
      (rawImg 5 a' (Submission.PTCert.applyLetter 5 b' [2 * i]))
      (prodImg_raw_letter_lt a b i ha hb hi) (prodImg_raw_letter_lt a' b' i ha' hb' hi) hu
    rw [prodImg_eq_redW a b i, prodImg_eq_redW a' b' i]
    exact hred'
  -- the model key only depends on these words
  have hdiv : (128 * a + b) / 128 = a := by omega
  have hmod : (128 * a + b) % 128 = b := by omega
  have hdiv' : (128 * a' + b') / 128 = a' := by omega
  have hmod' : (128 * a' + b') % 128 = b' := by omega
  show Submission.PTCert.modelKey (128 * a + b) = Submission.PTCert.modelKey (128 * a' + b')
  simp only [Submission.PTCert.modelKey, hdiv, hmod, hdiv', hmod']
  have hm : (List.range 5).map (fun i => Submission.PTCert.prodImg 5 [a, b] i)
      = (List.range 5).map (fun i => Submission.PTCert.prodImg 5 [a', b'] i) :=
    List.map_congr_left (fun i hi => hwords i (List.mem_range.mp hi))
  rw [hm]

end Work.PTCert
