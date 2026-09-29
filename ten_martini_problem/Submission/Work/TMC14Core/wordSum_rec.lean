import Mathlib
import Submission.Work.TMC14Core.InvSumAux
import Submission.Work.TMC14Core.wordSumAux

/-!
# `TMC14Core.wordSum_rec`

The two-parameter recursion for the weighted word sum `wordSum`

`wordSum ω (n+1) a = wordSum ω n a + ω ^ (n+1-a) * wordSum ω n (a-1)`  (for `1 ≤ a`),

obtained by splitting a word of length `n+1` according to its first letter:
prepending `V = (false,true)` leaves the inversion count unchanged and keeps the
number of `U`'s, while prepending `U = (true,true)` increases the number of `U`'s
by one and contributes `#V(g) = n+1-a` new inversions.

This file is self-contained: all auxiliary lemmas are proved here.
-/

namespace Work.TMC14Core

/-- `wordSum` rewritten as a sum of `if … then … else 0` over *all* words of
length `n` (the letter constraint becomes a condition inside the summand). -/
lemma wsr_wordSum_ite (ω : ℂ) (n a : ℕ) :
    wordSum ω n a = ∑ f : Fin n → Bool × Bool,
      (if letterOK n f ∧ cntL (true, true) n f = a then ω ^ invCount n f else 0) := by
  unfold wordSum letterOK cntL
  rw [Finset.sum_filter]

/-- Splitting off the first letter of a word of length `n+1`. -/
lemma wsr_letterOK_cons (c : Bool × Bool) (n : ℕ) (g : Fin n → Bool × Bool) :
    letterOK (n+1) (Fin.cons c g) ↔
      (c = (true,true) ∨ c = (false,true)) ∧ letterOK n g := by
  simp only [letterOK, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]

lemma wsr_letterOK_consU (n : ℕ) (g : Fin n → Bool × Bool) :
    letterOK (n+1) (consU g) ↔ letterOK n g := by
  have h : consU g = Fin.cons (true,true) g := rfl
  rw [h, wsr_letterOK_cons]
  simp

lemma wsr_letterOK_consV (n : ℕ) (g : Fin n → Bool × Bool) :
    letterOK (n+1) (consV g) ↔ letterOK n g := by
  have h : consV g = Fin.cons (false,true) g := rfl
  rw [h, wsr_letterOK_cons]
  simp

lemma wsr_letterOK_cons_false {c : Bool × Bool}
    (hc : ¬ (c = (true,true) ∨ c = (false,true)))
    (n : ℕ) (g : Fin n → Bool × Bool) : ¬ letterOK (n+1) (Fin.cons c g) := by
  rw [wsr_letterOK_cons]
  exact fun h => hc h.1

/-- For a word all of whose letters are `U` or `V`, the numbers of `U`'s and of
`V`'s add up to the length. -/
lemma wsr_cntL_letterOK_add (n : ℕ) (g : Fin n → Bool × Bool) (hg : letterOK n g) :
    cntL (true,true) n g + cntL (false,true) n g = n := by
  unfold cntL
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  trans ∑ _i : Fin n, (1:ℕ)
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rcases hg i with h | h
    · rw [if_pos h, if_neg (by rw [h]; decide)]
    · rw [if_neg (by rw [h]; decide), if_pos h]
  · simp

/-- Pointwise reduction of a summand when the first letter is `V`. -/
lemma wsr_term_V (ω : ℂ) (n a : ℕ) (g : Fin n → Bool × Bool) :
    (if letterOK (n+1) (consV g) ∧ cntL (true,true) (n+1) (consV g) = a
      then ω ^ invCount (n+1) (consV g) else 0)
    = (if letterOK n g ∧ cntL (true,true) n g = a then ω ^ invCount n g else 0) := by
  have hletter : letterOK (n+1) (consV g) ↔ letterOK n g := wsr_letterOK_consV n g
  have hcnt : cntL (true,true) (n+1) (consV g) = cntL (true,true) n g := by
    have h2 : consV g = Fin.cons (false,true) g := rfl
    rw [h2]
    exact cntL_cons_ne (show (false,true) ≠ (true,true) by decide) n g
  have hinv : invCount (n+1) (consV g) = invCount n g := invCount_cons_ft n g
  by_cases h : letterOK n g ∧ cntL (true,true) n g = a
  · have hc : letterOK (n+1) (consV g) ∧ cntL (true,true) (n+1) (consV g) = a :=
      ⟨hletter.mpr h.1, by rw [hcnt]; exact h.2⟩
    rw [if_pos hc, if_pos h, hinv]
  · have hc : ¬ (letterOK (n+1) (consV g) ∧ cntL (true,true) (n+1) (consV g) = a) := by
      rintro ⟨h1, h2⟩
      exact h ⟨hletter.mp h1, by rw [hcnt] at h2; exact h2⟩
    rw [if_neg h, if_neg hc]

/-- Pointwise reduction of a summand when the first letter is `U`. -/
lemma wsr_term_U (ω : ℂ) (n a : ℕ) (ha : 1 ≤ a) (g : Fin n → Bool × Bool) :
    (if letterOK (n+1) (consU g) ∧ cntL (true,true) (n+1) (consU g) = a
      then ω ^ invCount (n+1) (consU g) else 0)
    = (if letterOK n g ∧ cntL (true,true) n g = (a-1)
      then ω ^ (n+1-a) * ω ^ invCount n g else 0) := by
  have hletter : letterOK (n+1) (consU g) ↔ letterOK n g := wsr_letterOK_consU n g
  have hcnt : cntL (true,true) (n+1) (consU g) = cntL (true,true) n g + 1 :=
    cntL_cons_self (true,true) n g
  have hinv : invCount (n+1) (consU g) = cntL (false,true) n g + invCount n g :=
    invCount_cons_tt n g
  by_cases h : letterOK n g ∧ cntL (true,true) n g = (a-1)
  · have h1 : letterOK (n+1) (consU g) := hletter.mpr h.1
    have h2 : cntL (true,true) (n+1) (consU g) = a := by
      rw [hcnt, h.2]; omega
    have h3 : cntL (false,true) n g = n + 1 - a := by
      have hsum := wsr_cntL_letterOK_add n g h.1
      omega
    have h4 : invCount (n+1) (consU g) = (n+1-a) + invCount n g := by
      rw [hinv, h3]
    rw [if_pos ⟨h1, h2⟩, if_pos h, h4, pow_add]
  · have hc : ¬ (letterOK (n+1) (consU g) ∧ cntL (true,true) (n+1) (consU g) = a) := by
      rintro ⟨h1, h2⟩
      refine h ⟨hletter.mp h1, ?_⟩
      rw [hcnt] at h2
      omega
    rw [if_neg h, if_neg hc]

/-- Pull a constant factor out of a `wordSum`-shaped `if`-sum. -/
lemma wsr_mul_sum_ite (k : ℂ) (ω : ℂ) (n b : ℕ) :
    (∑ g : Fin n → Bool × Bool,
        (if letterOK n g ∧ cntL (true,true) n g = b then k * ω ^ invCount n g else 0))
      = k * (∑ g : Fin n → Bool × Bool,
        (if letterOK n g ∧ cntL (true,true) n g = b then ω ^ invCount n g else 0)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  by_cases h : letterOK n g ∧ cntL (true,true) n g = b <;> simp [h]

theorem wordSum_rec (ω : ℂ) (n a : ℕ) (ha : 1 ≤ a) :
    wordSum ω (n+1) a = wordSum ω n a + ω ^ (n + 1 - a) * wordSum ω n (a - 1) := by
  rw [wsr_wordSum_ite ω (n+1) a, wsr_wordSum_ite ω n a, wsr_wordSum_ite ω n (a-1)]
  have key : (∑ f : Fin (n+1) → Bool × Bool,
        (if letterOK (n+1) f ∧ cntL (true, true) (n+1) f = a then ω ^ invCount (n+1) f else 0))
      = ω ^ (n+1-a) * (∑ g : Fin n → Bool × Bool,
          (if letterOK n g ∧ cntL (true, true) n g = (a-1) then ω ^ invCount n g else 0))
        + (∑ g : Fin n → Bool × Bool,
          (if letterOK n g ∧ cntL (true, true) n g = a then ω ^ invCount n g else 0)) := by
    set G : (Fin (n+1) → Bool × Bool) → ℂ :=
      fun f => (if letterOK (n+1) f ∧ cntL (true, true) (n+1) f = a
        then ω ^ invCount (n+1) f else 0) with hG
    have hsplit : (∑ f : Fin (n+1) → Bool × Bool, G f)
        = (∑ g : Fin n → Bool × Bool, G (Fin.cons (true,true) g))
          + (∑ g : Fin n → Bool × Bool, G (Fin.cons (false,true) g)) := by
      have hG1 : (∑ f : Fin (n+1) → Bool × Bool, G f)
          = (∑ p : (Bool × Bool) × (Fin n → Bool × Bool), G (Fin.cons p.1 p.2)) := by
        refine Finset.sum_bijective (f := G)
          (g := fun p : (Bool × Bool) × (Fin n → Bool × Bool) => G (Fin.cons p.1 p.2))
          (fun f : Fin (n+1) → Bool × Bool => (f 0, Fin.tail f)) ?_ ?_ ?_
        · constructor
          · intro f f' h
            have h1 : f 0 = f' 0 := by simpa using congrArg Prod.fst h
            have h2 : Fin.tail f = Fin.tail f' := by simpa using congrArg Prod.snd h
            calc f = Fin.cons (f 0) (Fin.tail f) := (Fin.cons_self_tail f).symm
              _ = Fin.cons (f' 0) (Fin.tail f') := by rw [h1, h2]
              _ = f' := Fin.cons_self_tail f'
          · intro p
            exact ⟨Fin.cons p.1 p.2, Prod.ext (by simp) (by simp)⟩
        · intro i
          simp
        · intro f _
          exact (congrArg G (Fin.cons_self_tail f)).symm
      have hG2 : (∑ p : (Bool × Bool) × (Fin n → Bool × Bool), G (Fin.cons p.1 p.2))
          = (∑ c : Bool × Bool, ∑ g : Fin n → Bool × Bool, G (Fin.cons c g)) := by
        rw [Fintype.sum_prod_type]
      have hbool : (∑ c : Bool × Bool, ∑ g : Fin n → Bool × Bool, G (Fin.cons c g))
          = (∑ g : Fin n → Bool × Bool, G (Fin.cons (true,true) g))
            + (∑ g : Fin n → Bool × Bool, G (Fin.cons (false,true) g)) := by
        calc (∑ c : Bool × Bool, ∑ g : Fin n → Bool × Bool, G (Fin.cons c g))
            = (∑ c ∈ ({(true,true),(false,true)} : Finset (Bool × Bool)),
                ∑ g : Fin n → Bool × Bool, G (Fin.cons c g)) :=
              (Finset.sum_subset (Finset.subset_univ _) (by
                intro c _ hc
                have hc' : ¬ (c = (true,true) ∨ c = (false,true)) := by simpa using hc
                apply Finset.sum_eq_zero
                intro g _
                have hnc : ¬ (letterOK (n+1) (Fin.cons c g) ∧
                    cntL (true,true) (n+1) (Fin.cons c g) = a) :=
                  fun hh => (wsr_letterOK_cons_false hc' n g) hh.1
                rw [hG]
                exact if_neg hnc)).symm
          _ = (∑ g : Fin n → Bool × Bool, G (Fin.cons (true,true) g))
                + (∑ g : Fin n → Bool × Bool, G (Fin.cons (false,true) g)) :=
              Finset.sum_pair (show (true,true) ≠ (false,true) by decide)
      rw [hG1, hG2, hbool]
    have hU : (∑ g : Fin n → Bool × Bool, G (Fin.cons (true,true) g))
        = ω ^ (n+1-a) * (∑ g : Fin n → Bool × Bool,
            (if letterOK n g ∧ cntL (true, true) n g = (a-1) then ω ^ invCount n g else 0)) := by
      have hc : (∑ g : Fin n → Bool × Bool, G (Fin.cons (true,true) g))
          = ∑ g : Fin n → Bool × Bool,
              (if letterOK n g ∧ cntL (true, true) n g = (a-1)
                then ω ^ (n+1-a) * ω ^ invCount n g else 0) := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [hG]
        exact wsr_term_U ω n a ha g
      rw [hc, wsr_mul_sum_ite (ω ^ (n+1-a)) ω n (a-1)]
    have hV : (∑ g : Fin n → Bool × Bool, G (Fin.cons (false,true) g))
        = (∑ g : Fin n → Bool × Bool,
            (if letterOK n g ∧ cntL (true, true) n g = a then ω ^ invCount n g else 0)) := by
      refine Finset.sum_congr rfl (fun g _ => ?_)
      rw [hG]
      exact wsr_term_V ω n a g
    rw [hsplit, hU, hV]
  rw [key]
  ring

end Work.TMC14Core
