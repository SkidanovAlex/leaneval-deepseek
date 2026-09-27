import Mathlib
import Submission.Work.EQ.charValDefs
import Submission.Work.EQ.fan_base

/-!
# Auxiliary walk lemmas for `Work.EQ.charVal_props`

Elementary, independent facts about the walk of `charValDefs.lean`: the centre of state `0` is
`A₁ = -1/2`, counting bounds for the number of non-stationary steps, deletion of the stationary
steps, and finiteness of the value set of words of bounded length.
-/

namespace Work.EQ

open Complex

noncomputable section

@[simp] lemma stIdx_zero : stIdx 0 = 0 := by decide

@[simp] lemma stCtr_zero : stCtr 0 = (-1 / 2 : ℝ) := by
  simp [stCtr, stIdx]

lemma stIdx_even (k : ℕ) : stIdx (2 * k) = -(k : ℤ) := by
  have h : (2 * k) % 2 = 0 := by omega
  simp [stIdx, h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

lemma stIdx_odd (k : ℕ) : stIdx (2 * k + 1) = ((k + 1 : ℕ) : ℤ) := by
  have h : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 1 + 1) / 2 = k + 1 := by
    have : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
    rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  simp [stIdx, h, h2]

/-- The only state whose centre is `A₁ = -1/2` is state `0`. -/
lemma stIdx_eq_zero {n : ℕ} (h : stIdx n = 0) : n = 0 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    rw [show k + k = 2 * k from by omega, stIdx_even] at h
    omega
  · subst hk
    rw [stIdx_odd] at h
    omega

lemma stCtr_eq_iff {n : ℕ} : stCtr n = (-1 / 2 : ℝ) ↔ n = 0 := by
  constructor
  · intro h
    have h2 : (stIdx n : ℝ) = 0 := by
      have h3 := h
      simp only [stCtr] at h3
      linarith
    exact stIdx_eq_zero (by exact_mod_cast h2)
  · rintro rfl
    exact stCtr_zero

lemma stQ_zero {a : ℝ} (ha1 : a < 1) : stQ a 0 = (1 - a) / 2 := by
  rw [stQ, stCtr_zero, abs_of_neg (by linarith)]
  ring

lemma dnW_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : dnW a 0 = -1 := by
  have h1 : (1 : ℝ) - a ≠ 0 := by linarith
  have h2 : (1 : ℝ) + a ≠ 0 := by linarith
  rw [dnW, stQ_zero ha1, eqLam]
  field_simp
  ring

lemma stW_true_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : stW a true 0 = 1 := by
  rw [stW, dnW_zero ha0 ha1, abs_neg, abs_one]
  simp

lemma sgW_true_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : sgW a true 0 = 1 := by
  rw [sgW, dnW_zero ha0 ha1]; norm_num

lemma stp_false (n : ℕ) : stp false n = n + 1 := rfl

lemma stp_true_zero : stp true 0 = 0 := rfl

lemma stp_true_succ (n : ℕ) : stp true (n + 1) = n := by
  simp [stp]

lemma count_false_true_cons (l : List Bool) : (true :: l).count false = l.count false := by
  simp

lemma count_false_false_cons (l : List Bool) : (false :: l).count false = l.count false + 1 := by
  simp

/-- Walk counting bound: the number of non-stationary steps of a word read from state `n` is at
most twice the number of non-principal letters plus `n`.  (`false` letters always move up, and
the walk never goes below `0`.) -/
lemma nsAux_le (l : List Bool) (n : ℕ) : nsAux l n ≤ 2 * l.count false + n := by
  induction l generalizing n with
  | nil => simp
  | cons c l ih =>
    cases c with
    | true =>
      cases n with
      | zero =>
        have h := ih 0
        simp only [nsAux_cons, count_false_true_cons, stp_true_zero, and_self, ↓reduceIte,
          Nat.add_zero] at h ⊢
        omega
      | succ m =>
        have h := ih m
        simp only [nsAux_cons, count_false_true_cons, stp_true_succ, Nat.succ_ne_zero,
          and_false, ↓reduceIte] at h ⊢
        omega
    | false =>
      have h := ih (n + 1)
      simp only [nsAux_cons, count_false_false_cons, stp_false, Bool.false_eq_true,
        false_and, ↓reduceIte, Nat.add_zero] at h ⊢
      omega

lemma nsAux_le_two_mul_count {l : List Bool} (h : stAux l 0 = 0) :
    nsAux l 0 ≤ 2 * l.count false := by
  have := nsAux_le l 0
  omega

/-- Delete the stationary steps (the `true` letters read in state `0`) of a word. -/
def redAux : ℕ → List Bool → List Bool
  | _, [] => []
  | n, c :: l => if c ∧ n = 0 then redAux n l else c :: redAux (stp c n) l

@[simp] lemma redAux_nil (n : ℕ) : redAux n [] = [] := rfl

lemma redAux_stay (l : List Bool) : redAux 0 (true :: l) = redAux 0 l := by
  rw [redAux]; simp

lemma redAux_cons (c : Bool) (l : List Bool) (n : ℕ) (h : ¬ (c ∧ n = 0)) :
    redAux n (c :: l) = c :: redAux (stp c n) l := by
  rw [redAux]; exact if_neg h

lemma stAux_redAux (l : List Bool) (n : ℕ) : stAux (redAux n l) n = stAux l n := by
  induction l generalizing n with
  | nil => simp
  | cons c l ih =>
    by_cases h : c ∧ n = 0
    · obtain ⟨rfl, rfl⟩ := h
      simp only [redAux_stay, ih 0, stAux_cons, stp_true_zero]
    · simp only [redAux_cons c l n h, stAux_cons, ih (stp c n)]

lemma wtAux_redAux (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (l : List Bool) (n : ℕ) :
    wtAux a (redAux n l) n = wtAux a l n := by
  induction l generalizing n with
  | nil => simp
  | cons c l ih =>
    by_cases h : c ∧ n = 0
    · obtain ⟨rfl, rfl⟩ := h
      rw [redAux_stay, ih 0, wtAux_cons, stp_true_zero, stW_true_zero ha0 ha1, one_mul]
    · simp only [redAux_cons c l n h, wtAux_cons, ih (stp c n)]

lemma length_redAux (l : List Bool) (n : ℕ) : (redAux n l).length = nsAux l n := by
  induction l generalizing n with
  | nil => simp
  | cons c l ih =>
    by_cases h : c ∧ n = 0
    · obtain ⟨rfl, rfl⟩ := h
      simp only [redAux_stay, ih 0, nsAux_cons, stp_true_zero, and_self, ↓reduceIte,
        Nat.zero_add]
    · simp only [redAux_cons c l n h, List.length_cons, ih (stp c n), nsAux_cons]
      rw [if_neg h]; omega

/-- All words of length at most `n`. -/
def allWords : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => {[]} ∪ (allWords n).biUnion (fun l => {true :: l, false :: l})

lemma mem_allWords {l : List Bool} {n : ℕ} (h : l.length ≤ n) : l ∈ allWords n := by
  induction l generalizing n with
  | nil =>
    cases n with
    | zero => simp [allWords]
    | succ m => simp [allWords]
  | cons c l ih =>
    cases n with
    | zero => simp at h
    | succ m =>
      simp only [allWords, Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion,
        Finset.mem_insert]
      right
      exact ⟨l, ih (by simpa using h), by cases c <;> simp⟩

lemma finite_word_values (a : ℝ) (M : ℕ) :
    {v : ℝ | ∃ l : List Bool, l.length ≤ M ∧ wtAux a l 0 = v}.Finite := by
  refine Set.Finite.subset ((allWords M).finite_toSet.image (fun l => wtAux a l 0)) ?_
  rintro v ⟨l, hl, rfl⟩
  exact ⟨l, mem_allWords hl, rfl⟩

end

end Work.EQ
