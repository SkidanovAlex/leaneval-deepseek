import Mathlib
import Submission.Work.OROneRel.substDefs

universe u

namespace Work.OROneRel

variable {β : Type u}

/-! ### Elementary run computations -/

/-- The sign of an integer, as `±1` (`sgnI 0 = -1`). -/
def sgnI (n : ℤ) : ℤ := if 0 < n then 1 else -1

theorem sgnI_of_pos {n : ℤ} (h : 0 < n) : sgnI n = 1 := by rw [sgnI, if_pos h]

theorem sgnI_of_neg {n : ℤ} (h : n < 0) : sgnI n = -1 := by
  rw [sgnI, if_neg (not_lt.mpr h.le)]

theorem sgnI_opposite {p q : ℤ} (h : (0 < p ∧ q < 0) ∨ (p < 0 ∧ 0 < q)) :
    sgnI q = -sgnI p := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [sgnI_of_pos h1, sgnI_of_neg h2]
  · rw [sgnI_of_neg h1, sgnI_of_pos h2, neg_neg]

theorem natAbs_sub_sgnI {n : ℤ} (hn : n ≠ 0) : (n - sgnI n).natAbs = n.natAbs - 1 := by
  unfold sgnI; split <;> omega

theorem runLetters_cons (t : β) {n : ℤ} (hn : n ≠ 0) :
    runLetters t n = (t, decide (0 < n)) :: runLetters t (n - sgnI n) := by
  simp only [runLetters]
  have h : n.natAbs = (n - sgnI n).natAbs + 1 := by
    have := natAbs_sub_sgnI hn; omega
  rw [h, List.replicate_succ]
  congr 1
  by_cases hk : (n - sgnI n).natAbs = 0
  · rw [hk, List.replicate_zero, List.replicate_zero]
  · have hdec : decide (0 < n) = decide (0 < n - sgnI n) := by
      by_cases h : 0 < n
      · have hs : sgnI n = 1 := sgnI_of_pos h
        have h' : 0 < n - 1 := by rw [hs] at hk; omega
        rw [hs, decide_eq_true_eq.mpr h, decide_eq_true_eq.mpr h']
      · have hs : sgnI n = -1 := sgnI_of_neg (by omega)
        have h' : ¬ (0 < n - -1) := by rw [hs] at hk; omega
        rw [hs, decide_eq_false_iff_not.mpr h, decide_eq_false_iff_not.mpr h']
    rw [hdec]

theorem runLetters_concat (t : β) {n : ℤ} (hn : n ≠ 0) :
    runLetters t n = runLetters t (n - sgnI n) ++ [(t, decide (0 < n))] := by
  simp only [runLetters]
  have h : n.natAbs = (n - sgnI n).natAbs + 1 := by
    have := natAbs_sub_sgnI hn; omega
  rw [h, List.replicate_add, List.replicate_one]
  congr 1
  by_cases hk : (n - sgnI n).natAbs = 0
  · rw [hk, List.replicate_zero, List.replicate_zero]
  · have hdec : decide (0 < n) = decide (0 < n - sgnI n) := by
      by_cases h : 0 < n
      · have hs : sgnI n = 1 := sgnI_of_pos h
        have h' : 0 < n - 1 := by rw [hs] at hk; omega
        rw [hs, decide_eq_true_eq.mpr h, decide_eq_true_eq.mpr h']
      · have hs : sgnI n = -1 := sgnI_of_neg (by omega)
        have h' : ¬ (0 < n - -1) := by rw [hs] at hk; omega
        rw [hs, decide_eq_false_iff_not.mpr h, decide_eq_false_iff_not.mpr h']
    rw [hdec]

theorem runLetters_ne_nil (t : β) {n : ℤ} (hn : n ≠ 0) : runLetters t n ≠ [] := by
  rw [runLetters]
  intro h
  have h' : (t, decide (0 < n)) ∈ List.replicate n.natAbs (t, decide (0 < n)) :=
    List.mem_replicate.mpr ⟨by omega, rfl⟩
  rw [h] at h'
  simp at h'

theorem head?_runLetters_append (t : β) (n : ℤ) {Z : List (β × Bool)} (hZ : Z ≠ []) :
    (runLetters t n ++ Z).head? = if n = 0 then Z.head? else some (t, decide (0 < n)) := by
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg hn, List.head?_append_of_ne_nil _ (runLetters_ne_nil t hn), runLetters_cons t hn,
      List.head?_cons]

theorem getLast?_append_runLetters (t : β) (n : ℤ) {Z : List (β × Bool)} (hZ : Z ≠ []) :
    (Z ++ runLetters t n).getLast? = if n = 0 then Z.getLast? else some (t, decide (0 < n)) := by
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg hn, List.getLast?_append_of_ne_nil _ (runLetters_ne_nil t hn), runLetters_concat t hn,
      List.getLast?_append_cons, List.getLast?_singleton]

theorem invRev_runLetters (t : β) (n : ℤ) :
    FreeGroup.invRev (runLetters t n) = runLetters t (-n) := by
  by_cases hn : n = 0
  · subst hn; simp
  · simp only [runLetters, Int.natAbs_neg, FreeGroup.invRev, List.reverse_replicate,
      List.map_replicate]
    congr 1
    rw [Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    by_cases h : 0 < n
    · have h2 : ¬ (0 < -n) := by rw [neg_pos]; exact not_lt.mpr h.le
      simp only [decide_eq_true_eq.mpr h, decide_eq_false_iff_not.mpr h2, Bool.not_true]
    · have hn' : n < 0 := by omega
      have h2 : 0 < -n := by rw [neg_pos]; exact hn'
      simp only [decide_eq_false_iff_not.mpr h, decide_eq_true_eq.mpr h2, Bool.not_false]

/-! ### `conjugator` vanishes when the two ends do not cancel -/

theorem conjugator_eq_nil [DecidableEq β] {W : List (β × Bool)}
    (h : ∀ a ∈ W.head?, ∀ b ∈ W.getLast?, ¬ (b.1 = a.1 ∧ b.2 = !a.2)) :
    FreeGroup.reduceCyclically.conjugator W = [] := by
  induction W using List.bidirectionalRec with
  | nil => simp
  | singleton a => simp
  | cons_append a l b =>
    rw [FreeGroup.reduceCyclically.conjugator.cons_append]
    rw [if_neg]
    intro hc
    refine h a (by simp) b ?_ ?_
    · have h1 : a :: (l ++ [b]) = (a :: l) ++ [b] := by simp
      rw [h1, List.getLast?_append_cons, List.getLast?_singleton]
      simp
    · cases ha : a.2 <;> cases hb : b.2 <;> simp_all

/-! ### The peeling analysis -/

/-- The two ends of the sandwich are `t`-runs of opposite sign. -/
abbrev caseB (p q : ℤ) : Prop := (0 < p ∧ q < 0) ∨ (p < 0 ∧ 0 < q)

/-- The number of peeled letters. -/
def peelCount (p q : ℤ) : ℕ := if caseB p q then min p.natAbs q.natAbs else 0

/-- The letter of the peeled run. -/
def tLetter (t : β) (p : ℤ) : β × Bool := if 0 < p then (t, true) else (t, false)

/-- The exponent of the peeled run. -/
def peelM (p q : ℤ) : ℤ := if caseB p q then sgnI p * ((min p.natAbs q.natAbs : ℕ) : ℤ) else 0

theorem tLetter_eq (t : β) {p : ℤ} (hp : p ≠ 0) : tLetter t p = (t, decide (0 < p)) := by
  by_cases h : 0 < p
  · rw [tLetter, if_pos h, decide_eq_true_eq.mpr h]
  · rw [tLetter, if_neg h, decide_eq_false_iff_not.mpr h]

theorem runLetters_peelM (t : β) (p q : ℤ) :
    runLetters t (peelM p q) = List.replicate (peelCount p q) (tLetter t p) := by
  by_cases hB : caseB p q
  · have hp : p ≠ 0 := by rintro rfl; simp [caseB] at hB
    have hK : 0 < min p.natAbs q.natAbs := by
      rcases hB with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    have hK' : (0 : ℤ) < ((min p.natAbs q.natAbs : ℕ) : ℤ) := by exact_mod_cast hK
    have hnat : (sgnI p * ((min p.natAbs q.natAbs : ℕ) : ℤ)).natAbs = min p.natAbs q.natAbs := by
      rw [Int.natAbs_mul]
      have hs : (sgnI p).natAbs = 1 := by unfold sgnI; split <;> norm_num
      rw [hs, one_mul]
      omega
    rw [peelM, if_pos hB, peelCount, if_pos hB, tLetter_eq t hp, runLetters, hnat]
    congr 1
    rw [Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    rw [decide_eq_decide]
    rcases hB with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [sgnI_of_pos h1]
      exact ⟨fun _ => h1, fun _ => by rw [one_mul]; exact hK'⟩
    · rw [sgnI_of_neg h1]
      constructor
      · intro hh; omega
      · intro hh; omega
  · rw [peelM, if_neg hB, peelCount, if_neg hB, runLetters_zero, List.replicate_zero]

theorem peelCount_step {p q : ℤ} (hB : caseB p q) :
    peelCount (p - sgnI p) (q - sgnI q) + 1 = peelCount p q := by
  rcases hB with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [sgnI_of_pos h1, sgnI_of_neg h2]
    by_cases hmin : min p.natAbs q.natAbs ≤ 1
    · have hz : ¬ caseB (p - 1) (q - -1) := by
        simp only [caseB]
        rintro (⟨e1, e2⟩ | ⟨e1, e2⟩) <;> omega
      rw [peelCount, if_neg hz, peelCount, if_pos (Or.inl ⟨h1, h2⟩)]
      omega
    · have hc : caseB (p - 1) (q - -1) := by
        simp only [caseB]
        exact Or.inl ⟨by omega, by omega⟩
      rw [peelCount, if_pos hc, peelCount, if_pos (Or.inl ⟨h1, h2⟩)]
      omega
  · rw [sgnI_of_neg h1, sgnI_of_pos h2]
    by_cases hmin : min p.natAbs q.natAbs ≤ 1
    · have hz : ¬ caseB (p - -1) (q - 1) := by
        simp only [caseB]
        rintro (⟨e1, e2⟩ | ⟨e1, e2⟩) <;> omega
      rw [peelCount, if_neg hz, peelCount, if_pos (Or.inr ⟨h1, h2⟩)]
      omega
    · have hc : caseB (p - -1) (q - 1) := by
        simp only [caseB]
        exact Or.inr ⟨by omega, by omega⟩
      rw [peelCount, if_pos hc, peelCount, if_pos (Or.inr ⟨h1, h2⟩)]
      omega

theorem tLetter_step (t : β) {p q : ℤ} (hB : caseB p q)
    (h : peelCount (p - sgnI p) (q - sgnI q) ≠ 0) :
    tLetter t p = tLetter t (p - sgnI p) := by
  rcases hB with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [sgnI_of_pos h1] at h ⊢
    have hp' : 0 < p - 1 := by
      by_contra hc
      apply h
      have hz : ¬ caseB (p - 1) (q - sgnI q) := by
        rintro (⟨e1, e2⟩ | ⟨e1, e2⟩) <;> omega
      rw [peelCount, if_neg hz]
    rw [tLetter, if_pos h1, tLetter, if_pos hp']
  · rw [sgnI_of_neg h1] at h ⊢
    have hp' : ¬ (0 < p - -1) := by
      by_contra hc
      apply h
      have hz : ¬ caseB (p - -1) (q - sgnI q) := by
        rintro (⟨e1, e2⟩ | ⟨e1, e2⟩) <;> omega
      rw [peelCount, if_neg hz]
    rw [tLetter, if_neg (by omega : ¬ (0 < p)), tLetter, if_neg hp']

/-! ### The main peeling lemma -/

theorem conjAux (t : β) [DecidableEq β] :
    ∀ (N : ℕ) (p q : ℤ) (Y : List (β × Bool)), p.natAbs + q.natAbs ≤ N → Y ≠ [] →
      (∀ a ∈ Y.head?, a.1 ≠ t) → (∀ a ∈ Y.getLast?, a.1 ≠ t) →
      (p = -q → ∀ a ∈ Y.getLast?, ∀ b ∈ Y.head?, a.1 = b.1 → a.2 = b.2) →
      FreeGroup.reduceCyclically.conjugator (runLetters t p ++ Y ++ runLetters t q)
        = List.replicate (peelCount p q) (tLetter t p) := by
  intro N
  induction N with
  | zero =>
    intro p q Y hle hY hhead hlast hcyc
    have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    have hpc : peelCount p q = 0 := by
      rw [peelCount, if_neg]
      simp only [caseB]; omega
    rw [hp, hq] at hpc
    rw [hp, hq, hpc, List.replicate_zero]
    simp only [runLetters_zero, List.nil_append, List.append_nil]
    refine conjugator_eq_nil ?_
    intro a ha b hb hc
    have h2 := hcyc (by omega) b hb a ha hc.1
    cases ha2 : a.2 <;> cases hb2 : b.2 <;> simp_all
  | succ N ih =>
    intro p q Y hle hY hhead hlast hcyc
    by_cases hB : caseB p q
    · obtain ⟨hp, hq⟩ : p ≠ 0 ∧ q ≠ 0 :=
        ⟨by rintro rfl; simp [caseB] at hB, by rintro rfl; simp [caseB] at hB⟩
      have hshape : runLetters t p ++ Y ++ runLetters t q =
          (tLetter t p) :: ((runLetters t (p - sgnI p) ++ Y ++ runLetters t (q - sgnI q)) ++
            [(tLetter t q)]) := by
        rw [runLetters_cons t hp, runLetters_concat t hq, ← tLetter_eq t hp, ← tLetter_eq t hq]
        simp
      have hcancel : ((tLetter t q).1 = (tLetter t p).1 ∧
          (!(tLetter t q).2) = (tLetter t p).2) := by
        rw [tLetter_eq t hq, tLetter_eq t hp]
        refine ⟨rfl, ?_⟩
        simp only [Prod.snd]
        rcases hB with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hq' : ¬ (0 < q) := not_lt.mpr h2.le
          simp [h1, hq']
        · have hp' : ¬ (0 < p) := not_lt.mpr h1.le
          simp [h2, hp']
      have hle' : (p - sgnI p).natAbs + (q - sgnI q).natAbs ≤ N := by
        rw [natAbs_sub_sgnI hp, natAbs_sub_sgnI hq]
        omega
      have hcyc' : (p - sgnI p) = -(q - sgnI q) →
          ∀ a ∈ Y.getLast?, ∀ b ∈ Y.head?, a.1 = b.1 → a.2 = b.2 := by
        intro hpq a ha b hb hab
        exact hcyc (by have := sgnI_opposite hB; omega) a ha b hb hab
      have hIH := ih (p - sgnI p) (q - sgnI q) Y hle' hY hhead hlast hcyc'
      rw [hshape, FreeGroup.reduceCyclically.conjugator.cons_append, if_pos hcancel,
        ← peelCount_step hB]
      rw [List.replicate_succ]
      congr 1
      rw [hIH]
      by_cases hK : peelCount (p - sgnI p) (q - sgnI q) = 0
      · rw [hK, List.replicate_zero, List.replicate_zero]
      · congr 1
        exact (tLetter_step t hB hK).symm
    · rw [peelCount, if_neg hB, List.replicate_zero]
      refine conjugator_eq_nil ?_
      have hheadW : ((runLetters t p ++ Y) ++ runLetters t q).head? =
          if p = 0 then Y.head? else some (t, decide (0 < p)) := by
        rw [List.append_assoc, head?_runLetters_append t p (by simp [hY])]
        by_cases hp : p = 0 <;> simp [hp, List.head?_append_of_ne_nil _ hY]
      have hlastW : ((runLetters t p ++ Y) ++ runLetters t q).getLast? =
          if q = 0 then Y.getLast? else some (t, decide (0 < q)) := by
        rw [getLast?_append_runLetters t q (by simp [hY])]
        by_cases hq : q = 0 <;> simp [hq, List.getLast?_append_of_ne_nil _ hY]
      intro a ha b hb hc
      rw [hheadW] at ha
      rw [hlastW] at hb
      by_cases hp : p = 0 <;> by_cases hq : q = 0
      · rw [if_pos hp] at ha
        rw [if_pos hq] at hb
        have h2 := hcyc (by omega) b hb a ha hc.1
        cases ha2 : a.2 <;> cases hb2 : b.2 <;> simp_all
      · rw [if_pos hp] at ha
        rw [if_neg hq] at hb
        obtain rfl := Option.mem_some_iff.mp hb
        exact hhead a ha (by simpa using hc.1.symm)
      · rw [if_neg hp] at ha
        rw [if_pos hq] at hb
        obtain rfl := Option.mem_some_iff.mp ha
        exact hlast b hb (by simpa using hc.1)
      · rw [if_neg hp] at ha
        rw [if_neg hq] at hb
        obtain rfl := Option.mem_some_iff.mp ha
        obtain rfl := Option.mem_some_iff.mp hb
        have hdec : decide (0 < q) = decide (0 < p) := by
          rw [decide_eq_decide]
          constructor <;> intro h
          · by_contra hq'; simp only [caseB] at hB; omega
          · by_contra hp'; simp only [caseB] at hB; omega
        obtain ⟨-, hc2⟩ := hc
        simp only [Prod.snd] at hc2
        rw [hdec] at hc2
        cases hd : decide (0 < p) <;> simp [hd] at hc2

/-!
# Sandwiching a word between two `t`-runs

`Work.OROneRel.runLetters t n` is the signed run `t ^ n` as a word.  This file proves the list
lemma underlying the cyclic reduction of the Magnus expansion of a cyclically reduced decorated
word (`Work.OROneRel.mrsl_expAux_cyclicReduction`): a reduced word of the shape
`t ^ p · Y · t ^ q`, whose *inner* word `Y` begins and ends with letters different from `t`, is
`t ^ m`-conjugate to a cyclically reduced word, and the conjugating runs are exactly
`t ^ m` and `t ^ (-m)`.

The proof splits off the two runs: a word of the shape `run p ++ Y ++ run q` can be rewritten as
`a :: (l ++ [b])` where `a` (resp. `b`) is the first (resp. last) letter, so the Mathlib function
`FreeGroup.reduceCyclically.conjugator` — which peels such letters from both ends as long as they
cancel — can be evaluated by induction on `p.natAbs + q.natAbs`.  The peeled letters form the run
`run m`, the remaining middle is `reduceCyclically`, and Mathlib's
`conj_conjugator_reduceCyclically` finishes the job.
-/

/-- **Sandwiching a word between two `t`-runs.**  Let `W = runLetters t p ++ Y ++ runLetters t q` be
reduced, with the two ends of the nonempty `Y` different from `t` and not cancelling when
`p = -q`.  Then `W = runLetters t m ++ V ++ runLetters t (-m)` for some `m` and some *cyclically
reduced* `V` (namely `V = FreeGroup.reduceCyclically W`, the part of `W` left after peeling the
two runs from its ends). -/
theorem mrsl_runLetters_sandwich {β : Type u} (t : β) {W Y : List (β × Bool)} {p q : ℤ}
    (hW : W = Work.OROneRel.runLetters t p ++ Y ++ Work.OROneRel.runLetters t q)
    (hY : Y ≠ [])
    (hred : FreeGroup.IsReduced W)
    (hhead : ∀ a ∈ Y.head?, a.1 ≠ t)
    (hlast : ∀ a ∈ Y.getLast?, a.1 ≠ t)
    (hcyc : p = -q → ∀ a ∈ Y.getLast?, ∀ b ∈ Y.head?, a.1 = b.1 → a.2 = b.2) :
    ∃ m : ℤ, ∃ V : List (β × Bool),
      W = Work.OROneRel.runLetters t m ++ V ++ Work.OROneRel.runLetters t (-m) ∧
        FreeGroup.IsCyclicallyReduced V := by
  classical
  have hc := conjAux t (p.natAbs + q.natAbs) p q Y le_rfl hY hhead hlast hcyc
  have hm : FreeGroup.reduceCyclically.conjugator W = runLetters t (peelM p q) := by
    rw [hW, hc, ← runLetters_peelM]
  refine ⟨peelM p q, FreeGroup.reduceCyclically W, ?_, ?_⟩
  · calc W = FreeGroup.reduceCyclically.conjugator W ++ FreeGroup.reduceCyclically W ++
          FreeGroup.invRev (FreeGroup.reduceCyclically.conjugator W) :=
        (FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically W).symm
      _ = runLetters t (peelM p q) ++ FreeGroup.reduceCyclically W ++
          runLetters t (-(peelM p q)) := by rw [hm, invRev_runLetters]
  · exact FreeGroup.reduceCyclically.isCyclicallyReduced hred

end Work.OROneRel
