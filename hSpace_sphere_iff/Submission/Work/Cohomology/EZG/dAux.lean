/-
# Auxiliary facts for the cancellation of the "mixed" terms

The mixed (neither `a`-side nor `b`-side) indices of the expanded boundary of the shuffle chain
are paired by exchanging the membership of two adjacent positions `q.castSucc`, `q.succ` of the
shuffle (`swapA`), keeping the face index `k` fixed.  This file collects the elementary facts
about `swapA` that the cancellation uses.
-/
import Mathlib
import Submission.Work.Cohomology.EZG.EZShufSetup

namespace Work.Cohomology.EZG

open Work.Cohomology

variable {N : ℕ}

lemma swapA_of_mem {A : Finset (Fin (N+1))} {q : Fin N} (hq : q.castSucc ∈ A) :
    swapA N A q = insert q.succ (A.erase q.castSucc) := by
  unfold swapA; rw [if_pos hq]

lemma swapA_of_notMem {A : Finset (Fin (N+1))} {q : Fin N} (hq : q.castSucc ∉ A) :
    swapA N A q = insert q.castSucc (A.erase q.succ) := by
  unfold swapA; rw [if_neg hq]

/-- The two ways of saying that exactly one of `q.castSucc`, `q.succ` lies in `A`. -/
lemma dcond_iff {A : Finset (Fin (N+1))} {q : Fin N} :
    (q.castSucc ∈ A ↔ q.succ ∉ A) ↔ (q.succ ∈ A ↔ q.castSucc ∉ A) := by tauto

lemma swapA_card (A : Finset (Fin (N+1))) (q : Fin N)
    (h : q.castSucc ∈ A ↔ q.succ ∉ A) : (swapA N A q).card = A.card := by
  by_cases hq : q.castSucc ∈ A
  · have hq' : q.succ ∉ A := h.mp hq
    rw [swapA_of_mem hq]
    have hne : q.succ ∉ A.erase q.castSucc := by
      rw [Finset.mem_erase]; exact fun hh => hq' hh.2
    rw [Finset.card_insert_of_notMem hne, Finset.card_erase_add_one hq]
  · have hq' : q.succ ∈ A := by by_contra hc; exact hq (h.mpr hc)
    rw [swapA_of_notMem hq]
    have hne : q.castSucc ∉ A.erase q.succ := by
      rw [Finset.mem_erase]; exact fun hh => hq hh.2
    rw [Finset.card_insert_of_notMem hne, Finset.card_erase_add_one hq']

lemma swapA_mem_of_ne (A : Finset (Fin (N+1))) (q : Fin N) {i : Fin (N+1)}
    (hi : i ≠ q.castSucc) (hi' : i ≠ q.succ) : (i ∈ swapA N A q ↔ i ∈ A) := by
  by_cases hq : q.castSucc ∈ A
  · rw [swapA_of_mem hq, Finset.mem_insert, Finset.mem_erase]
    exact ⟨fun h => h.elim (fun heq => absurd heq hi') (fun hh => hh.2),
      fun h => Or.inr ⟨hi, h⟩⟩
  · rw [swapA_of_notMem hq, Finset.mem_insert, Finset.mem_erase]
    exact ⟨fun h => h.elim (fun heq => absurd heq hi) (fun hh => hh.2),
      fun h => Or.inr ⟨hi', h⟩⟩

lemma swapA_mem_castSucc (A : Finset (Fin (N+1))) (q : Fin N)
    (h : q.castSucc ∈ A ↔ q.succ ∉ A) : (q.castSucc ∈ swapA N A q ↔ q.succ ∈ A) := by
  by_cases hq : q.castSucc ∈ A
  · have hq' : q.succ ∉ A := h.mp hq
    rw [swapA_of_mem hq, Finset.mem_insert, Finset.mem_erase]
    exact ⟨fun hh => hh.elim (fun heq => absurd heq (Fin.castSucc_lt_succ (i := q)).ne)
        (fun hh => absurd rfl hh.1), fun hh => absurd hh hq'⟩
  · have hq' : q.succ ∈ A := by by_contra hc; exact hq (h.mpr hc)
    rw [swapA_of_notMem hq, Finset.mem_insert, Finset.mem_erase]
    exact ⟨fun _ => hq', fun _ => Or.inl rfl⟩

lemma swapA_mem_succ (A : Finset (Fin (N+1))) (q : Fin N)
    (h : q.castSucc ∈ A ↔ q.succ ∉ A) : (q.succ ∈ swapA N A q ↔ q.castSucc ∈ A) := by
  by_cases hq : q.castSucc ∈ A
  · rw [swapA_of_mem hq, Finset.mem_insert, Finset.mem_erase]
    exact ⟨fun _ => hq, fun _ => Or.inl rfl⟩
  · have hq' : q.succ ∈ A := by by_contra hc; exact hq (h.mpr hc)
    rw [swapA_of_notMem hq, Finset.mem_insert, Finset.mem_erase]
    exact ⟨fun hh => hh.elim (fun heq => absurd heq (Fin.castSucc_lt_succ (i := q)).ne')
        (fun hh => absurd rfl hh.1), fun hh => absurd hh hq⟩

/-- `swapA` again satisfies the "exactly one of `q.castSucc`, `q.succ` in `A`" condition. -/
lemma swapA_dcond (A : Finset (Fin (N+1))) (q : Fin N)
    (h : q.castSucc ∈ A ↔ q.succ ∉ A) :
    (q.castSucc ∈ swapA N A q ↔ q.succ ∉ swapA N A q) := by
  rw [swapA_mem_castSucc A q h, swapA_mem_succ A q h]
  exact dcond_iff.mp h

lemma swapA_invol (A : Finset (Fin (N+1))) (q : Fin N)
    (h : q.castSucc ∈ A ↔ q.succ ∉ A) : swapA N (swapA N A q) q = A := by
  have h' := swapA_dcond A q h
  ext i
  by_cases hi : i = q.castSucc
  · subst hi
    rw [swapA_mem_castSucc (swapA N A q) q h', swapA_mem_succ A q h]
  · by_cases hi' : i = q.succ
    · subst hi'
      rw [swapA_mem_succ (swapA N A q) q h', swapA_mem_castSucc A q h]
    · rw [swapA_mem_of_ne (swapA N A q) q hi hi', swapA_mem_of_ne A q hi hi']

/-- A `D`-index (neither on the `a`-side nor on the `b`-side) is never at the two ends. -/
lemma IsD_not_z {A : Finset (Fin (N+1))} {k : Fin (N+2)} (h : IsD N A k) :
    ¬ (k.val = 0 ∨ k.val = N + 1) := by
  rintro hz
  by_cases hd : delIdx k ∈ A
  · exact h.1 ⟨hd, hz.elim Or.inl fun h' => Or.inr (Or.inl h')⟩
  · exact h.2 ⟨hd, hz.elim Or.inl fun h' => Or.inr (Or.inl h')⟩

end Work.Cohomology.EZG
