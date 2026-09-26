import Submission.Work.Item3.NoReappearance
import Submission.Work.T3RebalanceTuple
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Submission.Nielsen
open Submission.FreeGroupAut
open FreeGroup
open scoped BigOperators
set_option autoImplicit false

/-!
# Item 3, PassRound: the fixpoint-pass product as a closure element

The balanced phase of the Fall-II run (`FallTwoRunNotes.md`: the classical
pass is a **fixpoint iteration** over the ends-with-`B` / begins-with-`B⁻¹`
word classes at the balanced coordinate `c`, halves `A ++ B`, `|A| = |B|`)
needs, as its first construction, the *closure element* that represents
"apply the pass for `K` rounds".  This module provides it:

* `passQ c` — all coordinates except `c` as a nodup list (a canonical round
  combines every coordinate; `item2` already decides per coordinate whether
  to act, so no external classification is needed);
* `passRound α c A B` — one canonical item-2 round over `passQ c`, with
  `passRound_mem_closure` (the round lies in `AutClosure n`),
  `passRound_fix_c` (the balanced coordinate is fixed: its word stays
  `A ++ B`), and `passRound_N_le` (one round never increases the total
  length `N`);
* `passIter K α c A B` — the product of `K` canonical rounds, round `t+1`
  computed against the automorphism reached after `t` rounds (the classical
  fixpoint-pass truncated at `K` rounds), with `passIter_mem_closure`,
  `passIter_fix_c`, `passIter_word_c` (the balanced word `A ++ B` survives
  all rounds, so every round is well-defined against the same halves) and
  `passIter_N_le`;
* `passIter_then_strict` — a phase that ends in a strict single move is a
  single strict closure macro: if after `K` rounds a closure element `σ`
  strictly shortens (`N ((α·γ)·σ) < N (α·γ)`, `γ := passIter K α c A B`),
  then `N (α·(γ·σ)) < N α` with `γ·σ ∈ AutClosure n`.

Per-coordinate content this is built from (`pass_coord_norm_le[_end/_begin]`,
`pass_coord_unchanged_of_id`): no coordinate's image grows under one pass —
an ends-with-`B` coordinate's new image is `w_q·w_c⁻¹`
(`item2Pass_apply_ends` + `norm_mul_inv_end_le`), a begins-with-`B⁻¹`
coordinate's is `w_c·w_q` (`item2Pass_apply_begins` +
`norm_mul_begin_le`), and an inactive coordinate is unchanged (`item2` is the
identity there, `item2_eq_one_of_neither` + the product-fix argument
`pass_coord_unchanged_of_id`).

**What this module does not claim** (recorded for the open core): how many
rounds suffice for the fixpoint (the phase-termination/no-reappearance
analysis), nor that after the fixpoint no row position ≤ p is balanced —
those are the index-advance lemmas that consume `passIter`; they are
separate and documented in `FallTwoRunNotes.md` / `NoReappearance.lean`.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- All coordinates except `c`, as a nodup list (the coordinate set of one
canonical item-2 round at the balanced coordinate `c`). -/
noncomputable def passQ {n : ℕ} (c : Fin n) : List (Fin n) :=
  ((Finset.univ.erase c : Finset (Fin n)).toList)

lemma passQ_nodup {n : ℕ} (c : Fin n) : (passQ c).Nodup := by
  classical
  unfold passQ
  exact Finset.nodup_toList (Finset.univ.erase c)

lemma passQ_mem {n : ℕ} {q c : Fin n} : q ∈ passQ c ↔ q ≠ c := by
  classical
  unfold passQ
  rw [Finset.mem_toList]
  rw [Finset.mem_erase]
  simp

lemma passQ_not_mem_c {n : ℕ} (c : Fin n) : c ∉ passQ c := by
  rw [passQ_mem]
  simp

/-- `item2` is the identity when `q ≠ c` is in neither pass class. -/
lemma item2_eq_one_of_neither {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (c q : Fin n)
    (A B : List (Fin n × Bool)) (hqc : q ≠ c)
    (hnoE : ¬ ∃ Y : List (Fin n × Bool), (α (FreeGroup.of q)).toWord = Y ++ B)
    (hnoB : ¬ ∃ Y : List (Fin n × Bool),
      (α (FreeGroup.of q)).toWord = FreeGroup.invRev B ++ Y) :
    item2 α c q A B = 1 := by
  classical
  simp [item2, hqc, hnoE, hnoB]

/-- If `item2` at `q ∈ Q` is the identity, the pass fixes the coordinate `q`
(its image is unchanged). -/
lemma pass_coord_unchanged_of_id {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (c q : Fin n)
    (A B : List (Fin n × Bool)) (Q : List (Fin n)) (hnd : Q.Nodup) (hq : q ∈ Q)
    (hid : item2 α c q A B = 1) :
    (α * item2Pass α c A B Q) (FreeGroup.of q) = α (FreeGroup.of q) := by
  classical
  let f : Fin n → MulAut (FreeGroup (Fin n)) := fun q' => item2 α c q' A B
  rcases mem_split_unique hq hnd with ⟨Q₁, Q₂, hQ, hq1, hq2⟩
  have hfix2 : ∀ σ ∈ Q₂.map f, σ (FreeGroup.of q) = FreeGroup.of q := by
    intro σ hσ
    rcases List.mem_map.mp hσ with ⟨q'', hq'', rfl⟩
    exact item2_fix_generator α c q'' q A B (by
      intro heq
      exact hq2 (by simpa [heq] using hq''))
  have hfix2p := prod_fix (Q₂.map f) (FreeGroup.of q) hfix2
  have hfix1 : ∀ σ ∈ Q₁.map f, σ (FreeGroup.of q) = FreeGroup.of q := by
    intro σ hσ
    rcases List.mem_map.mp hσ with ⟨q'', hq'', rfl⟩
    exact item2_fix_generator α c q'' q A B (by
      intro heq
      exact hq1 (by simpa [heq] using hq''))
  have hfix1p := prod_fix (Q₁.map f) (FreeGroup.of q) hfix1
  unfold item2Pass
  rw [hQ]
  rw [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  change α (((Q₁.map f).prod * (item2 α c q A B * (Q₂.map f).prod)) (FreeGroup.of q)) =
      α (FreeGroup.of q)
  calc
    α (((Q₁.map f).prod * (item2 α c q A B * (Q₂.map f).prod)) (FreeGroup.of q))
        = α ((Q₁.map f).prod ((item2 α c q A B * (Q₂.map f).prod) (FreeGroup.of q))) := rfl
    _ = α ((Q₁.map f).prod ((item2 α c q A B) ((Q₂.map f).prod (FreeGroup.of q)))) := rfl
    _ = α ((Q₁.map f).prod ((item2 α c q A B) (FreeGroup.of q))) := by rw [hfix2p]
    _ = α ((Q₁.map f).prod (FreeGroup.of q)) := by
          rw [hid]
          simp
    _ = α (FreeGroup.of q) := by rw [hfix1p]

/-- Ends-with-`B` coordinate: after the pass over `Q`, its length does not
increase. -/
lemma pass_coord_norm_le_end {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (c q : Fin n) (A B : List (Fin n × Bool)) (Q : List (Fin n))
    (hnd : Q.Nodup) (hq : q ∈ Q) (hqc : q ≠ c) (hcQ : c ∉ Q)
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B) (hAB : A.length = B.length)
    (hE : ∃ Y : List (Fin n × Bool), (α (FreeGroup.of q)).toWord = Y ++ B) :
    FreeGroup.norm ((α * item2Pass α c A B Q) (FreeGroup.of q)) ≤
      FreeGroup.norm (α (FreeGroup.of q)) := by
  rcases hE with ⟨Y, hqE⟩
  have happ := item2Pass_apply_ends α c A B Q hnd hq hqc hcQ (by exact ⟨Y, hqE⟩)
  rw [happ]
  exact norm_mul_inv_end_le (x := α (FreeGroup.of q)) (y := α (FreeGroup.of c))
    A B Y hAB hqE hmid

/-- Begins-with-`B⁻¹` coordinate (not ending with `B`): after the pass over
`Q`, its length does not increase. -/
lemma pass_coord_norm_le_begin {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (c q : Fin n) (A B : List (Fin n × Bool)) (Q : List (Fin n))
    (hnd : Q.Nodup) (hq : q ∈ Q) (hqc : q ≠ c) (hcQ : c ∉ Q)
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B) (hAB : A.length = B.length)
    (hnoE : ¬ ∃ Y : List (Fin n × Bool), (α (FreeGroup.of q)).toWord = Y ++ B)
    (hB : ∃ Y : List (Fin n × Bool),
      (α (FreeGroup.of q)).toWord = FreeGroup.invRev B ++ Y) :
    FreeGroup.norm ((α * item2Pass α c A B Q) (FreeGroup.of q)) ≤
      FreeGroup.norm (α (FreeGroup.of q)) := by
  rcases hB with ⟨Y, hqB⟩
  have happ := item2Pass_apply_begins α c A B Q hnd hq hqc hcQ hnoE (by exact ⟨Y, hqB⟩)
  rw [happ]
  exact norm_mul_begin_le (x := α (FreeGroup.of q)) (y := α (FreeGroup.of c))
    A B Y hAB hqB hmid

/-- Per-coordinate length bound under the pass over `Q`: no coordinate's
image grows. -/
theorem pass_coord_norm_le {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (c q : Fin n) (A B : List (Fin n × Bool)) (Q : List (Fin n))
    (hnd : Q.Nodup) (hq : q ∈ Q) (hqc : q ≠ c) (hcQ : c ∉ Q)
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B) (hAB : A.length = B.length) :
    FreeGroup.norm ((α * item2Pass α c A B Q) (FreeGroup.of q)) ≤
      FreeGroup.norm (α (FreeGroup.of q)) := by
  classical
  by_cases hE : ∃ Y : List (Fin n × Bool), (α (FreeGroup.of q)).toWord = Y ++ B
  · exact pass_coord_norm_le_end α c q A B Q hnd hq hqc hcQ hmid hAB hE
  · by_cases hB : ∃ Y : List (Fin n × Bool),
        (α (FreeGroup.of q)).toWord = FreeGroup.invRev B ++ Y
    · exact pass_coord_norm_le_begin α c q A B Q hnd hq hqc hcQ hmid hAB hE hB
    · have hid : item2 α c q A B = 1 :=
        item2_eq_one_of_neither α c q A B hqc hE hB
      have hunch := pass_coord_unchanged_of_id α c q A B Q hnd hq hid
      rw [hunch]

/-! ## The canonical round and the iterated (fixpoint) pass product -/

/-- One **canonical item-2 round** at the balanced coordinate `c` (halves
`A ++ B`): the item-2 pass over *all* coordinates except `c`.  Since `item2`
already decides per coordinate (ends-with-`B` → `rhoNeg q c`, else
begins-with-`B⁻¹` → `lam q c`, else identity), one round automatically
combines exactly the currently-active coordinates. -/
noncomputable def passRound {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool)) : MulAut (FreeGroup (Fin n)) :=
  item2Pass α c A B (passQ c)

/-- The round is a closure element. -/
theorem passRound_mem_closure {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool)) : passRound α c A B ∈ AutClosure n := by
  unfold passRound
  exact item2Pass_mem_closure α c A B (passQ c)

/-- The balanced coordinate is fixed by the round (its word stays
`A ++ B`). -/
theorem passRound_fix_c {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool)) :
    (α * passRound α c A B) (FreeGroup.of c) = α (FreeGroup.of c) := by
  unfold passRound
  exact item2Pass_fix α c A B (passQ c) (passQ_not_mem_c c)

/-- The round never increases the total length `N`. -/
theorem passRound_N_le {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool))
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B) (hAB : A.length = B.length) :
    N (α * passRound α c A B) ≤ N α := by
  classical
  unfold passRound
  have hnorm : ∀ k : Fin n,
      FreeGroup.norm ((α * item2Pass α c A B (passQ c)) (FreeGroup.of k)) ≤
        FreeGroup.norm (α (FreeGroup.of k)) := by
    intro k
    by_cases hkc : k = c
    · subst k
      have hfix := item2Pass_fix α c A B (passQ c) (passQ_not_mem_c c)
      rw [hfix]
    · have hq : k ∈ passQ c := passQ_mem.mpr hkc
      exact pass_coord_norm_le α c k A B (passQ c) (passQ_nodup c) hq hkc
        (passQ_not_mem_c c) hmid hAB
  unfold N
  exact Finset.sum_le_sum (fun i hi => hnorm i)

/-- The **iterated pass product**: the product of `K` canonical rounds, each
computed against the automorphism reached by the previous rounds (the
fixpoint-pass of the classical run, truncated at `K` rounds).  For `K`
rounds, `α · passIter K α c A B` is the automorphism after the phase. -/
noncomputable def passIter {n : ℕ} (K : ℕ) (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool)) : MulAut (FreeGroup (Fin n)) :=
  match K with
  | 0 => 1
  | K + 1 =>
      let γ : MulAut (FreeGroup (Fin n)) := passRound α c A B
      γ * passIter K (α * γ) c A B

/-- The iterated pass product is a closure element. -/
theorem passIter_mem_closure {n : ℕ} (K : ℕ) (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool)) : passIter K α c A B ∈ AutClosure n := by
  induction K generalizing α with
  | zero =>
      simp [passIter]
  | succ K ih =>
      rw [passIter]
      exact (AutClosure n).mul_mem (passRound_mem_closure α c A B)
        (ih (α := α * passRound α c A B))

/-- The balanced coordinate stays fixed through any number of rounds. -/
theorem passIter_fix_c {n : ℕ} (K : ℕ) (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool)) :
    (α * passIter K α c A B) (FreeGroup.of c) = α (FreeGroup.of c) := by
  induction K generalizing α with
  | zero =>
      simp [passIter]
  | succ K ih =>
      rw [passIter]
      rw [← mul_assoc]
      rw [ih (α := α * passRound α c A B)]
      exact passRound_fix_c α c A B

/-- The word of the balanced coordinate after any number of rounds is
unchanged (`A ++ B`). -/
theorem passIter_word_c {n : ℕ} (K : ℕ) (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool))
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B) :
    ((α * passIter K α c A B) (FreeGroup.of c)).toWord = A ++ B := by
  rw [passIter_fix_c K α c A B]
  exact hmid

/-- Any number of rounds never increases the total length `N`. -/
theorem passIter_N_le {n : ℕ} (K : ℕ) (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool))
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B) (hAB : A.length = B.length) :
    N (α * passIter K α c A B) ≤ N α := by
  revert hmid hAB
  induction K generalizing α with
  | zero =>
      intro hmid hAB
      simp [passIter]
  | succ K ih =>
      intro hmid hAB
      rw [passIter]
      rw [← mul_assoc]
      have hmid' : ((α * passRound α c A B) (FreeGroup.of c)).toWord = A ++ B := by
        rw [passRound_fix_c α c A B]
        exact hmid
      have h1 : N ((α * passRound α c A B) * passIter K (α * passRound α c A B) c A B) ≤
          N (α * passRound α c A B) := ih (α := α * passRound α c A B) hmid' hAB
      have h2 : N (α * passRound α c A B) ≤ N α := passRound_N_le α c A B hmid hAB
      exact le_trans h1 h2

/-- **A phase that ends in a strict single move is a strict closure macro.**
If after `K` pass rounds at the balanced coordinate `c` a closure element
`σ` strictly decreases the total length (`N ((α·γ)·σ) < N (α·γ)` with
`γ := passIter K α c A B`), then the whole phase — `K` rounds followed by the
strict move — is a single closure element strictly decreasing `N` from `α`:
`N (α·(γ·σ)) < N α`.  (The rounds are `N`-non-increasing by
`passIter_N_le`.) -/
theorem passIter_then_strict {n : ℕ} (K : ℕ) (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool)) (σ : MulAut (FreeGroup (Fin n)))
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B) (hAB : A.length = B.length)
    (hσ : σ ∈ AutClosure n)
    (hshort : N ((α * passIter K α c A B) * σ) < N (α * passIter K α c A B)) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  refine ⟨passIter K α c A B * σ, ?_, ?_⟩
  · exact (AutClosure n).mul_mem (passIter_mem_closure K α c A B) hσ
  · rw [← mul_assoc]
    exact lt_of_lt_of_le hshort (passIter_N_le K α c A B hmid hAB)

end Submission.Nielsen
