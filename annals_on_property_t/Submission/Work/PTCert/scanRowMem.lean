import Mathlib
import Submission.Work.PTCert.Checks.SharedAll
import Submission.Work.PTCert.rowHelp

namespace Work.PTCert

/-
Goal: the membership characterization of the kernel scan `scanRow`
(`Submission/Work/PTCert/KernelShared.lean`), by unfolding only its definition.

`scanRow cm rowIdx a b x0 pcs` folds over `pcs`; for each `pc` it runs a `Nat.rec` on `32`,
i.e. the steps `sc = 0,1,…,31`, and prepends to the accumulator exactly one of
* `32 * pc + sc`, when `y := normC cm (actL 5 pc sc a) (actL 5 pc sc b)` equals `x0`;
* `0`, when `y ≠ x0` but `rG rowIdx y ≠ 0`;
* nothing, when `y ≠ x0` and `rG rowIdx y = 0`.
The statement below is exactly this, as a membership equivalence. It needs no hypotheses at all
(`pcs` is arbitrary, `cm`/`rowIdx` arbitrary) and no data evaluation: split on `pcs` (`List.rec`)
and on the inner `Nat.rec` counter, using `List.mem_cons`, `if`/`bif` case splits.
-/
open Submission.PTCert

set_option maxHeartbeats 1000000

/-- The single scan step: given an accumulator `acc`, the code `(pc, sc)` prepends `32 * pc + sc`
when the image `y = normC cm (actL 5 pc sc a) (actL 5 pc sc b)` equals `x0`, prepends `0` when
`y ≠ x0` but `rG rowIdx y ≠ 0`, and leaves `acc` unchanged otherwise. This is exactly the body of
the inner `Nat.rec` of `scanRow`. -/
private noncomputable def sstep (cm rowIdx : NT) (a b x0 pc : ℕ) (sc : ℕ) (acc : List ℕ) :
    List ℕ :=
  let y := normC cm (actL 5 pc sc a) (actL 5 pc sc b)
  bif Nat.beq y x0 then (32 * pc + sc) :: acc
  else bif Nat.beq (rG rowIdx y) 0 then acc else 0 :: acc

/-- One unfolding of `scanRow` at a nonempty list; the inner recursion is `sstep`. -/
private lemma scanRow_cons (cm rowIdx : NT) (a b x0 pc : ℕ) (pcs : List ℕ) :
    scanRow cm rowIdx a b x0 (pc :: pcs) =
      Nat.rec (scanRow cm rowIdx a b x0 pcs)
        (fun sc ih2 => sstep cm rowIdx a b x0 pc sc ih2) 32 := rfl

/-- Membership in a single `sstep`, unfolded. -/
private lemma mem_sstep (cm rowIdx : NT) (a b x0 pc sc c : ℕ) (acc : List ℕ) :
    c ∈ sstep cm rowIdx a b x0 pc sc acc ↔
      c ∈ acc ∨
      (normC cm (actL 5 pc sc a) (actL 5 pc sc b) = x0 ∧ c = 32 * pc + sc) ∨
      (normC cm (actL 5 pc sc a) (actL 5 pc sc b) ≠ x0 ∧
        rG rowIdx (normC cm (actL 5 pc sc a) (actL 5 pc sc b)) ≠ 0 ∧ c = 0) := by
  unfold sstep
  simp only [Bool.cond_eq_ite, Nat.beq_eq]
  split_ifs with h1 h2
  · simp only [List.mem_cons]; tauto
  · simp_all
  · simp only [List.mem_cons]; tauto

/-- Splitting `∃ sc < n + 1` into `∃ sc < n` plus the last step. -/
private lemma exists_lt_succ_iff' {P : ℕ → Prop} (n : ℕ) :
    (∃ sc < n + 1, P sc) ↔ (∃ sc < n, P sc) ∨ P n := by
  constructor
  · rintro ⟨sc, hsc, hp⟩
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hsc) with h | h
    · exact Or.inl ⟨sc, h, hp⟩
    · exact Or.inr (h ▸ hp)
  · intro h
    rcases h with h | hp
    · rcases h with ⟨sc, hsc, hp⟩
      exact ⟨sc, Nat.lt_succ_of_lt hsc, hp⟩
    · exact ⟨n, Nat.lt_succ_self n, hp⟩

/-- Distributing an existential over a disjunction, pulling the common conjunct `C` out of the
right branch. -/
private lemma exists_or_and_right {B D : ℕ → Prop} {C : Prop} {n : ℕ} :
    (∃ sc < n, B sc ∨ (D sc ∧ C)) ↔ (∃ sc < n, B sc) ∨ (C ∧ ∃ sc < n, D sc) := by
  constructor
  · rintro ⟨sc, hsc, hb | ⟨hd, hc⟩⟩
    · exact Or.inl ⟨sc, hsc, hb⟩
    · exact Or.inr ⟨hc, sc, hsc, hd⟩
  · rintro (⟨sc, hsc, hb⟩ | ⟨hc, sc, hsc, hd⟩)
    · exact ⟨sc, hsc, Or.inl hb⟩
    · exact ⟨sc, hsc, Or.inr ⟨hd, hc⟩⟩

/-- Splitting `∃ pc' ∈ pc :: pcs` into the head and the tail. -/
private lemma exists_mem_cons {P : ℕ → Prop} {pc : ℕ} {pcs : List ℕ} :
    (∃ pc' ∈ pc :: pcs, P pc') ↔ P pc ∨ ∃ pc' ∈ pcs, P pc' := by
  constructor
  · rintro ⟨pc', hpc', hp⟩
    rcases List.mem_cons.mp hpc' with h | h
    · exact Or.inl (h ▸ hp)
    · exact Or.inr ⟨pc', h, hp⟩
  · rintro (hp | ⟨pc', hpc', hp⟩)
    · exact ⟨pc, List.mem_cons_self .., hp⟩
    · exact ⟨pc', List.mem_cons_of_mem _ hpc', hp⟩

/-- The final propositional rearrangement (associativity/commutativity of `∨`). -/
private lemma final_combine {A S F G C : Prop} :
    (A ∨ (C ∧ S)) ∨ (F ∨ (C ∧ G)) ↔ (F ∨ A) ∨ ((C ∧ G) ∨ (C ∧ S)) := by tauto

/-- Membership in the inner `Nat.rec` of `scanRow` for one fixed `pc`: the accumulator plus, for
each step `sc < n`, either the code `32 * pc + sc` (when `y = x0`) or the sentinel `0` (when
`y ≠ x0` but `rG rowIdx y ≠ 0`). -/
private lemma mem_natrec (cm rowIdx : NT) (a b x0 pc : ℕ) (acc : List ℕ) (n c : ℕ) :
    c ∈ Nat.rec (motive := fun _ => List ℕ) acc
          (fun sc ih2 => sstep cm rowIdx a b x0 pc sc ih2) n ↔
      c ∈ acc ∨ ∃ sc < n,
        ((normC cm (actL 5 pc sc a) (actL 5 pc sc b) = x0 ∧ c = 32 * pc + sc) ∨
         ((normC cm (actL 5 pc sc a) (actL 5 pc sc b) ≠ x0 ∧
           rG rowIdx (normC cm (actL 5 pc sc a) (actL 5 pc sc b)) ≠ 0) ∧ c = 0)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.rec_add_one, mem_sstep, ih]
    rw [exists_lt_succ_iff']
    simp only [or_assoc, and_assoc]

theorem scanRowMem (cm rowIdx : NT) (a b x0 : ℕ) (pcs : List ℕ) (c : ℕ) :
    c ∈ scanRow cm rowIdx a b x0 pcs ↔
      (∃ pc ∈ pcs, ∃ sc < 32,
          normC cm (actL 5 pc sc a) (actL 5 pc sc b) = x0 ∧ c = 32 * pc + sc) ∨
      (c = 0 ∧ ∃ pc ∈ pcs, ∃ sc < 32,
          normC cm (actL 5 pc sc a) (actL 5 pc sc b) ≠ x0 ∧
          rG rowIdx (normC cm (actL 5 pc sc a) (actL 5 pc sc b)) ≠ 0) := by
  induction pcs with
  | nil => simp [scanRow]
  | cons pc pcs ih =>
    rw [scanRow_cons, mem_natrec, ih]
    rw [exists_or_and_right]
    rw [exists_mem_cons, exists_mem_cons]
    rw [and_or_left]
    exact final_combine

end Work.PTCert
