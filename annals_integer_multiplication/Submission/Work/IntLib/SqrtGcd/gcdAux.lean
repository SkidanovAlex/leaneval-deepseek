import Mathlib
import Submission.Work.IntLib.ofBitsAPI

/-!
# Leading `false` bits of a least-significant-first bit list

Auxiliary facts for the correctness proof of the binary gcd (`SqrtGcd/gcdFinishEval.lean`).

A bit list `l : List Bool` is read least significant bit first, so the *leading* entries of `l`
are the low-order bits of the value `ofBits l`.  `nLead l` counts them (the number of factors of
`2` in `ofBits l`) and `dropLead l` removes them (the odd part).  The file records that
`ofBits l = 2 ^ nLead l * ofBits (dropLead l)`, how dropping `k ≤ nLead l` low bits scales the
value, and that an odd part dropped from a *canonical* list (`Nat.bits`) is non-zero.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib.SqrtGcd

open HvdH Work.IntLib

/-- Number of leading `false` bits of a least-significant-first bit list. -/
def nLead (l : List Bool) : ℕ := (l.takeWhile (fun b => !b)).length

/-- The bit list with its leading `false` bits removed. -/
def dropLead (l : List Bool) : List Bool := l.dropWhile (fun b => !b)

@[simp] theorem nLead_nil : nLead [] = 0 := rfl
@[simp] theorem nLead_cons_true (l : List Bool) : nLead (true :: l) = 0 := rfl
@[simp] theorem nLead_cons_false (l : List Bool) : nLead (false :: l) = nLead l + 1 := rfl
@[simp] theorem dropLead_nil : dropLead [] = [] := rfl
@[simp] theorem dropLead_cons_true (l : List Bool) : dropLead (true :: l) = true :: l := rfl
@[simp] theorem dropLead_cons_false (l : List Bool) : dropLead (false :: l) = dropLead l := rfl

/-- A bit list is its leading `false` bits followed by its odd part. -/
theorem replicate_nLead_dropLead (l : List Bool) :
    List.replicate (nLead l) false ++ dropLead l = l := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    cases b with
    | true => rw [nLead_cons_true, dropLead_cons_true]; simp
    | false =>
      rw [nLead_cons_false, dropLead_cons_false, List.replicate_succ, List.cons_append]
      exact congrArg (List.cons false) ih

theorem nLead_le_length (l : List Bool) : nLead l ≤ l.length := by
  have h := List.Sublist.length_le (List.takeWhile_sublist (p := fun b : Bool => !b) (l := l))
  simpa [nLead] using h

theorem length_dropLead_le (l : List Bool) : (dropLead l).length ≤ l.length :=
  List.length_dropWhile_le (l := l) (p := fun b : Bool => !b)

theorem length_eq_nLead_add (l : List Bool) :
    nLead l + (dropLead l).length = l.length := by
  have h := congrArg List.length (replicate_nLead_dropLead l)
  simpa [List.length_append, List.length_replicate] using h

/-- The odd part of a bit list is empty or starts with a `true` bit. -/
theorem dropLead_eq_nil_or_head_true (l : List Bool) :
    dropLead l = [] ∨ (dropLead l).head? = some true := by
  induction l with
  | nil => exact Or.inl rfl
  | cons b t ih =>
    cases b with
    | true => exact Or.inr rfl
    | false => exact ih

theorem dropLead_replicate_false_append (j : ℕ) (t : List Bool) :
    dropLead (List.replicate j false ++ t) = dropLead t := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, List.cons_append, dropLead_cons_false]; exact ih

/-- Dropping `k ≤ nLead l` low bits does not change the odd part. -/
theorem dropLead_drop (l : List Bool) (k : ℕ) (hk : k ≤ nLead l) :
    dropLead (l.drop k) = dropLead l := by
  calc dropLead (l.drop k)
      = dropLead ((List.replicate (nLead l) false ++ dropLead l).drop k) := by
        rw [replicate_nLead_dropLead]
    _ = dropLead (List.replicate (nLead l - k) false ++ dropLead l) := by
        rw [List.drop_append_of_le_length (l₁ := List.replicate (nLead l) false)
          (l₂ := dropLead l) (i := k) (by simpa using hk), List.drop_replicate]
    _ = dropLead (dropLead l) := dropLead_replicate_false_append _ _
    _ = dropLead l := List.dropWhile_idempotent _ _

theorem ofBits_replicate_false (j : ℕ) : ofBits (List.replicate j false) = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, ofBits_cons, ih]; norm_num

/-- `ofBits l` is `2 ^ nLead l` times the value of the odd part. -/
theorem ofBits_eq_two_pow_mul_nLead (l : List Bool) :
    ofBits l = 2 ^ nLead l * ofBits (dropLead l) := by
  conv_lhs => rw [← replicate_nLead_dropLead l]
  rw [ofBits_append, ofBits_replicate_false, List.length_replicate, zero_add]

theorem ofBits_cons_true_ne_zero (t : List Bool) : ofBits (true :: t) ≠ 0 := by
  have h : ofBits (true :: t) = 1 + 2 * ofBits t := rfl
  rw [h]
  omega

/-- Dropping the `k ≤ nLead l` low bits divides the value by `2 ^ k`. -/
theorem ofBits_drop_eq (l : List Bool) (k : ℕ) (hk : k ≤ nLead l) :
    ofBits (l.drop k) = 2 ^ (nLead l - k) * ofBits (dropLead l) := by
  calc ofBits (l.drop k)
      = ofBits ((List.replicate (nLead l) false ++ dropLead l).drop k) := by
        rw [replicate_nLead_dropLead]
    _ = ofBits (List.replicate (nLead l - k) false ++ dropLead l) := by
        rw [List.drop_append_of_le_length (l₁ := List.replicate (nLead l) false)
          (l₂ := dropLead l) (i := k) (by simpa using hk), List.drop_replicate]
    _ = 2 ^ (nLead l - k) * ofBits (dropLead l) := by
        rw [ofBits_append, ofBits_replicate_false, List.length_replicate, zero_add]

/-- Multiplying the dropped low bits back gives the value. -/
theorem two_pow_mul_ofBits_drop (l : List Bool) (k : ℕ) (hk : k ≤ nLead l) :
    2 ^ k * ofBits (l.drop k) = ofBits l := by
  rw [ofBits_drop_eq l k hk, ofBits_eq_two_pow_mul_nLead l, ← mul_assoc, ← Nat.pow_add,
    Nat.add_sub_cancel' hk]

/-- If the dropped low bits are all zero, so is the value. -/
theorem ofBits_eq_zero_of_drop_eq_nil (l : List Bool) (k : ℕ) (hk : k ≤ nLead l)
    (h : l.drop k = []) : ofBits l = 0 := by
  rw [← two_pow_mul_ofBits_drop l k hk, h]
  rfl

theorem dropLead_head_true (l : List Bool) (h : dropLead l ≠ []) :
    (dropLead l).head? = some true := by
  rcases dropLead_eq_nil_or_head_true l with h1 | h1
  · exact absurd h1 h
  · exact h1

theorem dropLead_eq_true_cons (l : List Bool) (h : dropLead l ≠ []) :
    ∃ t : List Bool, dropLead l = true :: t := by
  have h1 := dropLead_head_true l h
  rcases hl : dropLead l with _ | ⟨b, t⟩
  · exact absurd hl h
  · rw [hl] at h1
    simp only [List.head?_cons, Option.some.injEq] at h1
    refine ⟨t, ?_⟩
    show b :: t = true :: t
    rw [h1]

theorem ofBits_dropLead_odd (l : List Bool) (h : dropLead l ≠ []) :
    ofBits (dropLead l) % 2 = 1 := by
  obtain ⟨t, ht⟩ := dropLead_eq_true_cons l h
  rw [ht]
  have h1 : ofBits (true :: t) = 1 + 2 * ofBits t := rfl
  rw [h1]
  omega

theorem ofBits_dropLead_ne_zero (l : List Bool) (h : dropLead l ≠ []) :
    ofBits (dropLead l) ≠ 0 := by
  intro h0
  have h1 := ofBits_dropLead_odd l h
  rw [h0] at h1
  exact absurd h1 (by norm_num)

/-- The odd part of a non-zero canonical bit list (`Nat.bits`) is non-empty. -/
theorem dropLead_bits_ne_nil (n : ℕ) (hn : n ≠ 0) : dropLead n.bits ≠ [] := by
  intro h
  have h1 : ofBits n.bits = 2 ^ nLead n.bits * ofBits (dropLead n.bits) :=
    ofBits_eq_two_pow_mul_nLead _
  rw [h] at h1
  have h2 : ofBits ([] : List Bool) = 0 := rfl
  rw [h2, mul_zero] at h1
  rw [ofBits_bits] at h1
  exact hn h1

end Work.IntLib.SqrtGcd
