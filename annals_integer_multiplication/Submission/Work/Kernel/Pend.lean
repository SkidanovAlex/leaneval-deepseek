import Submission.Work.Kernel.Raw

/-!
# The "pending subtrees" counter of `Val.enc`

`enc v` is a self-delimiting encoding: reading it left to right, starting with one pending subtree,
incrementing on `cons` and decrementing on `nil`/`iend`, the counter returns to `0` exactly when the
whole encoding has been read; on every *proper* prefix it is still positive.

This module provides `pendStep`/`pendFold` and those two facts, for use by the value movers.
-/

set_option autoImplicit false

namespace HvdH

open Computability

/-- One step of the pending-subtree counter. -/
def pendStep (g : Glyph) (k : ℕ) : ℕ :=
  match g with
  | .cons => k + 1
  | .nil => k - 1
  | .iend => k - 1
  | _ => k

/-- Result of running the pending-subtree counter over the glyph list `l` from `k`. -/
def pendFold (l : List Glyph) (k : ℕ) : ℕ := l.foldl (fun k g => pendStep g k) k

@[simp] theorem pendStep_cons (k : ℕ) : pendStep .cons k = k + 1 := rfl
@[simp] theorem pendStep_nil (k : ℕ) : pendStep .nil k = k - 1 := rfl
@[simp] theorem pendStep_iend (k : ℕ) : pendStep .iend k = k - 1 := rfl
@[simp] theorem pendStep_pos (k : ℕ) : pendStep .pos k = k := rfl
@[simp] theorem pendStep_neg (k : ℕ) : pendStep .neg k = k := rfl
@[simp] theorem pendStep_bit (b : Bool) (k : ℕ) : pendStep (.bit b) k = k := rfl
@[simp] theorem pendStep_mk (i : Fin 16) (k : ℕ) : pendStep (.mk i) k = k := rfl
@[simp] theorem pendStep_eos (k : ℕ) : pendStep .eos k = k := rfl
@[simp] theorem pendStep_inp (a b : Option Bool) (k : ℕ) : pendStep (.inp a b) k = k := rfl

@[simp] theorem pendFold_nil (k : ℕ) : pendFold [] k = k := rfl

@[simp] theorem pendFold_cons (g : Glyph) (t : List Glyph) (k : ℕ) :
    pendFold (g :: t) k = pendFold t (pendStep g k) := by
  simp [pendFold]

theorem pendFold_append (l₁ l₂ : List Glyph) (k : ℕ) :
    pendFold (l₁ ++ l₂) k = pendFold l₂ (pendFold l₁ k) := by
  simp [pendFold, List.foldl_append]

theorem pendFold_map_bit (l : List Bool) (k : ℕ) : pendFold (l.map Glyph.bit) k = k := by
  induction l generalizing k with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem pendFold_take_map_bit (l : List Bool) (i k : ℕ) :
    pendFold ((l.map Glyph.bit).take i) k = k := by
  rw [← List.map_take]; exact pendFold_map_bit _ _

/-- `PendOK l k`: reading `l` from the counter value `k` returns `k - 1`, and the counter stays
`≥ k` on every proper prefix of `l`. -/
def PendOK (l : List Glyph) (k : ℕ) : Prop :=
  pendFold l k = k - 1 ∧ ∀ i < l.length, k ≤ pendFold (l.take i) k

theorem pendOK_nil (k : ℕ) : PendOK [Glyph.nil] k := by
  constructor
  · simp
  · intro i hi
    rcases i with _ | j
    · simp
    · simp at hi

theorem pendOK_int (sg : Glyph) (l : List Bool) (k : ℕ) (hsg : pendStep sg k = k) :
    PendOK (sg :: (l.map Glyph.bit ++ [Glyph.iend])) k := by
  constructor
  · rw [pendFold_cons, hsg, pendFold_append, pendFold_map_bit]; simp
  · intro i hi
    rcases i with _ | j
    · simp
    · rw [List.take_succ_cons, pendFold_cons]
      have hj : j ≤ l.length := by simp at hi; omega
      rw [List.take_append_of_le_length (show j ≤ (l.map Glyph.bit).length by simpa using hj)]
      rw [hsg, pendFold_take_map_bit]

theorem pendOK_cons (a b : Val) (k : ℕ) (hk : 1 ≤ k)
    (ha : PendOK a.enc (k + 1)) (hb : PendOK b.enc k) :
    PendOK (Glyph.cons :: (a.enc ++ b.enc)) k := by
  constructor
  · rw [pendFold_cons, pendStep_cons, pendFold_append, ha.1, Nat.add_sub_cancel]; exact hb.1
  · intro i hi
    rcases i with _ | j
    · simp
    · rw [List.take_succ_cons, pendFold_cons, pendStep_cons]
      have hj : j < a.enc.length + b.enc.length := by simp at hi; omega
      by_cases hja : j < a.enc.length
      · rw [List.take_append_of_le_length (by omega : j ≤ a.enc.length)]
        have := ha.2 j hja
        omega
      · have hja' : a.enc.length ≤ j := by omega
        rw [List.take_append, List.take_of_length_le hja']
        rw [pendFold_append, ha.1, Nat.add_sub_cancel]
        exact hb.2 (j - a.enc.length) (by omega)

theorem pendOK_enc (v : Val) (k : ℕ) (hk : 1 ≤ k) : PendOK v.enc k := by
  induction v generalizing k with
  | int z =>
    by_cases h : z < 0
    · simpa [Val.enc, h] using pendOK_int Glyph.neg (encodeNat z.natAbs) k (by simp)
    · simpa [Val.enc, h] using pendOK_int Glyph.pos (encodeNat z.natAbs) k (by simp)
  | nil => simpa [Val.enc] using pendOK_nil k
  | cons a b iha ihb =>
    simpa [Val.enc] using pendOK_cons a b k hk (iha (k + 1) (by omega)) (ihb k hk)

/-- The pending counter returns to zero after reading a complete value. -/
theorem pendFold_enc (v : Val) (k : ℕ) : pendFold v.enc (k + 1) = k :=
  (pendOK_enc v (k + 1) (by omega)).1

/-- On a proper prefix of an encoding the pending counter is still positive. -/
theorem pendFold_take_pos (v : Val) (i : ℕ) (hi : i < vsz v) : 0 < pendFold (v.enc.take i) 1 :=
  (pendOK_enc v 1 (by omega)).2 i hi

end HvdH
