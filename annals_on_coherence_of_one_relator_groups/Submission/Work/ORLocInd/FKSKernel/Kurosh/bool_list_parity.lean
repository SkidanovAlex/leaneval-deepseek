import Mathlib

namespace Work.ORLocInd.FKSKernel.Kurosh

/-- Arithmetic: `n + 1` is even iff `n` is odd. -/
lemma succ_mod_two_eq_zero_iff (n : ℕ) : (n + 1) % 2 = 0 ↔ n % 2 ≠ 0 := by
  omega

/-- Arithmetic: shifting two integers by one preserves equality of parities. -/
lemma succ_mod_two_eq_succ_mod_two_iff (k m : ℕ) :
    (k + 1) % 2 = (m + 1) % 2 ↔ k % 2 = m % 2 := by
  omega

/-- In `Bool`, if `a ≠ b` then being equal to `a` is the same as being different from `b`. -/
private lemma bool_eq_iff_ne_of_ne {a b c : Bool} (hab : a ≠ b) : (c = a) ↔ (c ≠ b) := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- In `Bool`, if `a ≠ b` then `a = c` is the same as `c ≠ b`. -/
private lemma bool_ne_iff_eq_of_ne {a b c : Bool} (hab : a ≠ b) : (a = c) ↔ (c ≠ b) := by
  cases a <;> cases b <;> cases c <;> simp_all

private lemma bool_list_parity_aux : ∀ (L : List Bool), L.IsChain (fun a b => a ≠ b) →
    ∀ i j : Fin L.length, L.get i = L.get j ↔ i.val % 2 = j.val % 2 := by
  intro L
  induction L using List.twoStepInduction with
  | nil =>
      intro _ i j
      exact Fin.elim0 i
  | singleton c =>
      intro _ i j
      have hi : i = 0 := Fin.eq_zero i
      have hj : j = 0 := Fin.eq_zero j
      rw [hi, hj]
      simp
  | cons_cons a b t _ ih =>
      intro h i j
      obtain ⟨hab, hbt⟩ := List.isChain_cons_cons.mp h
      rcases i with ⟨iv, hiv⟩
      rcases j with ⟨jv, hjv⟩
      simp only [Fin.val_mk]
      rcases iv with _ | k
      · -- iv = 0
        have hi0 : (a :: b :: t).get (⟨0, hiv⟩ : Fin (a :: b :: t).length) = a :=
          List.get_cons_zero (a := a) (l := b :: t)
        rcases jv with _ | m
        · -- jv = 0
          have hj0 : (a :: b :: t).get (⟨0, hjv⟩ : Fin (a :: b :: t).length) = a :=
            List.get_cons_zero (a := a) (l := b :: t)
          rw [hi0]
          simp
        · -- jv = m + 1
          have hm : m < (b :: t).length := by
            have h' : m + 1 < (b :: t).length + 1 := hjv
            omega
          have hj1 : (a :: b :: t).get (⟨m + 1, hjv⟩ : Fin (a :: b :: t).length) =
              (b :: t).get (⟨m, hm⟩ : Fin (b :: t).length) :=
            List.get_cons_succ (i := m) (a := a) (as := b :: t) (h := hjv)
          rw [hi0, hj1]
          have h0 : 0 < (b :: t).length := by omega
          have key : (b :: t).get (⟨m, hm⟩ : Fin (b :: t).length) = b ↔ m % 2 = 0 := by
            have hih := ih b hbt (⟨m, hm⟩ : Fin (b :: t).length) (⟨0, h0⟩ : Fin (b :: t).length)
            have hz : (b :: t).get (⟨0, h0⟩ : Fin (b :: t).length) = b :=
              List.get_cons_zero (a := b) (l := t)
            rw [hz, Fin.val_mk, Nat.zero_mod] at hih
            exact hih
          have hL : a = (b :: t).get (⟨m, hm⟩ : Fin (b :: t).length) ↔ m % 2 ≠ 0 :=
            Iff.trans (bool_ne_iff_eq_of_ne (c := (b :: t).get (⟨m, hm⟩ : Fin (b :: t).length)) hab)
              (Iff.not key)
          exact Iff.trans hL (by omega)
      · -- iv = k + 1
        have hi1 : (a :: b :: t).get (⟨k + 1, hiv⟩ : Fin (a :: b :: t).length) =
            (b :: t).get (⟨k, by
              have h' : k + 1 < (b :: t).length + 1 := hiv
              omega⟩ : Fin (b :: t).length) :=
          List.get_cons_succ (i := k) (a := a) (as := b :: t) (h := hiv)
        rcases jv with _ | m
        · -- jv = 0
          have hj0 : (a :: b :: t).get (⟨0, hjv⟩ : Fin (a :: b :: t).length) = a :=
            List.get_cons_zero (a := a) (l := b :: t)
          rw [hi1, hj0]
          have hk : k < (b :: t).length := by
            have h' : k + 1 < (b :: t).length + 1 := hiv
            omega
          have h0 : 0 < (b :: t).length := by omega
          have key : (b :: t).get (⟨k, hk⟩ : Fin (b :: t).length) = b ↔ k % 2 = 0 := by
            have hih := ih b hbt (⟨k, hk⟩ : Fin (b :: t).length) (⟨0, h0⟩ : Fin (b :: t).length)
            have hz : (b :: t).get (⟨0, h0⟩ : Fin (b :: t).length) = b :=
              List.get_cons_zero (a := b) (l := t)
            rw [hz, Fin.val_mk, Nat.zero_mod] at hih
            exact hih
          have hL : (b :: t).get (⟨k, hk⟩ : Fin (b :: t).length) = a ↔ k % 2 ≠ 0 :=
            Iff.trans (bool_eq_iff_ne_of_ne (c := (b :: t).get (⟨k, hk⟩ : Fin (b :: t).length)) hab)
              (Iff.not key)
          exact Iff.trans hL (by omega)
        · -- jv = m + 1
          have hm : m < (b :: t).length := by
            have h' : m + 1 < (b :: t).length + 1 := hjv
            omega
          have hj1 : (a :: b :: t).get (⟨m + 1, hjv⟩ : Fin (a :: b :: t).length) =
              (b :: t).get (⟨m, hm⟩ : Fin (b :: t).length) :=
            List.get_cons_succ (i := m) (a := a) (as := b :: t) (h := hjv)
          have hk : k < (b :: t).length := by
            have h' : k + 1 < (b :: t).length + 1 := hiv
            omega
          rw [hi1, hj1]
          have hih : (b :: t).get (⟨k, hk⟩ : Fin (b :: t).length) =
              (b :: t).get (⟨m, hm⟩ : Fin (b :: t).length) ↔ k % 2 = m % 2 :=
            ih b hbt (⟨k, hk⟩ : Fin (b :: t).length) (⟨m, hm⟩ : Fin (b :: t).length)
          exact Iff.trans hih (by omega)

theorem bool_list_parity (L : List Bool) (h : L.IsChain (fun a b => a ≠ b))
    (i j : Fin L.length) : L.get i = L.get j ↔ i.val % 2 = j.val % 2 :=
  bool_list_parity_aux L h i j

end Work.ORLocInd.FKSKernel.Kurosh
