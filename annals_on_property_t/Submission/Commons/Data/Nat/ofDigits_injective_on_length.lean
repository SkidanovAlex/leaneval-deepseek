import Mathlib.Data.Nat.Digits.Defs

namespace Commons.Data.Nat

/-- `Nat.ofDigits B` is injective on digit lists of equal length whose entries are all `< B`. -/
theorem ofDigits_injective_on_length {B : ℕ} (hB : 2 ≤ B) :
    ∀ {u v : List ℕ}, u.length = v.length →
      (∀ x ∈ u, x < B) → (∀ x ∈ v, x < B) →
      Nat.ofDigits B u = Nat.ofDigits B v → u = v := by
  have hBpos : 0 < B := by omega
  intro u
  induction u with
  | nil =>
    intro v hlen _ _ _
    cases v with
    | nil => rfl
    | cons b s => simp at hlen
  | cons a t ih =>
    intro v hlen hdu hdv heq
    cases v with
    | nil => simp at hlen
    | cons b s =>
      have hlen' : t.length = s.length := by simpa using hlen
      rw [Nat.ofDigits_cons, Nat.ofDigits_cons] at heq
      have ha : a < B := hdu a (by simp)
      have hb : b < B := hdv b (by simp)
      have hab : a = b := by
        have h1 : (a + B * Nat.ofDigits B t) % B = a := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
        have h2 : (b + B * Nat.ofDigits B s) % B = b := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
        rw [heq] at h1
        exact h1.symm.trans h2
      have hts : t = s :=
        ih hlen' (fun x hx => hdu x (List.mem_cons_of_mem a hx))
          (fun x hx => hdv x (List.mem_cons_of_mem b hx)) (by
            have hmul : B * Nat.ofDigits B t = B * Nat.ofDigits B s := by
              have h := heq
              rw [hab] at h
              exact Nat.add_left_cancel h
            exact Nat.mul_left_cancel hBpos hmul)
      rw [hab, hts]

end Commons.Data.Nat