import Mathlib.Data.Nat.Totient
open scoped Nat
open Finset

/-!
# Totient counting lemmas
-/

namespace Submission.DS

/-- The number of `1 ≤ x ≤ q` coprime to `q` equals `φ q`. -/
lemma card_coprime_Icc_one (q : ℕ) : #{x ∈ Finset.Icc 1 q | q.Coprime x} = φ q := by
  have hset : Finset.Icc 1 q = Finset.Ico 1 (1 + q) := by
    ext x
    simp [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hset]
  exact Nat.filter_coprime_Ico_eq_totient q 1

/-- `φ q > 0` for positive `q`. -/
lemma totient_pos_pnat (q : ℕ+) : 0 < φ q := by
  exact (Nat.totient_pos).mpr (by exact_mod_cast q.2 : 0 < (q : ℕ))

/-- The number of `0 ≤ x ≤ q` coprime to `q` is at most `φ q + 1`. -/
lemma card_coprime_Icc_zero_le (q : ℕ) : #{x ∈ Finset.Icc 0 q | q.Coprime x} ≤ φ q + 1 := by
  by_cases hq : q = 0
  · subst q
    decide
  · have hsub : Finset.filter (fun x : ℕ => q.Coprime x) (Finset.Icc 0 q) ⊆
        insert 0 (Finset.filter (fun x : ℕ => q.Coprime x) (Finset.Icc 1 q)) := by
      intro x hx
      have hx0 : x ∈ Finset.Icc 0 q := (Finset.mem_filter.mp hx).1
      have hpx : q.Coprime x := (Finset.mem_filter.mp hx).2
      by_cases hz : x = 0
      · simp [hz]
      · have hx1 : x ∈ Finset.Icc 1 q := by
          exact Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hx0).2⟩
        exact (Finset.mem_insert).2 (Or.inr (Finset.mem_filter.mpr ⟨hx1, hpx⟩))
    calc
      (Finset.filter (fun x : ℕ => q.Coprime x) (Finset.Icc 0 q)).card ≤
          (insert 0 (Finset.filter (fun x : ℕ => q.Coprime x) (Finset.Icc 1 q))).card :=
        Finset.card_le_card hsub
      _ ≤ (Finset.filter (fun x : ℕ => q.Coprime x) (Finset.Icc 1 q)).card + 1 := by
        simpa using (Finset.card_insert_le 0 (Finset.filter (fun x : ℕ => q.Coprime x) (Finset.Icc 1 q)))
      _ = φ q + 1 := by rw [card_coprime_Icc_one]

end Submission.DS
