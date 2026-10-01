import Mathlib

namespace Commons.Combinatorics.Counting

/-- The number of multisets of size `k` over `n` elements is at most the number of functions from
a `k`-element set to an `n`-element set: `multichoose n k ≤ n ^ k`. -/
theorem multichoose_le_pow (n k : ℕ) : n.multichoose k ≤ n ^ k := by
  induction n generalizing k with
  | zero =>
    rcases k with _ | k
    · simp [Nat.multichoose_zero_right]
    · simp [Nat.multichoose_zero_succ]
  | succ n ih =>
    induction k with
    | zero => simp [Nat.multichoose_zero_right]
    | succ k ihk =>
      rw [Nat.multichoose_succ_succ]
      have h1 : n ^ (k + 1) ≤ (n + 1) ^ k * n := by
        rw [pow_succ]
        exact Nat.mul_le_mul_right n (Nat.pow_le_pow_left (Nat.le_succ n) k)
      calc n.multichoose (k + 1) + (n + 1).multichoose k
          ≤ n ^ (k + 1) + (n + 1) ^ k := add_le_add (ih (k + 1)) ihk
        _ ≤ (n + 1) ^ k * n + (n + 1) ^ k := add_le_add h1 le_rfl
        _ = (n + 1) ^ (k + 1) := by rw [pow_succ]; ring

theorem card_fin_fun_sum_le (n A : ℕ) :
    Fintype.card {f : Fin n → Fin (A + 1) // ∑ i, (f i : ℕ) = A} ≤ n ^ A := by
  classical
  have inj : Function.Injective
      (fun f : {f : Fin n → Fin (A + 1) // ∑ i, (f i : ℕ) = A} =>
        (Sym.equivNatSumOfFintype (Fin n) A).symm
          ⟨fun i => (f.1 i : ℕ), f.2⟩) := by
    intro f g h
    have h2 := (Sym.equivNatSumOfFintype (Fin n) A).symm.injective h
    have h3 : (fun i => (f.1 i : ℕ)) = (fun i => (g.1 i : ℕ)) :=
      congrArg (fun x : {P : Fin n → ℕ // ∑ i, P i = A} => (x : Fin n → ℕ)) h2
    apply Subtype.ext
    funext i
    exact Fin.ext (congrFun h3 i)
  calc Fintype.card {f : Fin n → Fin (A + 1) // ∑ i, (f i : ℕ) = A}
      ≤ Fintype.card (Sym (Fin n) A) := Fintype.card_le_of_injective _ inj
    _ = n.multichoose A := Sym.card_sym_fin_eq_multichoose n A
    _ ≤ n ^ A := multichoose_le_pow n A

end Commons.Combinatorics.Counting
