import Mathlib

namespace Work.A7

/-- In any interval `(K, N]` of length at least `q` (i.e. `K + q ≤ N`) there is an integer
congruent to `a` modulo `q`, for every residue `a < q`.

Explicitly, `n = K + q - ((K + q - a) % q)` works: it equals `a + q * ((K + q - a) / q)`,
so it is `≡ a (mod q)`, and `0 ≤ (K + q - a) % q < q` puts it in `(K, K + q] ⊆ (K, N]`. -/
theorem fiber_exists_mod_eq (q K N a : ℕ) (hq : 0 < q) (ha : a < q) (hNK : K + q ≤ N) :
    ∃ n : ℕ, K < n ∧ n ≤ N ∧ n % q = a := by
  refine ⟨K + q - (K + q - a) % q, ?_, ?_, ?_⟩
  · -- `K < K + q - s` since `s < q`.
    have hs : (K + q - a) % q < q := Nat.mod_lt _ hq
    omega
  · -- `K + q - s ≤ K + q ≤ N`.
    exact le_trans (Nat.sub_le _ _) hNK
  · -- the residue: `K + q - s = a + q * m` with `m = (K + q - a) / q`.
    have hdm : q * ((K + q - a) / q) + (K + q - a) % q = K + q - a :=
      Nat.div_add_mod (K + q - a) q
    have key : a + q * ((K + q - a) / q) = K + q - (K + q - a) % q := by omega
    rw [← key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

end Work.A7
