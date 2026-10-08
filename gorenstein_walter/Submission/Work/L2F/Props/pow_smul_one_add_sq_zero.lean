import Mathlib

namespace Work.L2F.Props

/-- If `W * W = 0` then `(lam • 1 + W)^m = lam^m • 1 + (m * lam^(m-1)) • W`.

This is the "freshman's dream" for a square-zero perturbation of the identity:
the binomial expansion of `(lam • 1 + W)^m` truncates after the first two terms
because all powers `W^k` with `k ≥ 2` vanish.  We prove the identity for *all*
natural numbers `n` (the `n = 0` case is trivial as well) by induction; the
requested hypothesis `hm : m ≠ 0` is therefore not needed, but is kept in the
statement. -/
theorem pow_smul_one_add_sq_zero (F : Type*) [Field F]
    (lam : F) (W : Matrix (Fin 2) (Fin 2) F) (hW : W * W = 0) (m : ℕ) (hm : m ≠ 0) :
    (lam • (1 : Matrix (Fin 2) (Fin 2) F) + W) ^ m =
      lam ^ m • (1 : Matrix (Fin 2) (Fin 2) F) + ((m : F) * lam ^ (m - 1)) • W := by
  have _hm := hm
  have key : ∀ n : ℕ, (lam • (1 : Matrix (Fin 2) (Fin 2) F) + W) ^ n =
      lam ^ n • (1 : Matrix (Fin 2) (Fin 2) F) + ((n : F) * lam ^ (n - 1)) • W := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, mul_add, add_mul, add_mul]
      simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, hW, smul_zero, add_zero]
      rw [smul_smul, smul_smul, ← pow_succ', add_assoc, ← add_smul]
      congr 1
      rw [Nat.add_sub_cancel]
      have h2 : lam * ((k : F) * lam ^ (k - 1)) = (k : F) * lam ^ k := by
        rcases k with _ | j
        · simp
        · rw [Nat.add_sub_cancel, pow_succ']; ring
      rw [h2, Nat.cast_succ]
      ring_nf
  exact key m

end Work.L2F.Props
