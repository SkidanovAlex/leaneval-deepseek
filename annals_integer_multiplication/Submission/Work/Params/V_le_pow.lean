import Mathlib
import Submission.Work.Params.defs

namespace Work.Params

/-!
# The value bound `V ≤ W`

`KBsz` is `2 ^ (2 ^ 41) + 16`, which is far larger than any constant the program
manipulates *at runtime* but (crucially) still has `Nat.size` bounded by `n.size + 4` in the
"big `n`" regime.  The dominating quantity of the `Params` area is

`V = (KBsz + n.size + 6) · (D + 2)`  and  `W = (n.size + 1) ^ K0` with `K0 ≥ 2 ^ 44 + 100`.

The whole content is that `KBsz = 2 ^ (2 ^ 41) + 16` is absorbed by the two exponents
`2 ^ 41` (which dominates `KBsz`) and `100` (which dominates the constant factor `1731`).

Since the exponent of `KBsz` is *evaluated* by the kernel when a definition is unfolded,
we never write the number `2 ^ (2 ^ 41)` as a literal: instead we use the auxiliary
`p2 k = 2 ^ k + 16`, whose body keeps `k` a variable, so that `KBsz = p2 (2^41)` is a
definitional identity the kernel is happy to check.  All the arithmetic is then done for a
generic exponent `k`.
-/

/-- `2 ^ k + 16`, the shape of `KBsz` with the tower `2 ^ 41` kept as the argument `k`. -/
private def p2 (k : ℕ) : ℕ := 2 ^ k + 16

private lemma p2_eq (k : ℕ) : p2 k = 2 ^ k + 16 := rfl

/-- The generic value bound: `(2 ^ k + 16 + N + 6)·1731 + 1 ≤ (N+1) ^ K0` for
`N ≥ 65755586`, `k ≥ 5` and `K0 ≥ k + 100`. -/
private lemma value_bound (N k K0 : ℕ) (hN : 65755586 ≤ N) (hk : 5 ≤ k) (hK : k + 100 ≤ K0) :
    (p2 k + N + 6) * (1729 + 2) + 1 ≤ (N + 1) ^ K0 := by
  have hM2 : 2 ≤ N + 1 := by omega
  have hM1 : 1 ≤ N + 1 := by omega
  -- `2 ^ k` dominates the constant factor `1731 · (N+1)`
  have hk32 : 32 ≤ 2 ^ k := by
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hk
  have hstep1 : (p2 k + N + 6) * (1729 + 2) + 1 ≤ 2 ^ k * (1731 * (N + 1)) := by
    rw [p2_eq]
    nlinarith [hk32, hN]
  -- `2 ^ k · 1731 · (N+1) ≤ (N+1) ^ k · (N+1) ^ 100 = (N+1) ^ (k+100) ≤ (N+1) ^ K0`
  have hstep2 : 2 ^ k * (1731 * (N + 1)) ≤ (N + 1) ^ K0 := by
    have h1 : 2 ^ k ≤ (N + 1) ^ k :=
      pow_le_pow_left₀ (by norm_num : (0 : ℕ) ≤ 2) hM2 k
    have h2 : 1731 * (N + 1) ≤ (N + 1) ^ 100 := by
      have h1731 : (1731 : ℕ) ≤ (N + 1) ^ 99 := by
        calc (1731 : ℕ) ≤ N + 1 := by omega
          _ = (N + 1) ^ 1 := (pow_one _).symm
          _ ≤ (N + 1) ^ 99 := pow_le_pow_right₀ hM1 (by norm_num)
      calc 1731 * (N + 1) ≤ (N + 1) ^ 99 * (N + 1) := Nat.mul_le_mul_right _ h1731
        _ = (N + 1) ^ 100 := by rw [← pow_succ]
    calc 2 ^ k * (1731 * (N + 1)) ≤ (N + 1) ^ k * (N + 1) ^ 100 := Nat.mul_le_mul h1 h2
      _ = (N + 1) ^ (k + 100) := by rw [pow_add]
      _ ≤ (N + 1) ^ K0 := pow_le_pow_right₀ hM1 hK
  exact le_trans hstep1 hstep2

/-- The value bound `V = (KBsz + n.size + 6)·(D+2)` is dominated by `W = (n.size+1)^{K0}`. -/
theorem V_le_pow (n K0 : ℕ) (hsz : 65755586 ≤ n.size) (hK0 : 2 ^ 44 + 100 ≤ K0) :
    (Work.Params.KBsz + n.size + 6) * (HvdH.D + 2) + 1 ≤ (n.size + 1) ^ K0 := by
  have hKB : Work.Params.KBsz = p2 (2 ^ 41) := rfl
  have hD : HvdH.D = 1729 := rfl
  rw [hKB, hD]
  refine value_bound n.size (2 ^ 41) K0 hsz (by norm_num) ?_
  have hp : (2 : ℕ) ^ 41 ≤ 2 ^ 44 := by norm_num
  omega

end Work.Params
