import Submission.ZagierHoffmanProof.AntidiagonalSum
import Submission.ZagierHoffmanProof.CoeffNu

/-!
# The two-term coefficient collapse (`coeffNu_mul_two_terms`)

If `B` is a `θ`-two-term element of `A_0` (its only `θ`-components sit at `0` and `q` — e.g.
`W = X - C(θ^q)` and `L^q = X^q - C(θ^q)`) and `A` is `qℤ`-supported, then the `θ^(q·m)`-coefficient of
`B * A` is a **two-term combination**, one term per `θ`-monomial of `B`:

  `coeffNu 0 (q·m) (B * A) = coeffNu 0 0 B · coeffNu 0 (q·m) A
                            + coeffNu 0 q B · coeffNu 0 (q·(m-1)) A`.

This is the lemma that kills the convolution in every row of the `k = q-1` two-term endgame
(`Submission/PLAN.md` §«SESSION 354» §«continued 31»–§«continued 37»): the antidiagonal sum of
`coeffNu_mul` has two surviving indices, `0` and `q`, and this says their contributions are exactly the
two terms above.

⚠ Two hard-won proof details: the target must be read in the **`range`** form
(`sum_hasAntidiagonal_eq_sum_range`), because `rcases` cannot case-split a `Finset`-literal membership;
and the lemma carries **`1 ≤ m`**, without which `q * (m - 1)` silently becomes `q * 0` in `ℕ` and the
statement is false at `m = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Polynomial

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

lemma coeffNu_mul_two_terms {A B : Ambient F} (hA : A ∈ ambA F 0) (hB : B ∈ ambA F 0)
    (hAsupp : ∀ m, ¬ Nat.card F ∣ m → coeffNu F 0 m A = 0)
    (hBsupp : ∀ m, m ≠ 0 → m ≠ Nat.card F → coeffNu F 0 m B = 0)
    {m : ℕ} (hm : 1 ≤ m) :
    coeffNu F 0 (Nat.card F * m) (B * A)
      = coeffNu F 0 0 B * coeffNu F 0 (Nat.card F * m) A
        + coeffNu F 0 (Nat.card F) B * coeffNu F 0 (Nat.card F * (m - 1)) A := by
  have hq0 : 0 < Nat.card F := Nat.pos_of_ne_zero (FrobPow.ne_zero (Ambient F) (q := Nat.card F))
  have hidx : Nat.card F * m - Nat.card F = Nat.card F * (m - 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [coeffNu_mul F hB hA (Nat.card F * m)]
  rw [show (∑ i ∈ Finset.HasAntidiagonal.antidiagonal (Nat.card F * m),
        coeffNu F 0 i.1 B * coeffNu F 0 i.2 A)
      = ∑ k ∈ Finset.range (Nat.card F * m + 1),
        coeffNu F 0 k B * coeffNu F 0 (Nat.card F * m - k) A
      from sum_hasAntidiagonal_eq_sum_range (Nat.card F * m)
        (fun x y => coeffNu F 0 x B * coeffNu F 0 y A)]
  refine (Finset.sum_subset (s₁ := ({0, Nat.card F} : Finset ℕ)) ?_ ?_).symm.trans ?_
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact Finset.mem_range.mpr (by simp)
    · exact Finset.mem_range.mpr (by nlinarith)
  · intro k hk hks
    simp only [Finset.mem_insert, Finset.mem_singleton] at hks
    push_neg at hks
    rw [hBsupp k hks.1 hks.2, zero_mul]
  · rw [Finset.sum_insert (by simp only [Finset.mem_singleton]; omega), Finset.sum_singleton]
    simp only [Nat.sub_zero]
    rw [hidx]

end ZagierHoffmanPositiveChar
