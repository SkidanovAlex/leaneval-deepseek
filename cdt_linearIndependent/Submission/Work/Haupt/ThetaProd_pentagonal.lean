import Mathlib
import Submission.Work.Haupt.thetaCore

/-!
# The pentagonal specialisation of the two-variable theta product

For `‖X‖ < 1`, evaluating

`ThetaProd x z = ∏'_{n ≥ 0} (1 + x^{2n+1} z) (1 + x^{2n+1}/z)`

at the nome `x = X³` and the point `z = -X` gives

`ThetaProd (X³) (-X) = ∏'_{m} (1 - X^{6m+4}) · ∏'_{m} (1 - X^{6m+2})`.

Indeed the `n`-th pair of factors becomes

`(1 + (X³)^{2n+1} · (-X)) · (1 + (X³)^{2n+1}/(-X)) = (1 - X^{6n+4}) (1 - X^{6n+2})`,

using `(X³)^{2n+1} = X^{6n+3}`, `X^{6n+3} · X = X^{6n+4}` and
`X^{6n+3}/X = X^{6n+2}` (the last one is the only place where a case distinction
`X = 0` vs `X ≠ 0` is needed).  Both families `(1 - X^{6m+4})` and `(1 - X^{6n+2})`
are multipliable because `∑ ‖X^{6m+k}‖` converges for `‖X‖ < 1`, so the infinite
product may be split.
-/

namespace Work.Haupt

open scoped BigOperators

noncomputable section

theorem ThetaProd_pentagonal (X : ℂ) (hX : ‖X‖ < 1) :
    ThetaProd (X ^ 3) (-X) =
      (∏' m : ℕ, (1 - X ^ (6 * m + 4))) * (∏' m : ℕ, (1 - X ^ (6 * m + 2))) := by
  have hX6 : ‖X ^ 6‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg X) hX (by norm_num)
  -- summability of the two exponent families
  have hsum4 : Summable (fun m : ℕ => X ^ (6 * m + 4)) :=
    ((summable_geometric_of_norm_lt_one hX6).mul_right (X ^ 4)).congr (fun m => by
      rw [← pow_mul, ← pow_add])
  have hsum2 : Summable (fun m : ℕ => X ^ (6 * m + 2)) :=
    ((summable_geometric_of_norm_lt_one hX6).mul_right (X ^ 2)).congr (fun m => by
      rw [← pow_mul, ← pow_add])
  -- hence the two products are multipliable
  have m4 : Multipliable (fun m : ℕ => 1 - X ^ (6 * m + 4)) :=
    (Complex.multipliable_one_add_of_summable hsum4.neg).congr (fun m => by
      simp only [sub_eq_add_neg])
  have m2 : Multipliable (fun m : ℕ => 1 - X ^ (6 * m + 2)) :=
    (Complex.multipliable_one_add_of_summable hsum2.neg).congr (fun m => by
      simp only [sub_eq_add_neg])
  -- the pointwise factor computation
  have hfac : ∀ n : ℕ, (1 + (X ^ 3) ^ (2 * n + 1) * (-X)) * (1 + (X ^ 3) ^ (2 * n + 1) / (-X))
      = (1 - X ^ (6 * n + 4)) * (1 - X ^ (6 * n + 2)) := by
    intro n
    have h3 : (X ^ 3) ^ (2 * n + 1) = X ^ (6 * n + 3) := by
      rw [← pow_mul]; congr 1; ring
    have h4 : X ^ (6 * n + 3) * X = X ^ (6 * n + 4) := by rw [← pow_succ]
    have h2' : X ^ (6 * n + 3) / X = X ^ (6 * n + 2) := by
      by_cases h0 : X = 0
      · subst h0
        rw [zero_pow (by omega : 6 * n + 3 ≠ 0),
          zero_pow (by omega : 6 * n + 2 ≠ 0), zero_div]
      · rw [show 6 * n + 3 = (6 * n + 2) + 1 from by ring, pow_succ,
          mul_div_cancel_right₀ _ h0]
    rw [h3, mul_neg, h4, div_neg, h2']
    ring
  rw [ThetaProd]
  rw [show (∏' n : ℕ, (1 + (X ^ 3) ^ (2 * n + 1) * (-X)) * (1 + (X ^ 3) ^ (2 * n + 1) / (-X)))
      = ∏' n : ℕ, ((1 - X ^ (6 * n + 4)) * (1 - X ^ (6 * n + 2))) from tprod_congr hfac]
  exact Multipliable.tprod_mul m4 m2

end

end Work.Haupt
