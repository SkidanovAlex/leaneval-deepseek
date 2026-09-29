import Mathlib
import Submission.Work.Haupt.jtp_defs
import Submission.Work.Haupt.tprod_nat_split_three
import Submission.Work.Haupt.euler_pentagonal_cplx
import Submission.Work.Haupt.jtpTheta_eq_pentagonal

/-!
# The Jacobi triple product at the pentagonal point `(x, z) = (X³, -X)`

`Work.Haupt.jtp_at_pentagonal` evaluates both sides of the Jacobi triple product,

`jtpLHS x z = ∏' n, (1 - x ^ (2(n+1))) * (1 + x ^ (2n+1) z) * (1 + x ^ (2n+1) / z)`
and `jtpTheta x z = ∑' n : ℤ, x ^ (n²) z ^ n`,

at `x = X³`, `z = -X` (`‖X‖ < 1`).  There the second and third factors of the product
combine into `(1 - X ^ (6n+4)) (1 - X ^ (6n+2))` and the first is `1 - X ^ (6n+6)`, so the
product runs over the exponents `6n+2, 6n+4, 6n+6`, `n ≥ 0`, i.e. over all even exponents
`2m`, `m ≥ 1`:

`jtpLHS (X³) (-X) = ∏' n, (1 - X ^ (2(n+1)))`.

The theta series becomes `∑' n : ℤ, (-1)ⁿ X ^ (3n²+n)`; splitting the two-sided sum into
`n ≥ 0` and `n < 0` gives Euler's pentagonal number expansion of the same product,

`∑' k, (-1)^k (X ^ (3k²+k) - X ^ (3k²+5k+2)) = ∏' n, (1 - X ^ (2(n+1)))`

(the case `q = X²` of `Pentagonal.tprod_one_sub_pow`), so `jtpTheta (X³) (-X)` is the same
product.

The proof combines three independent pieces:
* `jtpTheta_eq_pentagonal` — the `ℤ`-sum against the pentagonal series,
* `euler_pentagonal_cplx` — the product `∏' (1 - q^(n+1))` against the pentagonal series
  (used here through the specialisation `pent_series_bridge` at `q = X²`),
* `tprod_nat_split_three` — the splitting of a product over `ℕ` into residue classes mod `3`
  (used here through the specialisation `pent_triple`).
-/

namespace Work.Haupt

open scoped BigOperators

noncomputable section

/-! ## Summability and multipliability of elementary geometric families -/

/-- `∑_n X ^ (a n + b)` converges absolutely for `‖X‖ < 1` and `1 ≤ a`. -/
lemma summable_pow_mul_add (X : ℂ) (hX : ‖X‖ < 1) (a b : ℕ) (ha : 1 ≤ a) :
    Summable (fun n : ℕ => X ^ (a * n + b)) := by
  have h : ‖X ^ a‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg X) hX (by omega : a ≠ 0)
  have h1 : Summable (fun n : ℕ => (X ^ a) ^ n) := summable_geometric_of_norm_lt_one h
  refine (h1.mul_left (X ^ b)).congr (fun n => ?_)
  rw [← pow_mul, ← pow_add]
  rw [Nat.add_comm]

/-- `∏_n (1 - X ^ (a n + b))` converges for `‖X‖ < 1` and `1 ≤ a`. -/
lemma multipliable_one_sub_pow (X : ℂ) (hX : ‖X‖ < 1) (a b : ℕ) (ha : 1 ≤ a) :
    Multipliable (fun n : ℕ => 1 - X ^ (a * n + b)) := by
  have hs : Summable (fun n : ℕ => X ^ (a * n + b)) := summable_pow_mul_add X hX a b ha
  exact (Complex.multipliable_one_add_of_summable hs.neg).congr (fun n => by simp [sub_eq_add_neg])

/-! ## The product side at `(X³, -X)` -/

/-- Unfolding `jtpLHS` at `x = X³`, `z = -X`. -/
lemma jtpLHS_pent_expand (X : ℂ) :
    jtpLHS (X ^ 3) (-X)
      = ∏' n : ℕ, (1 - X ^ (6 * (n + 1))) * (1 - X ^ (6 * n + 4)) * (1 - X ^ (6 * n + 2)) := by
  rw [jtpLHS]
  refine tprod_congr (fun n => ?_)
  have h1 : (X ^ 3) ^ (2 * (n + 1)) = X ^ (6 * (n + 1)) := by
    rw [← pow_mul, show 3 * (2 * (n + 1)) = 6 * (n + 1) by ring]
  have h3 : (X ^ 3) ^ (2 * n + 1) = X ^ (6 * n + 3) := by
    rw [← pow_mul, show 3 * (2 * n + 1) = 6 * n + 3 by ring]
  have hB : (X ^ 3) ^ (2 * n + 1) * (-X) = -X ^ (6 * n + 4) := by
    rw [h3, mul_neg, ← pow_succ, show 6 * n + 3 + 1 = 6 * n + 4 by ring]
  have hC : (X ^ 3) ^ (2 * n + 1) / (-X) = -X ^ (6 * n + 2) := by
    rcases eq_or_ne X 0 with hX0 | hX0
    · subst hX0
      rw [show (0 : ℂ) ^ 3 = 0 by norm_num, zero_pow (by omega : 2 * n + 1 ≠ 0), zero_div,
        zero_pow (by omega : 6 * n + 2 ≠ 0), neg_zero]
    · rw [h3, div_eq_iff (neg_ne_zero.mpr hX0), mul_neg, neg_mul, neg_neg, ← pow_succ,
        show 6 * n + 2 + 1 = 6 * n + 3 by ring]
  rw [h1, hB, hC]
  ring

/-- The product `∏' n, (1 - X ^ (2(n+1)))` equals the pentagonal series in the variable `X`. -/
lemma pent_series_bridge (X : ℂ) (hX : ‖X‖ < 1) :
    ∏' n : ℕ, (1 - X ^ (2 * (n + 1)))
      = ∑' k : ℕ, (-1) ^ k * (X ^ (3 * k ^ 2 + k) - X ^ (3 * k ^ 2 + 5 * k + 2)) := by
  have hX2 : ‖X ^ 2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg X) hX (by norm_num)
  have hL : (∏' n : ℕ, (1 - X ^ (2 * (n + 1)))) = ∏' n : ℕ, (1 - (X ^ 2) ^ (n + 1)) := by
    refine tprod_congr (fun n => ?_)
    rw [pow_mul]
  have hR : (∑' k : ℕ,
        (-1) ^ k * ((X ^ 2) ^ pentagonal (-(k : ℤ)) - (X ^ 2) ^ pentagonal ((k : ℤ) + 1)))
      = ∑' k : ℕ, (-1) ^ k * (X ^ (3 * k ^ 2 + k) - X ^ (3 * k ^ 2 + 5 * k + 2)) := by
    refine tsum_congr (fun k => ?_)
    have hA : 2 * pentagonal (-(k : ℤ)) = 3 * k ^ 2 + k := by
      have h2 : ((2 * pentagonal (-(k : ℤ)) : ℕ) : ℤ) = ((3 * k ^ 2 + k : ℕ) : ℤ) := by
        push_cast
        rw [two_mul_natCast_pentagonal_neg]
        ring
      exact_mod_cast h2
    have hB : 2 * pentagonal ((k : ℤ) + 1) = 3 * k ^ 2 + 5 * k + 2 := by
      have h2 : ((2 * pentagonal ((k : ℤ) + 1) : ℕ) : ℤ) = ((3 * k ^ 2 + 5 * k + 2 : ℕ) : ℤ) := by
        push_cast
        rw [two_mul_natCast_pentagonal]
        ring
      exact_mod_cast h2
    rw [← pow_mul, hA, ← pow_mul, hB]
  rw [hL, euler_pentagonal_cplx (X ^ 2) hX2, hR]

/-- Splitting `∏' n, (1 - X ^ (2(n+1)))` into the residue classes `2, 4, 6` mod `6`. -/
lemma pent_triple (X : ℂ) (hX : ‖X‖ < 1) :
    (∏' k : ℕ, (1 - X ^ (6 * k + 2))) * (∏' k : ℕ, (1 - X ^ (6 * k + 4))) *
      (∏' k : ℕ, (1 - X ^ (6 * k + 6))) = ∏' k : ℕ, (1 - X ^ (2 * (k + 1))) := by
  have h0 : Multipliable (fun k : ℕ => (fun n : ℕ => 1 - X ^ (2 * (n + 1))) (3 * k)) :=
    (multipliable_one_sub_pow X hX 6 2 (by norm_num)).congr (fun k => by
      show 1 - X ^ (6 * k + 2) = 1 - X ^ (2 * (3 * k + 1))
      rw [show 2 * (3 * k + 1) = 6 * k + 2 by ring])
  have h1 : Multipliable (fun k : ℕ => (fun n : ℕ => 1 - X ^ (2 * (n + 1))) (3 * k + 1)) :=
    (multipliable_one_sub_pow X hX 6 4 (by norm_num)).congr (fun k => by
      show 1 - X ^ (6 * k + 4) = 1 - X ^ (2 * (3 * k + 1 + 1))
      rw [show 2 * (3 * k + 1 + 1) = 6 * k + 4 by ring])
  have h2 : Multipliable (fun k : ℕ => (fun n : ℕ => 1 - X ^ (2 * (n + 1))) (3 * k + 2)) :=
    (multipliable_one_sub_pow X hX 6 6 (by norm_num)).congr (fun k => by
      show 1 - X ^ (6 * k + 6) = 1 - X ^ (2 * (3 * k + 2 + 1))
      rw [show 2 * (3 * k + 2 + 1) = 6 * k + 6 by ring])
  have h := tprod_nat_split_three (f := fun n : ℕ => 1 - X ^ (2 * (n + 1))) h0 h1 h2
  have e0 : (∏' k : ℕ, (fun n : ℕ => 1 - X ^ (2 * (n + 1))) (3 * k))
      = ∏' k : ℕ, (1 - X ^ (6 * k + 2)) := by
    refine tprod_congr (fun k => ?_)
    show 1 - X ^ (2 * (3 * k + 1)) = 1 - X ^ (6 * k + 2)
    rw [show 2 * (3 * k + 1) = 6 * k + 2 by ring]
  have e1 : (∏' k : ℕ, (fun n : ℕ => 1 - X ^ (2 * (n + 1))) (3 * k + 1))
      = ∏' k : ℕ, (1 - X ^ (6 * k + 4)) := by
    refine tprod_congr (fun k => ?_)
    show 1 - X ^ (2 * (3 * k + 1 + 1)) = 1 - X ^ (6 * k + 4)
    rw [show 2 * (3 * k + 1 + 1) = 6 * k + 4 by ring]
  have e2 : (∏' k : ℕ, (fun n : ℕ => 1 - X ^ (2 * (n + 1))) (3 * k + 2))
      = ∏' k : ℕ, (1 - X ^ (6 * k + 6)) := by
    refine tprod_congr (fun k => ?_)
    show 1 - X ^ (2 * (3 * k + 2 + 1)) = 1 - X ^ (6 * k + 6)
    rw [show 2 * (3 * k + 2 + 1) = 6 * k + 6 by ring]
  rw [e0, e1, e2] at h
  exact h

theorem jtp_at_pentagonal (X : ℂ) (hX : ‖X‖ < 1) :
    jtpLHS (X ^ 3) (-X) = ∏' n : ℕ, (1 - X ^ (2 * (n + 1))) ∧
    jtpTheta (X ^ 3) (-X) = ∏' n : ℕ, (1 - X ^ (2 * (n + 1))) := by
  have hA : Multipliable (fun n : ℕ => 1 - X ^ (6 * n + 6)) :=
    multipliable_one_sub_pow X hX 6 6 (by norm_num)
  have hB : Multipliable (fun n : ℕ => 1 - X ^ (6 * n + 4)) :=
    multipliable_one_sub_pow X hX 6 4 (by norm_num)
  have hC : Multipliable (fun n : ℕ => 1 - X ^ (6 * n + 2)) :=
    multipliable_one_sub_pow X hX 6 2 (by norm_num)
  have hsplit : (∏' n : ℕ,
        (1 - X ^ (6 * (n + 1))) * (1 - X ^ (6 * n + 4)) * (1 - X ^ (6 * n + 2)))
      = (∏' n : ℕ, (1 - X ^ (6 * n + 6))) * (∏' n : ℕ, (1 - X ^ (6 * n + 4))) *
          (∏' n : ℕ, (1 - X ^ (6 * n + 2))) := by
    have e : (fun n : ℕ =>
          (1 - X ^ (6 * (n + 1))) * (1 - X ^ (6 * n + 4)) * (1 - X ^ (6 * n + 2)))
        = (fun n : ℕ =>
          (1 - X ^ (6 * n + 6)) * (1 - X ^ (6 * n + 4)) * (1 - X ^ (6 * n + 2))) := by
      funext n; rw [show 6 * (n + 1) = 6 * n + 6 by ring]
    rw [e, Multipliable.tprod_mul (hA.mul hB) hC, Multipliable.tprod_mul hA hB]
  have hprod : (∏' n : ℕ,
        (1 - X ^ (6 * (n + 1))) * (1 - X ^ (6 * n + 4)) * (1 - X ^ (6 * n + 2)))
      = ∏' n : ℕ, (1 - X ^ (2 * (n + 1))) := by
    rw [hsplit, ← pent_triple X hX]
    ring
  refine ⟨?_, ?_⟩
  · rw [jtpLHS_pent_expand X]
    exact hprod
  · rw [jtpTheta_eq_pentagonal X hX, ← pent_series_bridge X hX]

end

end Work.Haupt
