import Mathlib
import Submission.Work.BW.totient_sq_ge
import Submission.Work.BW.isPrimitiveRoot_order_lt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- A root of unity in a number field `K` has order at most `4 [K : ℚ]²`.

Indeed, if `β` has finite order `k` then `β` is a primitive `k`-th root of unity, so
`minpoly ℚ β = cyclotomic k ℚ` has degree `Nat.totient k = [ℚ(β) : ℚ] ≤ [K : ℚ]`.
Combined with the elementary bound `k ≤ 2 · totient k²` (`Work.BW.totient_sq_ge`) this gives
`k ≤ 2 [K : ℚ]² ≤ 4 [K : ℚ]²`. -/
theorem orderOf_le_four_mul_finrank_sq {K : Type*} [Field K] [NumberField K] (β : K) (h : IsOfFinOrder β) : orderOf β ≤ 4 * (Module.finrank ℚ K) ^ 2 := by
  classical
  have hq : 0 < orderOf β := h.orderOf_pos
  -- `β` is a primitive `orderOf β`-th root of unity.
  have hprim : IsPrimitiveRoot β (orderOf β) :=
    ⟨pow_orderOf_eq_one β, fun l hl => orderOf_dvd_iff_pow_eq_one.mpr hl⟩
  -- Its minimal polynomial over `ℚ` is the cyclotomic polynomial, of degree `totient (orderOf β)`.
  have hmin : minpoly ℚ β = Polynomial.cyclotomic (orderOf β) ℚ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hprim hq).symm
  -- `totient (orderOf β) = [ℚ(β) : ℚ] ≤ [K : ℚ]`.
  have htot : Nat.totient (orderOf β) ≤ Module.finrank ℚ K := by
    rw [← Polynomial.natDegree_cyclotomic (orderOf β) ℚ, ← hmin]
    exact minpoly.natDegree_le β
  have htotR : (Nat.totient (orderOf β) : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast htot
  -- The elementary lower bound for the totient.
  have hsq : (orderOf β : ℝ) ≤ 2 * (Nat.totient (orderOf β) : ℝ) ^ 2 :=
    Work.BW.totient_sq_ge (orderOf β) hq
  have hmain : (orderOf β : ℝ) ≤ 4 * (Module.finrank ℚ K : ℝ) ^ 2 := by
    calc (orderOf β : ℝ) ≤ 2 * (Nat.totient (orderOf β) : ℝ) ^ 2 := hsq
      _ ≤ 2 * (Module.finrank ℚ K : ℝ) ^ 2 := by
          have h2 := pow_le_pow_left₀ (Nat.cast_nonneg _) htotR 2
          linarith
      _ ≤ 4 * (Module.finrank ℚ K : ℝ) ^ 2 := by
          nlinarith [sq_nonneg (Module.finrank ℚ K : ℝ)]
  have hm : ((orderOf β : ℕ) : ℝ) ≤ ((4 * (Module.finrank ℚ K) ^ 2 : ℕ) : ℝ) := by
    calc ((orderOf β : ℕ) : ℝ) ≤ 4 * ((Module.finrank ℚ K : ℕ) : ℝ) ^ 2 := hmain
      _ = ((4 * (Module.finrank ℚ K) ^ 2 : ℕ) : ℝ) := by push_cast; ring
  exact Nat.cast_le.mp hm

end Work.BW
