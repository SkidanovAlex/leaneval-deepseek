import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.OrderInf.ordInf_pow
import Submission.Work.Genus.OrderInf.ordInf_C_mul
import Submission.Work.Genus.OrderInf.min_ordInf_le_ordInf_add

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.OrderInf

/-- The order at infinity of the zero rational function is `0` (the convention
`RatFunc.intDegree 0 = 0`). -/
private lemma ordInf_zero {F : Type*} [Field F] : Work.Genus.ordInf (0 : RatFunc F) = 0 := by
  simp [Work.Genus.ordInf, RatFunc.intDegree_zero]

/-- The order at infinity of the constant rational function `1` is `0`. -/
private lemma ordInf_one {F : Type*} [Field F] : Work.Genus.ordInf (1 : RatFunc F) = 0 := by
  simp [Work.Genus.ordInf]

/-- **Functions without a pole at infinity are closed under addition.**  If `0 ≤ ordInf f` and
`0 ≤ ordInf g` then `0 ≤ ordInf (f + g)`.  The degenerate cases `f = 0`, `g = 0`, `f + g = 0` are
immediate (`ordInf_zero`); otherwise `min_ordInf_le_ordInf_add` bounds `ordInf (f + g)` from below
by `min (ordInf f) (ordInf g) ≥ 0`. -/
private lemma ordInf_add_nonneg {F : Type*} [Field F] {f g : RatFunc F}
    (hf : 0 ≤ Work.Genus.ordInf f) (hg : 0 ≤ Work.Genus.ordInf g) :
    0 ≤ Work.Genus.ordInf (f + g) := by
  by_cases hf0 : f = 0
  · rw [hf0, zero_add]; exact hg
  by_cases hg0 : g = 0
  · rw [hg0, add_zero]; exact hf
  by_cases hfg : f + g = 0
  · rw [hfg, ordInf_zero]
  exact le_trans (le_min hf hg) (min_ordInf_le_ordInf_add hf0 hg0 hfg)

/-- **Powers of a function without a pole at infinity have no pole at infinity.**  For `x = 0` the
power is `0` or `1` (`ordInf_zero`, `ordInf_one`); otherwise `ordInf_pow` gives
`ordInf (x ^ n) = n * ordInf x ≥ 0`. -/
private lemma ordInf_pow_nonneg {F : Type*} [Field F] {x : RatFunc F}
    (hx : 0 ≤ Work.Genus.ordInf x) (n : ℕ) :
    0 ≤ Work.Genus.ordInf (x ^ n) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rcases n with _ | k
    · simpa only [pow_zero] using (ordInf_one (F := F)).ge
    · rw [zero_pow (Nat.succ_ne_zero k), ordInf_zero]
  · rw [ordInf_pow hx0 n]
    exact mul_nonneg (Int.natCast_nonneg n) hx

/-- A constant multiple of a power of a function without a pole at infinity has no pole at
infinity: for `c = 0` the term vanishes, otherwise `ordInf_C_mul` removes the constant and
`ordInf_pow_nonneg` concludes. -/
private lemma ordInf_const_mul_pow_nonneg {F : Type*} [Field F] {x : RatFunc F}
    (hx : 0 ≤ Work.Genus.ordInf x) (c : F) (n : ℕ) :
    0 ≤ Work.Genus.ordInf (algebraMap F (RatFunc F) c * x ^ n) := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, zero_mul, ordInf_zero]
  · rw [ordInf_C_mul hc (x ^ n)]
    exact ordInf_pow_nonneg hx n

/-- If `x` has no pole at infinity then neither does `A(x)`. -/
theorem ordInf_aeval_nonneg {F : Type*} [Field F] {A : Polynomial F} {x : RatFunc F}
    (h : 0 ≤ Work.Genus.ordInf x) : 0 ≤ Work.Genus.ordInf (Polynomial.aeval x A) := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_def, Polynomial.sum_def]
  refine Finset.sum_induction (fun n => algebraMap F (RatFunc F) (A.coeff n) * x ^ n)
    (fun m => 0 ≤ Work.Genus.ordInf m) ?_ ?_ ?_
  · intro a b ha hb
    exact ordInf_add_nonneg ha hb
  · rw [ordInf_zero]
  · intro i _
    exact ordInf_const_mul_pow_nonneg h (A.coeff i) i

end Work.Genus.OrderInf
