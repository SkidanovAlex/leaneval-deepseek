import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Order.ord_mul
import Submission.Work.Genus.Order.ord_pow
import Submission.Work.Genus.Order.ord_C_mul
import Submission.Work.Genus.Order.min_ord_le_ord_add

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Order

open Polynomial

/-- The order of vanishing of the zero rational function is `0` (the convention of
`Polynomial.multiplicity` on `0`, which is `0` in the `ℕ`-valued convention). -/
@[simp] lemma ord_zero {F : Type*} [Field F] (π : Polynomial F) :
    Work.Genus.ord π (0 : RatFunc F) = 0 := by
  simp [Work.Genus.ord]

/-- The order of vanishing of the constant rational function `1` is `0`. -/
@[simp] lemma ord_one {F : Type*} [Field F] (π : Polynomial F) :
    Work.Genus.ord π (1 : RatFunc F) = 0 := by
  simp [Work.Genus.ord]

/-- **The set of rational functions with no pole at a place is closed under addition.** If
`0 ≤ ord π f` and `0 ≤ ord π g` then `0 ≤ ord π (f + g)`.

Route: the trivial cases `f = 0`, `g = 0`, `f + g = 0` (`ord_zero`) are immediate; otherwise
`min_ord_le_ord_add` bounds `ord π (f + g)` from below by `min (ord π f) (ord π g) ≥ 0`. -/
theorem ord_add_nonneg {F : Type*} [Field F] {π : Polynomial F} (hπ : Irreducible π)
    {f g : RatFunc F} (hf : 0 ≤ Work.Genus.ord π f) (hg : 0 ≤ Work.Genus.ord π g) :
    0 ≤ Work.Genus.ord π (f + g) := by
  by_cases hf0 : f = 0
  · rw [hf0, zero_add]; exact hg
  by_cases hg0 : g = 0
  · rw [hg0, add_zero]; exact hf
  by_cases hfg : f + g = 0
  · rw [hfg, ord_zero]
  exact le_trans (le_min hf hg) (min_ord_le_ord_add hπ hf0 hg0 hfg)

/-- **Powers of a pole-free function are pole-free.** If `0 ≤ ord π x` then `0 ≤ ord π (x ^ n)`
for every `n`.  For `x = 0` the power is `0` or `1` (`ord_zero`, `ord_one`); otherwise `ord_pow`
gives `n * ord π x ≥ 0`. -/
theorem ord_pow_nonneg {F : Type*} [Field F] {π : Polynomial F} (hπ : Irreducible π)
    {x : RatFunc F} (hx : 0 ≤ Work.Genus.ord π x) (n : ℕ) :
    0 ≤ Work.Genus.ord π (x ^ n) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rcases n with _ | k
    · simpa only [pow_zero] using (ord_one π).ge
    · rw [zero_pow (Nat.succ_ne_zero k), ord_zero]
  · rw [ord_pow hπ hx0 n]
    exact mul_nonneg (Int.natCast_nonneg n) hx

/-- **A non-zero constant multiple of a pole-free function is pole-free.** Route: for `c = 0` the
term vanishes; otherwise `ord_C_mul` removes the constant and `ord_pow_nonneg` concludes. -/
theorem ord_const_mul_pow_nonneg {F : Type*} [Field F] {π : Polynomial F} (hπ : Irreducible π)
    {x : RatFunc F} (hx : 0 ≤ Work.Genus.ord π x) (c : F) (n : ℕ) :
    0 ≤ Work.Genus.ord π (algebraMap F (RatFunc F) c * x ^ n) := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, zero_mul, ord_zero]
  · rw [ord_C_mul hc (x ^ n)]
    exact ord_pow_nonneg hπ hx n

/-- If `x` has no pole at the place of an irreducible `π` (`0 ≤ ord π x`) then neither does
`A(x)` of any polynomial `A`.

Route: `aeval x A = ∑ i ∈ A.support, C (A.coeff i) * x ^ i`; each term has order
`i * ord π x ≥ 0` (`ord_C_mul`, `ord_pow`, `0 ≤ ord π x`), and the sum of terms of order `≥ 0` has
order `≥ 0` (`min_ord_le_ord_add` by induction, handling vanishing partial sums). -/
theorem ord_aeval_nonneg {F : Type*} [Field F] {π : Polynomial F} (hπ : Irreducible π)
    {A : Polynomial F} {x : RatFunc F} (h : 0 ≤ Work.Genus.ord π x) :
    0 ≤ Work.Genus.ord π (Polynomial.aeval x A) := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_def, Polynomial.sum_def]
  refine Finset.sum_induction (fun n => algebraMap F (RatFunc F) (A.coeff n) * x ^ n)
    (fun m => 0 ≤ Work.Genus.ord π m) ?_ ?_ ?_
  · intro a b ha hb
    exact ord_add_nonneg hπ ha hb
  · rw [ord_zero]
  · intro i _
    exact ord_const_mul_pow_nonneg hπ h (A.coeff i) i

end Work.Genus.Order
