import Mathlib

namespace Work.ZeroDensity.Ingham

/-!
# Reducing the symmetric double sum in `divPairKernelBound` to the upper triangle

`divPairKernelBound` needs the elementary reduction

`∑_{m,n ≤ N} d(m) d(n) max(m,n) / (√(mn) |m-n|)`
`  ≤ 2 ∑_{m ≤ N} ∑_{m<n ≤ N} (d(m)/√m) (d(n)/√n) (n/(n-m))`,

where `d(k) = (Nat.divisors k).card` is the divisor function.  In fact the two
sides are *equal*: the diagonal terms `m = n` of the left-hand side vanish
(they are divisions by `0`), and every off-diagonal unordered pair `{m,n}`
contributes exactly twice on each side.  The proof below is purely
combinatorial:

* `doubleSum_alg` — the algebraic identity
  `A B y / (√(xy)|x-y|) = (A/√x)(B/√y) y/(y-x)` valid for `0 ≤ x < y`;
* `doubleSumF_comm` — the summand is symmetric in `(m,n)`;
* `doubleSumF_eq` — hence it decomposes over the two triangles;
* `sum_ite_lt_swap` / `Icc_filter_lt` — Finset bookkeeping converting the
  triangular indices into `Finset.Icc (m+1) N`.
-/

/-- The `(m,n)`-summand of the symmetric double sum.  Note that it is defined
by total division, so the diagonal terms `m = n` are `0`. -/
noncomputable def doubleSumF (m n : ℕ) : ℝ :=
  ((Nat.divisors m).card : ℝ) * ((Nat.divisors n).card : ℝ) * max (m : ℝ) (n : ℝ)
    / (Real.sqrt ((m : ℝ) * (n : ℝ)) * |(m : ℝ) - (n : ℝ)|)

/-- The `(m,n)`-summand of the upper-triangular sum. -/
noncomputable def doubleSumG (m n : ℕ) : ℝ :=
  (((Nat.divisors m).card : ℝ) / Real.sqrt (m : ℝ))
    * (((Nat.divisors n).card : ℝ) / Real.sqrt (n : ℝ))
    * ((n : ℝ) / ((n : ℝ) - (m : ℝ)))

/-- Elementary algebra: for `0 ≤ x < y`,
`A B y / (√(xy) |x-y|) = (A/√x)(B/√y) y/(y-x)`.  The case `x = 0` is
degenerate: both sides vanish because of total division. -/
lemma doubleSum_alg (A B x y : ℝ) (hx : 0 ≤ x) (hxy : x < y) :
    A * B * y / (Real.sqrt (x * y) * |x - y|)
      = (A / Real.sqrt x) * (B / Real.sqrt y) * (y / (y - x)) := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h; simp
  · have habs : |x - y| = y - x := by rw [abs_of_neg (by linarith)]; ring
    have hsqrt : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y :=
      Real.sqrt_mul (le_of_lt h) y
    rw [habs, hsqrt]
    have hx0 : Real.sqrt x ≠ 0 := by rw [Real.sqrt_ne_zero']; exact h
    have hy0 : Real.sqrt y ≠ 0 := by rw [Real.sqrt_ne_zero']; linarith
    have hxy0 : y - x ≠ 0 := by linarith
    field_simp

/-- `doubleSumF` is symmetric in its two arguments. -/
lemma doubleSumF_comm (m n : ℕ) : doubleSumF m n = doubleSumF n m := by
  have h1 : Real.sqrt ((m : ℝ) * (n : ℝ)) = Real.sqrt ((n : ℝ) * (m : ℝ)) := by
    rw [mul_comm]
  have h2 : max (m : ℝ) (n : ℝ) = max (n : ℝ) (m : ℝ) := max_comm _ _
  have h3 : |(m : ℝ) - (n : ℝ)| = |(n : ℝ) - (m : ℝ)| := abs_sub_comm _ _
  simp only [doubleSumF, h1, h2, h3]
  ring

/-- Pointwise decomposition of the summand into the two triangles.  The
diagonal contributes `0` on both sides. -/
lemma doubleSumF_eq (m n : ℕ) :
    doubleSumF m n
      = (if m < n then doubleSumG m n else 0)
        + (if n < m then doubleSumG n m else 0) := by
  rcases lt_trichotomy m n with hmn | heq | hnm
  · have hR : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
    have hmax : max (m : ℝ) (n : ℝ) = (n : ℝ) := max_eq_right (le_of_lt hR)
    have key := doubleSum_alg ((Nat.divisors m).card : ℝ) ((Nat.divisors n).card : ℝ)
        (m : ℝ) (n : ℝ) (by positivity) hR
    have hL : doubleSumF m n = doubleSumG m n := by
      simpa only [doubleSumF, doubleSumG, hmax] using key
    rw [hL, if_pos hmn, if_neg (by omega : ¬ n < m), add_zero]
  · subst heq; simp [doubleSumF]
  · have hR : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
    have hmax : max (n : ℝ) (m : ℝ) = (m : ℝ) := max_eq_right (le_of_lt hR)
    have key := doubleSum_alg ((Nat.divisors n).card : ℝ) ((Nat.divisors m).card : ℝ)
        (n : ℝ) (m : ℝ) (by positivity) hR
    have hL : doubleSumF n m = doubleSumG n m := by
      simpa only [doubleSumF, doubleSumG, hmax] using key
    rw [doubleSumF_comm m n, hL, if_neg (by omega : ¬ m < n), if_pos hnm, zero_add]

/-- Swapping the two summations turns the lower triangle into the upper
triangle. -/
lemma sum_ite_lt_swap (s : Finset ℕ) (H : ℕ → ℕ → ℝ) :
    (∑ m ∈ s, ∑ n ∈ s, (if n < m then H n m else 0))
      = (∑ m ∈ s, ∑ n ∈ s, (if m < n then H m n else 0)) := by
  rw [Finset.sum_comm]

/-- Restricting `Finset.Icc a b` to the `n` with `m < n` gives `Icc (max a (m+1)) b`. -/
lemma Icc_filter_lt (a b m : ℕ) :
    (Finset.Icc a b).filter (fun n => m < n) = Finset.Icc (max a (m + 1)) b := by
  ext n; simp only [Finset.mem_filter, Finset.mem_Icc]; omega

theorem doubleSumUpperReduce (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        ((Nat.divisors m).card : ℝ) * ((Nat.divisors n).card : ℝ) * max (m:ℝ) (n:ℝ)
          / (Real.sqrt ((m:ℝ)*(n:ℝ)) * |(m:ℝ)-(n:ℝ)|))
      ≤ 2 * ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc (m+1) N,
          (((Nat.divisors m).card : ℝ)/Real.sqrt (m:ℝ)) * (((Nat.divisors n).card : ℝ)/Real.sqrt (n:ℝ))
            * ((n:ℝ)/((n:ℝ)-(m:ℝ))) := by
  -- Rewrite the inner sum over the strict upper triangle as `Icc (m+1) N`.
  have hstep : ∀ m : ℕ, (∑ n ∈ Finset.Icc 1 N, (if m < n then doubleSumG m n else 0))
      = ∑ n ∈ Finset.Icc (m+1) N, doubleSumG m n := by
    intro m
    have h1 := Finset.sum_filter (s := Finset.Icc 1 N) (p := fun n => m < n)
      (f := fun n => doubleSumG m n)
    have h2 : (Finset.Icc 1 N).filter (fun n => m < n) = Finset.Icc (m+1) N := by
      rw [Icc_filter_lt, max_eq_right (by omega : 1 ≤ m + 1)]
    rw [← h1, h2]
  have hA : (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (if m < n then doubleSumG m n else 0))
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc (m+1) N, doubleSumG m n := by
    apply Finset.sum_congr rfl
    intro m _
    exact hstep m
  have hB : (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (if n < m then doubleSumG n m else 0))
      = (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (if m < n then doubleSumG m n else 0)) :=
    sum_ite_lt_swap (Finset.Icc 1 N) doubleSumG
  -- The two sides are in fact equal.
  have key : (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, doubleSumF m n)
      = 2 * (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc (m+1) N, doubleSumG m n) := by
    calc ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, doubleSumF m n
        = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            ((if m < n then doubleSumG m n else 0)
              + (if n < m then doubleSumG n m else 0)) := by
          apply Finset.sum_congr rfl; intro m _
          apply Finset.sum_congr rfl; intro n _
          exact doubleSumF_eq m n
      _ = (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
              (if m < n then doubleSumG m n else 0))
          + (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
              (if n < m then doubleSumG n m else 0)) := by
          simp only [Finset.sum_add_distrib]
      _ = (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
              (if m < n then doubleSumG m n else 0))
          + (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
              (if m < n then doubleSumG m n else 0)) := by
          rw [hB]
      _ = 2 * (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc (m+1) N, doubleSumG m n) := by
          rw [hA]; ring
  exact le_of_eq key

end Work.ZeroDensity.Ingham
