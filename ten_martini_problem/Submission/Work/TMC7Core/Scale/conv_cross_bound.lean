import Mathlib

/-!
# Cross bound for continued-fraction convergents

For a real number `v` whose (regular) continued fraction expansion never terminates, any two
convergents are at distance at most the first step of the telescoping chain starting at the
lower index:

  `|convs k - convs i| ≤ 1 / (dens i * dens (i+1))`   for `i < k`.

The proof has three ingredients.

* `dens_pos_of_nonterminating` : all denominators are positive (they dominate Fibonacci numbers).
* `convs_succ_sub_convs_aux` : consecutive convergents are exactly
  `(-1)^n / (dens n * dens (n+1))` apart (the determinant identity of a continued fraction).
* `abs_sum_range_alt` : the classical finite alternating-series estimate -- an alternating sum of a
  nonnegative antitone sequence is bounded, in absolute value, by its first term (Leibniz).

Telescoping `convs k - convs i` over the consecutive gaps produces an alternating sum whose terms
`1 / (dens j * dens (j+1))` are positive and antitone (denominators are monotone), so the Leibniz
estimate applies with first term `1 / (dens i * dens (i+1))`.
-/

namespace Work.TMC7Core.Scale

open GenContFract

/-- Every denominator of the continued fraction of a real with non-terminating expansion is
positive (in fact at least `1`), since it dominates a Fibonacci number. -/
theorem dens_pos_of_nonterminating (v : ℝ)
    (hv : ∀ n, ¬ (GenContFract.of v).TerminatedAt n) :
    ∀ n, 0 < (GenContFract.of v).dens n := by
  intro n
  have h := GenContFract.succ_nth_fib_le_of_nth_den (v := v) (n := n) (Or.inr (hv (n - 1)))
  have h1 : (1 : ℝ) ≤ (Nat.fib (n + 1) : ℝ) := by
    exact_mod_cast (show (1 : ℕ) ≤ Nat.fib (n + 1) from
      Nat.succ_le_of_lt (Nat.fib_pos.mpr (Nat.succ_pos n)))
  linarith

/-- Finite Leibniz estimate: for a nonnegative antitone `g`, every alternating partial sum is
bounded in absolute value by the first term `g 0`. -/
theorem abs_sum_range_alt (g : ℕ → ℝ) (hanti : Antitone g) (hnn : ∀ n, 0 ≤ g n) :
    ∀ m : ℕ, |∑ j ∈ Finset.range m, (-1 : ℝ) ^ j * g j| ≤ g 0 := by
  -- the odd partial sum is the preceding even one plus the fresh positive term
  have hO_eq : ∀ k : ℕ, (∑ j ∈ Finset.range (2 * k + 1), (-1 : ℝ) ^ j * g j)
      = (∑ j ∈ Finset.range (2 * k), (-1 : ℝ) ^ j * g j) + g (2 * k) := by
    intro k
    have h := Finset.sum_range_succ (f := fun j => (-1 : ℝ) ^ j * g j) (n := 2 * k)
    rw [h, Even.neg_one_pow (show Even (2 * k) from ⟨k, by ring⟩)]
    ring
  -- the next even partial sum is the odd one minus the fresh positive term
  have hE_succ : ∀ k : ℕ, (∑ j ∈ Finset.range (2 * (k + 1)), (-1 : ℝ) ^ j * g j)
      = (∑ j ∈ Finset.range (2 * k + 1), (-1 : ℝ) ^ j * g j) - g (2 * k + 1) := by
    intro k
    have h := Finset.sum_range_succ (f := fun j => (-1 : ℝ) ^ j * g j) (n := 2 * k + 1)
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring, h,
        Odd.neg_one_pow (show Odd (2 * k + 1) from ⟨k, by ring⟩)]
    ring
  -- the next odd partial sum is the even one plus the fresh positive term
  have hO_succ : ∀ k : ℕ, (∑ j ∈ Finset.range (2 * (k + 1) + 1), (-1 : ℝ) ^ j * g j)
      = (∑ j ∈ Finset.range (2 * (k + 1)), (-1 : ℝ) ^ j * g j) + g (2 * (k + 1)) := by
    intro k
    have h := Finset.sum_range_succ (f := fun j => (-1 : ℝ) ^ j * g j) (n := 2 * (k + 1))
    rw [h, Even.neg_one_pow (show Even (2 * (k + 1)) from ⟨k + 1, by ring⟩)]
    ring
  have key : ∀ k : ℕ,
      (0 ≤ ∑ j ∈ Finset.range (2 * k), (-1 : ℝ) ^ j * g j ∧
       ∑ j ∈ Finset.range (2 * k), (-1 : ℝ) ^ j * g j ≤ g 0 ∧
       0 ≤ ∑ j ∈ Finset.range (2 * k + 1), (-1 : ℝ) ^ j * g j ∧
       ∑ j ∈ Finset.range (2 * k + 1), (-1 : ℝ) ^ j * g j ≤ g 0) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp
      · simpa using hnn 0
      · simpa using hnn 0
      · simp
    | succ k ih =>
      obtain ⟨hE0, hE1, hO0, hO1⟩ := ih
      have hE0' : 0 ≤ ∑ j ∈ Finset.range (2 * (k + 1)), (-1 : ℝ) ^ j * g j := by
        rw [hE_succ k]
        have hle : g (2 * k + 1) ≤ ∑ j ∈ Finset.range (2 * k + 1), (-1 : ℝ) ^ j * g j := by
          rw [hO_eq k]
          linarith [hE0, hanti (show 2 * k ≤ 2 * k + 1 from by omega)]
        linarith
      have hE1' : ∑ j ∈ Finset.range (2 * (k + 1)), (-1 : ℝ) ^ j * g j ≤ g 0 := by
        rw [hE_succ k]
        linarith [hO1, hnn (2 * k + 1)]
      have hO0' : 0 ≤ ∑ j ∈ Finset.range (2 * (k + 1) + 1), (-1 : ℝ) ^ j * g j := by
        rw [hO_succ k]
        linarith [hE0', hnn (2 * (k + 1))]
      have hO1' : ∑ j ∈ Finset.range (2 * (k + 1) + 1), (-1 : ℝ) ^ j * g j ≤ g 0 := by
        rw [hO_succ k, hE_succ k]
        linarith [hO1, hnn (2 * k + 1),
          hanti (show 2 * k + 1 ≤ 2 * (k + 1) from by omega)]
      exact ⟨hE0', hE1', hO0', hO1'⟩
  intro m
  obtain hm | hm := Nat.even_or_odd m
  · obtain ⟨k, rfl⟩ := hm
    rw [show k + k = 2 * k from by ring]
    obtain ⟨h1, h2, -, -⟩ := key k
    exact abs_le.mpr ⟨by linarith [hnn 0], h2⟩
  · obtain ⟨k, rfl⟩ := hm
    obtain ⟨-, -, h1, h2⟩ := key k
    exact abs_le.mpr ⟨by linarith [hnn 0], h2⟩

/-- Consecutive convergents of a non-terminating continued fraction differ by
`(-1)^n / (dens n * dens (n+1))`; this is the determinant identity `AₙBₙ₊₁ - BₙAₙ₊₁ = (-1)^(n+1)`
of the convergents, rearranged. -/
theorem convs_succ_sub_convs_aux (v : ℝ)
    (hv : ∀ n, ¬ (GenContFract.of v).TerminatedAt n) (n : ℕ) :
    (GenContFract.of v).convs (n + 1) - (GenContFract.of v).convs n
      = (-1 : ℝ) ^ n / ((GenContFract.of v).dens n * (GenContFract.of v).dens (n + 1)) := by
  have hdet := SimpContFract.determinant (s := SimpContFract.of v) (n := n) (hv n)
  simp only [SimpContFract.of] at hdet
  have hdn : (GenContFract.of v).dens n ≠ 0 := ne_of_gt (dens_pos_of_nonterminating v hv n)
  have hdn1 : (GenContFract.of v).dens (n + 1) ≠ 0 :=
    ne_of_gt (dens_pos_of_nonterminating v hv (n + 1))
  rw [GenContFract.conv_eq_num_div_den (g := GenContFract.of v) (n := n + 1),
      GenContFract.conv_eq_num_div_den (g := GenContFract.of v) (n := n)]
  field_simp
  have e : -(-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ n := by rw [pow_succ]; ring
  linarith [hdet, e]

/-- **Cross bound.** For a real `v` with non-terminating continued fraction expansion, any two
convergents at indices `i < k` are at distance at most
`1 / (dens i * dens (i+1))`. -/
theorem conv_cross_bound (v : ℝ) (hv : ∀ n, ¬ (GenContFract.of v).TerminatedAt n) :
    ∀ i k : ℕ, i < k →
      |(GenContFract.of v).convs k - (GenContFract.of v).convs i|
        ≤ 1 / ((GenContFract.of v).dens i * (GenContFract.of v).dens (i + 1)) := by
  intro i k hik
  have hpos := dens_pos_of_nonterminating v hv
  have hmono : Monotone (fun n => (GenContFract.of v).dens n) :=
    monotone_nat_of_le_succ (fun n => GenContFract.of_den_mono (v := v) (n := n))
  -- telescoping identity
  have htel : (GenContFract.of v).convs k - (GenContFract.of v).convs i
      = ∑ r ∈ Finset.range (k - i),
          ((GenContFract.of v).convs (i + (r + 1)) - (GenContFract.of v).convs (i + r)) := by
    rw [Finset.sum_range_sub (fun r => (GenContFract.of v).convs (i + r)) (k - i),
        Nat.add_sub_of_le hik.le, Nat.add_zero]
  rw [htel]
  -- each gap is `(-1)^(i+r) * g r`
  have hstep : ∀ r : ℕ, (GenContFract.of v).convs (i + (r + 1)) - (GenContFract.of v).convs (i + r)
      = (-1 : ℝ) ^ (i + r)
        * (1 / ((GenContFract.of v).dens (i + r) * (GenContFract.of v).dens (i + r + 1))) := by
    intro r
    rw [show i + (r + 1) = (i + r) + 1 from by omega, convs_succ_sub_convs_aux v hv (i + r),
      div_eq_mul_one_div]
  simp_rw [hstep]
  -- factor out the sign `(-1)^i`
  have hfac : ∑ r ∈ Finset.range (k - i),
        (-1 : ℝ) ^ (i + r)
          * (1 / ((GenContFract.of v).dens (i + r) * (GenContFract.of v).dens (i + r + 1)))
      = (-1 : ℝ) ^ i * ∑ r ∈ Finset.range (k - i),
          (-1 : ℝ) ^ r
            * (1 / ((GenContFract.of v).dens (i + r) * (GenContFract.of v).dens (i + r + 1))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun r _ => by rw [pow_add]; ring)
  rw [hfac, abs_mul, abs_neg_one_pow, one_mul]
  -- the terms are positive and antitone
  have hanti : Antitone (fun r : ℕ =>
      1 / ((GenContFract.of v).dens (i + r) * (GenContFract.of v).dens (i + r + 1))) := by
    intro a b hab
    apply one_div_le_one_div_of_le
    · exact mul_pos (hpos (i + a)) (hpos (i + a + 1))
    · exact mul_le_mul (hmono (by omega)) (hmono (by omega))
        (le_of_lt (hpos (i + a + 1))) (le_of_lt (hpos (i + b)))
  have hnn : ∀ r : ℕ,
      0 ≤ 1 / ((GenContFract.of v).dens (i + r) * (GenContFract.of v).dens (i + r + 1)) :=
    fun r => div_nonneg zero_le_one (le_of_lt (mul_pos (hpos (i + r)) (hpos (i + r + 1))))
  have halt := abs_sum_range_alt
    (fun r : ℕ => 1 / ((GenContFract.of v).dens (i + r) * (GenContFract.of v).dens (i + r + 1)))
    hanti hnn (k - i)
  simpa [Nat.add_zero] using halt

end Work.TMC7Core.Scale
