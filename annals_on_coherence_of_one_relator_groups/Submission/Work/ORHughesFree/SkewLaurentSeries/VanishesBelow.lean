/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Monomials and the vanishing filtration of `A((t;τ))`

Two ingredients used to analyse units of the skew Laurent series ring
`A((t;τ)) = SkewLaurentSeries A`:

* `mono m a`, the monomial `a·tᵐ` (the series whose only possibly nonzero coefficient is `a`,
  at the index `m`);
* `VanishesBelow f N`, the statement that all coefficients of `f` at indices `< N` vanish.

The series ring is filtered by `VanishesBelow`: it is stable under addition and negation, and if
`f` vanishes below `M` and `g` vanishes below `N` then `f * g` vanishes below `M + N` — this is
the `t`-adic filtration, and it is what makes every `1 + u` with `u` vanishing below `1`
invertible (the geometric series `∑ (-u)^i` is finite in each degree).
-/
import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries
import Submission.Work.ORHughesFree.SkewLaurentSeriesInstances

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace Work.ORHughesFree
namespace SkewLaurentSeries

variable {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]

/-- The monomial `a·tᵐ` of `A((t;τ))`: the series with the single possibly nonzero coefficient
`a`, at the index `m`. -/
noncomputable def mono (m : ℤ) (a : A) : SkewLaurentSeries A :=
  ⟨fun n => if n = m then a else 0, ⟨m - 1, fun n hn => by
    simp only [show n ≠ m by omega, if_false]⟩⟩

@[simp] theorem mono_apply (m : ℤ) (a : A) (n : ℤ) :
    (mono m a).1 n = if n = m then a else 0 := rfl

/-- The monomial `t⁰ = 1`. -/
theorem mono_zero_one : (mono (0 : ℤ) (1 : A) : SkewLaurentSeries A) = 1 :=
  Subtype.ext rfl

/-- Multiplying a monomial `a·tᵏ` into a series `f` from the left shifts `f` by `k` and applies
the twist `k • ·` to the coefficients: `(a·tᵏ·f)ₙ = a·(k • fₙ₋ₖ)`. -/
theorem mono_mul_apply (k : ℤ) (a : A) (f : SkewLaurentSeries A) (n : ℤ) :
    (mono k a * f).1 n = a * (Multiplicative.ofAdd k • f.1 (n - k)) := by
  rw [mul_apply_of_bounds (mono k a) f (k - 1) (lo f)
    (fun i hi => by rw [mono_apply, if_neg (by omega : i ≠ k)])
    (fun i hi => lt_lo hi) n]
  rw [Finset.sum_eq_single k]
  · rw [mono_apply, if_pos rfl]
  · intro i _ hik
    rw [mono_apply, if_neg hik]
    exact MulZeroClass.zero_mul _
  · intro hk
    rw [Finset.mem_Icc] at hk
    rw [mono_apply, if_pos rfl]
    have hlt : n - k < lo f := by omega
    rw [lt_lo hlt, smul_zero]
    exact MulZeroClass.mul_zero _

/-- The product of two monomials: `(a·tᵐ)(b·tᵏ) = (a·(m • b))·tᵐ⁺ᵏ`. -/
theorem mono_mul (m k : ℤ) (a b : A) :
    mono m a * mono k b = mono (m + k) (a * (Multiplicative.ofAdd m • b)) := by
  apply Subtype.ext
  funext n
  rw [mul_apply_of_bounds (mono m a) (mono k b) (m - 1) (k - 1)
    (fun i hi => by rw [mono_apply, if_neg (by omega : i ≠ m)])
    (fun i hi => by rw [mono_apply, if_neg (by omega : i ≠ k)]) n]
  rw [Finset.sum_eq_single m]
  · rw [mono_apply, mono_apply, mono_apply, if_pos rfl]
    rw [smul_ite, smul_zero, mul_ite, MulZeroClass.mul_zero]
    exact if_congr (by omega : n - m = k ↔ n = m + k) rfl rfl
  · intro i _ hi
    rw [mono_apply, if_neg hi]
    exact MulZeroClass.zero_mul _
  · intro hm
    rw [Finset.mem_Icc] at hm
    rw [mono_apply, if_pos rfl, mono_apply, if_neg (by omega : n - m ≠ k), smul_zero]
    exact MulZeroClass.mul_zero _

/-- **The vanishing filtration.**  `VanishesBelow f N` says that every coefficient of `f` at an
index `< N` is zero. -/
def VanishesBelow (f : SkewLaurentSeries A) (N : ℤ) : Prop := ∀ n : ℤ, n < N → f.1 n = 0

/-- The shift of a series by `m`: `shift m f` is the series whose `j`-th coefficient is
`(-m) • f_{m+j}`.  It is characterised by `mono m 1 * shift m f = f`, so that every series
vanishing below `m` with a `m`-th coefficient `c` is `tᵐ` times a series with constant term
`(-m) • c` (and vanishing below `0`). -/
noncomputable def shift (m : ℤ) (f : SkewLaurentSeries A) : SkewLaurentSeries A :=
  ⟨fun j => (Multiplicative.ofAdd (-m)) • f.1 (m + j), ⟨lo f - m, fun j hj => by
    show (Multiplicative.ofAdd (-m)) • f.1 (m + j) = 0
    rw [lt_lo (f := f) (n := m + j) (by omega : m + j < lo f), smul_zero]⟩⟩

@[simp] theorem shift_apply (m : ℤ) (f : SkewLaurentSeries A) (j : ℤ) :
    (shift m f).1 j = (Multiplicative.ofAdd (-m)) • f.1 (m + j) := rfl

/-- The shift of a series vanishing below `m` vanishes below `0`. -/
theorem VanishesBelow.shift {f : SkewLaurentSeries A} {m : ℤ} (h : VanishesBelow f m) :
    VanishesBelow (shift m f) 0 := fun j hj => by
  show (Multiplicative.ofAdd (-m)) • f.1 (m + j) = 0
  rw [h (m + j) (by omega), smul_zero]

/-- Recovering a series from its shift: `tᵐ * shift m f = f`. -/
theorem mono_mul_shift (m : ℤ) (f : SkewLaurentSeries A) : mono m (1 : A) * shift m f = f := by
  apply Subtype.ext
  funext n
  rw [mono_mul_apply, shift_apply, _root_.one_mul, show m + (n - m) = n by ring, smul_smul,
    ← ofAdd_add, show m + -m = 0 by ring, ofAdd_zero, one_smul]

theorem vanishesBelow_lo (f : SkewLaurentSeries A) : VanishesBelow f (lo f) := fun _n hn => lt_lo hn

theorem VanishesBelow.mono {f : SkewLaurentSeries A} {M N : ℤ} (h : VanishesBelow f M)
    (hNM : N ≤ M) : VanishesBelow f N := fun n hn => h n (lt_of_lt_of_le hn hNM)

theorem VanishesBelow.zero (N : ℤ) : VanishesBelow (0 : SkewLaurentSeries A) N := fun _ _ => rfl

theorem VanishesBelow.add {f g : SkewLaurentSeries A} {N : ℤ} (hf : VanishesBelow f N)
    (hg : VanishesBelow g N) : VanishesBelow (f + g) N :=
  fun n hn => by simp [add_apply, hf n hn, hg n hn]

theorem VanishesBelow.neg {f : SkewLaurentSeries A} {N : ℤ} (hf : VanishesBelow f N) :
    VanishesBelow (-f) N := fun n hn => by rw [neg_apply, hf n hn, neg_zero]

@[simp] theorem sub_apply (f g : SkewLaurentSeries A) (n : ℤ) :
    (f - g).1 n = f.1 n - g.1 n := by
  simp [sub_eq_add_neg]

theorem VanishesBelow.sub {f g : SkewLaurentSeries A} {N : ℤ} (hf : VanishesBelow f N)
    (hg : VanishesBelow g N) : VanishesBelow (f - g) N :=
  fun n hn => by rw [sub_apply, hf n hn, hg n hn, sub_zero]

/-- The unit series `1` vanishes below any bound `N ≤ 0`. -/
theorem VanishesBelow.one (N : ℤ) (hN : N ≤ 0) : VanishesBelow (1 : SkewLaurentSeries A) N :=
  fun n hn => by rw [one_apply, if_neg (by omega : n ≠ 0)]

theorem one_vanishesBelow_zero : VanishesBelow (1 : SkewLaurentSeries A) 0 :=
  VanishesBelow.one 0 le_rfl

/-- If `f` vanishes below `N` and in addition its `N`-th coefficient vanishes, then `f` vanishes
below `N + 1`. -/
theorem VanishesBelow.succ {f : SkewLaurentSeries A} {N : ℤ} (h : VanishesBelow f N)
    (hN : f.1 N = 0) : VanishesBelow f (N + 1) := by
  intro n hn
  by_cases hlt : n < N
  · exact h n hlt
  · have : n = N := by omega
    rw [this]; exact hN

/-- A monomial `a·tᵐ` vanishes below any bound `N ≤ m`. -/
theorem mono_vanishesBelow (m : ℤ) (a : A) {N : ℤ} (hN : N ≤ m) :
    VanishesBelow (mono m a) N := fun n hn => by
  rw [mono_apply, if_neg (by omega : n ≠ m)]

/-- **The `t`-adic filtration is multiplicative**: if `f` vanishes below `M` and `g` vanishes
below `N`, then `f * g` vanishes below `M + N`.  This is immediate from the coefficient formula
`mul_apply_of_bounds`: for `n < M + N` the summation interval `[M, n - N]` is empty. -/
theorem VanishesBelow.mul {f g : SkewLaurentSeries A} {M N : ℤ} (hf : VanishesBelow f M)
    (hg : VanishesBelow g N) : VanishesBelow (f * g) (M + N) := by
  intro n hn
  rw [mul_apply_of_bounds f g M N hf hg n, Finset.Icc_eq_empty (by omega : ¬ M ≤ n - N)]
  simp

/-- Powers of a series vanishing below `1` vanish below the exponent. -/
theorem VanishesBelow.pow {u : SkewLaurentSeries A} (hu : VanishesBelow u 1) (n : ℕ) :
    VanishesBelow (u ^ n) (n : ℤ) := by
  induction n with
  | zero => simpa using (VanishesBelow.one (0 : ℤ) le_rfl)
  | succ n ih =>
      have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
      rw [hcast, pow_succ]
      exact ih.mul hu

/-- Coefficients of a finite sum of series are the finite sums of the coefficients. -/
theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → SkewLaurentSeries A) (n : ℤ) :
    (∑ i ∈ s, f i).1 n = ∑ i ∈ s, (f i).1 n := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]

theorem VanishesBelow.sum {ι : Type*} (s : Finset ι) (f : ι → SkewLaurentSeries A) {N : ℤ}
    (h : ∀ i ∈ s, VanishesBelow (f i) N) : VanishesBelow (∑ i ∈ s, f i) N := by
  intro n hn
  rw [sum_apply, Finset.sum_eq_zero]
  intro i hi
  exact h i hi n hn

end SkewLaurentSeries
end Work.ORHughesFree
