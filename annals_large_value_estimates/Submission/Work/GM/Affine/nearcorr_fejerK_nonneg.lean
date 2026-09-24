import Mathlib
import Submission.Work.GM.Affine.WinMass_fejer_defs

/-!
# Non-negativity of the Fejér kernel `fejerK` (GM §9, region II)

`fejerK M₃ x = 1 + 2 ∑_{k=1}^{N-1} (1 - k/N) cos (2π k x)` (`N = fejerN M₃`) is the classical
Fejér kernel, written as a cosine polynomial.  The standard route to its non-negativity is the
identity

  `N * fejerK M₃ x = (∑_{k<N} cos (2π k x))² + (∑_{k<N} sin (2π k x))²`,

whose right-hand side is visibly a sum of two squares.

The proof of that identity here is elementary and completely explicit.

* `fejerK_sum_range_range_sub`: the "difference correlation" identity
  `∑_{k,l<N} F (k-l) = N * F 0 + ∑_{j<N} (N-(j+1)) * (F (j+1) + F (-(j+1)))`,
  proved by induction on `N` (the induction step expands the two `range (N+1)` sums, uses
  `Finset.sum_range_reflect` twice and the exact linearity of the weights in `N`).
* `fejerK_sq_sum_cos_add_sq_sum_sin`: `C² + S²` *is* the difference correlation of `cos`,
  because `cos (a-b) = cos a cos b + sin a sin b`.
* `fejerK_double_cos_sum`: specialising the correlation identity to `F d = cos (2π d x)` and
  using `cos (-a) = cos a` turns the double sum into `N + 2 ∑_{j<N} (N-(j+1)) cos (2π(j+1)x)`.
* `fejerK_sum_range_succ_eq_sum_Icc_pred`: reindexes `∑_{j<N} H (j+1)` as `∑_{k ∈ Icc 1 (N-1)} H k`.

The two `Icc`/`range` conversions are the small lemmas
`fejerK_sum_Icc_one_eq_sum_range` and `fejerK_sum_range_succ_eq_sum_Icc_pred`.
-/

open Finset

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.GM.Affine

noncomputable section

/-- `∑_{k ∈ Icc 1 M} H k = ∑_{j ∈ range M} H (j+1)`. -/
lemma fejerK_sum_Icc_one_eq_sum_range (M : ℕ) (H : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 M, H k) = ∑ j ∈ Finset.range M, H (j + 1) := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih]

/-- `∑_{j ∈ range N} H (j+1) = ∑_{k ∈ Icc 1 (N-1)} H k` when `H N = 0` (so that the `k = N`
term may be dropped). -/
lemma fejerK_sum_range_succ_eq_sum_Icc_pred (N : ℕ) (H : ℕ → ℝ) (hN : 1 ≤ N) (hzero : H N = 0) :
    (∑ j ∈ Finset.range N, H (j + 1)) = ∑ k ∈ Finset.Icc 1 (N - 1), H k := by
  rw [← fejerK_sum_Icc_one_eq_sum_range N H]
  conv_lhs => rw [show N = N - 1 + 1 by omega]
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N - 1 + 1)]
  rw [show N - 1 + 1 = N by omega, hzero, add_zero]

/-- The weighted difference correlation
`∑_{k,l<N} F (k-l) = N * F 0 + ∑_{j<N} (N-(j+1)) * (F (j+1) + F (-(j+1)))`. -/
lemma fejerK_sum_range_range_sub (N : ℕ) (F : ℤ → ℝ) :
    (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, F ((k : ℤ) - (l : ℤ)))
      = (N : ℝ) * F 0
        + ∑ j ∈ Finset.range N,
            ((N : ℝ) - ((j : ℝ) + 1)) * (F ((j : ℤ) + 1) + F (-((j : ℤ) + 1))) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hL : (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1), F ((k : ℤ) - (l : ℤ)))
        = (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, F ((k : ℤ) - (l : ℤ)))
          + (∑ k ∈ Finset.range n, F ((k : ℤ) - (n : ℤ)))
          + (∑ l ∈ Finset.range n, F ((n : ℤ) - (l : ℤ)))
          + F 0 := by
      have hinner : ∀ k : ℕ, (∑ l ∈ Finset.range (n + 1), F ((k : ℤ) - (l : ℤ)))
          = (∑ l ∈ Finset.range n, F ((k : ℤ) - (l : ℤ))) + F ((k : ℤ) - (n : ℤ)) :=
        fun k => Finset.sum_range_succ (fun l => F ((k : ℤ) - (l : ℤ))) n
      rw [Finset.sum_congr rfl (fun k _ => hinner k)]
      rw [Finset.sum_add_distrib, Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [sub_self]
      ring
    have hk : (∑ k ∈ Finset.range n, F ((k : ℤ) - (n : ℤ)))
        = ∑ j ∈ Finset.range n, F (-((j : ℤ) + 1)) := by
      rw [← Finset.sum_range_reflect (fun k => F ((k : ℤ) - (n : ℤ))) n]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      simp only [Finset.mem_range] at hj
      congr 1
      omega
    have hl : (∑ l ∈ Finset.range n, F ((n : ℤ) - (l : ℤ)))
        = ∑ j ∈ Finset.range n, F ((j : ℤ) + 1) := by
      rw [← Finset.sum_range_reflect (fun l => F ((n : ℤ) - (l : ℤ))) n]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      simp only [Finset.mem_range] at hj
      congr 1
      omega
    have hG : (∑ j ∈ Finset.range (n + 1),
          (((n + 1 : ℕ) : ℝ) - ((j : ℝ) + 1)) * (F ((j : ℤ) + 1) + F (-((j : ℤ) + 1))))
        = (∑ j ∈ Finset.range n,
              ((n : ℝ) - ((j : ℝ) + 1)) * (F ((j : ℤ) + 1) + F (-((j : ℤ) + 1))))
          + (∑ j ∈ Finset.range n, (F ((j : ℤ) + 1) + F (-((j : ℤ) + 1)))) := by
      have hz : (((n + 1 : ℕ) : ℝ) - ((n : ℝ) + 1))
          * (F ((n : ℤ) + 1) + F (-((n : ℤ) + 1))) = 0 := by
        push_cast; ring
      rw [Finset.sum_range_succ, hz, add_zero, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hcoef : (((n + 1 : ℕ) : ℝ) - ((j : ℝ) + 1)) = ((n : ℝ) - ((j : ℝ) + 1)) + 1 := by
        push_cast; ring
      rw [hcoef, add_mul, one_mul]
    rw [hL, ih, hG, hk, hl, Finset.sum_add_distrib]
    push_cast
    ring

/-- `N abel`-free form of Wiener–Khinchin for a pure cosine: `C² + S²` is the difference
correlation of the cosine. -/
lemma fejerK_sq_sum_cos_add_sq_sum_sin (N : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range N, Real.cos (2 * Real.pi * k * x)) ^ 2
      + (∑ k ∈ Finset.range N, Real.sin (2 * Real.pi * k * x)) ^ 2
    = ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
        Real.cos (2 * Real.pi * ((k : ℝ) - (l : ℝ)) * x) := by
  have hcos : (∑ k ∈ Finset.range N, Real.cos (2 * Real.pi * k * x)) ^ 2
      = ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
          Real.cos (2 * Real.pi * k * x) * Real.cos (2 * Real.pi * l * x) := by
    rw [sq, Finset.sum_mul_sum]
  have hsin : (∑ k ∈ Finset.range N, Real.sin (2 * Real.pi * k * x)) ^ 2
      = ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
          Real.sin (2 * Real.pi * k * x) * Real.sin (2 * Real.pi * l * x) := by
    rw [sq, Finset.sum_mul_sum]
  rw [hcos, hsin, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [← Real.cos_sub]
  congr 1
  ring

/-- `∑_{k,l<N} cos (2π (k-l) x) = N + 2 ∑_{j<N} (N-(j+1)) cos (2π (j+1) x)`. -/
lemma fejerK_double_cos_sum (N : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
        Real.cos (2 * Real.pi * ((k : ℝ) - (l : ℝ)) * x))
      = (N : ℝ) + 2 * ∑ j ∈ Finset.range N,
          ((N : ℝ) - ((j : ℝ) + 1)) * Real.cos (2 * Real.pi * ((j : ℝ) + 1) * x) := by
  have hgen := fejerK_sum_range_range_sub N (fun d : ℤ => Real.cos (2 * Real.pi * ((d : ℝ)) * x))
  have hL : (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
        Real.cos (2 * Real.pi * ((k : ℝ) - (l : ℝ)) * x))
      = (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
          Real.cos (2 * Real.pi * (((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * x)) := by
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    congr 1
    push_cast
    ring
  rw [hL, hgen]
  have hF0 : (N : ℝ) * Real.cos (2 * Real.pi * ((0 : ℤ) : ℝ) * x) = (N : ℝ) := by simp
  rw [hF0]
  have hterm : ∀ j : ℕ, Real.cos (2 * Real.pi * (((j : ℤ) + 1 : ℤ) : ℝ) * x)
        + Real.cos (2 * Real.pi * ((-((j : ℤ) + 1) : ℤ) : ℝ) * x)
      = 2 * Real.cos (2 * Real.pi * ((j : ℝ) + 1) * x) := by
    intro j
    have h1 : (((j : ℤ) + 1 : ℤ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    have h2 : ((-((j : ℤ) + 1) : ℤ) : ℝ) = -((j : ℝ) + 1) := by push_cast; ring
    rw [h1, h2,
      show 2 * Real.pi * (-((j : ℝ) + 1)) * x = -(2 * Real.pi * ((j : ℝ) + 1) * x) by ring,
      Real.cos_neg]
    ring
  rw [Finset.sum_congr rfl (fun j _ => by rw [hterm j])]
  rw [show (∑ j ∈ Finset.range N,
        ((N : ℝ) - ((j : ℝ) + 1)) * (2 * Real.cos (2 * Real.pi * ((j : ℝ) + 1) * x)))
      = 2 * ∑ j ∈ Finset.range N,
        ((N : ℝ) - ((j : ℝ) + 1)) * Real.cos (2 * Real.pi * ((j : ℝ) + 1) * x) by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => by ring)]

/-- The Fejér cosine polynomial of order `N ≥ 1` is non-negative:
`N * (1 + 2 ∑_{k=1}^{N-1} (1-k/N) cos (2πkx)) = (∑_{k<N} cos (2πkx))² + (∑_{k<N} sin (2πkx))² ≥ 0`. -/
lemma fejerK_nonneg_of (N : ℕ) (hN : 1 ≤ N) (x : ℝ) :
    0 ≤ 1 + 2 * ∑ k ∈ Finset.Icc 1 (N - 1),
        (1 - (k : ℝ) / (N : ℝ)) * Real.cos (2 * Real.pi * (k : ℝ) * x) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hFej : (N : ℝ) * (1 + 2 * ∑ k ∈ Finset.Icc 1 (N - 1),
        (1 - (k : ℝ) / (N : ℝ)) * Real.cos (2 * Real.pi * (k : ℝ) * x))
      = (N : ℝ) + 2 * ∑ k ∈ Finset.Icc 1 (N - 1),
        ((N : ℝ) - (k : ℝ)) * Real.cos (2 * Real.pi * (k : ℝ) * x) := by
    have hmul : (N : ℝ) * (∑ k ∈ Finset.Icc 1 (N - 1),
        (1 - (k : ℝ) / (N : ℝ)) * Real.cos (2 * Real.pi * (k : ℝ) * x))
        = ∑ k ∈ Finset.Icc 1 (N - 1),
            ((N : ℝ) - (k : ℝ)) * Real.cos (2 * Real.pi * (k : ℝ) * x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have h1 : (N : ℝ) * (1 - (k : ℝ) / (N : ℝ)) = (N : ℝ) - (k : ℝ) := by
        rw [mul_sub, mul_one, mul_div_cancel₀ _ hNne]
      rw [← mul_assoc, h1]
    rw [mul_add, mul_one,
      show (N : ℝ) * (2 * ∑ k ∈ Finset.Icc 1 (N - 1),
          (1 - (k : ℝ) / (N : ℝ)) * Real.cos (2 * Real.pi * (k : ℝ) * x))
        = 2 * ((N : ℝ) * (∑ k ∈ Finset.Icc 1 (N - 1),
          (1 - (k : ℝ) / (N : ℝ)) * Real.cos (2 * Real.pi * (k : ℝ) * x))) by ring,
      hmul]
  have hS : (∑ j ∈ Finset.range N,
        ((N : ℝ) - ((j : ℝ) + 1)) * Real.cos (2 * Real.pi * ((j : ℝ) + 1) * x))
      = ∑ k ∈ Finset.Icc 1 (N - 1),
          ((N : ℝ) - (k : ℝ)) * Real.cos (2 * Real.pi * (k : ℝ) * x) := by
    have h1 := fejerK_sum_range_succ_eq_sum_Icc_pred N
      (fun k : ℕ => ((N : ℝ) - (k : ℝ)) * Real.cos (2 * Real.pi * (k : ℝ) * x)) hN (by simp)
    rw [← h1]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    push_cast
    ring
  have hfinal : (N : ℝ) * (1 + 2 * ∑ k ∈ Finset.Icc 1 (N - 1),
        (1 - (k : ℝ) / (N : ℝ)) * Real.cos (2 * Real.pi * (k : ℝ) * x))
      = (∑ k ∈ Finset.range N, Real.cos (2 * Real.pi * k * x)) ^ 2
        + (∑ k ∈ Finset.range N, Real.sin (2 * Real.pi * k * x)) ^ 2 := by
    rw [hFej, ← hS, ← fejerK_double_cos_sum N x, ← fejerK_sq_sum_cos_add_sq_sum_sin N x]
  have hP : 0 ≤ (∑ k ∈ Finset.range N, Real.cos (2 * Real.pi * k * x)) ^ 2
        + (∑ k ∈ Finset.range N, Real.sin (2 * Real.pi * k * x)) ^ 2 := by positivity
  have hdiv : (1 + 2 * ∑ k ∈ Finset.Icc 1 (N - 1),
        (1 - (k : ℝ) / (N : ℝ)) * Real.cos (2 * Real.pi * (k : ℝ) * x))
      = ((∑ k ∈ Finset.range N, Real.cos (2 * Real.pi * k * x)) ^ 2
        + (∑ k ∈ Finset.range N, Real.sin (2 * Real.pi * k * x)) ^ 2) / (N : ℝ) := by
    rw [eq_div_iff hNne, mul_comm]
    exact hfinal
  rw [hdiv]
  exact div_nonneg hP hNpos.le

/-- The Fejér kernel `fejerK M₃ x = 1 + 2 ∑_{k=1}^{N-1} (1-k/N) cos (2πkx)`, `N = fejerN M₃`,
is non-negative for every `x`. -/
theorem nearcorr_fejerK_nonneg (M₃ x : ℝ) : 0 ≤ fejerK M₃ x := by
  unfold fejerK
  exact fejerK_nonneg_of (fejerN M₃) (fejerN_pos M₃) x

end

end Work.GM.Affine
