import Mathlib
import Submission.Work.FIArea4.polya_vinogradov

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

/-- **Abel summation (summation by parts) with an explicit error term.**

If the partial sums `∑_{i < n} a i` of a sequence `a` are bounded by `Z` in absolute value, and
`φ` is bounded by `M` with first differences bounded by `D`, then the weighted sum of `a` against
`φ` over `[A, B]` is bounded by `Z * (2 M + (B - A) D)`.

The proof is the by-parts identity `∑_{[A,B]} φ·a = φ(B)·G(B+1) - φ(A)·G(A)
- ∑_{[A,B)} (φ(i+1) - φ(i))·G(i+1)` where `G(n) = ∑_{i<n} a i`, followed by the triangle
inequality. -/
lemma abel_bound_weights {a φ : ℕ → ℝ} {Z M D : ℝ} {A B : ℕ} (hAB : A ≤ B)
    (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hG : ∀ n, |∑ i ∈ Finset.range n, a i| ≤ Z)
    (hφ : ∀ n, |φ n| ≤ M)
    (hd : ∀ n, |φ (n + 1) - φ n| ≤ D) :
    |∑ i ∈ Finset.Ico A (B + 1), φ i * a i|
      ≤ Z * (2 * M + ((B - A : ℕ) : ℝ) * D) := by
  have hlt : A < B + 1 := by omega
  have key := Finset.sum_Ico_by_parts φ a hlt
  simp only [smul_eq_mul, Nat.add_sub_cancel] at key
  rw [key]
  have h1 : |φ B * (∑ i ∈ Finset.range (B + 1), a i)| ≤ M * Z := by
    rw [abs_mul]
    exact mul_le_mul (hφ B) (hG (B + 1)) (abs_nonneg _) hM
  have h2 : |φ A * (∑ i ∈ Finset.range A, a i)| ≤ M * Z := by
    rw [abs_mul]
    exact mul_le_mul (hφ A) (hG A) (abs_nonneg _) hM
  have h3 : |∑ i ∈ Finset.Ico A B, (φ (i + 1) - φ i) * (∑ j ∈ Finset.range (i + 1), a j)|
      ≤ ((B - A : ℕ) : ℝ) * D * Z := by
    calc |∑ i ∈ Finset.Ico A B, (φ (i + 1) - φ i) * (∑ j ∈ Finset.range (i + 1), a j)|
        ≤ ∑ i ∈ Finset.Ico A B, |(φ (i + 1) - φ i) * (∑ j ∈ Finset.range (i + 1), a j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Ico A B, D * Z := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hd i) (hG (i + 1)) (abs_nonneg _) hD
      _ = ((B - A : ℕ) : ℝ) * (D * Z) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ = ((B - A : ℕ) : ℝ) * D * Z := by ring
  suffices hmain : |φ B * (∑ i ∈ Finset.range (B + 1), a i) - φ A * (∑ i ∈ Finset.range A, a i)
        - ∑ i ∈ Finset.Ico A B, (φ (i + 1) - φ i) * (∑ j ∈ Finset.range (i + 1), a j)|
      ≤ M * Z + M * Z + ((B - A : ℕ) : ℝ) * D * Z by
    exact le_trans hmain (le_of_eq (by ring))
  have hu : |φ B * (∑ i ∈ Finset.range (B + 1), a i) - φ A * (∑ i ∈ Finset.range A, a i)|
      ≤ |φ B * (∑ i ∈ Finset.range (B + 1), a i)| + |φ A * (∑ i ∈ Finset.range A, a i)| := by
    simpa using abs_sub_le (φ B * (∑ i ∈ Finset.range (B + 1), a i)) 0
      (φ A * (∑ i ∈ Finset.range A, a i))
  have hv : |φ B * (∑ i ∈ Finset.range (B + 1), a i) - φ A * (∑ i ∈ Finset.range A, a i)
        - ∑ i ∈ Finset.Ico A B, (φ (i + 1) - φ i) * (∑ j ∈ Finset.range (i + 1), a j)|
      ≤ |φ B * (∑ i ∈ Finset.range (B + 1), a i) - φ A * (∑ i ∈ Finset.range A, a i)|
        + |∑ i ∈ Finset.Ico A B, (φ (i + 1) - φ i) * (∑ j ∈ Finset.range (i + 1), a j)| := by
    simpa using abs_sub_le
      (φ B * (∑ i ∈ Finset.range (B + 1), a i) - φ A * (∑ i ∈ Finset.range A, a i)) 0
      (∑ i ∈ Finset.Ico A B, (φ (i + 1) - φ i) * (∑ j ∈ Finset.range (i + 1), a j))
  linarith

/-- **Pólya–Vinogradov with a weight (Abel summation).**  Version of *FI* (22.5) for a weighted
sum.  If `m ≥ 1` has non-square odd part (so that `n ↦ (n|m)` is a non-trivial Jacobi-symbol
character mod `m`), `|φ n| ≤ M` and `|φ(n+1) − φ n| ≤ D` for all `n`, then

  `|Σ_{n ∈ [A, A+N]} (n|m)·φ(n)| ≤ C·(M + N·D)·√m·log m`.

This is the "`|k| + 1`" loss in the proof of *FI* Proposition 22.1: after splitting `s` into
residue classes mod `4d` (which fixes the values of the finite-modulus character `χ`) the inner sum
over a segment becomes a sum of the Jacobi symbol against a fixed modulus times the Hecke-character
factor `(z/|z|)^k`, whose total variation over the segment of length `≲ √N` is `≲ |k|`.  Summation
by parts turns the variation `D` into the `N·D` term and `M` into the boundary term.
`Work.FIArea7.polya_vinogradov_interval` is the unweighted case `M = 1, D = 0`. -/
theorem pv_weighted_jacobiSym :
    ∃ C : ℝ, 0 < C ∧ ∀ (m A N : ℕ) (φ : ℕ → ℝ) (M D : ℝ),
      1 ≤ m → (∀ k : ℕ, Work.FIPlan.oddPart m ≠ k ^ 2) →
      (∀ n, |φ n| ≤ M) → (∀ n, |φ (n + 1) - φ n| ≤ D) →
      |∑ n ∈ Finset.Icc A (A + N), ((jacobiSym (n : ℤ) m : ℝ) * φ n)|
        ≤ C * (M + (N : ℝ) * D) * Real.sqrt m * (Real.log m + 1) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.FIArea4.polya_vinogradov
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro m A N φ M D hm hns hφ hd
  have hm1 : m ≠ 1 := by
    intro h
    exact hns 1 (by rw [h]; simp [Work.FIPlan.oddPart])
  have hm1' : 1 < m := by omega
  have hM : 0 ≤ M := le_trans (abs_nonneg (φ 0)) (hφ 0)
  have hD : 0 ≤ D := le_trans (abs_nonneg (φ 1 - φ 0)) (hd 0)
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hZ0 : 0 ≤ C₀ * Real.sqrt m * (Real.log m + 1) := by
    have h1 : (0 : ℝ) ≤ Real.log m + 1 := by linarith
    positivity
  -- the prefix sums of the Jacobi symbol character are bounded by Pólya–Vinogradov
  have hG : ∀ n, |∑ i ∈ Finset.range n, (jacobiSym (i : ℤ) m : ℝ)|
      ≤ C₀ * Real.sqrt m * (Real.log m + 1) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [Finset.range_zero, Finset.sum_empty, abs_zero]
      positivity
    · obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      have hJ0 : (jacobiSym (((0 : ℕ) : ℤ)) m : ℝ) = 0 := by
        simpa using jacobiSym.zero_left (show 1 < m by omega)
      rw [Finset.sum_range_succ', hJ0, add_zero]
      have hseq : ∑ k ∈ Finset.range n', (jacobiSym (((k + 1 : ℕ) : ℤ)) m : ℝ)
          = ∑ k ∈ Finset.Icc 1 n', (jacobiSym (k : ℤ) m : ℝ) := by
        rw [show Finset.Icc 1 n' = Finset.Ico 1 (n' + 1) from rfl]
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Nat.add_comm]
      rw [hseq]
      exact hC₀ m n' hm hns
  -- Abel summation on the segment `[A, A+N]`
  have hmain := abel_bound_weights (a := fun i => (jacobiSym (i : ℤ) m : ℝ)) (φ := φ)
    (Z := C₀ * Real.sqrt m * (Real.log m + 1)) (M := M) (D := D)
    (Nat.le_add_right A N) hM hD hG hφ hd
  rw [Nat.add_sub_cancel_left] at hmain
  have hsum_eq : ∑ n ∈ Finset.Icc A (A + N), ((jacobiSym (n : ℤ) m : ℝ) * φ n)
      = ∑ i ∈ Finset.Ico A (A + N + 1), φ i * (jacobiSym (i : ℤ) m : ℝ) := by
    rw [show Finset.Icc A (A + N) = Finset.Ico A (A + N + 1) from rfl]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [hsum_eq]
  refine le_trans hmain ?_
  have hND : 0 ≤ (N : ℝ) * D := by positivity
  have h2 : 2 * M + (N : ℝ) * D ≤ 2 * (M + (N : ℝ) * D) := by linarith
  calc (C₀ * Real.sqrt m * (Real.log m + 1)) * (2 * M + (N : ℝ) * D)
      ≤ (C₀ * Real.sqrt m * (Real.log m + 1)) * (2 * (M + (N : ℝ) * D)) :=
        mul_le_mul_of_nonneg_left h2 hZ0
    _ = 2 * C₀ * (M + (N : ℝ) * D) * Real.sqrt m * (Real.log m + 1) := by ring

end Work.FIArea7
