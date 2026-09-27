import Mathlib

/-!
# Shift comparison for double grid sums

For `G : ℝ → ℝ → ℝ` which is `e`-Lipschitz under shifts of either argument by at most
`1 / N`, and which is bounded by `M` in absolute value, we compare the double sums over the
`m × m` grid `{i/N : i < m}²` with the same grid translated by `(r, s)`:

`|ΣΣ G (i/N + r) (j/N + s) - ΣΣ G (i/N) (j/N)| ≤ 2 m² e + 2 M (⌊r N⌋ + ⌊s N⌋) m`.

The proof compares the translated sum first with the grid translated by the *integer* vector
`(⌊r N⌋, ⌊s N⌋) / N` (cost `2 m² e`, by the Lipschitz bounds), and then compares this integer
translate with the origin: shifting the grid offset by one unit in either coordinate telescopes
in the corresponding index to a boundary difference of two `G`-values, giving `2 M m` per unit
shift.
-/

namespace Work.EKLComp.ErgMax

open Finset

noncomputable section

/-- The translated double grid sum, over `Finset.range m` indices. -/
def shiftSumR (N m : ℕ) (G : ℝ → ℝ → ℝ) (r s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, G ((i : ℝ) / N + r) ((j : ℝ) / N + s)

/-- The double grid sum with grid offset `(a, b)`: arguments `((i + a) / N, (j + b) / N)`. -/
def gridSumR (N m : ℕ) (G : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, G (((i : ℝ) + a) / N) (((j : ℝ) + b) / N)

/-- A double sum over `Finset.range m` equals the corresponding double sum over `Fin m`. -/
lemma sum_range2_eq_Fin (m : ℕ) (g : ℕ → ℕ → ℝ) :
    (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, g i j)
      = ∑ i : Fin m, ∑ j : Fin m, g i j := by
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => ∑ j ∈ Finset.range m, g i j)]
  apply Finset.sum_congr rfl
  intro i _
  exact (Fin.sum_univ_eq_sum_range (fun j : ℕ => g i j) m).symm

/-- Shifting the grid offset by `1` in the **first** coordinate: telescoping over `i` reduces the
difference to a boundary term of size `2 M` in each of the `m` columns. -/
lemma gridSumR_step_a (N m : ℕ) (G : ℝ → ℝ → ℝ) {M : ℝ}
    (hM : ∀ u v : ℝ, |G u v| ≤ M) (a b : ℝ) :
    |gridSumR N m G (a + 1) b - gridSumR N m G a b| ≤ 2 * M * m := by
  have hconv : gridSumR N m G (a + 1) b - gridSumR N m G a b
      = ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range m,
          (G (((i : ℝ) + (a + 1)) / N) (((j : ℝ) + b) / N)
            - G (((i : ℝ) + a) / N) (((j : ℝ) + b) / N)) := by
    simp only [gridSumR]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
  rw [hconv]
  have htel : ∀ j : ℕ, ∑ i ∈ Finset.range m,
        (G (((i : ℝ) + (a + 1)) / N) (((j : ℝ) + b) / N)
          - G (((i : ℝ) + a) / N) (((j : ℝ) + b) / N))
      = G (((m : ℝ) + a) / N) (((j : ℝ) + b) / N)
        - G ((a : ℝ) / N) (((j : ℝ) + b) / N) := by
    intro j
    have key : ∀ i : ℕ,
        G (((i : ℝ) + (a + 1)) / N) (((j : ℝ) + b) / N)
          - G (((i : ℝ) + a) / N) (((j : ℝ) + b) / N)
        = ((fun i : ℕ => G (((i : ℝ) + a) / N) (((j : ℝ) + b) / N)) (i + 1)
           - (fun i : ℕ => G (((i : ℝ) + a) / N) (((j : ℝ) + b) / N)) i) := by
      intro i
      have harg : ((i : ℝ) + (a + 1)) = (((i + 1 : ℕ) : ℝ) + a) := by push_cast; ring
      rw [harg]
    rw [Finset.sum_congr rfl (fun i _ => key i)]
    simpa using Finset.sum_range_sub (fun i : ℕ => G (((i : ℝ) + a) / N) (((j : ℝ) + b) / N)) m
  calc |∑ j ∈ Finset.range m, ∑ i ∈ Finset.range m,
          (G (((i : ℝ) + (a + 1)) / N) (((j : ℝ) + b) / N)
            - G (((i : ℝ) + a) / N) (((j : ℝ) + b) / N))|
      ≤ ∑ j ∈ Finset.range m, |∑ i ∈ Finset.range m,
          (G (((i : ℝ) + (a + 1)) / N) (((j : ℝ) + b) / N)
            - G (((i : ℝ) + a) / N) (((j : ℝ) + b) / N))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ Finset.range m,
          |G (((m : ℝ) + a) / N) (((j : ℝ) + b) / N)
            - G ((a : ℝ) / N) (((j : ℝ) + b) / N)| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [htel j]
    _ ≤ ∑ j ∈ Finset.range m, (M + M) := by
        apply Finset.sum_le_sum
        intro j _
        calc |G (((m : ℝ) + a) / N) (((j : ℝ) + b) / N)
                - G ((a : ℝ) / N) (((j : ℝ) + b) / N)|
            = |G (((m : ℝ) + a) / N) (((j : ℝ) + b) / N)
                + (- G ((a : ℝ) / N) (((j : ℝ) + b) / N))| := by rw [sub_eq_add_neg]
          _ ≤ |G (((m : ℝ) + a) / N) (((j : ℝ) + b) / N)|
                + |- G ((a : ℝ) / N) (((j : ℝ) + b) / N)| := abs_add_le _ _
          _ = |G (((m : ℝ) + a) / N) (((j : ℝ) + b) / N)|
                + |G ((a : ℝ) / N) (((j : ℝ) + b) / N)| := by rw [abs_neg]
          _ ≤ M + M := add_le_add (hM _ _) (hM _ _)
    _ = 2 * M * m := by
        simp [Finset.sum_const, Finset.card_range]
        ring

/-- Shifting the grid offset by `1` in the **second** coordinate (the transpose of
`gridSumR_step_a`). -/
lemma gridSumR_step_b (N m : ℕ) (G : ℝ → ℝ → ℝ) {M : ℝ}
    (hM : ∀ u v : ℝ, |G u v| ≤ M) (a b : ℝ) :
    |gridSumR N m G a (b + 1) - gridSumR N m G a b| ≤ 2 * M * m := by
  have hconv : gridSumR N m G a (b + 1) - gridSumR N m G a b
      = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
          (G (((i : ℝ) + a) / N) (((j : ℝ) + (b + 1)) / N)
            - G (((i : ℝ) + a) / N) (((j : ℝ) + b) / N)) := by
    simp only [gridSumR]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
  rw [hconv]
  have htel : ∀ i : ℕ, ∑ j ∈ Finset.range m,
        (G (((i : ℝ) + a) / N) (((j : ℝ) + (b + 1)) / N)
          - G (((i : ℝ) + a) / N) (((j : ℝ) + b) / N))
      = G (((i : ℝ) + a) / N) (((m : ℝ) + b) / N)
        - G (((i : ℝ) + a) / N) ((b : ℝ) / N) := by
    intro i
    have key : ∀ j : ℕ,
        G (((i : ℝ) + a) / N) (((j : ℝ) + (b + 1)) / N)
          - G (((i : ℝ) + a) / N) (((j : ℝ) + b) / N)
        = ((fun j : ℕ => G (((i : ℝ) + a) / N) (((j : ℝ) + b) / N)) (j + 1)
           - (fun j : ℕ => G (((i : ℝ) + a) / N) (((j : ℝ) + b) / N)) j) := by
      intro j
      have harg : ((j : ℝ) + (b + 1)) = (((j + 1 : ℕ) : ℝ) + b) := by push_cast; ring
      rw [harg]
    rw [Finset.sum_congr rfl (fun j _ => key j)]
    simpa using Finset.sum_range_sub (fun j : ℕ => G (((i : ℝ) + a) / N) (((j : ℝ) + b) / N)) m
  calc |∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
          (G (((i : ℝ) + a) / N) (((j : ℝ) + (b + 1)) / N)
            - G (((i : ℝ) + a) / N) (((j : ℝ) + b) / N))|
      ≤ ∑ i ∈ Finset.range m, |∑ j ∈ Finset.range m,
          (G (((i : ℝ) + a) / N) (((j : ℝ) + (b + 1)) / N)
            - G (((i : ℝ) + a) / N) (((j : ℝ) + b) / N))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range m,
          |G (((i : ℝ) + a) / N) (((m : ℝ) + b) / N)
            - G (((i : ℝ) + a) / N) ((b : ℝ) / N)| := by
        apply Finset.sum_congr rfl
        intro i _
        rw [htel i]
    _ ≤ ∑ i ∈ Finset.range m, (M + M) := by
        apply Finset.sum_le_sum
        intro i _
        calc |G (((i : ℝ) + a) / N) (((m : ℝ) + b) / N)
                - G (((i : ℝ) + a) / N) ((b : ℝ) / N)|
            = |G (((i : ℝ) + a) / N) (((m : ℝ) + b) / N)
                + (- G (((i : ℝ) + a) / N) ((b : ℝ) / N))| := by rw [sub_eq_add_neg]
          _ ≤ |G (((i : ℝ) + a) / N) (((m : ℝ) + b) / N)|
                + |- G (((i : ℝ) + a) / N) ((b : ℝ) / N)| := abs_add_le _ _
          _ = |G (((i : ℝ) + a) / N) (((m : ℝ) + b) / N)|
                + |G (((i : ℝ) + a) / N) ((b : ℝ) / N)| := by rw [abs_neg]
          _ ≤ M + M := add_le_add (hM _ _) (hM _ _)
    _ = 2 * M * m := by
        simp [Finset.sum_const, Finset.card_range]
        ring

/-- Iterating `gridSumR_step_a`: after `k` unit steps in the first coordinate the accumulated
error is at most `2 M m k`. -/
lemma gridSumR_shift_a_le (N m : ℕ) (G : ℝ → ℝ → ℝ) {M : ℝ}
    (hM : ∀ u v : ℝ, |G u v| ≤ M) (b : ℝ) (k : ℕ) :
    |gridSumR N m G (k : ℝ) b - gridSumR N m G 0 b| ≤ 2 * M * m * (k : ℝ) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h1 : ((Nat.succ n : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [h1]
    calc |gridSumR N m G ((n : ℝ) + 1) b - gridSumR N m G 0 b|
        = |(gridSumR N m G ((n : ℝ) + 1) b - gridSumR N m G (n : ℝ) b)
            + (gridSumR N m G (n : ℝ) b - gridSumR N m G 0 b)| := by ring
      _ ≤ |gridSumR N m G ((n : ℝ) + 1) b - gridSumR N m G (n : ℝ) b|
            + |gridSumR N m G (n : ℝ) b - gridSumR N m G 0 b| := abs_add_le _ _
      _ ≤ 2 * M * m + 2 * M * m * (n : ℝ) :=
            add_le_add (gridSumR_step_a N m G hM (n : ℝ) b) ih
      _ = 2 * M * m * ((n : ℝ) + 1) := by ring

/-- Iterating `gridSumR_step_b`: after `k` unit steps in the second coordinate the accumulated
error is at most `2 M m k`. -/
lemma gridSumR_shift_b_le (N m : ℕ) (G : ℝ → ℝ → ℝ) {M : ℝ}
    (hM : ∀ u v : ℝ, |G u v| ≤ M) (a : ℝ) (k : ℕ) :
    |gridSumR N m G a (k : ℝ) - gridSumR N m G a 0| ≤ 2 * M * m * (k : ℝ) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h1 : ((Nat.succ n : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [h1]
    calc |gridSumR N m G a ((n : ℝ) + 1) - gridSumR N m G a 0|
        = |(gridSumR N m G a ((n : ℝ) + 1) - gridSumR N m G a (n : ℝ))
            + (gridSumR N m G a (n : ℝ) - gridSumR N m G a 0)| := by ring
      _ ≤ |gridSumR N m G a ((n : ℝ) + 1) - gridSumR N m G a (n : ℝ)|
            + |gridSumR N m G a (n : ℝ) - gridSumR N m G a 0| := abs_add_le _ _
      _ ≤ 2 * M * m + 2 * M * m * (n : ℝ) :=
            add_le_add (gridSumR_step_b N m G hM a (n : ℝ)) ih
      _ = 2 * M * m * ((n : ℝ) + 1) := by ring

/-- Step A: the translated sum is within `2 m² e` of the sum at the offset `(K, L)`, where
`K/N ≤ r`, `L/N ≤ s` with `r - K/N ≤ 1/N` and `s - L/N ≤ 1/N`. -/
lemma shiftSumR_sub_gridSumR_le (N m : ℕ) (G : ℝ → ℝ → ℝ) {e r s K L : ℝ}
    (hstep1 : ∀ u v t : ℝ, 0 ≤ u → 0 ≤ v → 0 ≤ t → t ≤ 1 / (N : ℝ) →
      |G (u + t) v - G u v| ≤ e)
    (hstep2 : ∀ u v t : ℝ, 0 ≤ u → 0 ≤ v → 0 ≤ t → t ≤ 1 / (N : ℝ) →
      |G u (v + t) - G u v| ≤ e)
    (hKr : K / N ≤ r) (hKt : r - K / N ≤ 1 / (N : ℝ))
    (hLr : L / N ≤ s) (hLt : s - L / N ≤ 1 / (N : ℝ))
    (hK0 : 0 ≤ K) (hL0 : 0 ≤ L) :
    |shiftSumR N m G r s - gridSumR N m G K L| ≤ 2 * (m : ℝ) ^ 2 * e := by
  have hconv : shiftSumR N m G r s - gridSumR N m G K L
      = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
          (G ((i : ℝ) / N + r) ((j : ℝ) / N + s)
            - G (((i : ℝ) + K) / N) (((j : ℝ) + L) / N)) := by
    simp only [shiftSumR, gridSumR]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
  rw [hconv]
  have hterm : ∀ i j : ℕ,
      |G ((i : ℝ) / N + r) ((j : ℝ) / N + s)
        - G (((i : ℝ) + K) / N) (((j : ℝ) + L) / N)| ≤ 2 * e := by
    intro i j
    have hu : (((i : ℝ) + K) / N) + (r - K / N) = (i : ℝ) / N + r := by ring
    have hv : (((j : ℝ) + L) / N) + (s - L / N) = (j : ℝ) / N + s := by ring
    have hnum1 : (0 : ℝ) ≤ (i : ℝ) + K := add_nonneg (Nat.cast_nonneg i) hK0
    have hnum2 : (0 : ℝ) ≤ (j : ℝ) + L := add_nonneg (Nat.cast_nonneg j) hL0
    have hden : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hu0 : 0 ≤ ((i : ℝ) + K) / N := div_nonneg hnum1 hden
    have hv0 : 0 ≤ ((j : ℝ) + L) / N := div_nonneg hnum2 hden
    have ht1 : 0 ≤ r - K / N := by linarith
    have ht2 : 0 ≤ s - L / N := by linarith
    have hvt : 0 ≤ ((j : ℝ) + L) / N + (s - L / N) := add_nonneg hv0 ht2
    have h1 : |G (((i : ℝ) + K) / N + (r - K / N))
                  (((j : ℝ) + L) / N + (s - L / N))
                - G (((i : ℝ) + K) / N) (((j : ℝ) + L) / N + (s - L / N))| ≤ e :=
      hstep1 _ _ _ hu0 hvt ht1 hKt
    have h2 : |G (((i : ℝ) + K) / N) (((j : ℝ) + L) / N + (s - L / N))
                - G (((i : ℝ) + K) / N) (((j : ℝ) + L) / N)| ≤ e :=
      hstep2 _ _ _ hu0 hv0 ht2 hLt
    calc |G ((i : ℝ) / N + r) ((j : ℝ) / N + s)
            - G (((i : ℝ) + K) / N) (((j : ℝ) + L) / N)|
        = |G (((i : ℝ) + K) / N + (r - K / N)) (((j : ℝ) + L) / N + (s - L / N))
            - G (((i : ℝ) + K) / N) (((j : ℝ) + L) / N)| := by rw [hu, hv]
      _ ≤ |G (((i : ℝ) + K) / N + (r - K / N)) (((j : ℝ) + L) / N + (s - L / N))
              - G (((i : ℝ) + K) / N) (((j : ℝ) + L) / N + (s - L / N))|
            + |G (((i : ℝ) + K) / N) (((j : ℝ) + L) / N + (s - L / N))
              - G (((i : ℝ) + K) / N) (((j : ℝ) + L) / N)| := abs_sub_le _ _ _
      _ ≤ e + e := add_le_add h1 h2
      _ = 2 * e := by ring
  calc |∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
          (G ((i : ℝ) / N + r) ((j : ℝ) / N + s)
            - G (((i : ℝ) + K) / N) (((j : ℝ) + L) / N))|
      ≤ ∑ i ∈ Finset.range m, |∑ j ∈ Finset.range m,
          (G ((i : ℝ) / N + r) ((j : ℝ) / N + s)
            - G (((i : ℝ) + K) / N) (((j : ℝ) + L) / N))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
          |G ((i : ℝ) / N + r) ((j : ℝ) / N + s)
            - G (((i : ℝ) + K) / N) (((j : ℝ) + L) / N)| := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, (2 * e) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact hterm i j
    _ = 2 * (m : ℝ) ^ 2 * e := by
        simp [Finset.sum_const, Finset.card_range]
        ring

theorem shift_double_sum_le (N m : ℕ) (G : ℝ → ℝ → ℝ) {e M r s : ℝ}
    (hN : 1 ≤ N) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hstep1 : ∀ u v t : ℝ, 0 ≤ u → 0 ≤ v → 0 ≤ t → t ≤ 1 / (N : ℝ) →
      |G (u + t) v - G u v| ≤ e)
    (hstep2 : ∀ u v t : ℝ, 0 ≤ u → 0 ≤ v → 0 ≤ t → t ≤ 1 / (N : ℝ) →
      |G u (v + t) - G u v| ≤ e)
    (hM : ∀ u v : ℝ, |G u v| ≤ M) :
    |(∑ i : Fin m, ∑ j : Fin m, G ((i : ℝ) / N + r) ((j : ℝ) / N + s))
      - (∑ i : Fin m, ∑ j : Fin m, G ((i : ℝ) / N) ((j : ℝ) / N))|
      ≤ 2 * (m : ℝ) ^ 2 * e
        + 2 * M * (((⌊r * (N : ℝ)⌋ : ℤ) : ℝ) + ((⌊s * (N : ℝ)⌋ : ℤ) : ℝ)) * (m : ℝ) := by
  set K : ℤ := ⌊r * (N : ℝ)⌋ with hK
  set L : ℤ := ⌊s * (N : ℝ)⌋ with hL
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hKnn : 0 ≤ K := by
    rw [hK]; exact Int.floor_nonneg.mpr (mul_nonneg hr (Nat.cast_nonneg N))
  have hLnn : 0 ≤ L := by
    rw [hL]; exact Int.floor_nonneg.mpr (mul_nonneg hs (Nat.cast_nonneg N))
  have hKle : (K : ℝ) ≤ r * (N : ℝ) := by rw [hK]; exact Int.floor_le _
  have hKlt : r * (N : ℝ) < (K : ℝ) + 1 := by rw [hK]; exact Int.lt_floor_add_one _
  have hLle : (L : ℝ) ≤ s * (N : ℝ) := by rw [hL]; exact Int.floor_le _
  have hLlt : s * (N : ℝ) < (L : ℝ) + 1 := by rw [hL]; exact Int.lt_floor_add_one _
  have hKr : (K : ℝ) / N ≤ r := (div_le_iff₀ hNpos).mpr hKle
  have hLr : (L : ℝ) / N ≤ s := (div_le_iff₀ hNpos).mpr hLle
  have hKt : r - (K : ℝ) / N ≤ 1 / (N : ℝ) := by
    have h1 : r * (N : ℝ) - (K : ℝ) < 1 := by linarith
    have h2 : r - (K : ℝ) / N = (r * (N : ℝ) - (K : ℝ)) / (N : ℝ) := by
      rw [sub_div, mul_div_cancel_right₀ r (ne_of_gt hNpos)]
    rw [h2]
    exact le_of_lt ((div_lt_div_iff_of_pos_right hNpos).mpr h1)
  have hLt : s - (L : ℝ) / N ≤ 1 / (N : ℝ) := by
    have h1 : s * (N : ℝ) - (L : ℝ) < 1 := by linarith
    have h2 : s - (L : ℝ) / N = (s * (N : ℝ) - (L : ℝ)) / (N : ℝ) := by
      rw [sub_div, mul_div_cancel_right₀ s (ne_of_gt hNpos)]
    rw [h2]
    exact le_of_lt ((div_lt_div_iff_of_pos_right hNpos).mpr h1)
  have hA : |shiftSumR N m G r s - gridSumR N m G (K : ℝ) (L : ℝ)| ≤ 2 * (m : ℝ) ^ 2 * e :=
    shiftSumR_sub_gridSumR_le N m G hstep1 hstep2 hKr hKt hLr hLt
      (by exact_mod_cast hKnn) (by exact_mod_cast hLnn)
  have hk : ((K.toNat : ℕ) : ℝ) = (K : ℝ) := by
    have h : ((K.toNat : ℤ) : ℝ) = (K : ℝ) := by rw [Int.toNat_of_nonneg hKnn]
    rwa [Int.cast_natCast] at h
  have hl : ((L.toNat : ℕ) : ℝ) = (L : ℝ) := by
    have h : ((L.toNat : ℤ) : ℝ) = (L : ℝ) := by rw [Int.toNat_of_nonneg hLnn]
    rwa [Int.cast_natCast] at h
  have hB1 : |gridSumR N m G (K : ℝ) (L : ℝ) - gridSumR N m G 0 (L : ℝ)| ≤ 2 * M * m * (K : ℝ) := by
    rw [← hk]
    exact gridSumR_shift_a_le N m G hM (L : ℝ) K.toNat
  have hB2 : |gridSumR N m G 0 (L : ℝ) - gridSumR N m G 0 0| ≤ 2 * M * m * (L : ℝ) := by
    rw [← hl]
    exact gridSumR_shift_b_le N m G hM 0 L.toNat
  have hB : |gridSumR N m G (K : ℝ) (L : ℝ) - gridSumR N m G 0 0|
      ≤ 2 * M * ((K : ℝ) + (L : ℝ)) * (m : ℝ) := by
    calc |gridSumR N m G (K : ℝ) (L : ℝ) - gridSumR N m G 0 0|
        = |(gridSumR N m G (K : ℝ) (L : ℝ) - gridSumR N m G 0 (L : ℝ))
            + (gridSumR N m G 0 (L : ℝ) - gridSumR N m G 0 0)| := by ring
      _ ≤ |gridSumR N m G (K : ℝ) (L : ℝ) - gridSumR N m G 0 (L : ℝ)|
            + |gridSumR N m G 0 (L : ℝ) - gridSumR N m G 0 0| := abs_add_le _ _
      _ ≤ 2 * M * m * (K : ℝ) + 2 * M * m * (L : ℝ) := add_le_add hB1 hB2
      _ = 2 * M * ((K : ℝ) + (L : ℝ)) * (m : ℝ) := by ring
  have hS : shiftSumR N m G r s
      = ∑ i : Fin m, ∑ j : Fin m, G ((i : ℝ) / N + r) ((j : ℝ) / N + s) := by
    simp only [shiftSumR]
    exact sum_range2_eq_Fin m (fun i j => G ((i : ℝ) / N + r) ((j : ℝ) / N + s))
  have hG0 : gridSumR N m G 0 0
      = ∑ i : Fin m, ∑ j : Fin m, G ((i : ℝ) / N) ((j : ℝ) / N) := by
    have h := sum_range2_eq_Fin m (fun i j => G ((i : ℝ) / N) ((j : ℝ) / N))
    simpa only [gridSumR, add_zero] using h
  rw [← hS, ← hG0]
  calc |shiftSumR N m G r s - gridSumR N m G 0 0|
      ≤ |shiftSumR N m G r s - gridSumR N m G (K : ℝ) (L : ℝ)|
          + |gridSumR N m G (K : ℝ) (L : ℝ) - gridSumR N m G 0 0| := abs_sub_le _ _ _
    _ ≤ 2 * (m : ℝ) ^ 2 * e + 2 * M * ((K : ℝ) + (L : ℝ)) * (m : ℝ) := add_le_add hA hB

end

end Work.EKLComp.ErgMax
