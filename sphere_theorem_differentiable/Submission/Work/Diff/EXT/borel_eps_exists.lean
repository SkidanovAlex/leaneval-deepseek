import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Existence of a Borel-style cutoff scale `ε`

Given nonnegative "coefficient" data `Cap a` and `M n b`, this file produces a sequence
`ε : ℕ → ℝ` with `0 < ε n ≤ 1` such that for every `n`, `j`, `a` with `2(j+1) ≤ n` and `a ≤ j`

`(j.choose a) * Cap a * M n (j-a) * (ε n)^(n-a) ≤ (1/2)^n / (j+1)`.

The construction is a finite-sum pigeonhole: for fixed `n` the admissible pairs `(j,a)` all lie in
the box `range (n+1) × range (n+1)`, and we set

`ε n = 1 / (1 + ∑ p in box, c p / t p)`

where `c p` is the coefficient and `t p` the right-hand side.  Since `ε n ≤ t p / (c p + 1)` for each
pair in the box and the exponent `n - a ≥ 1`, the required estimate follows.  This is the standard
device for turning finitely many "make it small enough" conditions, one for each of infinitely many
scales, into a single sequence.
-/

namespace Work.Diff.EXT

/-- The finite box of indices `(j,a)` with `j,a ≤ n`. -/
private noncomputable def bepsBox (n : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (n + 1) ×ˢ Finset.range (n + 1)

/-- The coefficient `(j.choose a) * Cap a * M n (j-a)` attached to a pair `p = (j,a)`. -/
private noncomputable def bepsF (Cap : ℕ → ℝ) (M : ℕ → ℕ → ℝ) (n : ℕ) (p : ℕ × ℕ) : ℝ :=
  (p.1.choose p.2 : ℝ) * Cap p.2 * M n (p.1 - p.2)

/-- The target value `(1/2)^n / (j+1)` attached to a pair `p = (j,a)` (with `j = p.1`). -/
private noncomputable def bepsT (n : ℕ) (p : ℕ × ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ n / ((p.1 : ℝ) + 1)

/-- The denominator of the cutoff: `1` plus the sum of all coefficient/target ratios over the box. -/
private noncomputable def bepsDen (Cap : ℕ → ℝ) (M : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  1 + Finset.sum (bepsBox n) (fun p => bepsF Cap M n p / bepsT n p)

theorem borel_eps_exists
    (Cap : ℕ → ℝ) (M : ℕ → ℕ → ℝ) (hCap : ∀ a, 0 ≤ Cap a) (hM : ∀ n b, 0 ≤ M n b) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ (∀ n, ε n ≤ 1) ∧
      ∀ n j a, 2 * (j + 1) ≤ n → a ≤ j →
        (j.choose a : ℝ) * Cap a * M n (j - a) * (ε n) ^ (n - a) ≤ ((1 : ℝ) / 2) ^ n / (j + 1)
      := by
  -- Nonnegativity of the boxes' coefficients.
  have hFnn : ∀ n p, 0 ≤ bepsF Cap M n p := by
    intro n p
    simp only [bepsF]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCap _)) (hM _ _)
  -- Positivity of the target values.
  have hTpos : ∀ n p, 0 < bepsT n p := by
    intro n p
    simp only [bepsT]
    exact div_pos (pow_pos (by norm_num) n) (by positivity)
  -- The sum is nonnegative, hence the denominator is bounded below by `1` and is positive.
  have hSum_nn : ∀ n, 0 ≤ Finset.sum (bepsBox n) (fun p => bepsF Cap M n p / bepsT n p) := by
    intro n
    exact Finset.sum_nonneg (fun p _ => div_nonneg (hFnn n p) (le_of_lt (hTpos n p)))
  have hDenpos : ∀ n, 0 < bepsDen Cap M n := by
    intro n
    simp only [bepsDen]
    have := hSum_nn n
    linarith
  have hDen_ge1 : ∀ n, 1 ≤ bepsDen Cap M n := by
    intro n
    simp only [bepsDen]
    have := hSum_nn n
    linarith
  have heps_pos : ∀ n, 0 < 1 / bepsDen Cap M n := fun n => div_pos one_pos (hDenpos n)
  have heps_le1 : ∀ n, 1 / bepsDen Cap M n ≤ 1 := by
    intro n
    rw [div_le_one (hDenpos n)]
    exact hDen_ge1 n
  refine ⟨fun n => 1 / bepsDen Cap M n, heps_pos, heps_le1, ?_⟩
  intro n j a h1 h2
  -- The pair `(j,a)` lies in the box because `2(j+1) ≤ n` and `a ≤ j`.
  have hmem : (j, a) ∈ bepsBox n := by
    rw [bepsBox, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  -- Each single coefficient/target ratio is at most the whole sum.
  have hsingle : bepsF Cap M n (j, a) / bepsT n (j, a)
      ≤ Finset.sum (bepsBox n) (fun p => bepsF Cap M n p / bepsT n p) :=
    Finset.single_le_sum (fun p _ => div_nonneg (hFnn n p) (le_of_lt (hTpos n p))) hmem
  -- Hence the coefficient is at most `target * denominator`.
  have hle : bepsF Cap M n (j, a) ≤ bepsT n (j, a) * bepsDen Cap M n := by
    rw [bepsDen]
    have h1' : bepsF Cap M n (j, a)
        ≤ (Finset.sum (bepsBox n) (fun p => bepsF Cap M n p / bepsT n p)) * bepsT n (j, a) :=
      (div_le_iff₀ (hTpos n (j, a))).mp hsingle
    have h2' : (Finset.sum (bepsBox n) (fun p => bepsF Cap M n p / bepsT n p)) * bepsT n (j, a)
        ≤ (1 + Finset.sum (bepsBox n) (fun p => bepsF Cap M n p / bepsT n p)) * bepsT n (j, a) :=
      mul_le_mul_of_nonneg_right (by linarith [hSum_nn n]) (le_of_lt (hTpos n (j, a)))
    calc bepsF Cap M n (j, a)
        ≤ (Finset.sum (bepsBox n) (fun p => bepsF Cap M n p / bepsT n p)) * bepsT n (j, a) := h1'
      _ ≤ (1 + Finset.sum (bepsBox n) (fun p => bepsF Cap M n p / bepsT n p)) * bepsT n (j, a) := h2'
      _ = bepsT n (j, a) * (1 + Finset.sum (bepsBox n) (fun p => bepsF Cap M n p / bepsT n p)) := by ring
  -- The exponent is at least `1` under the constraints.
  have hk1 : 1 ≤ n - a := by omega
  -- Since `ε n ≤ 1`, raising it to a positive power only decreases it.
  have hpow : (1 / bepsDen Cap M n) ^ (n - a) ≤ 1 / bepsDen Cap M n := by
    have := pow_le_pow_of_le_one (le_of_lt (heps_pos n)) (heps_le1 n) hk1
    simpa using this
  have hstep1 : bepsF Cap M n (j, a) * (1 / bepsDen Cap M n) ^ (n - a)
      ≤ bepsF Cap M n (j, a) * (1 / bepsDen Cap M n) :=
    mul_le_mul_of_nonneg_left hpow (hFnn n (j, a))
  have hstep2 : bepsF Cap M n (j, a) * (1 / bepsDen Cap M n) ≤ bepsT n (j, a) := by
    have h2' := (div_le_iff₀ (hDenpos n)).mpr hle
    rw [mul_one_div]
    exact h2'
  have hTeq : bepsT n (j, a) = ((1 : ℝ) / 2) ^ n / (j + 1) := by
    simp only [bepsT]
  calc (j.choose a : ℝ) * Cap a * M n (j - a) * (1 / bepsDen Cap M n) ^ (n - a)
      = bepsF Cap M n (j, a) * (1 / bepsDen Cap M n) ^ (n - a) := by simp only [bepsF]
    _ ≤ bepsF Cap M n (j, a) * (1 / bepsDen Cap M n) := hstep1
    _ ≤ bepsT n (j, a) := hstep2
    _ = ((1 : ℝ) / 2) ^ n / (j + 1) := hTeq

end Work.Diff.EXT
