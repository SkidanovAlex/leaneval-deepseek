import Mathlib

/-!
# FI §15: the concrete cut-off family for the sharp-cut splitting

The frozen `VcutMod` uses the **sharp** cut `1{X < d ∧ 4dX < |Δ|}`.  Writing
`t = |Δ(z₁,z₂)|/(4Xd)` (an integer multiple of `1/X` on the pairs actually summed, because
`4d ∣ |Δ|`), the sharp cut is `1{X < d}·1{t > 1}`.

A smooth function can *never* equal a sharp indicator exactly, so **no** smooth `u` makes
`E = u − 1{t>1}` smooth: the jump of `1{t>1}` at `t = 1` is inherited by `E`.  The splitting used
here therefore keeps a **non-smooth** remainder `S15E = S15u − 1{t>1}` (supported on the bounded
factor range `1 ≤ t ≤ 3/2`), which is bounded *crudely* (its support is a bounded `q`-range
`q = |Δ|/(4d) ∈ [X, 3X/2]`, so at most `τ(|Δ|/4)` moduli per pair), while the smooth pieces

`S15psi τ = S15u (2τ) − S15u τ`   (`support ⊆ (1/2, 3/2) ⊂ (1/2, 5/2)`)

carry the main terms and are handled by `Work.FIArea4.S15_piece_bound`.

This module supplies the concrete `S15u`, `S15psi`, `S15E` and their elementary properties.
-/

namespace Work.FIArea4

open scoped BigOperators ContDiff

noncomputable section

/-- The concrete smooth cut-off: `S15u t = smoothTransition (2(t−1))`, so `0` for `t ≤ 1` and `1`
for `t ≥ 3/2`. -/
def S15u (t : ℝ) : ℝ := Real.smoothTransition (2 * (t - 1))

/-- The smooth dyadic bump of the splitting: `S15psi τ = S15u (2τ) − S15u τ`. -/
def S15psi (τ : ℝ) : ℝ := S15u (2 * τ) - S15u τ

/-- The **non-smooth** remainder of the splitting: `S15E t = S15u t − 1{t > 1}`, supported on
`[1, 3/2]`. -/
def S15E (t : ℝ) : ℝ := S15u t - (if 1 < t then 1 else 0)

lemma S15u_contDiff : ContDiff ℝ (⊤ : ℕ∞) S15u := by
  unfold S15u; fun_prop

lemma S15u_nonneg (t : ℝ) : 0 ≤ S15u t := Real.smoothTransition.nonneg _

lemma S15u_le_one (t : ℝ) : S15u t ≤ 1 := Real.smoothTransition.le_one _

lemma S15u_zero {t : ℝ} (h : t ≤ 1) : S15u t = 0 := by
  unfold S15u
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

lemma S15u_one {t : ℝ} (h : 3 / 2 ≤ t) : S15u t = 1 := by
  unfold S15u
  exact Real.smoothTransition.one_of_one_le (by linarith)

lemma S15u_mono : Monotone S15u := by
  intro t₁ t₂ h
  unfold S15u
  exact Real.smoothTransition.monotone (by linarith)

lemma S15psi_contDiff : ContDiff ℝ (⊤ : ℕ∞) S15psi := by
  unfold S15psi; exact (S15u_contDiff.comp (by fun_prop)).sub S15u_contDiff

lemma S15psi_nonneg (τ : ℝ) : 0 ≤ S15psi τ := by
  rcases le_total τ 0 with h | h
  · have h1 : S15u (2 * τ) = 0 := S15u_zero (by linarith)
    have h2 : S15u τ = 0 := S15u_zero (by linarith)
    unfold S15psi; rw [h1, h2]; norm_num
  · unfold S15psi
    exact sub_nonneg.mpr (S15u_mono (by linarith))

lemma S15psi_le_one (τ : ℝ) : S15psi τ ≤ 1 := by
  rcases le_total τ 0 with h | h
  · have h1 : S15u (2 * τ) = 0 := S15u_zero (by linarith)
    have h2 : S15u τ = 0 := S15u_zero (by linarith)
    unfold S15psi; rw [h1, h2]; norm_num
  · unfold S15psi
    have h2 := S15u_nonneg τ
    have h3 := S15u_le_one (2 * τ)
    linarith

lemma S15psi_support {τ : ℝ} (h : S15psi τ ≠ 0) : 1 / 2 < τ ∧ τ < 3 / 2 := by
  constructor
  · by_contra hc
    rw [not_lt] at hc
    have h1 : S15u (2 * τ) = 0 := S15u_zero (by linarith)
    have h2 : S15u τ = 0 := S15u_zero (by linarith)
    exact h (by unfold S15psi; rw [h1, h2]; ring)
  · by_contra hc
    rw [not_lt] at hc
    have h1 : S15u (2 * τ) = 1 := S15u_one (by linarith)
    have h2 : S15u τ = 1 := S15u_one (by linarith)
    exact h (by unfold S15psi; rw [h1, h2]; ring)

lemma S15E_abs_le_one (t : ℝ) : |S15E t| ≤ 1 := by
  unfold S15E
  have h0 := S15u_nonneg t
  have h1 := S15u_le_one t
  split_ifs <;> simp only [abs_le] <;> constructor <;> linarith

lemma S15E_support {t : ℝ} (h : S15E t ≠ 0) : 1 ≤ t ∧ t ≤ 3 / 2 := by
  constructor
  · by_contra hc
    rw [not_le] at hc
    have h1 : S15u t = 0 := S15u_zero (le_of_lt hc)
    have h2 : (if 1 < t then (1 : ℝ) else 0) = 0 := by rw [if_neg (not_lt.mpr (le_of_lt hc))]
    exact h (by unfold S15E; rw [h1, h2]; ring)
  · by_contra hc
    rw [not_le] at hc
    have h1 : S15u t = 1 := S15u_one (le_of_lt hc)
    have h2 : (if 1 < t then (1 : ℝ) else 0) = 1 := by rw [if_pos (by linarith)]
    exact h (by unfold S15E; rw [h1, h2]; ring)

/-- The exact relation between `S15u`, `S15psi` and `S15E` at the level of the cut: for `t > 0` and
`2^J ≥ t`, `Σ_{j<J} S15psi (t/2^{j+1}) − S15E t = 1{t > 1}`. -/
lemma S15psi_sum_eq {t : ℝ} (ht : 0 < t) {J : ℕ} (hJ : t ≤ 2 ^ J) :
    (∑ j ∈ Finset.range J, S15psi (t / 2 ^ (j + 1))) - S15E t = (if 1 < t then 1 else 0) := by
  have htel : ∀ N : ℕ, ∑ j ∈ Finset.range N, S15psi (t / 2 ^ (j + 1))
      = S15u t - S15u (t / 2 ^ N) := by
    intro N
    have h1 : ∀ j : ℕ, S15psi (t / 2 ^ (j + 1)) = S15u (t / 2 ^ j) - S15u (t / 2 ^ (j + 1)) := by
      intro j
      unfold S15psi
      have h2 : 2 * (t / 2 ^ (j + 1)) = t / 2 ^ j := by
        have hpos : (0 : ℝ) < 2 ^ (j + 1) := pow_pos (by norm_num) _
        field_simp
        ring
      rw [h2]
    simp only [h1]
    have h := Finset.sum_range_sub' (fun j : ℕ => S15u (t / 2 ^ j)) N
    simpa using h
  rw [htel J]
  have hzero : S15u (t / 2 ^ J) = 0 := by
    refine S15u_zero ?_
    rw [div_le_iff₀ (pow_pos (by norm_num : (0:ℝ) < 2) J)]
    nlinarith [hJ]
  rw [hzero]
  unfold S15E
  ring

end

end Work.FIArea4
