import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_divisor_le_L
import Submission.Commons.NumberTheory.DirichletCharacter.L_window_divisor_bound
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_window_cover
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_ball_divisor_le_L_ball

open Complex DirichletCharacter Metric
open scoped Real Topology BigOperators
set_option maxHeartbeats 0

noncomputable section

namespace Commons.NumberTheory.Linnik

/-- The number of unit windows needed to cover `[t−R−1, t+R+1]` is bounded by `4R` for `R ≥ 2`. -/
lemma window_count_bound {R : ℝ} (hR : 2 ≤ R) :
    ((Nat.ceil (2 * R + 2) + 1 : ℕ) : ℝ) ≤ 4 * R := by
  have h1 : (Nat.ceil (2 * R + 2) : ℝ) ≤ 2 * R + 3 := by
    have hc : (Nat.ceil (2 * R + 2) : ℝ) < 2 * R + 2 + 1 :=
      Nat.ceil_lt_add_one (a := 2 * R + 2) (by positivity : 0 ≤ 2 * R + 2)
    nlinarith
  have hcast : ((Nat.ceil (2 * R + 2) + 1 : ℕ) : ℝ) = (Nat.ceil (2 * R + 2) : ℝ) + 1 := by
    norm_num [Nat.cast_add, Nat.cast_one]
  rw [hcast]
  nlinarith [h1, hR]

/-- A window centre `m j = t − (R+1) + j` (`j ≤ n ≤ 2R+3`) satisfies `2 + |m j| ≤ 3·(2+|t|+R)`. -/
lemma window_center_le {R t : ℝ} {j n : ℕ} (hR : 2 ≤ R) (hj : j ≤ n)
    (hn : (n : ℝ) ≤ 2 * R + 3) :
    2 + |t - (R + 1) + (j : ℝ)| ≤ 3 * (2 + |t| + R) := by
  have htri1 : |(t - (R + 1)) + (j : ℝ)| ≤ |t - (R + 1)| + |(j : ℝ)| :=
    abs_add_le (t - (R + 1)) (j : ℝ)
  have htri2 : |t - (R + 1)| ≤ |t| + (R + 1) := by
    have h := abs_sub t (R + 1)
    -- |t - (R+1)| ≤ |t| + |R+1|  = |t| + (R+1)
    have hR1 : |R + 1| = R + 1 := abs_of_nonneg (by linarith)
    have h' : |t - (R + 1)| ≤ |t| + |R + 1| := h
    rw [hR1] at h'
    exact h'
  have htri3 : |t - (R + 1)| + |(j : ℝ)| ≤ |t| + (R + 1) + (j : ℝ) := by
    have hj0 : |(j : ℝ)| = (j : ℝ) := abs_of_nonneg (by exact_mod_cast (Nat.zero_le j))
    rw [hj0]
    linarith
  have htri : |t - (R + 1) + (j : ℝ)| ≤ |t| + (R + 1) + (j : ℝ) := by linarith
  have htri4 : 2 + |t - (R + 1) + (j : ℝ)| ≤ 2 + |t| + (R + 1) + (j : ℝ) := by linarith
  have hj' : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
  have hj2 : (j : ℝ) ≤ 2 * R + 3 := by linarith
  nlinarith [htri4, abs_nonneg t, hj2, hR]

/-- The window centre in the distributed-cast form equals the whole-cast form. -/
lemma window_center_eq (t R a : ℝ) :
    ((2 : ℂ) + Complex.I * (((t : ℂ) - ((R : ℂ) + 1)) + (a : ℂ))) =
      (2 : ℂ) + Complex.I * ((t - (R + 1) + a) : ℂ) := by
  simp

/-- Centre expressed via `m` (with `m k = t - (R+1) + k`) matches the distributed form. -/
lemma window_center_eq_m (t R : ℝ) (j : ℕ) (m : ℕ → ℝ) (hm : ∀ k : ℕ, m k = t - (R + 1) + (k : ℝ)) :
    ((2 : ℂ) + Complex.I * (((t : ℂ) - ((R : ℂ) + 1)) + ((j : ℝ) : ℂ))) =
      (2 : ℂ) + Complex.I * ((m j : ℝ) : ℂ) := by
  rw [hm j]
  simp

/-- Divisor sums over closed balls are unchanged when the centre is rewritten. -/
lemma sum_divisor_center_eq {f : ℂ → ℂ} {a b : ℂ} (h : a = b) (ρ : ℝ) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall a ρ)) u : ℤ) : ℝ)) =
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall b ρ)) u : ℤ) : ℝ)) := by
  rw [h]

/-- **Local zero count of the completed Dirichlet L-function in a disk centred on Re = 2.** -/
theorem completedL_local_zeroCount {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ c : ℝ, ∀ R : ℝ, 2 ≤ R → ∀ t : ℝ,
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) R)) u : ℤ) : ℝ)) ≤
        c * R * (Real.log (2 + |t| + R) + Real.log (N : ℝ) + 2) := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let L : ℂ → ℂ := DirichletCharacter.LFunction χ
  rcases Commons.NumberTheory.DirichletCharacter.L_window_divisor_bound χ hχ hχprim with ⟨cw, hcw, hwin⟩
  let c : ℝ := 4 * cw * (1 + Real.log 3 / 2)
  refine ⟨c, ?_⟩
  intro R hR t
  let n : ℕ := Nat.ceil (2 * R + 2)
  let J : Finset ℕ := Finset.range (n + 1)
  let m : ℕ → ℝ := fun j => t - (R + 1) + (j : ℝ)
  let X : ℝ := Real.log (2 + |t| + R) + Real.log (N : ℝ) + 2
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
  have hN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hX2 : 2 ≤ X := by
    dsimp [X]
    have h1 : 0 ≤ Real.log (2 + |t| + R) := by
      refine Real.log_nonneg ?_
      linarith [abs_nonneg t]
    linarith
  have hn_le : (n : ℝ) ≤ 2 * R + 3 := by
    dsimp [n]
    have hc : (Nat.ceil (2 * R + 2) : ℝ) < 2 * R + 2 + 1 :=
      Nat.ceil_lt_add_one (a := 2 * R + 2) (by positivity : 0 ≤ 2 * R + 2)
    nlinarith
  have hcard : ((n + 1 : ℕ) : ℝ) ≤ 4 * R := by
    dsimp [n]
    exact window_count_bound hR
  -- window bound at center m j
  have hwin' : ∀ j : ℕ, j ≤ n →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor L
          (Metric.closedBall ((2 : ℂ) + Complex.I * ((m j) : ℂ)) 2.5)) u : ℤ) : ℝ)) ≤
        cw * (Real.log (2 + |m j|) + Real.log (N : ℝ) + 2) := by
    intro j hj
    have h0 := hwin (m j)
    dsimp [m] at h0 ⊢
    simpa using h0
  -- ball Λ-sum ≤ ball L-sum per window
  have hΛL : ∀ j : ℕ, j ≤ n →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ
          (Metric.closedBall ((2 : ℂ) + Complex.I * ((m j) : ℂ)) 2.5)) u : ℤ) : ℝ)) ≤
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor L
          (Metric.closedBall ((2 : ℂ) + Complex.I * ((m j) : ℂ)) 2.5)) u : ℤ) : ℝ)) := by
    intro j hj
    have hb := Commons.NumberTheory.DirichletCharacter.completedL_ball_divisor_le_L_ball
      χ hχ hχprim ((2 : ℂ) + Complex.I * ((m j) : ℂ)) 2.5
    simpa [Λ, L] using hb
  -- per-window log control
  have hlogm : ∀ j : ℕ, j ≤ n →
      Real.log (2 + |m j|) ≤ Real.log (2 + |t| + R) + Real.log 3 := by
    intro j hj
    have hpos1 : 0 < 2 + |m j| := by positivity
    have hle : 2 + |m j| ≤ 3 * (2 + |t| + R) := by
      have hb := window_center_le (R := R) (t := t) (j := j) (n := n) hR hj hn_le
      simpa [m] using hb
    have hpos2 : 0 < 3 * (2 + |t| + R) := by positivity
    have h := Real.log_le_log hpos1 hle
    rw [show 3 * (2 + |t| + R) = (2 + |t| + R) * 3 by ring] at h
    rw [Real.log_mul (ne_of_gt (by positivity : 0 < 2 + |t| + R))
        (ne_of_gt (by norm_num : 0 < (3 : ℝ)))] at h
    exact h
  have hEj : ∀ j : ℕ, j ≤ n →
      (Real.log (2 + |m j|) + Real.log (N : ℝ) + 2) ≤ X + Real.log 3 := by
    intro j hj
    have h0 := hlogm j hj
    dsimp [X]
    linarith
  -- bound of the sum over windows
  have hsum_Λ_le : (∑ j ∈ J, (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ
          (Metric.closedBall ((2 : ℂ) + Complex.I * ((m j) : ℂ)) 2.5)) u : ℤ) : ℝ))) ≤
      ∑ j ∈ J, (∑ᶠ u : ℂ, (((MeromorphicOn.divisor L
          (Metric.closedBall ((2 : ℂ) + Complex.I * ((m j) : ℂ)) 2.5)) u : ℤ) : ℝ)) := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    exact hΛL j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have hsum_L_le : (∑ j ∈ J, (∑ᶠ u : ℂ, (((MeromorphicOn.divisor L
          (Metric.closedBall ((2 : ℂ) + Complex.I * ((m j) : ℂ)) 2.5)) u : ℤ) : ℝ))) ≤
      ∑ j ∈ J, cw * (Real.log (2 + |m j|) + Real.log (N : ℝ) + 2) := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    exact hwin' j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have hcw0 : 0 ≤ cw := hcw
  have hsum1 : (∑ j ∈ J, cw * (Real.log (2 + |m j|) + Real.log (N : ℝ) + 2)) ≤
      ((n + 1 : ℕ) : ℝ) * (cw * (X + Real.log 3)) := by
    have h1 : ∀ j ∈ J, cw * (Real.log (2 + |m j|) + Real.log (N : ℝ) + 2) ≤
        cw * (X + Real.log 3) := by
      intro j hj
      exact mul_le_mul_of_nonneg_left (hEj j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))) hcw0
    have h2 : (∑ j ∈ J, cw * (Real.log (2 + |m j|) + Real.log (N : ℝ) + 2)) ≤
        ∑ j ∈ J, cw * (X + Real.log 3) := Finset.sum_le_sum h1
    have h3 : (∑ j ∈ J, cw * (X + Real.log 3)) = ((n + 1 : ℕ) : ℝ) * (cw * (X + Real.log 3)) := by
      rw [Finset.sum_const]
      simp [J, nsmul_eq_mul]
    exact le_trans h2 (le_of_eq h3)
  have hsum2 : ((n + 1 : ℕ) : ℝ) * (cw * (X + Real.log 3)) ≤ c * R * X := by
    have h2 : 0 ≤ cw * (X + Real.log 3) := by positivity
    have h3 : cw * (X + Real.log 3) ≤ (cw * (1 + Real.log 3 / 2)) * X := by
      have h34 : 0 ≤ cw := hcw
      have hX : 0 ≤ X := by linarith
      have hx1 : X + Real.log 3 ≤ (1 + Real.log 3 / 2) * X := by
        have hposlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
        nlinarith [hX2, hposlog]
      nlinarith
    calc
      ((n + 1 : ℕ) : ℝ) * (cw * (X + Real.log 3))
          ≤ (4 * R) * (cw * (X + Real.log 3)) := by
              exact mul_le_mul_of_nonneg_right hcard h2
      _ ≤ (4 * R) * ((cw * (1 + Real.log 3 / 2)) * X) := by
              exact mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 4 * R)
      _ = c * R * X := by
              dsimp [c]
              ring
  -- cover inequality
  have hcover := Commons.NumberTheory.DirichletCharacter.completedL_window_cover
    χ hχ hχprim (R := R) (t := t) hR
  have hcvr_m : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) R)) u : ℤ) : ℝ)) ≤
      ∑ j ∈ J, (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ
          (Metric.closedBall ((2 : ℂ) + Complex.I * ((m j : ℝ) : ℂ)) 2.5)) u : ℤ) : ℝ)) := by
    have hEqSum : (∑ j ∈ J, (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ
            (Metric.closedBall ((2 : ℂ) + Complex.I * (((t : ℂ) - ((R : ℂ) + 1)) + ((j : ℝ) : ℂ))) 2.5)) u : ℤ) : ℝ))) =
        (∑ j ∈ J, (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ
            (Metric.closedBall ((2 : ℂ) + Complex.I * ((m j : ℝ) : ℂ)) 2.5)) u : ℤ) : ℝ))) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact sum_divisor_center_eq (f := Λ) (ρ := 2.5)
        (window_center_eq_m t R j m (by intro k; rfl))
    exact hcover.trans_eq hEqSum
  have hgoal : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) R)) u : ℤ) : ℝ)) ≤ c * R * X := by
    calc
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) R)) u : ℤ) : ℝ))
          ≤ ∑ j ∈ J, (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ
              (Metric.closedBall ((2 : ℂ) + Complex.I * ((m j : ℝ) : ℂ)) 2.5)) u : ℤ) : ℝ)) := by
              exact hcvr_m
      _ ≤ ∑ j ∈ J, (∑ᶠ u : ℂ, (((MeromorphicOn.divisor L
              (Metric.closedBall ((2 : ℂ) + Complex.I * ((m j : ℝ) : ℂ)) 2.5)) u : ℤ) : ℝ)) := hsum_Λ_le
      _ ≤ ∑ j ∈ J, cw * (Real.log (2 + |m j|) + Real.log (N : ℝ) + 2) := hsum_L_le
      _ ≤ ((n + 1 : ℕ) : ℝ) * (cw * (X + Real.log 3)) := hsum1
      _ ≤ c * R * X := hsum2
  simpa [X] using hgoal

end Commons.NumberTheory.Linnik
