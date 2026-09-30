import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.SD.window_helpers
import Submission.Work.BMF.SD.window_sum_ge
import Submission.Work.BMF.SD.geo_grid_exists

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

open Finset Real

set_option linter.unusedVariables false in
/-- Geometric window mass: under the Mertens-type lower bound `hMert` for the reciprocal prime
sum, whenever `log Q` is large enough compared with `exp (4K+CM+1) · (log P + log T + 2)`,
there is a ladder of geometric windows `[P (7/5)^j, P (7/5)^{j+1}]`, `j₀ ≤ j ≤ N-1`, lying inside
`[max(P,T), Q]` whose total reciprocal-prime mass is at least `4K`. -/
theorem geo_window_mass_lower2 (P Q T K CM : ℝ) (h2P : 2 ≤ P) (hPQ : P ≤ Q)
    (hPQ2 : 7 * P ≤ 5 * Q) (hT : 1 ≤ T) (hK : 0 < K)
    (hMert : ∀ A B : ℝ, 2 ≤ A → A ≤ B →
      Real.log (Real.log B / Real.log A) - CM ≤
        ∑ p ∈ Work.BMF.primesIn A B, (1 : ℝ) / (p : ℝ))
    (hA : Real.exp (4 * K + CM + 1) * (Real.log P + Real.log T + 2) + 2 ≤ Real.log Q) :
    ∃ N j₀ : ℕ, j₀ + 1 ≤ N ∧
      (∀ j ∈ Finset.Icc j₀ (N - 1), T ≤ P * (7 / 5) ^ j) ∧
      (∀ j ∈ Finset.Icc j₀ (N - 1), P ≤ P * (7 / 5) ^ j) ∧
      (∀ j ∈ Finset.Icc j₀ (N - 1), P * (7 / 5) ^ (j + 1) ≤ Q) ∧
      4 * K ≤ ∑ j ∈ Finset.Icc j₀ (N - 1),
        ∑ p ∈ Work.BMF.primesIn (P * (7 / 5) ^ j) (P * (7 / 5) ^ (j + 1)),
          (1 : ℝ) / (p : ℝ) := by
  have hPpos : 0 < P := by linarith
  have hQpos : 0 < Q := lt_of_lt_of_le (by linarith : (0 : ℝ) < P) hPQ
  -- `CM ≥ 0`, since the interval `[5/2, 5/2]` contains no prime
  have hCM0 : 0 ≤ CM := by
    have h := hMert (5/2) (5/2) (by norm_num) le_rfl
    have hlog52 : Real.log (5/2) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    have h1 : Real.log (Real.log (5/2) / Real.log (5/2)) = 0 := by
      rw [div_self hlog52, Real.log_one]
    have h2 : (∑ p ∈ Work.BMF.primesIn (5/2) (5/2), (1:ℝ)/(p:ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      exfalso
      rw [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc] at hp
      have hc : ⌈(5/2:ℝ)⌉₊ = 3 := by norm_num
      have hf : ⌊(5/2:ℝ)⌋₊ = 2 := by norm_num
      omega
    rw [h1, h2] at h
    linarith
  have hE1 : 1 ≤ Real.exp (4*K + CM + 1) := by
    rw [Real.one_le_exp_iff]
    linarith
  have hSnn : 0 ≤ Real.log P + Real.log T + 2 := by
    have hp : 0 ≤ Real.log P := Real.log_nonneg (by linarith)
    have ht : 0 ≤ Real.log T := Real.log_nonneg hT
    linarith
  -- `log Q` is at least `log P + log T + 4`
  have hlogQ2 : Real.log P + Real.log T + 4 ≤ Real.log Q := by
    have hmul : Real.log P + Real.log T + 2 ≤
        Real.exp (4*K+CM+1) * (Real.log P + Real.log T + 2) := by
      have := mul_le_mul_of_nonneg_right hE1 hSnn
      simpa using this
    linarith [hA, hmul]
  -- hence `Q ≥ P T e⁴`
  have hQ4 : P * T * Real.exp 4 ≤ Q := by
    have h5 : Real.exp (Real.log P + Real.log T + 4) ≤ Real.exp (Real.log Q) :=
      Real.exp_le_exp.mpr hlogQ2
    rw [Real.exp_add, Real.exp_add, Real.exp_log hPpos, Real.exp_log (by linarith : 0 < T),
      Real.exp_log hQpos] at h5
    simpa using h5
  obtain ⟨N, j₀, hjN, hTle, hPle, hbQ, hratio⟩ :=
    geo_grid_exists P Q T K CM h2P hT hQ4 hA
  set A : ℝ := P * (7/5)^j₀ with hAdef
  set B : ℝ := P * (7/5)^N with hBdef
  have hA2 : 2 ≤ A := by
    rw [hAdef]
    have h1 : (1:ℝ) ≤ (7/5 : ℝ)^j₀ := one_le_pow₀ (by norm_num)
    calc (2:ℝ) = 2 * 1 := by ring
      _ ≤ P * (7/5 : ℝ)^j₀ := mul_le_mul h2P h1 (by norm_num) (by linarith)
  have hAleB : A ≤ B := by
    rw [hAdef, hBdef]
    apply mul_le_mul_of_nonneg_left _ hPpos.le
    exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 7/5) (by omega : j₀ ≤ N)
  -- the Mertens bound on the full interval `[A, B]`
  have hsum_ge : 4*K ≤ ∑ p ∈ Work.BMF.primesIn A B, (1:ℝ)/(p:ℝ) := by
    have hmert := hMert A B hA2 hAleB
    have hg : 4*K + CM < Real.log (Real.log B / Real.log A) := by
      have := Real.log_lt_log (Real.exp_pos (4*K+CM)) hratio
      rwa [Real.log_exp] at this
    linarith
  -- the geometric windows dominate the full interval
  have hwin : (∑ p ∈ Work.BMF.primesIn A B, (1:ℝ)/(p:ℝ))
      ≤ ∑ j ∈ Finset.Icc j₀ (N - 1),
          ∑ p ∈ Work.BMF.primesIn (P * (7/5)^j) (P * (7/5)^(j+1)), (1:ℝ)/(p:ℝ) := by
    have := window_sum_ge (r := (7/5:ℝ)) (P := P) (by norm_num) (by norm_num) hPpos
      (j₀ := j₀) (N := N) hjN (fun p => (1:ℝ)/(p:ℝ)) (fun p => by positivity)
    simpa [hAdef, hBdef] using this
  exact ⟨N, j₀, hjN, hTle, hPle, hbQ, le_trans hsum_ge hwin⟩

end Work.BMF.SD
