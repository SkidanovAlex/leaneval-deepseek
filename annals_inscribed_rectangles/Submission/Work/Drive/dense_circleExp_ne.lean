import Mathlib

/-!
# Density of the complement of the "diagonal" for `Circle.exp`

`Circle.exp : ℝ → Circle` satisfies `Circle.exp x = Circle.exp y ↔ ∃ k : ℤ, x = y + k * (2π)`.
Consequently the set of `p : ℝ²` with `Circle.exp (p 0) ≠ Circle.exp (p 1)` is dense in `ℝ²`:
given any `p` one perturbs the first coordinate by a small amount `δ` avoiding the countable
discrete set `2πℤ - (p 0 - p 1)`.
-/

namespace Work.Drive

open Metric

/-- For every `x : ℝ` and every `ε > 0` there is `0 < δ < ε` with `δ ∉ 2πℤ - x`.  Explicitly, if
`n = ⌊x / 2π⌋ + 1` then `c = 2π n - x ∈ (0, 2π]` is the smallest positive element of `2πℤ - x`, and
one may take `δ = min c ε / 2`. -/
lemma exists_pos_lt_notMem_zsmul (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ ∀ k : ℤ, δ ≠ (k : ℝ) * (2 * Real.pi) - x := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  set r : ℝ := x / (2 * Real.pi) with hr
  set n : ℤ := ⌊r⌋ + 1 with hn
  set c : ℝ := (n : ℝ) * (2 * Real.pi) - x with hc
  have hnr : r < (n : ℝ) := by
    have h := Int.lt_floor_add_one r
    rw [hn]; push_cast; linarith
  have hc_pos : 0 < c := by
    have h1 : x < (n : ℝ) * (2 * Real.pi) := by
      have h2 := (div_lt_iff₀ hpi).mp (by rw [← hr]; exact hnr)
      simpa using h2
    rw [hc]; linarith
  have hc_le : c ≤ 2 * Real.pi := by
    have h1 : ((n : ℝ) - 1) * (2 * Real.pi) ≤ x := by
      have h2 : ((n : ℝ) - 1) ≤ r := by
        have h := Int.floor_le r
        rw [hn]; push_cast at h ⊢; linarith
      calc ((n : ℝ) - 1) * (2 * Real.pi) ≤ r * (2 * Real.pi) :=
            mul_le_mul_of_nonneg_right h2 (le_of_lt hpi)
        _ = x := by rw [hr, div_mul_cancel₀ x hpi.ne']
    rw [hc]; linarith
  refine ⟨min c ε / 2, ?_, ?_, ?_⟩
  · have h : 0 < min c ε := lt_min hc_pos hε
    linarith
  · have h : min c ε ≤ ε := min_le_right _ _
    linarith
  · intro k hk
    have hδpos : 0 < min c ε / 2 := by
      have h : 0 < min c ε := lt_min hc_pos hε
      linarith
    have hkgt : r < (k : ℝ) := by
      have h1 : x < (k : ℝ) * (2 * Real.pi) := by linarith [hk, hδpos]
      rw [hr]
      exact (div_lt_iff₀ hpi).mpr h1
    have hnle : n ≤ k := by
      have hnot : ¬ ((k : ℝ) ≤ r) := not_le.mpr hkgt
      have hnot2 : ¬ k ≤ ⌊r⌋ := fun h => hnot ((Int.le_floor (a := r) (z := k)).mp h)
      have hlt : ⌊r⌋ < k := not_le.mp hnot2
      have h3 : ⌊r⌋ + 1 ≤ k := Int.lt_iff_add_one_le.mp hlt
      rwa [hn]
    have hck : c ≤ (k : ℝ) * (2 * Real.pi) - x := by
      have hcast : (n : ℝ) ≤ (k : ℝ) := Int.cast_le.mpr hnle
      have hmul := mul_le_mul_of_nonneg_right hcast (le_of_lt hpi)
      rw [hc]; linarith
    have hδc : min c ε / 2 < c := by
      have h1 : min c ε ≤ c := min_le_left _ _
      linarith
    linarith [hck, hδc, hk]

theorem dense_circleExp_ne :
    Dense {p : EuclideanSpace ℝ (Fin 2) | Circle.exp (p 0) ≠ Circle.exp (p 1)} := by
  rw [dense_iff]
  intro p r hr
  obtain ⟨δ, hδpos, hδlt, hδne⟩ := exists_pos_lt_notMem_zsmul (p 0 - p 1) hr
  set y : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then p 0 + δ else p 1) with hy
  refine ⟨y, ?_, ?_⟩
  · rw [mem_ball, dist_comm]
    have hdist : dist p y = δ := by
      rw [hy, EuclideanSpace.dist_eq]
      simp [Fin.sum_univ_two, Real.dist_eq, Real.sqrt_sq_eq_abs, abs_of_pos hδpos]
    rw [hdist]; exact hδlt
  · have hy0 : y 0 = p 0 + δ := by rw [hy]; simp
    have hy1 : y 1 = p 1 := by rw [hy]; simp
    intro hcon
    rw [Circle.exp_eq_exp] at hcon
    obtain ⟨m, hm⟩ := hcon
    rw [hy0, hy1] at hm
    exact hδne m (by linarith)

end Work.Drive
