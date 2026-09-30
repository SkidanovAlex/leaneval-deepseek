import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- Given `delta > 0` and an interval `[u, u+W]` of length at least `(n+1)*delta`, there are
`n+1` distinct points of the lattice `delta * ℤ` inside `[u, u+W]`. -/
theorem exists_lattice_points {delta u W : ℝ} (hdelta : 0 < delta) {n : ℕ}
    (hn : ((n : ℝ) + 1) * delta ≤ W) :
    ∃ f : Fin (n + 1) → ℤ, Function.Injective (fun i => delta * (f i)) ∧
      ∀ i, u ≤ delta * (f i) ∧ delta * (f i) ≤ u + W := by
  -- `m` is the smallest integer with `delta * m ≥ u`.
  obtain ⟨m, hm1, hm2⟩ : ∃ m : ℤ, u / delta ≤ (m : ℝ) ∧ (m : ℝ) < u / delta + 1 :=
    ⟨⌈u / delta⌉, Int.le_ceil _, Int.ceil_lt_add_one _⟩
  refine ⟨fun i => m + (i.val : ℤ), ?_, ?_⟩
  · intro i j hij
    have hdelta_ne : delta ≠ 0 := ne_of_gt hdelta
    have h1 : ((m + (i.val : ℤ) : ℤ) : ℝ) = ((m + (j.val : ℤ) : ℤ) : ℝ) :=
      mul_left_cancel₀ hdelta_ne hij
    rw [Int.cast_add, Int.cast_add, Int.cast_natCast, Int.cast_natCast] at h1
    exact Fin.ext (Nat.cast_injective (add_left_cancel h1))
  · intro i
    refine ⟨?_, ?_⟩
    · -- lower bound: `delta * m ≥ u`
      have h0 : u ≤ delta * (m : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hm1 (le_of_lt hdelta)
        rwa [mul_div_cancel₀ u (ne_of_gt hdelta)] at h
      have hle : (m : ℝ) ≤ ((m + (i.val : ℤ) : ℤ) : ℝ) := by
        rw [Int.cast_add, Int.cast_natCast]
        exact le_add_of_nonneg_right (by positivity)
      calc u ≤ delta * (m : ℝ) := h0
        _ ≤ delta * ((m + (i.val : ℤ) : ℤ) : ℝ) :=
            mul_le_mul_of_nonneg_left hle (le_of_lt hdelta)
    · -- upper bound: `delta * m < u + delta`, and `i.val ≤ n` gives `delta * i.val ≤ delta * n`
      have hmn : ((i.val : ℝ)) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
      have hdm : delta * (m : ℝ) < u + delta := by
        have h : delta * (m : ℝ) < delta * (u / delta + 1) :=
          mul_lt_mul_of_pos_left hm2 hdelta
        rwa [mul_add, mul_div_cancel₀ u (ne_of_gt hdelta), mul_one] at h
      rw [Int.cast_add, Int.cast_natCast]
      nlinarith [hdm, hmn, hdelta, hn]

end Work.BMF
