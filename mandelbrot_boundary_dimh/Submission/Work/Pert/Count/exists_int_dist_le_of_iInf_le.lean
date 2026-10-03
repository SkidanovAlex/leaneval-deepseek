import Mathlib

namespace Work.Pert.Count

/-- Distance from a complex number to a real number, read as a complex number:
`dist z (t : ℂ) = √((z.re - t)^2 + z.im^2)`. -/
private lemma dist_ofReal_eq (z : ℂ) (t : ℝ) :
    dist z (t : ℂ) = Real.sqrt ((z.re - t) ^ 2 + z.im ^ 2) := by
  rw [Complex.dist_eq, Complex.norm_def, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im]
  congr 1
  ring

/-- The distance from `z` to the nearest integer (in the real direction) is
minimal among all distances `dist z (k : ℂ)`, `k : ℤ`. -/
private lemma exists_int_dist_le_all (z : ℂ) :
    ∃ m : ℤ, ∀ k : ℤ, dist z (m : ℂ) ≤ dist z (k : ℂ) := by
  -- the nearest integer to `z.re`
  set m : ℤ := ⌊z.re + (1 / 2 : ℝ)⌋ with hm
  have hmle : |z.re - (m : ℝ)| ≤ 1 / 2 := by
    have h1 : (m : ℝ) ≤ z.re + 1 / 2 := by rw [hm]; exact Int.floor_le _
    have h2 : z.re + 1 / 2 < (m : ℝ) + 1 := by rw [hm]; exact Int.lt_floor_add_one _
    rw [abs_le]
    constructor <;> linarith
  have hmin : ∀ k : ℤ, |z.re - (m : ℝ)| ≤ |z.re - (k : ℝ)| := by
    intro k
    by_cases hk : k = m
    · rw [hk]
    · -- for an integer `k ≠ m` the distance `|z.re - k|` is at least `1/2`
      have hone : (1 : ℝ) ≤ |(m : ℝ) - (k : ℝ)| := by
        have hne : m - k ≠ 0 := sub_ne_zero.mpr (Ne.symm hk)
        have hcast : ((1 : ℤ) : ℝ) ≤ ((|m - k| : ℤ) : ℝ) := by
          exact_mod_cast Int.one_le_abs hne
        rw [Int.cast_abs, Int.cast_sub, Int.cast_one] at hcast
        exact hcast
      have htri : |(m : ℝ) - (k : ℝ)| - |z.re - (k : ℝ)| ≤ |z.re - (m : ℝ)| := by
        have := abs_sub_abs_le_abs_sub ((m : ℝ) - (k : ℝ)) (z.re - (k : ℝ))
        have heq : ((m : ℝ) - (k : ℝ)) - (z.re - (k : ℝ)) = -(z.re - (m : ℝ)) := by ring
        rw [heq, abs_neg] at this
        exact this
      linarith
  refine ⟨m, fun k => ?_⟩
  have hm' : ((m : ℤ) : ℂ) = (((m : ℤ) : ℝ) : ℂ) := by push_cast; ring
  have hk' : ((k : ℤ) : ℂ) = (((k : ℤ) : ℝ) : ℂ) := by push_cast; ring
  rw [hm', hk', dist_ofReal_eq z (m : ℝ), dist_ofReal_eq z (k : ℝ)]
  apply Real.sqrt_le_sqrt
  have hsq : (z.re - (m : ℝ)) ^ 2 ≤ (z.re - (k : ℝ)) ^ 2 := (sq_le_sq).mpr (hmin k)
  linarith

/-- If the infimum of the distances from `z` to the integers (embedded in `ℂ` as real
numbers) is at most `s ≥ 0`, then some integer already achieves distance at most `s`:
the infimum is attained, by the nearest integer to the real part of `z`. -/
theorem exists_int_dist_le_of_iInf_le {z : ℂ} {s : ℝ} (hs : 0 ≤ s)
    (h : (⨅ k : ℤ, dist z (k : ℂ)) ≤ s) : ∃ k : ℤ, dist z (k : ℂ) ≤ s := by
  obtain ⟨m, hm⟩ := exists_int_dist_le_all z
  have hle : dist z (m : ℂ) ≤ ⨅ k : ℤ, dist z (k : ℂ) := le_ciInf hm
  -- the bound `h` alone finishes the job, because the infimum is attained at `m`; the
  -- hypothesis `hs : 0 ≤ s` is recorded here as the natural nonnegativity of the
  -- threshold (it in fact follows from the conclusion).
  have _hs : (0 : ℝ) ≤ s := hs
  exact ⟨m, le_trans hle h⟩

end Work.Pert.Count
