import Mathlib
import Submission.Work.TMC16Core.Core.geom
import Submission.Work.TMC16Core.Assembly.NR1

namespace Work.TMC16Core.Assembly

/-- The window `I1nr q n s ((s+1)/2)` lies inside the strip `[-((1-δ)K), -δK]`: the
`A`-block of Lemma 9.2 occupies the upper (right) part of the length-`K` interval, and
`hwin` says exactly that the half-width `(s+1)/2` (in blocks of `q(n-1)` sites) fits
inside `s(1-2δ) + δ/q(n-1)` blocks. -/
theorem nr_case1_i1win {q : ℕ → ℕ} {n s : ℕ} {δ : ℝ}
    (hs : 1 ≤ s) (hq : 1 ≤ q (n - 1))
    (hwin : (((s + 1) / 2 : ℕ) : ℝ) ≤ (s : ℝ) * (1 - 2 * δ) + δ / (q (n - 1) : ℝ)) :
    ∀ x ∈ Work.TMC16Core.Core.I1nr q n s ((s + 1) / 2),
      -((1 - δ) * (Work.TMC16Core.Core.Knr q n s : ℝ)) ≤ (x : ℝ) ∧
        (x : ℝ) ≤ -(δ * (Work.TMC16Core.Core.Knr q n s : ℝ)) := by
  intro x hx
  simp only [Work.TMC16Core.Core.I1nr, Work.TMC16Core.Core.Tnr, Finset.mem_Icc] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hqR : (0 : ℝ) < (q (n - 1) : ℝ) := by
    exact_mod_cast (by omega : 0 < q (n - 1))
  -- integer bounds on `x`, with the products of naturals folded into single casts
  have hx2z : x ≤ -(((s * q (n - 1) : ℕ) : ℤ)) + (((((s + 1) / 2) * q (n - 1) : ℕ) : ℤ)) := by
    rw [Nat.cast_mul, Nat.cast_mul]; exact hx2
  have hx1z : -(((s * q (n - 1) : ℕ) : ℤ)) + 1
      - (((((s + 1) / 2) * q (n - 1) : ℕ) : ℤ)) ≤ x := by
    rw [Nat.cast_mul, Nat.cast_mul]; exact hx1
  have hx2r : (x : ℝ) ≤ -(((s * q (n - 1) : ℕ) : ℝ))
      + (((((s + 1) / 2) * q (n - 1) : ℕ) : ℝ)) := by
    have h := (Int.cast_le (R := ℝ)).mpr hx2z
    simpa only [Int.cast_neg, Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_natCast] using h
  have hx1r : -(((s * q (n - 1) : ℕ) : ℝ)) + 1
      - (((((s + 1) / 2) * q (n - 1) : ℕ) : ℝ)) ≤ (x : ℝ) := by
    have h := (Int.cast_le (R := ℝ)).mpr hx1z
    simpa only [Int.cast_neg, Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_natCast] using h
  -- `hwin` multiplied by `q(n-1) > 0`
  have hTA : (((((s + 1) / 2) * q (n - 1) : ℕ) : ℝ))
      ≤ (((s * q (n - 1) : ℕ) : ℝ)) * (1 - 2 * δ) + δ := by
    have hmul := mul_le_mul_of_nonneg_right hwin (le_of_lt hqR)
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hqR)] at hmul
    rw [Nat.cast_mul, Nat.cast_mul]
    nlinarith [hmul]
  have hKcast : ((Work.TMC16Core.Core.Knr q n s : ℕ) : ℝ)
      = 2 * (((s * q (n - 1) : ℕ) : ℝ)) - 1 := by
    rw [knr_castR hs hq]; push_cast; ring
  constructor
  · rw [hKcast]; nlinarith [hx1r, hTA]
  · rw [hKcast]; nlinarith [hx2r, hTA]

end Work.TMC16Core.Assembly
