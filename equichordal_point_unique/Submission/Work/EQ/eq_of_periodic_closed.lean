import Mathlib

namespace Work.EQ

/-- A set `S ⊆ ℝ` invariant under translation by `p > 0` and containing the
fundamental interval `[0, p]` must be all of `ℝ`. -/
theorem eq_of_periodic_closed {S : Set ℝ} {p : ℝ} (hp : 0 < p) (hSc : IsClosed S)
    (hper : ∀ x, x ∈ S ↔ x + p ∈ S) (hbase : ∀ x, 0 ≤ x → x ≤ p → x ∈ S) :
    S = Set.univ := by
  -- Membership is invariant under translation by any integer multiple of `p`.
  have hshift : ∀ n : ℤ, ∀ y : ℝ, (y ∈ S ↔ y + (n:ℝ) * p ∈ S) := by
    intro n
    refine Int.induction_on n ?_ ?_ ?_
    · intro y; simp
    · intro i ih y
      have e : y + ((↑i : ℤ) + 1 : ℤ) * p = (y + (i:ℝ) * p) + p := by push_cast; ring
      rw [e, ← hper]
      exact ih y
    · intro i ih y
      have e : y + ((-↑i : ℤ) - 1 : ℤ) * p = (y + (-(i:ℝ)) * p) - p := by push_cast; ring
      rw [e]
      have hper' : (y + -(i:ℝ) * p - p) ∈ S ↔ y + -(i:ℝ) * p ∈ S := by
        have := hper (y + -(i:ℝ) * p - p)
        simpa using this
      have ih' : y ∈ S ↔ y + -(i:ℝ) * p ∈ S := by
        have := ih y
        push_cast at this
        simpa using this
      exact ih'.trans hper'.symm
  rw [Set.eq_univ_iff_forall]
  intro x
  -- Reduce `x` to its representative modulo `p`.
  set k : ℤ := ⌊x / p⌋ with hk
  set r : ℝ := x - (k:ℝ) * p with hr
  have hr0 : 0 ≤ r := by
    have h : (k:ℝ) ≤ x / p := by rw [hk]; exact Int.floor_le _
    have h2 : (k:ℝ) * p ≤ x / p * p := mul_le_mul_of_nonneg_right h (le_of_lt hp)
    rw [div_mul_cancel₀ x (ne_of_gt hp)] at h2
    rw [hr]; linarith
  have hrp : r ≤ p := by
    have h : x / p < (k:ℝ) + 1 := by rw [hk]; exact Int.lt_floor_add_one _
    have h2 : x / p * p < ((k:ℝ) + 1) * p := mul_lt_mul_of_pos_right h hp
    rw [div_mul_cancel₀ x (ne_of_gt hp)] at h2
    rw [hr]; linarith
  have hrS : r ∈ S := hbase r hr0 hrp
  have := (hshift k r).mp hrS
  rw [show r + (k:ℝ) * p = x by rw [hr]; ring] at this
  exact this

end Work.EQ
