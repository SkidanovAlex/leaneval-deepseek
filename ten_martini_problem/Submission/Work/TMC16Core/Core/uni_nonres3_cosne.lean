import Mathlib
import Submission.Work.TMC16Core.Core.uni_nonres3_support

namespace Work.TMC16Core.Core

/-- `fracDist` of an integer is zero. -/
lemma fracDist_intCast_zero (z : ℤ) : Work.TMC16Core.fracDist ((z : ℝ)) = 0 := by
  rw [Work.TMC16Core.fracDist, round_intCast, sub_self, abs_zero]

/-- **The cosines of the phases indexed by `Dnr` are pairwise distinct.**

Let `i ≠ j` both lie in the block-aligned index set `Dnr q n s a' b' y`, let `α` be such that
`k α ∉ ℤ` for every `k ≠ 0` (`hirr`), and let the phase `2 θ + k α` stay at distance at least
`c > 0` from the integers for every `|k| ≤ 2|y| + 6 s q(n-1) + 4` (`hθ`).  Then
`cos (2π (θ + i α)) ≠ cos (2π (θ + j α))`.

Indeed `cos x = cos y` forces `y = x + 2πk` or `y = -x + 2πk` (`Real.cos_eq_cos_iff`), which after
cancelling `2π` yields `(j - i) α = k ∈ ℤ` — impossible since `j - i ≠ 0` and `fracDist` of a
non-zero multiple of `α` does not vanish — or `2 θ + (i + j) α = k ∈ ℤ`, impossible because the
hypothesis `hθ` at `k = i + j` gives `fracDist (2 θ + (i+j) α) ≥ c > 0`; the range hypothesis for
`hθ` at `i + j` is supplied by `Dnr_add_abs_le`. -/
theorem uni_nonres3_cosne {α : ℝ} {q : ℕ → ℕ} {n s a' b' : ℕ} {y : ℤ} {θ c : ℝ}
    (hn : 2 ≤ n) (hs : 1 ≤ s) (hab : a' + b' = s)
    (hTn : 2 * s * q (n - 1) ≤ q n)
    (hy : Work.TMC16Core.Core.Tnr q n s ≤ y)
    (hc : 0 < c)
    (hirr : ∀ k : ℤ, k ≠ 0 → Work.TMC16Core.fracDist ((k : ℝ) * α) ≠ 0)
    (hθ : ∀ k : ℤ, |k| ≤ 2 * |y| + 6 * (s : ℤ) * (q (n - 1) : ℤ) + 4 →
      c ≤ Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α))
    {i j : ℤ} (hi : i ∈ Work.TMC16Core.Core.Dnr q n s a' b' y)
    (hj : j ∈ Work.TMC16Core.Core.Dnr q n s a' b' y) (hij : i ≠ j) :
    Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)) ≠ Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) := by
  intro hcon
  -- `cos x = cos y` forces `2π(θ + jα) = 2π(θ + iα) + 2πk` or `2π(θ + jα) = -2π(θ + iα) + 2πk`.
  rw [Real.cos_eq_cos_iff] at hcon
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  -- the range bound needed for `hθ` at the index `i + j`
  have hbnd := Work.TMC16Core.Core.Dnr_add_abs_le hab hi hj
  obtain ⟨k, hk | hk⟩ := hcon
  · -- the *difference* case: `(j - i) α` is an integer
    have hz : (((j - i : ℤ)) : ℝ) * α = (k : ℝ) := by
      have h3 : 2 * Real.pi * (θ + (j : ℝ) * α) - 2 * Real.pi * (θ + (i : ℝ) * α)
          = (2 * Real.pi) * (k : ℝ) := by
        rw [hk]; ring
      have h4 : 2 * Real.pi * (θ + (j : ℝ) * α) - 2 * Real.pi * (θ + (i : ℝ) * α)
          = (2 * Real.pi) * ((((j - i : ℤ)) : ℝ) * α) := by push_cast; ring
      rw [h4] at h3
      exact mul_left_cancel₀ h2pi h3
    have hm : j - i ≠ 0 := by intro h0; exact hij (by omega)
    exact (hirr (j - i) hm) (by rw [hz, fracDist_intCast_zero])
  · -- the *sum* case: `2 θ + (i + j) α` is an integer
    have hz : 2 * θ + (((i + j : ℤ)) : ℝ) * α = (k : ℝ) := by
      have h3 : 2 * Real.pi * (θ + (j : ℝ) * α) + 2 * Real.pi * (θ + (i : ℝ) * α)
          = (2 * Real.pi) * (k : ℝ) := by
        rw [hk]; ring
      have h4 : 2 * Real.pi * (θ + (j : ℝ) * α) + 2 * Real.pi * (θ + (i : ℝ) * α)
          = (2 * Real.pi) * (2 * θ + (((i + j : ℤ)) : ℝ) * α) := by push_cast; ring
      rw [h4] at h3
      exact mul_left_cancel₀ h2pi h3
    have hc' := hθ (i + j) hbnd
    rw [hz, fracDist_intCast_zero] at hc'
    linarith

end Work.TMC16Core.Core
