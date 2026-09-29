import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Assembly

/-- `fracDist` of an integer is zero. -/
lemma s0qn_fracDist_intCast_zero (z : ℤ) : Work.TMC16Core.fracDist ((z : ℝ)) = 0 := by
  rw [Work.TMC16Core.fracDist, round_intCast, sub_self, abs_zero]

/-- **Distinct phase indices carry distinct cosines.**

If the sums `2 θ + (i + k) α` over pairs in `S` stay at distance `≥ cθ > 0` from the integers
(`hclust`) and the differences `(i - k) α` over distinct pairs stay at distance `≥ csep > 0`
from the integers (`hsep`), then for `i ≠ k` in `S` the phases `θ + i α` and `θ + k α` have
distinct cosines.

Indeed `cos x = cos y` forces `y = x + 2πk` or `y = -x + 2πk` (`Real.cos_eq_cos_iff`); after
cancelling `2π` the first alternative gives `(k - i) α ∈ ℤ` (so `fracDist ((k-i)α) = 0`,
contradicting `hsep` for the pair `(k,i)`), and the second gives `2 θ + (i + k) α ∈ ℤ`
(so `fracDist (2θ + (i+k)α) = 0`, contradicting `hclust`). -/
theorem s0qn_cos_ne {α θ cθ csep : ℝ} {S : Finset ℤ}
    (hcθ : 0 < cθ) (hcsep : 0 < csep)
    (hclust : ∀ i : ℤ, i ∈ S → ∀ k : ℤ, k ∈ S →
      cθ ≤ Work.TMC16Core.fracDist (2 * θ + (((i + k : ℤ)) : ℝ) * α))
    (hsep : ∀ i : ℤ, i ∈ S → ∀ k : ℤ, k ∈ S → i ≠ k →
      csep ≤ Work.TMC16Core.fracDist ((((i - k : ℤ)) : ℝ) * α))
    {i k : ℤ} (hi : i ∈ S) (hk : k ∈ S) (hne : i ≠ k) :
    Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))
      ≠ Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) := by
  intro hcon
  rw [Real.cos_eq_cos_iff] at hcon
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  obtain ⟨m, hm | hm⟩ := hcon
  · -- difference case: `2π(θ + k α) = 2π m + 2π(θ + i α)`, so `(k - i) α = m ∈ ℤ`
    have hz : (((k - i : ℤ)) : ℝ) * α = (m : ℝ) := by
      have h3 : 2 * Real.pi * (θ + (k : ℝ) * α) - 2 * Real.pi * (θ + (i : ℝ) * α)
          = 2 * Real.pi * (m : ℝ) := by
        rw [hm]; ring
      have h4 : 2 * Real.pi * (θ + (k : ℝ) * α) - 2 * Real.pi * (θ + (i : ℝ) * α)
          = 2 * Real.pi * ((((k - i : ℤ)) : ℝ) * α) := by push_cast; ring
      rw [h4] at h3
      exact mul_left_cancel₀ h2pi h3
    have := hsep k hk i hi hne.symm
    rw [hz, s0qn_fracDist_intCast_zero] at this
    linarith
  · -- sum case: `2π(θ + k α) = 2π m - 2π(θ + i α)`, so `2 θ + (i + k) α = m ∈ ℤ`
    have hz : 2 * θ + (((i + k : ℤ)) : ℝ) * α = (m : ℝ) := by
      have h3 : 2 * Real.pi * (θ + (k : ℝ) * α) + 2 * Real.pi * (θ + (i : ℝ) * α)
          = 2 * Real.pi * (m : ℝ) := by
        rw [hm]; ring
      have h4 : 2 * Real.pi * (θ + (k : ℝ) * α) + 2 * Real.pi * (θ + (i : ℝ) * α)
          = 2 * Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α) := by push_cast; ring
      rw [h4] at h3
      exact mul_left_cancel₀ h2pi h3
    have := hclust i hi k hk
    rw [hz, s0qn_fracDist_intCast_zero] at this
    linarith

end Work.TMC16Core.Assembly
