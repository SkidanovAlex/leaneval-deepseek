import Mathlib
import Submission.Work.C17.logPw_setup

namespace Work.C17I

/-- Every point of the stadium `stadiumSet c δ ρ` (the union of the discs joining a disc
of radius `δ` around `c` to a disc of radius `ρ` around `p₀ = 1/4 + i/5`) has real part
`≥ 1/5`, as soon as `c - δ ≥ 1/5` and `1/4 - ρ ≥ 1/5`.

Indeed the centre of the `t`-th disc has real part `(1-t)c + t/4` and its radius is
`(1-t)δ + tρ`, so the leftmost real part is
`(1-t)(c-δ) + t(1/4-ρ) ≥ min(c-δ, 1/4-ρ) ≥ 1/5`. -/
theorem stadium_re_weak {c δ ρ : ℝ} (h1 : (1 : ℝ) / 5 ≤ c - δ) (h2 : (1 : ℝ) / 5 ≤ 1 / 4 - ρ) :
    ∀ z ∈ Work.C17.stadiumSet c δ ρ, (1 : ℝ) / 5 ≤ z.re := by
  intro z hz
  obtain ⟨t, ht, hzt⟩ := hz
  rw [Metric.mem_ball] at hzt
  have hp0 : Work.C17.p0C.re = (1 / 4 : ℝ) := by simp [Work.C17.p0C]
  set w : ℂ := ((((1 - t) * c : ℝ)) : ℂ) + (t : ℂ) * Work.C17.p0C with hw
  have hwre : w.re = (1 - t) * c + t * (1 / 4) := by
    rw [hw]
    simp [Complex.add_re, Complex.mul_re, hp0]
  have hnorm : ‖z - w‖ < (1 - t) * δ + t * ρ := by
    rwa [dist_eq_norm] at hzt
  have hre : z.re = w.re + (z - w).re := by
    rw [Complex.sub_re]; ring
  have hbnd : -‖z - w‖ ≤ (z - w).re := by
    have := Complex.abs_re_le_norm (z - w)
    rw [abs_le] at this
    exact this.1
  have hlow : (1 / 5 : ℝ) ≤ w.re - ((1 - t) * δ + t * ρ) := by
    rw [hwre]
    have h1t : 0 ≤ 1 - t := by linarith [ht.2]
    nlinarith [h1, h2, h1t, ht.1, ht.2]
  linarith [hlow, hbnd, hnorm, hre]

end Work.C17I
