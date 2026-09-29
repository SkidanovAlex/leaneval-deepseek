import Mathlib
import Submission.Work.C17.logPw_setup

namespace Work.C17

/-- Every point of the stadium `stadiumSet c δ ρ` (which joins the disc of radius `δ`
around the cusp value `c ≥ 3/4` to the disc of radius `ρ = 1/64` around `p₀ = 1/4 + i/5`)
has real part `≥ 15/64`.  Indeed the centre of the `t`-th disc has real part
`(1-t)c + t/4` and its radius is `(1-t)δ + tρ`, so the leftmost real part is
`(1-t)(c-δ) + t(1/4-ρ) ≥ min(c-δ, 1/4-ρ) ≥ 15/64` since `δ ≤ (1-c)/2` and `ρ = 1/64`. -/
theorem stadium_re_ge {c δ ρ : ℝ} (hc : 3 / 4 ≤ c) (hc1 : c < 1)
    (hδ : δ = min ((1 - c) / 2) (1 / 64)) (hρ : ρ = 1 / 64) :
    ∀ z ∈ stadiumSet c δ ρ, (15 / 64 : ℝ) ≤ z.re := by
  intro z hz
  obtain ⟨t, ht, hzt⟩ := hz
  rw [Metric.mem_ball] at hzt
  have hδle : δ ≤ (1 - c) / 2 := by rw [hδ]; exact min_le_left _ _
  have hp0 : p0C.re = (1 / 4 : ℝ) := by simp [p0C]
  set w : ℂ := ((((1 - t) * c : ℝ)) : ℂ) + (t : ℂ) * p0C with hw
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
  have hlow : (15 / 64 : ℝ) ≤ w.re - ((1 - t) * δ + t * ρ) := by
    rw [hwre, hρ]
    have hcδ : c - δ ≥ 15 / 64 := by linarith
    have h1 : 0 ≤ 1 - t := by linarith [ht.2]
    nlinarith [hcδ, h1, ht.1, ht.2]
  linarith [hlow, hbnd, hnorm, hre]

end Work.C17
