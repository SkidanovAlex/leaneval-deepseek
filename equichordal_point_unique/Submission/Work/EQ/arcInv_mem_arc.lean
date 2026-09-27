import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.hetero_gamma
import Submission.Work.EQ.hetero_box
import Submission.Work.EQ.normEqCurve_periodic_and_sum
import Submission.Work.EQ.polarPt_basic

namespace Work.EQ

open Complex

/-- Explicit normal form of `arcInv` on a point of the arc: if `z = O₁ + r e^{iθ}` with `r > 0`
(`O₁ = -a/2`), then `arcInv a z = O₂ + (1 - r) e^{iθ}` (`O₂ = a/2`), i.e.
`arcInv a z = polarPt (a/2) (1 - r) θ`. -/
theorem arcInv_polarPt {a r θ : ℝ} (hr : 0 < r) :
    arcInv a (polarPt (-(a/2)) r θ) = polarPt (a/2) (1 - r) θ := by
  have hw : polarPt (-(a/2)) r θ + ((a/2:ℝ):ℂ) = (r:ℂ) * Complex.exp ((θ:ℂ)*Complex.I) := by
    rw [polarPt]; push_cast; ring
  have hnormw : ‖polarPt (-(a/2)) r θ + ((a/2:ℝ):ℂ)‖ = r := by
    rw [hw, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      show ‖(r:ℂ)‖ = |r| from by simp, abs_of_pos hr]
  have hdiv : (polarPt (-(a/2)) r θ + ((a/2:ℝ):ℂ)) /
      ((‖polarPt (-(a/2)) r θ + ((a/2:ℝ):ℂ)‖ : ℝ) : ℂ) = Complex.exp ((θ:ℂ)*Complex.I) := by
    rw [hnormw, hw, mul_comm, mul_div_assoc, div_self (by exact_mod_cast (ne_of_gt hr)), mul_one]
  rw [arcInv, hdiv, hnormw, polarPt]
  push_cast
  ring

/-- **`arcInv` maps the open upper arc into itself.**  If `z` is a point of the arc
(`z ∈ arcSet a ρ₁ = range (polarPt (-(a/2)) (ρ₁·) ·)`) with `0 < z.im`, then so is
`arcInv a z`, and `arcInv a z` still has positive imaginary part.

Note `0 < a` and `a < 1` are NOT needed (do not route through `arc_near_A1`):  `hz` gives
`z = polarPt (-(a/2)) (ρ₁ θ) θ` for some `θ`; by `polarPt_basic`,
`z + a/2 = z - (-a/2) = (ρ₁ θ) * exp (θ * I)` and `‖z + a/2‖ = ρ₁ θ`, so
`arcInv a z = a/2 + (1 - ρ₁ θ) * exp (θ * I) = polarPt (a/2) (ρ₂ θ) θ`, using `ρ₂ θ = 1 - ρ₁ θ`
(`normEqCurve_periodic_and_sum`).  This is a member of `range (polarPt (a/2) (ρ₂·))`, which
`hC`'s last clause identifies with `arcSet a ρ₁`.  For positivity of the imaginary part:
`(arcInv a z).im = (1 - ρ₁ θ) * sin θ` (`polarPt_basic`), with `1 - ρ₁ θ > 0` (because
`ρ₁ θ + ρ₁ (θ + π) = 1` and `0 < ρ₁ (θ+π)`) and `sin θ > 0` (because `0 < z.im = ρ₁ θ * sin θ`
and `0 < ρ₁ θ`) — no reduction of `θ` into `(0,π)` is needed. -/
theorem arcInv_mem_arc {a : ℝ} {ρ₁ ρ₂ : ℝ → ℝ} (hC : NormEqCurve a ρ₁ ρ₂)
    (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ) (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ))
    {z : ℂ} (hz : z ∈ arcSet a ρ₁) (hzim : 0 < z.im) :
    arcInv a z ∈ arcSet a ρ₁ ∧ 0 < (arcInv a z).im := by
  obtain ⟨-, -, hsum⟩ := normEqCurve_periodic_and_sum hC hs₁ hs₂
  obtain ⟨-, -, hρ₁pos, hρ₂pos, -, -, hrange⟩ := hC
  rw [arcSet] at hz
  obtain ⟨θ, rfl⟩ := hz
  have hr := hρ₁pos θ
  have hsin : 0 < Real.sin θ := by
    have h1 := (polarPt_basic (c := -(a/2)) (r := ρ₁ θ) (θ := θ) hr).1
    rw [h1] at hzim
    exact pos_of_mul_pos_right hzim (le_of_lt hr)
  rw [arcInv_polarPt hr, ← hsum θ]
  refine ⟨?_, ?_⟩
  · rw [arcSet, hrange]
    exact ⟨θ, rfl⟩
  · have him := (polarPt_basic (c := a/2) (r := ρ₂ θ) (θ := θ) (hρ₂pos θ)).1
    rw [him]
    exact mul_pos (hρ₂pos θ) hsin

end Work.EQ
