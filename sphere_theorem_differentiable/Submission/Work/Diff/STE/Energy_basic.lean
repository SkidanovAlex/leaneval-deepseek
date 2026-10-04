import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Basic facts about the energy norm `ENormSq` and the Friedrichs truncation

* `trunc_eq_zero_of_far` : the truncation `trunc ρ ε` vanishes on frequencies with
  `Σᵢ (ε kᵢ)² > 2`; combined with `finite_bounded_lattice` this says that the range of the
  Friedrichs mollifier is finite dimensional (`D1` of the design).
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Friedrichs truncation vanishes on high frequencies. -/
theorem trunc_eq_zero_of_far (ρ : (ι → ℝ) → ℝ)
    (hρ0 : ∀ y : ι → ℝ, 2 < (∑ i, (y i) ^ 2) → ρ y = 0)
    (ε : ℝ) (c : (ι → ℤ) → ℂ) (k : ι → ℤ)
    (hk : 2 < ∑ i, (ε * (k i : ℝ)) ^ 2) :
    trunc ρ ε c k = 0 := by
  rw [trunc]
  have h : ρ (ε • fun i => (k i : ℝ)) = 0 := by
    apply hρ0
    simpa [Pi.smul_apply, smul_eq_mul] using hk
  rw [h, Complex.ofReal_zero, zero_mul]


/-- The Friedrichs truncation is self-adjoint for the coefficient pairing: the multiplier
`k ↦ ρ (ε k)` is real-valued. -/
theorem tsum_trunc_mul_star (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (c d : (ι → ℤ) → ℂ)
    (hc : Summable (fun k : ι → ℤ => ‖c k‖)) (hd : Summable (fun k : ι → ℤ => ‖d k‖)) :
    ∑' k : ι → ℤ, trunc ρ ε c k * star (d k)
      = ∑' k : ι → ℤ, c k * star (trunc ρ ε d k) := by
  have _ := hc
  have _ := hd
  refine tsum_congr (fun k => ?_)
  rw [trunc, trunc]
  simp only [Complex.star_def, map_mul, Complex.conj_ofReal]
  ring

end Work.Diff.STE
