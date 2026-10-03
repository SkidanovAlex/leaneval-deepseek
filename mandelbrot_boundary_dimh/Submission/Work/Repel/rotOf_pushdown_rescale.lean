import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.deriv_rescale
import Submission.Work.Repel.log_exp_two_pi_I
import Submission.Work.Repel.alphaOf_exp_eq
import Submission.Work.Repel.re_inv_add_bounds

/-!
# The rotation number of a rescaled pushdown (Shishikura §6, level 1)

Context.  `E = R̃_f` is the lifted return map of a parabolic perturbation `f` of the level-0 germ
`f₀ = x + x²`.  Its pushed-down germ `pushdown E` has derivative at `0` equal to
`exp (-2πi/α)`, where `α = alphaOf a₁ a₂ β = 1/(a₁ - 1/(a₂+β))` is the rotation number of `f`
(Shishikura (4.2.2): `R_f'(0) = e^{-2πi/α}`).  The level-1 germ used in Step 6 is the rescaling
`ζ ↦ s · pushdown E (ζ/s)`, `s = ½ · (pushdown E)''(0)`.

Mathematics of the proof.  Rescaling does not change the derivative at the fixed point, so
`rotOf (ζ ↦ s·pushdown E (ζ/s)) = log ((pushdown E)'(0))/(2πi)`.  Now
`1/α = a₁ - 1/(a₂+β)`, hence `-2πi/α = -2πi·a₁ + 2πi/(a₂+β)`, and since `a₁ ∈ ℤ` the factor
`exp(-2πi a₁) = 1` drops out: `(pushdown E)'(0) = exp (2πi/(a₂+β))`.  Finally `a₂ ≥ 4` and
`0 ≤ Re β < 1` give `0 < Re (1/(a₂+β)) ≤ 1/2`, i.e. `Im (2πi/(a₂+β)) ∈ (-π, π]`, so the principal
branch of `log` inverts `exp` on it, and `rotOf = 1/(a₂+β)`.
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

/-- The rotation number of `ζ ↦ s · pushdown E (ζ/s)` is the level-1 rotation number
`1/(a₂+β)`, given that `pushdown E` has derivative `exp (-2πi/alphaOf a₁ a₂ β)` at `0`. -/
theorem rotOf_pushdown_rescale (a₁ a₂ : ℕ) (β s : ℂ) (hs : s ≠ 0) {E : ℂ → ℂ}
    (hderiv : deriv (pushdown E) 0 =
      Complex.exp (-(2 * Real.pi * I * (1 / alphaOf a₁ a₂ β))))
    (ha₁ : 2 ≤ a₁) (ha₂ : 4 ≤ a₂) (hβre : 0 ≤ β.re) (hβre' : β.re < 1) :
    rotOf (fun ζ => s * pushdown E (ζ / s)) = 1 / ((a₂ : ℂ) + β) := by
  obtain ⟨hle, hlt⟩ := re_inv_add_bounds a₂ β ha₂ hβre hβre'
  have hlog := log_exp_two_pi_I (1 / ((a₂ : ℂ) + β)) hlt hle
  have hexp := alphaOf_exp_eq a₁ a₂ β
  have hd : deriv (fun ζ : ℂ => s * pushdown E (ζ / s)) 0 = deriv (pushdown E) 0 :=
    deriv_rescale (pushdown E) s hs
  simp only [rotOf]
  rw [hd, hderiv, hexp]
  exact hlog

end Work.Repel
