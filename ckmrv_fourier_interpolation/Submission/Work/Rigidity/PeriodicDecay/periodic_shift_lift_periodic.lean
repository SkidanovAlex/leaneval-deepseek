import Mathlib

namespace Work.Rigidity.PeriodicDecay

/-- If `u` is invariant under translation by `1` on `ℍ`, then the pullback of `u` along
`z ↦ ofComplex (z + I)` is `1`-periodic. -/
theorem periodic_shift_lift_periodic {u : UpperHalfPlane → ℂ}
    (hper : ∀ τ : UpperHalfPlane, u ((1 : ℝ) +ᵥ τ) = u τ) :
    Function.Periodic (fun z : ℂ => u (UpperHalfPlane.ofComplex (z + Complex.I))) 1 := by
  intro z
  change u (UpperHalfPlane.ofComplex (z + 1 + Complex.I))
      = u (UpperHalfPlane.ofComplex (z + Complex.I))
  by_cases hz : 0 < (z + Complex.I).im
  · -- `z + I` lies in the upper half plane; shifting by `1` is the `ℝ`-action of `1`.
    have hz1 : 0 < (z + 1 + Complex.I).im := by simpa using hz
    have hshift : UpperHalfPlane.ofComplex (z + 1 + Complex.I)
        = (1 : ℝ) +ᵥ UpperHalfPlane.ofComplex (z + Complex.I) := by
      rw [UpperHalfPlane.ext_iff]
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz1, UpperHalfPlane.coe_vadd,
        UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      push_cast
      ring
    rw [hshift, hper]
  · -- `z + I` is not in the upper half plane; `ofComplex` is constant there.
    have hzle : (z + Complex.I).im ≤ 0 := not_lt.mp hz
    have hzle1 : (z + 1 + Complex.I).im ≤ 0 := by simpa using hzle
    rw [UpperHalfPlane.ofComplex_apply_eq_of_im_nonpos hzle1 hzle]

end Work.Rigidity.PeriodicDecay
