import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.PARIMPL2.Direct.inbound_bounds

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- `d/dz log (sin (λz)) = λ·cos(λz)/sin(λz) = ζ(z)`, where `ζ = ecalPt (iλ)` is the
Écalle point map on the imaginary axis.

The hypotheses `0 < λ·Re w < π` put `sin (λw)` in the open right half-plane, hence in
the slit plane, so that the principal branch of `log` is differentiable at `sin (λw)`
(with derivative `sin (λw)⁻¹`); they also exclude the punctures `sin (λw) = 0`, where
`ζ` has a pole and the identity `ecalPt (iλ) w = λ·cot(λw)` fails. -/
theorem logSin_hasDerivAt (lam : ℝ) (hlam : 0 < lam) (w : ℂ)
    (h1 : 0 < lam * w.re) (h2 : lam * w.re < Real.pi) :
    HasDerivAt (fun z : ℂ => Complex.log (Complex.sin ((lam : ℂ) * z)))
      (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) w) w := by
  -- `sin (λw)` has positive real part, hence is nonzero and lies in the slit plane.
  have hsin_re : 0 < (Complex.sin ((lam : ℂ) * w)).re := by
    rw [inbound_sin_re]
    exact mul_pos (Real.sin_pos_of_pos_of_lt_pi h1 h2) (Real.cosh_pos _)
  have hsin_ne : Complex.sin ((lam : ℂ) * w) ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hsin_re
    exact lt_irrefl 0 hsin_re
  have hslit : Complex.sin ((lam : ℂ) * w) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl hsin_re)
  -- The punctures of the Écalle coordinate are avoided, so `ζ = ecalPt (iλ)` is finite.
  have hE_ne : Work.Implosion.ecalE ((lam : ℂ) * Complex.I) w ≠ 1 := by
    intro h
    have hzero : 2 * Complex.sinh (((lam : ℂ) * Complex.I) * w)
        * Complex.exp (((lam : ℂ) * Complex.I) * w) = 0 := by
      rw [← inbound_ecalE_sub_one ((lam : ℂ) * Complex.I) w, h]; ring
    rcases mul_eq_zero.mp hzero with h2' | h3
    · rcases mul_eq_zero.mp h2' with h4 | h5
      · exact absurd h4 (by norm_num)
      · rw [show (((lam : ℂ) * Complex.I) * w) = ((lam : ℂ) * w) * Complex.I by ring,
          Complex.sinh_mul_I] at h5
        exact hsin_ne (by simpa using h5)
    · exact absurd h3 (Complex.exp_ne_zero _)
  -- Chain rule: the inner map `z ↦ sin (λz)` has derivative `λ·cos(λw)`.
  have hinner : HasDerivAt (fun z : ℂ => Complex.sin ((lam : ℂ) * z))
      (Complex.cos ((lam : ℂ) * w) * (lam : ℂ)) w :=
    (Complex.hasDerivAt_sin ((lam : ℂ) * w)).comp w (hasDerivAt_const_mul (lam : ℂ))
  -- The derivative value is the Écalle point map.
  have hval : (Complex.sin ((lam : ℂ) * w))⁻¹ * (Complex.cos ((lam : ℂ) * w) * (lam : ℂ))
      = Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) w := by
    rw [inbound_ecalPt_eq lam hlam w hE_ne, div_eq_mul_inv]
    ring
  have hcomp := (Complex.hasDerivAt_log hslit).comp w hinner
  rw [hval] at hcomp
  exact hcomp

end Work.PARIMPL2.Direct
