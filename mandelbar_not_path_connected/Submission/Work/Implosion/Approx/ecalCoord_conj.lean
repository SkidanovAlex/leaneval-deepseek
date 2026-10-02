import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Approx

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Approx

open Complex

set_option linter.unusedVariables false

/-- Complex conjugation intertwines the Möbius coordinate with the conjugate parameter:
`conj (m_a ζ) = m_{conj a} (conj ζ)`. -/
theorem star_mobius (a ζ : ℂ) :
    starRingEnd ℂ (mobius a ζ) = mobius (starRingEnd ℂ a) (starRingEnd ℂ ζ) := by
  simp only [mobius, map_div₀, map_add, map_sub]

/-- `m_a(z) · m_{−a}(z) = 1` away from the two punctures `z = ±a`. -/
theorem mobius_mul_mobius_neg (a z : ℂ) (h1 : z ≠ a) (h2 : z ≠ -a) :
    mobius a z * mobius (-a) z = 1 := by
  have hd1 : z - a ≠ 0 := sub_ne_zero.mpr h1
  have hd2 : z + a ≠ 0 := fun h => h2 (by linear_combination h)
  rw [mobius, mobius, show z + -a = z - a from by ring, show z - -a = z + a from by ring]
  field_simp

/-- The Écalle coordinate of the local model is *anti*-equivariant under complex
conjugation, for the purely imaginary parameter `a = iλ` (`λ > 0`): conjugating the point
conjugates the coordinate.  The hypothesis `(m_a ζ).im ≠ 0` (i.e. `m_a ζ` is not real)
keeps `m_a ζ` off the branch cut of `Complex.log`, which is exactly where the identity
`log (conj z) = conj (log z)` would fail. -/
theorem ecalCoord_conj (lam : ℝ) (ζ : ℂ) (hlam : 0 < lam)
    (h1 : ζ ≠ (lam : ℂ) * I) (h2 : ζ ≠ -((lam : ℂ) * I))
    (h3 : (mobius ((lam : ℂ) * I) ζ).im ≠ 0) :
    ecalCoord ((lam : ℂ) * I) (starRingEnd ℂ ζ) = starRingEnd ℂ (ecalCoord ((lam : ℂ) * I) ζ) := by
  set a : ℂ := (lam : ℂ) * I with ha_def
  have hstar_a : starRingEnd ℂ a = -a := by
    rw [ha_def, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have h1' : ζ ≠ a := fun h => h1 (ha_def ▸ h)
  have h2' : ζ ≠ -a := fun h => h2 (ha_def ▸ h)
  have h3' : (mobius a ζ).im ≠ 0 := fun h => h3 (ha_def ▸ h)
  -- conjugation acts on `star ζ` by `±a ↔ ∓a`
  have hsa1 : starRingEnd ℂ ζ ≠ a := by
    intro h
    have h' : ζ = -a := by
      have := congrArg (starRingEnd ℂ) h
      simpa [hstar_a] using this
    exact h2' h'
  have hsa2 : starRingEnd ℂ ζ ≠ -a := by
    intro h
    have h' : ζ = a := by
      have := congrArg (starRingEnd ℂ) h
      simpa [hstar_a] using this
    exact h1' h'
  -- `m_a (conj ζ) = (conj (m_a ζ))⁻¹`
  have hconj : starRingEnd ℂ (mobius a ζ) = mobius (-a) (starRingEnd ℂ ζ) := by
    rw [star_mobius, hstar_a]
  have hprod : mobius a (starRingEnd ℂ ζ) * starRingEnd ℂ (mobius a ζ) = 1 := by
    rw [hconj]
    exact mobius_mul_mobius_neg a (starRingEnd ℂ ζ) hsa1 hsa2
  have hv : mobius a (starRingEnd ℂ ζ) = (starRingEnd ℂ (mobius a ζ))⁻¹ :=
    eq_inv_of_mul_eq_one_left hprod
  -- the branch-cut hypotheses for `Complex.log`
  have hwarg : (mobius a ζ).arg ≠ Real.pi := fun h => h3' (Complex.arg_eq_pi_iff.mp h).2
  have hcwarg : (starRingEnd ℂ (mobius a ζ)).arg ≠ Real.pi := by
    intro h
    have him := (Complex.arg_eq_pi_iff.mp h).2
    rw [Complex.conj_im] at him
    exact h3' (neg_eq_zero.mp him)
  -- the key identity: `log (m_a (conj ζ)) = -conj (log (m_a ζ))`
  have hlog : Complex.log (mobius a (starRingEnd ℂ ζ))
      = -starRingEnd ℂ (Complex.log (mobius a ζ)) := by
    rw [hv, Complex.log_inv _ hcwarg, Complex.log_conj _ hwarg]
  have h2c : starRingEnd ℂ (2 : ℂ) = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  have h2a : starRingEnd ℂ (2 * a) = -(2 * a) := by
    rw [map_mul, hstar_a, h2c]
    ring
  simp only [ecalCoord]
  rw [hlog, map_div₀, h2a, div_neg, neg_div]

end Work.Implosion.Approx
