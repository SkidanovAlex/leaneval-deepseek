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
open Work.Implosion

/-- For `a` purely imaginary (`star a = -a`), the Möbius coordinate `m_a` intertwines
complex conjugation composed with the half-turn `ζ ↦ -ζ` with complex conjugation:
`m_a(-ζ̄) = overline{m_a(ζ)}`.  This is the reflection symmetry of the local model
across the imaginary axis. -/
theorem mobius_neg_star (a ζ : ℂ) (hsa : starRingEnd ℂ a = -a) :
    mobius a (-(starRingEnd ℂ ζ)) = starRingEnd ℂ (mobius a ζ) := by
  have h_neg : -(starRingEnd ℂ ζ) = starRingEnd ℂ (-ζ) := (map_neg (starRingEnd ℂ) ζ).symm
  rw [h_neg, mobius]
  rw [show starRingEnd ℂ (-ζ) + a = starRingEnd ℂ ((-ζ) - a) by rw [map_sub, hsa]; ring]
  rw [show starRingEnd ℂ (-ζ) - a = starRingEnd ℂ ((-ζ) + a) by rw [map_add, hsa]; ring]
  rw [← map_div₀]
  congr 1
  rw [mobius]
  rw [show (-ζ - a) = -(ζ + a) by ring, show (-ζ + a) = -(ζ - a) by ring]
  rw [neg_div_neg_eq]

set_option linter.unusedVariables false in
theorem ecalCoord_reflect (lam : ℝ) (ζ : ℂ) (hlam : 0 < lam)
    (h1 : ζ ≠ (lam : ℂ) * I) (h2 : ζ ≠ -((lam : ℂ) * I))
    (h3 : (mobius ((lam : ℂ) * I) ζ).im ≠ 0) :
    ecalCoord ((lam : ℂ) * I) (-(starRingEnd ℂ ζ)) = -starRingEnd ℂ (ecalCoord ((lam : ℂ) * I) ζ) := by
  have hsa : starRingEnd ℂ ((lam : ℂ) * I) = -((lam : ℂ) * I) := by
    rw [map_mul]; simp
  have hw : mobius ((lam : ℂ) * I) (-(starRingEnd ℂ ζ))
      = starRingEnd ℂ (mobius ((lam : ℂ) * I) ζ) := mobius_neg_star _ _ hsa
  have harg : (mobius ((lam : ℂ) * I) ζ).arg ≠ Real.pi := by
    intro hh
    exact h3 (Complex.arg_eq_pi_iff.mp hh).2
  have hlog := Complex.log_conj (mobius ((lam : ℂ) * I) ζ) harg
  rw [ecalCoord, ecalCoord, hw, hlog]
  have hs2a : starRingEnd ℂ (2 * ((lam : ℂ) * I)) = -(2 * ((lam : ℂ) * I)) := by
    rw [two_mul, map_add, hsa]; ring
  rw [map_div₀, hs2a, div_neg, neg_neg]

end Work.Implosion.Approx
