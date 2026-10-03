import Mathlib
import Submission.Work.KMTPlan.A6.ConcAux.Defs

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6.ConcAux

open Polynomial Work.KMTPlan.A6.ConcAux

/-- The `p`-adic valuation of the Taylor coefficients of `H` at `r` is read off by the
multiplicity of `r` as a root of `H` modulo `p`: writing `s` for the latter,

* `p ∣ taylorCoeff H r i` for every `i < s`, and
* `p ∤ taylorCoeff H r s`.

Indeed, `taylorCoeff H r i` is the `i`-th coefficient of `H(r + X)`, and reducing that
polynomial modulo `p` gives `(H mod p)(r + X)`, whose order of vanishing at `0` is exactly
`s = rootMultiplicity (H mod p) r`.  The second statement needs no hypothesis; the
hypothesis `p ∣ H.eval r` of the original formulation is carried along harmlessly. -/
theorem taylor_dvd_iff_rootMultiplicity (p : ℕ) [Fact p.Prime] (H : ℤ[X]) {r : ℕ}
    (hH : H.map (Int.castRingHom (ZMod p)) ≠ 0) :
    (∀ i, i < (H.map (Int.castRingHom (ZMod p))).rootMultiplicity (r : ZMod p) →
        (p : ℤ) ∣ taylorCoeff H r i) ∧
    ((p : ℤ) ∣ H.eval (r : ℤ) →
      ¬ ((p : ℤ) ∣ taylorCoeff H r ((H.map (Int.castRingHom (ZMod p))).rootMultiplicity (r : ZMod p)))) := by
  classical
  -- The order of vanishing of the reduced Taylor shift `(H mod p)(r + X)` at `0` is `s`.
  have hntd : ((H.map (Int.castRingHom (ZMod p))).taylor (r : ZMod p)).natTrailingDegree
      = (H.map (Int.castRingHom (ZMod p))).rootMultiplicity (r : ZMod p) := by
    rw [rootMultiplicity_eq_natTrailingDegree, taylor_apply]
  -- Reduction modulo `p` commutes with the Taylor shift.
  have hmap : (taylor (r : ℤ) H).map (Int.castRingHom (ZMod p))
      = (H.map (Int.castRingHom (ZMod p))).taylor (r : ZMod p) := by
    rw [map_taylor]
    simp only [Int.coe_castRingHom, Int.cast_natCast]
  constructor
  · intro i hi
    have h1 : ((H.map (Int.castRingHom (ZMod p))).taylor (r : ZMod p)).coeff i = 0 :=
      coeff_eq_zero_of_lt_natTrailingDegree (by rw [hntd]; exact hi)
    have h2 : ((taylor (r : ℤ) H).map (Int.castRingHom (ZMod p))).coeff i = 0 := by
      rw [hmap]; exact h1
    rw [coeff_map] at h2
    have : ((taylorCoeff H r i : ℤ) : ZMod p) = 0 := h2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (taylorCoeff H r i) p).mp this
  · intro _ hdvd
    have hGne : (H.map (Int.castRingHom (ZMod p))).taylor (r : ZMod p) ≠ 0 := by
      intro h
      exact hH ((taylor_eq_zero (r : ZMod p) (H.map (Int.castRingHom (ZMod p)))).mp h)
    have hne := coeff_natTrailingDegree_ne_zero.mpr hGne
    have h2 : ((taylor (r : ℤ) H).map (Int.castRingHom (ZMod p))).coeff
        ((H.map (Int.castRingHom (ZMod p))).rootMultiplicity (r : ZMod p)) = 0 := by
      rw [coeff_map]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (taylorCoeff H r _) p).mpr hdvd
    have hz : ((H.map (Int.castRingHom (ZMod p))).taylor (r : ZMod p)).coeff
        ((H.map (Int.castRingHom (ZMod p))).taylor (r : ZMod p)).natTrailingDegree = 0 := by
      rw [hntd, ← hmap]
      exact h2
    exact hne hz

end Work.KMTPlan.A6.ConcAux
