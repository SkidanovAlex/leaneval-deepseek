import Mathlib

namespace Work.WilE4.CAD

theorem rootMultiplicity_gcd_complex (f g : Polynomial ℂ) (hf : f ≠ 0) (hg : g ≠ 0) (z : ℂ) :
    (gcd f g).rootMultiplicity z = min (f.rootMultiplicity z) (g.rootMultiplicity z) := by
  have hgcd : gcd f g ≠ 0 := by
    intro h
    have hd : gcd f g ∣ f := gcd_dvd_left f g
    rw [h] at hd
    exact hf (zero_dvd_iff.mp hd)
  have ha : (Polynomial.X - Polynomial.C z) ^ (gcd f g).rootMultiplicity z ∣ gcd f g :=
    Polynomial.pow_rootMultiplicity_dvd (gcd f g) z
  apply le_antisymm
  · apply le_min
    · exact (Polynomial.le_rootMultiplicity_iff hf).mpr (ha.trans (gcd_dvd_left f g))
    · exact (Polynomial.le_rootMultiplicity_iff hg).mpr (ha.trans (gcd_dvd_right f g))
  · refine (Polynomial.le_rootMultiplicity_iff hgcd).mpr ?_
    exact dvd_gcd
      (dvd_trans (pow_dvd_pow _ (min_le_left _ _)) (Polynomial.pow_rootMultiplicity_dvd f z))
      (dvd_trans (pow_dvd_pow _ (min_le_right _ _)) (Polynomial.pow_rootMultiplicity_dvd g z))

end Work.WilE4.CAD
