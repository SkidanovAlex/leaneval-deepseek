import Mathlib

namespace Work.WilE4.CAD

theorem map_ofReal_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) :
    (p.map (algebraMap ℝ ℂ)) ≠ 0 :=
  (Polynomial.map_ne_zero_iff (f := algebraMap ℝ ℂ) Complex.ofReal_injective).mpr hp

end Work.WilE4.CAD
