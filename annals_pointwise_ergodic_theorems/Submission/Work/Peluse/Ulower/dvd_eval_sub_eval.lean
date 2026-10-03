import Mathlib

namespace Work.Peluse.Ulower

/-- Integer polynomials preserve congruences: `t ∣ y - y'` implies `t ∣ P y - P y'`. -/
theorem dvd_eval_sub_eval {P : Polynomial ℤ} {t y y' : ℤ} (h : t ∣ y - y') :
    t ∣ P.eval y - P.eval y' :=
  dvd_trans h (P.sub_dvd_eval_sub y y')

end Work.Peluse.Ulower
