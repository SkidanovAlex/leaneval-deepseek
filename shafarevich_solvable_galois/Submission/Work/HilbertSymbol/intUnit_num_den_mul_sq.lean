import Mathlib.Analysis.Normed.Ring.Lemmas
import Submission.Work.HilbertSymbol.Places
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- For `a : ℚˣ`, writing `a = num / den` in lowest terms, the identity
`a * (intUnit den)^2 = intUnit (num * den)` holds in `ℚˣ`: both sides are the
rational number `a * den^2 = num * den`. -/
theorem intUnit_num_den_mul_sq (a : ℚˣ) :
    a * (intUnit ((a : ℚ).den : ℤ) (by exact_mod_cast (a : ℚ).den_ne_zero)) ^ 2
      = intUnit ((a : ℚ).num * ((a : ℚ).den : ℤ))
          (by
            refine mul_ne_zero ?_ ?_
            · exact Rat.num_ne_zero.mpr a.ne_zero
            · exact_mod_cast (a : ℚ).den_ne_zero) := by
  apply Units.ext
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, intUnit_coe]
  push_cast
  have hd : ((a : ℚ).den : ℚ) ≠ 0 := by exact_mod_cast (a : ℚ).den_ne_zero
  have h := Rat.num_div_den (a : ℚ)
  rw [div_eq_iff hd] at h
  rw [h]
  ring

end Work.HilbertSymbol
