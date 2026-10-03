import Mathlib
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea5.S16Hecke.thetaHol_twist_eq
import Submission.Work.FIArea5.S16Hecke.ramanujanSum_vanishes

namespace Work.FIArea6Hecke.R

/-- Every primary Gaussian integer is a unit modulo `4`, hence the principal strict character
modulo `4` takes the value `1` at it.

`IsPrimary z` gives `z.re` odd and `z.im` even, so `z.re + z.im` is odd; by
`dvd_oneAddI_iff_even` this means `(1+i) ∤ z`, i.e. `z` is coprime to `2`, hence (as `4 = 2²`)
to `4`.  Finally `IsUnitMod4d 1 z ↔ IsCoprime z 4`. -/
theorem principalStrict_one_of_isPrimary {z : GaussianInt} (hz : Work.FIPlan.IsPrimary z) :
    Work.FIArea6Hecke.principalStrict 1 z = 1 := by
  apply Work.FIArea6Hecke.principalStrict_of_unit
  rw [Work.FIArea5.S16Hecke.RamAux.isUnitMod4d_iff_isCoprime]
  rw [show (((4 * 1 : ℕ) : ℤ) : GaussianInt) = (((2 : ℕ) ^ 2 : ℕ) : GaussianInt) from by norm_num]
  rw [Work.FIArea5.S16Hecke.RamAux.isCoprime_two_pow_iff z (by norm_num)]
  rw [Work.FIArea5.S16Hecke.GaussBasic.dvd_oneAddI_iff_even]
  rw [Int.not_even_iff_odd]
  exact (Work.FIArea5.S16Hecke.GaussBasic.odd_add_even_iff hz.2.1).mpr hz.1

end Work.FIArea6Hecke.R
