import Mathlib
import Submission.Work.FIArea6Hecke.R.chiPrimeDefs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea4.GaussMoebiusCore

/-!
# `Submission.Work.FIArea6Hecke.R.chiPrimeAgree`

The elementary agreement between the normalised character `Work.FIArea6Hecke.R.chiPrime d chi`
(`chiPrime d chi z = chi (primAssoc z)` on the units modulo `4d`) and `chi` on the *primary* units:
for a primary `z` the primary associate of `z` is `z` itself, so `chiPrime d chi z = chi z`.
-/
set_option autoImplicit false

namespace Work.FIArea6Hecke.R

/-- **`chiPrime d chi` agrees with `chi` on the primary units.** -/
theorem chiPrime_eq_chi_of_primary {d : ℕ} {chi : GaussianInt → ℂ} {z : GaussianInt}
    (hzp : Work.FIPlan.IsPrimary z) (hzu : Work.FIArea5.S16Hecke.IsUnitMod4d d z) :
    Work.FIArea6Hecke.R.chiPrime d chi z = chi z := by
  rw [Work.FIArea6Hecke.R.chiPrime_of_unit hzu, Work.FIArea4.primAssoc_eq_self hzp]

end Work.FIArea6Hecke.R
