/-
# `Submission.Work.FIArea6Hecke.R.chiPrimeDefs`

The **real character attached to a self-dual strict character** — the construction behind
`Work.FIArea6Hecke.R.exists_real_pair_of_selfDual`.

A strict character `χ` modulo `4d` is a character of `(ℤ[i]/4dℤ[i])^*` extended by zero off the
units.  When `χ` is *self-dual*, i.e. `ψ_{χ,m}(z) = χ(z)(z/|z|)^m` is `±1` on the primary units
(`Work.FIArea6Hecke.R.SelfDual`, and `SelfDual` forces `m = 0`), `χ` is only known to be real on
the *primary* units; on the other units it may take non-real values.  The fix is the classical one:
normalise an odd `z` to its primary associate before evaluating `χ`,

  `chiPrime d χ z = χ (primAssoc z)`  for `z` a unit modulo `4d`,  `= 0` otherwise.

This is the same construction as the "real character" `χ'` of *FI* §16 (see the paper's
`χ' z = χ(ε⁻¹z)` with `ε ∈ μ₄` chosen so that `ε⁻¹z` is primary).  Since `primAssoc` is
multiplicative on the odd elements (`Work.FIArea6Hecke.R.primAssoc_mul_odd`) and --- this is the
arithmetic content, `Work.FIArea6Hecke.R.primAssoc_congr_of_isUnitMod4d` --- the primary associate
of a *unit* modulo `4d` depends only on its class modulo `4d`, `chiPrime d χ` is again a strict
character modulo `4d` (`Work.FIArea6Hecke.R.chiPrime_periodic`,
`Work.FIArea6Hecke.R.chiPrime_axioms`), it is real-valued on the (self-dual) primary elements, and
it agrees with `χ` on the primary elements, hence has the same Hecke eigenvalues and `L`-series.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea4.GaussMoebiusCore

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open Work.FIPlan

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The **normalised character** `χ'(z) = χ(primAssoc z)` on the units modulo `4d`, extended by
zero off the units. -/
def chiPrime (d : ℕ) (chi : GaussianInt → ℂ) : GaussianInt → ℂ :=
  fun z => if Work.FIArea5.S16Hecke.IsUnitMod4d d z then chi (Work.FIArea4.primAssoc z) else 0

/-- Value of `chiPrime` at a unit. -/
theorem chiPrime_of_unit {d : ℕ} {chi : GaussianInt → ℂ} {z : GaussianInt}
    (h : Work.FIArea5.S16Hecke.IsUnitMod4d d z) :
    chiPrime d chi z = chi (Work.FIArea4.primAssoc z) := by
  rw [chiPrime]; exact if_pos h

/-- `chiPrime` vanishes off the units modulo `4d` (definitional). -/
theorem chiPrime_of_not_unit {d : ℕ} {chi : GaussianInt → ℂ} {z : GaussianInt}
    (h : ¬ Work.FIArea5.S16Hecke.IsUnitMod4d d z) : chiPrime d chi z = 0 := by
  rw [chiPrime]; exact if_neg h

end

end Work.FIArea6Hecke.R
