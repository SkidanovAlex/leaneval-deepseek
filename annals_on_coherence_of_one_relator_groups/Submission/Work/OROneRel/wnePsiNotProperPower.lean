import Mathlib
import Submission.Work.OROneRel.psiSubstDefs
import Submission.Work.OROneRel.not_isProperPower_subst
import Submission.Work.OROneRel.isProperPower_subst_iff_powSubst

namespace Work.OROneRel

universe u

/-- The Magnus/Putman substitution `Psi r t x` of `psiSubstDefs` is exactly the substitution
`subst t x p q` of the Freiheitssatz case 2, with `p = σ_x r` and `q = σ_t r`: both send `t` to
`t ^ p`, `x` to `x * t ^ (-q)` and fix every other generator. -/
theorem Psi_eq_subst {β : Type u} (R : FreeGroup β) {y x : β} (hxy : x ≠ y) :
    Psi R y x = subst y x (Multiplicative.toAdd (sigma x R)) (Multiplicative.toAdd (sigma y R)) := by
  apply FreeGroup.ext_hom
  intro a
  by_cases ha : a = y
  · subst ha
    rw [Psi_of_eq_t, ips_subst_of_t]
  · by_cases hb : a = x
    · subst hb
      rw [Psi_of_eq_x hxy, ips_subst_of_x hxy]
    · rw [Psi_of_ne ha hb, ips_subst_of_ne ha hb]

/-- The substituted relator `Psi R y x R` is not a proper power when `R` is cyclically reduced, not
a proper power, and `σ_x R ≠ 0`.  `Psi R y x` is the Case-2 substitution, which makes the exponent
sum in `y` vanish, and `not_isProperPower_subst` is precisely the corresponding statement for it. -/
theorem wnePsiNotProperPower {β : Type u} (R : FreeGroup β) {y x : β} (hxy : x ≠ y)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator R)
    (hpp : ¬ Work.OROneRel.IsProperPower R)
    (hpx : Multiplicative.toAdd (Work.OROneRel.sigma x R) ≠ 0) :
    ¬ Work.OROneRel.IsProperPower (Work.OROneRel.Psi R y x R) := by
  rw [Psi_eq_subst R hxy]
  exact not_isProperPower_subst R hxy hcyc hpp hpx

end Work.OROneRel
