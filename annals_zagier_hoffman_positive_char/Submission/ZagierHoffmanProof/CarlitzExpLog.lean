import Submission.ZagierHoffmanProof.CarlitzModule
import Submission.Commons.RingTheory.PowerSeries.subst_injective_of_constantCoeff_eq_zero

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Polynomial
open scoped BigOperators

/-!
# The Carlitz exponential and logarithm are mutually inverse

`Submission.ZagierHoffmanProof.CarlitzLog` proves `log_C ∘ e_C = id` through the functional
equations.  Here we deduce the converse `e_C ∘ log_C = id`, using the commons lemma
`Commons.RingTheory.PowerSeries.subst_injective_of_constantCoeff_eq_zero`: substitution into a
series `g` with `constantCoeff g = 0` and `coeff 1 g` a unit is injective.

Indeed, from `log_C ∘ e_C = id` we get `(e_C ∘ log_C) ∘ e_C = e_C ∘ (log_C ∘ e_C) = e_C = id ∘ e_C`,
and injectivity of `· ∘ e_C` finishes.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

section Inv

open PowerSeries

lemma hasSubst_carlitzLog : PowerSeries.HasSubst (carlitzLog F) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by
    rw [carlitzLog, PowerSeries.constantCoeff_mk]
    exact carlitzLCoeff_eq_zero F (fun i h => by
      have h1 : 0 < Nat.card F ^ i := pow_pos (by have := carlitz_card_ge_two F; omega) i
      omega))

lemma isUnit_coeff_one_carlitzExp : IsUnit (PowerSeries.coeff 1 (carlitzExp F)) := by
  rw [carlitzExp_coeff_one F]
  exact isUnit_one

/-- ★★ **The Carlitz exponential and the Carlitz logarithm are mutually inverse**:
`e_C(log_C z) = z`. -/
theorem carlitzExp_subst_log : (carlitzExp F).subst (carlitzLog F) = PowerSeries.X := by
  have h1 : PowerSeries.subst (carlitzExp F)
        (PowerSeries.subst (carlitzLog F) (carlitzExp F)) = carlitzExp F := by
    rw [PowerSeries.subst_comp_subst_apply (a := carlitzLog F) (b := carlitzExp F)
        (f := carlitzExp F) (hasSubst_carlitzLog F) (hasSubst_carlitzExp F),
      carlitzLog_subst_exp, PowerSeries.X_subst (carlitzExp F)]
  have h2 : PowerSeries.subst (carlitzExp F) (PowerSeries.X : PowerSeries (RatFunc F))
      = carlitzExp F :=
    PowerSeries.subst_X (a := carlitzExp F) (hasSubst_carlitzExp F)
  refine Commons.RingTheory.PowerSeries.subst_injective_of_constantCoeff_eq_zero
    (constantCoeff_carlitzExp F) (isUnit_coeff_one_carlitzExp F) ?_
  show PowerSeries.subst (carlitzExp F) (PowerSeries.subst (carlitzLog F) (carlitzExp F))
      = PowerSeries.subst (carlitzExp F) (PowerSeries.X : PowerSeries (RatFunc F))
  rw [h1, h2]

/-- The two inverse laws, packaged. -/
theorem carlitzLog_exp_inverse :
    (carlitzLog F).subst (carlitzExp F) = PowerSeries.X
      ∧ (carlitzExp F).subst (carlitzLog F) = PowerSeries.X :=
  ⟨carlitzLog_subst_exp F, carlitzExp_subst_log F⟩

end Inv

end ZagierHoffmanPositiveChar
