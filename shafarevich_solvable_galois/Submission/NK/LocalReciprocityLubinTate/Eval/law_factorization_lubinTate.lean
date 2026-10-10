import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.FormalGroup.Basic
import Submission.NK.LocalReciprocityLubinTate.Eval.X_one_dvd_law_sub_X_zero
import Submission.NK.LocalReciprocityLubinTate.Eval.law_factorization
import Submission.NK.LocalReciprocityLubinTate.LubinTate.FormalGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped ValuativeRel
open MvPowerSeries

namespace NK.LocalReciprocityLubinTate

universe u

/-- **The unit factorisation of the Lubin–Tate group law**: for every `LubinTateModule` over
`𝒪[F]` there is a unit `Θ` of the two-variable power series ring with
`F_π(X,Y) = X + Y·Θ(X,Y)`. -/
theorem LubinTateModule.exists_unit_factorization {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : ↥(ValuativeRel.valuation F).integer) (hπ : Irreducible π) (q : ℕ)
    (M : LubinTateModule (↥(ValuativeRel.valuation F).integer) π q) :
    ∃ Θ : MvPowerSeries (Fin 2) (↥(ValuativeRel.valuation F).integer), IsUnit Θ ∧
      (M.toLaw.law : MvPowerSeries (Fin 2) (↥(ValuativeRel.valuation F).integer)) =
        MvPowerSeries.X 0 + MvPowerSeries.X 1 * Θ :=
  Eval.FormalGroup.exists_unit_factorization M.toLaw.law
    (Eval.X_one_dvd_law_sub_X_zero M.toLaw.law)

end NK.LocalReciprocityLubinTate
