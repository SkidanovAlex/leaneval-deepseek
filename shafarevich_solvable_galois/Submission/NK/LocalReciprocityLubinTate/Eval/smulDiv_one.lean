import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.MvPowerSeries.Evaluation
import Submission.NK.LocalReciprocityLubinTate.Eval.TorsionAction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped ValuativeRel
open Polynomial MvPowerSeries

namespace NK.LocalReciprocityLubinTate.Eval

open LTtorsionRing

set_option linter.style.haveILetI false

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- **Milne's evaluation of `X`.**  Evaluating the power series `X` (the indeterminate) at the
class `τ` of `T` in `T_n = 𝒪[F][T]/(f^{(n)}(T))` returns `τ`: this is the defining property of
`MvPowerSeries.eval₂`, read through `MvPowerSeries.eval₂Hom`. -/
theorem evalTau_X (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q) :
    evalTau π hπ q n hq (MvPowerSeries.X 0) = LTtorsionRing.tau π q n := by
  letI : CompleteSpace (LTtorsionRing F π q n) := completeSpace_ltTorsionRing π hπ q n hq
  letI : T2Space (LTtorsionRing F π q n) := t2Space_ltTorsionRing π hπ q n hq
  rw [evalTau, MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_X]

/-- **The class `[1]_n` is the class `τ` of `T`.**  For the unit `1 ∈ 𝒪[F]`, the `1`-multiplication
series is `[1] = X` (`LubinTateModule.action_one`), so evaluating at `τ` gives `τ`. -/
theorem actionTau_one (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (O F) π q) :
    actionTau π hπ q n hq M 1 = LTtorsionRing.tau π q n := by
  rw [actionTau, M.action_one]
  exact evalTau_X π hπ q n hq

/-- **The unit of `𝒪[F]` acts trivially on the `π^n`-torsion points.**  With
`a · x = smulDiv π hπ q n hq M hx a = evMap x ([a]_n)`, the action of `1` sends the torsion point
`x ∈ Λ_n` to itself, because `[1]_n = τ` (`actionTau_one`) and `evMap x (τ) = x`
(`evMap_tau`). -/
theorem smulDiv_one {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (π : ↥(ValuativeRel.valuation F).integer) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (↥(ValuativeRel.valuation F).integer) π q)
    (x : AlgebraicClosure F) (hx : x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q n) :
    NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ q n hq M hx 1 = x := by
  show evMap π q n hq x hx (actionTau π hπ q n hq M 1) = x
  rw [actionTau_one π hπ q n hq M, evMap_tau π q n hq x hx]

end NK.LocalReciprocityLubinTate.Eval
