import Mathlib.CategoryTheory.Action.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.MvPowerSeries.Evaluation
import Submission.NK.LocalReciprocityLubinTate.Eval.TorsionInstances
import Submission.NK.LocalReciprocityLubinTate.Eval.continuous_algebraMap_ltTorsionRing
import Submission.NK.LocalReciprocityLubinTate.Eval.evMap_tau
import Submission.NK.LocalReciprocityLubinTate.Eval.hasEval_ltTorsionRing
import Submission.NK.LocalReciprocityLubinTate.LubinTate.FormalGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped ValuativeRel
open Polynomial MvPowerSeries

namespace NK.LocalReciprocityLubinTate.Eval

noncomputable section

universe u

open LTtorsionRing

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

section EvalTau

variable (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)

/-- **Evaluation of a power series over `𝒪[F]` at `τ`.**  Milne's evaluation `MvPowerSeries.eval₂`
is a ring homomorphism at a point satisfying `HasEval`; here the point is the class `τ` of `T` in
`T_n = 𝒪[F][T]/(f^{(n)}(T))`, which is topologically nilpotent for the `(π)`-adic topology
(`hasEval_ltTorsionRing`).  The coefficient ring `𝒪[F]` carries the discrete structure
(`instDiscreteUniformityO`, `instDiscreteTopologicalSpaceO` in `Eval/TorsionRing.lean`), which is the
one `MvPowerSeries.subst` is defined with. -/
noncomputable def evalTau : MvPowerSeries (Fin 1) (O F) →+* LTtorsionRing F π q n :=
  letI : CompleteSpace (LTtorsionRing F π q n) := completeSpace_ltTorsionRing π hπ q n hq
  letI : T2Space (LTtorsionRing F π q n) := t2Space_ltTorsionRing π hπ q n hq
  MvPowerSeries.eval₂Hom (φ := algebraMap (O F) (LTtorsionRing F π q n))
    (a := fun _ : Fin 1 => tau π q n) continuous_of_discreteTopology
    (hasEval_ltTorsionRing π q n hq)

end EvalTau

section Action

variable (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
  (M : LubinTateModule (O F) π q)

/-- **The `a`-multiplication series `[a]` of the Lubin–Tate module, evaluated at `τ`.** -/
noncomputable def actionTau (a : O F) : LTtorsionRing F π q n :=
  evalTau π hπ q n hq (M.action a)

theorem actionTau_pi :
    actionTau π hπ q n hq M π = evalTau π hπ q n hq M.toLaw.piEndo := by
  rw [actionTau, M.action_pi]

end Action

section Smul

variable (π : O F) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
  (M : LubinTateModule (O F) π q)

/-- **The `𝒪[F]`-action on the `π^n`-torsion points**: for `x ∈ Λ_n` and `a ∈ 𝒪[F]`, the point
`a · x = [a](x)`, computed in the ambient ring `T_n` and transported by `evMap x`. -/
noncomputable def smulDiv {x : AlgebraicClosure F} (hx : x ∈ LTdivisionSet F (π : F) q n)
    (a : O F) : AlgebraicClosure F :=
  evMap π q n hq x hx (actionTau π hπ q n hq M a)

end Smul

end

end NK.LocalReciprocityLubinTate.Eval
