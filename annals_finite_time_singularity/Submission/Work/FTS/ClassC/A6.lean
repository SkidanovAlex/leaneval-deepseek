/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS.ClassC.A6` — the Hamel step on `ClassC` (design (A), item A6)

Item A6 of the design: given a *linear* class `C` of profiles and a relation `P` on
(`profile`, `stream function`) which contains `(0,0)`, is closed under linear combinations over
`C`, and has a witness over every element of `C`, there is a **linear** operator
`E : Fn →ₗ[ℝ] Fn` whose values on `C` are witnesses.

The work is done once and for all in `Work.FTS.ClassC.exists_linear_selector` (the `GalClass`
version of `FTS/EllSol/Hamel.lean` abstracted to an arbitrary predicate `C : Fn → Prop`).
This module instantiates it at `C := ClassC α`, using the two closure theorems of `A1`
(`classC_add`, `classC_smul`) and the inhabitation `classC_zero`.

Everything is `sorry`-free.
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.ClassC.exists_linear_selector

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **A6: the Hamel step on `ClassC`.**

No uniqueness of the elliptic solution is used: the values of `E` on a Hamel basis of the
subspace spanned by `ClassC` are chosen with `Classical.choose`, and `E` is extended to all of
`Fn` by `LinearMap.exists_extend`. -/
theorem exists_linear_selector_classC {α : ℝ} {P : Fn → Fn → Prop}
    (hP0 : P 0 0)
    (hPlin : ∀ g g' Ψ Ψ' : Fn, ∀ c : ℝ, ClassC α g → ClassC α g' →
      P g Ψ → P g' Ψ' → P (g + c • g') (Ψ + c • Ψ'))
    (hex : ∀ g, ClassC α g → ∃ Ψ, P g Ψ) :
    ∃ E : Fn →ₗ[ℝ] Fn, ∀ g, ClassC α g → P g (E g) :=
  exists_linear_selector (α := α) (classC_zero α)
    (fun g g' c hg hg' => classC_add hg (classC_smul c hg')) hP0 hPlin hex

end Work.FTS.ClassC
