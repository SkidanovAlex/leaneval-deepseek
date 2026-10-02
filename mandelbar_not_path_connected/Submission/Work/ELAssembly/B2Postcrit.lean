/-
# `ELAssembly` — `b₂` is not postcritical, from the bundle

The field `b2_not_postcrit` of `Work.ELRig.B2Data` — no iterate of the critical point `0` hits the
branch point `b₂` — is **not** an independent hypothesis of the assembly: it follows from

* the critical orbit of `RootParabolic.crit` (`(F c)^[n] c → z₁`, never hitting `z₁`),
* `Tsq c b₂ = b₂` (itself derived from the three tripod rays, `Assembly.lean`),
* the orbit portrait `hzero` at `z₁` (which rules out `b₂ = z₁`: the ray `22/63` lands at `b₂`,
  and `22/63 ∉ {371/1023, 404/1023}`).

This file performs that reduction on the bundle `Work.ELAssembly.AssemblyInputs`, so that
`b2_not_postcrit` need not be assumed by a caller.
-/
import Mathlib
import Submission.Work.ELAssembly.Defs
import Submission.Work.ELAssembly.Inputs
import Submission.Work.ELAssembly.Assembly
import Submission.Work.ELAssembly.b2_not_postcrit_of

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **`b₂` is not postcritical**, from the bundle: the critical orbit, the periodicity of `b₂`
under `Tsq c` and the orbit portrait at `z₁`. -/
theorem b2_not_postcrit_of_inputs {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.ELNest.FlowerData c d.z₁} (A : AssemblyInputs c d fl) :
    ∀ n : ℕ, (Tantibar c)^[n] 0 ≠ A.T.y := by
  have heq : (fun n : ℕ => (Work.Landing.Tsq c)^[5 * n] c)
      = fun n : ℕ => (Work.EL.F c)^[n] c := by
    funext n
    rw [Function.iterate_mul]
    rfl
  refine b2_not_postcrit_of d.hN A.hzero ⟨?_, ?_⟩
    (b2_fix_of_lands d.hN d.bottcher A.T.lands₁ A.T.lands₂) A.T.lands₁
  · rw [heq]; exact d.crit.1
  · intro n
    have hn : (Work.Landing.Tsq c)^[5 * n] c = (Work.EL.F c)^[n] c := by
      rw [Function.iterate_mul]
      rfl
    rw [hn]
    exact d.crit.2 n

end Work.ELAssembly
