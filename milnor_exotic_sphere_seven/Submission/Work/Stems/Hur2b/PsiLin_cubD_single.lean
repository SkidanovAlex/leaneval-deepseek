import Mathlib
import Submission.Work.Stems.Hur2b.Assembly
import Submission.Work.Stems.Hur2b.assembly_homotopic_const

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `(Y)`: `Ψ` kills the boundary of every 3-cube

`Work.Stems.Hur2b.PsiLin_cubD_single`: for every 3-cube `τ : I³ → X` (with `X` simply connected),
`PsiLin x₀ (cubD 2 X (single τ 1)) = 0` in `π₂(X,x₀)`.  This is Hutchings' `(2.5)`.

The combinatorial reduction (`Submission/Work/Stems/Hur2b/Assembly.lean`) identifies `PsiLin` of
the boundary of a 3-cube with the class of the explicit **assembly** `assembly x₀ τ`: the six
fillings `Ψ(τ_{i,b})` concatenated in the square, with the sign `(-1)^{i+b}` realised by reversing
one coordinate.

What remains, and is proved here, is the *geometric core* `assembly_homotopic_const`: the assembly
is null as a *based* 2-cube.  This is where the 3-cube `τ` is used.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical
open Work.Stems.Hur2

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem PsiLin_cubD_single {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x₀ : X)
    (τ : ContinuousMap (Work.Stems.Cubical.IC 3) X) :
    Work.Stems.Hur2.PsiLin x₀ (Work.Stems.Cubical.cubD 2 X (Finsupp.single τ 1)) = 0 := by
  rw [PsiLin_cubD_single_expand, expand_eq_assembly]
  have h := assembly_homotopic_const x₀ τ
  rw [show cl x₀ (assembly x₀ τ) = 1 from Quotient.sound h]
  simp

end Work.Stems.Hur2b
