import Mathlib
import Submission.Work.RatHurewicz.Basic
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.isSerreFibration_evalOne
import Submission.Work.StemsB.BundlePullback
import Submission.Work.StemsB.fibrationLES_of_serre
import Submission.Work.StemsB.LoopShiftShifted

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Relative homotopy groups and the long exact sequence of a pair

(draft; see the final version)
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.RatHurewicz

noncomputable section

open Work.StemsB

variable {X : Type} [TopologicalSpace X] {A : Type} [TopologicalSpace A]

/-- The homotopy fibre of `i : C(A,X)` over the base point `i a₀`: the space of pairs `(a, γ)`
with `γ` a path in `X` from `i a₀` to `i a`. -/
abbrev homotopyFibre (i : C(A, X)) (a₀ : A) : Type := bundlePullback X (i a₀) A i

example (i : C(A, X)) (a₀ : A) : TopologicalSpace (homotopyFibre i a₀) :=
  inferInstanceAs (TopologicalSpace (bundlePullback X (i a₀) A i))

/-- The constant path in the path space `PathSpace X x₀`. -/
def pathSpaceConst (X : Type) [TopologicalSpace X] (x₀ : X) : PathSpace X x₀ :=
  ⟨ContinuousMap.const I x₀, rfl⟩

/-- The base point of the homotopy fibre: the pair `(a₀, constant path at i a₀)`. -/
def homotopyFibreBasepoint (i : C(A, X)) (a₀ : A) : homotopyFibre i a₀ :=
  ⟨(a₀, pathSpaceConst X (i a₀)), rfl⟩

/-- The first projection of the homotopy fibre, `(a,γ) ↦ a`; a fibration with fibre `Ω X`. -/
def homotopyFibreFst (i : C(A, X)) (a₀ : A) : C(homotopyFibre i a₀, A) :=
  bundlePullbackFst (X := X) (x₀ := i a₀) A i

/-- **The relative homotopy group** `πₙ(X,A,a₀)` of the "pair" `i : A → X`, modelled as the `n`-th
homotopy group of the homotopy fibre of `i`; equivalently (for `n ≥ 2`) the classical relative
homotopy group `π_{n+1}(X,A,a₀)`. -/
abbrev RelHomotopyGroup (i : C(A, X)) (a₀ : A) (n : ℕ) : Type :=
  HomotopyGroup (Fin n) (homotopyFibre i a₀) (homotopyFibreBasepoint i a₀)

end

end Work.RatHurewicz
