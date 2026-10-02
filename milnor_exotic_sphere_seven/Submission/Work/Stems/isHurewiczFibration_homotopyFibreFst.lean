import Mathlib
import Submission.Work.RatHurewicz.isSerreFibration_homotopyFibreFst
import Submission.Work.StemsB.HurewiczFibration

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The first projection of the homotopy fibre is a Hurewicz fibration

`Work.RatHurewicz.homotopyFibreFst i a₀ : homotopyFibre i a₀ → A` is the first projection of the
homotopy fibre of `i : C(A,X)` over `a₀`, i.e. of the pullback of the path–loop fibration
`evalOne X (i a₀) : PathSpace X (i a₀) → X` along `i`.  This is the same map whose Serre fibration
property is proved in `Submission/Work/RatHurewicz/isSerreFibration_homotopyFibreFst.lean`
(`Work.RatHurewicz.isSerreFibration_homotopyFibreFst`); here we record the stronger Hurewicz
statement, which is what the cofibre/fibre-transport machinery of the workspace consumes.

The proof is the Serre proof run at an *arbitrary* test space `Z`: the path–loop fibration is a
Hurewicz fibration (`Work.StemsB.isHurewiczFibration_evalOne`), base change preserves the homotopy
lifting property (`Work.StemsB.hasHLP_pullback`), and the homotopy lifting property is invariant
under a change of the total space along a mutually inverse pair of continuous maps
(`Work.RatHurewicz.hasHLP_comp_of_inverse`), which identifies the two models of the pullback
(`bundlePullback` and `Pullback`, differing only in the order of the coordinates) along
`Work.RatHurewicz.pullbackSnd_comp_bundlePullbackToPullback`.
-/

open scoped Topology unitInterval

namespace Work.Stems

/-- **The first projection of the homotopy fibre of `i : C(A,X)` is a Hurewicz fibration.**  It is
the base change of the path–loop fibration (a Hurewicz fibration) along `i`, up to the coordinate
swap between the two models of the pullback. -/
theorem isHurewiczFibration_homotopyFibreFst {X : Type} [TopologicalSpace X] {A : Type}
    [TopologicalSpace A] (i : C(A, X)) (a₀ : A) :
    Work.StemsB.IsHurewiczFibration (Work.RatHurewicz.homotopyFibreFst i a₀) := by
  intro Z _
  -- the base change of the path–loop fibration along `i` has the HLP with respect to `Z`
  have hHLP : Work.StemsB.HasHLP
      (Work.StemsB.pullbackSnd (Work.StemsB.evalOne X (i a₀)) i) Z :=
    Work.StemsB.hasHLP_pullback (Work.StemsB.evalOne X (i a₀)) i
      (Work.StemsB.isHurewiczFibration_evalOne X (i a₀) Z)
  -- and the coordinate swap carries it to the HLP of the first projection of the homotopy fibre
  have htr : Work.StemsB.HasHLP (Work.StemsB.bundlePullbackFst (x₀ := i a₀) A i) Z := by
    have h := Work.RatHurewicz.hasHLP_comp_of_inverse
      (p := Work.StemsB.pullbackSnd (Work.StemsB.evalOne X (i a₀)) i)
      (φ := Work.RatHurewicz.bundlePullbackToPullback (i a₀) A i)
      (ψ := Work.RatHurewicz.pullbackToBundlePullback (i a₀) A i)
      (fun p => Work.RatHurewicz.pullbackToBundlePullback_to (i a₀) A i p)
      (fun q => Work.RatHurewicz.bundlePullbackToPullback_to (i a₀) A i q) hHLP
    rwa [Work.RatHurewicz.pullbackSnd_comp_bundlePullbackToPullback] at h
  exact htr

end Work.Stems
