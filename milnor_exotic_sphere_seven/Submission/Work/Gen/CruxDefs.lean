import Mathlib
import Submission.Work.Gen.ModelKDefs
import Submission.Work.LerayHirsch.FibreBasis

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Notation for the fibre of the projectivisation

Two maps that occur in every fibre computation of the `ψ`-analysis of the crux
(`Submission/Work/Gen/NOTES_psi_delta.md`), named here so that the statements below stay readable:

* `Work.Gen.constFibre Z b : C(ProjFibre Z b, B)` — the constant map (for a bundle `Z` over `B`);
  pulling a cohomology class back along it computes its *value at `b`*;
* `Work.Gen.fibreIdent Z b : C(ProjFibre Z b, ProjSpace (trivCore m))` — the canonical
  identification of the fibre of `P(Z)` over `b` with the model projectivisation `P(ε^m)`
  (`Work.LerayHirsch.projUniv m ∘ projClassFibre Z b`).
-/

namespace Work.Gen

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {m : ℕ}

/-- The constant map from a fibre of `P(Z)` to the base. -/
def constFibre (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    C(Work.LerayHirsch.ProjFibre Z b, B) :=
  ContinuousMap.const _ b

/-- The canonical identification of the fibre of `P(Z)` over `b` with `P(ε^m)`. -/
def fibreIdent (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    C(Work.LerayHirsch.ProjFibre Z b, Work.LerayHirsch.ProjSpace (Work.LerayHirsch.trivCore m)) :=
  (Work.LerayHirsch.projUniv m).comp (Work.LerayHirsch.projClassFibre Z b)

/-- **The top index of the Leray–Hirsch decomposition at level `n - 1`**: the index at which the
coefficient of a class of `H^{2(n-1)}` has degree `0`. -/
abbrev topCoeffIdx {n : ℕ} : {j : Fin (n + 1) // (j : ℕ) ≤ n - 1} :=
  ⟨⟨n - 1, by omega⟩, le_rfl⟩

theorem topCoeffIdx_val {n : ℕ} : ((topCoeffIdx (n := n) : {j : Fin (n + 1) // (j : ℕ) ≤ n - 1}) : ℕ)
    = n - 1 := rfl

/-- The coefficient degree at the top index is `0`. -/
theorem topCoeffIdx_degree {n : ℕ} :
    2 * ((n - 1) - ((topCoeffIdx (n := n) : {j : Fin (n + 1) // (j : ℕ) ≤ n - 1}) : ℕ)) = 2 * 0 := by
  rw [topCoeffIdx_val]
  omega

/-- The coefficient degree at the top index is `0` (both orientations). -/
theorem topCoeffIdx_degree' {n : ℕ} :
    2 * 0 = 2 * ((n - 1) - ((topCoeffIdx (n := n) : {j : Fin (n + 1) // (j : ℕ) ≤ n - 1}) : ℕ)) :=
  (topCoeffIdx_degree (n := n)).symm

end

end Work.Gen
