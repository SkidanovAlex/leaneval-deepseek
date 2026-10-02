import Mathlib
import Submission.Work.Whitney.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The `n`-fold direct sum of line bundles over a common cover

This module contains the elementary vocabulary of the *flag bundle* form of the splitting principle:

* `Work.LerayHirsch.lineSumIndex n ι` — the index type of the `n`-fold direct sum of complex line
  bundles over a common cover `ι` (`PUnit` for `n = 0`, and `lineSumIndex n ι × ι` for `n + 1`), with
  the `Fintype` instance `Work.LerayHirsch.instFintypeLineSumIndex`;
* `Work.LerayHirsch.lineSumCore n L` — the `n`-fold direct sum
  `L 0 ⊕ L 1 ⊕ … ⊕ L (n-1)` of a family of complex line bundles over a common cover, in the standard
  fibre `EuclideanSpace ℂ (Fin n)`; it is defined by recursion as
  `whitneySum (lineSumCore n L) (L (Fin.last n))`, so the *last* summand is the outermost one.

The point of a *common* cover is that no reindexing of the summands is needed: the statement of the
splitting principle (`Work.LerayHirsch.SplittingPrinciple`, in `Submission/Work/LerayHirsch/FlagBundle.lean`)
says that `π^*E` is isomorphic to `lineSumCore m L` for a single family `L` of line bundles over one
cover `ιL` of the flag bundle.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

/-! ## The cover index type -/

/-- **The index type of the `n`-fold direct sum of line bundles over a common cover `ι`**: `PUnit`
for `n = 0` and `lineSumIndex n ι × ι` for `n + 1`, matching the cover of the recursive
`Work.Whitney.whitneySum`. -/
def lineSumIndex : ℕ → Type → Type
  | 0, _ => PUnit
  | n + 1, ι => lineSumIndex n ι × ι

/-- The index type of the `n`-fold direct sum of line bundles over a finite cover is finite. -/
instance instFintypeLineSumIndex (n : ℕ) (ι : Type) [Fintype ι] : Fintype (lineSumIndex n ι) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
      haveI := ih
      exact inferInstanceAs (Fintype (lineSumIndex n ι × ι))

/-- The index type of the `n`-fold direct sum of line bundles over an inhabited cover is
inhabited. -/
instance instInhabitedLineSumIndex (n : ℕ) (ι : Type) [Inhabited ι] :
    Inhabited (lineSumIndex n ι) := by
  induction n with
  | zero => exact inferInstanceAs (Inhabited PUnit)
  | succ n ih =>
      haveI := ih
      exact inferInstanceAs (Inhabited (lineSumIndex n ι × ι))

@[simp] theorem lineSumIndex_zero (ι : Type) : lineSumIndex 0 ι = PUnit := rfl

@[simp] theorem lineSumIndex_succ (n : ℕ) (ι : Type) :
    lineSumIndex (n + 1) ι = (lineSumIndex n ι × ι) := rfl

/-! ## The iterated direct sum -/

/-- **The `n`-fold direct sum of a family of complex line bundles over a common cover**, in the
standard fibre `EuclideanSpace ℂ (Fin n)` and over the cover `lineSumIndex n ι`:
`lineSumCore (n+1) L = whitneySum (lineSumCore n (L ∘ Fin.castSucc)) (L (Fin.last n))`. -/
noncomputable def lineSumCore {P : Type} [TopologicalSpace P] {ι : Type} :
    (n : ℕ) → (Fin n → VectorBundleCore ℂ P (EuclideanSpace ℂ (Fin 1)) ι) →
      VectorBundleCore ℂ P (EuclideanSpace ℂ (Fin n)) (lineSumIndex n ι)
  | 0, _ => trivialVectorBundleCore ℂ P (EuclideanSpace ℂ (Fin 0)) PUnit
  | n + 1, L => Work.Whitney.whitneySum (lineSumCore n (L ∘ Fin.castSucc)) (L (Fin.last n))

@[simp] theorem lineSumCore_zero {P : Type} [TopologicalSpace P] {ι : Type}
    (L : Fin 0 → VectorBundleCore ℂ P (EuclideanSpace ℂ (Fin 1)) ι) :
    lineSumCore 0 L = trivialVectorBundleCore ℂ P (EuclideanSpace ℂ (Fin 0)) PUnit := rfl

@[simp] theorem lineSumCore_succ {P : Type} [TopologicalSpace P] {ι : Type} (n : ℕ)
    (L : Fin (n + 1) → VectorBundleCore ℂ P (EuclideanSpace ℂ (Fin 1)) ι) :
    lineSumCore (n + 1) L
      = Work.Whitney.whitneySum (lineSumCore n (L ∘ Fin.castSucc)) (L (Fin.last n)) := rfl

end

end Work.LerayHirsch
