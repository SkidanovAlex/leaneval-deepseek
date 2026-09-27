import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLComp.LeafDefs

/-!
# Shared vocabulary for the construction of leaf-wise measures (Pisa §5–6)

Vocabulary common to the pieces of the proof of `Work.EKLRelCross.leafwise_exists`
(Pisa Theorem 6.3: existence of leaf-wise measures for a horospherical subgroup
`U ≤ SL₃(ℝ)`).

* `MSAlgG α` — a σ-algebra on `α`, wrapped so that a *local hypothesis* of class type
  `MeasurableSpace α` does not get captured by instance search (the hazard of
  `EKLContract/NOTES.md`: Mathlib's `Measure`, `Kernel`, `condExpKernel` all bind the ambient
  `MeasurableSpace` as an instance argument).
* `kappa μ M x` — the *conditional measure* of `μ` given the σ-algebra `M.m`, at the point `x`
  (Mathlib's `ProbabilityTheory.condExpKernel`), for `μ` a finite measure on a standard Borel
  space.  It satisfies Pisa 5.9(i): `∫ f d(kappa μ M x) = μ[f | M.m] x` for `μ`-a.e. `x`.
* `atomOf M x` — the atom of the wrapped σ-algebra at `x` (Pisa's `[x]_A`).
-/

open MeasureTheory Topology Filter
open scoped ENNReal

set_option linter.unusedVariables false

namespace Work.EKLRelCross

open Work.EKLContract Work.EKLComp

/-- A σ-algebra on `α`, wrapped in a structure.  Two purposes: (i) a local hypothesis
`A : MSAlgG α` is *not* of class type, so it cannot be captured by instance search for
`MeasurableSpace α`; (ii) statements can pass it around without the ambient instance being
silently changed. -/
structure MSAlgG (α : Type*) where
  m : MeasurableSpace α

@[simp] theorem MSAlgG.mk_m (α : Type*) (m : MeasurableSpace α) : (MSAlgG.mk m).m = m := rfl

/-- The atom of the wrapped σ-algebra `A` at `x`: the intersection of all `A`-measurable sets
containing `x` (Pisa's `[x]_A`). -/
def atomOf {α : Type*} (A : MSAlgG α) (x : α) : Set α :=
  ⋂₀ {s | MeasurableSet[A.m] s ∧ x ∈ s}

theorem atomOf_eq_atomG {α : Type*} [mα : MeasurableSpace α] (A : MSAlgG α) (x : α) :
    atomOf A x = atomG A.m x := rfl

/-- **The conditional measure of `μ` given the σ-algebra `A.m`, at the point `x`** (Pisa §5):
`kappa μ A x = ProbabilityTheory.condExpKernel μ A.m x`.  For a finite Borel measure on a
standard Borel space this is a probability measure carried by the atom `atomOf A x`, and it
satisfies Pisa 5.9(i): `∫ f d(kappa μ A x) = μ[f | A.m] x` for `μ`-a.e. `x`. -/
noncomputable def kappa {α : Type*} [mα : MeasurableSpace α] [StandardBorelSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (A : MSAlgG α) (x : α) : Measure α :=
  ProbabilityTheory.condExpKernel (mΩ := mα) μ A.m x

@[simp] theorem kappa_def {α : Type*} [mα : MeasurableSpace α] [StandardBorelSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (A : MSAlgG α) (x : α) :
    kappa μ A x = ProbabilityTheory.condExpKernel (mΩ := mα) μ A.m x := rfl

end Work.EKLRelCross
