import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.EntSig
import Submission.Work.EKLContract.Interfaces

/-!
# `Work.EKLC6Core.CountableGen` — the countable-generator interface of Pisa 7.43

Pisa 7.43 produces a *countable* partition `P` of finite entropy which is a generator for
`aDiag t ·` modulo `μ`; Pisa 7.53 explains that the finite form (a `FinPart`) may fail, because
finitely many scales cannot force the atom of the past σ-algebra to be a plaque.

This file fixes the countable interface.  For a countable family `S : ℕ → Set X₃`:

* `biOrbit t S` is the bi-infinite orbit σ-algebra of `S`,
  `⨆ n, (comap ((aDiag t ·)^[n]) σ(S) ⊔ comap ((aDiag (-t) ·)^[n]) σ(S))`;
* `GeneratesModMu μ t S` says that every Borel set agrees with a `biOrbit t S`-measurable set up
  to `μ`-null sets (the "generator mod μ" property of 7.43);
* `pastSig t S = ⨆ n, comap ((aDiag t ·)^[n]) σ(S)` is the past σ-algebra `A` of 7.43, which is
  automatically `aDiag t ·`-decreasing and satisfies `A = σ(S) ∨ comap (aDiag t ·) A`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The bi-infinite orbit σ-algebra of a countable family `S`. -/
def biOrbit (t : Fin 3 → ℝ) (S : ℕ → Set X3) : MeasurableSpace X3 :=
  ⨆ n : ℕ, (MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
      (MeasurableSpace.generateFrom (Set.range S)) ⊔
    MeasurableSpace.comap ((fun x : X3 => aDiag (-t) • x)^[n])
      (MeasurableSpace.generateFrom (Set.range S)))

/-- The past σ-algebra of a countable family `S` (Pisa 7.43's `A`). -/
def pastSigSet (t : Fin 3 → ℝ) (S : ℕ → Set X3) : MeasurableSpace X3 :=
  ⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
    (MeasurableSpace.generateFrom (Set.range S))

/-- **The generator property modulo `μ`** for a countable family: every Borel set agrees, up to
`μ`-null sets, with a set measurable for the bi-infinite orbit σ-algebra of `S` (Pisa 7.43). -/
def GeneratesModMuSet (μ : MeasureTheory.Measure X3) (t : Fin 3 → ℝ) (S : ℕ → Set X3) : Prop :=
  ∀ E : Set X3, MeasurableSet E → ∃ E' : Set X3, MeasurableSet[biOrbit t S] E' ∧
    μ (E \ E') = 0 ∧ μ (E' \ E) = 0

/-- The past σ-algebra of a countable family is `aDiag t ·`-decreasing. -/
theorem comap_pastSigSet_le (t : Fin 3 → ℝ) (S : ℕ → Set X3) :
    MeasurableSpace.comap (fun x : X3 => aDiag t • x) (pastSigSet t S) ≤ pastSigSet t S := by
  rw [pastSigSet, MeasurableSpace.comap_iSup]
  refine iSup_le fun n => ?_
  have hcomp : ((fun x : X3 => aDiag t • x)^[n]) ∘ (fun x : X3 => aDiag t • x)
      = ((fun x : X3 => aDiag t • x)^[n + 1]) :=
    (Function.iterate_succ (fun x : X3 => aDiag t • x) n).symm
  rw [MeasurableSpace.comap_comp, hcomp]
  exact le_iSup (fun m : ℕ => MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[m])
    (MeasurableSpace.generateFrom (Set.range S))) (n + 1)

/-- `comap (aDiag t ·)` of the past σ-algebra of `S` is its shift. -/
theorem comap_pastSigSet_eq (t : Fin 3 → ℝ) (S : ℕ → Set X3) :
    MeasurableSpace.comap (fun x : X3 => aDiag t • x) (pastSigSet t S)
      = (⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n + 1])
          (MeasurableSpace.generateFrom (Set.range S))) := by
  rw [pastSigSet, MeasurableSpace.comap_iSup]
  refine iSup_congr fun n => ?_
  have hcomp : ((fun x : X3 => aDiag t • x)^[n + 1])
      = ((fun x : X3 => aDiag t • x)^[n]) ∘ (fun x : X3 => aDiag t • x) :=
    Function.iterate_succ (fun x : X3 => aDiag t • x) n
  rw [MeasurableSpace.comap_comp, hcomp]

/-- `A = σ(S) ∨ comap (aDiag t ·) A` by construction. -/
theorem pastSigSet_eq_sup (t : Fin 3 → ℝ) (S : ℕ → Set X3) :
    pastSigSet t S
      = MeasurableSpace.generateFrom (Set.range S) ⊔
        MeasurableSpace.comap (fun x : X3 => aDiag t • x) (pastSigSet t S) := by
  have hcomap : MeasurableSpace.comap (fun x : X3 => aDiag t • x)
        (⨆ m : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[m])
          (MeasurableSpace.generateFrom (Set.range S)))
      = (⨆ m : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[m + 1])
          (MeasurableSpace.generateFrom (Set.range S))) := by
    rw [MeasurableSpace.comap_iSup]
    refine iSup_congr fun n => ?_
    have hcomp : ((fun x : X3 => aDiag t • x)^[n + 1])
        = ((fun x : X3 => aDiag t • x)^[n]) ∘ (fun x : X3 => aDiag t • x) :=
      Function.iterate_succ (fun x : X3 => aDiag t • x) n
    rw [MeasurableSpace.comap_comp, hcomp]
  rw [pastSigSet]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun n => ?_
    cases n with
    | zero =>
        rw [Function.iterate_zero, MeasurableSpace.comap_id]
        exact le_sup_left
    | succ k =>
        rw [hcomap]
        exact le_trans (le_iSup (fun m : ℕ => MeasurableSpace.comap
          ((fun x : X3 => aDiag t • x)^[m + 1])
          (MeasurableSpace.generateFrom (Set.range S))) k) le_sup_right
  · refine sup_le ?_ ?_
    · refine le_trans ?_ (le_iSup (fun n : ℕ => MeasurableSpace.comap
        ((fun x : X3 => aDiag t • x)^[n])
        (MeasurableSpace.generateFrom (Set.range S))) 0)
      rw [Function.iterate_zero, MeasurableSpace.comap_id]
    · rw [hcomap]
      refine iSup_le fun n => ?_
      exact le_iSup (fun m : ℕ => MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[m])
        (MeasurableSpace.generateFrom (Set.range S))) (n + 1)

end Work.EKLC6Core

end
