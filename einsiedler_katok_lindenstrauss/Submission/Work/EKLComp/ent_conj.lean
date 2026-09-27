import Mathlib
import Submission.Work.EKLComp.Entropy

/-!
# Entropy is invariant under a bimeasurable conjugacy (`C3` item (E2))

If `φ : X → X` is a measurable bijection (with measurable inverse `ψ`) that commutes with
`T`, then pushing a probability measure `μ` forward along `φ` does not change the
Kolmogorov–Sinai entropy with respect to `T`:

`ent (μ.map φ) T = ent μ T`.

The proof is the textbook one: `X ↦ φ⁻¹X` is a bijection of measurable partitions, and
`φ⁻¹ (⋁_{k<N} T^{-k} P) = ⋁_{k<N} T^{-k} (φ⁻¹ P)` because `φ` commutes with `T`.  Hence
`hPart (μ.map φ) T P = hPart μ T (φ⁻¹P)`, and both sides of the defining `iSup` agree.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.EKLComp

open Work.EKLContract

variable {X : Type} [mX : MeasurableSpace X]

/-! ## The pull-back partition `φ⁻¹ P` -/

/-- The measurable partition obtained by pulling `P` back along a measurable map `φ`. -/
def prePart (φ : X → X) (hφ : Measurable φ) (P : FinPart X) : FinPart X where
  n := P.n
  parts := fun i => φ ⁻¹' P.parts i
  measurable := fun i => (P.measurable i).preimage hφ
  disjoint := by
    intro i j hij
    exact Set.disjoint_left.mpr fun x hx hy => Set.disjoint_left.mp (P.disjoint hij) hx hy
  cover := by
    rw [← Set.preimage_iUnion, P.cover, Set.preimage_univ]

@[simp] theorem prePart_n (φ : X → X) (hφ : Measurable φ) (P : FinPart X) :
    (prePart φ hφ P).n = P.n := rfl

@[simp] theorem prePart_parts (φ : X → X) (hφ : Measurable φ) (P : FinPart X)
    (i : Fin P.n) : (prePart φ hφ P).parts i = φ ⁻¹' P.parts i := rfl

/-! ## Commutation with iterates -/

theorem iterate_comm_φ (φ T : X → X) (hcomm : ∀ x, φ (T x) = T (φ x)) :
    ∀ k : ℕ, ∀ x, T^[k] (φ x) = φ (T^[k] x) := by
  intro k
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
    intro x
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← hcomm x, ih (T x)]

/-! ## Preimages of `joinSets` atoms -/

theorem preimage_joinSets (φ T : X → X) (hφ : Measurable φ)
    (hcomm : ∀ x, φ (T x) = T (φ x)) (P : FinPart X) (N : ℕ) (w : Fin N → Fin P.n) :
    φ ⁻¹' joinSets T P N w = joinSets T (prePart φ hφ P) N w := by
  ext x
  simp only [joinSets, Set.mem_preimage, Set.mem_iInter, prePart_parts]
  constructor
  · intro h k
    rw [← iterate_comm_φ φ T hcomm k x]
    exact h k
  · intro h k
    rw [iterate_comm_φ φ T hcomm k x]
    exact h k

/-! ## Entropy of the atoms of `hPart (μ.map φ) T P` -/

theorem Hfam_map_joinSets {φ T : X → X} (hφ : Measurable φ) (hT : Measurable T)
    (hcomm : ∀ x, φ (T x) = T (φ x)) (μ : Measure X) (P : FinPart X) (M : ℕ) :
    Hfam (μ.map φ) (joinSets T P M) = Hfam μ (joinSets T (prePart φ hφ P) M) := by
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Measure.map_apply hφ (Core.joinSets_measurable hT P M w),
    preimage_joinSets φ T hφ hcomm P M w]

theorem hPart_map {φ T : X → X} (hφ : Measurable φ) (hT : Measurable T)
    (hcomm : ∀ x, φ (T x) = T (φ x)) (μ : Measure X) (P : FinPart X) :
    hPart (μ.map φ) T P = hPart μ T (prePart φ hφ P) := by
  have hfun : (fun N : ℕ => Hfam (μ.map φ) (joinSets T P (N+1)) / ((N:ℝ)+1))
      = (fun N : ℕ => Hfam μ (joinSets T (prePart φ hφ P) (N+1)) / ((N:ℝ)+1)) := by
    funext N
    rw [Hfam_map_joinSets hφ hT hcomm μ P (N+1)]
  simp only [hPart]
  rw [hfun]

/-! ## The pull-back map on partitions is a left inverse of the push-forward map -/

theorem joinSets_prePart_comp {φ ψ : X → X} (T : X → X) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hl : Function.LeftInverse ψ φ) (Q : FinPart X) (M : ℕ) :
    joinSets T (prePart φ hφ (prePart ψ hψ Q)) M = joinSets T Q M := by
  have hl' : ∀ x, ψ (φ x) = x := hl
  funext w
  ext x
  simp only [joinSets, Set.mem_iInter, Set.mem_preimage, prePart, hl']

theorem hPart_prePart_comp {φ ψ : X → X} (T : X → X) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hl : Function.LeftInverse ψ φ) (μ : Measure X) (Q : FinPart X) :
    hPart μ T (prePart φ hφ (prePart ψ hψ Q)) = hPart μ T Q := by
  have hfun : (fun N : ℕ => Hfam μ (joinSets T (prePart φ hφ (prePart ψ hψ Q)) (N+1))
        / ((N:ℝ)+1))
      = (fun N : ℕ => Hfam μ (joinSets T Q (N+1)) / ((N:ℝ)+1)) := by
    funext N
    exact congrArg (fun s => Hfam μ s / ((N:ℝ)+1))
      (joinSets_prePart_comp T hφ hψ hl Q (N+1))
  simp only [hPart]
  rw [hfun]

/-! ## The main statement -/

theorem ent_conj {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T φ ψ : X → X) (hT : Measurable T) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hmp : MeasureTheory.MeasurePreserving T μ μ) (hl : Function.LeftInverse ψ φ)
    (hr : Function.RightInverse ψ φ) (hcomm : ∀ x, φ (T x) = T (φ x)) :
    Work.EKLContract.ent (μ.map φ) T = Work.EKLContract.ent μ T := by
  have key : ∀ P : FinPart X, hPart (μ.map φ) T P = hPart μ T (prePart φ hφ P) :=
    fun P => hPart_map hφ hT hcomm μ P
  show (⨆ P : FinPart X, ENNReal.ofReal (hPart (μ.map φ) T P))
      = ⨆ P : FinPart X, ENNReal.ofReal (hPart μ T P)
  refine le_antisymm ?_ ?_
  · refine iSup_le fun P => ?_
    rw [key P]
    exact le_iSup (fun Q : FinPart X => ENNReal.ofReal (hPart μ T Q)) (prePart φ hφ P)
  · refine iSup_le fun Q => ?_
    have h1 : hPart (μ.map φ) T (prePart ψ hψ Q) = hPart μ T Q :=
      (hPart_map hφ hT hcomm μ (prePart ψ hψ Q)).trans
        (hPart_prePart_comp T hφ hψ hl μ Q)
    rw [← h1]
    exact le_iSup (fun P : FinPart X => ENNReal.ofReal (hPart (μ.map φ) T P))
      (prePart ψ hψ Q)

end Work.EKLComp
