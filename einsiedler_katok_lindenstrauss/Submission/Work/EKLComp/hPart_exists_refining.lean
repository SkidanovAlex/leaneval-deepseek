import Mathlib
import Submission.Work.EKLComp.Core
import Submission.Work.EKLComp.Entropy

/-!
# `hPart_exists_refining`

The entropy `hPart μ T P` of a finite partition is monotone under refinement of the
partition: if `R` refines `P` (every atom of `R` is contained in an atom of `P`) then
`hPart μ T P ≤ hPart μ T R`.  Applying this to the common refinement (join)
`P ∨ Q` of two partitions gives the requested statement: there is always a single
partition `R = P ∨ Q` whose `hPart` dominates both `hPart μ T P` and `hPart μ T Q`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

namespace Work.EKLComp

open Work.EKLContract

variable {X : Type} [MeasurableSpace X]

/-! ## 1. The common refinement (join) of two finite partitions -/

/-- The common refinement `P ∨ Q` of two finite partitions, indexed via
`finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)`; its atoms are `P_i ∩ Q_j`. -/
def commonRefinement (P Q : FinPart X) : FinPart X where
  n := P.n * Q.n
  parts := fun k => P.parts (finProdFinEquiv.symm k).1 ∩ Q.parts (finProdFinEquiv.symm k).2
  measurable := fun k => (P.measurable _).inter (Q.measurable _)
  disjoint := by
    rw [Pairwise]
    intro k l hkl
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rw [Set.mem_inter_iff] at hx1 hx2
    by_cases h1 : (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm l).1
    · have h2 : (finProdFinEquiv.symm k).2 ≠ (finProdFinEquiv.symm l).2 := by
        intro h2
        refine hkl ?_
        have hp : finProdFinEquiv.symm k = finProdFinEquiv.symm l := Prod.ext h1 h2
        rw [← Equiv.apply_symm_apply finProdFinEquiv k,
          ← Equiv.apply_symm_apply finProdFinEquiv l, hp]
      exact (Q.disjoint h2).le_bot ⟨hx1.2, hx2.2⟩
    · exact (P.disjoint h1).le_bot ⟨hx1.1, hx2.1⟩
  cover := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hxP : x ∈ ⋃ i, P.parts i := by rw [P.cover]; exact trivial
    have hxQ : x ∈ ⋃ j, Q.parts j := by rw [Q.cover]; exact trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxP
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxQ
    refine Set.mem_iUnion.mpr ⟨finProdFinEquiv (i, j), ?_⟩
    have hk : finProdFinEquiv.symm (finProdFinEquiv (i, j)) = (i, j) :=
      Equiv.symm_apply_apply _ _
    rw [hk]
    exact ⟨hi, hj⟩

@[simp] theorem commonRefinement_n (P Q : FinPart X) : (commonRefinement P Q).n = P.n * Q.n := rfl

theorem commonRefinement_parts (P Q : FinPart X) (k : Fin (P.n * Q.n)) :
    (commonRefinement P Q).parts k
      = P.parts (finProdFinEquiv.symm k).1 ∩ Q.parts (finProdFinEquiv.symm k).2 := rfl

theorem refines_commonRefinement_left (P Q : FinPart X) : Refines (commonRefinement P Q) P :=
  fun k => ⟨(finProdFinEquiv.symm k).1, Set.inter_subset_left⟩

theorem refines_commonRefinement_right (P Q : FinPart X) : Refines (commonRefinement P Q) Q :=
  fun k => ⟨(finProdFinEquiv.symm k).2, Set.inter_subset_right⟩

/-! ## 2. Monotonicity of `hPart` under refinement -/

/-- If `R` refines `P`, then at every level the entropy of the corresponding join is at
most that of the join along `R`. -/
theorem Hfam_joinSets_le_of_refines (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hT : Measurable T) {P R : FinPart X} (h : Refines R P) (N : ℕ) :
    Hfam μ (joinSets T P N) ≤ Hfam μ (joinSets T R N) := by
  classical
  choose g hg using h
  refine Core.Hfam_mono μ (Core.joinSets_isMPart hT P N) (Core.joinSets_isMPart hT R N)
    (fun w : Fin N → Fin R.n => fun k => g (w k)) ?_
  intro w x hx
  simp only [joinSets, Set.mem_iInter, Set.mem_preimage] at hx ⊢
  intro k
  exact hg (w k) (hx k)

/-- `hPart` is monotone under refinement of the partition. -/
theorem hPart_le_of_refines (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hT : Measurable T) {P R : FinPart X} (h : Refines R P) :
    hPart μ T P ≤ hPart μ T R := by
  rw [hPart, hPart]
  refine le_ciInf fun N => ?_
  calc hPart μ T P ≤ Hfam μ (joinSets T P (N + 1)) / ((N : ℝ) + 1) :=
        Core.hPart_le_avg μ T P N
    _ ≤ Hfam μ (joinSets T R (N + 1)) / ((N : ℝ) + 1) :=
        div_le_div_of_nonneg_right (Hfam_joinSets_le_of_refines μ hT h (N + 1)) (by positivity)

/-! ## 3. The requested statement -/

theorem hPart_exists_refining {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (T : X → X) (hT : Measurable T)
    (P Q : Work.EKLContract.FinPart X) :
    ∃ R : Work.EKLContract.FinPart X,
      Work.EKLContract.hPart μ T P ≤ Work.EKLContract.hPart μ T R ∧
      Work.EKLContract.hPart μ T Q ≤ Work.EKLContract.hPart μ T R :=
  ⟨commonRefinement P Q,
   hPart_le_of_refines μ hT (refines_commonRefinement_left P Q),
   hPart_le_of_refines μ hT (refines_commonRefinement_right P Q)⟩

end Work.EKLComp
