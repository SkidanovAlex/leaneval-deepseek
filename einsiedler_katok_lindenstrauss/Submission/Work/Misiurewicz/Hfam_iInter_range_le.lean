import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLComp.Core

/-!
# Subadditivity of `Hfam` over a range-indexed join of measurable partitions

`Work.EKLContract.Hfam μ P = ∑ i, Real.negMulLog (μ (P i)).toReal` is the Shannon entropy of a
finite family `P` of measurable sets.  For an `m`-tuple of finite measurable partitions
`A 0, …, A (m-1)` of a probability space `(X, μ)` the join

`V ↦ ⋂ i : Fin m, A i (V i)`

is again a finite measurable partition of `X` (its atoms are the intersections of one atom of
each `A i`), and Shannon entropy is subadditive over joins:

`Hfam μ (⋂ i, A i (· i)) ≤ ∑ i < m, Hfam μ (A i)`.

This is the standard `H(P ∨ Q) ≤ H(P) + H(Q)` iterated.  The two ingredients are isolated here:

* `isMPart_iInter` — the join of a finite family of finite measurable partitions is a finite
  measurable partition;
* `Hfam_inter_le` (`Work.EKLComp.Core`) — the two-partition case, applied at the splitting point,
  after splitting off the index `0` of `Fin (m+1)` via `consEquiv`.
-/

namespace Work.Misiurewicz

open MeasureTheory

/-- The join `⋂ i, A i (V i)` of a finite family of finite measurable partitions is again a
finite measurable partition: its atoms are measurable, pairwise disjoint, and cover `X`. -/
theorem isMPart_iInter {X : Type*} [MeasurableSpace X] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : Type*} [Fintype κ] {A : ι → κ → Set X} (hA : ∀ i, Work.EKLComp.Core.IsMPart (A i)) :
    Work.EKLComp.Core.IsMPart (fun V : ι → κ => ⋂ i, A i (V i)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro V
    exact MeasurableSet.iInter fun i => (hA i).measurable (V i)
  · intro V W hVW
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hVW
    exact Disjoint.mono (Set.iInter_subset _ i) (Set.iInter_subset _ i) ((hA i).disjoint hi)
  · apply Set.eq_univ_of_forall
    intro x
    choose c hc using fun i => Set.mem_iUnion.mp (by rw [(hA i).cover]; exact Set.mem_univ x)
    exact Set.mem_iUnion.mpr ⟨c, Set.mem_iInter.mpr hc⟩

/-- Reindexing `(Fin m → κ)`-families by splitting off the index `0`:
`(c, V) ↦ Fin.cons c V`. -/
def consEquiv (κ : Type*) (m : ℕ) : κ × (Fin m → κ) ≃ (Fin (m+1) → κ) where
  toFun p := Fin.cons p.1 p.2
  invFun V := (V 0, fun j => V j.succ)
  left_inv p := by simp
  right_inv V := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp

@[simp] theorem consEquiv_apply (κ : Type*) (m : ℕ) (p : κ × (Fin m → κ)) :
    consEquiv κ m p = Fin.cons p.1 p.2 := rfl

set_option maxHeartbeats 2000000 in
theorem Hfam_iInter_range_le {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] {κ : Type*} [Fintype κ] (m : ℕ)
    (A : ℕ → κ → Set X) (hA : ∀ i < m, Work.EKLComp.Core.IsMPart (A i)) :
    Work.EKLContract.Hfam μ (fun V : Fin m → κ => ⋂ i : Fin m, A (i : ℕ) (V i)) ≤
      ∑ i ∈ Finset.range m, Work.EKLContract.Hfam μ (A i) := by
  revert A
  induction m with
  | zero =>
    intro A hA
    have hzero : Work.EKLContract.Hfam μ (fun V : Fin 0 → κ => ⋂ i : Fin 0, A (i:ℕ) (V i)) = 0 := by
      simp only [Work.EKLContract.Hfam]
      refine Finset.sum_eq_zero fun V _ => ?_
      rw [Set.iInter_of_empty, measure_univ, ENNReal.toReal_one, Real.negMulLog_one]
    rw [hzero]
    simp
  | succ m ih =>
    intro A hA
    have hpt : ∀ p : κ × (Fin m → κ),
        (⋂ i : Fin (m+1), A (i:ℕ) ((consEquiv κ m) p i)) =
          A 0 p.1 ∩ ⋂ j : Fin m, A ((j:ℕ)+1) (p.2 j) := by
      intro p
      ext x
      simp only [consEquiv_apply, Set.mem_iInter, Set.mem_inter_iff, Fin.forall_fin_succ,
        Fin.cons_zero, Fin.cons_succ, Fin.val_succ, Fin.val_zero]
    have hsplit : Work.EKLContract.Hfam μ (fun V : Fin (m+1) → κ => ⋂ i : Fin (m+1), A (i:ℕ) (V i))
        = Work.EKLContract.Hfam μ (fun p : κ × (Fin m → κ) =>
            A 0 p.1 ∩ ⋂ j : Fin m, A ((j:ℕ)+1) (p.2 j)) := by
      rw [← Work.EKLComp.Core.Hfam_equiv μ (consEquiv κ m)
        (fun V : Fin (m+1) → κ => ⋂ i : Fin (m+1), A (i:ℕ) (V i))]
      simp only [Work.EKLContract.Hfam]
      exact Finset.sum_congr rfl fun p _ => by rw [hpt p]
    rw [hsplit]
    calc Work.EKLContract.Hfam μ (fun p : κ × (Fin m → κ) =>
            A 0 p.1 ∩ ⋂ j : Fin m, A ((j:ℕ)+1) (p.2 j))
        ≤ Work.EKLContract.Hfam μ (A 0) +
            Work.EKLContract.Hfam μ (fun W : Fin m → κ => ⋂ j : Fin m, A ((j:ℕ)+1) (W j)) :=
          Work.EKLComp.Core.Hfam_inter_le μ (hA 0 (Nat.succ_pos m))
            (isMPart_iInter (A := fun (j : Fin m) (c : κ) => A ((j:ℕ)+1) c)
              (fun j => hA ((j:ℕ)+1) (by omega)))
      _ ≤ Work.EKLContract.Hfam μ (A 0) +
            ∑ j ∈ Finset.range m, Work.EKLContract.Hfam μ (A (j+1)) :=
          add_le_add (le_refl _) (ih (fun j => A (j+1)) (fun j hj => hA (j+1) (by omega)))
      _ = ∑ i ∈ Finset.range (m+1), Work.EKLContract.Hfam μ (A i) := by
          rw [Finset.sum_range_succ']; ring

end Work.Misiurewicz
