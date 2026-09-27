import Mathlib
import Submission.Work.EKLComp.prop92defs
import Submission.Work.EKLComp.tendsto_hPart
import Submission.Work.EKLComp.prop92win.hPart_le_of_joinSets_le

/-!
# `hPart` is unchanged by passing to the two-sided window partition
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

noncomputable section

namespace Work.EKLComp.prop92win

open Work.EKLContract Work.EKLComp

set_option maxHeartbeats 2000000

/-! ## 1. Algebra of the shift -/

theorem shiftZ_apply_add (t : Fin 3 → ℝ) (k l : ℤ) (x : X3) :
    shiftZ t (k + l) x = shiftZ t k (shiftZ t l x) :=
  congrFun (shiftZ_add t k l) x

theorem preimage_shiftZ_shiftZ (t : Fin 3 → ℝ) (a b : ℤ) (S : Set X3) :
    (shiftZ t a) ⁻¹' ((shiftZ t b) ⁻¹' S) = (shiftZ t (b + a)) ⁻¹' S := by
  ext x
  simp only [Set.mem_preimage, shiftZ_apply_add]

/-- The `k`-fold iterate of `shiftZ t 1` is `shiftZ t k`. -/
theorem iterate_shiftZ (t : Fin 3 → ℝ) (k : ℕ) :
    (shiftZ t 1)^[k] = shiftZ t (k : ℤ) := by
  induction k with
  | zero =>
    rw [Function.iterate_zero]
    show id = shiftZ t (((0 : ℕ)) : ℤ)
    rw [show (((0 : ℕ)) : ℤ) = (0 : ℤ) by norm_num, shiftZ_zero]
  | succ k ih =>
    rw [Function.iterate_succ', ih, ← shiftZ_add]
    congr 1
    push_cast
    ring

/-! ## 2. Basic measure-theoretic API -/

theorem preimage_isMPart_shiftZ (t : Fin 3 → ℝ) {ι : Type*} [Fintype ι] {A : ι → Set X3}
    (hA : Core.IsMPart A) (k : ℤ) : Core.IsMPart (fun i => (shiftZ t k) ⁻¹' A i) := by
  refine ⟨fun i => (hA.measurable i).preimage (measurable_shiftZ t k), ?_, ?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hx hy
    simp only [Set.mem_preimage] at hx hy
    exact Set.disjoint_left.mp (hA.disjoint hij) hx hy
  · rw [← Set.preimage_iUnion, hA.cover, Set.preimage_univ]

theorem Hfam_preimage_shiftZ {ν : Measure X3} [IsProbabilityMeasure ν] (t : Fin 3 → ℝ)
    (hm : MeasurePreserving (shiftZ t 1) ν ν) {ι : Type*} [Fintype ι] (k : ℕ)
    (A : ι → Set X3) (hA : ∀ i, MeasurableSet (A i)) :
    Hfam ν (fun i => (shiftZ t (k : ℤ)) ⁻¹' A i) = Hfam ν A := by
  have hmp : MeasurePreserving (shiftZ t (k : ℤ)) ν ν := by
    have h := hm.iterate k
    rwa [iterate_shiftZ] at h
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hmp.measure_preimage (hA i).nullMeasurableSet]

/-! ## 3. `winPart` refines `P` -/

theorem refines_winPart (t : Fin 3 → ℝ) (P : FinPart X3) (m : ℕ) :
    Refines (winPart t P m) P := by
  intro i
  refine ⟨winIdx P m i ⟨m, by omega⟩, ?_⟩
  intro x hx
  have h := Set.mem_iInter.mp hx ⟨m, by omega⟩
  simp only [Set.mem_preimage] at h
  have h0 : ((⟨m, by omega⟩ : Fin (2 * m + 1)) : ℤ) - (m : ℤ) = 0 := by simp
  rw [h0, shiftZ_zero] at h
  exact h

/-! ## 4. The key `Hfam` identity -/

/-- The `(N + 2m)`-fold join of `P` is contained in the `aZ t m`-preimage of the `N`-fold
join of the window partition `winPart t P m`, for the diagonal filling of the window. -/
theorem winPart_joinSets_subset (t : Fin 3 → ℝ) (P : FinPart X3) (m N : ℕ)
    (v : Fin (N + 2 * m) → Fin P.n) :
    joinSets (shiftZ t 1) P (N + 2 * m) v ⊆
      (shiftZ t (m : ℤ)) ⁻¹' joinSets (shiftZ t 1) (winPart t P m) N
        (fun k => finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)
          (fun j => v ⟨(k : ℕ) + (j : ℕ), by omega⟩)) := by
  intro x hx
  unfold joinSets at hx
  simp only [Set.mem_iInter, Set.mem_preimage, iterate_shiftZ] at hx
  rw [Set.mem_preimage]
  unfold joinSets
  simp only [Set.mem_iInter, Set.mem_preimage]
  intro k
  rw [iterate_shiftZ, ← shiftZ_apply_add]
  rw [show (winPart t P m).parts (finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)
        (fun j => v ⟨(k : ℕ) + (j : ℕ), by omega⟩)) = ⋂ j : Fin (2 * m + 1),
        (shiftZ t ((j : ℤ) - (m : ℤ))) ⁻¹' P.parts (winIdx P m
          (finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)
            (fun j => v ⟨(k : ℕ) + (j : ℕ), by omega⟩)) j)
      from winPart_parts' t P m _]
  rw [Set.mem_iInter]
  intro j
  rw [Set.mem_preimage, ← shiftZ_apply_add]
  have hkm : winIdx P m (finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)
        (fun j => v ⟨(k : ℕ) + (j : ℕ), by omega⟩)) j
      = v ⟨(k : ℕ) + (j : ℕ), by omega⟩ := by
    simp [winIdx, Equiv.symm_apply_apply]
  rw [hkm]
  have hexp : ((j : ℤ) - (m : ℤ)) + ((k : ℤ) + (m : ℤ))
      = ((⟨(k : ℕ) + (j : ℕ), by omega⟩ : Fin (N + 2 * m)) : ℤ) := by
    push_cast
    ring
  rw [hexp]
  exact hx _

theorem Hfam_joinSets_winPart_le {ν : Measure X3} [IsProbabilityMeasure ν] (t : Fin 3 → ℝ)
    (hm : MeasurePreserving (shiftZ t 1) ν ν) (P : FinPart X3) (m N : ℕ) :
    Hfam ν (joinSets (shiftZ t 1) (winPart t P m) N)
      ≤ Hfam ν (joinSets (shiftZ t 1) P (N + 2 * m)) := by
  have hT : Measurable (shiftZ t 1) := measurable_shiftZ t 1
  have hA : Core.IsMPart (fun w : Fin N → Fin (winPart t P m).n =>
      (shiftZ t (m : ℤ)) ⁻¹' joinSets (shiftZ t 1) (winPart t P m) N w) :=
    preimage_isMPart_shiftZ t (Core.joinSets_isMPart hT (winPart t P m) N) (m : ℤ)
  have hB : Core.IsMPart (joinSets (shiftZ t 1) P (N + 2 * m)) :=
    Core.joinSets_isMPart hT P (N + 2 * m)
  have key : Hfam ν (fun w : Fin N → Fin (winPart t P m).n =>
      (shiftZ t (m : ℤ)) ⁻¹' joinSets (shiftZ t 1) (winPart t P m) N w)
      ≤ Hfam ν (joinSets (shiftZ t 1) P (N + 2 * m)) :=
    Core.Hfam_mono ν hA hB
      (fun v : Fin (N + 2 * m) → Fin P.n =>
        fun k => finFunctionFinEquiv (m := P.n) (n := 2 * m + 1)
          (fun j => v ⟨(k : ℕ) + (j : ℕ), by omega⟩))
      (fun v => winPart_joinSets_subset t P m N v)
  rw [Hfam_preimage_shiftZ t hm m (joinSets (shiftZ t 1) (winPart t P m) N)
    (fun w => Core.joinSets_measurable hT (winPart t P m) N w)] at key
  exact key

/-! ## 5. The main statement -/

theorem hPart_winPart {ν : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure ν] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (Work.EKLComp.shiftZ t 1) ν ν)
    (P : Work.EKLContract.FinPart Work.EKLContract.X3) (m : ℕ) :
    Work.EKLContract.hPart ν (Work.EKLComp.shiftZ t 1) (Work.EKLComp.winPart t P m)
      = Work.EKLContract.hPart ν (Work.EKLComp.shiftZ t 1) P := by
  have hT : Measurable (shiftZ t 1) := measurable_shiftZ t 1
  have hle1 : hPart ν (shiftZ t 1) P ≤ hPart ν (shiftZ t 1) (winPart t P m) :=
    hPart_le_of_refines ν hT (refines_winPart t P m)
  have hle2 : hPart ν (shiftZ t 1) (winPart t P m) ≤ hPart ν (shiftZ t 1) P :=
    hPart_le_of_joinSets_le ν hmp P (winPart t P m) (2 * m)
      (fun N => Hfam_joinSets_winPart_le t hmp P m N)
  exact le_antisymm hle2 hle1

end Work.EKLComp.prop92win
