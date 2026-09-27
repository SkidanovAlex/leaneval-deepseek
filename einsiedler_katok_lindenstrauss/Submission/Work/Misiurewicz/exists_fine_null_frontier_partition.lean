import Mathlib
import Submission.Work.Misiurewicz.exists_null_frontier_Vball_radius
import Submission.Work.Misiurewicz.Vball_mem_nhds
import Submission.Work.Misiurewicz.exists_V_mul_inv_subset
import Submission.Work.Misiurewicz.exists_fine_null_frontier_nhd
import Submission.Work.Misiurewicz.exists_finPart_null_frontier_of_finite_cover
import Submission.Work.EKLNonExc.VFacts
import Submission.Work.EKLComp.Misiurewicz.Defs

namespace Work.Misiurewicz

open MeasureTheory Filter Topology
open Work.EKLContract Work.EKLComp

noncomputable section

theorem exists_fine_null_frontier_partition (K : Set Work.EKLContract.X3) (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) (ν : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsFiniteMeasure ν] (hνK : ν K = 1) :
    ∃ P : Work.EKLContract.FinPart Work.EKLContract.X3,
      (∀ i, (P.parts i ∩ K).Nonempty → Work.EKLComp.Fine ε (P.parts i)) ∧
      (∀ i, ν (frontier (P.parts i)) = 0) := by
  classical
  -- Every point of `X₃` has an `ε`-fine open neighbourhood with `ν`-null frontier.
  have hnhd : ∀ x : X3, ∃ U : Set X3, IsOpen U ∧ x ∈ U ∧ Fine ε U ∧ ν (frontier U) = 0 :=
    fun x => exists_fine_null_frontier_nhd ε hε ν x
  choose U hU using hnhd
  have hUo : ∀ x, IsOpen (U x) := fun x => (hU x).1
  -- Compactness turns the open cover into a finite subcover of `K`.
  have hcover : K ⊆ ⋃ x, U x := fun y hy => Set.mem_iUnion.mpr ⟨y, (hU y).2.1⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUo hcover
  -- Re-index the finite family `t` by `Fin t.card`.
  let V : Fin t.card → Set X3 := fun i => U ((t.equivFin.symm i).val)
  have hVo : ∀ i, IsOpen (V i) := fun i => hUo _
  have hVfr : ∀ i, ν (frontier (V i)) = 0 := fun i => (hU _).2.2.2
  have hVfine : ∀ i, Fine ε (V i) := fun i => (hU _).2.2.1
  have hKcover : K ⊆ ⋃ i, V i := by
    intro y hy
    rcases Set.mem_iUnion.mp (ht hy) with ⟨x, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hxt, hyU⟩
    refine Set.mem_iUnion.mpr ⟨t.equivFin ⟨x, hxt⟩, ?_⟩
    show y ∈ U ((t.equivFin.symm (t.equivFin ⟨x, hxt⟩)).val)
    rw [Equiv.symm_apply_apply]
    exact hyU
  -- The combinatorial partition adapted to the finite cover.
  obtain ⟨P, hPfr, hPfine⟩ :=
    exists_finPart_null_frontier_of_finite_cover ν V hVo hVfr
  refine ⟨P, ?_, hPfr⟩
  intro i hi
  rcases hi with ⟨y, hyP, hyK⟩
  obtain ⟨j, hj⟩ := hPfine i ⟨y, hyP, hKcover hyK⟩
  exact fun a ha b hb => hVfine j a (hj ha) b (hj hb)

end

end Work.Misiurewicz
