import Mathlib.Algebra.Module.ZLattice.Covolume

namespace Commons.Lattice.Counting

open Filter MeasureTheory Metric Set
open scoped Topology Pointwise

noncomputable section

/-- The number of lattice points in the closed ball of radius `N` equals the number of points
of the scaled lattice `(N : ℝ)⁻¹ • L` inside the unit closed ball. -/
private lemma lattice_ball_card_eq_smulSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Submodule ℤ E) {N : ℕ} (hN : 1 ≤ N) :
    Nat.card {v : L // ‖(v : E)‖ ≤ N} =
      Nat.card ↑(Metric.closedBall (0 : E) 1 ∩ (N : ℝ)⁻¹ • (L : Set E)) := by
  have hc : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hN))
  have hset : Metric.closedBall (0 : E) (N : ℝ) = (N : ℝ) • Metric.closedBall (0 : E) 1 := by
    rw [smul_closedBall' hc (0 : E) 1]
    simp
  calc
    Nat.card {v : L // ‖(v : E)‖ ≤ N}
        = Nat.card {x : E // x ∈ (L : Set E) ∧ ‖x‖ ≤ N} := by
            refine Nat.card_congr ?_
            change {v : {y : E // y ∈ (L : Set E)} // ‖(v : E)‖ ≤ N} ≃
              {x : E // x ∈ (L : Set E) ∧ ‖x‖ ≤ N}
            exact Equiv.subtypeSubtypeEquivSubtypeInter (fun x : E => x ∈ (L : Set E))
              (fun x => ‖x‖ ≤ N)
    _ = Nat.card {x : E // x ∈ (L : Set E) ∧ x ∈ Metric.closedBall (0 : E) (N : ℝ)} := by
            refine Nat.card_congr ?_
            refine Equiv.subtypeEquivRight (fun x => ?_)
            rw [and_congr_right_iff]
            intro hx
            exact mem_closedBall_zero_iff.symm
    _ = Nat.card ↑(Metric.closedBall (0 : E) (N : ℝ) ∩ (L : Set E)) := by
            refine Nat.card_congr ?_
            refine Equiv.subtypeEquivRight (fun x => ?_)
            rw [Set.mem_inter_iff, and_comm]
    _ = Nat.card ↑(((N : ℝ) • Metric.closedBall (0 : E) 1) ∩ (L : Set E)) := by
            refine Nat.card_congr ?_
            refine Equiv.subtypeEquivRight (fun x => ?_)
            rw [hset]
    _ = Nat.card ↑(Metric.closedBall (0 : E) 1 ∩ (N : ℝ)⁻¹ • (L : Set E)) := by
            refine Nat.card_congr ?_
            refine (Equiv.subtypeEquiv (Equiv.smulRight hc) (fun x ↦ by
                simp_rw [Set.mem_inter_iff, Equiv.smulRight_apply, Set.smul_mem_smul_set_iff₀ hc,
                  ← Set.mem_inv_smul_set_iff₀ hc])).symm

lemma card_inter_closedBall_tendsto
    {n : ℕ} (hE : Nontrivial (EuclideanSpace ℝ (Fin n)))
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L] :
    Filter.Tendsto (fun N : ℕ =>
        (Nat.card {v : L // ‖(v : EuclideanSpace ℝ (Fin n))‖ ≤ N} : ℝ) / (N : ℝ) ^ n)
      Filter.atTop (nhds ((MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal /
        ZLattice.covolume L)) := by
  let E := EuclideanSpace ℝ (Fin n)
  have hfin : Module.finrank ℝ E = n := by
    dsimp [E]
    simp
  have hfront : volume (frontier (Metric.closedBall (0 : E) 1)) = 0 := by
    have hsub : frontier (Metric.closedBall (0 : E) 1) ⊆ Metric.sphere (0 : E) (1 : ℝ) :=
      Metric.frontier_closedBall_subset_sphere
    have hsphere : volume (Metric.sphere (0 : E) (1 : ℝ)) = 0 := by
      simpa using (MeasureTheory.Measure.addHaar_sphere_of_ne_zero volume (0 : E)
        (by norm_num : (1 : ℝ) ≠ 0))
    apply le_antisymm
    · simpa [hsphere] using (measure_mono (μ := volume) hsub)
    · simp
  have hmain := ZLattice.covolume.tendsto_card_div_pow' (E := E) L
      (s := Metric.closedBall (0 : E) 1)
      (Metric.isBounded_closedBall) (Metric.isClosed_closedBall.measurableSet) hfront
  refine Filter.Tendsto.congr' ?event (by simpa [hfin, measureReal_def] using hmain)
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  congr 1
  apply congrArg (fun k : ℕ => (k : ℝ))
  exact (lattice_ball_card_eq_smulSet (E := E) L hN).symm

end

end Commons.Lattice.Counting