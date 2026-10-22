import Mathlib
import Submission.Work.CWTOP.Basic
import Submission.Work.CWTOP.Pieces

/-!
# CWTOP: the radial homotopy descends to the collar space

The radial homotopy `stepHomPiece` on the glued pieces is constant on the fibres of `stepGlue`, so
that it factors through the collar space; equivalently, for each parameter `t` the map
`stepHomPiece (t, ·)` is constant on the fibres of `stepGlue`.

The proof is the same case analysis as for the radial projection
(`Submission.Work.CWTOP.Pieces`, `stepRadialPiece_factors`) with `radialUnitSafe` replaced by
`radialInterpSafe (·) t`: a collar point whose image lies in the `n`-skeleton has norm exactly `1`,
and there the interpolation is constant, so everything reduces to the values of the characteristic
maps.
-/

open CategoryTheory Limits Topology Set Function Metric

noncomputable section

namespace Work.CWTOP

variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

/-- At a fixed parameter `t`, the radial homotopy `stepHomPiece` is constant on the fibres of
`stepGlue`. -/
lemma stepHomPiece_factors_point (n : ℕ) (t : unitInterval) {p q : stepPieces C n}
    (hpq : stepGlue C n p = stepGlue C n q) :
    stepHomPiece C n (t, p) = stepHomPiece C n (t, q) := by
  have hval : ((stepGlue C n p : {x : X // x ∈ stepCollar C n}) : X)
      = ((stepGlue C n q : {x : X // x ∈ stepCollar C n}) : X) := congrArg Subtype.val hpq
  rcases p with x | ⟨j, y⟩
  · rcases q with x' | ⟨j', y'⟩
    · refine Subtype.ext ?_
      rw [stepHomPiece_inl_val n t x, stepHomPiece_inl_val n t x']
      simpa only [stepGlue_inl_val] using hval
    · have h1 : (x : X) = RelCWComplex.map (n + 1) j' (y' : Fin (n + 1) → ℝ) := by
        simpa only [stepGlue_inl_val, stepGlue_inr_val] using hval
      have hyS : RelCWComplex.map (n + 1) j' (y' : Fin (n + 1) → ℝ) ∈ skel C n := by
        rw [← h1]
        exact x.2
      have hu : radialInterpSafe (y' : Fin (n + 1) → ℝ) (t : ℝ) = (y' : Fin (n + 1) → ℝ) :=
        radialInterpSafe_eq_self_of_norm_eq_one
          (norm_eq_one_of_map_mem_skel j' (mem_closedBall_of_mem_modelCollar y'.2) hyS) t
      refine Subtype.ext ?_
      rw [stepHomPiece_inl_val n t x, stepHomPiece_inr_val n t j' y', hu]
      exact h1
  · rcases q with x' | ⟨j', y'⟩
    · have h1 : RelCWComplex.map (n + 1) j (y : Fin (n + 1) → ℝ) = (x' : X) := by
        simpa only [stepGlue_inr_val, stepGlue_inl_val] using hval
      have hyS : RelCWComplex.map (n + 1) j (y : Fin (n + 1) → ℝ) ∈ skel C n := by
        rw [h1]
        exact x'.2
      have hu : radialInterpSafe (y : Fin (n + 1) → ℝ) (t : ℝ) = (y : Fin (n + 1) → ℝ) :=
        radialInterpSafe_eq_self_of_norm_eq_one
          (norm_eq_one_of_map_mem_skel j (mem_closedBall_of_mem_modelCollar y.2) hyS) t
      refine Subtype.ext ?_
      rw [stepHomPiece_inr_val n t j y, hu, stepHomPiece_inl_val n t x']
      exact h1
    · have hmap : RelCWComplex.map (n + 1) j (y : Fin (n + 1) → ℝ)
          = RelCWComplex.map (n + 1) j' (y' : Fin (n + 1) → ℝ) := by
        simpa only [stepGlue_inr_val] using hval
      have hycl : (y : Fin (n + 1) → ℝ) ∈ Metric.closedBall 0 1 :=
        mem_closedBall_of_mem_modelCollar y.2
      have hy'cl : (y' : Fin (n + 1) → ℝ) ∈ Metric.closedBall 0 1 :=
        mem_closedBall_of_mem_modelCollar y'.2
      have hd : Disjoint (skel C n) (RelCWComplex.openCell (n + 1) j) :=
        RelCWComplex.disjoint_skeleton_openCell (C := C) (n := (n : ℕ∞)) (m := n + 1) (j := j)
          (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self n))
      by_cases hy : ‖(y : Fin (n + 1) → ℝ)‖ = 1
      · have hy' : ‖(y' : Fin (n + 1) → ℝ)‖ = 1 := by
          refine norm_eq_one_of_map_mem_skel j' hy'cl ?_
          rw [← hmap]
          exact RelCWComplex.cellFrontier_subset_skeleton (n := n) (j := j)
            ⟨(y : Fin (n + 1) → ℝ), by
              rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hy, rfl⟩
        refine Subtype.ext ?_
        rw [stepHomPiece_inr_val n t j y, stepHomPiece_inr_val n t j' y',
          radialInterpSafe_eq_self_of_norm_eq_one hy t,
          radialInterpSafe_eq_self_of_norm_eq_one hy' t]
        exact hmap
      · have hlt : ‖(y : Fin (n + 1) → ℝ)‖ < 1 :=
          lt_of_le_of_ne (by rw [← dist_zero_right]; exact Metric.mem_closedBall.mp hycl) hy
        have hy'ne : ‖(y' : Fin (n + 1) → ℝ)‖ ≠ 1 := by
          intro h1
          have hS : RelCWComplex.map (n + 1) j (y : Fin (n + 1) → ℝ) ∈ skel C n := by
            rw [hmap]
            exact RelCWComplex.cellFrontier_subset_skeleton (n := n) (j := j')
              ⟨(y' : Fin (n + 1) → ℝ), by
                rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact h1, rfl⟩
          exact Set.disjoint_left.mp hd hS
            ⟨(y : Fin (n + 1) → ℝ), by rwa [Metric.mem_ball, dist_eq_norm, sub_zero], rfl⟩
        obtain ⟨hj, hyeq⟩ := eq_of_map_eq_of_norm_ne_one j j'
          (by rwa [Metric.mem_ball, dist_eq_norm, sub_zero])
          (by
            rw [Metric.mem_ball, dist_eq_norm, sub_zero]
            exact lt_of_le_of_ne
              (by rw [← dist_zero_right]; exact Metric.mem_closedBall.mp hy'cl) hy'ne)
          hmap hlt
        subst hj
        refine Subtype.ext ?_
        rw [stepHomPiece_inr_val n t j y, stepHomPiece_inr_val n t j y', hyeq]

theorem stepHomPiece_factors {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X}
    [Topology.CWComplex C] (n : ℕ) :
    Function.FactorsThrough (Work.CWTOP.stepHomPiece C n)
      (Prod.map id (Work.CWTOP.stepGlue C n)) := by
  intro a b hab
  obtain ⟨t, p⟩ := a
  obtain ⟨s, q⟩ := b
  simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at hab
  obtain ⟨ht, hg⟩ := hab
  simpa only [← ht] using stepHomPiece_factors_point n t hg

end Work.CWTOP

end
