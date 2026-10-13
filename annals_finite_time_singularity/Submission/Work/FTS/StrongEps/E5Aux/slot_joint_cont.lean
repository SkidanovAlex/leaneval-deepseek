import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.E5Aux.contDiffOn_zero_mixed_le
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux

theorem slot_joint_cont {F : ℝ → Work.FTS.Galerkin.Fn} {T : ℝ}
    (hsm : ∀ τ ∈ Set.Icc 0 T,
      ContDiffOn ℝ 4 (Function.uncurry (F τ)) Work.FTS.EllipticEst.Q0)
    (hlipF : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (j i : ℕ), j + i ≤ 1 → ∀ p ∈ K,
        ∀ τ ∈ Set.Icc 0 T, ∀ τ' ∈ Set.Icc 0 T,
          |Work.Spaces.mixed j i (F τ) p.1 p.2
            - Work.Spaces.mixed j i (F τ') p.1 p.2| ≤ C * |τ - τ'|) :
    ∀ (j i : ℕ), j + i ≤ 1 →
      ContinuousOn (fun q : ℝ × ℝ × ℝ => Work.Spaces.mixed j i (F q.2.2) q.1 q.2.1)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 T) := by
  intro j i hji
  -- Componentwise control of `dist q q0` for `q q0 : ℝ × ℝ × ℝ = ℝ × (ℝ × ℝ)`
  -- (that space carries the sup metric, `Prod.dist_eq`).
  have dist_pair_le_dist_triple : ∀ {q q0 : ℝ × ℝ × ℝ},
      dist (q.1, q.2.1) (q0.1, q0.2.1) ≤ dist q q0 := by
    intro q q0
    simp only [Prod.dist_eq]
    exact max_le (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
  have abs_sub_snd_snd_le_dist_triple : ∀ {q q0 : ℝ × ℝ × ℝ},
      |q.2.2 - q0.2.2| ≤ dist q q0 := by
    intro q q0
    simp only [Prod.dist_eq, Real.dist_eq]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  -- Spatial continuity of every slot `mixed j i (F τ)` on the open quadrant, at each fixed
  -- time `τ ∈ [0,T]`: `D_z^j D_θ^i` costs `j + i ≤ 1 ≤ 4` of the four available orders.
  have hA : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i (F τ) p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
    intro τ hτ
    exact (contDiffOn_zero_mixed_le (n := 4) (hsm τ hτ) (by omega)).continuousOn
  intro q0 hq0
  obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq0
  obtain ⟨hq21, hq22⟩ := Set.mem_prod.mp hq2
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hp0 : (q0.1, q0.2.1) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hq1, hq21.1, hq21.2⟩
  -- A compact neighbourhood of `(q0.1, q0.2.1)` inside the open quadrant.
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp Work.FTS.EllipticEst.isOpen_Q0 _ hp0
  have hr0pos : 0 < r / 2 := by linarith
  have hKsub : Metric.closedBall (q0.1, q0.2.1) (r / 2) ⊆ Work.FTS.EllipticEst.Q0 :=
    (Metric.closedBall_subset_ball (by linarith : r / 2 < r)).trans hrsub
  have hK : IsCompact (Metric.closedBall (q0.1, q0.2.1) (r / 2)) := isCompact_closedBall _ _
  obtain ⟨C, hC0, hC⟩ := hlipF _ hK hKsub
  -- Continuity at the base point (spatial variables), and the Lipschitz bound in time on
  -- the compact neighbourhood.
  have hcont0 : ContinuousAt
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i (F q0.2.2) p.1 p.2) (q0.1, q0.2.1) :=
    (hA q0.2.2 hq22).continuousAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp0)
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨δ2, hδ2pos, hδ2⟩ := (Metric.continuousAt_iff.mp hcont0) (ε / 2) hε2
  set δ := min (r / 2) (min (ε / (2 * (C + 1))) δ2) with hδdef
  have hC1 : 0 < C + 1 := by linarith
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min hr0pos (lt_min (div_pos hε (by linarith)) hδ2pos)
  refine ⟨δ, hδpos, ?_⟩
  intro q hq hdq
  obtain ⟨hq1', hq2'⟩ := Set.mem_prod.mp hq
  obtain ⟨hq21', hq22'⟩ := Set.mem_prod.mp hq2'
  have hδ_le_r : δ ≤ r / 2 := by rw [hδdef]; exact min_le_left _ _
  have hδ_le_eps : δ ≤ ε / (2 * (C + 1)) := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ_le_δ2 : δ ≤ δ2 := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hdp : dist (q.1, q.2.1) (q0.1, q0.2.1) < δ :=
    lt_of_le_of_lt dist_pair_le_dist_triple hdq
  have hpK : (q.1, q.2.1) ∈ Metric.closedBall (q0.1, q0.2.1) (r / 2) :=
    Metric.mem_closedBall.mpr (le_of_lt (lt_of_lt_of_le hdp hδ_le_r))
  -- The two terms of the telescoping decomposition.
  have h1 : |Work.Spaces.mixed j i (F q.2.2) q.1 q.2.1
      - Work.Spaces.mixed j i (F q0.2.2) q.1 q.2.1| ≤ C * |q.2.2 - q0.2.2| :=
    hC j i hji (q.1, q.2.1) hpK q.2.2 hq22' q0.2.2 hq22
  have h2 : dist (Work.Spaces.mixed j i (F q0.2.2) q.1 q.2.1)
      (Work.Spaces.mixed j i (F q0.2.2) q0.1 q0.2.1) < ε / 2 :=
    hδ2 (lt_of_lt_of_le hdp hδ_le_δ2)
  rw [Real.dist_eq] at h2
  have hdτ : |q.2.2 - q0.2.2| ≤ δ :=
    le_of_lt (lt_of_le_of_lt abs_sub_snd_snd_le_dist_triple hdq)
  have h4 : C * |q.2.2 - q0.2.2| < ε / 2 := by
    have hprod : C * |q.2.2 - q0.2.2| ≤ C * (ε / (2 * (C + 1))) :=
      mul_le_mul_of_nonneg_left (hdτ.trans hδ_le_eps) hC0
    have hlt : C * (ε / (2 * (C + 1))) < ε / 2 := by
      have hCe : C / (C + 1) < 1 := by rw [div_lt_one hC1]; linarith
      have heq : C * (ε / (2 * (C + 1))) = (ε / 2) * (C / (C + 1)) := by field_simp
      rw [heq]
      calc (ε / 2) * (C / (C + 1)) < (ε / 2) * 1 := mul_lt_mul_of_pos_left hCe (by linarith)
        _ = ε / 2 := by ring
    linarith
  rw [Real.dist_eq]
  have hsplit : Work.Spaces.mixed j i (F q.2.2) q.1 q.2.1
      - Work.Spaces.mixed j i (F q0.2.2) q0.1 q0.2.1
      = (Work.Spaces.mixed j i (F q.2.2) q.1 q.2.1
          - Work.Spaces.mixed j i (F q0.2.2) q.1 q.2.1)
      + (Work.Spaces.mixed j i (F q0.2.2) q.1 q.2.1
          - Work.Spaces.mixed j i (F q0.2.2) q0.1 q0.2.1) := by ring
  rw [hsplit]
  have := abs_add_le
    (Work.Spaces.mixed j i (F q.2.2) q.1 q.2.1 - Work.Spaces.mixed j i (F q0.2.2) q.1 q.2.1)
    (Work.Spaces.mixed j i (F q0.2.2) q.1 q.2.1 - Work.Spaces.mixed j i (F q0.2.2) q0.1 q0.2.1)
  linarith

end Work.FTS.StrongEps.E5Aux
