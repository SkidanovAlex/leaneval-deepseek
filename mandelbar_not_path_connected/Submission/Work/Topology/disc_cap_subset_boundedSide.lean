import Mathlib
import Submission.Work.TopJordan.SidesAPI

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Topology

/-- **Local two-sidedness of a Jordan curve along a circle arc.**  Let `C` be a Jordan curve
contained in the closed unit disc, passing through a point `x` of the unit circle, and such that
near `x` the points of the unit circle are exactly the points of `C`.  Then a whole cap of the
open unit disc near `x` lies in the bounded side of `C`. -/
theorem disc_cap_subset_boundedSide {C : Set ℂ} (S : Work.Top.Sides C)
    (hC : C ⊆ Metric.closedBall (0:ℂ) 1) {x : ℂ} (hx : x ∈ Metric.sphere (0:ℂ) 1)
    (hδ : ∃ δ > 0, Metric.ball x δ ∩ Metric.sphere (0:ℂ) 1 = Metric.ball x δ ∩ C) :
    ∃ ε > 0, Metric.ball x ε ∩ Metric.ball (0:ℂ) 1 ⊆ S.I := by
  obtain ⟨δ, hδpos, hδeq⟩ := hδ
  -- the local radius
  set ε : ℝ := min δ (1 / 2 : ℝ) / 2 with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact div_pos (lt_min hδpos (by norm_num)) (by norm_num)
  have hεδ : ε ≤ δ := by
    rw [hεdef]
    have h := min_le_left δ (1 / 2 : ℝ)
    linarith
  refine ⟨ε, hεpos, ?_⟩
  -- the circle agrees with `C` in the ball of radius `ε`
  have hballsub : Metric.ball x ε ⊆ Metric.ball x δ := Metric.ball_subset_ball hεδ
  have hloc : Metric.ball x ε ∩ Metric.sphere (0 : ℂ) 1 = Metric.ball x ε ∩ C := by
    calc Metric.ball x ε ∩ Metric.sphere (0 : ℂ) 1
        = (Metric.ball x ε ∩ Metric.ball x δ) ∩ Metric.sphere (0 : ℂ) 1 := by
            rw [Set.inter_eq_left.mpr hballsub]
      _ = Metric.ball x ε ∩ (Metric.ball x δ ∩ Metric.sphere (0 : ℂ) 1) := Set.inter_assoc ..
      _ = Metric.ball x ε ∩ (Metric.ball x δ ∩ C) := by rw [hδeq]
      _ = (Metric.ball x ε ∩ Metric.ball x δ) ∩ C := (Set.inter_assoc ..).symm
      _ = Metric.ball x ε ∩ C := by rw [Set.inter_eq_left.mpr hballsub]
  -- `x` lies on the curve
  have hxC : x ∈ C := by
    have h1 : x ∈ Metric.ball x δ ∩ Metric.sphere (0 : ℂ) 1 :=
      ⟨Metric.mem_ball_self hδpos, hx⟩
    rw [hδeq] at h1
    exact h1.2
  -- the inner cap `P` and the outer cap `Q`
  set P : Set ℂ := Metric.ball x ε ∩ Metric.ball (0 : ℂ) 1 with hPdef
  set Q : Set ℂ := Metric.ball x ε ∩ {z : ℂ | 1 < ‖z‖} with hQdef
  have hPpre : IsPreconnected P := by
    rw [hPdef]
    exact ((convex_ball x ε).inter (convex_ball (0 : ℂ) 1)).isPreconnected
  -- the inner cap misses the curve, by local agreement with the circle
  have hPsub : P ⊆ Cᶜ := by
    rw [hPdef]
    rintro z ⟨hzB, hz1⟩ hzC
    rw [Metric.mem_ball, dist_zero_right] at hz1
    have h1 : z ∈ Metric.ball x ε ∩ Metric.sphere (0 : ℂ) 1 := by
      rw [hloc]
      exact ⟨hzB, hzC⟩
    have h2 : dist z 0 = 1 := h1.2
    rw [dist_zero_right] at h2
    linarith
  -- the outer cap lies in the unbounded side
  have hQO : Q ⊆ S.O := by
    rw [hQdef]
    intro z hz
    exact Work.TopJordan.exterior_subset_sides_O S hC hz.2
  -- the two caps cover the ball minus the curve
  have hcov : Metric.ball x ε \ C ⊆ P ∪ Q := by
    rintro z ⟨hzB, hzC⟩
    have hzB' : dist z x < ε := hzB
    rcases lt_trichotomy ‖z‖ 1 with h | h | h
    · refine Or.inl ?_
      rw [hPdef]
      simp only [Set.mem_inter_iff, Metric.mem_ball, dist_zero_right]
      exact ⟨hzB', h⟩
    · exfalso
      have h1 : z ∈ Metric.ball x ε ∩ Metric.sphere (0 : ℂ) 1 := by
        refine ⟨hzB, ?_⟩
        rw [Metric.mem_sphere, dist_zero_right]
        exact h
      rw [hloc] at h1
      exact hzC h1.2
    · refine Or.inr ?_
      rw [hQdef]
      exact ⟨hzB, h⟩
  -- main step: the inner cap lies in the bounded side
  have hPI : P ⊆ S.I := by
    rcases S.subset_of_preconnected hPpre hPsub with h | h
    · exact h
    · exfalso
      have hxfront : x ∈ frontier S.I := by rw [S.frontier_I]; exact hxC
      have hxcl : x ∈ closure S.I := frontier_subset_closure hxfront
      obtain ⟨w, hwB, hwI⟩ := mem_closure_iff.mp hxcl (Metric.ball x ε) Metric.isOpen_ball
        (Metric.mem_ball_self hεpos)
      have hwC : w ∉ C := S.notMem_C_of_mem_I hwI
      rcases hcov ⟨hwB, hwC⟩ with hwP | hwQ
      · exact S.notMem_O_of_mem_I hwI (h hwP)
      · exact S.notMem_O_of_mem_I hwI (hQO hwQ)
  simpa only [hPdef] using hPI

end Work.Topology
