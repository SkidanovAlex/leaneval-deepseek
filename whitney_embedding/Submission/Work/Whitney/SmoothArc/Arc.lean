import Mathlib
import Submission.Work.Whitney.SmoothArc.ManifoldBump
import Submission.Work.Whitney.SmoothArc.ChartArc

/-!
# Smooth arcs in an open path-connected subset of a smooth manifold

The main result of this file is `Work.Whitney.exists_smooth_arc_of_isPreconnected`: in an open
path-connected subset `W` of a smooth manifold, any two distinct points are joined by a smooth
injective arc lying in `W`.  The proof is the usual open/closed argument, in which the endpoint of
an arc is moved by the bump translation of `SmoothArc.ManifoldBump`, and the initial step uses the
chart arcs of `SmoothArc.ChartArc`.
-/

namespace Work.Whitney

open Set Metric Function
open scoped Manifold ContDiff

set_option maxHeartbeats 2000000 in
theorem exists_smooth_arc_of_isPreconnected {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M] [T2Space M]
    {W : Set M} (hW : IsOpen W) (hWc : IsPreconnected W) {x y : M}
    (hx : x ∈ W) (hy : y ∈ W) (hxy : x ≠ y) :
    ∃ γ : ℝ → M,
      ContMDiff 𝓘(ℝ,ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ γ ∧
      γ 0 = x ∧ γ 1 = y ∧ Set.InjOn γ (Set.Icc (0:ℝ) 1) ∧
      ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ W := by
  classical
  have chart_data : ∀ z ∈ W, ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (R : ℝ),
      0 < R ∧ z ∈ c.source ∧ ContMDiffOn (𝓡 n) (𝓡 n) ∞ c c.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ c.symm c.target ∧
      Metric.closedBall (c z) R ⊆ c.target ∧ c.symm '' Metric.closedBall (c z) R ⊆ W := by
    intro z hz
    have htgt : (extChartAt (𝓡 n) z).target = (chartAt (EuclideanSpace ℝ (Fin n)) z).target := by
      rw [extChartAt_target]
      simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
        Set.range_id, Set.inter_univ]
    have hcc : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (chartAt (EuclideanSpace ℝ (Fin n)) z)
        (chartAt (EuclideanSpace ℝ (Fin n)) z).source :=
      contMDiffOn_extChartAt (I := 𝓡 n) (x := z) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    have hcs : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (chartAt (EuclideanSpace ℝ (Fin n)) z).symm
        (chartAt (EuclideanSpace ℝ (Fin n)) z).target := by
      have h := contMDiffOn_extChartAt_symm (I := 𝓡 n) (x := z) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      rw [htgt] at h
      exact h
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp (chartAt (EuclideanSpace ℝ (Fin n)) z).open_target
      ((chartAt (EuclideanSpace ℝ (Fin n)) z) z) (mem_chart_target (EuclideanSpace ℝ (Fin n)) z)
    have hcont : ContinuousAt (chartAt (EuclideanSpace ℝ (Fin n)) z).symm
        ((chartAt (EuclideanSpace ℝ (Fin n)) z) z) :=
      (chartAt (EuclideanSpace ℝ (Fin n)) z).continuousOn_symm.continuousAt
        ((chartAt (EuclideanSpace ℝ (Fin n)) z).open_target.mem_nhds
          (mem_chart_target (EuclideanSpace ℝ (Fin n)) z))
    have hzW : (chartAt (EuclideanSpace ℝ (Fin n)) z).symm
        ((chartAt (EuclideanSpace ℝ (Fin n)) z) z) ∈ W := by
      rw [(chartAt (EuclideanSpace ℝ (Fin n)) z).left_inv (mem_chart_source (EuclideanSpace ℝ (Fin n)) z)]
      exact hz
    obtain ⟨σ, hσ, hσsub⟩ := Metric.mem_nhds_iff.mp (hcont (hW.mem_nhds hzW))
    refine ⟨chartAt (EuclideanSpace ℝ (Fin n)) z, min ρ σ / 2,
      div_pos (lt_min hρ hσ) (by norm_num),
      mem_chart_source (EuclideanSpace ℝ (Fin n)) z, hcc, hcs, ?_, ?_⟩
    · exact Subset.trans (Metric.closedBall_subset_ball (by have := min_le_left ρ σ; linarith)) hρsub
    · intro x' hx'
      obtain ⟨u, hu, rfl⟩ := hx'
      exact hσsub (Metric.closedBall_subset_ball (by have := min_le_right ρ σ; linarith) hu)
  have shrink : ∀ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (p : M) (R : ℝ),
      0 < R → Metric.closedBall (c p) R ⊆ c.target → p ∈ c.source → p ≠ x →
      ∃ R' : ℝ, R' > 0 ∧ R' ≤ R ∧ x ∉ c.symm '' Metric.ball (c p) R' ∧
        Metric.closedBall (c p) R' ⊆ c.target := by
    intro c p R hR hclosed hp hpx
    by_cases hxs : x ∈ c.source
    · have hcpx : c p ≠ c x := fun h => hpx (c.injOn hp hxs h)
      have hdpos : 0 < dist (c p) (c x) := dist_pos.mpr hcpx
      refine ⟨min R (dist (c p) (c x) / 2), lt_min hR (by linarith), min_le_left _ _, ?_, ?_⟩
      · rintro ⟨u, hu, hxu⟩
        have h1 : dist u (c p) < min R (dist (c p) (c x) / 2) := Metric.mem_ball.mp hu
        have huT : u ∈ c.target :=
          hclosed (Metric.mem_closedBall.mpr (le_of_lt (lt_of_lt_of_le h1 (min_le_left _ _))))
        have hcu : c x = u := by rw [← hxu, c.right_inv huT]
        have hcon : dist (c p) (c x) < dist (c p) (c x) := by
          calc dist (c p) (c x) ≤ dist (c p) u + dist u (c x) := dist_triangle _ _ _
            _ = dist (c p) u := by rw [hcu, dist_self, add_zero]
            _ = dist u (c p) := dist_comm (c p) u
            _ < min R (dist (c p) (c x) / 2) := h1
            _ ≤ dist (c p) (c x) / 2 := min_le_right _ _
            _ < dist (c p) (c x) := by linarith
        exact lt_irrefl _ hcon
      · exact Subset.trans (Metric.closedBall_subset_closedBall (min_le_left _ _)) hclosed
    · refine ⟨R, hR, le_rfl, ?_, hclosed⟩
      rintro ⟨u, hu, hxu⟩
      exact hxs (hxu ▸ c.map_target (hclosed (Metric.ball_subset_closedBall hu)))
  let S : Set M := {z | z ∈ W ∧ (z = x ∨ ∃ γ : ℝ → M,
      ContMDiff 𝓘(ℝ,ℝ) (𝓡 n) ∞ γ ∧ γ 0 = x ∧ γ 1 = z ∧
      Set.InjOn γ (Set.Icc (0:ℝ) 1) ∧ ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ W)}
  have hxS : x ∈ S := ⟨hx, Or.inl rfl⟩
  have hSopen : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    rintro z ⟨hzW, hzcase⟩
    by_cases hzx : z = x
    · obtain ⟨c, R, hR, hzc, hcc, hcs, hclosed, hRW⟩ := chart_data z hzW
      refine ⟨c.symm '' Metric.ball (c z) R, ?_, ?_, ?_⟩
      · rintro w hw
        obtain ⟨v, hv, rfl⟩ := hw
        have hvT : v ∈ c.target := hclosed (Metric.ball_subset_closedBall hv)
        have hwW : c.symm v ∈ W := hRW ⟨v, Metric.ball_subset_closedBall hv, rfl⟩
        refine ⟨hwW, ?_⟩
        by_cases hwz : c.symm v = z
        · exact Or.inl (hwz.trans hzx)
        · right
          have hvlt : ‖v - c z‖ < R := by
            have h := Metric.mem_ball.mp hv; rwa [dist_eq_norm] at h
          have hRv : (0:ℝ) < (‖v - c z‖ + R)/2 := by have := norm_nonneg (v - c z); linarith
          have hRlt : (‖v - c z‖ + R)/2 < R := by linarith
          have hcx : c x = c z := by rw [← hzx]
          have hca : c x ∈ Metric.closedBall (c z) ((‖v - c z‖ + R)/2) := by
            rw [Metric.mem_closedBall, hcx, dist_self]
            exact le_of_lt hRv
          have hcb : c (c.symm v) ∈ Metric.closedBall (c z) ((‖v - c z‖ + R)/2) := by
            rw [c.right_inv hvT, Metric.mem_closedBall, dist_eq_norm]
            linarith
          obtain ⟨γ, hγc, hγ0, hγ1, hγinj, hγmem⟩ := exists_contMDiff_chartArc (n := n) c hcs
            (y := z) (R₁ := (‖v - c z‖ + R)/2) (R₂ := R) hRv hRlt hclosed
            (a := x) (b := c.symm v) (show x ∈ c.source from hzx ▸ hzc) (c.map_target hvT)
            (fun h => hwz (h.symm.trans hzx.symm)) hca hcb
          exact ⟨γ, hγc, hγ0, hγ1, hγinj, fun t ht => hRW (hγmem t)⟩
      · exact c.isOpen_image_symm_of_subset_target Metric.isOpen_ball
          (fun v hv => hclosed (Metric.ball_subset_closedBall hv))
      · exact ⟨c z, Metric.mem_ball_self hR, c.left_inv hzc⟩
    · rcases hzcase with h | ⟨γ, hγc, hγ0, hγ1, hγinj, hγW⟩
      · exact absurd h hzx
      · obtain ⟨c, R, hR, hzc, hcc, hcs, hclosed, hRW⟩ := chart_data z hzW
        have hznex : z ≠ x := hzx
        obtain ⟨R', hR'pos, hR'le, hxnotin, hclosed'⟩ := shrink c z R hR hclosed hzc hznex
        have hRW' : c.symm '' Metric.closedBall (c z) R' ⊆ W := by
          intro x' hx'
          obtain ⟨u, hu, rfl⟩ := hx'
          exact hRW ⟨u, Metric.closedBall_subset_closedBall hR'le hu, rfl⟩
        obtain ⟨ε, hεpos, hεbump⟩ := exists_contMDiff_injective_bump (n := n)
        set δ : ℝ := min (R'/4) (ε * R'/4) / 2 with hδdef
        have hδpos : 0 < δ := by
          rw [hδdef]; exact div_pos (lt_min (by linarith) (by positivity)) (by norm_num)
        have hδ8 : δ ≤ R'/8 := by
          rw [hδdef]; have := min_le_left (R'/4) (ε * R'/4); linarith
        have hδR' : δ ≤ R' := by linarith
        have hδε : δ < ε * R' := by
          rw [hδdef]; have := min_le_right (R'/4) (ε * R'/4)
          have h2 : 0 < ε * R' := mul_pos hεpos hR'pos
          linarith
        refine ⟨c.symm '' Metric.ball (c z) δ, ?_, ?_, ?_⟩
        · rintro w hw
          obtain ⟨v, hv, rfl⟩ := hw
          have hvT : v ∈ c.target := hclosed' (Metric.mem_closedBall.mpr
            (le_trans (le_of_lt (Metric.mem_ball.mp hv)) hδR'))
          have hzv : ‖c (c.symm v) - c z‖ < ε * R' := by
            rw [c.right_inv hvT]
            have h := Metric.mem_ball.mp hv; rw [dist_eq_norm] at h; linarith
          obtain ⟨ψ, hψc, hψinj, hψid, hψw, hψA⟩ := hεbump c hcc hcs z hzc R' hR'pos hclosed'
            (c.symm v) (c.map_target hvT) hzv
          have hwmem : c.symm v ∈ W := hRW' ⟨v, Metric.closedBall_subset_closedBall hδR'
            (Metric.ball_subset_closedBall hv), rfl⟩
          refine ⟨hwmem, ?_⟩
          right
          refine ⟨ψ ∘ γ, hψc.comp hγc, ?_, ?_, ?_, ?_⟩
          · rw [Function.comp_apply, hγ0]; exact hψid x hxnotin
          · rw [Function.comp_apply, hγ1]; exact hψw
          · exact fun s hs t ht hst => hγinj hs ht (hψinj hst)
          · intro t ht
            by_cases htA : γ t ∈ c.symm '' Metric.ball (c z) R'
            · have hmem : ψ (γ t) ∈ c.symm '' Metric.ball (c z) R' := hψA ⟨γ t, htA, rfl⟩
              have hsub : c.symm '' Metric.ball (c z) R' ⊆ W := by
                intro x' hx'
                obtain ⟨u, hu, rfl⟩ := hx'
                exact hRW' ⟨u, Metric.ball_subset_closedBall hu, rfl⟩
              rw [Function.comp_apply]
              exact hsub hmem
            · rw [Function.comp_apply, hψid (γ t) htA]; exact hγW t ht
        · exact c.isOpen_image_symm_of_subset_target Metric.isOpen_ball
            (fun v hv => hclosed' (Metric.mem_closedBall.mpr (le_trans (le_of_lt (Metric.mem_ball.mp hv)) hδR')))
        · exact ⟨c z, Metric.mem_ball_self hδpos, c.left_inv hzc⟩
  have hScl : closure S ∩ W ⊆ S := by
    rintro p ⟨hpcl, hpW⟩
    by_cases hpx : p = x
    · exact ⟨hpW, Or.inl hpx⟩
    · obtain ⟨c, R, hR, hpc, hcc, hcs, hclosed, hRW⟩ := chart_data p hpW
      have hpnex : p ≠ x := hpx
      obtain ⟨R', hR'pos, hR'le, hxnotin, hclosed'⟩ := shrink c p R hR hclosed hpc hpnex
      have hRW' : c.symm '' Metric.closedBall (c p) R' ⊆ W := by
        intro x' hx'
        obtain ⟨u, hu, rfl⟩ := hx'
        exact hRW ⟨u, Metric.closedBall_subset_closedBall hR'le hu, rfl⟩
      obtain ⟨ε, hεpos, hεbump⟩ := exists_contMDiff_injective_bump (n := n)
      set δ : ℝ := min (R'/4) (ε * R'/4) / 2 with hδdef
      have hδpos : 0 < δ := by
        rw [hδdef]; exact div_pos (lt_min (by linarith) (by positivity)) (by norm_num)
      have hδ8 : δ ≤ R'/8 := by
        rw [hδdef]; have := min_le_left (R'/4) (ε * R'/4); linarith
      have hδR' : δ ≤ R' := by linarith
      have hδε : δ < ε * (R'/4) := by
        rw [hδdef]; have := min_le_right (R'/4) (ε * R'/4)
        have h2 : 0 < ε * (R'/4) := by positivity
        linarith
      have hballopen : IsOpen (c.symm '' Metric.ball (c p) δ) :=
        c.isOpen_image_symm_of_subset_target Metric.isOpen_ball
          (fun v hv => hclosed' (Metric.mem_closedBall.mpr (le_trans (le_of_lt (Metric.mem_ball.mp hv)) hδR')))
      have hpball : p ∈ c.symm '' Metric.ball (c p) δ := ⟨c p, Metric.mem_ball_self hδpos, c.left_inv hpc⟩
      obtain ⟨u, huB, huS⟩ := (mem_closure_iff_nhds.mp hpcl) _ (hballopen.mem_nhds hpball)
      rcases huS with ⟨huW, hux | ⟨γu, hγuc, hγu0, hγu1, hγuinj, hγuW⟩⟩
      · rcases huB with ⟨w, hwball, hwu⟩
        exact absurd ⟨w, Metric.ball_subset_ball hδR' hwball, hwu.trans hux⟩ hxnotin
      · rcases huB with ⟨w, hwball, hwu⟩
        have hwT : w ∈ c.target := hclosed' (Metric.mem_closedBall.mpr
          (le_trans (le_of_lt (Metric.mem_ball.mp hwball)) hδR'))
        have hcu : c u = w := by rw [← hwu, c.right_inv hwT]
        have hu_src : u ∈ c.source := hwu ▸ c.map_target hwT
        have hdist_uw : dist (c u) (c p) < δ := by rw [hcu]; exact Metric.mem_ball.mp hwball
        have hclosed'' : Metric.closedBall (c u) (R'/4) ⊆ c.target := by
          intro w' hw'
          apply hclosed'
          rw [Metric.mem_closedBall] at hw' ⊢
          calc dist w' (c p) ≤ dist w' (c u) + dist (c u) (c p) := dist_triangle _ _ _
            _ ≤ R'/4 + δ := add_le_add hw' (le_of_lt hdist_uw)
            _ ≤ R' := by linarith
        have hxu'' : x ∉ c.symm '' Metric.ball (c u) (R'/4) := by
          rintro ⟨w', hw', hxw'⟩
          apply hxnotin
          refine ⟨w', ?_, hxw'⟩
          rw [Metric.mem_ball] at hw' ⊢
          calc dist w' (c p) ≤ dist w' (c u) + dist (c u) (c p) := dist_triangle _ _ _
            _ < R'/4 + R'/4 := by
                refine add_lt_add hw' ?_
                rw [hcu]; exact lt_of_lt_of_le (Metric.mem_ball.mp hwball) (by linarith)
            _ ≤ R' := by linarith
        have hdist_up : ‖c p - c u‖ < ε * (R'/4) := by
          have h1 : dist (c u) (c p) < δ := hdist_uw
          rw [dist_eq_norm, norm_sub_rev] at h1
          linarith
        obtain ⟨ψ, hψc, hψinj, hψid, hψp, hψA⟩ := hεbump c hcc hcs u hu_src (R'/4) (by linarith)
          hclosed'' p hpc hdist_up
        refine ⟨hpW, ?_⟩
        right
        refine ⟨ψ ∘ γu, hψc.comp hγuc, ?_, ?_, ?_, ?_⟩
        · rw [Function.comp_apply, hγu0]; exact hψid x hxu''
        · rw [Function.comp_apply, hγu1]; exact hψp
        · exact fun s hs t ht hst => hγuinj hs ht (hψinj hst)
        · intro t ht
          by_cases htA : γu t ∈ c.symm '' Metric.ball (c u) (R'/4)
          · have hmem : ψ (γu t) ∈ c.symm '' Metric.ball (c u) (R'/4) := hψA ⟨γu t, htA, rfl⟩
            have hAsub : c.symm '' Metric.ball (c u) (R'/4) ⊆ c.symm '' Metric.closedBall (c p) R' := by
              rintro v ⟨v', hv', rfl⟩
              refine ⟨v', ?_, rfl⟩
              rw [Metric.mem_ball] at hv'
              exact Metric.mem_closedBall.mpr (le_of_lt (by
                calc dist v' (c p) ≤ dist v' (c u) + dist (c u) (c p) := dist_triangle _ _ _
                  _ < R'/4 + δ := add_lt_add hv' hdist_uw
                  _ ≤ R' := by linarith))
            rw [Function.comp_apply]
            exact hRW' (hAsub hmem)
          · rw [Function.comp_apply, hψid (γu t) htA]; exact hγuW t ht
  have hWsubS : W ⊆ S := hWc.subset_of_closure_inter_subset hSopen ⟨x, hx, hxS⟩ hScl
  rcases hWsubS hy with ⟨-, hycase⟩
  rcases hycase with h | ⟨γ, hγc, hγ0, hγ1, hγinj, hγW⟩
  · exact absurd h.symm hxy
  · exact ⟨γ, hγc, hγ0, hγ1, hγinj, hγW⟩

end Work.Whitney
