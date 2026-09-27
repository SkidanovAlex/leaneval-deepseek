import Mathlib
import Submission.Work.Whitney.PathTools.exists_arc_of_isPathConnected
import Submission.Work.Whitney.PathTools.isPathConnected_sdiff_finite_of_isOpen
import Submission.Work.Noncompact.CompressionTube.exists_arc_first_exit_of_collar

/-!
# One strand's `(EXIT)` arc out of the collar

The per-strand level step of the spine recursion (`NOTES_pocketFree_collar_SESSION.md` §4ter).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option autoImplicit false

namespace Work.Noncompact.CompressionTube

open Set Topology

theorem exists_level_arc_of_collar {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {C K L U Shell : Set M}
    (hC : IsOpen C) (hCc : IsPreconnected C) (hLc : IsClosed L) (hKc : IsCompact K)
    (hLK : L ⊆ K) (hUo : IsOpen U) (hUL : Disjoint U L)
    (hShellO : IsOpen Shell) (hfrontShell : frontier L ⊆ Shell)
    (hpieces : ∀ z ∈ frontier L, ∃ (x : M) (b : Work.Whitney.PathTools.ChartBall n M Set.univ x),
      z ∈ b.K ∧ b.c.symm '' Metric.ball (b.c x) b.ρ ⊆ U)
    {s : M} (hsC : s ∈ C) (hsint : s ∈ interior L) (hnt : ¬ IsCompact (closure C))
    {F : Set M} (hF : F.Finite) (hsF : s ∉ F)
    {k : ℕ} {β : Fin k → ℝ → M} (hβc : ∀ j, Continuous (β j))
    (hβsub : ∀ j, β j '' Set.Ioc (0:ℝ) 1 ⊆ U)
    (hβ0F : ∀ j, β j 0 ∈ F)
    (hβfront : ∀ j, ∀ z ∈ frontier L, z ∈ closure (β j '' Set.Icc (0:ℝ) 1) → z ∈ F) :
    ∃ (α : ℝ → M) (σ : ℝ), Continuous α ∧ Set.InjOn α (Set.Icc (0:ℝ) 1) ∧ α 0 = s ∧
      σ ∈ Set.Icc (0:ℝ) 1 ∧ (∀ u ∈ Set.Icc (0:ℝ) σ, α u ∈ L) ∧
      (∀ u ∈ Set.Ioc σ 1, α u ∉ L) ∧ (∀ u ∈ Set.Ioc σ 1, α u ∈ U) ∧
      α 1 ∈ Shell ∧ α 1 ∈ U ∧ α 1 ∉ F ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, α u ∈ C ∪ U) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, α u ∉ F) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, ∀ j, α u ∉ β j '' Set.Icc (0:ℝ) 1) ∧
      0 < σ ∧ σ < 1 := by
  classical
  haveI : LocallyPathConnectedSpace M :=
    Work.Whitney.PathTools.locallyPathConnectedSpace_chartedSpace (n := n)
  obtain ⟨γ₁, t₀, hγ₁c, hγ₁i, hγ₁0, hγ₁C, hγ₁1L, ht₀, hγ₁L, hzfr, hγ₁F⟩ :=
    exists_arc_first_exit_of_collar_avoiding hn hC hCc hLc hKc hLK hsC (interior_subset hsint) hnt
      (hF.inter_of_left C) inter_subset_right (fun h => hsF h.1)
  have hzL : γ₁ t₀ ∈ L := hLc.closure_eq ▸ frontier_subset_closure hzfr
  have hzU : γ₁ t₀ ∉ U := fun h => (Set.disjoint_left.mp hUL h) hzL
  obtain ⟨x, b, hzbK, hbU⟩ := hpieces (γ₁ t₀) hzfr
  have hzsrc : γ₁ t₀ ∈ b.c.source := b.K_subset_source hzbK
  have hzF : γ₁ t₀ ∉ F := fun h => hγ₁F t₀ ht₀ ⟨h, hγ₁C t₀ ht₀⟩
  have hzβ : ∀ j, γ₁ t₀ ∉ β j '' Set.Icc (0:ℝ) 1 := fun j hmem =>
    absurd (hβfront j (γ₁ t₀) hzfr (subset_closure hmem)) hzF
  -- the open set to be avoided near the exit point
  have hclβ : IsClosed (⋃ j : Fin k, β j '' Set.Icc (0:ℝ) 1) := by
    have h := (Set.finite_univ (α := Fin k)).isClosed_biUnion
      (f := fun j : Fin k => β j '' Set.Icc (0:ℝ) 1)
      (fun j _ => (isCompact_Icc.image (hβc j)).isClosed)
    simpa only [Set.mem_univ, Set.iUnion_true] using h
  have hYopen : IsOpen (Shell ∩ Fᶜ ∩ ⋂ j, (β j '' Set.Icc (0:ℝ) 1)ᶜ) := by
    refine (hShellO.inter (hF.isClosed.isOpen_compl)).inter ?_
    simpa only [Set.compl_iUnion] using hclβ.isOpen_compl
  have hzY : γ₁ t₀ ∈ Shell ∩ Fᶜ ∩ ⋂ j, (β j '' Set.Icc (0:ℝ) 1)ᶜ := by
    refine ⟨⟨hfrontShell hzfr, hzF⟩, ?_⟩
    simp only [Set.mem_iInter, Set.mem_compl_iff]
    exact hzβ
  -- a small chart ball around the exit point inside it
  obtain ⟨ρ, hρ0, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (b.c (γ₁ t₀)) ρ ⊆
      b.c '' ((Shell ∩ Fᶜ ∩ ⋂ j, (β j '' Set.Icc (0:ℝ) 1)ᶜ) ∩ b.c.source) :=
    Metric.mem_nhds_iff.mp (b.c.image_mem_nhds hzsrc
      (Filter.inter_mem (hYopen.mem_nhds hzY) (b.c.open_source.mem_nhds hzsrc)))
  have hballT : Metric.ball (b.c (γ₁ t₀)) ρ ⊆ b.c.target := fun v hv => by
    obtain ⟨v', hv', hvv'⟩ := hρ hv
    rw [← hvv']; exact b.c.map_source hv'.2
  have hVopen : IsOpen (b.c.symm '' Metric.ball (b.c (γ₁ t₀)) ρ) :=
    b.c.isOpen_image_symm_of_subset_target Metric.isOpen_ball hballT
  have hρY : b.c.symm '' Metric.ball (b.c (γ₁ t₀)) ρ ⊆
      Shell ∩ Fᶜ ∩ ⋂ j, (β j '' Set.Icc (0:ℝ) 1)ᶜ := by
    rintro y ⟨v, hv, rfl⟩
    obtain ⟨v', hv', hvv'⟩ := hρ hv
    rw [show b.c.symm v = b.c.symm (b.c v') from by rw [hvv'], b.c.left_inv hv'.2]
    exact hv'.1
  have hzV : γ₁ t₀ ∈ b.c.symm '' Metric.ball (b.c (γ₁ t₀)) ρ :=
    ⟨b.c (γ₁ t₀), Metric.mem_ball_self hρ0, b.c.left_inv hzsrc⟩
  have hopenReg : IsOpen (b.c.symm '' Metric.ball (b.c (γ₁ t₀)) ρ ∩
      b.c.symm '' Metric.ball (b.c x) b.ρ ∩ Shell) :=
    (hVopen.inter b.ballImage_open).inter hShellO
  -- the region is nonempty: an explicit point on the chart segment from the exit point to the centre
  have hxz : b.c x ≠ b.c (γ₁ t₀) := by
    intro h
    have h1 : x = γ₁ t₀ := by
      have h2 : x = b.c.symm (b.c x) := (b.c.left_inv (b.K_subset_source b.self_mem_K)).symm
      have h3 : b.c.symm (b.c x) = b.c.symm (b.c (γ₁ t₀)) := by rw [h]
      rw [h2, h3, b.c.left_inv hzsrc]
    exact hzU (h1 ▸ hbU b.self_mem_ballImage)
  -- the chart coordinates of the exit point
  obtain ⟨v₀, hv₀, hv₀z⟩ := hzbK
  have hztK : b.c (γ₁ t₀) ∈ Metric.closedBall (b.c x) b.ρ := by
    rw [show b.c (γ₁ t₀) = v₀ from by rw [← hv₀z, b.c.right_inv (b.hclosed hv₀)]]
    exact hv₀
  have hN : ‖b.c x - b.c (γ₁ t₀)‖ ≤ b.ρ := by
    rw [norm_sub_rev]
    simpa [Metric.mem_closedBall, dist_eq_norm] using hztK
  have hN' : ‖b.c (γ₁ t₀) - b.c x‖ ≤ b.ρ := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hztK
  have hneReg : (b.c.symm '' Metric.ball (b.c (γ₁ t₀)) ρ ∩
      b.c.symm '' Metric.ball (b.c x) b.ρ ∩ Shell).Nonempty := by
    have hNn : (0:ℝ) ≤ ‖b.c x - b.c (γ₁ t₀)‖ := norm_nonneg _
    have hden : 0 < 2 * (‖b.c x - b.c (γ₁ t₀)‖ + 1) := by linarith
    set s : ℝ := min (1/2) (ρ / (2 * (‖b.c x - b.c (γ₁ t₀)‖ + 1))) with hsdef
    have hs0 : 0 < s := lt_min (by norm_num) (div_pos hρ0 hden)
    have hs1 : s ≤ 1/2 := min_le_left _ _
    have hsN : s * ‖b.c x - b.c (γ₁ t₀)‖ < ρ := by
      have h3 : s * ‖b.c x - b.c (γ₁ t₀)‖
          ≤ (ρ / (2 * (‖b.c x - b.c (γ₁ t₀)‖ + 1))) * ‖b.c x - b.c (γ₁ t₀)‖ :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hNn
      have h4 : (ρ / (2 * (‖b.c x - b.c (γ₁ t₀)‖ + 1))) * ‖b.c x - b.c (γ₁ t₀)‖ < ρ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
        nlinarith [hNn, hρ0, mul_nonneg hρ0.le hNn]
      linarith
    have hsN' : (1 - s) * ‖b.c (γ₁ t₀) - b.c x‖ < b.ρ := by
      have h5 : (1 - s) * ‖b.c (γ₁ t₀) - b.c x‖ ≤ (1 - s) * b.ρ :=
        mul_le_mul_of_nonneg_left hN' (by linarith)
      have h6 : (1 - s) * b.ρ < b.ρ := by nlinarith [hs0, b.hρ]
      linarith
    refine ⟨b.c.symm ((1 - s) • b.c (γ₁ t₀) + s • b.c x), ⟨?_, ?_⟩, ?_⟩
    · refine ⟨_, ?_, rfl⟩
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : (1 - s) • b.c (γ₁ t₀) + s • b.c x - b.c (γ₁ t₀)
          = s • (b.c x - b.c (γ₁ t₀)) := by module
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0.le]
      exact hsN
    · refine ⟨_, ?_, rfl⟩
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : (1 - s) • b.c (γ₁ t₀) + s • b.c x - b.c x
          = (1 - s) • (b.c (γ₁ t₀) - b.c x) := by module
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s)]
      exact hsN'
    · exact (hρY ⟨(1 - s) • b.c (γ₁ t₀) + s • b.c x, (by
        rw [Metric.mem_ball, dist_eq_norm]
        have h1 : (1 - s) • b.c (γ₁ t₀) + s • b.c x - b.c (γ₁ t₀)
            = s • (b.c x - b.c (γ₁ t₀)) := by module
        rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0.le]
        exact hsN), rfl⟩).1.1
  obtain ⟨tt, htt⟩ :=
    ((Work.Whitney.PathTools.infinite_of_isOpen_nonempty (n := n) hn hopenReg hneReg).sdiff hF).nonempty
  have httV : tt ∈ b.c.symm '' Metric.ball (b.c (γ₁ t₀)) ρ := htt.1.1.1
  have httPiece : tt ∈ b.c.symm '' Metric.ball (b.c x) b.ρ := htt.1.1.2
  have httShell : tt ∈ Shell := htt.1.2
  have httF : tt ∉ F := htt.2
  have httSrc : tt ∈ b.c.source := b.K_subset_source (b.ballImage_subset_K httPiece)
  -- the chart coordinates of the tip
  obtain ⟨v₁, hv₁, hv₁t⟩ := httPiece
  have hv₁c : v₁ ∈ Metric.closedBall (b.c x) b.ρ := Metric.ball_subset_closedBall hv₁
  have httK : b.c tt ∈ Metric.closedBall (b.c x) b.ρ := by
    rw [show b.c tt = v₁ from by rw [← hv₁t, b.c.right_inv (b.hclosed hv₁c)]]
    exact hv₁c
  have httBall : b.c tt ∈ Metric.ball (b.c x) b.ρ := by
    rw [show b.c tt = v₁ from by rw [← hv₁t, b.c.right_inv (b.hclosed hv₁c)]]
    exact hv₁
  have httBallV : b.c tt ∈ Metric.ball (b.c (γ₁ t₀)) ρ := by
    obtain ⟨w, hw, hwt⟩ := httV
    rw [show b.c tt = w from by rw [← hwt, b.c.right_inv (hballT hw)]]
    exact hw
  have hzw : b.c (γ₁ t₀) ≠ b.c tt := by
    intro h
    have h1 : γ₁ t₀ = tt := by
      have h2 : γ₁ t₀ = b.c.symm (b.c (γ₁ t₀)) := (b.c.left_inv hzsrc).symm
      rw [h2, h, b.c.left_inv httSrc]
    exact hzU (h1 ▸ hbU (htt.1.1.2))
  -- the outside segment from the exit point to the tip
  set δ : ℝ → M := fun u =>
    b.c.symm (b.c (γ₁ t₀) + Work.Whitney.PathTools.clamp u • (b.c tt - b.c (γ₁ t₀))) with hδdef
  have hδc : Continuous δ := b.continuous_seg hztK httK
  have hδi : Set.InjOn δ (Set.Icc (0:ℝ) 1) := b.seg_injOn hztK httK hzw
  have hδ0 : δ 0 = γ₁ t₀ := (b.seg_zero _ _).trans (b.c.left_inv hzsrc)
  have hδ1 : δ 1 = tt := (b.seg_one _ _).trans (b.c.left_inv httSrc)
  have hδV : ∀ u ∈ Set.Icc (0:ℝ) 1, δ u ∈ b.c.symm '' Metric.ball (b.c (γ₁ t₀)) ρ := by
    intro u _
    refine ⟨_, ?_, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : b.c (γ₁ t₀) + Work.Whitney.PathTools.clamp u • (b.c tt - b.c (γ₁ t₀)) - b.c (γ₁ t₀)
        = Work.Whitney.PathTools.clamp u • (b.c tt - b.c (γ₁ t₀)) := by abel
    rw [h1, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Work.Whitney.PathTools.clamp_nonneg u)]
    have h2 : ‖b.c tt - b.c (γ₁ t₀)‖ < ρ := by
      simpa [Metric.mem_ball, dist_eq_norm] using httBallV
    nlinarith [Work.Whitney.PathTools.clamp_le_one u, Work.Whitney.PathTools.clamp_nonneg u,
      norm_nonneg (b.c tt - b.c (γ₁ t₀))]
  have hδY : ∀ u ∈ Set.Icc (0:ℝ) 1, δ u ∈ Shell ∩ Fᶜ ∩ ⋂ j, (β j '' Set.Icc (0:ℝ) 1)ᶜ :=
    fun u hu => hρY (hδV u hu)
  have hδavoidF : ∀ u ∈ Set.Icc (0:ℝ) 1, δ u ∉ F := fun u hu h => (hδY u hu).1.2 h
  have hδavoidβ : ∀ u ∈ Set.Icc (0:ℝ) 1, ∀ j, δ u ∉ β j '' Set.Icc (0:ℝ) 1 := by
    intro u hu j hj
    exact (Set.mem_iInter.mp (hδY u hu).2) j hj
  have hδOpen : ∀ u ∈ Set.Ioc (0:ℝ) 1, δ u ∈ b.c.symm '' Metric.ball (b.c x) b.ρ := by
    intro u hu
    have hcu : Work.Whitney.PathTools.clamp u = u :=
      Work.Whitney.PathTools.clamp_of_mem ⟨hu.1.le, hu.2⟩
    refine ⟨_, ?_, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have halg : b.c (γ₁ t₀) + Work.Whitney.PathTools.clamp u • (b.c tt - b.c (γ₁ t₀)) - b.c x
        = (1 - Work.Whitney.PathTools.clamp u) • (b.c (γ₁ t₀) - b.c x)
          + Work.Whitney.PathTools.clamp u • (b.c tt - b.c x) := by module
    rw [halg]
    have hcw0 : 0 < Work.Whitney.PathTools.clamp u := by
      rw [hcu]; exact hu.1
    have hcw1 : Work.Whitney.PathTools.clamp u ≤ 1 := Work.Whitney.PathTools.clamp_le_one u
    have ha : ‖b.c (γ₁ t₀) - b.c x‖ ≤ b.ρ := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hztK
    have hb2 : ‖b.c tt - b.c x‖ < b.ρ := by
      simpa [Metric.mem_ball, dist_eq_norm] using httBall
    have hnn : (0:ℝ) ≤ 1 - Work.Whitney.PathTools.clamp u := by linarith
    calc ‖(1 - Work.Whitney.PathTools.clamp u) • (b.c (γ₁ t₀) - b.c x)
          + Work.Whitney.PathTools.clamp u • (b.c tt - b.c x)‖
        ≤ ‖(1 - Work.Whitney.PathTools.clamp u) • (b.c (γ₁ t₀) - b.c x)‖
          + ‖Work.Whitney.PathTools.clamp u • (b.c tt - b.c x)‖ := norm_add_le _ _
      _ = (1 - Work.Whitney.PathTools.clamp u) * ‖b.c (γ₁ t₀) - b.c x‖
          + Work.Whitney.PathTools.clamp u * ‖b.c tt - b.c x‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn,
            abs_of_nonneg (le_of_lt hcw0)]
      _ < (1 - Work.Whitney.PathTools.clamp u) * b.ρ
          + Work.Whitney.PathTools.clamp u * b.ρ := by
          have h1 : (1 - Work.Whitney.PathTools.clamp u) * ‖b.c (γ₁ t₀) - b.c x‖
              ≤ (1 - Work.Whitney.PathTools.clamp u) * b.ρ :=
            mul_le_mul_of_nonneg_left ha hnn
          have h2 : Work.Whitney.PathTools.clamp u * ‖b.c tt - b.c x‖
              < Work.Whitney.PathTools.clamp u * b.ρ :=
            mul_lt_mul_of_pos_left hb2 hcw0
          linarith
      _ = b.ρ := by ring
  have hδU : ∀ u ∈ Set.Ioc (0:ℝ) 1, δ u ∈ U := fun u hu => hbU (hδOpen u hu)
  have hδnotL : ∀ u ∈ Set.Ioc (0:ℝ) 1, δ u ∉ L := fun u hu h =>
    (Set.disjoint_left.mp hUL (hδU u hu)) h
  -- the two cases: `t₀ = 0` (the exit is the start point) and `t₀ > 0`
  by_cases ht₀0 : t₀ = 0
  · -- impossible: the inside piece is trivial only if the start point is already on the
    -- frontier, but `s` lies in the *interior* of the collar
    exfalso
    have h1 : γ₁ t₀ ∈ interior L := by rw [ht₀0, hγ₁0]; exact hsint
    have h2 : γ₁ t₀ ∈ frontier L := hzfr
    rw [hLc.frontier_eq] at h2
    exact h2.2 h1
  · have hpos : 0 < t₀ := lt_of_le_of_ne ht₀.1 (Ne.symm ht₀0)
    set βb : ℝ → M := fun u => γ₁ (u * t₀) with hβbdef
    have hβb0 : βb 0 = s := by rw [hβbdef]; simp [hγ₁0]
    have hβb1 : βb 1 = γ₁ t₀ := by rw [hβbdef]; simp
    have hβbi : Set.InjOn βb (Set.Icc (0:ℝ) 1) := by
      intro u hu u' hu' h
      have h1 : u * t₀ = u' * t₀ :=
        hγ₁i ⟨by nlinarith [hu.1, hpos.le], by nlinarith [hu.2, ht₀.2]⟩
             ⟨by nlinarith [hu'.1, hpos.le], by nlinarith [hu'.2, ht₀.2]⟩ h
      exact mul_right_cancel₀ (ne_of_gt hpos) h1
    have hβbL : ∀ u ∈ Set.Icc (0:ℝ) 1, βb u ∈ L := by
      intro u hu
      exact hγ₁L (u * t₀) ⟨by nlinarith [hu.1, hpos.le], by nlinarith [hu.2, ht₀.2]⟩
    have hβbC : ∀ u ∈ Set.Icc (0:ℝ) 1, βb u ∈ C := by
      intro u hu
      exact hγ₁C (u * t₀) ⟨by nlinarith [hu.1, hpos.le], by nlinarith [hu.2, ht₀.2]⟩
    have hβbF : ∀ u ∈ Set.Icc (0:ℝ) 1, βb u ∉ F := by
      intro u hu h
      exact hγ₁F (u * t₀) ⟨by nlinarith [hu.1, hpos.le], by nlinarith [hu.2, ht₀.2]⟩
        ⟨h, hγ₁C (u * t₀) ⟨by nlinarith [hu.1, hpos.le], by nlinarith [hu.2, ht₀.2]⟩⟩
    set α : ℝ → M := fun u => if (1:ℝ)/2 ≤ u then δ (2 * u - 1) else βb (2 * u) with hαdef
    have hα1 : ∀ u, u < (1:ℝ)/2 → α u = βb (2 * u) := by
      intro u hu; rw [hαdef]; simp only [if_neg (not_le.mpr hu)]
    have hα2 : ∀ u, (1:ℝ)/2 ≤ u → α u = δ (2 * u - 1) := by
      intro u hu; rw [hαdef]; simp only [if_pos hu]
    have hαc : Continuous α := by
      rw [hαdef]
      refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_const continuous_id ?_
      intro u hu
      rw [← hu]
      norm_num
      exact hδ0.trans hβb1.symm
    have hinL : ∀ u ∈ Set.Icc (0:ℝ) (1/2), α u ∈ L := by
      intro u hu
      rcases lt_or_eq_of_le hu.2 with h | h
      · rw [hα1 u h]
        exact hβbL (2 * u) ⟨by linarith [hu.1], by linarith⟩
      · rw [h, hα2 (1/2) le_rfl]
        norm_num
        rw [hδ0]
        exact hzL
    have houtL : ∀ u ∈ Set.Ioc (1/2) 1, α u ∉ L := by
      intro u hu
      rw [hα2 u (le_of_lt hu.1)]
      exact hδnotL (2 * u - 1) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hαU : ∀ u ∈ Set.Ioc (1/2) 1, α u ∈ U := by
      intro u hu
      rw [hα2 u (le_of_lt hu.1)]
      exact hδU (2 * u - 1) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have himgCU : ∀ u ∈ Set.Icc (0:ℝ) 1, α u ∈ C ∪ U := by
      intro u hu
      rcases lt_or_ge u ((1:ℝ)/2) with h | h
      · rw [hα1 u h]
        exact Set.mem_union_left _ (hβbC (2 * u) ⟨by linarith [hu.1], by linarith⟩)
      · rcases eq_or_lt_of_le h with heq | hlt
        · rw [← heq, hα2 (1/2) le_rfl]
          norm_num
          rw [hδ0]
          exact Set.mem_union_left _ (hβb1 ▸ hβbC 1 ⟨zero_le_one, le_rfl⟩)
        · rw [hα2 u h]
          exact Set.mem_union_right _ (hδU (2 * u - 1) ⟨by linarith, by linarith [hu.2]⟩)
    have hkey : ∀ u ∈ Set.Icc (0:ℝ) 1, ∀ u' ∈ Set.Icc (0:ℝ) 1, u ≤ u' → α u = α u' → u = u' := by
      intro u hu u' hu' hle heq
      rcases lt_or_ge u' ((1:ℝ)/2) with h' | h'
      · rw [hα1 u (lt_of_le_of_lt hle h'), hα1 u' h'] at heq
        have h2 := hβbi ⟨by linarith [hu.1], by linarith [hu.2]⟩
          ⟨by linarith [hu'.1], by linarith [hu'.2]⟩ heq
        linarith
      · rcases lt_or_ge u ((1:ℝ)/2) with h | h
        · rcases lt_or_eq_of_le h' with hlt' | heq'
          · have h1 : α u ∈ L := hinL u ⟨hu.1, le_of_lt h⟩
            have h2 : α u' ∉ L := houtL u' ⟨hlt', hu'.2⟩
            rw [heq] at h1
            exact absurd h1 h2
          · rw [← heq']
            rw [hα1 u h] at heq
            rw [← heq', hα2 (1/2) le_rfl] at heq
            norm_num at heq
            rw [hδ0, ← hβb1] at heq
            have h3 := hβbi ⟨by linarith [hu.1], by linarith⟩ ⟨zero_le_one, le_rfl⟩ heq
            linarith
        · rw [hα2 u h, hα2 u' h'] at heq
          have h2 := hδi ⟨by linarith, by linarith [hu.2]⟩
            ⟨by linarith, by linarith [hu'.2]⟩ heq
          linarith
    have hαi : Set.InjOn α (Set.Icc (0:ℝ) 1) := by
      intro u hu u' hu' heq
      rcases le_total u u' with hle | hle
      · exact hkey u hu u' hu' hle heq
      · exact (hkey u' hu' u hu hle heq.symm).symm
    have hαF : ∀ u ∈ Set.Icc (0:ℝ) 1, α u ∉ F := by
      intro u hu
      rcases lt_or_ge u ((1:ℝ)/2) with h | h
      · rw [hα1 u h]
        exact hβbF (2 * u) ⟨by linarith [hu.1], by linarith⟩
      · rcases eq_or_lt_of_le h with heq | hlt
        · rw [← heq, hα2 (1/2) le_rfl]
          norm_num
          rw [hδ0]
          exact hzF
        · rw [hα2 u h]
          exact hδavoidF (2 * u - 1) ⟨by linarith, by linarith [hu.2]⟩
    have hαβ : ∀ u ∈ Set.Icc (0:ℝ) 1, ∀ j, α u ∉ β j '' Set.Icc (0:ℝ) 1 := by
      intro u hu j
      rcases lt_or_ge u ((1:ℝ)/2) with h | h
      · rw [hα1 u h]
        intro hmem
        obtain ⟨t, ht, hbt⟩ := hmem
        have hmemL : βb (2 * u) ∈ L :=
          hβbL (2 * u) ⟨by linarith [hu.1], by linarith⟩
        rcases eq_or_lt_of_le ht.1 with h0 | h0
        · rw [← h0] at hbt
          exact hβbF (2 * u) ⟨by linarith [hu.1], by linarith⟩ (hbt ▸ hβ0F j)
        · exact (Set.disjoint_left.mp hUL (hβsub j ⟨t, ⟨h0, ht.2⟩, rfl⟩))
            (by rw [hbt]; exact hmemL)
      · rcases eq_or_lt_of_le h with heq | hlt
        · rw [← heq, hα2 (1/2) le_rfl]
          norm_num
          rw [hδ0]
          intro xx hx1 hx2 hmem
          exact hzβ j ⟨xx, ⟨hx1, hx2⟩, hmem⟩
        · rw [hα2 u h]
          exact hδavoidβ (2 * u - 1) ⟨by linarith, by linarith [hu.2]⟩ j
    refine ⟨α, 1/2, hαc, hαi, ?_, ⟨by norm_num, by norm_num⟩, hinL, houtL, hαU, ?_, ?_, ?_, himgCU, hαF, hαβ, ?_, ?_⟩
    · rw [hα1 0 (by norm_num)]; norm_num; exact hβb0
    · rw [hα2 1 (by norm_num)]; norm_num; rw [hδ1]; exact httShell
    · rw [hα2 1 (by norm_num)]; norm_num; rw [hδ1]; exact hbU (htt.1.1.2)
    · rw [hα2 1 (by norm_num)]; norm_num; rw [hδ1]; exact httF
    · norm_num
    · norm_num

/-- **Removing a compact set keeps the closure non-compact.**  This is the bookkeeping step of the
peeling construction of `exists_disjoint_exit_arcs_of_collar`: the carrier of the `(i+1)`-st strand
is `C` minus the (compact) images of the strands already routed, and the first-exit argument of
`exists_level_arc_of_collar` still needs `¬ IsCompact (closure ·)`. -/
theorem not_isCompact_closure_sdiff_of_isCompact {M : Type*} [TopologicalSpace M] [T2Space M]
    {C K : Set M} (hnt : ¬ IsCompact (closure C)) (hK : IsCompact K) :
    ¬ IsCompact (closure (C \ K)) := by
  intro hcon
  have hsub : closure C ⊆ closure (C \ K) ∪ K := by
    refine closure_minimal ?_ (hcon.isClosed.union hK.isClosed)
    intro x hx
    by_cases hxK : x ∈ K
    · exact Or.inr hxK
    · exact Or.inl (subset_closure ⟨hx, hxK⟩)
  exact hnt ((hcon.union hK).of_isClosed_subset isClosed_closure hsub)

/-- **The inside piece of a `(EXIT)` arc is again an arc.**  The peeling construction of
`exists_disjoint_exit_arcs_of_collar` must delete the already routed strands' *inside pieces*
(`α '' Icc 0 σ`) from the carrier; `Work.Noncompact.Routing.isPreconnected_sdiff_iUnion_image_arcs`
wants each of them reparameterized as an arc `[0,1] → M`. -/
theorem isArc_inside_piece {M : Type*} [TopologicalSpace M] {α : ℝ → M} (hα : Continuous α)
    (hinj : Set.InjOn α (Set.Icc (0:ℝ) 1)) {σ : ℝ} (hσ : σ ∈ Set.Ioc (0:ℝ) 1) :
    Continuous (fun u : ℝ => α (u * σ)) ∧
      Set.InjOn (fun u : ℝ => α (u * σ)) (Set.Icc (0:ℝ) 1) ∧
      (fun u : ℝ => α (u * σ)) '' Set.Icc (0:ℝ) 1 ⊆ α '' Set.Icc (0:ℝ) σ := by
  refine ⟨?_, ?_, ?_⟩
  · exact hα.comp (continuous_id.mul continuous_const)
  · intro u hu v hv huv
    have hu' : u * σ ∈ Set.Icc (0:ℝ) 1 :=
      ⟨mul_nonneg hu.1 hσ.1.le, by nlinarith [hu.2, hσ.2, hσ.1]⟩
    have hv' : v * σ ∈ Set.Icc (0:ℝ) 1 :=
      ⟨mul_nonneg hv.1 hσ.1.le, by nlinarith [hv.2, hσ.2, hσ.1]⟩
    have h2 : u * σ = v * σ := hinj hu' hv' huv
    exact mul_right_cancel₀ (ne_of_gt hσ.1) h2
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨u * σ, ⟨mul_nonneg hu.1 hσ.1.le, by nlinarith [hu.2, hσ.2, hσ.1]⟩, rfl⟩

end Work.Noncompact.CompressionTube
