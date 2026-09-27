import Mathlib
import Submission.Work.Noncompact.CompressionTube.LineBuild.piece_basic
import Submission.Work.Noncompact.ProperLine.rayAssemble
import Submission.Work.Noncompact.ProperLine.raySmooth

/-!
# The stage piece of the line construction

`Work.Noncompact.CompressionTube.nc_stage_piece`: the stage piece, in the import cone of the
canal construction.  See the module docstring at the end of the file for the construction.
-/

open Set Metric Topology
open scoped Manifold ContDiff Pointwise

namespace Work.Noncompact.CompressionTube

/-- **A small chart ball around the centre misses a closed set avoiding the centre.** -/
theorem nc_chartBall_avoids {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {z : M}
    (hcsrc : z ∈ c.source) (hcz : c z = 0) {K : Set M} (hK : IsClosed K) (hzK : z ∉ K) :
    ∃ ρ : ℝ, 0 < ρ ∧ c.symm '' Metric.ball 0 ρ ⊆ Kᶜ := by
  have hmem : (0 : EuclideanSpace ℝ (Fin n)) ∈ c.target := by
    rw [← hcz]; exact c.map_source hcsrc
  have hcont : ContinuousAt (⇑c.symm) 0 :=
    c.continuousOn_symm.continuousAt (c.open_target.mem_nhds hmem)
  have hopen : (⇑c.symm) ⁻¹' Kᶜ ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)) :=
    hcont.preimage_mem_nhds (hK.isOpen_compl.mem_nhds (by
      rw [show (⇑c.symm) 0 = z from by rw [← hcz]; exact c.left_inv hcsrc]
      exact hzK))
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hopen
  refine ⟨ρ, hρ, ?_⟩
  rintro x ⟨y, hy, hxy⟩
  have h1 : (⇑c.symm) y ∈ Kᶜ := hρsub (Metric.mem_ball.mp hy)
  rwa [hxy] at h1


/-- `Real.smoothTransition` maps `[0,1]` onto `[0,1]`. -/
theorem nc_smoothTransition_surjOn :
    Set.SurjOn Real.smoothTransition (Set.Icc (0:ℝ) 1) (Set.Icc (0:ℝ) 1) := by
  intro y hy
  rcases eq_or_lt_of_le hy.1 with h | h
  · exact ⟨0, ⟨le_refl 0, zero_le_one⟩, by rw [← h, Real.smoothTransition.zero]⟩
  rcases eq_or_lt_of_le hy.2 with h' | h'
  · exact ⟨1, ⟨zero_le_one, le_refl 1⟩, by rw [h', Real.smoothTransition.one]⟩
  · have hcont : ContinuousOn Real.smoothTransition (Set.Icc (0:ℝ) 1) :=
      Real.smoothTransition.continuous.continuousOn
    have hmem : y ∈ Set.Icc (Real.smoothTransition 0) (Real.smoothTransition 1) := by
      rw [Real.smoothTransition.zero, Real.smoothTransition.one]
      exact ⟨h.le, h'.le⟩
    obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc (zero_le_one : (0:ℝ) ≤ 1) hcont hmem
    exact ⟨x, hx, hxy⟩

/-- **The stage piece.** -/
theorem nc_stage_piece {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M] [T2Space M]
    {X : Set M} (hXo : IsOpen X) (hXp : IsPreconnected X)
    {O : Set M} (hOX : Disjoint O X)
    {z : M} (hzO : z ∈ O) {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hcsrc : z ∈ c.source) (hcz : c z = 0)
    (hcsymm : ContMDiffOn (MC n) (MC n) smoothOrder (⇑c.symm) c.target)
    {δ : ℝ} (hδ : 0 < δ) (hδtgt : Metric.closedBall 0 δ ⊆ c.target)
    {w : EuclideanSpace ℝ (Fin n)} (hw : ‖w‖ = 1)
    (hGerm : O ∩ (c.symm '' Metric.closedBall 0 δ) ⊆
      c.symm '' {y : EuclideanSpace ℝ (Fin n) | ∃ s : ℝ, 0 ≤ s ∧ s ≤ δ ∧ y = s • w})
    {ε : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ / 2)
    {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ = 1) (hvw : inner ℝ v w = 0)
    (hqX : c.symm (ε • v) ∈ X)
    {z' : M} (hz'X : z' ∈ X) (hz'far : z' ∉ c.symm '' Metric.closedBall 0 δ)
    {c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc'src : z' ∈ c'.source) (hc'z : c' z' = 0)
    (hc'symm : ContMDiffOn (MC n) (MC n) smoothOrder (⇑c'.symm) c'.target)
    {ε' : ℝ} (hε' : 0 < ε') (hε'tgt : Metric.closedBall 0 ε' ⊆ c'.target)
    (hε'X : c'.symm '' Metric.closedBall 0 ε' ⊆ X)
    {u' : EuclideanSpace ℝ (Fin n)} (hu' : ‖u'‖ = 1)
    (hdisj : Disjoint (c.symm '' Metric.closedBall 0 δ) (c'.symm '' Metric.closedBall 0 ε')) :
    ∃ P : ℝ → M, ContMDiff MCreal (MC n) smoothOrder P ∧
      (∀ t : ℝ, t ≤ 0 → P t = z) ∧ (∀ t : ℝ, 1 ≤ t → P t = z') ∧
      Set.InjOn P (Set.Icc (0:ℝ) 1) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, P t ∈ X ∪ c.symm '' Metric.closedBall 0 δ) ∧
      (P '' Set.Icc (0:ℝ) 1 ∩ O ⊆ {z}) ∧
      (∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ε' ∧
        (P '' Set.Icc (0:ℝ) 1 ∩ c'.symm '' Metric.ball 0 ρ) =
          c'.symm '' {y : EuclideanSpace ℝ (Fin n) | ∃ s : ℝ, 0 ≤ s ∧ s < ρ ∧ y = s • u'}) := by
  classical
  -- ## 0. setup
  have hc0 : c.symm 0 = z := by rw [← hcz]; exact c.left_inv hcsrc
  have hc'0 : c'.symm 0 = z' := by rw [← hc'z]; exact c'.left_inv hc'src
  set q : M := c.symm (ε • v) with hqdef
  set q' : M := c'.symm (ε' • u') with hq'def
  have hε_ball : ε • v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) δ := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hv, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hε.le]
    linarith [hεδ, hδ]
  have hε'_ball : ε' • u' ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ε' := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hu', mul_one, Real.norm_eq_abs,
      abs_of_nonneg hε'.le]
  have hq_ne : q ≠ q' := by
    intro h
    have h1 : q ∈ c.symm '' Metric.closedBall 0 δ := ⟨ε • v, hε_ball, rfl⟩
    have h2 : q ∈ c'.symm '' Metric.closedBall 0 ε' := by rw [h]; exact ⟨ε' • u', hε'_ball, rfl⟩
    exact Set.disjoint_left.mp hdisj h1 h2
  -- ## 1. the region for the middle arc
  haveI : LocallyPathConnectedSpace M :=
    Work.Whitney.PathTools.locallyPathConnectedSpace_chartedSpace (n := n)
  have hWopen : IsOpen (X \ {z'}) := hXo.sdiff isClosed_singleton
  have hWpc : IsPreconnected (X \ {z'}) := by
    have hcX : IsConnected X := ⟨⟨z', hz'X⟩, hXp⟩
    have hpc : IsPathConnected X := (hXo.isConnected_iff_isPathConnected).mp hcX
    exact (Work.Whitney.PathTools.isPathConnected_sdiff_finite_of_isOpen hn hXo hpc
      (Set.finite_singleton z') (Set.singleton_subset_iff.mpr hz'X)).isConnected.isPreconnected
  have hq_not : q ∉ ({z'} : Set M) := by
    intro h
    rw [Set.mem_singleton_iff] at h
    exact hz'far ⟨ε • v, hε_ball, by rw [← hqdef]; exact h⟩
  have hq'X : q' ∈ X := hε'X ⟨ε' • u', hε'_ball, rfl⟩
  have hq'_not : q' ∉ ({z'} : Set M) := by
    intro h
    rw [Set.mem_singleton_iff] at h
    have h1 : c'.symm (ε' • u') = c'.symm 0 := by rw [hc'0]; exact h
    have h2 := c'.symm.injOn
      (hε'tgt (by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hu', mul_one, Real.norm_eq_abs,
          abs_of_nonneg hε'.le]))
      (by rw [← hc'z]; exact c'.map_source hc'src) h1
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (ne_of_gt hε')
    · exact absurd h3 (by intro h4; rw [h4] at hu'; norm_num at hu')
  obtain ⟨γ, hγsm, hγ0, hγ1, hγinj, hγW, _hγf0, _hγf1⟩ :=
    Work.Noncompact.ProperLine.exists_flat_smooth_arc (n := n) hn hWopen hWpc
      ⟨hqX, hq_not⟩ ⟨hq'X, hq'_not⟩ hq_ne
  -- ## 2. the two chart radii as sets
  set A : Set M := c.symm '' {y : EuclideanSpace ℝ (Fin n) | ∃ s : ℝ, 0 ≤ s ∧ s ≤ ε ∧ y = s • v}
    with hAdef
  set C : Set M := c'.symm '' {y : EuclideanSpace ℝ (Fin n) | ∃ s : ℝ, 0 ≤ s ∧ s ≤ ε' ∧ y = s • u'}
    with hCdef
  have hA_sub : A ⊆ c.symm '' Metric.closedBall 0 δ := by
    rw [hAdef]
    rintro x ⟨y, ⟨s, hs0, hsε, rfl⟩, rfl⟩
    refine ⟨s • v, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hv, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hs0]
    linarith [hsε, hεδ, hδ]
  have hC_sub : C ⊆ c'.symm '' Metric.closedBall 0 ε' := by
    rw [hCdef]
    rintro x ⟨y, ⟨s, hs0, hsε, rfl⟩, rfl⟩
    exact ⟨s • u', by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hu', mul_one, Real.norm_eq_abs,
        abs_of_nonneg hs0]
      exact hsε, rfl⟩
  have hAcompact : IsCompact A := by
    rw [hAdef]
    have himg : (fun s : ℝ => c.symm (s • v)) '' Set.Icc (0:ℝ) ε
        = c.symm '' {y : EuclideanSpace ℝ (Fin n) | ∃ s : ℝ, 0 ≤ s ∧ s ≤ ε ∧ y = s • v} := by
      ext x; constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨s • v, ⟨s, hs.1, hs.2, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨s, hs0, hsε, rfl⟩, rfl⟩
        exact ⟨s, ⟨hs0, hsε⟩, rfl⟩
    rw [← himg]
    refine IsCompact.image_of_continuousOn isCompact_Icc ?_
    refine ContinuousOn.comp hcsymm.continuousOn
      (continuous_id.smul continuous_const).continuousOn ?_
    intro s hs
    exact hδtgt (by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hv, mul_one, Real.norm_eq_abs,
        abs_of_nonneg hs.1]
      linarith [hs.2, hεδ, hδ])
  have hCcompact : IsCompact C := by
    rw [hCdef]
    have himg : (fun s : ℝ => c'.symm (s • u')) '' Set.Icc (0:ℝ) ε'
        = c'.symm '' {y : EuclideanSpace ℝ (Fin n) | ∃ s : ℝ, 0 ≤ s ∧ s ≤ ε' ∧ y = s • u'} := by
      ext x; constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨s • u', ⟨s, hs.1, hs.2, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨s, hs0, hsε, rfl⟩, rfl⟩
        exact ⟨s, ⟨hs0, hsε⟩, rfl⟩
    rw [← himg]
    refine IsCompact.image_of_continuousOn isCompact_Icc ?_
    refine ContinuousOn.comp hc'symm.continuousOn
      (continuous_id.smul continuous_const).continuousOn ?_
    intro s hs
    exact hε'tgt (by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hu', mul_one, Real.norm_eq_abs,
        abs_of_nonneg hs.1]
      exact hs.2)
  have hAclosed : IsClosed A := hAcompact.isClosed
  have hCclosed : IsClosed C := hCcompact.isClosed
  -- ## 3. the two cuts
  set T : Set ℝ := Set.Icc (0:ℝ) 1 ∩ γ ⁻¹' A with hTdef
  have hTclosed : IsClosed T := isClosed_Icc.inter (hAclosed.preimage hγsm.continuous)
  have hTne : T.Nonempty := ⟨0, ⟨⟨le_refl 0, zero_le_one⟩, by
    rw [Set.mem_preimage, hγ0]
    rw [hqdef]
    rw [hAdef]
    exact ⟨ε • v, ⟨ε, hε.le, le_rfl, rfl⟩, rfl⟩⟩⟩
  have hTbdd : BddAbove T := ⟨1, fun t ht => ht.1.2⟩
  set t₀ : ℝ := sSup T with ht₀def
  have ht₀T : t₀ ∈ T := hTclosed.csSup_mem hTne hTbdd
  have ht₀Icc : t₀ ∈ Set.Icc (0:ℝ) 1 := ht₀T.1
  have hγt₀A : γ t₀ ∈ A := ht₀T.2
  obtain ⟨y₀, hy₀S, hy₀eq⟩ := hγt₀A
  obtain ⟨s₀, hs₀0, hs₀ε, hy₀v⟩ := hy₀S
  have hs₀eq : c.symm (s₀ • v) = γ t₀ := by rw [← hy₀v]; exact hy₀eq
  have ht₀max : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ A → t ≤ t₀ :=
    fun t ht hmem => le_csSup hTbdd ⟨ht, hmem⟩
  set T' : Set ℝ := Set.Icc t₀ 1 ∩ γ ⁻¹' C with hT'def
  have hT'closed : IsClosed T' := isClosed_Icc.inter (hCclosed.preimage hγsm.continuous)
  have hT'ne : T'.Nonempty := ⟨1, ⟨⟨ht₀Icc.2, le_rfl⟩, by
    rw [Set.mem_preimage, hγ1]
    rw [hq'def]
    rw [hCdef]
    exact ⟨ε' • u', ⟨ε', hε'.le, le_rfl, rfl⟩, rfl⟩⟩⟩
  have hT'bdd : BddBelow T' := ⟨t₀, fun t ht => ht.1.1⟩
  set t₁ : ℝ := sInf T' with ht₁def
  have ht₁T : t₁ ∈ T' := hT'closed.csInf_mem hT'ne hT'bdd
  have ht₁Icc : t₁ ∈ Set.Icc t₀ 1 := ht₁T.1
  have hγt₁C : γ t₁ ∈ C := ht₁T.2
  obtain ⟨y₁, hy₁S, hy₁eq⟩ := hγt₁C
  obtain ⟨s₁, hs₁0, hs₁ε', hy₁v⟩ := hy₁S
  have hs₁eq : c'.symm (s₁ • u') = γ t₁ := by rw [← hy₁v]; exact hy₁eq
  have ht₁min : ∀ t ∈ Set.Icc t₀ 1, t < t₁ → γ t ∉ C :=
    fun t ht hlt hmem => absurd (csInf_le hT'bdd ⟨ht, hmem⟩) (not_le.mpr hlt)
  have hs₀pos : 0 < s₀ := by
    rcases eq_or_lt_of_le hs₀0 with h | h
    · exfalso
      have hγz : γ t₀ = z := by
        have hzz : c.symm (s₀ • v) = z := by rw [← h, zero_smul, hc0]
        rwa [hs₀eq] at hzz
      have hzX : z ∈ X := by
        rw [← hγz]
        exact (hγW t₀ ht₀Icc).1
      exact Set.disjoint_left.mp hOX hzO hzX
    · exact h
  have hs₁pos : 0 < s₁ := by
    rcases eq_or_lt_of_le hs₁0 with h | h
    · exfalso
      apply (hγW t₁ ⟨le_trans ht₀Icc.1 ht₁Icc.1, ht₁Icc.2⟩).2
      have hz' : c'.symm (s₁ • u') = z' := by rw [← h, zero_smul, hc'0]
      rw [Set.mem_singleton_iff, ← hs₁eq, hz']
    · exact h
  have ht₀t₁ : t₀ < t₁ := by
    rcases lt_or_eq_of_le ht₁Icc.1 with h | h
    · exact h
    · exfalso
      have h1 : γ t₀ ∈ C := h.symm ▸ ht₁T.2
      have h2 : c.symm (s₀ • v) ∈ c'.symm '' Metric.closedBall 0 ε' := by
        rw [hs₀eq]
        exact hC_sub h1
      exact Set.disjoint_left.mp hdisj (hA_sub (by
        rw [hAdef]
        exact ⟨s₀ • v, ⟨s₀, hs₀0, hs₀ε, rfl⟩, rfl⟩)) h2
  -- ## 4. the three partial curves
  set Arad : ℝ → M := fun t => c.symm ((s₀ * Real.smoothTransition (3 * t)) • v) with hAraddef
  set Bmid : ℝ → M := fun t => γ (t₀ + (t₁ - t₀) * Real.smoothTransition (3 * t - 1))
    with hBmiddef
  set Crad : ℝ → M := fun t => c'.symm ((s₁ * (1 - Real.smoothTransition (3 * t - 2))) • u')
    with hCraddef
  have harg_mem : ∀ t : ℝ, t₀ + (t₁ - t₀) * Real.smoothTransition (3 * t - 1) ∈ Set.Icc (0:ℝ) 1 := by
    intro t
    constructor
    · have : 0 ≤ (t₁ - t₀) * Real.smoothTransition (3 * t - 1) :=
        mul_nonneg (by linarith) (Real.smoothTransition.nonneg _)
      linarith [ht₀Icc.1]
    · have : (t₁ - t₀) * Real.smoothTransition (3 * t - 1) ≤ t₁ - t₀ :=
        mul_le_of_le_one_right (by linarith) (Real.smoothTransition.le_one _)
      linarith [ht₁Icc.2]
  have harg_ge : ∀ t : ℝ, t₀ ≤ t₀ + (t₁ - t₀) * Real.smoothTransition (3 * t - 1) := by
    intro t
    have h := mul_nonneg (sub_nonneg.mpr ht₀t₁.le) (Real.smoothTransition.nonneg (3 * t - 1))
    linarith
  have hA_sm : ContMDiff MCreal (MC n) smoothOrder Arad := by
    have hpoly : ContMDiff MCreal (MC n) smoothOrder
        (fun t : ℝ => (s₀ * Real.smoothTransition (3 * t)) • v) := by
      rw [contMDiff_iff_contDiff]
      exact (contDiff_const.mul (Real.smoothTransition.contDiff.comp
        (contDiff_const.mul contDiff_id))).smul contDiff_const
    have hsymm : ∀ t : ℝ, ContMDiffAt (MC n) (MC n) smoothOrder (⇑c.symm)
        ((s₀ * Real.smoothTransition (3 * t)) • v) := by
      intro t
      refine hcsymm.contMDiffAt ?_
      refine c.open_target.mem_nhds (hδtgt ?_)
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hv, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hs₀0 (Real.smoothTransition.nonneg _))]
      have h1 : s₀ * Real.smoothTransition (3 * t) ≤ s₀ :=
        mul_le_of_le_one_right hs₀0 (Real.smoothTransition.le_one (3 * t))
      linarith [h1, hs₀ε, hεδ, hδ]
    intro t
    exact (hsymm t).comp t hpoly.contMDiffAt
  have hB_sm : ContMDiff MCreal (MC n) smoothOrder Bmid := by
    have hpsi : ContMDiff MCreal MCreal smoothOrder
        (fun t : ℝ => t₀ + (t₁ - t₀) * Real.smoothTransition (3 * t - 1)) := by
      rw [contMDiff_iff_contDiff]
      exact contDiff_const.add (contDiff_const.mul (Real.smoothTransition.contDiff.comp
        (contDiff_const.mul contDiff_id |>.sub contDiff_const)))
    intro t
    exact hγsm.contMDiffAt.comp t hpsi.contMDiffAt
  have hC_sm : ContMDiff MCreal (MC n) smoothOrder Crad := by
    have hpoly : ContMDiff MCreal (MC n) smoothOrder
        (fun t : ℝ => (s₁ * (1 - Real.smoothTransition (3 * t - 2))) • u') := by
      rw [contMDiff_iff_contDiff]
      exact (contDiff_const.mul (contDiff_const.sub (Real.smoothTransition.contDiff.comp
        (contDiff_const.mul contDiff_id |>.sub contDiff_const)))).smul contDiff_const
    have hsymm : ∀ t : ℝ, ContMDiffAt (MC n) (MC n) smoothOrder (⇑c'.symm)
        ((s₁ * (1 - Real.smoothTransition (3 * t - 2))) • u') := by
      intro t
      refine hc'symm.contMDiffAt ?_
      refine c'.open_target.mem_nhds (hε'tgt ?_)
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hu', mul_one, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hs₁0 (by linarith [Real.smoothTransition.le_one (3 * t - 2)]))]
      have h1 : s₁ * (1 - Real.smoothTransition (3 * t - 2)) ≤ s₁ :=
        mul_le_of_le_one_right hs₁0 (by linarith [Real.smoothTransition.nonneg (3 * t - 2)])
      linarith [h1, hs₁ε']
    intro t
    exact (hsymm t).comp t hpoly.contMDiffAt
  -- junction facts
  have hA_one_third : Arad (1/3) = γ t₀ := by
    change c.symm ((s₀ * Real.smoothTransition (3 * (1/3:ℝ))) • v) = γ t₀
    rw [show 3 * (1/3:ℝ) = 1 from by norm_num, Real.smoothTransition.one, mul_one]
    exact hs₀eq
  have hB_one_third : Bmid (1/3) = γ t₀ := by
    change γ (t₀ + (t₁ - t₀) * Real.smoothTransition (3 * (1/3:ℝ) - 1)) = γ t₀
    rw [show 3 * (1/3:ℝ) - 1 = 0 from by norm_num, Real.smoothTransition.zero, mul_zero, add_zero]
  have hB_two_thirds : Bmid (2/3) = γ t₁ := by
    change γ (t₀ + (t₁ - t₀) * Real.smoothTransition (3 * (2/3:ℝ) - 1)) = γ t₁
    rw [show 3 * (2/3:ℝ) - 1 = 1 from by norm_num, Real.smoothTransition.one, mul_one]
    ring_nf
  have hC_two_thirds : Crad (2/3) = γ t₁ := by
    change c'.symm ((s₁ * (1 - Real.smoothTransition (3 * (2/3:ℝ) - 2))) • u') = γ t₁
    rw [show 3 * (2/3:ℝ) - 2 = 0 from by norm_num, Real.smoothTransition.zero, sub_zero, mul_one]
    exact hs₁eq
  have hA_const_right : ∀ t : ℝ, 1/3 ≤ t → Arad t = γ t₀ := by
    intro t ht
    have h1 : 1 ≤ 3 * t := by linarith
    change c.symm ((s₀ * Real.smoothTransition (3 * t)) • v) = γ t₀
    rw [Real.smoothTransition.one_of_one_le h1, mul_one]
    exact hs₀eq
  have hB_const_left : ∀ t : ℝ, t ≤ 1/3 → Bmid t = γ t₀ := by
    intro t ht
    have h1 : 3 * t - 1 ≤ 0 := by linarith
    change γ (t₀ + (t₁ - t₀) * Real.smoothTransition (3 * t - 1)) = γ t₀
    rw [Real.smoothTransition.zero_of_nonpos h1, mul_zero, add_zero]
  have hB_const_right : ∀ t : ℝ, 2/3 ≤ t → Bmid t = γ t₁ := by
    intro t ht
    have h1 : 1 ≤ 3 * t - 1 := by linarith
    change γ (t₀ + (t₁ - t₀) * Real.smoothTransition (3 * t - 1)) = γ t₁
    rw [Real.smoothTransition.one_of_one_le h1, mul_one]
    ring_nf
  have hC_const_left : ∀ t : ℝ, t ≤ 2/3 → Crad t = γ t₁ := by
    intro t ht
    have h1 : 3 * t - 2 ≤ 0 := by linarith
    change c'.symm ((s₁ * (1 - Real.smoothTransition (3 * t - 2))) • u') = γ t₁
    rw [Real.smoothTransition.zero_of_nonpos h1, sub_zero, mul_one]
    exact hs₁eq
  -- ## 5. the piece
  set P : ℝ → M := fun t =>
    if t ≤ 1/3 then Arad t else if t ≤ 2/3 then Bmid t else Crad t with hPdef
  have hP_rad : ∀ t : ℝ, t ≤ 1/3 → P t = Arad t := by
    intro t ht
    show (if t ≤ 1/3 then Arad t else if t ≤ 2/3 then Bmid t else Crad t) = Arad t
    rw [if_pos ht]
  have hP_mid : ∀ t : ℝ, t ≤ 2/3 → ¬ (t ≤ 1/3) → P t = Bmid t := by
    intro t ht h1
    show (if t ≤ 1/3 then Arad t else if t ≤ 2/3 then Bmid t else Crad t) = Bmid t
    rw [if_neg h1, if_pos ht]
  have hP_arr : ∀ t : ℝ, ¬ (t ≤ 2/3) → P t = Crad t := by
    intro t ht
    show (if t ≤ 1/3 then Arad t else if t ≤ 2/3 then Bmid t else Crad t) = Crad t
    rw [if_neg (fun h => ht (le_trans h (by norm_num))), if_neg ht]
  have hP_arr' : ∀ t : ℝ, 2/3 ≤ t → P t = Crad t := by
    intro t ht
    rcases lt_or_eq_of_le ht with h | h
    · exact hP_arr t (not_le.mpr h)
    · rw [← h, hP_mid (2/3) le_rfl (by norm_num), hB_two_thirds, ← hC_two_thirds]
  have hP_const_left : ∀ t : ℝ, t ≤ 0 → P t = z := by
    intro t ht
    have h1 : 3 * t ≤ 0 := by linarith
    rw [hP_rad t (by linarith)]
    change c.symm ((s₀ * Real.smoothTransition (3 * t)) • v) = z
    rw [Real.smoothTransition.zero_of_nonpos h1, mul_zero, zero_smul, hc0]
  have hP_const_right : ∀ t : ℝ, 1 ≤ t → P t = z' := by
    intro t ht
    have h1 : 1 ≤ 3 * t - 2 := by linarith
    rw [hP_arr t (by linarith)]
    change c'.symm ((s₁ * (1 - Real.smoothTransition (3 * t - 2))) • u') = z'
    rw [Real.smoothTransition.one_of_one_le h1, sub_self, mul_zero, zero_smul, hc'0]
  have hPsm : ContMDiff MCreal (MC n) smoothOrder P := by
    intro t
    rcases lt_trichotomy t (1/3:ℝ) with ht | ht | ht
    · refine hA_sm.contMDiffAt.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
      exact hP_rad s (le_of_lt hs)
    · subst ht
      have hev : P =ᶠ[𝓝 (1/3:ℝ)] (fun s => if s ≤ 1/3 then Arad s else Bmid s) := by
        have hmem : Set.Iio (2/3:ℝ) ∈ 𝓝 (1/3:ℝ) := isOpen_Iio.mem_nhds (by norm_num)
        refine Filter.eventually_of_mem hmem ?_
        intro s hs
        have hs2 : s < 2/3 := hs
        rw [hPdef]
        by_cases hs' : s ≤ 1/3
        · simp only [if_pos hs', if_pos hs']
        · simp only [if_neg hs', if_neg hs', if_pos (le_of_lt hs2)]
      exact (Work.Noncompact.ProperLine.contMDiffAt_junction (A := Arad) (B := Bmid)
        (τ := (1/3:ℝ)) (p := γ t₀) hA_sm hB_sm
        hA_const_right hB_const_left).congr_of_eventuallyEq hev
    · rcases lt_trichotomy t (2/3:ℝ) with ht2 | ht2 | ht2
      · refine hB_sm.contMDiffAt.congr_of_eventuallyEq ?_
        have hmem : Set.Ioo (1/3:ℝ) (2/3:ℝ) ∈ 𝓝 t := isOpen_Ioo.mem_nhds ⟨ht, ht2⟩
        filter_upwards [hmem] with s hs
        exact hP_mid s (le_of_lt hs.2) (not_le.mpr hs.1)
      · subst ht2
        have hev : P =ᶠ[𝓝 (2/3:ℝ)] (fun s => if s ≤ 2/3 then Bmid s else Crad s) := by
          have hmem : Set.Ioo (1/3:ℝ) 1 ∈ 𝓝 (2/3:ℝ) := isOpen_Ioo.mem_nhds (by norm_num)
          refine Filter.eventually_of_mem hmem ?_
          intro s hs
          have hs1' : ¬ (s ≤ 1/3) := not_le.mpr hs.1
          rw [hPdef]
          by_cases hs' : s ≤ 2/3
          · simp only [if_neg hs1', if_pos hs']
          · simp only [if_neg hs1', if_neg hs']
        exact (Work.Noncompact.ProperLine.contMDiffAt_junction (A := Bmid) (B := Crad)
          (τ := (2/3:ℝ)) (p := γ t₁) hB_sm hC_sm
          hB_const_right hC_const_left).congr_of_eventuallyEq hev
      · refine hC_sm.contMDiffAt.congr_of_eventuallyEq ?_
        have hmem : Set.Ioi (2/3:ℝ) ∈ 𝓝 t := isOpen_Ioi.mem_nhds ht2
        filter_upwards [hmem] with s hs
        exact hP_arr s (not_le.mpr (show (2/3:ℝ) < s from hs))
  -- ## 6. the four properties
  have hA_mem : ∀ t : ℝ, Arad t ∈ A := by
    intro t
    have h1 : 0 ≤ s₀ * Real.smoothTransition (3 * t) :=
      mul_nonneg hs₀0 (Real.smoothTransition.nonneg _)
    have h2 : s₀ * Real.smoothTransition (3 * t) ≤ ε :=
      le_trans (mul_le_of_le_one_right hs₀0 (Real.smoothTransition.le_one (3 * t))) hs₀ε
    rw [hAdef]
    exact ⟨(s₀ * Real.smoothTransition (3 * t)) • v,
      ⟨s₀ * Real.smoothTransition (3 * t), h1, h2, rfl⟩, rfl⟩
  have hC_mem : ∀ t : ℝ, Crad t ∈ C := by
    intro t
    have h0 : 0 ≤ 1 - Real.smoothTransition (3 * t - 2) := by
      linarith [Real.smoothTransition.le_one (3 * t - 2)]
    have h1 : 0 ≤ s₁ * (1 - Real.smoothTransition (3 * t - 2)) := mul_nonneg hs₁0 h0
    have h3 : 1 - Real.smoothTransition (3 * t - 2) ≤ 1 := by
      linarith [Real.smoothTransition.nonneg (3 * t - 2)]
    have h2 : s₁ * (1 - Real.smoothTransition (3 * t - 2)) ≤ ε' :=
      le_trans (mul_le_of_le_one_right hs₁0 h3) hs₁ε'
    rw [hCdef]
    exact ⟨(s₁ * (1 - Real.smoothTransition (3 * t - 2))) • u',
      ⟨s₁ * (1 - Real.smoothTransition (3 * t - 2)), h1, h2, rfl⟩, rfl⟩
  have hB_mem : ∀ t : ℝ, Bmid t ∈ γ '' Set.Icc (0:ℝ) 1 := by
    intro t
    exact ⟨_, harg_mem t, rfl⟩
  have hB_A_eq : ∀ t : ℝ, Bmid t ∈ A → Bmid t = γ t₀ := by
    intro t ht
    have hle := ht₀max _ (harg_mem t) ht
    have hz : Real.smoothTransition (3 * t - 1) = 0 := by
      have h2 : 0 ≤ Real.smoothTransition (3 * t - 1) := Real.smoothTransition.nonneg _
      nlinarith [ht₀t₁]
    change γ (t₀ + (t₁ - t₀) * Real.smoothTransition (3 * t - 1)) = γ t₀
    rw [hz, mul_zero, add_zero]
  have hB_C_eq : ∀ t : ℝ, Bmid t ∈ C → Bmid t = γ t₁ := by
    intro t ht
    have hle : t₀ + (t₁ - t₀) * Real.smoothTransition (3 * t - 1) ≤ t₁ := by
      have h1 : (t₁ - t₀) * Real.smoothTransition (3 * t - 1) ≤ t₁ - t₀ :=
        mul_le_of_le_one_right (sub_nonneg.mpr ht₀t₁.le) (Real.smoothTransition.le_one _)
      calc t₀ + (t₁ - t₀) * Real.smoothTransition (3 * t - 1)
          ≤ t₀ + (t₁ - t₀) := add_le_add_right h1 t₀
        _ = t₁ := by ring
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact absurd ht (ht₁min _ ⟨harg_ge t, (harg_mem t).2⟩ hlt)
    · change γ (t₀ + (t₁ - t₀) * Real.smoothTransition (3 * t - 1)) = γ t₁
      rw [heq]
  -- the middle curve meets `A` resp. `C` only at the junctions
  have hB_A_jun : ∀ t : ℝ, Bmid t ∈ A → Bmid t = Bmid (1/3) := fun t ht => by
    rw [hB_A_eq t ht, hB_one_third]
  have hB_C_jun : ∀ t : ℝ, Bmid t ∈ C → Bmid t = Bmid (2/3) := fun t ht => by
    rw [hB_C_eq t ht, hB_two_thirds]
  -- the access and arrival curves are injective on their pieces
  have hA_inj : Set.InjOn Arad (Set.Icc (0:ℝ) (1/3)) := by
    intro s hs t ht hst
    have h1 : (s₀ * Real.smoothTransition (3 * s)) • v
        = (s₀ * Real.smoothTransition (3 * t)) • v := by
      apply c.symm.injOn
      · exact hδtgt (by
          rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hv, mul_one, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg hs₀0 (Real.smoothTransition.nonneg _))]
          linarith [Real.smoothTransition.le_one (3 * s), mul_le_of_le_one_right hs₀0
            (Real.smoothTransition.le_one (3 * s)), hs₀ε, hεδ, hδ])
      · exact hδtgt (by
          rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hv, mul_one, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg hs₀0 (Real.smoothTransition.nonneg _))]
          linarith [Real.smoothTransition.le_one (3 * t), mul_le_of_le_one_right hs₀0
            (Real.smoothTransition.le_one (3 * t)), hs₀ε, hεδ, hδ])
      · exact hst
    have h2 : s₀ * Real.smoothTransition (3 * s) = s₀ * Real.smoothTransition (3 * t) := by
      have h3 : (s₀ * Real.smoothTransition (3 * s) - s₀ * Real.smoothTransition (3 * t)) • v = 0 := by
        rw [sub_smul, h1, sub_self]
      rcases smul_eq_zero.mp h3 with h4 | h4
      · linarith
      · exact absurd h4 (by intro hv0; rw [hv0] at hv; norm_num at hv)
    have h5 : Real.smoothTransition (3 * s) = Real.smoothTransition (3 * t) :=
      mul_left_cancel₀ (ne_of_gt hs₀pos) h2
    have h6 : 3 * s = 3 * t :=
      Work.Noncompact.ProperLine.smoothTransition_injOn
        ⟨by linarith [hs.1], by linarith [hs.2]⟩
        ⟨by linarith [ht.1], by linarith [ht.2]⟩ h5
    linarith
  have hB_inj : Set.InjOn Bmid (Set.Icc (1/3:ℝ) (2/3)) := by
    intro s hs t ht hst
    have h1 : t₀ + (t₁ - t₀) * Real.smoothTransition (3 * s - 1)
        = t₀ + (t₁ - t₀) * Real.smoothTransition (3 * t - 1) := by
      apply hγinj (harg_mem s) (harg_mem t)
      exact hst
    have h2 : (t₁ - t₀) * Real.smoothTransition (3 * s - 1)
        = (t₁ - t₀) * Real.smoothTransition (3 * t - 1) := by linarith
    have h3 : Real.smoothTransition (3 * s - 1) = Real.smoothTransition (3 * t - 1) :=
      mul_left_cancel₀ (ne_of_gt (by linarith : 0 < t₁ - t₀)) h2
    have h4 : 3 * s - 1 = 3 * t - 1 :=
      Work.Noncompact.ProperLine.smoothTransition_injOn
        ⟨by linarith [hs.1], by linarith [hs.2]⟩
        ⟨by linarith [ht.1], by linarith [ht.2]⟩ h3
    linarith
  have hC_inj : Set.InjOn Crad (Set.Icc (2/3:ℝ) 1) := by
    intro s hs t ht hst
    have h1 : (s₁ * (1 - Real.smoothTransition (3 * s - 2))) • u'
        = (s₁ * (1 - Real.smoothTransition (3 * t - 2))) • u' := by
      apply c'.symm.injOn
      · exact hε'tgt (by
          have h0 : 0 ≤ 1 - Real.smoothTransition (3 * s - 2) := by
            linarith [Real.smoothTransition.le_one (3 * s - 2)]
          have h1 : 0 ≤ s₁ * (1 - Real.smoothTransition (3 * s - 2)) := mul_nonneg hs₁0 h0
          have h3 : 1 - Real.smoothTransition (3 * s - 2) ≤ 1 := by
            linarith [Real.smoothTransition.nonneg (3 * s - 2)]
          have h2 : s₁ * (1 - Real.smoothTransition (3 * s - 2)) ≤ s₁ :=
            mul_le_of_le_one_right hs₁0 h3
          rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hu', mul_one, Real.norm_eq_abs,
            abs_of_nonneg h1]
          exact le_trans h2 hs₁ε')
      · exact hε'tgt (by
          have h0 : 0 ≤ 1 - Real.smoothTransition (3 * t - 2) := by
            linarith [Real.smoothTransition.le_one (3 * t - 2)]
          have h1 : 0 ≤ s₁ * (1 - Real.smoothTransition (3 * t - 2)) := mul_nonneg hs₁0 h0
          have h3 : 1 - Real.smoothTransition (3 * t - 2) ≤ 1 := by
            linarith [Real.smoothTransition.nonneg (3 * t - 2)]
          have h2 : s₁ * (1 - Real.smoothTransition (3 * t - 2)) ≤ s₁ :=
            mul_le_of_le_one_right hs₁0 h3
          rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hu', mul_one, Real.norm_eq_abs,
            abs_of_nonneg h1]
          exact le_trans h2 hs₁ε')
      · exact hst
    have h2 : s₁ * (1 - Real.smoothTransition (3 * s - 2))
        = s₁ * (1 - Real.smoothTransition (3 * t - 2)) := by
      have h3 : (s₁ * (1 - Real.smoothTransition (3 * s - 2))
          - s₁ * (1 - Real.smoothTransition (3 * t - 2))) • u' = 0 := by
        rw [sub_smul, h1, sub_self]
      rcases smul_eq_zero.mp h3 with h4 | h4
      · linarith
      · exact absurd h4 (by intro hu0; rw [hu0] at hu'; norm_num at hu')
    have h5 : 1 - Real.smoothTransition (3 * s - 2) = 1 - Real.smoothTransition (3 * t - 2) :=
      mul_left_cancel₀ (ne_of_gt hs₁pos) h2
    have h6 : Real.smoothTransition (3 * s - 2) = Real.smoothTransition (3 * t - 2) := by linarith
    have h7 : 3 * s - 2 = 3 * t - 2 :=
      Work.Noncompact.ProperLine.smoothTransition_injOn
        ⟨by linarith [hs.1], by linarith [hs.2]⟩
        ⟨by linarith [ht.1], by linarith [ht.2]⟩ h6
    linarith
  refine ⟨P, hPsm, hP_const_left, hP_const_right, ?_, ?_, ?_, ?_⟩
  · -- injectivity
    have key : ∀ a b : ℝ, a ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 → a < b → P a = P b → False := by
      intro a b ha hb hab hab_eq
      rcases le_or_gt b (1/3) with hb1 | hb1
      · -- both in the access radius
        have hab1 : a ≤ 1/3 := le_trans hab.le hb1
        have h1 : Arad a = Arad b := by
          rw [hP_rad a hab1, hP_rad b hb1] at hab_eq
          exact hab_eq
        exact absurd (hA_inj ⟨ha.1, hab1⟩ ⟨hb.1, hb1⟩ h1) hab.ne
      · rcases le_or_gt a (1/3) with ha1 | ha1
        · rcases le_or_gt b (2/3) with hb2 | hb2
          · -- access / middle
            have h1 : Arad a = Bmid b := by
              rw [hP_rad a ha1, hP_mid b hb2 (not_le.mpr hb1)] at hab_eq
              exact hab_eq
            have h2 : Bmid b ∈ A := h1 ▸ hA_mem a
            have h3 : Bmid b = Bmid (1/3) := hB_A_jun b h2
            have h4 : b = 1/3 := hB_inj ⟨le_of_lt hb1, hb2⟩ ⟨by norm_num, by norm_num⟩ h3
            have h5 : Arad a = Arad (1/3) := by rw [h1, h4, hB_one_third, hA_one_third]
            have h6 : a = 1/3 := hA_inj ⟨ha.1, ha1⟩ ⟨by norm_num, by norm_num⟩ h5
            exact hab.ne (by linarith)
          · -- access / arrival: `A ∩ C = ∅`
            have h2 : P b ∈ C := by rw [hP_arr b (not_le.mpr hb2)]; exact hC_mem b
            have h3 : P a ∈ A := by rw [hP_rad a ha1]; exact hA_mem a
            have h4 : P a ∈ C := by rw [hab_eq]; exact h2
            exact Set.disjoint_left.mp hdisj (hA_sub h3) (hC_sub h4)
        · rcases le_or_gt b (2/3) with hb2 | hb2
          · -- both in the middle
            have ha2 : a ≤ 2/3 := le_trans hab.le hb2
            have h1 : Bmid a = Bmid b := by
              rw [hP_mid a ha2 (not_le.mpr ha1), hP_mid b hb2 (not_le.mpr hb1)] at hab_eq
              exact hab_eq
            exact absurd (hB_inj ⟨le_of_lt ha1, ha2⟩ ⟨le_of_lt hb1, hb2⟩ h1) hab.ne
          · rcases le_or_gt a (2/3) with ha2 | ha2
            · -- middle / arrival
              have h2 : Bmid a ∈ C := by
                have h2' : P a ∈ C := by rw [hab_eq, hP_arr b (not_le.mpr hb2)]; exact hC_mem b
                rwa [hP_mid a ha2 (not_le.mpr ha1)] at h2'
              have h5 : Crad b = Crad (2/3) :=
                calc Crad b = P b := (hP_arr b (not_le.mpr hb2)).symm
                  _ = P a := hab_eq.symm
                  _ = Bmid a := hP_mid a ha2 (not_le.mpr ha1)
                  _ = γ t₁ := hB_C_eq a h2
                  _ = Crad (2/3) := hC_two_thirds.symm
              have h6 : b = 2/3 := hC_inj ⟨le_of_lt hb2, hb.2⟩ ⟨by norm_num, by norm_num⟩ h5
              have h7 : a = 2/3 := hB_inj ⟨le_of_lt ha1, ha2⟩ ⟨by norm_num, by norm_num⟩
                (Eq.trans (hB_C_eq a h2) hB_two_thirds.symm)
              exact hab.ne (by linarith)
            · -- both in the arrival radius
              have h1 : Crad a = Crad b := by
                rw [hP_arr a (not_le.mpr ha2), hP_arr b (not_le.mpr hb2)] at hab_eq
                exact hab_eq
              exact absurd (hC_inj ⟨le_of_lt ha2, ha.2⟩ ⟨le_of_lt hb2, hb.2⟩ h1) hab.ne
    intro s hs t ht hst
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key s t hs ht hlt hst
    · exact key t s ht hs hlt hst.symm
  · -- range
    intro t ht
    rcases le_or_gt t (1/3) with h1 | h1
    · rw [hP_rad t h1]
      exact Or.inr (hA_sub (hA_mem t))
    · rcases le_or_gt t (2/3) with h2 | h2
      · rw [hP_mid t h2 (not_le.mpr h1)]
        exact Or.inl (hγW _ (harg_mem t)).1
      · rw [hP_arr t (not_le.mpr h2)]
        exact Or.inl (hε'X (hC_sub (hC_mem t)))
  · -- the obstacle
    rintro x ⟨⟨t, ht, rfl⟩, hxO⟩
    rcases le_or_gt t (1/3) with h1 | h1
    · have hxA : P t ∈ A := by rw [hP_rad t h1]; exact hA_mem t
      have h2 := nc_seg_avoids_germ (n := n) (M := M) hcsrc hcz hδtgt hw hv hvw hGerm
        (s := ε) hε.le (by linarith [hεδ, hδ])
      exact h2 ⟨hxO, by rw [← hAdef]; exact hxA⟩
    · rcases le_or_gt t (2/3) with h2 | h2
      · exfalso
        rw [hP_mid t h2 (not_le.mpr h1)] at hxO
        exact (fun h => Set.disjoint_left.mp hOX h (hγW _ (harg_mem t)).1) hxO
      · exfalso
        rw [hP_arr t (not_le.mpr h2)] at hxO
        exact (fun h => Set.disjoint_left.mp hOX h (hε'X (hC_sub (hC_mem t)))) hxO
  · -- the germ
    have hγim_closed : IsClosed (γ '' Set.Icc (0:ℝ) 1) :=
      (isCompact_Icc.image hγsm.continuous).isClosed
    obtain ⟨ρ₁, hρ₁pos, hρ₁sub⟩ := nc_chartBall_avoids (n := n) (M := M) hc'src hc'z
      hAcompact.isClosed (fun h => hz'far (hA_sub h))
    obtain ⟨ρ₂, hρ₂pos, hρ₂sub⟩ := nc_chartBall_avoids (n := n) (M := M) hc'src hc'z
      hγim_closed (fun h => by
        obtain ⟨u, hu, hux⟩ := h
        exact (hγW u ⟨hu.1, hu.2⟩).2 (Set.mem_singleton_iff.mpr hux))
    have hρpos : 0 < min s₁ (min ρ₁ ρ₂) := lt_min hs₁pos (lt_min hρ₁pos hρ₂pos)
    have hρle : min s₁ (min ρ₁ ρ₂) ≤ ε' := le_trans (min_le_left _ _) hs₁ε'
    have hb1 : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (min s₁ (min ρ₁ ρ₂))
        ⊆ Metric.ball 0 ρ₁ :=
      Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_left _ _))
    have hb2 : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (min s₁ (min ρ₁ ρ₂))
        ⊆ Metric.ball 0 ρ₂ :=
      Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_right _ _))
    refine ⟨min s₁ (min ρ₁ ρ₂), hρpos, hρle, ?_⟩
    ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hxball⟩
      rcases le_or_gt t (1/3) with h1 | h1
      · exfalso
        have hxA : P t ∈ A := by rw [hP_rad t h1]; exact hA_mem t
        have hx1 : P t ∈ c'.symm '' Metric.ball 0 (min s₁ (min ρ₁ ρ₂)) := hxball
        obtain ⟨y, hy, hyx⟩ := hx1
        have hx2 : P t ∈ c'.symm '' Metric.ball 0 ρ₁ := ⟨y, hb1 hy, hyx⟩
        exact hρ₁sub hx2 hxA
      · rcases le_or_gt t (2/3) with h2 | h2
        · exfalso
          have hxA : P t ∈ γ '' Set.Icc (0:ℝ) 1 := by
            rw [hP_mid t h2 (not_le.mpr h1)]; exact hB_mem t
          have hx1 : P t ∈ c'.symm '' Metric.ball 0 (min s₁ (min ρ₁ ρ₂)) := hxball
          obtain ⟨y, hy, hyx⟩ := hx1
          have hx2 : P t ∈ c'.symm '' Metric.ball 0 ρ₂ := ⟨y, hb2 hy, hyx⟩
          exact hρ₂sub hx2 hxA
        · have hpt : P t = c'.symm ((s₁ * (1 - Real.smoothTransition (3 * t - 2))) • u') := by
            rw [hP_arr t (not_le.mpr h2)]
          obtain ⟨y, hy, hyx⟩ := hxball
          have hyρ : ‖y‖ < min s₁ (min ρ₁ ρ₂) := by simpa using hy
          have htgt_y : y ∈ c'.target := hε'tgt (by
            rw [Metric.mem_closedBall, dist_zero_right]
            exact le_of_lt (lt_of_lt_of_le hyρ hρle))
          have h0 : 0 ≤ 1 - Real.smoothTransition (3 * t - 2) := by
            linarith [Real.smoothTransition.le_one (3 * t - 2)]
          have h1 : 0 ≤ s₁ * (1 - Real.smoothTransition (3 * t - 2)) := mul_nonneg hs₁0 h0
          have h3 : 1 - Real.smoothTransition (3 * t - 2) ≤ 1 := by
            linarith [Real.smoothTransition.nonneg (3 * t - 2)]
          have h2' : s₁ * (1 - Real.smoothTransition (3 * t - 2)) ≤ s₁ :=
            mul_le_of_le_one_right hs₁0 h3
          have htgt_r : (s₁ * (1 - Real.smoothTransition (3 * t - 2))) • u' ∈ c'.target :=
            hε'tgt (by
              rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hu', mul_one,
                Real.norm_eq_abs, abs_of_nonneg h1]
              exact le_trans h2' hs₁ε')
          have hyeq : y = (s₁ * (1 - Real.smoothTransition (3 * t - 2))) • u' := by
            refine c'.symm.injOn htgt_y htgt_r ?_
            rw [hyx, hpt]
          refine ⟨(s₁ * (1 - Real.smoothTransition (3 * t - 2))) • u',
            ⟨s₁ * (1 - Real.smoothTransition (3 * t - 2)), h1, ?_, rfl⟩, hpt.symm⟩
          rw [hyeq, norm_smul, hu', mul_one, Real.norm_eq_abs, abs_of_nonneg h1] at hyρ
          exact hyρ
    · rintro ⟨y, ⟨s, hy0, hyρ, rfl⟩, rfl⟩
      have hs₁ne : s₁ ≠ 0 := ne_of_gt hs₁pos
      have hle : s ≤ s₁ := le_of_lt (lt_of_lt_of_le hyρ (min_le_left _ _))
      have hval : 1 - s / s₁ ∈ Set.Icc (0:ℝ) 1 := by
        constructor
        · rw [sub_nonneg, div_le_one hs₁pos]; exact hle
        · exact sub_le_self 1 (div_nonneg hy0 (le_of_lt hs₁pos))
      obtain ⟨ζ, hζ, hζeq⟩ := nc_smoothTransition_surjOn hval
      have harg : 3 * ((ζ + 2) / 3) - 2 = ζ := by ring
      have htmem : (ζ + 2) / 3 ∈ Set.Icc (0:ℝ) 1 := by
        constructor
        · exact div_nonneg (by linarith [hζ.1]) (by norm_num)
        · have h3 : (0:ℝ) < 3 := by norm_num
          have h4 : ζ + 2 ≤ 3 := by linarith [hζ.2]
          exact (div_le_one h3).mpr h4
      have ht23 : (2:ℝ)/3 ≤ (ζ + 2) / 3 :=
        div_le_div_of_nonneg_right (by linarith [hζ.1] : (2:ℝ) ≤ ζ + 2) (by norm_num)
      refine ⟨⟨(ζ + 2) / 3, htmem, ?_⟩, ?_⟩
      · have hψ : Real.smoothTransition (3 * ((ζ + 2) / 3) - 2) = 1 - s / s₁ := by
          rw [harg]; exact hζeq
        rw [hP_arr' _ ht23]
        change c'.symm ((s₁ * (1 - Real.smoothTransition (3 * ((ζ + 2) / 3) - 2))) • u')
          = c'.symm (s • u')
        rw [hψ]
        congr 1
        congr 1
        rw [sub_sub_cancel, mul_comm, div_mul_cancel₀ s hs₁ne]
      · refine ⟨s • u', ?_, rfl⟩
        rw [Metric.mem_ball, dist_zero_right, norm_smul, hu', mul_one, Real.norm_eq_abs,
          abs_of_nonneg hy0]
        exact hyρ

end Work.Noncompact.CompressionTube
