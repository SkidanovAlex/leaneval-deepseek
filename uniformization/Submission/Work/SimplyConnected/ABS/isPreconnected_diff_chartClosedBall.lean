import Mathlib
import Submission.Work.SimplyConnected.ABS.GreenSetupReg
import Submission.Work.SimplyConnected.ABS.isPreconnected_diff_singleton_of_isOpen

/-!
# Deleting a closed chart disc from a preconnected open set

For an open preconnected set `Ω` of a complex one-manifold `X` and a closed chart disc
`chartClosedBall c a s ⊆ Ω`, the complement `Ω \ chartClosedBall c a s` is preconnected.

The mathematics is the classical fact that a closed disc does not disconnect a connected
surface.  The proof splits into three cases.

* `s < 0`: the closed ball `Metric.closedBall a s` is empty, so there is nothing to remove.
* `s = 0`: the chart disc is a single point `c.symm a ∈ Ω`, and deleting one point of an open
  preconnected set of a surface leaves it preconnected
  (`isPreconnected_diff_singleton_of_isOpen`).
* `s > 0`: the chart sphere being compact and `Ω` open, there is `ρ > 0` such that the whole
  larger chart disc `chartClosedBall c a (s + ρ)` is still contained in `Ω`
  (`exists_chartShell_aux`).  Then `Ω \ chartClosedBall c a s` is the union of the preconnected
  annulus `chartClosedBall c a (s + ρ) \ chartClosedBall c a s` and of the parts of `Ω \ K`
  reached by paths from outside the large disc to its centre, the two meeting at the point
  where such a path first enters the large disc.

The auxiliary lemmas on path connected neighbourhoods, on the chart annulus and on first
entrance times are the same tools used by the sibling file
`Work.SimplyConnected.ABS.isPreconnected_sdiff_chartClosedBall`.
-/

noncomputable section

open Set Metric Filter

open scoped Topology

namespace Work.SimplyConnected.ABS

/-! ## Path connected neighbourhoods from a chart -/

/-- Every point of a charted space over `ℂ` has arbitrarily small path connected
neighbourhoods: the inverse image of a small Euclidean ball under a chart at the point. -/
theorem pathConnected_nhds_aux {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (x : X) {u : Set X} (hu : u ∈ 𝓝 x) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ u ∧ IsPathConnected V := by
  obtain ⟨u₀, hu₀sub, hu₀open, hxu₀⟩ := _root_.mem_nhds_iff.mp hu
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc
  have hxsrc : x ∈ c.source := mem_chart_source ℂ x
  have hct : c x ∈ c.target := mem_chart_target ℂ x
  have hopen : IsOpen (c '' (c.source ∩ u₀)) := c.isOpen_image_source_inter hu₀open
  have hxmem : c x ∈ c '' (c.source ∩ u₀) := ⟨x, ⟨hxsrc, hxu₀⟩, rfl⟩
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp (hopen.inter c.open_target) (c x) ⟨hxmem, hct⟩
  have hbt : Metric.ball (c x) ε ⊆ c.target := fun z hz => (hball hz).2
  refine ⟨c.symm '' Metric.ball (c x) ε, ?_, ?_, ?_, ?_⟩
  · exact c.isOpen_image_symm_of_subset_target Metric.isOpen_ball hbt
  · exact ⟨c x, mem_ball_self hε, c.left_inv hxsrc⟩
  · rintro y ⟨w, hw, rfl⟩
    obtain ⟨z, ⟨hzsrc, hzu⟩, hzw⟩ := (hball hw).1
    rw [← hzw, c.left_inv hzsrc]
    exact hu₀sub hzu
  · obtain ⟨b, hbmem, hbjoin⟩ := (convex_ball (c x) ε).isPathConnected ⟨c x, mem_ball_self hε⟩
    refine ⟨c.symm b, ⟨b, hbmem, rfl⟩, fun y hy => ?_⟩
    obtain ⟨w, hw, rfl⟩ := hy
    exact JoinedIn.map_continuousOn (hbjoin hw) (c.continuousOn_symm.mono hbt)

/-- A charted space over `ℂ` is locally path connected. -/
theorem locallyPathConnectedSpace_aux (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] :
    LocallyPathConnectedSpace X := by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro x u hu hxu
  obtain ⟨V, hVopen, hxV, hVsub, hVpc⟩ := pathConnected_nhds_aux x (hu.mem_nhds hxu)
  refine Filter.mem_of_superset (hVopen.mem_nhds hxV) ?_
  intro y hy
  exact (hVpc.joinedIn x hxV y hy).mono hVsub

/-! ## The chart annulus -/

/-- The half-open closed annulus `{z | s < ‖z - a‖ ≤ ρ}` is preconnected: it is the image of
the preconnected set `(s, ρ] × S¹` under `(t, u) ↦ a + t • u`. -/
theorem preconnected_halfOpenAnnulus_aux (a : ℂ) {s ρ : ℝ} (hs : 0 < s) :
    IsPreconnected {z : ℂ | s < ‖z - a‖ ∧ ‖z - a‖ ≤ ρ} := by
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  have himg : (fun p : ℝ × ℂ => a + p.1 • p.2) '' (Set.Ioc s ρ ×ˢ Metric.sphere (0 : ℂ) 1)
      = {z : ℂ | s < ‖z - a‖ ∧ ‖z - a‖ ≤ ρ} := by
    ext z
    constructor
    · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
      have hp2' : ‖p.2‖ = 1 := mem_sphere_zero_iff_norm.mp hp2
      have hnorm : ‖(a + p.1 • p.2) - a‖ = p.1 := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hp2', mul_one,
          abs_of_pos (lt_trans hs hp1.1)]
      exact ⟨by rw [hnorm]; exact hp1.1, by rw [hnorm]; exact hp1.2⟩
    · rintro ⟨h1, h2⟩
      have hne : z - a ≠ 0 := by
        intro h
        rw [h, norm_zero] at h1
        linarith
      have hpos : 0 < ‖z - a‖ := norm_pos_iff.mpr hne
      refine ⟨(‖z - a‖, (‖z - a‖)⁻¹ • (z - a)), ⟨⟨h1, h2⟩, ?_⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos,
          inv_mul_cancel₀ hpos.ne']
      · change a + ‖z - a‖ • (‖z - a‖⁻¹ • (z - a)) = z
        rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul, add_sub_cancel]
  rw [← himg]
  exact IsPreconnected.image (isPreconnected_Ioc.prod (isPreconnected_sphere hrank 0 1))
    (fun p : ℝ × ℂ => a + p.1 • p.2) (by fun_prop)

/-- The annulus of a complex chart cut out by two concentric chart discs is preconnected. -/
theorem preconnected_chartAnnulus_aux {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {s ρ : ℝ} (hs : 0 < s)
    (hρsub : Metric.closedBall a ρ ⊆ c.target) :
    IsPreconnected (Submission.chartClosedBall c a ρ \ Submission.chartClosedBall c a s) := by
  have hBsub : {z : ℂ | s < ‖z - a‖ ∧ ‖z - a‖ ≤ ρ} ⊆ c.target := fun z hz =>
    hρsub (Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hz.2))
  have hset : Submission.chartClosedBall c a ρ \ Submission.chartClosedBall c a s
      = c.symm '' {z : ℂ | s < ‖z - a‖ ∧ ‖z - a‖ ≤ ρ} := by
    ext x
    constructor
    · rintro ⟨hxρ, hxs⟩
      rw [Submission.mem_chartClosedBall] at hxρ
      have hcx : c x ∉ Metric.closedBall a s := by
        intro hmem
        exact hxs (by rw [Submission.mem_chartClosedBall]; exact ⟨hxρ.1, hmem⟩)
      have hxρ2 : ‖c x - a‖ ≤ ρ := by
        have h := hxρ.2
        rwa [Metric.mem_closedBall, dist_eq_norm] at h
      refine ⟨c x, ⟨?_, hxρ2⟩, c.left_inv hxρ.1⟩
      rw [Metric.mem_closedBall, dist_eq_norm] at hcx
      exact not_le.mp hcx
    · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
      have hwt : w ∈ c.target := hBsub ⟨h1, h2⟩
      constructor
      · rw [Submission.mem_chartClosedBall]
        exact ⟨c.map_target hwt,
          by rw [c.right_inv hwt, Metric.mem_closedBall, dist_eq_norm]; exact h2⟩
      · intro hmem
        rw [Submission.mem_chartClosedBall] at hmem
        have hws : ‖w - a‖ ≤ s := by
          have := hmem.2
          rw [c.right_inv hwt] at this
          rwa [Metric.mem_closedBall, dist_eq_norm] at this
        linarith
  rw [hset]
  exact (preconnected_halfOpenAnnulus_aux a hs).image c.symm (c.continuousOn_symm.mono hBsub)

/-! ## The first entrance time of a closed set -/

/-- Let `f : ℝ → X` be continuous, `K ⊆ X` closed, `f 0 ∉ K` and `f 1 ∈ K`.  Then there is
`t > 0` with `f t ∈ K`, `f t ∉ interior K` and `f u ∉ K` for all `0 ≤ u < t`. -/
theorem first_exit_aux {X : Type*} [TopologicalSpace X] {f : ℝ → X} (hf : Continuous f)
    {K : Set X} (hK : IsClosed K) (h0 : f 0 ∉ K) (h1 : f 1 ∈ K) :
    ∃ t : ℝ, 0 < t ∧ f t ∈ K ∧ f t ∉ interior K ∧ ∀ u, 0 ≤ u → u < t → f u ∉ K := by
  set S : Set ℝ := f ⁻¹' K ∩ Set.Icc 0 1 with hS
  have hSclosed : IsClosed S := (hK.preimage hf).inter isClosed_Icc
  have hSne : S.Nonempty := ⟨1, h1, by norm_num⟩
  have hSbd : BddBelow S := ⟨0, fun t ht => ht.2.1⟩
  have hmemS : sInf S ∈ S := hSclosed.csInf_mem hSne hSbd
  set t : ℝ := sInf S with ht
  have htmem : f t ∈ K := by rw [ht]; exact hmemS.1
  have ht0 : 0 ≤ t := by rw [ht]; exact hmemS.2.1
  have htle : t ≤ 1 := by rw [ht]; exact hmemS.2.2
  have htpos : 0 < t := by
    rcases lt_or_eq_of_le ht0 with h | h
    · exact h
    · exfalso
      rw [← h] at htmem
      exact h0 htmem
  refine ⟨t, htpos, htmem, ?_, ?_⟩
  · intro hint
    obtain ⟨ε, hε, hεK⟩ := Metric.mem_nhds_iff.mp
      (hf.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hint))
    set δ : ℝ := min (ε / 2) (t / 2) with hδ
    have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
    have hδle : δ ≤ ε / 2 := min_le_left _ _
    have hδle' : δ ≤ t / 2 := min_le_right _ _
    have hmem : t - δ ∈ Metric.ball t ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hsub : t - δ - t = -δ := by ring
      rw [hsub, abs_neg, abs_of_pos hδpos]
      linarith
    have huK : f (t - δ) ∈ K := interior_subset (hεK hmem)
    have huS : t - δ ∈ S := ⟨huK, by linarith, by linarith⟩
    have := csInf_le hSbd huS
    rw [← ht] at this
    linarith
  · intro u hu0 hut huK
    have huS : u ∈ S := ⟨huK, hu0, le_trans hut.le htle⟩
    have := csInf_le hSbd huS
    rw [← ht] at this
    linarith

/-! ## The shell lemma -/

/-- **Shell lemma.**  If the closed chart disc `chartClosedBall c a s` (with `0 ≤ s` and
`Metric.closedBall a s ⊆ c.target`) is contained in the open set `Ω`, then some whole larger
closed chart disc `chartClosedBall c a (s + ρ)` is still contained in `Ω`.

Concretely: there is `ρ > 0` such that `Metric.closedBall a (s + ρ) ⊆ c.target` and
`c.symm w ∈ Ω` for every `w` with `s ≤ dist w a ≤ s + ρ`. -/
theorem exists_chartShell_aux {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Ω : Set X} (hΩo : IsOpen Ω) {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {s : ℝ}
    (hsub : Metric.closedBall a s ⊆ c.target)
    (hKΩ : Submission.chartClosedBall c a s ⊆ Ω) (hs : 0 ≤ s) :
    ∃ ρ > 0, (∀ w : ℂ, dist w a ≤ s + ρ → w ∈ c.target) ∧
      (∀ w : ℂ, s ≤ dist w a → dist w a ≤ s + ρ → c.symm w ∈ Ω) := by
  -- the chart image of `Ω` is open and contains the closed ball
  have hVopen : IsOpen (c '' (c.source ∩ Ω)) := c.isOpen_image_source_inter hΩo
  have hBV : Metric.closedBall a s ⊆ c '' (c.source ∩ Ω) := by
    intro w hw
    have hwt : w ∈ c.target := hsub hw
    refine ⟨c.symm w, ⟨c.map_target hwt, ?_⟩, c.right_inv hwt⟩
    have hmem : c.symm w ∈ Submission.chartClosedBall c a s := by
      rw [Submission.chartClosedBall_eq_image hsub]
      exact ⟨w, hw, rfl⟩
    exact hKΩ hmem
  obtain ⟨δ, hδpos, hδ⟩ :=
    (isCompact_closedBall a s).exists_cthickening_subset_open hVopen hBV
  -- every point of the thickened ball lies in the target
  have hthick : ∀ w : ℂ, dist w a ≤ s + δ → w ∈ Metric.cthickening δ (Metric.closedBall a s) := by
    intro w hw
    have hwna : ‖w - a‖ ≤ s + δ := by
      have h := hw; rwa [dist_eq_norm] at h
    rw [Metric.mem_cthickening_iff]
    rcases le_or_gt ‖w - a‖ s with hle | hlt
    · have hwB : w ∈ Metric.closedBall a s := by
        rw [Metric.mem_closedBall, dist_eq_norm]; exact hle
      refine le_trans (Metric.infEDist_le_edist_of_mem hwB) ?_
      rw [edist_self]; exact bot_le
    · set y : ℂ := a + (s / ‖w - a‖) • (w - a) with hy
      have hd : 0 < ‖w - a‖ := lt_of_le_of_lt hs hlt
      have hyball : y ∈ Metric.closedBall a s := by
        rw [Metric.mem_closedBall, dist_eq_norm, hy, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg (div_nonneg hs hd.le), div_mul_cancel₀ _ hd.ne']
      have hdist : dist w y ≤ δ := by
        have hsd : 0 ≤ 1 - s / ‖w - a‖ := by
          have h1 : s / ‖w - a‖ ≤ 1 := by rw [div_le_iff₀ hd]; linarith
          linarith
        have hkey : (s / ‖w - a‖) * ‖w - a‖ = s := div_mul_cancel₀ _ hd.ne'
        have hwnorm : ‖w - y‖ = ‖w - a‖ - s := by
          have hsub' : w - y = (1 - s / ‖w - a‖) • (w - a) := by
            rw [hy]; module
          rw [hsub', norm_smul, Real.norm_eq_abs, abs_of_nonneg hsd]
          rw [sub_mul, one_mul, hkey]
        rw [dist_eq_norm, hwnorm]
        linarith
      refine le_trans (Metric.infEDist_le_edist_of_mem hyball) ?_
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal hdist
  refine ⟨δ, hδpos, ?_, ?_⟩
  · -- points of the thickened closed ball are in the target
    intro w hw
    obtain ⟨x, hxmem2, hxw⟩ := hδ (hthick w hw)
    obtain ⟨hxsrc, -⟩ := hxmem2
    rw [← hxw]
    exact c.map_source hxsrc
  · -- and their chart preimages lie in `Ω`
    intro w h1 h2
    obtain ⟨x, hxmem2, hxw⟩ := hδ (hthick w h2)
    obtain ⟨hxsrc, hxΩ⟩ := hxmem2
    rw [← hxw, c.left_inv hxsrc]
    exact hxΩ

/-! ## A preconnectedness criterion with a hub -/

/-- If `A₀ ⊆ Z` is preconnected and every point of `Z` lies in a preconnected subset of `Z`
meeting `A₀`, then `Z` is preconnected. -/
theorem isPreconnected_of_hub {X : Type*} [TopologicalSpace X] {Z A₀ : Set X}
    (hA : A₀ ⊆ Z) (hAp : IsPreconnected A₀)
    (h : ∀ y ∈ Z, ∃ T : Set X, T ⊆ Z ∧ IsPreconnected T ∧ y ∈ T ∧ (T ∩ A₀).Nonempty) :
    IsPreconnected Z := by
  intro u v hu hv hZuv huneu hunev
  obtain ⟨x, hxZ, hxu⟩ := huneu
  obtain ⟨y, hyZ, hyv⟩ := hunev
  obtain ⟨Tx, hTxZ, hTxp, hxTx, wx, hwxTx, hwxA⟩ := h x hxZ
  obtain ⟨Ty, hTyZ, hTyp, hyTy, wy, hwyTy, hwyA⟩ := h y hyZ
  have h1 : IsPreconnected (Tx ∪ A₀) := hTxp.union wx hwxTx hwxA hAp
  have h2 : IsPreconnected (Tx ∪ A₀ ∪ Ty) :=
    h1.union wy (Or.inr hwyA) hwyTy hTyp
  have hTxAZ : Tx ∪ A₀ ⊆ Z := fun z hz => hz.elim (fun hz' => hTxZ hz') (fun hz' => hA hz')
  have hWZ : Tx ∪ A₀ ∪ Ty ⊆ Z := fun z hz => hz.elim (fun hz' => hTxAZ hz') (fun hz' => hTyZ hz')
  have hWuv : Tx ∪ A₀ ∪ Ty ⊆ u ∪ v := fun z hz => hZuv (hWZ hz)
  have hxW : x ∈ (Tx ∪ A₀ ∪ Ty) ∩ u := ⟨Or.inl (Or.inl hxTx), hxu⟩
  have hyW : y ∈ (Tx ∪ A₀ ∪ Ty) ∩ v := ⟨Or.inr hyTy, hyv⟩
  obtain ⟨w, hwW, hwu, hwv⟩ := h2 u v hu hv hWuv ⟨x, hxW⟩ ⟨y, hyW⟩
  exact ⟨w, hWZ hwW, hwu, hwv⟩

/-! ## Deleting a chart disc that has room inside `Ω` -/

/-- If the larger chart disc `chartClosedBall c a ρ` (`s < ρ`) is contained in the open
preconnected set `Ω`, then removing the smaller closed disc `chartClosedBall c a s` leaves `Ω`
preconnected. -/
theorem preconnected_sdiff_chartClosedBall_aux {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] {Ω : Set X} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ s : ℝ} (hs : 0 < s) (hsρ : s < ρ)
    (hρsub : Metric.closedBall a ρ ⊆ c.target)
    (hρΩ : Submission.chartClosedBall c a ρ ⊆ Ω) :
    IsPreconnected (Ω \ Submission.chartClosedBall c a s) := by
  haveI : LocallyPathConnectedSpace X := locallyPathConnectedSpace_aux X
  set Ks : Set X := Submission.chartClosedBall c a s with hKs
  set Kρ : Set X := Submission.chartClosedBall c a ρ with hKρ
  set A : Set X := Kρ \ Ks with hA
  have hKsKρ : Ks ⊆ Kρ := by
    rw [hKs, hKρ]
    exact fun y hy => ⟨hy.1, Metric.closedBall_subset_closedBall hsρ.le hy.2⟩
  have hAsub : A ⊆ Ω \ Ks := fun y hy => ⟨hρΩ hy.1, hy.2⟩
  have hAp : IsPreconnected A := preconnected_chartAnnulus_aux hs hρsub
  have hKρclosed : IsClosed Kρ := by
    rw [hKρ]; exact Submission.isClosed_chartClosedBall hρsub
  have hball_int : Submission.chartBall c a ρ ⊆ interior Kρ :=
    (Submission.chartBall_isOpen c a ρ).subset_interior_iff.mpr (by
      rw [hKρ]; exact Submission.chartBall_subset_chartClosedBall c a ρ)
  -- the centre of the discs lies in `Ω`
  have haρ : a ∈ Metric.closedBall a ρ := Metric.mem_closedBall_self (lt_trans hs hsρ).le
  have hcρ : c.symm a ∈ Kρ := by
    rw [hKρ, Submission.mem_chartClosedBall]
    exact ⟨c.map_target (hρsub haρ), by rw [c.right_inv (hρsub haρ)]; exact haρ⟩
  have hΩpc : IsPathConnected Ω :=
    (hΩo.isConnected_iff_isPathConnected).mp ⟨⟨c.symm a, hρΩ hcρ⟩, hΩc⟩
  refine isPreconnected_of_hub hAsub hAp ?_
  intro z hz
  by_cases hzA : z ∈ Kρ
  · -- points of the annulus itself
    exact ⟨A, hAsub, hAp, ⟨hzA, hz.2⟩, ⟨z, ⟨hzA, hz.2⟩, hzA, hz.2⟩⟩
  · -- points outside the large disc: walk from `z` to the centre of the disc
    have hjoin : JoinedIn Ω z (c.symm a) := hΩpc.joinedIn z hz.1 (c.symm a) (hρΩ hcρ)
    set γ : Path z (c.symm a) := hjoin.somePath with hγ
    have hγmem : ∀ t : unitInterval, γ t ∈ Ω := hjoin.somePath_mem
    have hfΩ : ∀ t : ℝ, γ.extend t ∈ Ω := by
      intro t
      rcases le_or_gt t 0 with ht | ht
      · rw [Path.extend_of_le_zero γ ht]; exact hz.1
      · rcases le_or_gt 1 t with ht1 | ht1
        · rw [Path.extend_of_one_le γ ht1]; exact hρΩ hcρ
        · rw [Path.extend_apply γ ⟨ht.le, ht1.le⟩]
          exact hγmem ⟨t, ⟨ht.le, ht1.le⟩⟩
    have hzKρ : γ.extend 0 ∉ Kρ := by rw [Path.extend_zero]; exact hzA
    have hcKρ : γ.extend 1 ∈ Kρ := by rw [Path.extend_one]; exact hcρ
    obtain ⟨t₁, ht₁pos, ht₁mem, ht₁notint, ht₁out⟩ :=
      first_exit_aux γ.continuous_extend hKρclosed hzKρ hcKρ
    -- the first entrance point of the path into the large disc lies in the annulus
    have hnorm : ‖c (γ.extend t₁) - a‖ = ρ := by
      have hle : ‖c (γ.extend t₁) - a‖ ≤ ρ := by
        have h : c (γ.extend t₁) ∈ Metric.closedBall a ρ := ht₁mem.2
        rwa [Metric.mem_closedBall, dist_eq_norm] at h
      have hge : ρ ≤ ‖c (γ.extend t₁) - a‖ := by
        by_contra hlt
        refine ht₁notint (hball_int ⟨ht₁mem.1, ?_⟩)
        simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm]
        exact not_le.mp hlt
      linarith
    have hpA : γ.extend t₁ ∈ A := by
      refine ⟨ht₁mem, ?_⟩
      intro hcon
      have hle : ‖c (γ.extend t₁) - a‖ ≤ s := by
        have h : c (γ.extend t₁) ∈ Metric.closedBall a s := hcon.2
        rwa [Metric.mem_closedBall, dist_eq_norm] at h
      linarith
    -- the part of the path before the first entrance lies in `Ω \ Ks`, and it meets `A`
    have hsub : γ.extend '' Set.Iic t₁ ⊆ Ω \ Ks := by
      rintro y ⟨u, hu, rfl⟩
      refine ⟨hfΩ u, ?_⟩
      intro hyKs
      have huKρ : γ.extend u ∈ Kρ := hKsKρ hyKs
      rcases le_or_gt 0 u with hu0 | hu0
      · by_cases hut : u < t₁
        · exact ht₁out u hu0 hut huKρ
        · have hue : u = t₁ := le_antisymm hu (not_lt.mp hut)
          exact hpA.2 (hue ▸ hyKs)
      · rw [Path.extend_of_le_zero γ hu0.le] at huKρ
        exact hzA huKρ
    exact ⟨γ.extend '' Set.Iic t₁, hsub,
      isPreconnected_Iic.image _ γ.continuous_extend.continuousOn,
      ⟨0, ht₁pos.le, γ.extend_zero⟩,
      ⟨γ.extend t₁, ⟨t₁, le_refl t₁, rfl⟩, hpA⟩⟩

/-! ## The main theorem -/

theorem isPreconnected_diff_chartClosedBall {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {s : ℝ}
    (hsub : Metric.closedBall a s ⊆ c.target)
    (hKΩ : Submission.chartClosedBall c a s ⊆ Ω) :
    IsPreconnected (Ω \ Submission.chartClosedBall c a s) := by
  rcases lt_trichotomy s 0 with hsneg | hszero | hspos
  · -- `s < 0`: the closed ball is empty
    have hKempty : Submission.chartClosedBall c a s = ∅ := by
      rw [Submission.chartClosedBall, Metric.closedBall_eq_empty.mpr hsneg]
      simp
    rw [hKempty, Set.sdiff_empty]
    exact hΩc
  · -- `s = 0`: the chart disc is a single point
    subst hszero
    have hKsing : Submission.chartClosedBall c a 0 = {c.symm a} := by
      rw [Submission.chartClosedBall_eq_image hsub]
      ext x
      simp only [Set.mem_image, Metric.mem_closedBall, Set.mem_singleton_iff]
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hw0 : dist w a = 0 := le_antisymm hw dist_nonneg
        rw [dist_eq_zero.mp hw0]
      · rintro rfl
        exact ⟨a, by simp, rfl⟩
    have hmemΩ : c.symm a ∈ Ω := hKΩ (by rw [hKsing]; exact rfl)
    rw [hKsing]
    exact isPreconnected_diff_singleton_of_isOpen hΩo hΩc hmemΩ
  · -- `s > 0`: cut out a slightly larger chart disc that still lies in `Ω`
    obtain ⟨ρ, hρpos, htarget, hshell⟩ := exists_chartShell_aux hΩo hsub hKΩ hspos.le
    have hsub' : Metric.closedBall a (s + ρ) ⊆ c.target := fun w hw =>
      htarget w (Metric.mem_closedBall.mp hw)
    have hKbig : Submission.chartClosedBall c a (s + ρ) ⊆ Ω := by
      rw [Submission.chartClosedBall_eq_image hsub']
      rintro x ⟨w, hw, rfl⟩
      have hw' : dist w a ≤ s + ρ := Metric.mem_closedBall.mp hw
      rcases le_or_gt (dist w a) s with h | h
      · refine hKΩ ?_
        rw [Submission.chartClosedBall_eq_image hsub]
        exact ⟨w, Metric.mem_closedBall.mpr h, rfl⟩
      · exact hshell w h.le hw'
    exact preconnected_sdiff_chartClosedBall_aux hΩo hΩc hspos (by linarith) hsub' hKbig

end Work.SimplyConnected.ABS
