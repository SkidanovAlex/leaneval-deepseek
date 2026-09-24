import Mathlib
import Submission.Work.SimplyConnected.ABS.GreenSetupReg
import Submission.Work.SimplyConnected.ABS.dirichletSphereEnvelope_facts

/-!
# Cutting a closed chart disc out of a preconnected open set

For a connected open set `Ω` of a complex one-manifold and a chart disc
`chartClosedBall c a ρ ⊆ Ω`, removing the smaller closed disc
`chartClosedBall c a s` (with `s < ρ`) leaves `Ω` preconnected.

The mathematics is the classical fact that a closed disc does not disconnect a connected
surface.  The proof is assembled from four independent pieces:

* `exists_isPathConnected_subset_of_mem_nhds`: a chart supplies arbitrarily small
  path-connected neighbourhoods;
* `locallyPathConnectedSpace_of_chartedSpace`: consequently a charted space over `ℂ` is
  locally path connected, so a preconnected open set in it is path connected;
* `isPreconnected_halfOpenAnnulus` / `isPreconnected_chartAnnulus`: the half-open closed
  annulus between the two chart spheres is preconnected;
* `exists_first_exit`: the first time a continuous path enters a closed set is a point of
  that set which is not an interior point.
-/

namespace Work.SimplyConnected.ABS

open Set Metric

open scoped Topology

noncomputable section

/-! ## Local path connectivity from a chart -/

/-- Every point of a charted space over `ℂ` has arbitrarily small path-connected
neighbourhoods: the inverse image of a small Euclidean ball under a chart at the point. -/
theorem exists_isPathConnected_subset_of_mem_nhds {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
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
theorem locallyPathConnectedSpace_of_chartedSpace (X : Type*) [TopologicalSpace X]
    [ChartedSpace ℂ X] : LocallyPathConnectedSpace X := by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro x u hu hxu
  obtain ⟨V, hVopen, hxV, hVsub, hVpc⟩ :=
    exists_isPathConnected_subset_of_mem_nhds x (hu.mem_nhds hxu)
  refine Filter.mem_of_superset (hVopen.mem_nhds hxV) ?_
  intro y hy
  exact (hVpc.joinedIn x hxV y hy).mono hVsub

/-! ## The half-open annulus in `ℂ` -/

/-- The half-open closed annulus `{z | s < ‖z - a‖ ≤ ρ}` is preconnected: it is the image of
the preconnected set `(s, ρ] × S¹` under `(t, u) ↦ a + t • u`. -/
theorem isPreconnected_halfOpenAnnulus (a : ℂ) {s ρ : ℝ} (hs : 0 < s) :
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

/-- The annulus of a complex chart cut out by two closed balls is preconnected. -/
theorem isPreconnected_chartAnnulus {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
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
        exact ⟨c.map_target hwt, by rw [c.right_inv hwt, Metric.mem_closedBall, dist_eq_norm]; exact h2⟩
      · intro hmem
        rw [Submission.mem_chartClosedBall] at hmem
        have hws : ‖w - a‖ ≤ s := by
          have := hmem.2
          rw [c.right_inv hwt] at this
          rwa [Metric.mem_closedBall, dist_eq_norm] at this
        linarith
  rw [hset]
  exact (isPreconnected_halfOpenAnnulus a hs).image c.symm (c.continuousOn_symm.mono hBsub)

/-! ## The first entrance time of a closed set -/

/-- Let `f : ℝ → X` be continuous, `K ⊆ X` closed, `f 0 ∉ K` and `f 1 ∈ K`.  Then there is
`t > 0` with `f t ∈ K`, `f t ∉ interior K` and `f u ∉ K` for all `0 ≤ u < t`. -/
theorem exists_first_exit {X : Type*} [TopologicalSpace X] {f : ℝ → X} (hf : Continuous f)
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

/-! ## The main theorem -/

theorem isPreconnected_sdiff_chartClosedBall {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] {Ω : Set X} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ s : ℝ} (hs : 0 < s) (hsρ : s < ρ)
    (hρsub : Metric.closedBall a ρ ⊆ c.target) (hρΩ : Submission.chartClosedBall c a ρ ⊆ Ω) :
    IsPreconnected (Ω \ Submission.chartClosedBall c a s) := by
  have hLP : LocallyPathConnectedSpace X := locallyPathConnectedSpace_of_chartedSpace X
  have hρpos : 0 < ρ := lt_trans hs hsρ
  -- the centre of the chart disc lies in `Ω`
  have haρ : a ∈ Metric.closedBall a ρ := Metric.mem_closedBall_self hρpos.le
  have hw₀Kρ : c.symm a ∈ Submission.chartClosedBall c a ρ := by
    rw [Submission.mem_chartClosedBall]
    exact ⟨c.map_target (hρsub haρ), by rw [c.right_inv (hρsub haρ)]; exact haρ⟩
  have hw₀Ω : c.symm a ∈ Ω := hρΩ hw₀Kρ
  have hΩpc : IsPathConnected Ω :=
    (hΩo.isConnected_iff_isPathConnected).mp ⟨⟨c.symm a, hw₀Ω⟩, hΩc⟩
  -- the annulus is preconnected and is contained in `Ω \ chartClosedBall c a s`
  have hAp : IsPreconnected
      (Submission.chartClosedBall c a ρ \ Submission.chartClosedBall c a s) :=
    isPreconnected_chartAnnulus hs hρsub
  have hAsub : Submission.chartClosedBall c a ρ \ Submission.chartClosedBall c a s
      ⊆ Ω \ Submission.chartClosedBall c a s :=
    fun y hy => ⟨hρΩ hy.1, hy.2⟩
  -- the open chart ball is contained in the interior of the closed chart ball
  have hball_int : Submission.chartBall c a ρ ⊆ interior (Submission.chartClosedBall c a ρ) :=
    (Submission.chartBall_isOpen c a ρ).subset_interior_iff.mpr
      (Submission.chartBall_subset_chartClosedBall c a ρ)
  set Ks : Set X := Submission.chartClosedBall c a s with hKs
  set Kρ : Set X := Submission.chartClosedBall c a ρ with hKρ
  set A : Set X := Kρ \ Ks with hA
  have hKsKρ : Ks ⊆ Kρ := fun y hy =>
    ⟨hy.1, Metric.closedBall_subset_closedBall (le_of_lt hsρ) hy.2⟩
  have hKρclosed : IsClosed Kρ := Submission.isClosed_chartClosedBall hρsub
  intro u v hu hv huv huneu hunev
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hdisj : ∀ y, y ∈ Ω \ Ks → y ∈ u → y ∈ v → False := by
    intro y hy hyu hyv
    exact (Set.eq_empty_iff_forall_notMem.mp hcon) y ⟨hy, hyu, hyv⟩
  -- Core step: a point of the outer part of `Ω` lies on the same side as the annulus.
  have key : ∀ {w w' : Set X}, IsOpen w → IsOpen w' → A ⊆ w → u ∪ v = w ∪ w' →
      (∀ y, y ∈ Ω \ Ks → y ∈ w → y ∈ w' → False) →
      ((Ω \ Ks) ∩ w').Nonempty → False := by
    intro w w' hw hw' hAw hww' hdisj' hne'
    obtain ⟨z, hzS, hzw'⟩ := hne'
    have hzΩ : z ∈ Ω := hzS.1
    have hzKs : z ∉ Ks := hzS.2
    have hznKρ : z ∉ Kρ := fun hzρ => hdisj' z hzS (hAw ⟨hzρ, hzKs⟩) hzw'
    -- a path in `Ω` from `z` to the centre of the chart disc
    obtain ⟨x₀, hx₀Ω, hjoin⟩ := hΩpc
    have hji : JoinedIn Ω z (c.symm a) := (hjoin hzΩ).symm.trans (hjoin hw₀Ω)
    set γ : Path z (c.symm a) := hji.somePath with hγ
    have hγmem : ∀ τ : unitInterval, γ τ ∈ Ω := hji.somePath_mem
    have hfΩ : ∀ τ : ℝ, γ.extend τ ∈ Ω := by
      intro τ
      rcases le_or_gt τ 0 with hτ | hτ
      · rw [Path.extend_of_le_zero γ hτ]; exact hzΩ
      · rcases le_or_gt 1 τ with hτ1 | hτ1
        · rw [Path.extend_of_one_le γ hτ1]; exact hw₀Ω
        · rw [Path.extend_apply γ ⟨hτ.le, hτ1.le⟩]
          exact hγmem ⟨τ, ⟨hτ.le, hτ1.le⟩⟩
    obtain ⟨t₁, ht₁pos, ht₁mem, ht₁notint, ht₁out⟩ :=
      exists_first_exit γ.continuous_extend hKρclosed (by rw [Path.extend_zero]; exact hznKρ)
        (by rw [Path.extend_one]; exact hw₀Kρ)
    -- the exit point has chart modulus exactly `ρ`, hence lies in the annulus
    have hpnorm : ‖c (γ.extend t₁) - a‖ = ρ := by
      have hle : ‖c (γ.extend t₁) - a‖ ≤ ρ := by
        have h : c (γ.extend t₁) ∈ Metric.closedBall a ρ := ht₁mem.2
        rwa [Metric.mem_closedBall, dist_eq_norm] at h
      have hge : ρ ≤ ‖c (γ.extend t₁) - a‖ := by
        by_contra hlt
        have hb : γ.extend t₁ ∈ Submission.chartBall c a ρ := by
          rw [Submission.mem_chartBall]
          refine ⟨ht₁mem.1, ?_⟩
          rw [Metric.mem_ball, dist_eq_norm]
          exact not_le.mp hlt
        exact ht₁notint (hball_int hb)
      linarith
    have hpA : γ.extend t₁ ∈ A := by
      refine ⟨ht₁mem, ?_⟩
      intro hKs'
      have hle : ‖c (γ.extend t₁) - a‖ ≤ s := by
        have h : c (γ.extend t₁) ∈ Metric.closedBall a s := hKs'.2
        rwa [Metric.mem_closedBall, dist_eq_norm] at h
      linarith
    have hpw : γ.extend t₁ ∈ w := hAw hpA
    -- a time just before `t₁` at which the path is already inside `w`
    obtain ⟨ε, hε, hεw⟩ := Metric.mem_nhds_iff.mp
      (γ.continuous_extend.continuousAt.preimage_mem_nhds (hw.mem_nhds hpw))
    set τ : ℝ := t₁ - ε / 2 with hτ
    have hτlt : τ < t₁ := by rw [hτ]; linarith
    have hτw : γ.extend τ ∈ w := by
      apply hεw
      rw [Metric.mem_ball, Real.dist_eq]
      have hsub : τ - t₁ = -(ε / 2) := by rw [hτ]; ring
      rw [hsub, abs_neg, abs_of_pos (by linarith)]
      linarith
    -- the piece of the path before `t₁` lies in `Ω \ Ks`
    have hpcs : IsPreconnected (γ.extend '' Set.Iio t₁) :=
      isPreconnected_Iio.image _ γ.continuous_extend.continuousOn
    have hpcs_sub : γ.extend '' Set.Iio t₁ ⊆ Ω \ Ks := by
      rintro y ⟨σ, hσ, rfl⟩
      refine ⟨hfΩ σ, ?_⟩
      intro hyKs
      by_cases h0σ : 0 ≤ σ
      · exact ht₁out σ h0σ hσ (hKsKρ hyKs)
      · rw [Path.extend_of_le_zero γ (not_le.mp h0σ).le] at hyKs
        exact hznKρ (hKsKρ hyKs)
    have hzs : z ∈ γ.extend '' Set.Iio t₁ := ⟨0, ht₁pos, γ.extend_zero⟩
    have hpcs_uv : γ.extend '' Set.Iio t₁ ⊆ u ∪ v := fun y hy => huv (hpcs_sub hy)
    by_cases hmeet : ((γ.extend '' Set.Iio t₁) ∩ w).Nonempty
    · -- the piece meets both sides, so it meets their intersection
      obtain ⟨y, hys, hyw⟩ := hmeet
      obtain ⟨y', hy's, hy'w, hy'w'⟩ :=
        hpcs w w' hw hw' (fun y hy => hww' ▸ hpcs_uv hy) ⟨y, hys, hyw⟩ ⟨z, hzs, hzw'⟩
      exact hdisj' y' (hpcs_sub hy's) hy'w hy'w'
    · -- otherwise the piece stays on the other side, contradicting `γ.extend τ ∈ w`
      have hsw' : γ.extend '' Set.Iio t₁ ⊆ w' := by
        intro y hy
        rcases (hww' ▸ hpcs_uv hy : y ∈ w ∪ w') with hyw | hyw'
        · exact absurd ⟨y, hy, hyw⟩ hmeet
        · exact hyw'
      exact hdisj' (γ.extend τ) (hpcs_sub ⟨τ, hτlt, rfl⟩) hτw (hsw' ⟨τ, hτlt, rfl⟩)
  -- the case analysis
  have hAuv : A ⊆ u ∪ v := fun y hy => huv (hAsub hy)
  by_cases hAu : (A ∩ u).Nonempty
  · by_cases hAv : (A ∩ v).Nonempty
    · obtain ⟨y, hyA, hyu, hyv⟩ := hAp u v hu hv hAuv hAu hAv
      exact hdisj y (hAsub hyA) hyu hyv
    · have hAusub : A ⊆ u := by
        intro y hy
        rcases hAuv hy with hyu | hyv
        · exact hyu
        · exact absurd ⟨y, hy, hyv⟩ hAv
      exact key (w := u) (w' := v) hu hv hAusub rfl hdisj hunev
  · have hAvsub : A ⊆ v := by
      intro y hy
      rcases hAuv hy with hyu | hyv
      · exact absurd ⟨y, hy, hyu⟩ hAu
      · exact hyv
    exact key (w := v) (w' := u) hv hu hAvsub (Set.union_comm u v)
        (fun y hy hyv hyu => hdisj y hy hyu hyv) huneu

end

end Work.SimplyConnected.ABS
