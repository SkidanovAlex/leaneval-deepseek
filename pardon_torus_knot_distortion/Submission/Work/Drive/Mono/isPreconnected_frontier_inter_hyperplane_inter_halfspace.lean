import Mathlib

namespace Work.Drive.Mono

open Set Filter
open scoped Topology Pointwise

noncomputable section

/-- **The frontier of a convex body is preconnected** (dimension `≥ 2`). -/
private theorem frontier_convex_preconnected_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hE : 1 < Module.rank ℝ E) {S : Set E} (hSc : Convex ℝ S)
    (hSint : (interior S).Nonempty) (hb : Bornology.IsBounded S) :
    IsPreconnected (frontier S) := by
  obtain ⟨h, -, -, hfr⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hSc hSint hb
  have hsphere : IsPreconnected (Metric.sphere (0 : E) 1) := isPreconnected_sphere hE 0 1
  rw [← h.isInducing.isPreconnected_image, hfr]
  exact hsphere

/-- **The unit sphere cut by a half-space through the origin** is preconnected. -/
private theorem sphere_inter_halfspace_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : 1 < Module.rank ℝ E) (lam : E →L[ℝ] ℝ) :
    IsPreconnected (Metric.sphere (0 : E) 1 ∩ {x : E | lam x ≤ 0}) := by
  by_cases h0 : lam = 0
  · subst h0
    have hset : {x : E | (0 : E →L[ℝ] ℝ) x ≤ 0} = Set.univ := by
      ext x; simp
    rw [hset, Set.inter_univ]
    exact isPreconnected_sphere hE 0 1
  · obtain ⟨v, hv⟩ : ∃ v : E, lam v < 0 := by
      obtain ⟨w, hw⟩ : ∃ w : E, lam w ≠ 0 := by
        by_contra hh
        push Not at hh
        exact h0 (ContinuousLinearMap.ext hh)
      rcases lt_or_gt_of_ne hw with h | h
      · exact ⟨w, h⟩
      · exact ⟨-w, by rw [map_neg]; linarith⟩
    have hconv : Convex ℝ {x : E | lam x < 0} := by
      have h := (convex_Iio (0 : ℝ)).linear_preimage (lam : E →ₗ[ℝ] ℝ)
      simpa [Set.preimage, Set.mem_Iio] using h
    have hcont : ContinuousOn (fun x : E => (‖x‖)⁻¹ • x) {x : E | lam x < 0} := by
      apply ContinuousOn.smul
      · apply ContinuousOn.inv₀ continuous_norm.continuousOn
        intro x hx
        simp only [Set.mem_ofPred_eq] at hx
        exact norm_ne_zero_iff.mpr (fun h => by rw [h] at hx; simp at hx)
      · exact continuousOn_id
    have himgset : ((fun x : E => (‖x‖)⁻¹ • x) '' {x : E | lam x < 0})
        = Metric.sphere (0 : E) 1 ∩ {x : E | lam x < 0} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        change (‖x‖)⁻¹ • x ∈ Metric.sphere (0 : E) 1 ∩ {x : E | lam x < 0}
        have hxne : x ≠ 0 := by intro h; rw [h] at hx; simp at hx
        have hxn : (0:ℝ) < ‖x‖ := norm_pos_iff.mpr hxne
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
            abs_of_nonneg (norm_nonneg x)]
          exact inv_mul_cancel₀ hxn.ne'
        · change lam ((‖x‖)⁻¹ • x) < 0
          rw [map_smul, smul_eq_mul]
          exact mul_neg_of_pos_of_neg (inv_pos.mpr hxn) hx
      · rintro ⟨hy1, hy2⟩
        refine ⟨y, hy2, ?_⟩
        rw [Metric.mem_sphere, dist_zero_right] at hy1
        change (‖y‖)⁻¹ • y = y
        rw [hy1, inv_one, one_smul]
    have hpre : IsPreconnected (Metric.sphere (0 : E) 1 ∩ {x : E | lam x < 0}) := by
      rw [← himgset]
      exact hconv.isPreconnected.image _ hcont
    refine IsPreconnected.subset_closure hpre ?_ ?_
    · intro x hx
      refine ⟨hx.1, ?_⟩
      show lam x ≤ 0
      exact le_of_lt hx.2
    · rintro y ⟨hy1, hy2⟩
      have hyn : ‖y‖ = 1 := by rw [Metric.mem_sphere, dist_zero_right] at hy1; exact hy1
      have hy2' : lam y ≤ 0 := hy2
      rcases lt_or_eq_of_le hy2' with hlt | heq
      · exact subset_closure ⟨hy1, hlt⟩
      · have hyne : y ≠ 0 := by intro h; rw [h] at hyn; simp at hyn
        have hbase : Tendsto (fun t : ℝ => y + t • v) (𝓝 (0 : ℝ)) (𝓝 y) := by
          have h2 : Tendsto (fun t : ℝ => y + t • v) (𝓝 (0 : ℝ)) (𝓝 (y + (0 : ℝ) • v)) :=
            tendsto_const_nhds.add (tendsto_id.smul tendsto_const_nhds)
          simpa using h2
        have hrad : ContinuousAt (fun x : E => (‖x‖)⁻¹ • x) y := by
          have h1 : ContinuousAt (fun x : E => (‖x‖)⁻¹) y :=
            (continuous_norm.continuousAt).inv₀ (by simpa using hyne)
          apply h1.smul
          exact continuousAt_id
        have hfy : (fun x : E => (‖x‖)⁻¹ • x) y = y := by
          change (‖y‖)⁻¹ • y = y
          rw [hyn, inv_one, one_smul]
        have hcomp : Tendsto (fun t : ℝ => (‖y + t • v‖)⁻¹ • (y + t • v))
            (𝓝[>] (0 : ℝ)) (𝓝 y) := by
          have h1 : Tendsto (fun t : ℝ => y + t • v) (𝓝[>] (0 : ℝ)) (𝓝 y) :=
            hbase.mono_left nhdsWithin_le_nhds
          have h2 := hrad.tendsto.comp h1
          simpa [Function.comp_def, hfy] using h2
        apply mem_closure_of_tendsto hcomp
        filter_upwards [self_mem_nhdsWithin] with t ht
        have hlam0 : lam (y + t • v) < 0 := by
          rw [map_add, map_smul, smul_eq_mul, heq, zero_add]
          exact mul_neg_of_pos_of_neg ht hv
        have hne' : y + t • v ≠ 0 := by
          intro h; rw [h] at hlam0; simp at hlam0
        have hlam' : lam ((‖y + t • v‖⁻¹) • (y + t • v)) < 0 := by
          rw [map_smul, smul_eq_mul]
          exact mul_neg_of_pos_of_neg (inv_pos.mpr (norm_pos_iff.mpr hne')) hlam0
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
            abs_of_nonneg (norm_nonneg _)]
          exact inv_mul_cancel₀ (norm_pos_iff.mpr hne').ne'
        · change lam ((‖y + t • v‖⁻¹) • (y + t • v)) < 0
          exact hlam'

/-- **A section of the frontier of a convex body by a half-space is preconnected.** -/
private theorem frontier_inter_halfspace_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hE : 1 < Module.rank ℝ E) {S : Set E} (hSc : Convex ℝ S)
    (hScomp : IsCompact S) (hSint : (interior S).Nonempty) (lam : E →L[ℝ] ℝ) (c : ℝ) :
    IsPreconnected (frontier S ∩ {x : E | lam x ≤ c}) := by
  by_cases hcase : ({x : E | lam x = c} ∩ interior S).Nonempty
  · -- Case 2: the level set meets the interior; recentre at a point of it
    obtain ⟨o, ho_eq, ho_int⟩ := hcase
    have ho_lam : lam o = c := ho_eq
    set S' : Set E := (-o) +ᵥ S with hS'
    have hS'conv : Convex ℝ S' := hS'
      ▸ hSc.vadd (-o)
    have h0int : (0 : E) ∈ interior S' := by
      rw [hS', interior_vadd, Set.mem_vadd_set]
      exact ⟨o, ho_int, by simp [vadd_eq_add]⟩
    have hS'int : (interior S').Nonempty := ⟨0, h0int⟩
    have hnhds : S' ∈ 𝓝 (0 : E) :=
      mem_of_superset (isOpen_interior.mem_nhds h0int) interior_subset
    have hbdd : Bornology.IsBounded S' := hS' ▸ hScomp.isBounded.vadd (-o)
    have hvnb : Bornology.IsVonNBounded ℝ S' := NormedSpace.isVonNBounded_of_isBounded ℝ hbdd
    have hball_conv : Convex ℝ (Metric.ball (0 : E) 1) := convex_ball 0 1
    have hball_nhds : Metric.ball (0 : E) 1 ∈ 𝓝 (0 : E) := Metric.ball_mem_nhds 0 one_pos
    have hball_vnb : Bornology.IsVonNBounded ℝ (Metric.ball (0 : E) 1) :=
      NormedSpace.isVonNBounded_ball ℝ E 1
    set H : E ≃ₜ E := gaugeRescaleHomeomorph S' (Metric.ball (0 : E) 1) hS'conv hnhds hvnb
      hball_conv hball_nhds hball_vnb with hH
    have hHform : ∀ x : E, H x = gaugeRescale S' (Metric.ball (0 : E) 1) x := fun x => rfl
    have hHrad : ∀ x : E, H x = (gauge S' x / gauge (Metric.ball (0 : E) 1) x) • x := by
      intro x; rw [hHform x, gaugeRescale_def]
    have hHsymm : ∀ y : E, H.symm y = gaugeRescale (Metric.ball (0 : E) 1) S' y := fun y => rfl
    have hHsymm_rad : ∀ y : E,
        H.symm y = (gauge (Metric.ball (0 : E) 1) y / gauge S' y) • y := by
      intro y; rw [hHsymm y, gaugeRescale_def]
    have hHfrontier : H '' frontier S' = Metric.sphere (0 : E) 1 := by
      rw [← closure_sdiff_interior]
      rw [Set.image_sdiff H.injective]
      rw [hH]
      rw [image_gaugeRescaleHomeomorph_closure hS'conv hnhds hvnb hball_conv hball_nhds hball_vnb,
        image_gaugeRescaleHomeomorph_interior hS'conv hnhds hvnb hball_conv hball_nhds hball_vnb,
        closure_ball 0 one_ne_zero, (Metric.isOpen_ball).interior_eq]
      exact Metric.closedBall_sdiff_ball
    have hHhalf : H '' {x : E | lam x ≤ 0} = {x : E | lam x ≤ 0} := by
      apply Set.Subset.antisymm
      · rintro z ⟨x, hx, rfl⟩
        show lam (H x) ≤ 0
        rw [hHrad x, map_smul, smul_eq_mul]
        exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg (gauge_nonneg _) (gauge_nonneg _)) hx
      · intro z hz
        refine ⟨H.symm z, ?_, H.apply_symm_apply z⟩
        show lam (H.symm z) ≤ 0
        rw [hHsymm_rad z, map_smul, smul_eq_mul]
        exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg (gauge_nonneg _) (gauge_nonneg _)) hz
    have himg : H '' (frontier S' ∩ {x : E | lam x ≤ 0})
        = Metric.sphere (0 : E) 1 ∩ {x : E | lam x ≤ 0} := by
      rw [Set.image_inter H.injective, hHfrontier, hHhalf]
    have hpre0 : IsPreconnected (frontier S' ∩ {x : E | lam x ≤ 0}) := by
      have hpreimg : IsPreconnected (H '' (frontier S' ∩ {x : E | lam x ≤ 0})) := by
        rw [himg]; exact sphere_inter_halfspace_aux hE lam
      exact (H.isInducing.isPreconnected_image).mp hpreimg
    have hTfront : (fun w : E => o + w) '' (frontier S' ∩ {x : E | lam x ≤ 0})
        = frontier S ∩ {x : E | lam x ≤ c} := by
      let T : E ≃ₜ E := Homeomorph.addLeft o
      have hTapp : ⇑T = fun w : E => o + w := rfl
      have hTS' : T '' S' = S := by
        ext z
        constructor
        · rintro ⟨w, hw, rfl⟩
          rw [hS', Set.mem_vadd_set] at hw
          obtain ⟨s, hs, hws⟩ := hw
          have hw' : w = s - o := by rw [← hws, vadd_eq_add]; abel
          show o + w ∈ S
          rw [hw', show o + (s - o) = s by abel]
          exact hs
        · intro hz
          refine ⟨z - o, ?_, ?_⟩
          · rw [hS', Set.mem_vadd_set]
            exact ⟨z, hz, by simp only [vadd_eq_add]; abel⟩
          · change o + (z - o) = z
            abel
      have hThalf : T '' {x : E | lam x ≤ 0} = {x : E | lam x ≤ c} := by
        ext z
        constructor
        · rintro ⟨w, hw, rfl⟩
          change lam (o + w) ≤ c
          have hw' : lam w ≤ 0 := hw
          rw [map_add, ho_lam]; linarith
        · intro hz
          refine ⟨z - o, ?_, ?_⟩
          · change lam (z - o) ≤ 0
            have hz' : lam z ≤ c := hz
            rw [map_sub, ho_lam]; linarith
          · change o + (z - o) = z
            abel
      rw [← hTapp, Set.image_inter T.injective, T.image_frontier, hTS', hThalf]
    rw [← hTfront]
    exact hpre0.image _ (continuous_const.add continuous_id).continuousOn
  · -- Case 1: the level set misses the interior
    have hmiss : ∀ x ∈ interior S, lam x ≠ c := fun x hx hxc => hcase ⟨x, hxc, hx⟩
    have hintpre : IsPreconnected (interior S) := hSc.interior.isPreconnected
    have hcover : interior S ⊆ {x : E | lam x < c} ∪ {x : E | lam x > c} := by
      intro x hx
      rcases lt_trichotomy (lam x) c with h | h | h
      · exact Or.inl h
      · exact absurd h (hmiss x hx)
      · exact Or.inr h
    have hu : IsOpen {x : E | lam x < c} := isOpen_lt lam.continuous continuous_const
    have hv : IsOpen {x : E | lam x > c} := isOpen_lt continuous_const lam.continuous
    have hScl : closure (interior S) = S := by
      rw [hSc.closure_interior_eq_closure_of_nonempty_interior hSint, hScomp.isClosed.closure_eq]
    by_cases hA : (interior S ∩ {x : E | lam x < c}).Nonempty
    · -- interior S ⊆ {lam < c}
      have hBempty : interior S ∩ {x : E | lam x > c} = ∅ := by
        by_contra hne
        have hne' : (interior S ∩ {x : E | lam x > c}).Nonempty :=
          Set.nonempty_iff_ne_empty.mpr hne
        obtain ⟨z, hz, hzu, hzv⟩ :=
          hintpre {x : E | lam x < c} {x : E | lam x > c} hu hv hcover hA hne'
        have h1 : lam z < c := hzu
        have h2 : c < lam z := hzv
        linarith
      have hintlt : ∀ x ∈ interior S, lam x < c := by
        intro x hx
        rcases lt_trichotomy (lam x) c with h | h | h
        · exact h
        · exact absurd h (hmiss x hx)
        · exfalso
          have : x ∈ interior S ∩ {x : E | lam x > c} := ⟨hx, h⟩
          rw [hBempty] at this; exact this
      have hSle : S ⊆ {x : E | lam x ≤ c} := by
        rw [← hScl]
        exact closure_minimal (fun x hx => le_of_lt (hintlt x hx))
          (isClosed_Iic.preimage lam.continuous)
      have hAeq : frontier S ∩ {x : E | lam x ≤ c} = frontier S := by
        apply Set.Subset.antisymm Set.inter_subset_left
        intro x hx
        exact ⟨hx, hSle (hScomp.isClosed.frontier_subset hx)⟩
      rw [hAeq]
      exact frontier_convex_preconnected_aux hE hSc hSint hScomp.isBounded
    · -- interior S ⊆ {lam > c}
      have hintgt : ∀ x ∈ interior S, c < lam x := by
        intro x hx
        rcases lt_trichotomy (lam x) c with h | h | h
        · exact absurd ⟨x, hx, h⟩ hA
        · exact absurd h (hmiss x hx)
        · exact h
      have hSge : S ⊆ {x : E | lam x ≥ c} := by
        rw [← hScl]
        exact closure_minimal (fun x hx => le_of_lt (hintgt x hx))
          (isClosed_Ici.preimage lam.continuous)
      have hAeq : frontier S ∩ {x : E | lam x ≤ c} = S ∩ {x : E | lam x = c} := by
        apply Set.Subset.antisymm
        · rintro x ⟨hx, hxl⟩
          refine ⟨hScomp.isClosed.frontier_subset hx, le_antisymm hxl ?_⟩
          exact hSge (hScomp.isClosed.frontier_subset hx)
        · rintro x ⟨hx, hxl⟩
          refine ⟨?_, le_of_eq hxl⟩
          rw [← closure_sdiff_interior]
          exact ⟨hScomp.isClosed.closure_eq.symm ▸ hx, fun hxi => hmiss x hxi hxl⟩
      rw [hAeq]
      exact (hSc.inter ((convex_singleton c).linear_preimage (lam : E →ₗ[ℝ] ℝ))).isPreconnected

/-- **Pardon's slice of the frontier.** -/
theorem isPreconnected_frontier_inter_hyperplane_inter_halfspace {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hKc : Convex ℝ K) (hKcomp : IsCompact K) (hKint : (interior K).Nonempty)
    {f : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ} (hf : f ≠ 0) (t : ℝ)
    {ℓ : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ} (lam : ℝ) :
    IsPreconnected (frontier K ∩ {y : EuclideanSpace ℝ (Fin 3) | f y = t}
      ∩ {y : EuclideanSpace ℝ (Fin 3) | ℓ y ≤ lam}) := by
  by_cases hcase : (interior K ∩ {y : EuclideanSpace ℝ (Fin 3) | f y = t}).Nonempty
  · obtain ⟨o, ho_int, ho_f⟩ := hcase
    have ho_ft : f o = t := ho_f
    set L : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
      LinearMap.ker (f : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) with hL
    have hrank : 1 < Module.rank ℝ L := by
      have hfin : Module.finrank ℝ L = 2 := by
        have hsurj : Function.Surjective f := by
          intro y
          obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
            by_contra h
            push Not at h
            exact hf (ContinuousLinearMap.ext h)
          exact ⟨(y / f x) • x, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]⟩
        have hrange : LinearMap.range (f : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) = ⊤ :=
          LinearMap.range_eq_top.mpr hsurj
        have h1 : Module.finrank ℝ (LinearMap.range (f : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ))
            + Module.finrank ℝ L = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) :=
          LinearMap.finrank_range_add_finrank_ker (f : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)
        have hr1 : Module.finrank ℝ (LinearMap.range (f : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)) = 1 := by
          rw [hrange]
          rw [show Module.finrank ℝ ↥(⊤ : Submodule ℝ ℝ) = 1 by rw [finrank_top]; simp]
        have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
        rw [hr1, hE] at h1
        omega
      have h := Module.finrank_eq_rank ℝ L
      rw [hfin] at h
      rw [← h]
      norm_num
    have hLmem : ∀ v : EuclideanSpace ℝ (Fin 3), v ∈ L ↔ f v = 0 := fun v => by
      rw [hL, LinearMap.mem_ker]; exact Iff.rfl
    set S : Set L := {w : L | o + (w : EuclideanSpace ℝ (Fin 3)) ∈ K} with hS
    let μ : L →L[ℝ] ℝ := ℓ.comp (Submodule.subtypeL L)
    have hSclosed : IsClosed S := by
      have h : S = (fun w : L => o + (w : EuclideanSpace ℝ (Fin 3))) ⁻¹' K := rfl
      rw [h]
      exact hKcomp.isClosed.preimage (continuous_const.add continuous_subtype_val)
    have hSconv : Convex ℝ S := by
      intro a ha b hb r s hr hs hrs
      show o + ((r • a + s • b : L) : EuclideanSpace ℝ (Fin 3)) ∈ K
      have hrs' : r = 1 - s := by linarith
      have hkey : o + ((r • a + s • b : L) : EuclideanSpace ℝ (Fin 3))
          = r • (o + (a : EuclideanSpace ℝ (Fin 3)))
            + s • (o + (b : EuclideanSpace ℝ (Fin 3))) := by
        rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, hrs']
        module
      rw [hkey]
      exact hKc ha hb hr hs hrs
    have hSbdd : Bornology.IsBounded S := by
      obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hKcomp.isBounded
      refine Metric.isBounded_iff.mpr ⟨C, fun a ha b hb => ?_⟩
      rw [Subtype.dist_eq]
      have hd : dist (a : EuclideanSpace ℝ (Fin 3)) (b : EuclideanSpace ℝ (Fin 3))
          = dist (o + (a : EuclideanSpace ℝ (Fin 3))) (o + (b : EuclideanSpace ℝ (Fin 3))) := by
        rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
      rw [hd]
      exact hC ha hb
    have hScomp : IsCompact S := by
      rw [Metric.isCompact_iff_isClosed_bounded]
      exact ⟨hSclosed, hSbdd⟩
    have hSint : (interior S).Nonempty := by
      obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp isOpen_interior o ho_int
      refine ⟨0, mem_interior_iff_mem_nhds.mpr ?_⟩
      refine mem_of_superset (Metric.ball_mem_nhds (0 : L) hε) ?_
      intro w hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      show o + (w : EuclideanSpace ℝ (Fin 3)) ∈ K
      apply interior_subset (s := K)
      apply hεsub
      rw [Metric.mem_ball, dist_eq_norm]
      rw [show (o + (w : EuclideanSpace ℝ (Fin 3))) - o = (w : EuclideanSpace ℝ (Fin 3)) by abel]
      exact hw
    have himg_frontier : (fun w : L => o + (w : EuclideanSpace ℝ (Fin 3))) '' frontier S
        = frontier K ∩ {y : EuclideanSpace ℝ (Fin 3) | f y = t} := by
      apply Set.Subset.antisymm
      · rintro y ⟨w, hw, rfl⟩
        change o + (w : EuclideanSpace ℝ (Fin 3))
          ∈ frontier K ∩ {y : EuclideanSpace ℝ (Fin 3) | f y = t}
        rw [← closure_sdiff_interior] at hw
        have hwS : w ∈ S := hSclosed.closure_eq ▸ hw.1
        have hwK : o + (w : EuclideanSpace ℝ (Fin 3)) ∈ K := hwS
        have hwf : f (w : EuclideanSpace ℝ (Fin 3)) = 0 := (hLmem _).mp w.2
        refine ⟨?_, ?_⟩
        · rw [← closure_sdiff_interior]
          refine ⟨hKcomp.isClosed.closure_eq.symm ▸ hwK, ?_⟩
          intro hxint
          obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp isOpen_interior _ hxint
          have hwin : w ∈ interior S := by
            rw [mem_interior_iff_mem_nhds]
            refine mem_of_superset (Metric.ball_mem_nhds w hε) ?_
            intro v hv
            have hv' : ‖v - w‖ < ε := by rw [← dist_eq_norm]; exact hv
            have hKv : o + (v : EuclideanSpace ℝ (Fin 3)) ∈ K := by
              apply interior_subset (s := K)
              apply hεsub
              rw [Metric.mem_ball, dist_eq_norm]
              rw [show (o + (v : EuclideanSpace ℝ (Fin 3))) - (o + (w : EuclideanSpace ℝ (Fin 3)))
                  = ((v - w : L) : EuclideanSpace ℝ (Fin 3)) by rw [Submodule.coe_sub]; abel]
              exact hv'
            exact hKv
          exact hw.2 hwin
        · change f (o + (w : EuclideanSpace ℝ (Fin 3))) = t
          rw [map_add, ho_ft, hwf, add_zero]
      · rintro y ⟨hyfr, hyf⟩
        have hyft : f y = t := hyf
        rw [← closure_sdiff_interior] at hyfr
        have hyK : y ∈ K := hKcomp.isClosed.closure_eq ▸ hyfr.1
        have hynotint : y ∉ interior K := hyfr.2
        set w : L := ⟨y - o, (hLmem _).mpr (by rw [map_sub, hyft, ho_ft, sub_self])⟩ with hwdef
        refine ⟨w, ?_, ?_⟩
        · rw [← closure_sdiff_interior]
          refine ⟨?_, ?_⟩
          · rw [hSclosed.closure_eq]
            change o + (w : EuclideanSpace ℝ (Fin 3)) ∈ K
            rw [hwdef]
            change o + (y - o) ∈ K
            rw [show o + (y - o) = y by abel]; exact hyK
          · intro hwint
            obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp isOpen_interior _ hwint
            have hyne : y - o ≠ 0 := by
              intro h
              exact hynotint (by rw [sub_eq_zero.mp h]; exact ho_int)
            have hypos : (0:ℝ) < ‖(y - o : EuclideanSpace ℝ (Fin 3))‖ := norm_pos_iff.mpr hyne
            obtain ⟨s, hs, hsε⟩ : ∃ s : ℝ, 0 < s ∧ s * ‖(y - o : EuclideanSpace ℝ (Fin 3))‖ < ε := by
              refine ⟨ε / (2 * ‖(y - o : EuclideanSpace ℝ (Fin 3))‖),
                div_pos hε (by linarith), ?_⟩
              have h2 : (0:ℝ) < 2 * ‖(y - o : EuclideanSpace ℝ (Fin 3))‖ := by linarith
              rw [div_mul_eq_mul_div, div_lt_iff₀ h2]; nlinarith
            have hmemS : w + s • w ∈ S := by
              apply interior_subset
              apply hεsub
              rw [Metric.mem_ball, dist_eq_norm]
              rw [show (w + s • w) - w = s • w by abel]
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, hwdef]
              exact hsε
            have hk : o + ((w + s • w : L) : EuclideanSpace ℝ (Fin 3)) = y + s • (y - o) := by
              rw [hwdef, Submodule.coe_add, Submodule.coe_smul]
              module
            have hray : ∀ t : ℝ, 0 < t → y + t • (y - o) ∉ K := by
              intro t ht hmem
              have ht1 : (1:ℝ) + t ≠ 0 := by linarith
              have hcoef : 1 / (1 + t) + t / (1 + t) = 1 := by field_simp
              have hcombo : (1 / (1 + t)) • (y + t • (y - o)) + (t / (1 + t)) • o = y := by
                have hc : (1 / (1 + t)) * t = t / (1 + t) := by field_simp
                have hc2 : (1 / (1 + t)) + t / (1 + t) = 1 := by field_simp
                rw [smul_add, smul_smul, hc, add_assoc, ← smul_add, sub_add_cancel y o,
                  ← add_smul, hc2, one_smul]
              have hint : (1 / (1 + t)) • (y + t • (y - o)) + (t / (1 + t)) • o ∈ interior K :=
                hKc.combo_closure_interior_mem_interior
                  (hKcomp.isClosed.closure_eq.symm ▸ hmem) ho_int
                  (by positivity) (div_pos ht (by linarith)) hcoef
              rw [hcombo] at hint
              exact hynotint hint
            change o + ((w + s • w : L) : EuclideanSpace ℝ (Fin 3)) ∈ K at hmemS
            rw [hk] at hmemS
            exact hray s hs hmemS
        · change o + (w : EuclideanSpace ℝ (Fin 3)) = y
          rw [hwdef]
          change o + (y - o) = y
          abel
    have himg_half : (fun w : L => o + (w : EuclideanSpace ℝ (Fin 3)))
          '' {w : L | μ w ≤ lam - ℓ o}
        = {y : EuclideanSpace ℝ (Fin 3) | f y = t} ∩ {y : EuclideanSpace ℝ (Fin 3) | ℓ y ≤ lam} := by
      apply Set.Subset.antisymm
      · rintro y ⟨w, hw, rfl⟩
        change o + (w : EuclideanSpace ℝ (Fin 3))
          ∈ {y : EuclideanSpace ℝ (Fin 3) | f y = t}
            ∩ {y : EuclideanSpace ℝ (Fin 3) | ℓ y ≤ lam}
        have hwf : f (w : EuclideanSpace ℝ (Fin 3)) = 0 := (hLmem _).mp w.2
        have hwμ : μ w = ℓ (w : EuclideanSpace ℝ (Fin 3)) := rfl
        refine ⟨?_, ?_⟩
        · change f (o + (w : EuclideanSpace ℝ (Fin 3))) = t
          rw [map_add, ho_ft, hwf, add_zero]
        · change ℓ (o + (w : EuclideanSpace ℝ (Fin 3))) ≤ lam
          rw [map_add]
          have hw' : μ w ≤ lam - ℓ o := hw
          linarith
      · intro y hy
        rcases hy with ⟨hyf, hyl⟩
        have hyft : f y = t := hyf
        have hyl' : ℓ y ≤ lam := hyl
        let w : L := ⟨y - o, (hLmem _).mpr (by rw [map_sub, hyft, ho_ft, sub_self])⟩
        refine ⟨w, ?_, ?_⟩
        · show μ w ≤ lam - ℓ o
          change ℓ (y - o) ≤ lam - ℓ o
          rw [map_sub]; linarith
        · show o + (w : EuclideanSpace ℝ (Fin 3)) = y
          change o + (y - o) = y
          abel
    have hmain := frontier_inter_halfspace_aux hrank hSconv hScomp hSint μ (lam - ℓ o)
    have hsetid : frontier K ∩ {y : EuclideanSpace ℝ (Fin 3) | f y = t}
          ∩ {y : EuclideanSpace ℝ (Fin 3) | ℓ y ≤ lam}
        = (fun w : L => o + (w : EuclideanSpace ℝ (Fin 3))) ''
            (frontier S ∩ {w : L | μ w ≤ lam - ℓ o}) := by
      have hinj : Function.Injective (fun w : L => o + (w : EuclideanSpace ℝ (Fin 3))) :=
        fun a b hab => Subtype.ext (add_left_cancel hab)
      rw [Set.image_inter hinj, himg_frontier, himg_half]
      ext y
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, h2⟩, h2, h3⟩
      · rintro ⟨⟨h1, h2⟩, -, h3⟩
        exact ⟨⟨h1, h2⟩, h3⟩
    rw [hsetid]
    exact hmain.image _ (continuous_const.add continuous_subtype_val).continuousOn
  · -- Case 1: the plane misses the interior
    have hmiss : ∀ y ∈ interior K, f y ≠ t := fun y hy hyt => hcase ⟨y, hy, hyt⟩
    have hfr_eq : frontier K ∩ {y : EuclideanSpace ℝ (Fin 3) | f y = t}
        = K ∩ {y : EuclideanSpace ℝ (Fin 3) | f y = t} := by
      apply Set.Subset.antisymm
      · intro y hy
        exact ⟨hKcomp.isClosed.frontier_subset hy.1, hy.2⟩
      · rintro y ⟨hyK, hyf⟩
        refine ⟨?_, hyf⟩
        rw [← closure_sdiff_interior]
        exact ⟨hKcomp.isClosed.closure_eq.symm ▸ hyK, fun hyi => hmiss y hyi hyf⟩
    rw [hfr_eq]
    have hconv : Convex ℝ (K ∩ {y : EuclideanSpace ℝ (Fin 3) | f y = t}
        ∩ {y : EuclideanSpace ℝ (Fin 3) | ℓ y ≤ lam}) := by
      refine (hKc.inter ?_).inter ?_
      · have h := (convex_singleton t).linear_preimage (f : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)
        simpa [Set.preimage] using h
      · have h := (convex_Iic lam).linear_preimage (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)
        simpa [Set.preimage, Set.mem_Iic] using h
    exact hconv.isPreconnected

end

end Work.Drive.Mono
