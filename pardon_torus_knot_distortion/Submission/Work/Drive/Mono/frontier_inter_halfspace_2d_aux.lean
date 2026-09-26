import Mathlib

namespace Work.Drive.Mono

open Set

open scoped Pointwise

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The normalisation map `x ↦ ‖x‖⁻¹ • x` (used only on sets avoiding the origin). -/
def normMap (x : E) : E := ‖x‖⁻¹ • x

theorem norm_normMap (x : E) (hx : x ≠ 0) : ‖normMap x‖ = 1 := by
  rw [normMap, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg x),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- **The intersection of the unit sphere with a convex cone containing no line is
preconnected.**  Every point `u` of the intersection is joined to a fixed point `e` by the
normalised chord `{‖x‖⁻¹ • x | x ∈ [e,u]}`: this lies in the sphere, and it lies in the cone
because the cone is convex and closed under nonnegative scaling. -/
theorem isPreconnected_sphere_inter_cone {Q : Set E} (hc : Convex ℝ Q) (h0 : (0 : E) ∈ Q)
    (hcone : ∀ (t : ℝ), 0 ≤ t → ∀ x ∈ Q, t • x ∈ Q)
    (hline : ∀ x ∈ Q, x ≠ 0 → -x ∉ Q) :
    IsPreconnected (Metric.sphere (0 : E) 1 ∩ Q) := by
  rcases (Metric.sphere (0 : E) 1 ∩ Q).eq_empty_or_nonempty with hemp | hne
  · rw [hemp]; exact isPreconnected_empty
  · obtain ⟨e, he⟩ := hne
    have henorm : ‖e‖ = 1 := by
      have h := he.1
      rwa [Metric.mem_sphere, dist_zero_right] at h
    -- the chord from `e` to `u` avoids the origin
    have hseg_ne : ∀ u : E, u ∈ Metric.sphere (0 : E) 1 ∩ Q →
        (0 : E) ∉ segment ℝ e u := by
      intro u hu h0seg
      rw [segment_eq_image] at h0seg
      obtain ⟨θ, hθ, hθeq⟩ := h0seg
      have huQ : u ∈ Q := hu.2
      have hu_norm : ‖u‖ = 1 := by
        have h := hu.1
        rwa [Metric.mem_sphere, dist_zero_right] at h
      rcases lt_or_eq_of_le hθ.1 with hθpos | hθ0
      · have hθne : θ ≠ 0 := ne_of_gt hθpos
        have h2 : θ • u = -((1 - θ) • e) := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact hθeq
        have h1 : u = -((1 - θ) / θ) • e := by
          have h3 : u = θ⁻¹ • (θ • u) := by rw [smul_smul, inv_mul_cancel₀ hθne, one_smul]
          rw [h3, h2, smul_neg, smul_smul, div_eq_inv_mul, neg_smul]
        have hcpos : 0 ≤ (1 - θ) / θ := div_nonneg (by linarith [hθ.2]) (le_of_lt hθpos)
        have hmem : ((1 - θ) / θ) • e ∈ Q := hcone _ hcpos e he.2
        have : -u ∈ Q := by
          rw [h1, neg_smul]
          simpa using hmem
        exact hline u huQ (by intro h; rw [h] at hu_norm; norm_num at hu_norm) this
      · subst hθ0
        simp only [sub_zero, one_smul, zero_smul, add_zero] at hθeq
        rw [hθeq] at henorm
        norm_num at henorm
    -- the family of chords
    let chord : E → Set E := fun u => normMap '' (segment ℝ e u)
    have hchord_sub : ∀ u : E, u ∈ Metric.sphere (0 : E) 1 ∩ Q →
        chord u ⊆ Metric.sphere (0 : E) 1 ∩ Q := by
      intro u hu y hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hxQ : x ∈ Q := hc.segment_subset he.2 hu.2 hx
      have hxne : x ≠ 0 := fun h => hseg_ne u hu (h ▸ hx)
      constructor
      · exact Metric.mem_sphere.mpr (by rw [dist_zero_right, norm_normMap x hxne])
      · exact hcone _ (inv_nonneg.mpr (norm_nonneg x)) x hxQ
    have hunion : Metric.sphere (0 : E) 1 ∩ Q
        = ⋃ u : ↥(Metric.sphere (0 : E) 1 ∩ Q), chord (u : E) := by
      ext x
      constructor
      · intro hx
        rw [Set.mem_iUnion]
        refine ⟨⟨x, hx⟩, ?_⟩
        have hxnorm : ‖x‖ = 1 := by
          have h := hx.1
          rwa [Metric.mem_sphere, dist_zero_right] at h
        refine ⟨x, ?_, ?_⟩
        · rw [segment_eq_image]
          exact ⟨1, ⟨zero_le_one, le_refl 1⟩, by simp⟩
        · rw [normMap, hxnorm, inv_one, one_smul]
      · rw [Set.mem_iUnion]
        rintro ⟨u, hu⟩
        exact hchord_sub (u : E) u.2 hu
    rw [hunion]
    refine isPreconnected_iUnion ?_ ?_
    · refine ⟨e, ?_⟩
      rw [Set.mem_iInter]
      intro u
      refine ⟨e, ?_, ?_⟩
      · rw [segment_eq_image]
        exact ⟨0, ⟨le_refl 0, zero_le_one⟩, by simp⟩
      · rw [normMap, henorm, inv_one, one_smul]
    · intro u
      have hcont : ContinuousOn normMap (segment ℝ e (u : E)) := by
        have hnorm : ContinuousOn (fun x : E => ‖x‖⁻¹) (segment ℝ e (u : E)) :=
          continuous_norm.continuousOn.inv₀
            (fun x hx => ne_of_gt (norm_pos_iff.mpr (fun h => hseg_ne (u : E) u.2 (h ▸ hx))))
        show ContinuousOn (fun x : E => ‖x‖⁻¹ • x) (segment ℝ e (u : E))
        exact hnorm.smul continuousOn_id
      exact (convex_segment e (u : E)).isPreconnected.image _ hcont

/-- **The frontier of a compact convex set with nonempty interior in a normed space of
dimension at least `2` is preconnected** (it is homeomorphic to the unit sphere). -/
theorem isPreconnected_frontier_of_convex_aux [FiniteDimensional ℝ E]
    (h2 : Module.finrank ℝ E = 2) {C : Set E} (hCc : Convex ℝ C)
    (hCb : Bornology.IsBounded C) (hint : (interior C).Nonempty) :
    IsPreconnected (frontier C) := by
  obtain ⟨h, -, -, hfr⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hCc hint hCb
  have hrank : (1 : Cardinal) < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank ℝ E, h2]
    norm_num
  have hsphere : IsPreconnected (Metric.sphere (0 : E) 1) := isPreconnected_sphere hrank 0 1
  rw [← h.isInducing.isPreconnected_image, hfr]
  exact hsphere

/-- **The gauge computation.**  If `K` is compact convex with `0` in its interior and `μ < 0`,
then `frontier K ∩ {ℓ ≤ μ}` is preconnected: it is the image under the radial map
`u ↦ (gauge K u)⁻¹ • u` of `sphere 0 1 ∩ Q`, where `Q = {ℓ - μ * gauge K ≤ 0}` is a convex cone
containing no line. -/
theorem isPreconnected_frontier_inter_halfspace_of_zero_mem_interior {K : Set E}
    (hKc : Convex ℝ K) (hKk : IsCompact K) (h0 : (0 : E) ∈ interior K)
    {ℓ : E →L[ℝ] ℝ} {μ : ℝ} (hμ : μ < 0) :
    IsPreconnected (frontier K ∩ {x : E | ℓ x ≤ μ}) := by
  have hKnhds : K ∈ nhds (0 : E) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds h0) interior_subset
  have habs : Absorbent ℝ K := absorbent_nhds_zero hKnhds
  have hvonN : Bornology.IsVonNBounded ℝ K :=
    NormedSpace.isVonNBounded_of_isBounded ℝ hKk.isBounded
  have hgauge0 : gauge K (0 : E) = 0 := by
    simpa using gauge_smul_of_nonneg (show (0 : ℝ) ≤ 0 by norm_num) (0 : E)
  have hgcont : Continuous (gauge K) := continuous_gauge hKc hKnhds
  have hgpos : ∀ x : E, x ≠ 0 → 0 < gauge K x := fun x hx => (gauge_pos habs hvonN).mpr hx
  have hg1 : ∀ x : E, gauge K x = 1 ↔ x ∈ frontier K :=
    fun x => gauge_eq_one_iff_mem_frontier hKc hKnhds
  have hgle : ∀ x : E, gauge K x ≤ 1 → x ∈ K := by
    intro x hx
    have := (gauge_le_one_iff_mem_closure hKc hKnhds).mp hx
    rwa [hKk.isClosed.closure_eq] at this
  -- the cone
  set Q : Set E := {x : E | ℓ x - μ * gauge K x ≤ 0} with hQ
  have hQconv : Convex ℝ Q := by
    intro x hx y hy a b ha hb hab
    have hx' : ℓ x - μ * gauge K x ≤ 0 := hx
    have hy' : ℓ y - μ * gauge K y ≤ 0 := hy
    have hsub : gauge K (a • x + b • y) ≤ a * gauge K x + b * gauge K y := by
      calc gauge K (a • x + b • y) ≤ gauge K (a • x) + gauge K (b • y) :=
            gauge_add_le hKc habs _ _
        _ = a * gauge K x + b * gauge K y := by
            rw [gauge_smul_of_nonneg ha, gauge_smul_of_nonneg hb, smul_eq_mul, smul_eq_mul]
    have hsplit : ℓ (a • x + b • y) = a * ℓ x + b * ℓ y := by
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have hneg : (0 : ℝ) < -μ := neg_pos.mpr hμ
    show ℓ (a • x + b • y) - μ * gauge K (a • x + b • y) ≤ 0
    have hkey : -μ * gauge K (a • x + b • y) ≤ -μ * (a * gauge K x + b * gauge K y) :=
      mul_le_mul_of_nonneg_left hsub hneg.le
    have hfin : a * (ℓ x - μ * gauge K x) + b * (ℓ y - μ * gauge K y) ≤ 0 := by
      have h1 : a * (ℓ x - μ * gauge K x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hx'
      have h2 : b * (ℓ y - μ * gauge K y) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hy'
      linarith
    linarith [hsplit, hkey, hfin]
  have hQcone : ∀ (t : ℝ), 0 ≤ t → ∀ x ∈ Q, t • x ∈ Q := by
    intro t ht x hx
    have hx' : ℓ x - μ * gauge K x ≤ 0 := hx
    show ℓ (t • x) - μ * gauge K (t • x) ≤ 0
    rw [map_smul, smul_eq_mul, gauge_smul_of_nonneg ht, smul_eq_mul]
    nlinarith [hx', ht]
  have hQline : ∀ x ∈ Q, x ≠ 0 → -x ∉ Q := by
    intro x hx hxne hnegx
    have hx' : ℓ x - μ * gauge K x ≤ 0 := hx
    have hnegx' : ℓ (-x) - μ * gauge K (-x) ≤ 0 := hnegx
    have hgx : 0 < gauge K x := hgpos x hxne
    have hmulp : μ * gauge K x < 0 := mul_neg_of_neg_of_pos hμ hgx
    have h1 : ℓ x ≤ μ * gauge K x := by linarith
    have h5 : ℓ x < 0 := lt_of_le_of_lt h1 hmulp
    rw [map_neg] at hnegx'
    have hneg' : μ * gauge K (-x) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hμ.le (gauge_nonneg _)
    linarith [hnegx', hneg', h5]
  -- the sphere piece
  have hQmem0 : (0 : E) ∈ Q := by
    show ℓ (0 : E) - μ * gauge K (0 : E) ≤ 0
    rw [map_zero, hgauge0]
    linarith
  have hsphere : IsPreconnected (Metric.sphere (0 : E) 1 ∩ Q) :=
    isPreconnected_sphere_inter_cone hQconv hQmem0 hQcone hQline
  have hradial : frontier K ∩ {x : E | ℓ x ≤ μ}
      = (fun u : E => (gauge K u)⁻¹ • u) '' (Metric.sphere (0 : E) 1 ∩ Q) := by
    ext x
    constructor
    · rintro ⟨hxfr, hxμ⟩
      rw [Set.mem_ofPred_eq] at hxμ
      have hgx : gauge K x = 1 := (hg1 x).mpr hxfr
      have hxne : x ≠ 0 := by
        intro h; rw [h, hgauge0] at hgx; norm_num at hgx
      have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hxne
      refine ⟨‖x‖⁻¹ • x, ⟨?_, ?_⟩, ?_⟩
      · rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_pos (norm_pos_iff.mpr hxne), inv_mul_cancel₀ hxnorm]
      · show ℓ (‖x‖⁻¹ • x) - μ * gauge K (‖x‖⁻¹ • x) ≤ 0
        have hinv : (0 : ℝ) ≤ ‖x‖⁻¹ := inv_nonneg.mpr (norm_nonneg x)
        rw [map_smul, smul_eq_mul, gauge_smul_of_nonneg hinv, smul_eq_mul, hgx, mul_one]
        have := mul_le_mul_of_nonneg_left hxμ hinv
        nlinarith [this]
      · have hgu : gauge K (‖x‖⁻¹ • x) = ‖x‖⁻¹ := by
          rw [gauge_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), smul_eq_mul, hgx, mul_one]
        change (gauge K (‖x‖⁻¹ • x))⁻¹ • (‖x‖⁻¹ • x) = x
        rw [hgu, smul_smul, inv_inv, mul_inv_cancel₀ hxnorm, one_smul]
    · rintro ⟨u, ⟨hu, huQ⟩, rfl⟩
      have hunorm : ‖u‖ = 1 := by
        have h := hu; rwa [Metric.mem_sphere, dist_zero_right] at h
      have huQ' : ℓ u - μ * gauge K u ≤ 0 := huQ
      have hupos : 0 < gauge K u :=
        hgpos u (by intro h; rw [h] at hunorm; norm_num at hunorm)
      constructor
      · rw [← hg1, gauge_smul_of_nonneg (inv_nonneg.mpr hupos.le), smul_eq_mul,
          inv_mul_cancel₀ (ne_of_gt hupos)]
      · show ℓ ((gauge K u)⁻¹ • u) ≤ μ
        rw [map_smul, smul_eq_mul]
        have hle : ℓ u ≤ μ * gauge K u := by linarith
        have hinv : 0 < (gauge K u)⁻¹ := inv_pos.mpr hupos
        calc (gauge K u)⁻¹ * ℓ u ≤ (gauge K u)⁻¹ * (μ * gauge K u) :=
              mul_le_mul_of_nonneg_left hle hinv.le
          _ = μ := by
              rw [mul_comm μ (gauge K u), ← mul_assoc,
                inv_mul_cancel₀ (ne_of_gt hupos), one_mul]
  rw [hradial]
  refine IsPreconnected.image hsphere _ ?_
  have hcont : ContinuousOn (fun u : E => (gauge K u)⁻¹ • u)
      (Metric.sphere (0 : E) 1 ∩ Q) := by
    have h1 : ContinuousOn (fun u : E => (gauge K u)⁻¹) (Metric.sphere (0 : E) 1 ∩ Q) :=
      (hgcont.continuousOn).inv₀ (fun u hu => by
        have hunorm : ‖u‖ = 1 := by
          have h := hu.1; rwa [Metric.mem_sphere, dist_zero_right] at h
        exact ne_of_gt (hgpos u (by intro h; rw [h] at hunorm; norm_num at hunorm)))
    show ContinuousOn (fun u : E => (gauge K u)⁻¹ • u) (Metric.sphere (0 : E) 1 ∩ Q)
    exact h1.smul continuousOn_id
  exact hcont

/-- **The frontier of a compact convex set with nonempty interior in a `2`-dimensional space,
cut by a closed halfspace, is preconnected.** -/
theorem isPreconnected_frontier_inter_halfspace_2d_aux [FiniteDimensional ℝ E]
    (h2 : Module.finrank ℝ E = 2) {C : Set E} (hCc : Convex ℝ C) (hCk : IsCompact C)
    (hint : (interior C).Nonempty) {ℓ : E →L[ℝ] ℝ} (lam : ℝ) :
    IsPreconnected (frontier C ∩ {x : E | ℓ x ≤ lam}) := by
  have hCcl : IsClosed C := hCk.isClosed
  by_cases hsub : C ⊆ {x : E | ℓ x ≤ lam}
  · have hEq : frontier C ∩ {x : E | ℓ x ≤ lam} = frontier C :=
      Set.inter_eq_left.mpr (fun x hx => hsub (hCcl.frontier_subset hx))
    rw [hEq]
    exact isPreconnected_frontier_of_convex_aux h2 hCc hCk.isBounded hint
  · by_cases hne : (C ∩ {x : E | ℓ x ≤ lam}).Nonempty
    · -- the cutting case: shift so that an interior point of `C` above the wall becomes the origin
      have hex : ∃ z : E, z ∈ C ∧ lam < ℓ z := by
        by_contra h
        apply hsub
        intro x hx
        by_contra hx'
        exact h ⟨x, hx, not_le.mp hx'⟩
      obtain ⟨z, hzC, hzlt⟩ := hex
      have hclosure : closure (interior C) = C := by
        rw [hCc.closure_interior_eq_closure_of_nonempty_interior hint, hCcl.closure_eq]
      have hzcl : z ∈ closure (interior C) := by rw [hclosure]; exact hzC
      obtain ⟨ε, hε, hεsub⟩ :=
        Metric.isOpen_iff.mp (isOpen_lt continuous_const ℓ.continuous) z hzlt
      obtain ⟨p, hpint, hpdist⟩ := Metric.mem_closure_iff.mp hzcl ε hε
      have hplt : lam < ℓ p := hεsub (by rwa [Metric.mem_ball, dist_comm])
      -- shift by `p`
      set C' : Set E := (-p) +ᵥ C with hC'
      have hC'c : Convex ℝ C' := by rw [hC']; exact hCc.vadd (-p)
      have hC'k : IsCompact C' := by rw [hC']; exact hCk.vadd (-p)
      have hC'0 : (0 : E) ∈ interior C' := by
        rw [hC', interior_vadd, Set.mem_vadd_set]
        exact ⟨p, hpint, by simp⟩
      have hμ : lam - ℓ p < 0 := by linarith
      have hpre := isPreconnected_frontier_inter_halfspace_of_zero_mem_interior
        hC'c hC'k hC'0 hμ (ℓ := ℓ)
      -- transfer back
      have himg : (fun y : E => y + p) '' (frontier C' ∩ {x : E | ℓ x ≤ lam - ℓ p})
          = frontier C ∩ {x : E | ℓ x ≤ lam} := by
        ext y
        constructor
        · rintro ⟨x, ⟨hxfr, hxH⟩, rfl⟩
          have hxC : x + p ∈ C := by
            have h := hC'k.isClosed.frontier_subset hxfr
            rw [hC', Set.mem_vadd_set] at h
            obtain ⟨y, hyC, hyx⟩ := h
            have : (-p +ᵥ y) + p = y := by simp
            rw [← hyx, this]
            exact hyC
          have hxint : x + p ∉ interior C := by
            intro hc
            have h4 : x ∈ interior C' := by
              rw [hC', interior_vadd, Set.mem_vadd_set]
              exact ⟨x + p, hc, by rw [vadd_eq_add]; abel⟩
            have h5 := hxfr
            rw [hC'k.isClosed.frontier_eq] at h5
            exact h5.2 h4
          have hr : x + p ∈ frontier C := by
            rw [hCcl.frontier_eq]
            exact ⟨hxC, hxint⟩
          rw [Set.mem_ofPred_eq] at hxH
          refine ⟨hr, ?_⟩
          rw [Set.mem_ofPred_eq]
          have : ℓ (x + p) = ℓ x + ℓ p := map_add ℓ x p
          linarith
        · rintro ⟨hyfr, hyH⟩
          have hyC : y ∈ C := hCcl.frontier_subset hyfr
          have hyint : y ∉ interior C := (hCcl.frontier_eq ▸ hyfr).2
          refine ⟨y - p, ⟨?_, ?_⟩, by simp⟩
          · rw [hC'k.isClosed.frontier_eq]
            refine ⟨?_, ?_⟩
            · rw [hC', Set.mem_vadd_set]
              exact ⟨y, hyC, by rw [vadd_eq_add]; abel⟩
            · intro hc
              have h4 : y ∈ interior C := by
                rw [hC', interior_vadd (-p) C, Set.mem_vadd_set] at hc
                obtain ⟨y1, hy1, hy1eq⟩ := hc
                have hy1eq' : -p + y1 = y - p := by simpa [vadd_eq_add] using hy1eq
                have h2 : -p + y1 = -p + y := by
                  rw [hy1eq', sub_eq_add_neg, add_comm y (-p)]
                have : y1 = y := add_left_cancel_iff.mp h2
                rwa [this] at hy1
              exact hyint h4
          · rw [Set.mem_ofPred_eq]
            rw [Set.mem_ofPred_eq] at hyH
            have : ℓ (y - p) = ℓ y - ℓ p := map_sub ℓ y p
            linarith
      rw [← himg]
      exact hpre.image _ (by fun_prop : Continuous fun y : E => y + p).continuousOn
    · -- the halfspace misses the set
      have hEmp : frontier C ∩ {x : E | ℓ x ≤ lam} = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        rintro ⟨x, hxfr, hxH⟩
        exact hne ⟨x, hCcl.frontier_subset hxfr, hxH⟩
      rw [hEmp]
      exact isPreconnected_empty

end

end Work.Drive.Mono
