import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.exists_planeCurve_of_avoids_infty

/-!
# A point off finitely many simple closed curves of the Riemann sphere

This file proves `Work.Smooth.SphereJordan.exists_notMem_iUnion_range`: for a finite family of
simple closed curves `c i` of the Riemann sphere `ℂ ∪ {∞}` there is a point of the sphere which
lies on none of them.

The mathematical content is that the trace of a simple closed curve has empty interior — an arc
cannot fill an open set — together with the standard finite-intersection argument for dense open
sets.  The scheme of the empty-interior statement is the following.

Let `K` be the trace of a simple closed curve `c` and suppose `K` has nonempty interior.  Then `K`
contains an open *plane* ball `O = ↑ '' Metric.ball w ε` with `z = ↑w ∈ O`.  Since `O ≠ K`
(otherwise the periodic plane lift `γ : ℝ → ℂ` of `c` would have as its range the ball
`Metric.ball w ε`; that range is compact, hence closed, whereas a ball is not closed in `ℂ`) there
is a parameter `τ` with `c τ ∉ O`.  Cutting the parameter circle at `τ` writes `K` as the union of
the two compact pieces `c '' Icc τ u` and `c '' Icc u (τ + 2π)`, where `u` is a parameter of `z`
with `τ < u < τ + 2π`; the two pieces meet exactly in `{c τ, z}`.  Since `c τ ∉ O` and
`z ∉ O \ {z}`, they separate `O \ {z}` into two disjoint sets which are closed in `O \ {z}` and both
meet it.  But `O \ {z} = ↑ '' (Metric.ball w ε \ {w})` is preconnected, being the image of the
centre-punctured ball of `ℂ`, which in turn is a continuous image of the punctured plane `{0}ᶜ`
(connected in real dimension `> 1`).
-/

open Set Filter

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## The centre-punctured ball of `ℂ` -/

/-- **The centre-punctured ball of `ℂ` is preconnected.**

The map `v ↦ z + v * (ε / (1 + ‖v‖))` is a continuous surjection of `ℂ` onto the open ball
`Metric.ball z ε` which sends `0` to `z`; restricting it to the complement of `0` — which is path
connected because `ℂ` has real dimension `2` — exhibits `Metric.ball z ε \ {z}` as a continuous
image of a preconnected set. -/
theorem isPreconnected_ball_diff_center {z : ℂ} {ε : ℝ} (hε : 0 < ε) :
    IsPreconnected (Metric.ball z ε \ {z}) := by
  have hpre : IsPreconnected ({0}ᶜ : Set ℂ) :=
    ((isPathConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num) (0 : ℂ)).isConnected).isPreconnected
  have hcont : Continuous (fun v : ℂ => z + v * ((ε / (1 + ‖v‖) : ℝ) : ℂ)) := by
    refine continuous_const.add (continuous_id.mul ?_)
    exact Complex.continuous_ofReal.comp
      (continuous_const.div (continuous_const.add continuous_norm) (fun v => by positivity))
  have himg : (fun v : ℂ => z + v * ((ε / (1 + ‖v‖) : ℝ) : ℂ)) '' ({0}ᶜ : Set ℂ)
      = Metric.ball z ε \ {z} := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hden : 0 < 1 + ‖v‖ := by positivity
      have hnorm : ‖v * ((ε / (1 + ‖v‖) : ℝ) : ℂ)‖ < ε := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hε hden),
          ← mul_div_assoc, div_lt_iff₀ hden]
        nlinarith
      have hq : v * ((ε / (1 + ‖v‖) : ℝ) : ℂ) ≠ 0 := by
        intro h0
        have h1 : ‖v * ((ε / (1 + ‖v‖) : ℝ) : ℂ)‖ = 0 := by rw [h0, norm_zero]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hε hden)] at h1
        have hpos : (0 : ℝ) < ε / (1 + ‖v‖) := div_pos hε hden
        have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
        nlinarith
      constructor
      · simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using hnorm
      · simp only [mem_singleton_iff]
        intro hcon
        have h : v * ((ε / (1 + ‖v‖) : ℝ) : ℂ) = 0 := by
          have := congrArg (fun x : ℂ => x - z) hcon
          simpa using this
        exact hq h
    · rintro ⟨hw, hwne⟩
      have hd : 0 < ε - ‖w - z‖ := by
        have h := hw; rw [Metric.mem_ball, dist_eq_norm] at h; linarith
      have hwz : w - z ≠ 0 := by
        intro h
        exact hwne (by simp only [mem_singleton_iff]; exact sub_eq_zero.mp h)
      refine ⟨(w - z) * (((ε - ‖w - z‖)⁻¹ : ℝ) : ℂ), ?_, ?_⟩
      · simp only [mem_compl_iff, mem_singleton_iff]
        intro h0
        rcases mul_eq_zero.mp h0 with h | h
        · exact hwz h
        · exact absurd h (Complex.ofReal_ne_zero.mpr (inv_ne_zero (ne_of_gt hd)))
      · have hnormv :
            ‖(w - z) * (((ε - ‖w - z‖)⁻¹ : ℝ) : ℂ)‖ = ‖w - z‖ / (ε - ‖w - z‖) := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd),
            inv_eq_one_div, mul_one_div]
        have h1 : (1 + ‖(w - z) * (((ε - ‖w - z‖)⁻¹ : ℝ) : ℂ)‖ : ℝ)
            = ε / (ε - ‖w - z‖) := by
          rw [hnormv]; field_simp; try ring
        have h2 : (ε / (1 + ‖(w - z) * (((ε - ‖w - z‖)⁻¹ : ℝ) : ℂ)‖) : ℝ)
            = ε - ‖w - z‖ := by
          rw [h1]; field_simp; try ring
        have hne : (((ε - ‖w - z‖) : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (ne_of_gt hd)
        change z + ((w - z) * (((ε - ‖w - z‖)⁻¹ : ℝ) : ℂ)) *
          ((ε / (1 + ‖(w - z) * (((ε - ‖w - z‖)⁻¹ : ℝ) : ℂ)‖) : ℝ) : ℂ) = w
        rw [h2, Complex.ofReal_inv, mul_assoc, inv_mul_cancel₀ hne, mul_one]
        ring
  rw [← himg]
  exact hpre.image _ hcont.continuousOn

/-! ## Parameters of equal points differ by a period -/

/-- Two parameters giving the same point of the curve differ by an integral multiple of `2π`. -/
theorem sub_mem_zsmul_of_apply_eq {c : ℝ → RiemannSphere} (hc : IsSimpleClosedCurve c)
    {a b : ℝ} (h : c a = c b) : ∃ k : ℤ, b - a = (k : ℝ) * (2 * Real.pi) := by
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  obtain ⟨m, hmI, -⟩ := existsUnique_add_zsmul_mem_Ico (G := ℝ) hT a 0
  obtain ⟨n, hnI, -⟩ := existsUnique_add_zsmul_mem_Ico (G := ℝ) hT b 0
  have e1 : c (a + (m : ℝ) * (2 * Real.pi)) = c a := by
    have := hc.periodic.zsmul m a
    simpa [zsmul_eq_mul] using this
  have e2 : c (b + (n : ℝ) * (2 * Real.pi)) = c b := by
    have := hc.periodic.zsmul n b
    simpa [zsmul_eq_mul] using this
  have hmI' : a + (m : ℝ) * (2 * Real.pi) ∈ Set.Ico 0 (2 * Real.pi) := by
    simpa [zsmul_eq_mul] using hmI
  have hnI' : b + (n : ℝ) * (2 * Real.pi) ∈ Set.Ico 0 (2 * Real.pi) := by
    simpa [zsmul_eq_mul] using hnI
  have heq : a + (m : ℝ) * (2 * Real.pi) = b + (n : ℝ) * (2 * Real.pi) := by
    refine hc.injOn hmI' hnI' ?_
    rw [e1, e2]; exact h
  refine ⟨m - n, ?_⟩
  push_cast
  linarith [heq]

/-- Parameters at distance `< 2π` giving the same point of the curve coincide. -/
theorem eq_of_apply_eq_of_abs_lt {c : ℝ → RiemannSphere} (hc : IsSimpleClosedCurve c)
    {a b : ℝ} (h : c a = c b) (hab : |b - a| < 2 * Real.pi) : a = b := by
  obtain ⟨k, hk⟩ := sub_mem_zsmul_of_apply_eq hc h
  have habs : |(k : ℝ) * (2 * Real.pi)| < 2 * Real.pi := by rw [← hk]; exact hab
  have habs2pi : |(k : ℝ) * (2 * Real.pi)| = |(k : ℝ)| * (2 * Real.pi) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  rw [habs2pi] at habs
  have habs' : |(k : ℝ)| < 1 := by nlinarith [habs, Real.pi_pos]
  obtain ⟨habs1, habs2⟩ := abs_lt.mp habs'
  have hk1 : k < 1 := by exact_mod_cast habs2
  have hk2 : -1 < k := by exact_mod_cast habs1
  have hk0 : k = 0 := by omega
  rw [hk0] at hk
  have : b - a = 0 := by simpa using hk
  linarith

/-! ## A chart ball lying in the trace of a curve is a proper subset of it -/

/-- **A chart ball contained in the trace of a simple closed curve is not all of it.**

Otherwise the periodic plane lift `γ` of `c` would have range the ball `Metric.ball w ε`; that
range is compact, hence closed, while a ball is not closed in `ℂ`. -/
theorem coe_ball_image_ne_range {c : ℝ → RiemannSphere} (hc : IsSimpleClosedCurve c)
    {w : ℂ} {ε : ℝ} (hε : 0 < ε) :
    (↑) '' Metric.ball w ε ≠ Set.range c := by
  intro heq
  have hinf : ∀ t : ℝ, c t ≠ infty := by
    intro t ht
    have : infty ∈ (↑) '' Metric.ball w ε := by rw [heq]; exact ⟨t, ht⟩
    exact OnePoint.infty_notMem_image_coe this
  obtain ⟨γ, hγcont, hγper, -, hγc⟩ := exists_planeCurve_of_avoids_infty hc hinf
  have hrangeγ : Set.range γ = Metric.ball w ε := by
    apply Subset.antisymm
    · rintro v ⟨t, rfl⟩
      have hmem : (γ t : RiemannSphere) ∈ (↑) '' Metric.ball w ε := by
        rw [← hγc t, heq]; exact ⟨t, rfl⟩
      obtain ⟨v', hv', hv'eq⟩ := hmem
      rwa [← OnePoint.coe_eq_coe.mp hv'eq]
    · intro v hv
      have hmem : (v : RiemannSphere) ∈ Set.range c := by rw [← heq]; exact ⟨v, hv, rfl⟩
      obtain ⟨t, ht⟩ := hmem
      exact ⟨t, OnePoint.coe_eq_coe.mp (by rw [← hγc t]; exact ht)⟩
  have hclosed : IsClosed (Metric.ball w ε) := by
    rw [← hrangeγ, ← hγper.image_Icc (by positivity : (0 : ℝ) < 2 * Real.pi) 0]
    exact (isCompact_Icc.image hγcont).isClosed
  have hclosure : closure (Metric.ball w ε) = Metric.ball w ε := hclosed.closure_eq
  rw [closure_ball w (ne_of_gt hε)] at hclosure
  have hmem : w + (ε : ℂ) ∈ Metric.closedBall w ε := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hε]
  rw [hclosure] at hmem
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hε] at hmem
  exact absurd hmem (lt_irrefl ε)

/-! ## The trace of a simple closed curve has empty interior -/

/-- **The trace of a simple closed curve of the Riemann sphere has empty interior.** -/
theorem interior_range_empty {c : ℝ → RiemannSphere} (hc : IsSimpleClosedCurve c) :
    interior (Set.range c) = ∅ := by
  by_contra hne
  obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hne
  -- an interior point of the finite part of the sphere
  have hfin : ∃ w : ℂ, (w : RiemannSphere) ∈ interior (Set.range c) := by
    by_cases h : ∃ w : ℂ, (w : RiemannSphere) ∈ interior (Set.range c)
    · exact h
    · exfalso
      push Not at h
      have hsubset : interior (Set.range c) ⊆ ({infty} : Set RiemannSphere) := by
        intro x hx
        by_contra hx'
        have hxr : x ∈ Set.range ((↑) : ℂ → RiemannSphere) := by
          rw [← OnePoint.compl_infty]
          exact hx'
        obtain ⟨w, hw⟩ := hxr
        exact h w (hw ▸ hx)
      have hmeminf : infty ∈ interior (Set.range c) := by
        by_cases hy' : y = infty
        · exact hy' ▸ hy
        · obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp hy'
          exact absurd (hw ▸ hy) (h w)
      have hsingle : interior (Set.range c) = {infty} :=
        le_antisymm hsubset (Set.singleton_subset_iff.mpr hmeminf)
      have hopen : IsOpen ({infty} : Set RiemannSphere) := hsingle ▸ isOpen_interior
      have hclosed : IsClosed (Set.range ((↑) : ℂ → RiemannSphere)) := by
        rw [← OnePoint.compl_infty]; exact hopen.isClosed_compl
      have hmem : infty ∈ closure (Set.range ((↑) : ℂ → RiemannSphere)) := by
        rw [OnePoint.denseRange_coe.closure_eq]; trivial
      rw [hclosed.closure_eq] at hmem
      exact OnePoint.infty_notMem_range_coe hmem
  obtain ⟨w₀, hw₀⟩ := hfin
  obtain ⟨ε, hε, hεball⟩ :=
    Metric.mem_nhds_iff.mp ((isOpen_interior.preimage OnePoint.continuous_coe).mem_nhds hw₀)
  set O : Set RiemannSphere := (↑) '' Metric.ball w₀ ε with hOdef
  have hOsub : O ⊆ Set.range c := by
    rintro x ⟨v, hv, rfl⟩
    exact interior_subset (hεball hv)
  have hOopen : IsOpen O := OnePoint.isOpenMap_coe _ Metric.isOpen_ball
  set z : RiemannSphere := (w₀ : RiemannSphere) with hzdef
  have hzO : z ∈ O := ⟨w₀, Metric.mem_ball_self hε, rfl⟩
  -- a parameter whose image lies outside the chart ball
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, c τ ∉ O := by
    by_contra h
    push Not at h
    refine coe_ball_image_ne_range hc hε (Set.Subset.antisymm hOsub ?_)
    intro x hx
    obtain ⟨τ, rfl⟩ := hx
    exact h τ
  -- a parameter `u` of `z` with `τ < u < τ + 2π`
  have hzmem : z ∈ Set.range c := hOsub hzO
  obtain ⟨s, hs⟩ := hzmem
  obtain ⟨u, huIco, hu⟩ :=
    hc.periodic.exists_mem_Ico (by positivity : (0 : ℝ) < 2 * Real.pi) s τ
  have hcu : c u = z := by rw [← hu, hs]
  have hut : u ≠ τ := by
    intro h; exact hτ (h ▸ hcu ▸ hzO)
  have hτu : τ < u := lt_of_le_of_ne huIco.1 hut.symm
  have hu2pi : u < τ + 2 * Real.pi := huIco.2
  -- an interval around `u` mapped into `O`
  obtain ⟨δ, hδpos, hδsub⟩ : ∃ δ > 0, ∀ s : ℝ, dist s u < δ → c s ∈ O := by
    have hmem : c ⁻¹' O ∈ nhds u :=
      (hOopen.preimage hc.continuous).mem_nhds (by show c u ∈ O; rw [hcu]; exact hzO)
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hmem
    exact ⟨δ, hδpos, fun s hs => hδsub (by rwa [Metric.mem_ball])⟩
  set δ' : ℝ := min δ (min ((u - τ) / 2) ((τ + 2 * Real.pi - u) / 2)) with hδ'def
  have hδ'pos : 0 < δ' := by
    rw [hδ'def]; exact lt_min hδpos (lt_min (by linarith) (by linarith))
  have hδ'le : δ' ≤ δ := by rw [hδ'def]; exact min_le_left _ _
  have hδ'lt1 : δ' < u - τ := by
    have h1 := min_le_right δ (min ((u - τ) / 2) ((τ + 2 * Real.pi - u) / 2))
    have h2 : min ((u - τ) / 2) ((τ + 2 * Real.pi - u) / 2) ≤ (u - τ) / 2 := min_le_left _ _
    linarith
  have hδ'lt2 : δ' < τ + 2 * Real.pi - u := by
    have h1 := min_le_right δ (min ((u - τ) / 2) ((τ + 2 * Real.pi - u) / 2))
    have h2 : min ((u - τ) / 2) ((τ + 2 * Real.pi - u) / 2) ≤ (τ + 2 * Real.pi - u) / 2 :=
      min_le_right _ _
    linarith
  set s₁ : ℝ := u - δ' / 2 with hs₁def
  set s₂ : ℝ := u + δ' / 2 with hs₂def
  have hs₁dist : dist s₁ u < δ := by
    rw [Real.dist_eq, hs₁def, show u - δ' / 2 - u = -(δ' / 2) by ring, abs_neg,
      abs_of_pos (by linarith : (0 : ℝ) < δ' / 2)]
    linarith
  have hs₂dist : dist s₂ u < δ := by
    rw [Real.dist_eq, hs₂def, show u + δ' / 2 - u = δ' / 2 by ring,
      abs_of_pos (by linarith : (0 : ℝ) < δ' / 2)]
    linarith
  have hs₁O : c s₁ ∈ O := hδsub s₁ hs₁dist
  have hs₂O : c s₂ ∈ O := hδsub s₂ hs₂dist
  have hs₁I : s₁ ∈ Set.Icc τ u := ⟨by rw [hs₁def]; linarith, by rw [hs₁def]; linarith⟩
  have hs₂I : s₂ ∈ Set.Icc u (τ + 2 * Real.pi) :=
    ⟨by rw [hs₂def]; linarith, by rw [hs₂def]; linarith⟩
  have hs₁ne : c s₁ ≠ z := by
    intro hsz
    have h1 : |u - s₁| < 2 * Real.pi := by
      rw [hs₁def, show u - (u - δ' / 2) = δ' / 2 by ring,
        abs_of_pos (by linarith : (0 : ℝ) < δ' / 2)]
      linarith
    have : s₁ = u := eq_of_apply_eq_of_abs_lt hc (by rw [hsz, hcu]) h1
    rw [hs₁def] at this
    linarith
  have hs₂ne : c s₂ ≠ z := by
    intro hsz
    have h1 : |u - s₂| < 2 * Real.pi := by
      rw [hs₂def, show u - (u + δ' / 2) = -(δ' / 2) by ring, abs_neg,
        abs_of_pos (by linarith : (0 : ℝ) < δ' / 2)]
      linarith
    have : s₂ = u := eq_of_apply_eq_of_abs_lt hc (by rw [hsz, hcu]) h1
    rw [hs₂def] at this
    linarith
  -- the two arcs through `z`
  have hclosed₁ : IsClosed (c '' Set.Icc τ u) := (isCompact_Icc.image hc.continuous).isClosed
  have hclosed₂ : IsClosed (c '' Set.Icc u (τ + 2 * Real.pi)) :=
    (isCompact_Icc.image hc.continuous).isClosed
  have hcover : O \ {z} ⊆ c '' Set.Icc τ u ∪ c '' Set.Icc u (τ + 2 * Real.pi) := by
    intro x hx
    have hxK : x ∈ Set.range c := hOsub hx.1
    have hper : c '' Set.Icc τ (τ + 2 * Real.pi) = Set.range c :=
      hc.periodic.image_Icc (by positivity : (0 : ℝ) < 2 * Real.pi) τ
    rw [← hper] at hxK
    obtain ⟨t', ht'I, ht'eq⟩ := hxK
    rw [← Set.Icc_union_Icc_eq_Icc huIco.1 (le_of_lt huIco.2)] at ht'I
    rcases ht'I with h | h
    · exact Or.inl ⟨t', h, ht'eq⟩
    · exact Or.inr ⟨t', h, ht'eq⟩
  have hpieces : c '' Set.Icc τ u ∩ c '' Set.Icc u (τ + 2 * Real.pi) ⊆ {c τ, z} := by
    rintro x ⟨⟨a, haI, ha⟩, ⟨b, hbI, hb⟩⟩
    have hba : 0 ≤ b - a := by linarith [haI.2, hbI.1]
    have hba' : b - a ≤ 2 * Real.pi := by linarith [haI.1, hbI.2]
    obtain ⟨k, hk⟩ := sub_mem_zsmul_of_apply_eq hc (by rw [ha, hb] : c a = c b)
    have hk01 : k = 0 ∨ k = 1 := by
      have h0 : (0 : ℝ) ≤ (k : ℝ) := by nlinarith [hk, hba, Real.pi_pos]
      have h1 : (k : ℝ) ≤ 1 := by nlinarith [hk, hba', Real.pi_pos]
      have hk0 : (0 : ℤ) ≤ k := by exact_mod_cast h0
      have hk1 : k ≤ 1 := by exact_mod_cast h1
      omega
    rcases hk01 with hk0 | hk0
    · have hab : a = b := by
        rw [hk0] at hk
        simp only [Int.cast_zero, zero_mul] at hk
        linarith
      have hau : a = u := by
        rw [← hab] at hbI
        exact le_antisymm haI.2 hbI.1
      refine Or.inr (by simp only [mem_singleton_iff]; rw [← ha, hau, hcu])
    · have hb : b = a + 2 * Real.pi := by
        rw [hk0] at hk
        push_cast at hk
        linarith
      have haτ : a = τ := by linarith [haI.1, hbI.2, hb]
      refine Or.inl ?_
      rw [← ha, haτ]
  have hdisj : (O \ {z}) ∩ (c '' Set.Icc τ u ∩ c '' Set.Icc u (τ + 2 * Real.pi)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨⟨hxO, hxz⟩, hxP⟩
    rcases hpieces hxP with h | h
    · exact hτ (h ▸ hxO)
    · exact hxz h
  -- `O \ {z}` is preconnected
  have hpreO : IsPreconnected (O \ {z}) := by
    have hset : O \ {z} = (↑) '' (Metric.ball w₀ ε \ {w₀}) := by
      rw [hOdef, hzdef]
      ext x
      constructor
      · rintro ⟨⟨v, hv, rfl⟩, hxz⟩
        refine ⟨v, ⟨hv, ?_⟩, rfl⟩
        intro hv0
        have hv0' : v = w₀ := by simpa using hv0
        exact hxz (by simp only [mem_singleton_iff, hv0'])
      · rintro ⟨v, ⟨hv, hv0⟩, rfl⟩
        refine ⟨⟨v, hv, rfl⟩, fun h => ?_⟩
        exact hv0 (OnePoint.coe_eq_coe.mp (by simpa only [mem_singleton_iff] using h))
    rw [hset]
    exact (isPreconnected_ball_diff_center hε).image _ OnePoint.continuous_coe.continuousOn
  rw [isPreconnected_iff_subset_of_disjoint_closed] at hpreO
  rcases hpreO _ _ hclosed₁ hclosed₂ hcover hdisj with hsub | hsub
  · have hmem : c s₂ ∈ (O \ {z}) ∩ (c '' Set.Icc τ u ∩ c '' Set.Icc u (τ + 2 * Real.pi)) :=
      ⟨⟨hs₂O, hs₂ne⟩, hsub ⟨hs₂O, hs₂ne⟩, ⟨s₂, hs₂I, rfl⟩⟩
    rw [hdisj] at hmem
    exact hmem
  · have hmem : c s₁ ∈ (O \ {z}) ∩ (c '' Set.Icc τ u ∩ c '' Set.Icc u (τ + 2 * Real.pi)) :=
      ⟨⟨hs₁O, hs₁ne⟩, ⟨s₁, hs₁I, rfl⟩, hsub ⟨hs₁O, hs₁ne⟩⟩
    rw [hdisj] at hmem
    exact hmem

/-! ## A point off finitely many curves -/

/-- **A finite family of simple closed curves of the Riemann sphere misses a point.** -/
theorem exists_notMem_iUnion_range {ι : Type} [Fintype ι] (c : ι → ℝ → RiemannSphere)
    (hc : ∀ i, IsSimpleClosedCurve (c i)) :
    ∃ x : RiemannSphere, ∀ i : ι, x ∉ Set.range (c i) := by
  have hclosed : ∀ i : ι, IsClosed (Set.range (c i)) := by
    intro i
    rw [← (hc i).periodic.image_Icc (by positivity : (0 : ℝ) < 2 * Real.pi) 0]
    exact (isCompact_Icc.image (hc i).continuous).isClosed
  have hdense : ∀ i : ι, Dense ((Set.range (c i))ᶜ) := by
    intro i
    rw [dense_iff_closure_eq, closure_compl, interior_range_empty (c := c i) (hc i)]
    simp
  have hdenseall : Dense (⋂₀ Set.range (fun i : ι => (Set.range (c i))ᶜ)) :=
    Set.Finite.dense_sInter (Set.finite_range _)
      (by rintro t ⟨i, rfl⟩; exact (hclosed i).isOpen_compl)
      (by rintro t ⟨i, rfl⟩; exact hdense i)
  obtain ⟨x, hx⟩ := hdenseall.nonempty
  refine ⟨x, fun i => ?_⟩
  exact Set.mem_sInter.mp hx _ (Set.mem_range_self i)

end

end Work.Smooth.SphereJordan
