import Mathlib
import Submission.Work.Smooth.SphereJordan.jsepExists
import Submission.Work.Smooth.SphereJordan.Caratheodory.CapSetup
import Submission.Work.Smooth.SphereJordan.Caratheodory.TopologyAux
import Submission.Work.Smooth.SphereJordan.Caratheodory.Jacobian
import Submission.Work.Smooth.SphereJordan.Caratheodory.LengthArea

/-!
# The cap argument of the Carathéodory boundary correspondence

This file assembles the Garnett–Marshall uniform-continuity argument for the Riemann map
`f : 𝔻 → Ω` of a Jordan domain:

* `capLimits_mem_frontier` — the two limiting points of the image of the cap arc lie on `∂Ω`;
* `diam_lens_le` (**main**) — for every `ε > 0` there is `s ∈ (0, 1/2)` such that the image of the
  lens `𝔻 ∩ ball 1 s` has diameter at most `ε`.

The proof of the main result: the arc is closed up into a Jordan curve by a short sub-arc of `γ`
(`exists_short_arc`); the bounded side of that Jordan curve is contained in `Ω`
(`JSep.V_subset_of_disjoint_trace`) and has diameter at most the diameter of the curve, which is
small; it cannot be the side containing `f '' outerLens` (whose diameter is bounded below by a
positive constant), so it is the side containing the lens.
-/

noncomputable section
open Set Metric Filter
open scoped Topology

namespace Work.Smooth.SphereJordan.Caratheodory

theorem capPt_neg_capAlpha_mem_sphere {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    capPt s (-(capAlpha s)) ∈ Metric.sphere (0 : ℂ) 1 := by
  have h := capArcPath_mem_sphere hs hs2 ⟨0, by norm_num⟩ (Or.inl rfl)
  rwa [capArcPath_zero] at h

theorem capPt_capAlpha_mem_sphere {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    capPt s (capAlpha s) ∈ Metric.sphere (0 : ℂ) 1 := by
  have h := capArcPath_mem_sphere hs hs2 ⟨1, by norm_num⟩ (Or.inr rfl)
  rwa [capArcPath_one] at h

/-- **The two limiting points of the image of the cap arc lie on `∂Ω`.** -/
theorem capLimits_mem_frontier {Ω : Set ℂ} {γ : ℝ → ℂ} (hΩo : IsOpen Ω)
    (hfr : frontier Ω = Set.range γ) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1)) {g : ℂ → ℂ} (hg : ContinuousOn g Ω)
    (hgf : ∀ w ∈ Metric.ball (0 : ℂ) 1, g (f w) = w)
    (hgmem : Set.MapsTo g Ω (Metric.ball (0 : ℂ) 1))
    (himg : f '' Metric.ball (0 : ℂ) 1 = Ω)
    {s : ℝ} (hs : 0 < s) (hs2 : s < 2) (hfin : capLen f s < ⊤) :
    ∃ a b : ℂ, a ∈ frontier Ω ∧ b ∈ frontier Ω ∧
      Tendsto (fun τ => f (capPt s τ)) (𝓝[>] (-(capAlpha s))) (𝓝 a) ∧
      Tendsto (fun τ => f (capPt s τ)) (𝓝[<] (capAlpha s)) (𝓝 b) ∧
      ‖a - b‖ ≤ (capLen f s).toReal := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_tendsto_capPt hf hs hs2 hfin
  have hα : 0 < capAlpha s := capAlpha_pos hs2
  have hnear : ∀ᶠ τ in 𝓝[>] (-(capAlpha s)), capPt s τ ∈ Metric.ball (0 : ℂ) 1 := by
    have h1 : ∀ᶠ τ in 𝓝[>] (-(capAlpha s)), τ < capAlpha s :=
      (nhdsWithin_le_nhds : 𝓝[Set.Ioi (-(capAlpha s))] (-(capAlpha s)) ≤ 𝓝 (-(capAlpha s)))
        (IsOpen.mem_nhds isOpen_Iio (by linarith : -(capAlpha s) < capAlpha s))
    have h2 : ∀ᶠ τ in 𝓝[>] (-(capAlpha s)), -(capAlpha s) < τ :=
      (self_mem_nhdsWithin : Set.Ioi (-(capAlpha s)) ∈ 𝓝[>] (-(capAlpha s)))
    filter_upwards [h1, h2] with τ hτ hτ'
    exact capPt_mem_ball_of_mem_Ioo hs hs2 ⟨hτ', hτ⟩
  have key : ∀ {c : ℂ}, Tendsto (fun τ => f (capPt s τ)) (𝓝[>] (-(capAlpha s))) (𝓝 c) →
      c ∉ Ω := by
    intro c hc hcΩ
    -- `g ∘ f ∘ capPt` is both `capPt` and eventually equal to the constant `g c`
    have h1 : Tendsto (fun τ => g (f (capPt s τ))) (𝓝[>] (-(capAlpha s))) (𝓝 (g c)) :=
      Filter.Tendsto.comp (hg.continuousAt (hΩo.mem_nhds hcΩ)) hc
    have h2 : Tendsto (fun τ => capPt s τ) (𝓝[>] (-(capAlpha s))) (𝓝 (g c)) :=
      h1.congr' (hnear.mono fun τ hτ => (hgf (capPt s τ) hτ))
    have h3 : Tendsto (fun τ => capPt s τ) (𝓝[>] (-(capAlpha s)))
        (𝓝 (capPt s (-(capAlpha s)))) :=
      ((continuous_capPt s).tendsto (-(capAlpha s))).mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (-(capAlpha s)) ≤ 𝓝 (-(capAlpha s)))
    have heq : g c = capPt s (-(capAlpha s)) := tendsto_nhds_unique h2 h3
    have h4 : g c ∈ Metric.ball (0 : ℂ) 1 := hgmem hcΩ
    rw [Metric.mem_ball, dist_zero_right] at h4
    have h5 : ‖capPt s (-(capAlpha s))‖ = 1 := by
      have := capPt_neg_capAlpha_mem_sphere hs hs2
      rwa [Metric.mem_sphere, dist_zero_right] at this
    rw [heq, h5] at h4
    exact lt_irrefl 1 h4
  have hsub : ∀ᶠ τ in 𝓝[>] (-(capAlpha s)), f (capPt s τ) ∈ closure Ω :=
    hnear.mono fun τ hτ => subset_closure (by rw [← himg]; exact ⟨capPt s τ, hτ, rfl⟩)
  have hb' : ∀ᶠ τ in 𝓝[<] (capAlpha s), capPt s τ ∈ Metric.ball (0 : ℂ) 1 := by
    have h1 : ∀ᶠ τ in 𝓝[<] (capAlpha s), -(capAlpha s) < τ :=
      (nhdsWithin_le_nhds : 𝓝[Set.Iio (capAlpha s)] (capAlpha s) ≤ 𝓝 (capAlpha s))
        (IsOpen.mem_nhds isOpen_Ioi (by linarith : -(capAlpha s) < capAlpha s))
    have h2 : ∀ᶠ τ in 𝓝[<] (capAlpha s), τ < capAlpha s :=
      (self_mem_nhdsWithin : Set.Iio (capAlpha s) ∈ 𝓝[<] (capAlpha s))
    filter_upwards [h1, h2] with τ hτ hτ'
    exact capPt_mem_ball_of_mem_Ioo hs hs2 ⟨hτ, hτ'⟩
  have key' : ∀ {c : ℂ}, Tendsto (fun τ => f (capPt s τ)) (𝓝[<] (capAlpha s)) (𝓝 c) →
      c ∉ Ω := by
    intro c hc hcΩ
    have h1 : Tendsto (fun τ => g (f (capPt s τ))) (𝓝[<] (capAlpha s)) (𝓝 (g c)) :=
      Filter.Tendsto.comp (hg.continuousAt (hΩo.mem_nhds hcΩ)) hc
    have h2 : Tendsto (fun τ => capPt s τ) (𝓝[<] (capAlpha s)) (𝓝 (g c)) :=
      h1.congr' (hb'.mono fun τ hτ => (hgf (capPt s τ) hτ))
    have h3 : Tendsto (fun τ => capPt s τ) (𝓝[<] (capAlpha s)) (𝓝 (capPt s (capAlpha s))) :=
      ((continuous_capPt s).tendsto (capAlpha s)).mono_left
        (nhdsWithin_le_nhds : 𝓝[<] (capAlpha s) ≤ 𝓝 (capAlpha s))
    have heq : g c = capPt s (capAlpha s) := tendsto_nhds_unique h2 h3
    have h4 : g c ∈ Metric.ball (0 : ℂ) 1 := hgmem hcΩ
    rw [Metric.mem_ball, dist_zero_right] at h4
    have h5 : ‖capPt s (capAlpha s)‖ = 1 := by
      have := capPt_capAlpha_mem_sphere hs hs2
      rwa [Metric.mem_sphere, dist_zero_right] at this
    rw [heq, h5] at h4
    exact lt_irrefl 1 h4
  refine ⟨a, b, ?_, ?_, ha, hb, hab⟩
  · have h1 : a ∈ closure Ω := isClosed_closure.mem_of_tendsto ha hsub
    rw [closure_eq_self_union_frontier] at h1
    rcases h1 with h | h
    · exact absurd h (key ha)
    · exact h
  · have h1 : b ∈ closure Ω := isClosed_closure.mem_of_tendsto hb
        (hb'.mono fun τ hτ => subset_closure (by rw [← himg]; exact ⟨capPt s τ, hτ, rfl⟩))
    rw [closure_eq_self_union_frontier] at h1
    rcases h1 with h | h
    · exact absurd h (key' hb)
    · exact h

/-- **The image of the cap arc has diameter at most its length `capLen f s`.** -/
theorem diam_image_capArc_le {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1))
    {s : ℝ} (hs : 0 < s) (hs2 : s < 2) (hfin : capLen f s < ⊤) :
    Metric.diam (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s))) ≤
      (capLen f s).toReal := by
  refine Metric.diam_le_of_forall_dist_le (by positivity) fun u hu v hv => ?_
  obtain ⟨x, ⟨τ, hτ, rfl⟩, rfl⟩ := hu
  obtain ⟨y, ⟨τ', hτ', rfl⟩, rfl⟩ := hv
  rw [dist_eq_norm]
  rcases le_total τ τ' with hle | hle
  · refine le_trans ?_ (integral_capPt_le_capLen hs hfin hτ.1 hτ'.2 hle)
    rw [norm_sub_rev]
    exact norm_sub_le_integral_capPt hf hs hs2 hτ.1 hle hτ'.2
  · refine le_trans ?_ (integral_capPt_le_capLen hs hfin hτ'.1 hτ.2 hle)
    exact norm_sub_le_integral_capPt hf hs hs2 hτ'.1 hle hτ.2

/-- The cap arc closed up by its two limiting values. -/
def capExtend (f : ℂ → ℂ) (s : ℝ) (a b : ℂ) : ℝ → ℂ :=
  fun τ => if τ ≤ -(capAlpha s) then a else if capAlpha s ≤ τ then b else f (capPt s τ)

/-- **The cap arc extended by its limiting values is continuous.** -/
theorem continuous_capExtend {f : ℂ → ℂ} {s : ℝ} {a b : ℂ}
    (ha : Tendsto (fun τ => f (capPt s τ)) (𝓝[>] (-(capAlpha s))) (𝓝 a))
    (hb : Tendsto (fun τ => f (capPt s τ)) (𝓝[<] (capAlpha s)) (𝓝 b))
    (hα : 0 < capAlpha s) (hf : Continuous f) :
    Continuous (capExtend f s a b) := by
  rw [continuous_iff_continuousAt]
  intro τ
  rcases lt_trichotomy τ (-(capAlpha s)) with h | h | h
  · -- `τ < -α`: locally equal to the constant `a`
    refine (continuousAt_const (y := a)).congr ?_
    filter_upwards [IsOpen.mem_nhds isOpen_Iio h] with τ' hτ'
    have h1 : τ' < -(capAlpha s) := hτ'
    simp only [capExtend, if_pos h1.le]
  · -- `τ = -α`: glue the constant `a` (on the left) with the one-sided limit `ha`
    subst h
    show Tendsto (capExtend f s a b) (𝓝 (-(capAlpha s)))
      (𝓝 (capExtend f s a b (-(capAlpha s))))
    rw [show capExtend f s a b (-(capAlpha s)) = a from by
      simp only [capExtend, if_pos le_rfl]]
    rw [← nhdsWithin_univ, ← Set.Iic_union_Ioi (a := -(capAlpha s)), nhdsWithin_union]
    refine tendsto_sup.mpr ⟨?_, ?_⟩
    · refine (tendsto_const_nhds (x := a)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with τ' hτ'
      have h1 : τ' ≤ -(capAlpha s) := hτ'
      simp only [capExtend, if_pos h1]
    · refine ha.congr' ?_
      have hlt : ∀ᶠ τ' in 𝓝[Set.Ioi (-(capAlpha s))] (-(capAlpha s)), τ' < capAlpha s :=
        (nhdsWithin_le_nhds : 𝓝[Set.Ioi (-(capAlpha s))] (-(capAlpha s)) ≤ 𝓝 (-(capAlpha s)))
          (IsOpen.mem_nhds isOpen_Iio (by linarith : -(capAlpha s) < capAlpha s))
      filter_upwards [self_mem_nhdsWithin, hlt] with τ' h1 h2
      have h1' : -(capAlpha s) < τ' := h1
      have h2' : τ' < capAlpha s := h2
      simp only [capExtend, if_neg (not_le.mpr h1'), if_neg (not_le.mpr h2')]
  · -- `-α < τ`
    rcases lt_or_ge τ (capAlpha s) with h' | h'
    · -- `-α < τ < α`: the plain composition
      refine (((hf.comp (continuous_capPt s))).continuousAt).congr ?_
      filter_upwards [IsOpen.mem_nhds isOpen_Ioi h, IsOpen.mem_nhds isOpen_Iio h'] with τ' hτ' hτ''
      have h1 : -(capAlpha s) < τ' := hτ'
      have h2 : τ' < capAlpha s := hτ''
      simp only [Function.comp_apply, capExtend, if_neg (not_le.mpr h1), if_neg (not_le.mpr h2)]
    · rcases lt_or_eq_of_le h' with h'' | h''
      · -- `τ > α`: locally equal to the constant `b`
        refine (continuousAt_const (y := b)).congr ?_
        filter_upwards [IsOpen.mem_nhds isOpen_Ioi h''] with τ' hτ'
        have h2 : capAlpha s < τ' := hτ'
        have h1 : -(capAlpha s) < τ' :=
          lt_of_lt_of_le (by linarith : -(capAlpha s) < capAlpha s) h2.le
        simp only [capExtend, if_neg (not_le.mpr h1), if_pos h2.le]
      · -- `τ = α`: glue the one-sided limit `hb` with the constant `b`
        subst h''
        show Tendsto (capExtend f s a b) (𝓝 (capAlpha s))
          (𝓝 (capExtend f s a b (capAlpha s)))
        rw [show capExtend f s a b (capAlpha s) = b from by
          simp only [capExtend, if_neg (not_le.mpr h), if_pos le_rfl]]
        rw [← nhdsWithin_univ, ← Set.Iio_union_Ici (a := capAlpha s), nhdsWithin_union]
        refine tendsto_sup.mpr ⟨?_, ?_⟩
        · refine hb.congr' ?_
          have hlt : ∀ᶠ τ' in 𝓝[Set.Iio (capAlpha s)] (capAlpha s), -(capAlpha s) < τ' :=
            (nhdsWithin_le_nhds : 𝓝[Set.Iio (capAlpha s)] (capAlpha s) ≤ 𝓝 (capAlpha s))
              (IsOpen.mem_nhds isOpen_Ioi (by linarith : -(capAlpha s) < capAlpha s))
          filter_upwards [self_mem_nhdsWithin, hlt] with τ' h1 h2
          have h1' : τ' < capAlpha s := h1
          have h2' : -(capAlpha s) < τ' := h2
          simp only [capExtend, if_neg (not_le.mpr h2'), if_neg (not_le.mpr h1')]
        · refine (tendsto_const_nhds (x := b)).congr' ?_
          filter_upwards [self_mem_nhdsWithin] with τ' hτ'
          have h2 : capAlpha s ≤ τ' := hτ'
          have h1 : -(capAlpha s) < τ' :=
            lt_of_lt_of_le (by linarith : -(capAlpha s) < capAlpha s) h2
          simp only [capExtend, if_neg (not_le.mpr h1), if_pos h2]

/-- The range of the extension is the image of the *open* cap arc together with the two limits. -/
theorem range_capExtend {f : ℂ → ℂ} {s : ℝ} {a b : ℂ} (hα : 0 < capAlpha s) :
    Set.range (capExtend f s a b) =
      f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) ∪ {a, b} := by
  ext z
  constructor
  · rintro ⟨τ, rfl⟩
    rcases lt_trichotomy τ (-(capAlpha s)) with h | h | h
    · refine Or.inr (Or.inl ?_)
      rw [capExtend, if_pos h.le]
    · refine Or.inr (Or.inl ?_)
      rw [h, capExtend, if_pos le_rfl]
    · rcases lt_trichotomy τ (capAlpha s) with h' | h' | h'
      · have h1 : -(capAlpha s) < τ := h
        have h2 : τ < capAlpha s := h'
        refine Or.inl ⟨capPt s τ, ⟨⟨τ, ⟨h1, h2⟩, rfl⟩, ?_⟩⟩
        simp only [capExtend, if_neg (not_le.mpr h1), if_neg (not_le.mpr h2)]
      · refine Or.inr (Or.inr ?_)
        have hc : -(capAlpha s) < capAlpha s := by linarith
        rw [h', capExtend, if_neg (not_le.mpr hc), if_pos le_rfl]
        exact Set.mem_singleton b
      · refine Or.inr (Or.inr ?_)
        rw [capExtend, if_neg (not_le.mpr h), if_pos h'.le]
        exact Set.mem_singleton b
  · rintro (⟨y, ⟨σ, hσ, rfl⟩, rfl⟩ | h)
    · have h1 : -(capAlpha s) < σ := hσ.1
      have h2 : σ < capAlpha s := hσ.2
      exact ⟨σ, by simp only [capExtend, if_neg (not_le.mpr h1), if_neg (not_le.mpr h2)]⟩
    · rcases h with h | h
      · exact ⟨-(capAlpha s), by simp only [capExtend, if_pos le_rfl, h]⟩
      · have hc : -(capAlpha s) < capAlpha s := by linarith
        have hz : z = b := h
        exact ⟨capAlpha s, by
          simp only [capExtend, if_neg (not_le.mpr hc), if_pos le_rfl, hz]⟩

/-- **The cap arc as a path from its left limiting value `a` to its right one `b`.** -/
def capArcPathPath (f : ℂ → ℂ) (s : ℝ) (a b : ℂ) (hα : 0 < capAlpha s)
    (hcont : Continuous (capExtend f s a b)) : Path a b where
  toFun t := capExtend f s a b (-(capAlpha s) + (t : ℝ) * (2 * capAlpha s))
  continuous_toFun := hcont.comp (by fun_prop)
  source' := by
    have h : ((0 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 := rfl
    rw [h, zero_mul, add_zero]
    simp only [capExtend, if_pos le_rfl]
  target' := by
    have h : ((1 : Set.Icc (0 : ℝ) 1) : ℝ) = 1 := rfl
    rw [h, one_mul, show -(capAlpha s) + 2 * capAlpha s = capAlpha s by ring]
    have hc : -(capAlpha s) < capAlpha s := by linarith
    simp only [capExtend, if_neg (not_le.mpr hc), if_pos le_rfl]

/-- The range of the cap-arc path is the image of the open arc together with the two limits. -/
theorem range_capArcPathPath {f : ℂ → ℂ} {s : ℝ} {a b : ℂ} (hα : 0 < capAlpha s)
    {hcont : Continuous (capExtend f s a b)} :
    Set.range (capArcPathPath f s a b hα hcont) =
      f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) ∪ {a, b} := by
  rw [← range_capExtend (f := f) (s := s) (a := a) (b := b) hα]
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨t, rfl⟩
    exact ⟨-(capAlpha s) + (t : ℝ) * (2 * capAlpha s), rfl⟩
  · rintro _ ⟨τ, rfl⟩
    rcases lt_or_ge τ (-(capAlpha s)) with h | h
    · -- `τ < -α`: the value is already `a`
      have ha : capExtend f s a b τ = capExtend f s a b (-(capAlpha s)) := by
        rw [show capExtend f s a b τ = a from by rw [capExtend, if_pos h.le]]
        rw [show capExtend f s a b (-(capAlpha s)) = a from by
          rw [capExtend, if_pos le_rfl]]
      refine ⟨⟨0, by norm_num⟩, ?_⟩
      show capExtend f s a b (-(capAlpha s) + ((0 : Set.Icc (0 : ℝ) 1) : ℝ) * (2 * capAlpha s))
        = capExtend f s a b τ
      rw [show ((0 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 from rfl, zero_mul, add_zero]
      exact ha.symm
    · rcases lt_or_ge τ (capAlpha s) with h' | h'
      · -- `-α ≤ τ < α`: solve for the parameter
        refine ⟨⟨(τ + capAlpha s) / (2 * capAlpha s), ?_⟩, ?_⟩
        · rw [Set.mem_Icc]
          constructor
          · apply div_nonneg <;> linarith
          · rw [div_le_one (by linarith)]; linarith
        · show capExtend f s a b
            (-(capAlpha s) + (((τ + capAlpha s) / (2 * capAlpha s) : ℝ)) * (2 * capAlpha s))
            = capExtend f s a b τ
          rw [show -(capAlpha s) + ((τ + capAlpha s) / (2 * capAlpha s)) * (2 * capAlpha s) = τ
            from by field_simp; ring]
      · -- `α ≤ τ`: the value is already `b`
        have hc1 : -(capAlpha s) < τ :=
          lt_of_lt_of_le (by linarith : -(capAlpha s) < capAlpha s) h'
        have hb : capExtend f s a b τ = capExtend f s a b (capAlpha s) := by
          rw [show capExtend f s a b τ = b from by
            rw [capExtend, if_neg (not_le.mpr hc1), if_pos h']]
          rw [show capExtend f s a b (capAlpha s) = b from by
            have hc : -(capAlpha s) < capAlpha s := by linarith
            rw [capExtend, if_neg (not_le.mpr hc), if_pos le_rfl]]
        refine ⟨⟨1, by norm_num⟩, ?_⟩
        show capExtend f s a b (-(capAlpha s) + ((1 : Set.Icc (0 : ℝ) 1) : ℝ) * (2 * capAlpha s))
          = capExtend f s a b τ
        rw [show ((1 : Set.Icc (0 : ℝ) 1) : ℝ) = 1 from rfl, one_mul,
          show -(capAlpha s) + 2 * capAlpha s = capAlpha s by ring]
        exact hb.symm

/-- **A sub-arc of `γ`, as a path from `γ x` to `γ y`.** -/
def arcPathBetween (γ : ℝ → ℂ) (x y : ℝ) (hcont : Continuous γ) : Path (γ x) (γ y) where
  toFun u := γ (x + (u : ℝ) * (y - x))
  continuous_toFun := hcont.comp (by fun_prop)
  source' := by
    show γ (x + ((0 : Set.Icc (0 : ℝ) 1) : ℝ) * (y - x)) = γ x
    rw [show ((0 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 from rfl, zero_mul, add_zero]
  target' := by
    show γ (x + ((1 : Set.Icc (0 : ℝ) 1) : ℝ) * (y - x)) = γ y
    rw [show ((1 : Set.Icc (0 : ℝ) 1) : ℝ) = 1 from rfl, one_mul]
    congr 1
    ring

theorem arcPathBetween_apply (γ : ℝ → ℂ) (x y : ℝ) (hcont : Continuous γ)
    (u : Set.Icc (0 : ℝ) 1) :
    arcPathBetween γ x y hcont u = γ (x + (u : ℝ) * (y - x)) := rfl

/-- The range of the sub-arc path is the image of the corresponding parameter interval. -/
theorem range_arcPathBetween {γ : ℝ → ℂ} {x y : ℝ} (hcont : Continuous γ) (hxy : x < y) :
    Set.range (arcPathBetween γ x y hcont) = γ '' Set.Icc x y := by
  have hpos : 0 < y - x := sub_pos.mpr hxy
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨x + (u : ℝ) * (y - x), ⟨?_, ?_⟩, rfl⟩
    · nlinarith [u.2.1]
    · nlinarith [u.2.2]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨(t - x) / (y - x), ?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith [ht.1]) hpos.le
    · rw [div_le_one hpos]; linarith [ht.2]
    · show γ (x + ((t - x) / (y - x)) * (y - x)) = γ t
      rw [div_mul_cancel₀ _ (ne_of_gt hpos)]
      ring_nf

/-- The sub-arc path is injective as soon as the parameter interval is shorter than the period. -/
theorem arcPathBetween_injective {γ : ℝ → ℂ} (hcont : Continuous γ)
    (hγp : Function.Periodic γ (2 * Real.pi)) (hγi : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    {x y : ℝ} (hxy : x < y) (hlen : y - x < 2 * Real.pi) :
    Function.Injective (arcPathBetween γ x y hcont) := by
  have hpos : 0 < y - x := sub_pos.mpr hxy
  intro u v huv
  have hu : x + (u : ℝ) * (y - x) ∈ Set.Icc x y :=
    ⟨by nlinarith [u.2.1], by nlinarith [u.2.2]⟩
  have hv : x + (v : ℝ) * (y - x) ∈ Set.Icc x y :=
    ⟨by nlinarith [v.2.1], by nlinarith [v.2.2]⟩
  have hγ : γ (x + (u : ℝ) * (y - x)) = γ (x + (v : ℝ) * (y - x)) := by
    rw [arcPathBetween_apply, arcPathBetween_apply] at huv
    exact huv
  have h1 := injOn_Icc_of_sub_lt hγp hγi hlen hu hv hγ
  have h2 : (u : ℝ) * (y - x) = (v : ℝ) * (y - x) := by linarith
  exact Subtype.ext (mul_right_cancel₀ (ne_of_gt hpos) h2)

/-- **The two traversals of the `γ`-arc have the same range (the image of the parameter
interval).**  Stated for the raw parametrisations, which is what the loop is assembled from. -/
theorem range_arcPathForward {γ : ℝ → ℂ} {x y : ℝ} (hγc : Continuous γ) (hxy : x < y) :
    Set.range (fun u : Set.Icc (0 : ℝ) 1 => γ (x + (u : ℝ) * (y - x))) = γ '' Set.Icc x y :=
  range_arcPathBetween hγc hxy

theorem range_arcPathBackward {γ : ℝ → ℂ} {x y : ℝ} (hγc : Continuous γ) (hxy : x < y) :
    Set.range (fun u : Set.Icc (0 : ℝ) 1 => γ (y + (u : ℝ) * (x - y))) = γ '' Set.Icc x y := by
  have hpos : 0 < y - x := sub_pos.mpr hxy
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨y + (u : ℝ) * (x - y), ⟨?_, ?_⟩, rfl⟩
    · nlinarith [u.2.1, u.2.2, hxy]
    · nlinarith [u.2.1, u.2.2, hxy]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨(y - t) / (y - x), ?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith [ht.2]) hpos.le
    · rw [div_le_one hpos]; linarith [ht.1]
    · show γ (y + ((y - t) / (y - x)) * (x - y)) = γ t
      rw [show y + ((y - t) / (y - x)) * (x - y) = t from by field_simp; ring]

/-- **The closed loop**: the extended cap arc, closed up by the `γ`-arc joining `a` back to `a`. -/
theorem exists_capLoop {γ : ℝ → ℂ} (f : ℂ → ℂ) (s : ℝ) (a b : ℂ) (hα : 0 < capAlpha s)
    (hcont : Continuous (capExtend f s a b)) (hγc : Continuous γ) {x y : ℝ} (hxy : x < y)
    (h : (γ x = a ∧ γ y = b) ∨ (γ x = b ∧ γ y = a)) :
    ∃ L : Path a a,
      Set.range L = (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) ∪ {a, b})
        ∪ γ '' Set.Icc x y := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · -- `γ x = a`, `γ y = b`: traverse the `γ`-arc backwards
    refine ⟨(capArcPathPath f s a b hα hcont).trans
      { toFun := fun u => γ (y + (u : ℝ) * (x - y))
        continuous_toFun := hγc.comp (by fun_prop)
        source' := by
          show γ (y + ((0 : Set.Icc (0 : ℝ) 1) : ℝ) * (x - y)) = b
          rw [show ((0 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 from rfl, zero_mul, add_zero, hy]
        target' := by
          show γ (y + ((1 : Set.Icc (0 : ℝ) 1) : ℝ) * (x - y)) = a
          rw [show ((1 : Set.Icc (0 : ℝ) 1) : ℝ) = 1 from rfl, one_mul,
            show y + (x - y) = x by ring, hx] }, ?_⟩
    rw [Work.Smooth.SphereJordan.path_range_trans, range_capArcPathPath hα]
    congr 1
    exact range_arcPathBackward hγc hxy
  · -- `γ x = b`, `γ y = a`: traverse the `γ`-arc forwards
    refine ⟨(capArcPathPath f s a b hα hcont).trans
      { toFun := fun u => γ (x + (u : ℝ) * (y - x))
        continuous_toFun := hγc.comp (by fun_prop)
        source' := by
          show γ (x + ((0 : Set.Icc (0 : ℝ) 1) : ℝ) * (y - x)) = b
          rw [show ((0 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 from rfl, zero_mul, add_zero, hx]
        target' := by
          show γ (x + ((1 : Set.Icc (0 : ℝ) 1) : ℝ) * (y - x)) = a
          rw [show ((1 : Set.Icc (0 : ℝ) 1) : ℝ) = 1 from rfl, one_mul,
            show x + (y - x) = y by ring, hy] }, ?_⟩
    rw [Work.Smooth.SphereJordan.path_range_trans, range_capArcPathPath hα]
    congr 1
    exact range_arcPathForward hγc hxy
/-- **The cap half and the `γ`-half of the loop meet only at the two endpoints.**  The cap half lies
in `Ω ∪ γ.trace` and meets `γ.trace` exactly in `{a, b}`, while the `γ`-half lies in `γ.trace`; this
is exactly the hypothesis of `path_injOn_trans_loop`. -/
theorem range_capArcPathPath_inter {Ω : Set ℂ} {γ : ℝ → ℂ} {f : ℂ → ℂ} {s : ℝ} {a b : ℂ}
    {x y : ℝ} (hΩo : IsOpen Ω) (hs : 0 < s) (hs2 : s < 2)
    {hcont : Continuous (capExtend f s a b)}
    (himg : f '' Metric.ball (0 : ℂ) 1 = Ω) (hfr : frontier Ω = Set.range γ) :
    Set.range (capArcPathPath f s a b (capAlpha_pos hs2) hcont) ∩ (γ '' Set.Icc x y) ⊆ {a, b} := by
  rw [range_capArcPathPath (capAlpha_pos hs2)]
  rintro z ⟨hz | hz, hz'⟩
  · -- a point of the open-arc image is in `Ω`, but `γ '' Icc x y ⊆ frontier Ω`
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨τ, hτ, rfl⟩ := hw
    obtain ⟨t, _, htz⟩ := hz'
    have hΩ : f (capPt s τ) ∈ Ω := by
      rw [← himg]
      exact ⟨capPt s τ, capPt_mem_ball_of_mem_Ioo hs hs2 hτ, rfl⟩
    have hfr' : γ t ∈ frontier Ω := by
      rw [hfr]
      exact ⟨t, rfl⟩
    rw [htz, hΩo.frontier_eq] at hfr'
    exact (hfr'.2 hΩ).elim
  · -- the endpoints of the cap half are `a` and `b`
    rcases hz with h | h
    · exact Or.inl h
    · exact Or.inr h

theorem capArcPathPath_apply (f : ℂ → ℂ) (s : ℝ) (a b : ℂ) (hα : 0 < capAlpha s)
    (hcont : Continuous (capExtend f s a b)) (u : Set.Icc (0 : ℝ) 1) :
    capArcPathPath f s a b hα hcont u
      = capExtend f s a b (-(capAlpha s) + (u : ℝ) * (2 * capAlpha s)) := rfl

/-- **The cap half of the loop is injective**, provided the two endpoint values differ.  The value of
the path determines its index: it is `a` exactly at the left end, `b` exactly at the right end, and
on the open arc it is `f ∘ capPt s`, which is injective because both factors are. -/
theorem capArcPathPath_injective {Ω : Set ℂ} {f : ℂ → ℂ} {s : ℝ} {a b : ℂ}
    (hΩo : IsOpen Ω) (hs : 0 < s) (hs2 : s < 2) (hcont : Continuous (capExtend f s a b))
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1)) (hsub : f '' Metric.ball (0 : ℂ) 1 ⊆ Ω)
    (hafr : a ∈ frontier Ω) (hbfr : b ∈ frontier Ω) (hab : a ≠ b) :
    Function.Injective (capArcPathPath f s a b (capAlpha_pos hs2) hcont) := by
  have hα : 0 < capAlpha s := capAlpha_pos hs2
  have hαπ : capAlpha s < Real.pi := capAlpha_lt_pi hs
  have haΩ : a ∉ Ω := by rw [hΩo.frontier_eq] at hafr; exact hafr.2
  have hbΩ : b ∉ Ω := by rw [hΩo.frontier_eq] at hbfr; exact hbfr.2
  -- the parameter of an interior index lies in `(-α, α)`
  have hτmem : ∀ u : Set.Icc (0 : ℝ) 1, 0 < (u : ℝ) → (u : ℝ) < 1 →
      -(capAlpha s) + (u : ℝ) * (2 * capAlpha s) ∈ Set.Ioo (-(capAlpha s)) (capAlpha s) := by
    intro u h0 h1
    exact ⟨by nlinarith [hα], by nlinarith [hα]⟩
  -- and there the extension is the plain composition with `f`
  have hval : ∀ u : Set.Icc (0 : ℝ) 1, 0 < (u : ℝ) → (u : ℝ) < 1 →
      capArcPathPath f s a b hα hcont u
        = f (capPt s (-(capAlpha s) + (u : ℝ) * (2 * capAlpha s))) := by
    intro u h0 h1
    have hτ := hτmem u h0 h1
    rw [capArcPathPath_apply, capExtend, if_neg (not_le.mpr hτ.1),
      if_neg (not_le.mpr hτ.2)]
  -- the value `a` pins down the left end
  have hleft : ∀ u : Set.Icc (0 : ℝ) 1, capArcPathPath f s a b hα hcont u = a → (u : ℝ) = 0 := by
    intro u hu
    by_contra hne
    have hpos : 0 < (u : ℝ) := lt_of_le_of_ne u.2.1 (Ne.symm hne)
    rcases lt_or_eq_of_le u.2.2 with hlt | heq
    · have hτ := hτmem u hpos hlt
      rw [hval u hpos hlt] at hu
      have hmem : f (capPt s (-(capAlpha s) + (u : ℝ) * (2 * capAlpha s))) ∈ Ω :=
        hsub ⟨_, capPt_mem_ball_of_mem_Ioo hs hs2 hτ, rfl⟩
      exact haΩ (hu ▸ hmem)
    · have hu1 : u = ⟨1, by norm_num⟩ := Subtype.ext heq
      rw [hu1] at hu
      exact hab (hu.symm.trans (capArcPathPath f s a b hα hcont).target)
  -- the value `b` pins down the right end
  have hright : ∀ u : Set.Icc (0 : ℝ) 1, capArcPathPath f s a b hα hcont u = b → (u : ℝ) = 1 := by
    intro u hu
    by_contra hne
    have hlt : (u : ℝ) < 1 := lt_of_le_of_ne u.2.2 hne
    rcases eq_or_lt_of_le u.2.1 with heq | hpos
    · have hu0 : u = ⟨0, by norm_num⟩ := Subtype.ext heq.symm
      rw [hu0] at hu
      exact hab ((capArcPathPath f s a b hα hcont).source.symm.trans hu)
    · have hτ := hτmem u hpos hlt
      rw [hval u hpos hlt] at hu
      have hmem : f (capPt s (-(capAlpha s) + (u : ℝ) * (2 * capAlpha s))) ∈ Ω :=
        hsub ⟨_, capPt_mem_ball_of_mem_Ioo hs hs2 hτ, rfl⟩
      exact hbΩ (hu ▸ hmem)
  intro u v huv
  by_cases hua : capArcPathPath f s a b hα hcont u = a
  · have h1 := hleft u hua
    have h2 := hleft v (by rw [← huv]; exact hua)
    exact Subtype.ext (by rw [h1, h2])
  · by_cases hub : capArcPathPath f s a b hα hcont u = b
    · have h1 := hright u hub
      have h2 := hright v (by rw [← huv]; exact hub)
      exact Subtype.ext (by rw [h1, h2])
    · -- both indices are interior
      have hu0 : (u : ℝ) ≠ 0 := by
        intro h
        exact hua (by
          rw [show u = ⟨0, by norm_num⟩ from Subtype.ext h]
          exact (capArcPathPath f s a b hα hcont).source)
      have hu1 : (u : ℝ) ≠ 1 := by
        intro h
        exact hub (by
          rw [show u = ⟨1, by norm_num⟩ from Subtype.ext h]
          exact (capArcPathPath f s a b hα hcont).target)
      have hv0 : (v : ℝ) ≠ 0 := by
        intro h
        have hv : v = ⟨0, by norm_num⟩ := Subtype.ext h
        exact hua (by rw [huv, hv]; exact (capArcPathPath f s a b hα hcont).source)
      have hv1 : (v : ℝ) ≠ 1 := by
        intro h
        have hv : v = ⟨1, by norm_num⟩ := Subtype.ext h
        exact hub (by rw [huv, hv]; exact (capArcPathPath f s a b hα hcont).target)
      have hui : 0 < (u : ℝ) ∧ (u : ℝ) < 1 :=
        ⟨lt_of_le_of_ne u.2.1 (Ne.symm hu0), lt_of_le_of_ne u.2.2 hu1⟩
      have hvi : 0 < (v : ℝ) ∧ (v : ℝ) < 1 :=
        ⟨lt_of_le_of_ne v.2.1 (Ne.symm hv0), lt_of_le_of_ne v.2.2 hv1⟩
      have hτu := hτmem u hui.1 hui.2
      have hτv := hτmem v hvi.1 hvi.2
      have h1 : f (capPt s (-(capAlpha s) + (u : ℝ) * (2 * capAlpha s)))
          = f (capPt s (-(capAlpha s) + (v : ℝ) * (2 * capAlpha s))) := by
        rw [← hval u hui.1 hui.2, ← hval v hvi.1 hvi.2, huv]
      have h2 : capPt s (-(capAlpha s) + (u : ℝ) * (2 * capAlpha s))
          = capPt s (-(capAlpha s) + (v : ℝ) * (2 * capAlpha s)) :=
        hinj (capPt_mem_ball_of_mem_Ioo hs hs2 hτu) (capPt_mem_ball_of_mem_Ioo hs hs2 hτv) h1
      have h3 : -(capAlpha s) + (u : ℝ) * (2 * capAlpha s)
          = -(capAlpha s) + (v : ℝ) * (2 * capAlpha s) :=
        capPt_injOn hs ⟨by linarith [hτu.1, hαπ], by linarith [hτu.2, hαπ]⟩
          ⟨by linarith [hτv.1, hαπ], by linarith [hτv.2, hαπ]⟩ h2
      have h4 : (u : ℝ) * (2 * capAlpha s) = (v : ℝ) * (2 * capAlpha s) := by linarith [h3]
      exact Subtype.ext (mul_right_cancel₀ (by linarith : (2 : ℝ) * capAlpha s ≠ 0) h4)

/-- The *backwards* traversal of a sub-arc is injective whenever the forwards one is: the backward
parametrisation is the forward one precomposed with `u ↦ 1 - u`. -/
theorem arcPathBackward_injective {γ : ℝ → ℂ} (hγc : Continuous γ)
    (hγp : Function.Periodic γ (2 * Real.pi)) (hγi : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    {x y : ℝ} (hxy : x < y) (hlen : y - x < 2 * Real.pi) :
    Function.Injective (fun u : Set.Icc (0 : ℝ) 1 => γ (y + (u : ℝ) * (x - y))) := by
  intro u v huv
  have hu : (1 - (u : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [u.2.2], by linarith [u.2.1]⟩
  have hv : (1 - (v : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [v.2.2], by linarith [v.2.1]⟩
  have h1 : y + (u : ℝ) * (x - y) = x + (1 - (u : ℝ)) * (y - x) := by ring
  have h2 : y + (v : ℝ) * (x - y) = x + (1 - (v : ℝ)) * (y - x) := by ring
  have h3 : (fun w : Set.Icc (0 : ℝ) 1 => γ (x + (w : ℝ) * (y - x))) ⟨1 - (u : ℝ), hu⟩
      = (fun w : Set.Icc (0 : ℝ) 1 => γ (x + (w : ℝ) * (y - x))) ⟨1 - (v : ℝ), hv⟩ := by
    show γ (x + (1 - (u : ℝ)) * (y - x)) = γ (x + (1 - (v : ℝ)) * (y - x))
    rw [← h1, ← h2]
    exact huv
  have h4 := arcPathBetween_injective hγc hγp hγi hxy hlen h3
  have h5 := congrArg Subtype.val h4
  simp only at h5
  exact Subtype.ext (by linarith [h5])

/-- **The loop is simple on the half-open interval.**  This feeds `loopCurve_isSimple`. -/
theorem exists_capLoop_simple {Ω : Set ℂ} {γ : ℝ → ℂ} {f : ℂ → ℂ} {s : ℝ} {a b : ℂ}
    (hΩo : IsOpen Ω) (hγc : Continuous γ) (hγp : Function.Periodic γ (2 * Real.pi))
    (hγi : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (hs : 0 < s) (hs2 : s < 2) (hcont : Continuous (capExtend f s a b))
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1)) (himg : f '' Metric.ball (0 : ℂ) 1 = Ω)
    (hfr : frontier Ω = Set.range γ)
    (hafr : a ∈ frontier Ω) (hbfr : b ∈ frontier Ω) (hab : a ≠ b)
    {x y : ℝ} (hxy : x < y) (hlen : y - x < 2 * Real.pi)
    (h : (γ x = a ∧ γ y = b) ∨ (γ x = b ∧ γ y = a)) :
    ∃ L : Path a a, Set.InjOn L {t : Set.Icc (0 : ℝ) 1 | (t : ℝ) < 1} ∧
      Set.range L = (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) ∪ {a, b})
        ∪ γ '' Set.Icc x y := by
  have hP : Function.Injective (capArcPathPath f s a b (capAlpha_pos hs2) hcont) :=
    capArcPathPath_injective hΩo hs hs2 hcont hinj himg.le hafr hbfr hab
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · -- `γ x = a`, `γ y = b`: traverse the `γ`-arc backwards
    set Q : Path b a :=
      { toFun := fun u => γ (y + (u : ℝ) * (x - y))
        continuous_toFun := hγc.comp (by fun_prop)
        source' := by
          show γ (y + ((0 : Set.Icc (0 : ℝ) 1) : ℝ) * (x - y)) = b
          rw [show ((0 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 from rfl, zero_mul, add_zero, hy]
        target' := by
          show γ (y + ((1 : Set.Icc (0 : ℝ) 1) : ℝ) * (x - y)) = a
          rw [show ((1 : Set.Icc (0 : ℝ) 1) : ℝ) = 1 from rfl, one_mul,
            show y + (x - y) = x by ring, hx] } with hQ
    have hQinj : Function.Injective Q := by
      rw [hQ]
      exact arcPathBackward_injective hγc hγp hγi hxy hlen
    have hQrange : Set.range Q = γ '' Set.Icc x y := by
      rw [hQ]
      exact range_arcPathBackward hγc hxy
    have hdisj : Set.range (capArcPathPath f s a b (capAlpha_pos hs2) hcont) ∩ Set.range Q
        ⊆ {a, b} := by
      rw [hQrange]
      exact range_capArcPathPath_inter hΩo hs hs2 himg hfr
    refine ⟨(capArcPathPath f s a b (capAlpha_pos hs2) hcont).trans Q, ?_, ?_⟩
    · exact Work.Smooth.SphereJordan.path_injOn_trans_loop _ _ hP hQinj hdisj
    · rw [Work.Smooth.SphereJordan.path_range_trans, range_capArcPathPath (capAlpha_pos hs2),
        hQrange]
  · -- `γ x = b`, `γ y = a`: traverse the `γ`-arc forwards
    set Q : Path b a :=
      { toFun := fun u => γ (x + (u : ℝ) * (y - x))
        continuous_toFun := hγc.comp (by fun_prop)
        source' := by
          show γ (x + ((0 : Set.Icc (0 : ℝ) 1) : ℝ) * (y - x)) = b
          rw [show ((0 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 from rfl, zero_mul, add_zero, hx]
        target' := by
          show γ (x + ((1 : Set.Icc (0 : ℝ) 1) : ℝ) * (y - x)) = a
          rw [show ((1 : Set.Icc (0 : ℝ) 1) : ℝ) = 1 from rfl, one_mul,
            show x + (y - x) = y by ring, hy] } with hQ
    have hQinj : Function.Injective Q := by
      rw [hQ]
      exact arcPathBetween_injective hγc hγp hγi hxy hlen
    have hQrange : Set.range Q = γ '' Set.Icc x y := by
      rw [hQ]
      exact range_arcPathForward hγc hxy
    have hdisj : Set.range (capArcPathPath f s a b (capAlpha_pos hs2) hcont) ∩ Set.range Q
        ⊆ {a, b} := by
      rw [hQrange]
      exact range_capArcPathPath_inter hΩo hs hs2 himg hfr
    refine ⟨(capArcPathPath f s a b (capAlpha_pos hs2) hcont).trans Q, ?_, ?_⟩
    · exact Work.Smooth.SphereJordan.path_injOn_trans_loop _ _ hP hQinj hdisj
    · rw [Work.Smooth.SphereJordan.path_range_trans, range_capArcPathPath (capAlpha_pos hs2),
        hQrange]

/-- **The loop as a simple closed plane curve**, ready for `exists_jsep`.
(`loopCurve` and `loopCurve_isSimple` are the workspace's `Work.Smooth.SphereJordan` lemmas that
turn a loop injective on `[0,1)` into a simple `2π`-periodic `PlaneCurve`.) -/
theorem exists_capPlaneCurve {Ω : Set ℂ} {γ : ℝ → ℂ} {f : ℂ → ℂ} {s : ℝ} {a b : ℂ}
    (hΩo : IsOpen Ω) (hγc : Continuous γ) (hγp : Function.Periodic γ (2 * Real.pi))
    (hγi : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (hs : 0 < s) (hs2 : s < 2) (hcont : Continuous (capExtend f s a b))
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1)) (himg : f '' Metric.ball (0 : ℂ) 1 = Ω)
    (hfr : frontier Ω = Set.range γ)
    (hafr : a ∈ frontier Ω) (hbfr : b ∈ frontier Ω) (hab : a ≠ b)
    {x y : ℝ} (hxy : x < y) (hlen : y - x < 2 * Real.pi)
    (h : (γ x = a ∧ γ y = b) ∨ (γ x = b ∧ γ y = a)) :
    ∃ K : Work.Smooth.Jordan.PlaneCurve, K.IsSimple ∧
      Set.range K.γ = (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) ∪ {a, b})
        ∪ γ '' Set.Icc x y := by
  obtain ⟨L, hL, hLrange⟩ := exists_capLoop_simple hΩo hγc hγp hγi hs hs2 hcont hinj himg hfr
    hafr hbfr hab hxy hlen h
  refine ⟨Work.Smooth.SphereJordan.loopCurve L (L.source.trans L.target.symm), ?_, ?_⟩
  · exact Work.Smooth.SphereJordan.loopCurve_isSimple L _ hL
  · rw [Work.Smooth.SphereJordan.range_loopCurve]
    exact hLrange

/-- **The image of the outer lens has positive diameter**, so it can never be the "small side" of
the Jordan curve. -/
theorem diam_image_outerLens_pos {f : ℂ → ℂ} {s : ℝ} (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1))
    (hs : 0 < s) (hs2 : s < 2) (hbdd : Bornology.IsBounded (f '' outerLens s)) :
    0 < Metric.diam (f '' outerLens s) := by
  obtain ⟨z, hz⟩ := outerLens_nonempty hs hs2
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (outerLens_isOpen s) z hz
  set w : ℂ := z + (((ε / 2 : ℝ)) : ℂ) with hw
  have hwmem : w ∈ outerLens s := by
    refine hball ?_
    rw [Metric.mem_ball, dist_eq_norm, hw, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hzne : z ≠ w := by
    intro h
    have h1 : (((ε / 2 : ℝ)) : ℂ) = 0 := by
      have := congrArg (fun u => u - z) h
      rw [hw, add_sub_cancel_left, sub_self] at this
      exact this.symm
    rw [Complex.ofReal_eq_zero] at h1
    linarith
  have hfd : f z ≠ f w := fun h => hzne (hinj hz.1 hwmem.1 h)
  have hle : dist (f z) (f w) ≤ Metric.diam (f '' outerLens s) :=
    Metric.dist_le_diam_of_mem hbdd ⟨z, hz, rfl⟩ ⟨w, hwmem, rfl⟩
  linarith [dist_pos.mpr hfd, hle]

/-- The image of the outer lens *grows* as the radius `s` shrinks, so a fixed positive lower bound
at one radius bounds it below at every smaller radius. -/
theorem diam_image_outerLens_le {f : ℂ → ℂ} {s s₀ : ℝ} (hss : s ≤ s₀)
    (hbdd : Bornology.IsBounded (f '' outerLens s)) :
    Metric.diam (f '' outerLens s₀) ≤ Metric.diam (f '' outerLens s) := by
  refine Metric.diam_mono ?_ hbdd
  rintro w ⟨z, hz, rfl⟩
  exact ⟨z, ⟨hz.1, lt_of_le_of_lt hss hz.2⟩, rfl⟩

/-- **The Jordan separation datum of the loop.**  Packages the simple closed curve with its
separation datum and its trace, ready for the diameter argument. -/
theorem exists_capJSep {Ω : Set ℂ} {γ : ℝ → ℂ} {f : ℂ → ℂ} {s : ℝ} {a b : ℂ}
    (hΩo : IsOpen Ω) (hγc : Continuous γ) (hγp : Function.Periodic γ (2 * Real.pi))
    (hγi : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (hs : 0 < s) (hs2 : s < 2) (hcont : Continuous (capExtend f s a b))
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1)) (himg : f '' Metric.ball (0 : ℂ) 1 = Ω)
    (hfr : frontier Ω = Set.range γ)
    (hafr : a ∈ frontier Ω) (hbfr : b ∈ frontier Ω) (hab : a ≠ b)
    {x y : ℝ} (hxy : x < y) (hlen : y - x < 2 * Real.pi)
    (h : (γ x = a ∧ γ y = b) ∨ (γ x = b ∧ γ y = a)) :
    ∃ (K : Work.Smooth.Jordan.PlaneCurve) (T : JSep K), K.IsSimple ∧
      Set.range K.γ = (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) ∪ {a, b})
        ∪ γ '' Set.Icc x y := by
  obtain ⟨K, hK, hKrange⟩ := exists_capPlaneCurve hΩo hγc hγp hγi hs hs2 hcont hinj himg hfr
    hafr hbfr hab hxy hlen h
  obtain ⟨T⟩ := Work.Smooth.SphereJordan.exists_jsep K hK
  exact ⟨K, T, hK, hKrange⟩

/-- **A curve lying in `S.V ∪ γ.trace` avoids the exterior `S.U`.**  This turns the trace inclusion
produced by `exists_capJSep` into the hypothesis of `JSep.V_subset_of_disjoint_trace`. -/
theorem jsep_disjoint_trace_of_subset {γ c : Work.Smooth.Jordan.PlaneCurve} (S : JSep γ)
    (h : Set.range c.γ ⊆ S.V ∪ Set.range γ) : Disjoint c.trace S.U := by
  rw [Set.disjoint_left]
  intro z hz hzU
  have hz' : z ∈ Set.range c.γ := hz
  rcases h hz' with h2 | h2
  · exact (Set.disjoint_left.mp S.disjoint_UV hzU) h2
  · have h3 : z ∉ S.U ∪ S.V := by
      rw [S.union_eq, Set.mem_compl_iff]
      exact fun hcon => hcon h2
    exact h3 (Or.inl hzU)

/-- **The trace of the loop lies in `Ω ∪ γ.trace`** (in the form `S.V ∪ γ.trace` for a separation
datum `S` of `γ`): the cap-arc image lies in `Ω`, the two limits lie on `γ.trace`, and the closing
arc lies in `γ.trace`. -/
theorem capCurve_range_subset {γ : Work.Smooth.Jordan.PlaneCurve} {f : ℂ → ℂ} {s : ℝ} {a b : ℂ}
    {x y : ℝ} {K : Work.Smooth.Jordan.PlaneCurve} (S : JSep γ) (hs : 0 < s) (hs2 : s < 2)
    (hsub : f '' Metric.ball (0 : ℂ) 1 ⊆ S.V)
    (ha : a ∈ Set.range γ.γ) (hb : b ∈ Set.range γ.γ)
    (hKrange : Set.range K.γ = (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) ∪ {a, b})
      ∪ γ.γ '' Set.Icc x y) :
    Set.range K.γ ⊆ S.V ∪ Set.range γ.γ := by
  rw [hKrange]
  rintro z ((hz | hz) | hz)
  · obtain ⟨u, ⟨τ, hτ, rfl⟩, rfl⟩ := hz
    exact Or.inl (hsub ⟨capPt s τ, capPt_mem_ball_of_mem_Ioo hs hs2 hτ, rfl⟩)
  · rcases hz with h | h
    · exact Or.inr (h ▸ ha)
    · exact Or.inr (h ▸ hb)
  · obtain ⟨t, _, rfl⟩ := hz
    exact Or.inr ⟨t, rfl⟩

/-- **The bounded side of the loop lies in `Ω`.** -/
theorem capJSep_V_subset {Ω : Set ℂ} {γ : Work.Smooth.Jordan.PlaneCurve} {f : ℂ → ℂ} {s : ℝ}
    {a b : ℂ} {x y : ℝ} {K : Work.Smooth.Jordan.PlaneCurve} (S : JSep γ) (T : JSep K)
    (hΩ : Ω = S.V) (hs : 0 < s) (hs2 : s < 2)
    (hsub : f '' Metric.ball (0 : ℂ) 1 ⊆ S.V)
    (ha : a ∈ Set.range γ.γ) (hb : b ∈ Set.range γ.γ)
    (hKrange : Set.range K.γ = (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) ∪ {a, b})
      ∪ γ.γ '' Set.Icc x y) :
    T.V ⊆ Ω := by
  have h1 : Set.range K.γ ⊆ S.V ∪ Set.range γ.γ :=
    capCurve_range_subset S hs hs2 hsub ha hb hKrange
  have h2 : Disjoint K.trace S.U := jsep_disjoint_trace_of_subset S h1
  have h3 : T.V ⊆ S.V := JSep.V_subset_of_disjoint_trace S T h2
  rwa [hΩ]

/-- **A point of the closure of `s` does not increase the diameter**: `diam (insert a s) ≤ diam s`
when `a ∈ closure s`. -/
theorem diam_insert_le {s : Set ℂ} {a : ℂ} (ha : a ∈ closure s)
    (hbdd : Bornology.IsBounded s) :
    Metric.diam (insert a s) ≤ Metric.diam s := by
  refine Metric.diam_le_of_forall_dist_le Metric.diam_nonneg fun u hu v hv => ?_
  rw [Set.mem_insert_iff] at hu hv
  rcases hu with rfl | hu
  · rcases hv with rfl | hv
    · rw [dist_self]; exact Metric.diam_nonneg
    · have h1 := Metric.dist_le_diam_of_mem hbdd.closure ha (subset_closure hv)
      rwa [Metric.diam_closure] at h1
  · rcases hv with rfl | hv
    · have h1 := Metric.dist_le_diam_of_mem hbdd.closure (subset_closure hu) ha
      rw [Metric.diam_closure] at h1
      exact h1
    · exact Metric.dist_le_diam_of_mem hbdd hu hv

/-- **Diameter of a union of two sets meeting at a common point** (here a point of `closure s` that
also lies in `t`). -/
theorem diam_union_le {s t : Set ℂ} {a : ℂ} (ha : a ∈ closure s) (hat : a ∈ t)
    (hbdd : Bornology.IsBounded s) (htbdd : Bornology.IsBounded t) :
    Metric.diam (s ∪ t) ≤ Metric.diam s + Metric.diam t := by
  refine Metric.diam_le_of_forall_dist_le (by positivity) fun u hu v hv => ?_
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact le_trans (Metric.dist_le_diam_of_mem hbdd hu hv) (le_add_of_nonneg_right Metric.diam_nonneg)
  · have h1 : dist u a ≤ Metric.diam s := by
      have h := Metric.dist_le_diam_of_mem hbdd.closure (subset_closure hu) ha
      rwa [Metric.diam_closure] at h
    have h2 : dist a v ≤ Metric.diam t := Metric.dist_le_diam_of_mem htbdd hat hv
    linarith [dist_triangle u a v]
  · have h1 : dist v a ≤ Metric.diam s := by
      have h := Metric.dist_le_diam_of_mem hbdd.closure (subset_closure hv) ha
      rwa [Metric.diam_closure] at h
    have h2 : dist a u ≤ Metric.diam t := Metric.dist_le_diam_of_mem htbdd hat hu
    rw [dist_comm u v]
    linarith [dist_triangle v a u]
  · exact le_trans (Metric.dist_le_diam_of_mem htbdd hu hv) (le_add_of_nonneg_left Metric.diam_nonneg)

/-- **The bounded side of the loop has small diameter.**  This is the quantitative heart of the cap
argument: `diam T.V ≤ diam K.trace ≤ diam A + diam C ≤ capLen + ε/4 ≤ ε/2`. -/
theorem diam_capJSep_V_le {γ : Work.Smooth.Jordan.PlaneCurve} {f : ℂ → ℂ} {s : ℝ} {a b : ℂ}
    {x y : ℝ} {K : Work.Smooth.Jordan.PlaneCurve} (T : JSep K) {ε : ℝ}
    (hKrange : Set.range K.γ = (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) ∪ {a, b})
      ∪ γ.γ '' Set.Icc x y)
    (haA : a ∈ closure (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s))))
    (hbA : b ∈ closure (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s))))
    (haC : a ∈ γ.γ '' Set.Icc x y)
    (hAbdd : Bornology.IsBounded (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s))))
    (hCbdd : Bornology.IsBounded (γ.γ '' Set.Icc x y))
    (hA : Metric.diam (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)))
      ≤ (capLen f s).toReal)
    (hC : Metric.diam (γ.γ '' Set.Icc x y) ≤ ε / 4)
    (hcap : (capLen f s).toReal ≤ ε / 4) :
    Metric.diam T.V ≤ ε / 2 := by
  have h1 : Metric.diam T.V ≤ Metric.diam K.trace := by
    rw [← T.frontier_V]
    exact diam_le_diam_frontier T.isOpen_V T.bounded_V
  have h2 : Metric.diam K.trace ≤ (capLen f s).toReal + ε / 4 := by
    have htr : K.trace = Set.range K.γ := rfl
    rw [htr, hKrange]
    have h5 : f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) ∪ {a, b}
        = insert a (insert b (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)))) := by
      ext z
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have hAbdd' : Bornology.IsBounded
        (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) ∪ {a, b}) := by
      rw [h5]
      exact Bornology.IsBounded.insert (Bornology.IsBounded.insert hAbdd b) a
    have h3 : Metric.diam ((f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) ∪ {a, b})
        ∪ γ.γ '' Set.Icc x y)
        ≤ Metric.diam (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) ∪ {a, b})
          + Metric.diam (γ.γ '' Set.Icc x y) :=
      diam_union_le (subset_closure (Or.inr (Or.inl rfl))) haC hAbdd' hCbdd
    have h4 : Metric.diam (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s)) ∪ {a, b})
        ≤ Metric.diam (f '' (capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s))) := by
      rw [h5]
      refine le_trans (diam_insert_le ?_ (Bornology.IsBounded.insert hAbdd b))
        (diam_insert_le hbA hAbdd)
      exact closure_mono (Set.subset_insert _ _) haA
    linarith
  linarith

end Work.Smooth.SphereJordan.Caratheodory
