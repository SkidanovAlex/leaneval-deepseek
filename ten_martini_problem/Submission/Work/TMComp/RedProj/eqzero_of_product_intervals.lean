import Mathlib

namespace Work.TMComp.RedProj

open Set

/-- Auxiliary lemma: if `F : ℂ → ℂ` vanishes on the rectangle of real points `Ioo a b`
(viewed as a subset of `ℂ`) and `x₀ ∈ Ioo a b`, then `x₀` (as a complex number) is an
accumulation point of the zero set of `F`. -/
lemma mem_closure_coe_Ioo {a b : ℝ} {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo a b) {F : ℂ → ℂ}
    (hF : ∀ x ∈ Set.Ioo a b, F (x : ℂ) = 0) :
    (x₀ : ℂ) ∈ closure ({z : ℂ | F z = 0} \ {(x₀ : ℂ)}) := by
  have hS : x₀ ∈ closure (Set.Ioo a b \ {x₀}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hlt : x₀ < min b (x₀ + ε) := lt_min hx₀.2 (lt_add_of_pos_right x₀ hε)
    obtain ⟨y, hy1, hy2⟩ := exists_between hlt
    refine ⟨y, ⟨⟨hx₀.1.trans hy1, hy2.trans_le (min_le_left _ _)⟩, ?_⟩, ?_⟩
    · exact ne_of_gt hy1
    · rw [dist_comm, Real.dist_eq, abs_of_pos (sub_pos.mpr hy1)]
      linarith [hy2.trans_le (min_le_right _ _)]
  have him : (x₀ : ℂ) ∈ closure ((fun x : ℝ => (x : ℂ)) '' (Set.Ioo a b \ {x₀})) :=
    image_closure_subset_closure_image Complex.continuous_ofReal ⟨x₀, hS, rfl⟩
  refine closure_mono ?_ him
  rintro z ⟨x, hx, rfl⟩
  exact ⟨hF x hx.1, fun h => hx.2 (Complex.ofReal_injective h)⟩

theorem eqzero_of_product_intervals {U1 U2 : Set ℂ} (ho1 : IsOpen U1) (ho2 : IsOpen U2)
    (hc1 : IsPreconnected U1) (hc2 : IsPreconnected U2) {H : ℂ × ℂ → ℂ}
    (hH : AnalyticOnNhd ℂ H (U1 ×ˢ U2)) {a b p q : ℝ} (hab : a < b) (hpq : p < q)
    (hsub : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo p q, ((x : ℂ), (y : ℂ)) ∈ U1 ×ˢ U2)
    (hzero : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo p q, H ((x : ℂ), (y : ℂ)) = 0) :
    Set.EqOn H 0 (U1 ×ˢ U2) := by
  -- The openness hypotheses are not needed: preconnectedness of the slices suffices.
  have _ := ho1
  have _ := ho2
  obtain ⟨x0, hx0⟩ := exists_between hab
  obtain ⟨y0, hy0⟩ := exists_between hpq
  -- Step 1: for each real `y` in `(p,q)`, the slice `z ↦ H (z,y)` vanishes on `U1`.
  have hstep1 : ∀ y ∈ Set.Ioo p q, EqOn (fun z : ℂ => H (z, (y : ℂ))) 0 U1 := by
    intro y hy
    have hslice : AnalyticOnNhd ℂ (fun z : ℂ => H (z, (y : ℂ))) U1 := by
      have h1 := hH.curry_left (y := (y : ℂ))
      refine h1.mono ?_
      intro z hz
      exact Set.mem_prod.mpr ⟨hz, (Set.mem_prod.mp (hsub x0 hx0 y hy)).2⟩
    refine AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure hslice hc1
      (Set.mem_prod.mp (hsub x0 hx0 y hy)).1 ?_
    exact mem_closure_coe_Ioo hx0 (fun x hx => hzero x hx y hy)
  -- Step 2: for each `z ∈ U1`, the slice `w ↦ H (z,w)` vanishes on `U2`.
  intro ⟨z, w⟩ hzw
  obtain ⟨hz, hw⟩ := Set.mem_prod.mp hzw
  have hslice2 : AnalyticOnNhd ℂ (fun w : ℂ => H (z, w)) U2 := by
    have h1 := hH.curry_right (x := z)
    refine h1.mono ?_
    intro w hw'
    exact Set.mem_prod.mpr ⟨hz, hw'⟩
  have hEq2 : EqOn (fun w : ℂ => H (z, w)) 0 U2 := by
    refine AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure hslice2 hc2
      (Set.mem_prod.mp (hsub x0 hx0 y0 hy0)).2 ?_
    exact mem_closure_coe_Ioo hy0 (fun y hy => hstep1 y hy hz)
  exact hEq2 hw

end Work.TMComp.RedProj
