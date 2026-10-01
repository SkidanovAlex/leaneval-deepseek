import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_shift_identity_gen
import Submission.Work.ZeroDensity.Ingham.horizontalPoleDecayAdd
import Submission.Work.ZeroDensity.Ingham.horizontalPoleDecaySub

namespace Work.ZeroDensity.Ingham

open Complex MeasureTheory intervalIntegral Filter
open scoped Real Topology
open Commons.NumberTheory.DirichletCharacter

noncomputable section

/-- `rectInt` depends only on the rectangle boundary, and only on the boundary away from `0`:
two functions agreeing on the boundary except possibly at the single point `0` have the same
`rectInt`, provided the horizontal sides do not pass through `0`. -/
private lemma rectInt_congr_ae_boundary {z w : ℂ} {f g : ℂ → ℂ}
    (hzim : z.im ≠ 0) (hwim : w.im ≠ 0)
    (h : ∀ s ∈ rectBoundary z w, s ≠ 0 → f s = g s) :
    rectInt z w f = rectInt z w g := by
  have hy0 : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  have e1 : (∫ x : ℝ in z.re..w.re, f ((x : ℂ) + ↑z.im * Complex.I))
      = ∫ x : ℝ in z.re..w.re, g ((x : ℂ) + ↑z.im * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    refine h _ ?_ ?_
    · have h1 : (((x : ℂ) + ↑z.im * Complex.I : ℂ)).re = x := by simp
      have h2 : (((x : ℂ) + ↑z.im * Complex.I : ℂ)).im = z.im := by simp
      exact Or.inl ⟨by rw [h1]; exact hx, Or.inl (by rw [h2])⟩
    · intro h0
      have h2 : (((x : ℂ) + ↑z.im * Complex.I : ℂ)).im = z.im := by simp
      have hz0 : z.im = 0 := by
        have := congrArg Complex.im h0
        rwa [h2] at this
      exact hzim hz0
  have e2 : (∫ x : ℝ in z.re..w.re, f ((x : ℂ) + ↑w.im * Complex.I))
      = ∫ x : ℝ in z.re..w.re, g ((x : ℂ) + ↑w.im * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    refine h _ ?_ ?_
    · have h1 : (((x : ℂ) + ↑w.im * Complex.I : ℂ)).re = x := by simp
      have h2 : (((x : ℂ) + ↑w.im * Complex.I : ℂ)).im = w.im := by simp
      exact Or.inl ⟨by rw [h1]; exact hx, Or.inr (by rw [h2])⟩
    · intro h0
      have h2 : (((x : ℂ) + ↑w.im * Complex.I : ℂ)).im = w.im := by simp
      have hw0 : w.im = 0 := by
        have := congrArg Complex.im h0
        rwa [h2] at this
      exact hwim hw0
  have e3 : (∫ y : ℝ in z.im..w.im, f (↑w.re + ↑y * Complex.I))
      = ∫ y : ℝ in z.im..w.im, g (↑w.re + ↑y * Complex.I) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hy0] with y hy hyIoc
    refine h _ ?_ ?_
    · have h1 : ((↑w.re + ↑y * Complex.I : ℂ)).re = w.re := by simp
      have h2 : ((↑w.re + ↑y * Complex.I : ℂ)).im = y := by simp
      exact Or.inr ⟨by rw [h2]; exact Set.uIoc_subset_uIcc hyIoc, Or.inr (by rw [h1])⟩
    · intro h0
      apply hy
      have h2 : ((↑w.re + ↑y * Complex.I : ℂ)).im = y := by simp
      have := congrArg Complex.im h0
      rwa [h2] at this
  have e4 : (∫ y : ℝ in z.im..w.im, f (↑z.re + ↑y * Complex.I))
      = ∫ y : ℝ in z.im..w.im, g (↑z.re + ↑y * Complex.I) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hy0] with y hy hyIoc
    refine h _ ?_ ?_
    · have h1 : ((↑z.re + ↑y * Complex.I : ℂ)).re = z.re := by simp
      have h2 : ((↑z.re + ↑y * Complex.I : ℂ)).im = y := by simp
      exact Or.inr ⟨by rw [h2]; exact Set.uIoc_subset_uIcc hyIoc, Or.inl (by rw [h1])⟩
    · intro h0
      apply hy
      have h2 : ((↑z.re + ↑y * Complex.I : ℂ)).im = y := by simp
      have := congrArg Complex.im h0
      rwa [h2] at this
  rw [rectInt_eq_def, rectInt_eq_def, e1, e2, e3, e4]

theorem verticalShiftPatchedPoleSelf (F H : ℂ → ℂ) (p q : ℝ) (hpq : p < q) (u a : ℂ)
    (hu : p < u.re ∧ u.re < q)
    (hH : ∀ R : ℝ, DifferentiableOn ℂ H (Set.uIcc p q ×ℂ Set.uIcc (-R) R))
    (hdec : ∀ R : ℝ, 1 ≤ R → ∀ s ∈ (Set.uIcc p q ×ℂ Set.uIcc (-R) R), s ≠ u → s ≠ 0 →
      F s = a / (s - u) + H s)
    (htop : Filter.Tendsto (fun R : ℝ => ∫ x in p..q, H ((x : ℂ) + (R : ℂ) * Complex.I))
      Filter.atTop (nhds 0))
    (hbot : Filter.Tendsto (fun R : ℝ => ∫ x in p..q, H ((x : ℂ) - (R : ℂ) * Complex.I))
      Filter.atTop (nhds 0))
    (hpint : MeasureTheory.Integrable (fun t : ℝ => F ((p : ℂ) + (t : ℂ) * Complex.I)))
    (hqint : MeasureTheory.Integrable (fun t : ℝ => F ((q : ℂ) + (t : ℂ) * Complex.I))) :
    (∫ t : ℝ, F ((q : ℂ) + (t : ℂ) * Complex.I))
      = (∫ t : ℝ, F ((p : ℂ) + (t : ℂ) * Complex.I)) + 2 * Real.pi * a := by
  obtain ⟨T0, hT0_1, hT0_u⟩ : ∃ T0 : ℝ, 1 ≤ T0 ∧ |u.im| < T0 := by
    refine ⟨max 1 (|u.im| + 1), le_max_left _ _, ?_⟩
    exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hres : ∀ T : ℝ, T0 ≤ T →
      rectInt ((p : ℂ) - (T : ℂ) * Complex.I) ((q : ℂ) + (T : ℂ) * Complex.I) F
        = 2 * Real.pi * Complex.I * a := by
    intro T hT
    have hT1 : (1 : ℝ) ≤ T := le_trans hT0_1 hT
    have hTu : |u.im| < T := lt_of_lt_of_le hT0_u hT
    have huim_lt : u.im < T := lt_of_le_of_lt (le_abs_self u.im) hTu
    have hTpos : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT1
    set z : ℂ := (p : ℂ) - (T : ℂ) * Complex.I with hz
    set w : ℂ := (q : ℂ) + (T : ℂ) * Complex.I with hw
    have hzre : z.re = p := by rw [hz]; simp
    have hzim : z.im = -T := by rw [hz]; simp
    have hwre : w.re = q := by rw [hw]; simp
    have hwim : w.im = T := by rw [hw]; simp
    have hzre_lt : z.re < w.re := by rw [hzre, hwre]; exact hpq
    have hzim_lt : z.im < w.im := by rw [hzim, hwim]; linarith
    have huin : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im := by
      rw [hzre, hwre, hzim, hwim]
      exact ⟨hu.1, hu.2, by linarith [hTu, neg_abs_le u.im], huim_lt⟩
    have hFdecomp : ∀ s ∈ rectBoundary z w, s ≠ 0 → F s = a / (s - u) + H s := by
      intro s hs hs0
      have hsmem : s ∈ rectSet z w := rectBoundary_subset_rectSet hzre_lt hzim_lt hs
      have hsu : s ≠ u := ne_of_mem_rectBoundary_of_inside huin hs
      have hsdec : s ∈ (Set.uIcc p q ×ℂ Set.uIcc (-T) T) := by
        have hmem := hsmem
        rw [rectSet, hzre, hwre, hzim, hwim] at hmem
        exact hmem
      exact hdec T hT1 s hsdec hsu hs0
    have hKeq : rectInt z w F = rectInt z w (fun s => a / (s - u) + H s) := by
      apply rectInt_congr_ae_boundary
      · rw [hzim]; exact neg_ne_zero.mpr (ne_of_gt hTpos)
      · rw [hwim]; exact ne_of_gt hTpos
      · exact hFdecomp
    have hKcont : ContinuousOn (fun s : ℂ => a / (s - u)) {s : ℂ | s ≠ u} :=
      continuousOn_const.div (by fun_prop) (fun s hs => sub_ne_zero.mpr hs)
    obtain ⟨k1, k2, k3, k4⟩ := edgeIntegrable_of_continuousOn_ne huin hKcont
    have hHdiff : DifferentiableOn ℂ H (rectSet z w) := by
      simpa only [rectSet, hzre, hwre, hzim, hwim] using hH T
    obtain ⟨m1, m2, m3, m4⟩ := edgeIntegrable_of_continuousOn hHdiff.continuousOn
    have hadd : rectInt z w (fun s => a / (s - u) + H s)
        = rectInt z w (fun s => a / (s - u)) + rectInt z w H :=
      rectInt_add'' k1 m1 k2 m2 k3 m3 k4 m4
    have hK : rectInt z w (fun s => a / (s - u)) = 2 * Real.pi * Complex.I * a := by
      rw [rectInt_const_div_sub_inside a hzre_lt hzim_lt huin]
      ring
    have hHz : rectInt z w H = 0 := rectInt_eq_zero_of_differentiableOn hHdiff
    calc rectInt ((p : ℂ) - (T : ℂ) * Complex.I) ((q : ℂ) + (T : ℂ) * Complex.I) F
        = rectInt z w F := by rw [hz, hw]
      _ = rectInt z w (fun s => a / (s - u) + H s) := hKeq
      _ = rectInt z w (fun s => a / (s - u)) + rectInt z w H := hadd
      _ = 2 * Real.pi * Complex.I * a := by rw [hK, hHz, add_zero]
  have hFtop : Filter.Tendsto (fun T : ℝ => ∫ x in p..q, F ((x : ℂ) + (T : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
    have hk : Filter.Tendsto
        (fun T : ℝ => ∫ x in p..q, a / ((x : ℂ) + (T : ℂ) * Complex.I - u))
        Filter.atTop (nhds 0) := horizontalPoleDecayAdd a u p q
    have hsum : Filter.Tendsto (fun T : ℝ =>
        (∫ x in p..q, a / ((x : ℂ) + (T : ℂ) * Complex.I - u))
          + ∫ x in p..q, H ((x : ℂ) + (T : ℂ) * Complex.I)) Filter.atTop (nhds 0) := by
      simpa using hk.add htop
    refine Filter.Tendsto.congr' (f₁ := fun T : ℝ =>
      (∫ x in p..q, a / ((x : ℂ) + (T : ℂ) * Complex.I - u))
        + ∫ x in p..q, H ((x : ℂ) + (T : ℂ) * Complex.I)) ?_ hsum
    filter_upwards [Filter.eventually_ge_atTop T0] with T hT
    have hT1 : (1 : ℝ) ≤ T := le_trans hT0_1 hT
    have hTu : |u.im| < T := lt_of_lt_of_le hT0_u hT
    have huim_lt : u.im < T := lt_of_le_of_lt (le_abs_self u.im) hTu
    have hpt : Set.EqOn (fun x : ℝ => F ((x : ℂ) + (T : ℂ) * Complex.I))
        (fun x : ℝ => a / ((x : ℂ) + (T : ℂ) * Complex.I - u)
          + H ((x : ℂ) + (T : ℂ) * Complex.I)) (Set.uIcc p q) := by
      intro x hx
      have hsdec : ((x : ℂ) + (T : ℂ) * Complex.I) ∈ (Set.uIcc p q ×ℂ Set.uIcc (-T) T) := by
        refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
        · have hre : ((x : ℂ) + (T : ℂ) * Complex.I).re = x := by simp
          rw [hre]; exact hx
        · have him : ((x : ℂ) + (T : ℂ) * Complex.I).im = T := by simp
          rw [him]; exact Set.right_mem_uIcc
      have hsu : ((x : ℂ) + (T : ℂ) * Complex.I) ≠ u := by
        intro h
        have hT_eq : T = u.im := by
          have := congrArg Complex.im h
          simpa using this
        linarith
      have hs0 : ((x : ℂ) + (T : ℂ) * Complex.I) ≠ 0 := by
        intro h
        have hT_eq : T = 0 := by
          have := congrArg Complex.im h
          simpa using this
        linarith
      exact hdec T hT1 _ hsdec hsu hs0
    have hint1 : IntervalIntegrable
        (fun x : ℝ => a / ((x : ℂ) + (T : ℂ) * Complex.I - u)) volume p q := by
      apply ContinuousOn.intervalIntegrable
      refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
      intro x hx hzero
      have hz : T - u.im = 0 := by
        have him : ((x : ℂ) + (T : ℂ) * Complex.I - u).im = 0 := by rw [hzero]; rfl
        simpa using him
      linarith
    have hint2 : IntervalIntegrable
        (fun x : ℝ => H ((x : ℂ) + (T : ℂ) * Complex.I)) volume p q := by
      apply ContinuousOn.intervalIntegrable
      have himg : Set.MapsTo (fun x : ℝ => (x : ℂ) + (T : ℂ) * Complex.I)
          (Set.uIcc p q) (Set.uIcc p q ×ℂ Set.uIcc (-T) T) := by
        intro x hx
        refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
        · have hre : ((x : ℂ) + (T : ℂ) * Complex.I).re = x := by simp
          rw [hre]; exact hx
        · have him : ((x : ℂ) + (T : ℂ) * Complex.I).im = T := by simp
          rw [him]; exact Set.right_mem_uIcc
      exact (hH T).continuousOn.comp (by fun_prop) himg
    rw [← intervalIntegral.integral_add hint1 hint2, ← intervalIntegral.integral_congr hpt]
  have hFbot : Filter.Tendsto (fun T : ℝ => ∫ x in p..q, F ((x : ℂ) - (T : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
    have hk : Filter.Tendsto
        (fun T : ℝ => ∫ x in p..q, a / ((x : ℂ) - (T : ℂ) * Complex.I - u))
        Filter.atTop (nhds 0) := horizontalPoleDecaySub a u p q
    have hsum : Filter.Tendsto (fun T : ℝ =>
        (∫ x in p..q, a / ((x : ℂ) - (T : ℂ) * Complex.I - u))
          + ∫ x in p..q, H ((x : ℂ) - (T : ℂ) * Complex.I)) Filter.atTop (nhds 0) := by
      simpa using hk.add hbot
    refine Filter.Tendsto.congr' (f₁ := fun T : ℝ =>
      (∫ x in p..q, a / ((x : ℂ) - (T : ℂ) * Complex.I - u))
        + ∫ x in p..q, H ((x : ℂ) - (T : ℂ) * Complex.I)) ?_ hsum
    filter_upwards [Filter.eventually_ge_atTop T0] with T hT
    have hT1 : (1 : ℝ) ≤ T := le_trans hT0_1 hT
    have hTu : |u.im| < T := lt_of_lt_of_le hT0_u hT
    have huim_lt : u.im < T := lt_of_le_of_lt (le_abs_self u.im) hTu
    have hpt : Set.EqOn (fun x : ℝ => F ((x : ℂ) - (T : ℂ) * Complex.I))
        (fun x : ℝ => a / ((x : ℂ) - (T : ℂ) * Complex.I - u)
          + H ((x : ℂ) - (T : ℂ) * Complex.I)) (Set.uIcc p q) := by
      intro x hx
      have hsdec : ((x : ℂ) - (T : ℂ) * Complex.I) ∈ (Set.uIcc p q ×ℂ Set.uIcc (-T) T) := by
        refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
        · have hre : ((x : ℂ) - (T : ℂ) * Complex.I).re = x := by simp
          rw [hre]; exact hx
        · have him : ((x : ℂ) - (T : ℂ) * Complex.I).im = -T := by simp
          rw [him]; exact Set.left_mem_uIcc
      have hsu : ((x : ℂ) - (T : ℂ) * Complex.I) ≠ u := by
        intro h
        have hT_eq : -T = u.im := by
          have := congrArg Complex.im h
          simpa using this
        have hneg : -T < u.im := by linarith [hTu, neg_abs_le u.im]
        linarith
      have hs0 : ((x : ℂ) - (T : ℂ) * Complex.I) ≠ 0 := by
        intro h
        have hT_eq : -T = 0 := by
          have := congrArg Complex.im h
          simpa using this
        linarith
      exact hdec T hT1 _ hsdec hsu hs0
    have hint1 : IntervalIntegrable
        (fun x : ℝ => a / ((x : ℂ) - (T : ℂ) * Complex.I - u)) volume p q := by
      apply ContinuousOn.intervalIntegrable
      refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
      intro x hx hzero
      have hz : -T - u.im = 0 := by
        have him : ((x : ℂ) - (T : ℂ) * Complex.I - u).im = 0 := by rw [hzero]; rfl
        simpa using him
      have hneg : -T < u.im := by linarith [hTu, neg_abs_le u.im]
      linarith
    have hint2 : IntervalIntegrable
        (fun x : ℝ => H ((x : ℂ) - (T : ℂ) * Complex.I)) volume p q := by
      apply ContinuousOn.intervalIntegrable
      have himg : Set.MapsTo (fun x : ℝ => (x : ℂ) - (T : ℂ) * Complex.I)
          (Set.uIcc p q) (Set.uIcc p q ×ℂ Set.uIcc (-T) T) := by
        intro x hx
        refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
        · have hre : ((x : ℂ) - (T : ℂ) * Complex.I).re = x := by simp
          rw [hre]; exact hx
        · have him : ((x : ℂ) - (T : ℂ) * Complex.I).im = -T := by simp
          rw [him]; exact Set.left_mem_uIcc
      exact (hH T).continuousOn.comp (by fun_prop) himg
    rw [← intervalIntegral.integral_add hint1 hint2, ← intervalIntegral.integral_congr hpt]
  have hlim := rectInt_tendsto_vertical_gen_comp (F := F) (A := p) (B := q) hpq (Tf := id)
    tendsto_id hqint hpint hFtop hFbot
  have hresTend : Filter.Tendsto
      (fun T : ℝ => rectInt ((p : ℂ) - (T : ℂ) * Complex.I) ((q : ℂ) + (T : ℂ) * Complex.I) F)
      Filter.atTop (nhds (2 * Real.pi * Complex.I * a)) :=
    tendsto_const_nhds.congr' (Filter.eventually_atTop.mpr ⟨T0, fun T hT => (hres T hT).symm⟩)
  have huniq := tendsto_nhds_unique hlim hresTend
  have hmul : Complex.I * ((∫ t : ℝ, F ((q : ℂ) + (t : ℂ) * Complex.I))
      - (∫ t : ℝ, F ((p : ℂ) + (t : ℂ) * Complex.I)) - 2 * Real.pi * a) = 0 := by
    rw [mul_sub, huniq]
    ring
  have h0 : (∫ t : ℝ, F ((q : ℂ) + (t : ℂ) * Complex.I))
      - (∫ t : ℝ, F ((p : ℂ) + (t : ℂ) * Complex.I)) - 2 * Real.pi * a = 0 :=
    (mul_eq_zero.mp hmul).resolve_left Complex.I_ne_zero
  have hAB : (∫ t : ℝ, F ((q : ℂ) + (t : ℂ) * Complex.I))
      - (∫ t : ℝ, F ((p : ℂ) + (t : ℂ) * Complex.I)) = 2 * Real.pi * a := sub_eq_zero.mp h0
  simpa [add_comm] using (sub_eq_iff_eq_add.mp hAB)

end

end Work.ZeroDensity.Ingham
