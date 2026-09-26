/-
# Auxiliary lemmas for the assembled continuation `Hleft` (Session 3)

This module collects the pieces of the local-continuation assembly that are proved directly (the
remaining global-geometry pieces are delegated separately and imported alongside).
-/
import Mathlib
import Submission.Work.Asymptotics.contourLeftDefs
import Submission.Work.Asymptotics.exists_bound_straightPart_of_clean_MR
import Submission.Work.Asymptotics.measurable_Kfun_snd_all
import Submission.Work.Asymptotics.exists_contour_avoid

noncomputable section

namespace Work.Asymptotics

open UpperHalfPlane MeasureTheory

/-- **Splitting the naive contour integral** into the retained-axis part and the two removed
intervals.  The two removed intervals lie in `(0,∞)` (from `A₁ < t₀`, `A₂ < t₀⁻¹`) and are
disjoint, so `Ioi 0` is their disjoint union with `straightPartSet`. -/
theorem straightPart_add_intervals (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (r t₀ A₁ A₂ : ℝ) (τ : UpperHalfPlane) (hA₁ : A₁ < t₀) (hA₂ : A₂ < t₀⁻¹)
    (hint : IntegrableOn (fun t : ℝ =>
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * gaussWeight r t) (Set.Ioi (0 : ℝ)))
    (hdisj : Set.Ioo (t₀ - A₁) (t₀ + A₁) ∩ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂) = ∅) :
    straightPart ℓ d r t₀ A₁ A₂ τ
      + (∫ t in Set.Ioo (t₀ - A₁) (t₀ + A₁),
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * gaussWeight r t)
      + (∫ t in Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂),
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * gaussWeight r t)
      = ∫ t in Set.Ioi (0 : ℝ),
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * gaussWeight r t := by
  set f : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * gaussWeight r t
    with hf
  set I₁ : Set ℝ := Set.Ioo (t₀ - A₁) (t₀ + A₁) with hI₁
  set I₂ : Set ℝ := Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂) with hI₂
  have hS : straightPart ℓ d r t₀ A₁ A₂ τ = ∫ t in (Set.Ioi (0:ℝ) \ (I₁ ∪ I₂)), f t := rfl
  have hI₁sub : I₁ ⊆ Set.Ioi (0:ℝ) := by
    intro t ht
    simp only [hI₁, Set.mem_Ioo] at ht
    simp only [Set.mem_Ioi]
    linarith [ht.1]
  have hI₂sub : I₂ ⊆ Set.Ioi (0:ℝ) := by
    intro t ht
    simp only [hI₂, Set.mem_Ioo] at ht
    simp only [Set.mem_Ioi]
    linarith [ht.1]
  have hmeas₁ : MeasurableSet I₁ := by rw [hI₁]; exact measurableSet_Ioo
  have hmeas₂ : MeasurableSet I₂ := by rw [hI₂]; exact measurableSet_Ioo
  have hint₁ : IntegrableOn f I₁ := hint.mono_set hI₁sub
  have hint₂ : IntegrableOn f I₂ := hint.mono_set hI₂sub
  have hintU : IntegrableOn f (I₁ ∪ I₂) := hint.mono_set (Set.union_subset hI₁sub hI₂sub)
  have hintC : IntegrableOn f (Set.Ioi (0:ℝ) \ (I₁ ∪ I₂)) := hint.mono_set (Set.diff_subset)
  have hdisjU : Disjoint (Set.Ioi (0:ℝ) \ (I₁ ∪ I₂)) (I₁ ∪ I₂) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx.2 hx'
  have hmeasU : MeasurableSet (I₁ ∪ I₂) := hmeas₁.union hmeas₂
  have hstep1 : (∫ t in (Set.Ioi (0:ℝ) \ (I₁ ∪ I₂)) ∪ (I₁ ∪ I₂), f t)
      = (∫ t in (Set.Ioi (0:ℝ) \ (I₁ ∪ I₂)), f t) + (∫ t in (I₁ ∪ I₂), f t) :=
    setIntegral_union hdisjU hmeasU hintC hintU
  have hcover : (Set.Ioi (0:ℝ) \ (I₁ ∪ I₂)) ∪ (I₁ ∪ I₂) = Set.Ioi (0:ℝ) := by
    have h := Set.union_sdiff_cancel (Set.union_subset hI₁sub hI₂sub)
    rwa [Set.union_comm] at h
  have hstep2 : (∫ t in (I₁ ∪ I₂), f t) = (∫ t in I₁, f t) + (∫ t in I₂, f t) := by
    have hd : Disjoint I₁ I₂ := by
      rw [Set.disjoint_iff_inter_eq_empty]; exact hdisj
    exact setIntegral_union hd hmeas₂ hint₁ hint₂
  rw [hS, add_assoc, ← hstep2, ← hstep1, hcover]

/-- The squared Euclidean distance of two points of `ℍ` in terms of `cosh` of their hyperbolic
distance. -/
lemma sq_norm_coe_sub_eq (z w : UpperHalfPlane) :
    ‖(z : ℂ) - (w : ℂ)‖ ^ 2 = 2 * z.im * w.im * (Real.cosh (dist z w) - 1) := by
  have h := UpperHalfPlane.cosh_dist z w
  have hX : dist (z : ℂ) (w : ℂ) ^ 2 / (2 * z.im * w.im) = Real.cosh (dist z w) - 1 := by
    linarith
  have hden : (2 * z.im * w.im) ≠ 0 := by
    have h1 := z.im_pos
    have h2 := w.im_pos
    positivity
  rw [div_eq_iff hden] at hX
  rw [dist_eq_norm] at hX
  rw [mul_comm] at hX
  exact hX

/-- `straightPartSet t₀ 0 0` is the whole positive axis. -/
lemma straightPartSet_zero (t₀ : ℝ) : straightPartSet t₀ 0 0 = Set.Ioi (0 : ℝ) := by
  rw [straightPartSet]
  simp

/-- **The hyperbolic ball of radius `ρ` around `z` stays in the half-plane `Re < 1`** (when `ρ` is at
most `(1 - z.re)/(8 z.im)` and `z.re < 1`). -/
lemma re_lt_one_of_dist_le {z w : UpperHalfPlane} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hz : z.re < 1) (hρs : ρ * (8 * z.im) ≤ 1 - z.re) (h : dist w z ≤ ρ) : w.re < 1 := by
  have hcosh : Real.cosh (dist w z) ≤ Real.cosh ρ := by
    rw [Real.cosh_le_cosh]
    rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg hρ0.le]
  have hwim : w.im ≤ z.im * Real.exp ρ := by
    have h1 : w.im ≤ z.im * Real.exp (dist w z) := UpperHalfPlane.im_le_im_mul_exp_dist w z
    have h2 : Real.exp (dist w z) ≤ Real.exp ρ := Real.exp_le_exp.mpr h
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 z.im_pos.le)
  have hexp3 : Real.exp ρ ≤ 3 := by
    have h1 : Real.exp ρ ≤ Real.exp 1 := Real.exp_le_exp.mpr hρ1
    have h2 : Real.exp 1 < 3 := Real.exp_one_lt_three
    linarith
  have hcosh2 : Real.cosh ρ - 1 ≤ ρ ^ 2 := by
    have h3 := cosh_le_one_add_sq (x := ρ) (by nlinarith)
    linarith
  have hcd : Real.cosh (dist w z) = 1 + ‖(w : ℂ) - (z : ℂ)‖ ^ 2 / (2 * z.im * w.im) := by
    rw [UpperHalfPlane.cosh_dist, dist_eq_norm]
    ring_nf
  have hden : 0 < 2 * z.im * w.im := by
    have h1 := z.im_pos
    have h2 := w.im_pos
    positivity
  have hDle : ‖(w : ℂ) - (z : ℂ)‖ ^ 2 / (2 * z.im * w.im) ≤ Real.cosh ρ - 1 := by
    have h4 : 1 + ‖(w : ℂ) - (z : ℂ)‖ ^ 2 / (2 * z.im * w.im) ≤ Real.cosh ρ := by
      rw [← hcd]; exact hcosh
    linarith
  have hdist2 : ‖(w : ℂ) - (z : ℂ)‖ ^ 2 ≤ 2 * z.im * w.im * (Real.cosh ρ - 1) := by
    have h5 := (div_le_iff₀ hden).mp hDle
    nlinarith [h5]
  have him2 : 2 * z.im * w.im * (Real.cosh ρ - 1) ≤ 2 * z.im * (z.im * 3) * ρ ^ 2 := by
    have h1 : w.im * (Real.cosh ρ - 1) ≤ (z.im * 3) * ρ ^ 2 := by
      have h3 : w.im * (Real.cosh ρ - 1) ≤ (z.im * Real.exp ρ) * ρ ^ 2 :=
        mul_le_mul hwim hcosh2 (by have := Real.one_le_cosh ρ; linarith) (by positivity)
      refine le_trans h3 ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp3 z.im_pos.le) (sq_nonneg ρ)
    nlinarith [h1, z.im_pos]
  have hnn : (0:ℝ) ≤ 3 * z.im * ρ := by
    have h1 := z.im_pos; positivity
  have hdist3 : ‖(w : ℂ) - (z : ℂ)‖ ≤ 3 * z.im * ρ := by
    have h2 : ‖(w : ℂ) - (z : ℂ)‖ ^ 2 ≤ (3 * z.im * ρ) ^ 2 := by
      have h7 : (3 * z.im * ρ) ^ 2 = 9 * z.im ^ 2 * ρ ^ 2 := by ring
      rw [h7]
      nlinarith [hdist2, him2, z.im_pos]
    nlinarith [h2, hnn, norm_nonneg ((w : ℂ) - (z : ℂ))]
  have hre : |w.re - z.re| ≤ ‖(w : ℂ) - (z : ℂ)‖ := by
    have h6 := Complex.abs_re_le_norm ((w : ℂ) - (z : ℂ))
    simpa [Complex.sub_re] using h6
  have h8 : 3 * z.im * ρ ≤ 3 * (1 - z.re) / 8 := by
    have h1 := z.im_pos
    nlinarith [hρs]
  have h7 := abs_le.mp (le_trans hre hdist3)
  linarith [h7.2]

/-- **Integrability of the naive contour integrand.**  Under the contour-cleanliness hypothesis
(every `i t`, `t > 0`, has `j`-invariant different from every `τ` of the ball with `Re τ < 1`),
the naive integrand `t ↦ K^{(d)}(τ,it)e^{-πr²t}` is integrable on `(0,∞)` for `r ≠ 0` and
(`d = 8` or `2 < r²`). -/
theorem integrableOn_naive_integrand (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {r t₀ A₁ A₂ ε : ℝ} (ht₀ : 0 < t₀) (hr : r ≠ 0)
    (hrange : d = 8 ∨ 2 < r ^ 2) (hε : 0 < ε)
    (haxis : ∀ (t : ℝ) (ht : 0 < t), ∀ τ : UpperHalfPlane,
      dist τ (onePlusI t₀ ht₀) < ε → τ.re < 1 →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε → τ.re < 1 →
      IntegrableOn (fun t : ℝ =>
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * gaussWeight r t) (Set.Ioi (0 : ℝ)) := by
  intro τ hτ1 hτ2
  set ρ : ℝ := min ((ε - dist τ (onePlusI t₀ ht₀)) / 2)
    (min 1 ((1 - τ.re) / (8 * τ.im))) with hρdef
  have hdpos : 0 < (ε - dist τ (onePlusI t₀ ht₀)) / 2 := by
    have := hτ1; linarith
  have hhpos : 0 < (1 - τ.re) / (8 * τ.im) := by
    have := τ.im_pos; positivity
  have hρ0 : 0 < ρ := lt_min hdpos (lt_min one_pos hhpos)
  have hρd : ρ ≤ (ε - dist τ (onePlusI t₀ ht₀)) / 2 := min_le_left _ _
  have hρ1 : ρ ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρs : ρ * (8 * τ.im) ≤ 1 - τ.re := by
    have h2 : ρ ≤ (1 - τ.re) / (8 * τ.im) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h2
    linarith
  have hclean : ∀ (t : ℝ) (ht : 0 < t), t ∈ straightPartSet t₀ 0 0 →
      ∀ τ' : UpperHalfPlane, dist τ' τ ≤ ρ →
        Work.Kernels.jInvariantFun τ' ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
    intro t ht htS τ' hτ'
    have hdist : dist τ' (onePlusI t₀ ht₀) < ε := by
      have h1 : dist τ' (onePlusI t₀ ht₀) ≤ dist τ' τ + dist τ (onePlusI t₀ ht₀) :=
        dist_triangle _ _ _
      linarith
    exact haxis t ht τ' hdist (re_lt_one_of_dist_le hρ0 hρ1 hτ2 hρs hτ')
  obtain ⟨bound, hbint, hbnn, hbd⟩ :=
    exists_bound_straightPart_of_clean_MR ℓ d hd hr hrange hρ0 hclean
  have hmeasK : Measurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t) :=
    measurable_Kaxis_of_measurable (Work.Kernels.Kfun ℓ d) τ
      (measurable_Kfun_snd_all ℓ d hd τ)
  refine Integrable.mono' hbint (hmeasK.mul (by unfold gaussWeight; fun_prop)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htS : t ∈ straightPartSet t₀ 0 0 := by
    rw [straightPartSet_zero]; exact ht
  have hdt : dist τ τ ≤ ρ := by rw [dist_self]; exact hρ0.le
  have h1 := hbd τ t ht hdt htS
  have h2 : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * gaussWeight r t‖
      = ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ * Real.exp (-(Real.pi * r ^ 2 * t)) := by
    rw [norm_mul, norm_gaussWeight]
  rw [h2]
  exact h1

/-- **The coordinate bounds of the ball.**  For `dist z (1+i s₀) < ε ≤ 1` one has
`|Re z - 1| < 3 s₀ ε` and `|Im z - s₀| < 3 s₀ ε`. -/
lemma abs_re_im_sub_lt {s₀ : ℝ} (hs₀ : 0 < s₀) {z : UpperHalfPlane} {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (h : dist z (onePlusI s₀ hs₀) < ε) :
    |z.re - 1| < 3 * s₀ * ε ∧ |z.im - s₀| < 3 * s₀ * ε := by
  have hcosh : Real.cosh (dist z (onePlusI s₀ hs₀)) ≤ Real.cosh ε := by
    rw [Real.cosh_le_cosh, abs_of_nonneg dist_nonneg, abs_of_nonneg hε0.le]
    exact h.le
  have hcd := UpperHalfPlane.cosh_dist' z (onePlusI s₀ hs₀)
  rw [onePlusI_re, onePlusI_im] at hcd
  have hden : 0 < 2 * z.im * s₀ := by
    have h1 := z.im_pos
    positivity
  have hkey : (z.re - 1) ^ 2 + z.im ^ 2 + s₀ ^ 2 ≤ 2 * z.im * s₀ * Real.cosh ε := by
    rw [hcd] at hcosh
    rw [div_le_iff₀ hden] at hcosh
    linarith
  have hsum : (z.re - 1) ^ 2 + (z.im - s₀) ^ 2 ≤ 2 * z.im * s₀ * (Real.cosh ε - 1) := by
    nlinarith [hkey]
  have hre_le : (z.re - 1) ^ 2 ≤ 2 * z.im * s₀ * (Real.cosh ε - 1) := by
    nlinarith [hsum, sq_nonneg (z.im - s₀)]
  have him_le : (z.im - s₀) ^ 2 ≤ 2 * z.im * s₀ * (Real.cosh ε - 1) := by
    nlinarith [hsum, sq_nonneg (z.re - 1)]
  have him : z.im ≤ s₀ * Real.exp ε := by
    have h1 : z.im ≤ (onePlusI s₀ hs₀).im * Real.exp (dist z (onePlusI s₀ hs₀)) :=
      UpperHalfPlane.im_le_im_mul_exp_dist z _
    rw [onePlusI_im] at h1
    have h2 : Real.exp (dist z (onePlusI s₀ hs₀)) ≤ Real.exp ε := Real.exp_le_exp.mpr h.le
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hs₀.le)
  have hcosh2 : Real.cosh ε - 1 ≤ ε ^ 2 := by
    have h3 := cosh_le_one_add_sq (x := ε) (by nlinarith)
    linarith
  have hcoshpos : 0 ≤ Real.cosh ε - 1 := by
    have h3 := Real.one_le_cosh ε
    linarith
  have hexp3 : Real.exp ε ≤ 3 := by
    have h1 : Real.exp ε ≤ Real.exp 1 := Real.exp_le_exp.mpr hε1
    have h2 : Real.exp 1 < 3 := Real.exp_one_lt_three
    linarith
  have hb1 : 2 * z.im * s₀ * (Real.cosh ε - 1) ≤ 2 * (s₀ * Real.exp ε) * s₀ * ε ^ 2 := by
    have h2 : 2 * z.im * s₀ ≤ 2 * (s₀ * Real.exp ε) * s₀ := by nlinarith [him, hs₀]
    calc 2 * z.im * s₀ * (Real.cosh ε - 1)
        ≤ 2 * (s₀ * Real.exp ε) * s₀ * (Real.cosh ε - 1) :=
          mul_le_mul_of_nonneg_right h2 hcoshpos
      _ ≤ 2 * (s₀ * Real.exp ε) * s₀ * ε ^ 2 :=
          mul_le_mul_of_nonneg_left hcosh2 (by positivity)
  have hb2 : 2 * (s₀ * Real.exp ε) * s₀ * ε ^ 2 < (3 * s₀ * ε) ^ 2 := by
    have h3 : (3 * s₀ * ε) ^ 2 - 2 * (s₀ * Real.exp ε) * s₀ * ε ^ 2
        = s₀ ^ 2 * ε ^ 2 * (9 - 2 * Real.exp ε) := by ring
    have h4 : 0 < 9 - 2 * Real.exp ε := by
      have hp := Real.exp_pos ε
      linarith
    have h5 : 0 < s₀ ^ 2 * ε ^ 2 * (9 - 2 * Real.exp ε) := by positivity
    linarith [h3, h5]
  have hb : 2 * z.im * s₀ * (Real.cosh ε - 1) < (3 * s₀ * ε) ^ 2 := lt_of_le_of_lt hb1 hb2
  have hpos : (0:ℝ) < 3 * s₀ * ε := by positivity
  constructor
  · have h1 : (z.re - 1) ^ 2 < (3 * s₀ * ε) ^ 2 := lt_of_le_of_lt hre_le hb
    have h2 : |z.re - 1| < |3 * s₀ * ε| := sq_lt_sq.mp h1
    rwa [abs_of_pos hpos] at h2
  · have h1 : (z.im - s₀) ^ 2 < (3 * s₀ * ε) ^ 2 := lt_of_le_of_lt him_le hb
    have h2 : |z.im - s₀| < |3 * s₀ * ε| := sq_lt_sq.mp h1
    rwa [abs_of_pos hpos] at h2

end Work.Asymptotics
