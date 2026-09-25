/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Smoothness of the one-variable Cauchy transform `dbarTransform`

`dbarTransform ρ j g z = -(1/π) ∫_{‖w‖ < ρ} g (z + w e_j) / w dw` is, in the `j`-th
complex coordinate, the convolution of `g` with the (locally integrable, compactly
supported) kernel `w ↦ -(1/π) 1_{‖w‖ < ρ} w⁻¹`.

Because `g` is `Cᵐ` and vanishes for `‖y j‖ ≥ b` (with `b < ρ`), the parametrised
integrand `w ↦ g (z + w e_j) / w` is a uniformly compactly supported `Cᵐ` function of
the parameter `z`; the general smoothness theorem for parametrised convolutions
`MeasureTheory.contDiffOn_convolution_right_with_param` then shows that
`dbarTransform ρ j g` is `Cᵐ`.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.openSolDefs

noncomputable section

open scoped NNReal ENNReal Convolution
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-- Lebesgue measure on `ℂ` is invariant under `w ↦ -w`, hence so is the Bochner integral. -/
private lemma integral_comp_neg_complex (F : ℂ → ℂ) : ∫ t, F (-t) = ∫ t, F t := by
  have h := MeasurableEmbedding.integral_map (μ := (volume : Measure ℂ)) measurableEmbedding_neg F
  rw [Measure.map_neg_eq_self (volume : Measure ℂ)] at h
  exact h.symm

/-- The integral of an indicator times a function, written as a set integral. -/
private lemma integral_indicator_mul_eq_setIntegral (s : Set ℂ) (hs : MeasurableSet s)
    (f h : ℂ → ℂ) : ∫ t, s.indicator f t * h t = ∫ t in s, f t * h t := by
  rw [← MeasureTheory.integral_indicator hs (f := fun t => f t * h t)]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ s
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]

/-- The "disc Cauchy kernel" `w ↦ -1/w` on `‖w‖ < ρ` (and `0` outside) is locally integrable,
since it is dominated by `‖w‖ ^ (-1)` and `1 < finrank ℝ ℂ = 2`. -/
private lemma locallyIntegrable_cauchyKernelBall (ρ : ℝ) :
    LocallyIntegrable ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹)))
      (volume : Measure ℂ) := by
  refine MeasureTheory.locallyIntegrable_of_norm_le_rpow (E := ℂ) (F := ℂ) (C := 1) (α := 1)
    (le_of_lt (by rw [Complex.finrank_real_complex]; norm_num))
    (by rw [Complex.finrank_real_complex]; norm_num) ?_ ?_
  · filter_upwards with x
    by_cases hx : x = 0
    · subst hx; simp
    · rw [Real.rpow_neg_one, one_mul]
      by_cases hxb : x ∈ Metric.ball (0 : ℂ) ρ
      · rw [Set.indicator_of_mem hxb, norm_neg, norm_inv]
      · rw [Set.indicator_of_notMem hxb, norm_zero]
        positivity
  · exact ((measurable_inv.neg).indicator measurableSet_ball).aestronglyMeasurable

/-- The disc integral defining `dbarTransform` equals the integral of the "sign-flipped"
Cauchy kernel against `g`, obtained through the substitution `w ↦ -w`. -/
private lemma setIntegral_ball_eq_cauchyKernel {n : ℕ} (ρ : ℝ) (j : Fin n)
    (g : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    (∫ w in Metric.ball (0 : ℂ) ρ, g (z + Function.update (0 : Fin n → ℂ) j w) / w)
      = ∫ t, ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹))) t
            * g (z + Function.update (0 : Fin n → ℂ) j (-t)) := by
  have hKneg : ∀ t : ℂ, ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹))) (-t)
      = ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => a⁻¹)) t := by
    intro t
    by_cases ht : t ∈ Metric.ball (0 : ℂ) ρ
    · have hnt : -t ∈ Metric.ball (0 : ℂ) ρ := by
        rw [Metric.mem_ball, dist_zero_right] at ht ⊢
        simpa using ht
      simp only [Set.indicator_of_mem hnt, Set.indicator_of_mem ht, inv_neg, neg_neg]
    · have hnt : -t ∉ Metric.ball (0 : ℂ) ρ := by
        rw [Metric.mem_ball, dist_zero_right] at ht ⊢
        simpa using ht
      simp only [Set.indicator_of_notMem hnt, Set.indicator_of_notMem ht]
  have h1 : (∫ t, ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹))) t
                * g (z + Function.update (0 : Fin n → ℂ) j (-t)))
          = ∫ t, ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹))) (-t)
                * g (z + Function.update (0 : Fin n → ℂ) j t) := by
    have h := integral_comp_neg_complex (fun t : ℂ =>
      ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹))) t
        * g (z + Function.update (0 : Fin n → ℂ) j (-t)))
    simp only [neg_neg] at h
    exact h.symm
  have h2 : (∫ t, ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹))) (-t)
                * g (z + Function.update (0 : Fin n → ℂ) j t))
          = ∫ t in Metric.ball (0 : ℂ) ρ,
              t⁻¹ * g (z + Function.update (0 : Fin n → ℂ) j t) := by
    simp only [hKneg]
    exact integral_indicator_mul_eq_setIntegral (Metric.ball (0 : ℂ) ρ) measurableSet_ball
      (fun a : ℂ => a⁻¹) (fun t : ℂ => g (z + Function.update (0 : Fin n → ℂ) j t))
  calc (∫ w in Metric.ball (0 : ℂ) ρ, g (z + Function.update (0 : Fin n → ℂ) j w) / w)
      = ∫ t in Metric.ball (0 : ℂ) ρ,
          t⁻¹ * g (z + Function.update (0 : Fin n → ℂ) j t) := by
        apply setIntegral_congr_fun measurableSet_ball
        intro t _
        change g (z + Function.update (0 : Fin n → ℂ) j t) / t
          = t⁻¹ * g (z + Function.update (0 : Fin n → ℂ) j t)
        rw [div_eq_mul_inv, mul_comm]
    _ = ∫ t, ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹))) (-t)
            * g (z + Function.update (0 : Fin n → ℂ) j t) := h2.symm
    _ = ∫ t, ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹))) t
            * g (z + Function.update (0 : Fin n → ℂ) j (-t)) := h1.symm

/-- Pointwise, `dbarTransform` is (up to the constant `-1/π`) the convolution, in the `j`-th
coordinate, of `g` with the disc Cauchy kernel. -/
private lemma dbarTransform_eq_convolution {n : ℕ} (ρ : ℝ) (j : Fin n)
    (g : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    dbarTransform ρ j g z
      = -((Real.pi : ℂ))⁻¹
        * convolution ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹)))
            (fun t : ℂ => g (z + Function.update (0 : Fin n → ℂ) j t))
            (ContinuousLinearMap.mul ℝ ℂ) (volume : Measure ℂ) 0 := by
  simp only [dbarTransform, MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply',
    zero_sub]
  rw [setIntegral_ball_eq_cauchyKernel ρ j g z]

theorem contDiff_dbarTransform {n : ℕ} {ρ b : ℝ} (hρ : b < ρ) (j : Fin n) (m : ℕ)
    {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ m g) (hsupp : ∀ y, b ≤ ‖y j‖ → g y = 0) :
    ContDiff ℝ m (dbarTransform ρ j g) := by
  have := hρ
  set K : ℂ → ℂ := (Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹)) with hK
  set Gt : (Fin n → ℂ) → ℂ → ℂ :=
    fun p t => g (p + Function.update (0 : Fin n → ℂ) j t) with hGt
  set F : (Fin n → ℂ) → ℂ :=
    fun z => convolution K (Gt z) (ContinuousLinearMap.mul ℝ ℂ) (volume : Measure ℂ) 0 with hF
  have hident : dbarTransform ρ j g = fun z => -((Real.pi : ℂ))⁻¹ * F z := by
    funext z
    simp only [hF, hK, hGt]
    exact dbarTransform_eq_convolution ρ j g z
  have hupd : ContDiff ℝ m (fun t : ℂ => Function.update (0 : Fin n → ℂ) j t) := by
    rw [contDiff_pi]
    intro l
    by_cases hl : l = j
    · have hcomp : (fun t : ℂ => Function.update (0 : Fin n → ℂ) j t l) = fun t : ℂ => t := by
        funext t
        simp only [Function.update_apply, ite_eq_left hl]
      rw [hcomp]; exact contDiff_id
    · have hcomp : (fun t : ℂ => Function.update (0 : Fin n → ℂ) j t l)
          = fun _ : ℂ => (0 : ℂ) := by
        funext t
        simp only [Function.update_apply, ite_eq_right hl]
        rfl
      rw [hcomp]; exact contDiff_const
  have hT : ContDiff ℝ m
      (fun q : (Fin n → ℂ) × ℂ => q.1 + Function.update (0 : Fin n → ℂ) j q.2) :=
    (contDiff_fst (E := Fin n → ℂ) (F := ℂ)).add (hupd.comp contDiff_snd)
  have hFsm : ContDiff ℝ m F := by
    rw [contDiff_iff_contDiffAt]
    intro z
    set R : ℝ := ‖z‖ + 1 with hR
    have hRpos : 0 < R := by rw [hR]; positivity
    have hzR : z ∈ Metric.ball (0 : Fin n → ℂ) R := by
      rw [Metric.mem_ball, dist_zero_right, hR]; linarith
    have hGtsm : ContDiff ℝ m (Function.uncurry Gt) := by
      have hu : Function.uncurry Gt
          = fun q : (Fin n → ℂ) × ℂ => g (q.1 + Function.update (0 : Fin n → ℂ) j q.2) := by
        funext q
        simp only [Function.uncurry, hGt]
      rw [hu]
      exact hg.comp hT
    have hk : IsCompact (Metric.closedBall (0 : ℂ) (R + b)) := isCompact_closedBall _ _
    have hsupp_conv : ∀ p : Fin n → ℂ, ∀ t : ℂ, p ∈ Metric.ball (0 : Fin n → ℂ) R →
        t ∉ Metric.closedBall (0 : ℂ) (R + b) → Gt p t = 0 := by
      intro p t hp ht
      have hp' : ‖p‖ < R := by
        rw [Metric.mem_ball, dist_zero_right] at hp; exact hp
      have ht' : R + b < ‖t‖ := by
        rw [Metric.mem_closedBall, dist_zero_right] at ht
        exact lt_of_not_ge ht
      have hpt : b ≤ ‖(p + Function.update (0 : Fin n → ℂ) j t) j‖ := by
        have hja : (p + Function.update (0 : Fin n → ℂ) j t) j = p j + t := by
          simp [Pi.add_apply]
        rw [hja]
        have h1 : ‖t‖ ≤ ‖p j + t‖ + ‖p j‖ := by
          have h2 : (p j + t) - p j = t := by ring
          calc ‖t‖ = ‖(p j + t) - p j‖ := by rw [h2]
            _ ≤ ‖p j + t‖ + ‖p j‖ := norm_sub_le _ _
        have h2 : ‖p j‖ ≤ ‖p‖ := norm_le_pi_norm p j
        linarith
      simp only [hGt]
      exact hsupp _ hpt
    have hcont : ContDiffOn ℝ m (Function.uncurry Gt)
        (Metric.ball (0 : Fin n → ℂ) R ×ˢ Set.univ) := hGtsm.contDiffOn
    have hconv := MeasureTheory.contDiffOn_convolution_right_with_param
        (L := ContinuousLinearMap.mul ℝ ℂ) (f := K) (g := Gt) (μ := (volume : Measure ℂ))
        (s := Metric.ball (0 : Fin n → ℂ) R) (k := Metric.closedBall (0 : ℂ) (R + b)) (n := m)
        Metric.isOpen_ball hk hsupp_conv (locallyIntegrable_cauchyKernelBall ρ) hcont
    have hcomp := hconv.comp
        (contDiffOn_id.prodMk (contDiffOn_const (c := (0 : ℂ))))
        (fun x hx => ⟨hx, trivial⟩)
    have hz : ContDiffAt ℝ m
        (fun p : Fin n → ℂ =>
          convolution K (Gt p) (ContinuousLinearMap.mul ℝ ℂ) (volume : Measure ℂ) 0) z :=
      hcomp.contDiffAt (Metric.isOpen_ball.mem_nhds hzR)
    simpa only [hF] using hz
  rw [hident]
  exact contDiff_const.mul hFsm

end Work.CR.Flat.Cauchy
