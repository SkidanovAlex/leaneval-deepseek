/-
# The interior chart of the layer continuation: `paperLayer` is holomorphic on a ball inside `𝒟`

The CKMRV layer `F₂` restricted to the fundamental domain `𝒟` is the convergent contour integral
`paperLayer = layerLow + layerTrunc + highPart` (CKMRV (5.2)--(5.3)).  Off the imaginary axis this
is an absolutely convergent integral with a *clean* contour (`j τ ≠ j (i t)` for every `t > 0`,
`Work.LayerCont.InteriorDD.jInvariantFun_ne_imagAxis_of_mem_DomainD`), so it is holomorphic:
differentiating under the integral sign only needs

* a uniform bound for the low piece on `(0,1]` (`exists_bound_layerLow` below),
* the cusp expansion of the kernel for the trunc piece on `[1,∞)` (`TruncCuspDominator`), and
* holomorphy of the integrand in `τ` for a.e. `t` (`Work.Asymptotics.differentiableAt_Kfun_tau`,
  `Work.LayerCont.differentiableAt_Aexp_ofComplex`).

The `highPart` is the closed form of the `Aexp` tail, hence a constant-coefficient combination of
the cusp coefficient functions `Gcusp ℓ d i j`, which are holomorphic
(`Work.LayerCont.mdifferentiable_Gcusp`).

## Contents

* `mdifferentiableOn_layerLow_of_clean` — the low piece is holomorphic on a ball whose closed
  neighbourhood is contour-clean on `(0,1]`;
* `mdifferentiableOn_layerTrunc_of_clean` — the trunc piece is holomorphic on a ball whose closed
  neighbourhood is contour-clean on all of `(0,∞)`;
* `mdifferentiable_highPart` — the high piece is holomorphic (everywhere);
* `mdifferentiableOn_paperLayer_of_mem_DomainD` — the interior chart: for `τ₀ ∈ 𝒟` with
  `Re τ₀ ≠ 0` there is a ball around `τ₀` inside `𝒟` on which `τ ↦ paperLayer (Gcusp ℓ d) ℓ d τ r`
  is holomorphic, for **every** real `r` (no convergence restriction: the truncation is the
  regularised one, so nothing here depends on `r² > 2`).

NOTE (import hygiene): `Work.LayerCont.CleanBoundedBall` is *not* imported — its closure contains
`Work.Asymptotics.Kaxis_bounded_compact`, which declares `Work.Asymptotics.Pspace`, a name that is
also declared by `Work.Asymptotics.MiddleRange.Main` (in the closure of
`Work.LayerCont.GcuspHolomorphic`).  The two cannot be imported together, so the low-range bound is
rebuilt here from the `HalfFunnel` inputs `Kaxis_cusp_of_bounded` and
`exists_bound_Kfun_off_coincidence`, whose closures avoid `Kaxis_bounded_compact`.
-/
import Mathlib
import Submission.Work.CKFinal.U0Defs
import Submission.Work.LayerCont.GcuspHolomorphic
import Submission.Work.LayerCont.TruncDominator
import Submission.Work.LayerCont.TailIntegrable
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded
import Submission.Work.Asymptotics.HalfFunnel.exists_bound_Kfun_off_coincidence
import Submission.Work.Asymptotics.ParamIntegral
import Submission.Work.Asymptotics.differentiableAt_Kfun_tau
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun
import Submission.Work.Asymptotics.aeStronglyMeasurable_deriv_of_differentiableOn

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.CBEngine

open Work.Asymptotics Work.Kernels

/-! ## The two pieces as indicator integrals along the whole axis -/

/-- The plain low piece as an indicator integral over `(0,∞)`. -/
private lemma layerLow_eq_indicator (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r : ℝ) (z : ℂ) :
    Work.Asymptotics.layerLow ℓ d (UpperHalfPlane.ofComplex z) r
      = Work.Asymptotics.sinSq r * ∫ t in Set.Ioi (0 : ℝ),
          (Set.Ioc (0 : ℝ) 1).indicator
            (fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d)
              (UpperHalfPlane.ofComplex z) t * Work.Asymptotics.gaussWeight r t) t := by
  have hsub : Set.Ioc (0 : ℝ) 1 ⊆ Set.Ioi (0 : ℝ) := fun y hy => Set.mem_Ioi.mpr hy.1
  rw [Work.Asymptotics.layerLow]
  simp only [Work.Asymptotics.gaussWeight]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [MeasureTheory.integral_indicator (μ := volume.restrict (Set.Ioi (0 : ℝ))) measurableSet_Ioc,
    Measure.restrict_restrict_of_subset hsub]

/-- The trunc piece as an indicator integral over `(0,∞)`. -/
private lemma layerTrunc_eq_indicator (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r : ℝ) (z : ℂ) :
    Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d (UpperHalfPlane.ofComplex z) r
      = Work.Asymptotics.sinSq r * ∫ t in Set.Ioi (0 : ℝ),
          (Set.Ici (1 : ℝ)).indicator
            (fun t => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d)
              (UpperHalfPlane.ofComplex z) t
                - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d)
                  (UpperHalfPlane.ofComplex z) t)
              * Work.Asymptotics.gaussWeight r t) t := by
  have hsub : Set.Ici (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) :=
    fun y hy => Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one hy)
  rw [Work.Asymptotics.layerTrunc]
  simp only [Work.Asymptotics.gaussWeight]
  rw [MeasureTheory.integral_indicator (μ := volume.restrict (Set.Ioi (0 : ℝ))) measurableSet_Ici,
    Measure.restrict_restrict_of_subset hsub]

/-! ## The uniform low-range bound -/

/-- The arc `{i t : t ∈ [a,b]}` of the contour, as a subset of `ℍ`. -/
def imagArc (a b : ℝ) : Set UpperHalfPlane :=
  UpperHalfPlane.ofComplex '' ((fun t : ℝ => Complex.I * (t : ℂ)) '' Set.Icc a b)

lemma isCompact_imagArc (a b : ℝ) (h : 0 < a) : IsCompact (imagArc a b) := by
  rw [imagArc, Set.image_image]
  refine IsCompact.image_of_continuousOn isCompact_Icc ?_
  exact UpperHalfPlane.continuousOn_ofComplex_I_mul.mono
    (fun t ht => Set.mem_Ioi.mpr (lt_of_lt_of_le h ht.1))

lemma imagAxis_mem_imagArc {a b : ℝ} (h : 0 < a) {v : ℝ} (hv : v ∈ Set.Icc a b) :
    Work.Kernels.imagAxis v (lt_of_lt_of_le h hv.1) ∈ imagArc a b := by
  refine ⟨Complex.I * (v : ℂ), ⟨v, hv, rfl⟩, ?_⟩
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos
    (by rw [Complex.I_mul_im, Complex.ofReal_re]; exact lt_of_lt_of_le h hv.1)]
  apply UpperHalfPlane.ext
  show Complex.I * (v : ℂ) = (v : ℂ) * Complex.I
  rw [mul_comm]

/-- **The uniform low-range bound.**  On a closed ball whose contour is clean on `(0,1]`, the low
integrand `Kaxis · gaussWeight r` is uniformly bounded on `(0,1]`. -/
theorem exists_bound_layerLow (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ₀ : UpperHalfPlane} {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ)
    (hclean : ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) 1 → ∀ τ : UpperHalfPlane,
      dist τ τ₀ ≤ ρ → Work.Kernels.jInvariantFun τ
        ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane), dist τ τ₀ ≤ ρ →
      ∀ v ∈ Set.Icc (0 : ℝ) 1,
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v
          * Work.Asymptotics.gaussWeight r v‖ ≤ C := by
  obtain ⟨δ, hδpos, hcusp⟩ :=
    Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded ℓ d hd
      (K := Metric.closedBall τ₀ ρ) (isCompact_closedBall τ₀ ρ).isBounded
  obtain ⟨c₁, hc₁pos, hc₁b⟩ := hcusp 0 le_rfl
  have hgw : ∀ v : ℝ, 0 ≤ v → ‖Work.Asymptotics.gaussWeight r v‖ ≤ 1 := by
    intro v hv
    rw [Work.Asymptotics.norm_gaussWeight, Real.exp_le_one_iff]
    have h : (0 : ℝ) ≤ Real.pi * r ^ 2 * v := by positivity
    linarith
  by_cases hδ1 : δ ≤ 1
  · obtain ⟨C₂, hC₂pos, hC₂b⟩ := Work.Asymptotics.HalfFunnel.exists_bound_Kfun_off_coincidence
      ℓ d hd (isCompact_closedBall τ₀ ρ) (isCompact_imagArc δ 1 hδpos)
      (fun τ hτ z hz => by
        obtain ⟨w, ⟨t, ht, rfl⟩, rfl⟩ := hz
        have ht0 : 0 < t := lt_of_lt_of_le hδpos ht.1
        have hz' : UpperHalfPlane.ofComplex (Complex.I * (t : ℂ))
            = Work.Kernels.imagAxis t ht0 := by
          rw [UpperHalfPlane.ofComplex_apply_of_im_pos
            (by rw [Complex.I_mul_im, Complex.ofReal_re]; exact ht0)]
          apply UpperHalfPlane.ext
          show Complex.I * (t : ℂ) = (t : ℂ) * Complex.I
          rw [mul_comm]
        rw [hz']
        exact hclean t ht0 ⟨ht0, ht.2⟩ τ (Metric.mem_closedBall.mp hτ))
    refine ⟨max (max c₁ C₂) 1,
      le_trans (le_trans hc₁pos.le (le_max_left c₁ C₂)) (le_max_left _ 1), fun τ hτ v hv => ?_⟩
    have hτρ : τ ∈ Metric.closedBall τ₀ ρ := Metric.mem_closedBall.mpr hτ
    by_cases hv0 : 0 < v
    · rw [norm_mul]
      by_cases hvδ : v ≤ δ
      · have h1 : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v‖ ≤ c₁ := by
          have h := hc₁b τ v hτρ hv0 hvδ
          rw [Real.rpow_zero, mul_one] at h
          exact h
        calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v‖
              * ‖Work.Asymptotics.gaussWeight r v‖ ≤ c₁ * 1 :=
              mul_le_mul h1 (hgw v hv0.le) (norm_nonneg _) hc₁pos.le
          _ ≤ max (max c₁ C₂) 1 := by
              linarith [le_max_left (max c₁ C₂) 1, le_max_left c₁ C₂]
      · have hvI : v ∈ Set.Icc δ 1 := ⟨le_of_lt (lt_of_not_ge hvδ), hv.2⟩
        have h2 : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v‖ ≤ C₂ := by
          have h := hC₂b τ hτρ (Work.Kernels.imagAxis v hv0) (imagAxis_mem_imagArc hδpos hvI)
          rw [Work.Kernels.Kaxis, dif_pos hv0]
          exact h
        calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v‖
              * ‖Work.Asymptotics.gaussWeight r v‖ ≤ C₂ * 1 :=
              mul_le_mul h2 (hgw v hv0.le) (norm_nonneg _) hC₂pos.le
          _ ≤ max (max c₁ C₂) 1 := by
              linarith [le_max_left (max c₁ C₂) 1, le_max_right c₁ C₂]
    · push_neg at hv0
      rw [Work.Kernels.Kaxis, dif_neg (not_lt.mpr hv0), zero_mul, norm_zero]
      linarith [le_max_left (max c₁ C₂) 1, le_trans hc₁pos.le (le_max_left c₁ C₂)]
  · push_neg at hδ1
    refine ⟨max c₁ 1, le_trans hc₁pos.le (le_max_left c₁ 1), fun τ hτ v hv => ?_⟩
    have hτρ : τ ∈ Metric.closedBall τ₀ ρ := Metric.mem_closedBall.mpr hτ
    have hvδ : v ≤ δ := by linarith [hv.2, hδ1]
    by_cases hv0 : 0 < v
    · rw [norm_mul]
      have h1 : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v‖ ≤ c₁ := by
        have h := hc₁b τ v hτρ hv0 hvδ
        rw [Real.rpow_zero, mul_one] at h
        exact h
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v‖
            * ‖Work.Asymptotics.gaussWeight r v‖ ≤ c₁ * 1 :=
            mul_le_mul h1 (hgw v hv0.le) (norm_nonneg _) hc₁pos.le
        _ ≤ max c₁ 1 := by linarith [le_max_left c₁ 1, hc₁pos.le]
    · push_neg at hv0
      rw [Work.Kernels.Kaxis, dif_neg (not_lt.mpr hv0), zero_mul, norm_zero]
      linarith [le_max_left c₁ 1, hc₁pos.le]

/-! ## The low piece -/

/-- **The low piece is holomorphic on a contour-clean ball.** -/
theorem mdifferentiableOn_layerLow_of_clean (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {τ₀ : UpperHalfPlane} {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ)
    (hclean : ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) 1 → ∀ τ : UpperHalfPlane,
      dist τ τ₀ ≤ ρ → Work.Kernels.jInvariantFun τ
        ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => Work.Asymptotics.layerLow ℓ d τ r) (Metric.ball τ₀ ρ) := by
  classical
  obtain ⟨C, hCnn, hCb⟩ := exists_bound_layerLow ℓ d hd hρ r hclean
  intro x hx
  have hxρ : dist x τ₀ < ρ := Metric.mem_ball.mp hx
  set ρ' : ℝ := (ρ - dist x τ₀) / 2 with hρ'def
  have hρ'pos : 0 < ρ' := by rw [hρ'def]; linarith
  set E : Set ℝ := Set.Ioc (0 : ℝ) 1 with hEdef
  have hEmeas : MeasurableSet E := measurableSet_Ioc
  have hEsub : E ⊆ Set.Ioi (0 : ℝ) := fun y hy => Set.mem_Ioi.mpr hy.1
  have hEfin : volume E ≠ ⊤ := by
    rw [hEdef, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  set U : Set ℂ := (UpperHalfPlane.coe : UpperHalfPlane → ℂ) '' (Metric.ball x ρ') with hUdef
  have hUopen : IsOpen U :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ Metric.isOpen_ball
  have hxU : (x : ℂ) ∈ U := ⟨x, Metric.mem_ball_self hρ'pos, rfl⟩
  have hUim : ∀ z ∈ U, 0 < z.im := by rintro z ⟨w, _, rfl⟩; exact w.im_pos
  have hUb : ∀ z ∈ U, ∃ w : UpperHalfPlane, dist w x ≤ ρ' ∧ (w : ℂ) = z := by
    rintro z ⟨w, hw, rfl⟩
    exact ⟨w, le_of_lt (Metric.mem_ball.mp hw), rfl⟩
  have hinner : ∀ w : UpperHalfPlane, dist w x ≤ ρ' → dist w τ₀ < ρ := by
    intro w hw
    calc dist w τ₀ ≤ dist w x + dist x τ₀ := dist_triangle _ _ _
      _ ≤ ρ' + dist x τ₀ := by linarith
      _ < ρ := by rw [hρ'def]; linarith
  have hbc : IntegrableOn (fun t : ℝ => E.indicator (fun _ => C) t) (Set.Ioi (0 : ℝ)) := by
    show Integrable (E.indicator (fun _ => C)) (volume.restrict (Set.Ioi (0 : ℝ)))
    rw [integrable_indicator_iff hEmeas]
    show Integrable (fun _ : ℝ => C) ((volume.restrict (Set.Ioi (0 : ℝ))).restrict E)
    rw [Measure.restrict_restrict_of_subset hEsub]
    exact MeasureTheory.integrableOn_const hEfin (by simp)
  set F : ℂ → ℝ → ℂ := fun z t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d)
    (UpperHalfPlane.ofComplex z) t * Work.Asymptotics.gaussWeight r t with hFdef
  have hbb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ U, ‖E.indicator (fun t' => F z t') t‖ ≤ E.indicator (fun _ => C) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    by_cases htE : t ∈ E
    · rw [Set.indicator_apply, if_pos htE, Set.indicator_apply, if_pos htE]
      obtain ⟨w, hwρ, hwz⟩ := hUb z hz
      have hcoe : UpperHalfPlane.ofComplex z = w := by
        apply UpperHalfPlane.ext
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos (hUim z hz), UpperHalfPlane.coe_mk, hwz]
      have hcoe' : ‖F z t‖ = ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
          * Work.Asymptotics.gaussWeight r t‖ := by simp only [hFdef, hcoe]
      calc ‖F z t‖ = _ := hcoe'
        _ ≤ C := hCb w (hinner w hwρ).le t ⟨htE.1.le, htE.2⟩
    · rw [Set.indicator_apply, if_neg htE, Set.indicator_apply, if_neg htE, norm_zero]
  have hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ U, DifferentiableAt ℂ (fun z' => E.indicator (fun t' => F z' t') t) z := by
    filter_upwards with t
    intro z hz
    have hzim : 0 < z.im := hUim z hz
    have heq : (fun z' : ℂ => E.indicator (fun t' => F z' t') t)
        = fun z' : ℂ => if t ∈ E then F z' t else 0 := by
      funext z'; simp only [Set.indicator_apply]
    rw [heq]
    by_cases htE : t ∈ E
    · simp only [if_pos htE]
      have ht0 : 0 < t := htE.1
      obtain ⟨w, hwρ, hwz⟩ := hUb z hz
      have hJ : Work.Kernels.jInvariantFun (⟨z, hzim⟩ : UpperHalfPlane)
          ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht0) := by
        have hdist : dist (⟨z, hzim⟩ : UpperHalfPlane) x ≤ ρ' := by
          have hzw : (⟨z, hzim⟩ : UpperHalfPlane) = w := UpperHalfPlane.ext hwz.symm
          rw [hzw]; exact hwρ
        exact hclean t ht0 htE ⟨z, hzim⟩ (hinner _ hdist).le
      have heq2 : (fun z' : ℂ => F z' t) = fun z' : ℂ =>
          Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex z') (Work.Kernels.imagAxis t ht0)
            * Work.Asymptotics.gaussWeight r t := by
        funext z'; simp only [hFdef, Work.Kernels.Kaxis, dif_pos ht0]
      rw [heq2]
      exact (Work.Asymptotics.differentiableAt_Kfun_tau (ℓ := ℓ) (d := d) hd
        (τ := (⟨z, hzim⟩ : UpperHalfPlane)) (z := Work.Kernels.imagAxis t ht0) hJ).mul_const _
    · simp only [if_neg htE]; exact differentiableAt_const _
  have hmeas : ∀ z ∈ U, AEStronglyMeasurable (fun t : ℝ => E.indicator (fun t' => F z t') t)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro z hz
    have hFmeas : Measurable (fun t : ℝ => F z t) := by
      have h1 : Measurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d)
          (UpperHalfPlane.ofComplex z) t) :=
        Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd (UpperHalfPlane.ofComplex z)
      have h2 : Measurable (fun t : ℝ => Work.Asymptotics.gaussWeight r t) := by
        unfold Work.Asymptotics.gaussWeight; fun_prop
      exact h1.mul h2
    have h3 : Measurable (E.indicator (fun t : ℝ => F z t)) := hFmeas.indicator hEmeas
    simpa only using h3.aestronglyMeasurable
  have hdiffOn : DifferentiableOn ℂ
      (fun z : ℂ => ∫ t in Set.Ioi (0 : ℝ), E.indicator (fun t' => F z t') t) U :=
    Work.Asymptotics.differentiableOn_integral_Ioi hUopen (E.indicator (fun _ => C)) hbc hbb hdiff
      hmeas
      (fun z hz => Work.Asymptotics.aeStronglyMeasurable_deriv_of_differentiableOn
        hUopen hmeas hdiff z hz)
  refine MDifferentiableAt.mdifferentiableWithinAt ?_
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  refine ((hdiffOn.differentiableAt (hUopen.mem_nhds hxU)).const_mul
    (Work.Asymptotics.sinSq r)).congr_of_eventuallyEq ?_
  filter_upwards [hUopen.mem_nhds hxU] with z hz
  simp only [Function.comp_apply, hEdef, hFdef]
  exact layerLow_eq_indicator ℓ d r z

/-! ## The trunc piece -/

/-- **The trunc piece is holomorphic on a contour-clean ball.** -/
theorem mdifferentiableOn_layerTrunc_of_clean (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {τ₀ : UpperHalfPlane} {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ)
    (hclean : ∀ (t : ℝ) (ht : 0 < t), ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ ρ →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane =>
        Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r) (Metric.ball τ₀ ρ) := by
  classical
  obtain ⟨Cd, Md, T₀, hCdpos, hMdnn, hT₀nn, hdb⟩ :=
    TruncCuspDominator ℓ d hd (K := Metric.closedBall τ₀ ρ) (isCompact_closedBall τ₀ ρ)
      (t₀ := 0) (A := 0)
      (fun τ hτ s hs _ => hclean s hs τ (Metric.mem_closedBall.mp hτ))
  intro x hx
  have hxρ : dist x τ₀ < ρ := Metric.mem_ball.mp hx
  set ρ' : ℝ := (ρ - dist x τ₀) / 2 with hρ'def
  have hρ'pos : 0 < ρ' := by rw [hρ'def]; linarith
  set E : Set ℝ := Set.Ici (1 : ℝ) with hEdef
  have hEmeas : MeasurableSet E := measurableSet_Ici
  have hEsub : E ⊆ Set.Ioi (0 : ℝ) :=
    fun y hy => Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one hy)
  have hE1 : E ⊆ Set.Ici (1 : ℝ) := fun y hy => hy
  set Dfun : ℝ → ℝ := fun t => Cd * Real.exp (Real.pi * T₀)
    * ((1 + t) ^ Md * Real.exp (-(Real.pi * (1 + r ^ 2) * t))) with hDfundef
  have hDint : IntegrableOn Dfun (Set.Ici (1 : ℝ)) := by
    have ha : (0 : ℝ) < Real.pi * (1 + r ^ 2) := by positivity
    have h := TailIntegrable hMdnn ha
    exact h.const_mul (Cd * Real.exp (Real.pi * T₀))
  set bound : ℝ → ℝ := E.indicator Dfun with hbounddef
  have hbc : IntegrableOn bound (Set.Ioi (0 : ℝ)) := by
    show Integrable (E.indicator Dfun) (volume.restrict (Set.Ioi (0 : ℝ)))
    rw [integrable_indicator_iff hEmeas]
    show Integrable Dfun ((volume.restrict (Set.Ioi (0 : ℝ))).restrict E)
    rw [Measure.restrict_restrict_of_subset hEsub]
    exact hDint.mono_set hE1
  set U : Set ℂ := (UpperHalfPlane.coe : UpperHalfPlane → ℂ) '' (Metric.ball x ρ') with hUdef
  have hUopen : IsOpen U :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ Metric.isOpen_ball
  have hxU : (x : ℂ) ∈ U := ⟨x, Metric.mem_ball_self hρ'pos, rfl⟩
  have hUim : ∀ z ∈ U, 0 < z.im := by rintro z ⟨w, _, rfl⟩; exact w.im_pos
  have hUb : ∀ z ∈ U, ∃ w : UpperHalfPlane, dist w x ≤ ρ' ∧ (w : ℂ) = z := by
    rintro z ⟨w, hw, rfl⟩
    exact ⟨w, le_of_lt (Metric.mem_ball.mp hw), rfl⟩
  have hinner : ∀ w : UpperHalfPlane, dist w x ≤ ρ' → dist w τ₀ < ρ := by
    intro w hw
    calc dist w τ₀ ≤ dist w x + dist x τ₀ := dist_triangle _ _ _
      _ ≤ ρ' + dist x τ₀ := by linarith
      _ < ρ := by rw [hρ'def]; linarith
  set F : ℂ → ℝ → ℂ := fun z t => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d)
    (UpperHalfPlane.ofComplex z) t
      - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) (UpperHalfPlane.ofComplex z) t)
    * Work.Asymptotics.gaussWeight r t with hFdef
  have hbb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ U, ‖E.indicator (fun t' => F z t') t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    by_cases htE : t ∈ E
    · have ht1 : (1 : ℝ) ≤ t := Set.mem_Ici.mp htE
      obtain ⟨w, hwρ, hwz⟩ := hUb z hz
      have hcoe : UpperHalfPlane.ofComplex z = w := by
        apply UpperHalfPlane.ext
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos (hUim z hz), UpperHalfPlane.coe_mk, hwz]
      have hdist : dist w τ₀ ≤ ρ := (hinner w hwρ).le
      have hdb' := hdb w t (Metric.mem_closedBall.mpr hdist) ⟨htE, by simp⟩
      have hnormg : ‖Work.Asymptotics.gaussWeight r t‖
          = Real.exp (-(Real.pi * r ^ 2 * t)) := Work.Asymptotics.norm_gaussWeight r t
      have hexp : Real.exp (-(Real.pi * (t - T₀))) * Real.exp (-(Real.pi * r ^ 2 * t))
          = Real.exp (Real.pi * T₀) * Real.exp (-(Real.pi * (1 + r ^ 2) * t)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [Set.indicator_apply, if_pos htE, hbounddef, Set.indicator_apply, if_pos htE, hDfundef]
      simp only [hFdef, hcoe]
      calc ‖(Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t)
            * Work.Asymptotics.gaussWeight r t‖
          = ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t‖
            * ‖Work.Asymptotics.gaussWeight r t‖ := norm_mul _ _
        _ ≤ (Cd * (1 + t) ^ Md * Real.exp (-(Real.pi * (t - T₀))))
              * ‖Work.Asymptotics.gaussWeight r t‖ :=
            mul_le_mul_of_nonneg_right hdb' (norm_nonneg _)
        _ = Cd * (1 + t) ^ Md * Real.exp (-(Real.pi * (t - T₀)))
              * Real.exp (-(Real.pi * r ^ 2 * t)) := by rw [hnormg]
        _ = Cd * Real.exp (Real.pi * T₀)
              * ((1 + t) ^ Md * Real.exp (-(Real.pi * (1 + r ^ 2) * t))) := by
            have hassoc : Cd * (1 + t) ^ Md * Real.exp (-(Real.pi * (t - T₀)))
                  * Real.exp (-(Real.pi * r ^ 2 * t))
                = Cd * (1 + t) ^ Md * (Real.exp (-(Real.pi * (t - T₀)))
                  * Real.exp (-(Real.pi * r ^ 2 * t))) := by ring
            rw [hassoc, hexp]
            ring
    · rw [Set.indicator_apply, if_neg htE, norm_zero, hbounddef, Set.indicator_apply, if_neg htE]
  have hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ z ∈ U, DifferentiableAt ℂ (fun z' => E.indicator (fun t' => F z' t') t) z := by
    filter_upwards with t
    intro z hz
    have hzim : 0 < z.im := hUim z hz
    have heq : (fun z' : ℂ => E.indicator (fun t' => F z' t') t)
        = fun z' : ℂ => if t ∈ E then F z' t else 0 := by
      funext z'; simp only [Set.indicator_apply]
    rw [heq]
    by_cases htE : t ∈ E
    · simp only [if_pos htE]
      have ht1 : (1 : ℝ) ≤ t := Set.mem_Ici.mp htE
      have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
      obtain ⟨w, hwρ, hwz⟩ := hUb z hz
      have hJ : Work.Kernels.jInvariantFun (⟨z, hzim⟩ : UpperHalfPlane)
          ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht0) := by
        have hdist : dist (⟨z, hzim⟩ : UpperHalfPlane) x ≤ ρ' := by
          have hzw : (⟨z, hzim⟩ : UpperHalfPlane) = w := UpperHalfPlane.ext hwz.symm
          rw [hzw]; exact hwρ
        exact hclean t ht0 ⟨z, hzim⟩ (hinner _ hdist).le
      have heq2 : (fun z' : ℂ => F z' t)
          = fun z' : ℂ => (Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex z')
              (Work.Kernels.imagAxis t ht0)
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d)
                (UpperHalfPlane.ofComplex z') t)
            * Work.Asymptotics.gaussWeight r t := by
        funext z'; simp only [hFdef, Work.Kernels.Kaxis, dif_pos ht0]
      rw [heq2]
      exact ((Work.Asymptotics.differentiableAt_Kfun_tau (ℓ := ℓ) (d := d) hd
        (τ := (⟨z, hzim⟩ : UpperHalfPlane)) (z := Work.Kernels.imagAxis t ht0) hJ).sub
        (differentiableAt_Aexp_ofComplex ℓ d hd t (⟨z, hzim⟩ : UpperHalfPlane))).mul_const _
    · simp only [if_neg htE]; exact differentiableAt_const _
  have hmeas : ∀ z ∈ U, AEStronglyMeasurable (fun t : ℝ => E.indicator (fun t' => F z t') t)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro z hz
    have hFmeas : Measurable (fun t : ℝ => F z t) := by
      have h1 : Measurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d)
          (UpperHalfPlane.ofComplex z) t) :=
        Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd (UpperHalfPlane.ofComplex z)
      have h2 : Measurable (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d)
          (UpperHalfPlane.ofComplex z) t) :=
        (Work.LayerCont.continuous_Aexp_snd ℓ d hd (UpperHalfPlane.ofComplex z)).measurable
      have h3 : Measurable (fun t : ℝ => Work.Asymptotics.gaussWeight r t) := by
        unfold Work.Asymptotics.gaussWeight; fun_prop
      exact (h1.sub h2).mul h3
    have h4 : Measurable (E.indicator (fun t : ℝ => F z t)) := hFmeas.indicator hEmeas
    simpa only using h4.aestronglyMeasurable
  have hdiffOn : DifferentiableOn ℂ
      (fun z : ℂ => ∫ t in Set.Ioi (0 : ℝ), E.indicator (fun t' => F z t') t) U :=
    Work.Asymptotics.differentiableOn_integral_Ioi hUopen bound hbc hbb hdiff hmeas
      (fun z hz => Work.Asymptotics.aeStronglyMeasurable_deriv_of_differentiableOn
        hUopen hmeas hdiff z hz)
  refine MDifferentiableAt.mdifferentiableWithinAt ?_
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  refine ((hdiffOn.differentiableAt (hUopen.mem_nhds hxU)).const_mul
    (Work.Asymptotics.sinSq r)).congr_of_eventuallyEq ?_
  filter_upwards [hUopen.mem_nhds hxU] with z hz
  simp only [Function.comp_apply, hEdef, hFdef]
  exact layerTrunc_eq_indicator ℓ d r z

/-! ## The high piece -/

/-- **The high piece is holomorphic.**  It is a constant-coefficient combination of the cusp
coefficient functions `Gcusp ℓ d i j`, which are holomorphic on `ℍ`. -/
theorem mdifferentiable_highPart (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ r) := by
  set l : ℂ := ((Real.pi * r ^ 2 : ℝ) : ℂ) with hl
  set m : ℂ := ((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ) with hm
  have hfun : (fun τ : UpperHalfPlane =>
        Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ r)
      = fun τ : UpperHalfPlane =>
          (l * (Work.Asymptotics.psi1 (Real.pi * r ^ 2) : ℂ) * Complex.exp (-l))
              * Work.Asymptotics.Gcusp ℓ d 0 0 τ
            + ((Complex.I * (Work.Asymptotics.psi1 (Real.pi * r ^ 2) : ℂ) * (l + 1)
                * Complex.exp (-l)) * Work.Asymptotics.Gcusp ℓ d 0 1 τ
              + ((m * (Work.Asymptotics.psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℂ)
                  * Complex.exp (-m)) * Work.Asymptotics.Gcusp ℓ d 1 0 τ
                + (Complex.I * (Work.Asymptotics.psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℂ)
                    * (m + 1) * Complex.exp (-m)) * Work.Asymptotics.Gcusp ℓ d 1 1 τ)) := by
    funext τ
    simp only [Work.Asymptotics.highPart]
    rw [hl, hm]
    ring
  rw [hfun]
  have h00 := (mdifferentiable_const (c :=
    l * (Work.Asymptotics.psi1 (Real.pi * r ^ 2) : ℂ) * Complex.exp (-l))).mul
      (mdifferentiable_Gcusp ℓ d hd 0 0)
  have h01 := (mdifferentiable_const (c :=
    Complex.I * (Work.Asymptotics.psi1 (Real.pi * r ^ 2) : ℂ) * (l + 1)
      * Complex.exp (-l))).mul (mdifferentiable_Gcusp ℓ d hd 0 1)
  have h10 := (mdifferentiable_const (c :=
    m * (Work.Asymptotics.psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℂ) * Complex.exp (-m))).mul
      (mdifferentiable_Gcusp ℓ d hd 1 0)
  have h11 := (mdifferentiable_const (c :=
    Complex.I * (Work.Asymptotics.psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℂ) * (m + 1)
      * Complex.exp (-m))).mul (mdifferentiable_Gcusp ℓ d hd 1 1)
  exact h00.add (h01.add (h10.add h11))

end Work.LayerCont.CBEngine

namespace Work.CKFinal

theorem mdifferentiableOn_paperLayer_of_cleanBall (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ) {τ₀ : UpperHalfPlane} {ρ : ℝ} (hρ : 0 < ρ)
    (hclean : Work.CKFinal.CleanOnClosedBall τ₀ ρ) :
    MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r)
      (Metric.ball τ₀ ρ) := by
  have hcleanLow : ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) 1 → ∀ τ : UpperHalfPlane,
      dist τ τ₀ ≤ ρ → Work.Kernels.jInvariantFun τ
        ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) :=
    fun t ht _ τ hτ => hclean t ht τ hτ
  have hlow := Work.LayerCont.CBEngine.mdifferentiableOn_layerLow_of_clean ℓ d hd hρ r hcleanLow
  have htrunc := Work.LayerCont.CBEngine.mdifferentiableOn_layerTrunc_of_clean ℓ d hd hρ r hclean
  have hhigh := (Work.LayerCont.CBEngine.mdifferentiable_highPart ℓ d hd r).mdifferentiableOn
    (s := Metric.ball τ₀ ρ)
  exact (hlow.add htrunc).add hhigh

end Work.CKFinal
