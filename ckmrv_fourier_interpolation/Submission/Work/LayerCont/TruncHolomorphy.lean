import Mathlib
import Submission.Work.LayerCont.TruncDefs
import Submission.Work.LayerCont.TruncDominator
import Submission.Work.LayerCont.GcuspHolomorphic
import Submission.Work.LayerCont.TailIntegrable
import Submission.Work.Asymptotics.detourLeftC_mdifferentiableOn_MR
import Submission.Work.Asymptotics.ParamIntegral
import Submission.Work.Asymptotics.aeStronglyMeasurable_deriv_of_differentiableOn
import Submission.Work.Asymptotics.differentiableAt_Kfun_tau
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

/-- The indicator form of `layerTruncPiece`. -/
lemma layerTruncPiece_eq_indicatorIoi (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (t₀ A r : ℝ)
    (z : ℂ) :
    layerTruncPiece ℓ d t₀ A r (UpperHalfPlane.ofComplex z)
      = ∫ t in Set.Ioi (0 : ℝ),
          (Set.Ici (1 : ℝ) \ Set.Ioo (t₀ - A) (t₀ + A)).indicator
            (fun t => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d)
                (UpperHalfPlane.ofComplex z) t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d)
                (UpperHalfPlane.ofComplex z) t)
              * Work.Asymptotics.gaussWeight r t) t := by
  have hEmeas : MeasurableSet (Set.Ici (1 : ℝ) \ Set.Ioo (t₀ - A) (t₀ + A)) :=
    measurableSet_Ici.diff measurableSet_Ioo
  have hEsub : (Set.Ici (1 : ℝ) \ Set.Ioo (t₀ - A) (t₀ + A)) ⊆ Set.Ioi (0 : ℝ) :=
    fun x hx => Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one (Set.mem_Ici.mp hx.1))
  rw [layerTruncPiece, integral_indicator hEmeas, Measure.restrict_restrict_of_subset hEsub]

/-- The indicator form of `∫_{(t₀-A,t₀+A)} Aexp · gaussWeight` (the `Aexp` detour term). -/
lemma AexpInterval_eq_indicatorIoi (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    {t₀ A : ℝ} (hhi : 1 < t₀ - A) (r : ℝ) (z : ℂ) :
    (∫ t in Set.Ioo (t₀ - A) (t₀ + A),
        Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) (UpperHalfPlane.ofComplex z) t
          * Work.Asymptotics.gaussWeight r t)
      = ∫ t in Set.Ioi (0 : ℝ),
          (Set.Ioo (t₀ - A) (t₀ + A)).indicator
            (fun t => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d)
                (UpperHalfPlane.ofComplex z) t
              * Work.Asymptotics.gaussWeight r t) t := by
  have hImeas : MeasurableSet (Set.Ioo (t₀ - A) (t₀ + A)) := measurableSet_Ioo
  have hIsub : Set.Ioo (t₀ - A) (t₀ + A) ⊆ Set.Ioi (0 : ℝ) :=
    fun x hx => Set.mem_Ioi.mpr (lt_trans (by linarith) (Set.mem_Ioo.mp hx).1)
  rw [integral_indicator hImeas, Measure.restrict_restrict_of_subset hIsub]

/-- `‖gaussWeight r t‖ = e^{-π r² t}`, and hence `≤ 1` for `t ≥ 0`. -/
lemma gaussWeight_eq (r t : ℝ) :
    Work.Asymptotics.gaussWeight r t = ((Real.exp (-(Real.pi * r ^ 2 * t)) : ℝ) : ℂ) := by
  rw [Work.Asymptotics.gaussWeight]
  congr 1
  push_cast
  ring

lemma norm_gaussWeight (r t : ℝ) :
    ‖Work.Asymptotics.gaussWeight r t‖ = Real.exp (-(Real.pi * r ^ 2 * t)) := by
  rw [gaussWeight_eq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_pos _).le]

theorem TruncHolomorphy (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {t₀ A ξ ε r : ℝ} (ht₀ : 0 < t₀) (hA : 0 < A) (hξ : 0 < ξ) (hε : 0 < ε)
    (hhi : 1 < t₀ - A)
    (hedge : ∀ (u v : ℝ), 0 < v →
      ((-ξ < u ∧ u < 0 ∧ (v = t₀ - A ∨ v = t₀ + A)) ∨ (u = -ξ ∧ t₀ - A < v ∧ v < t₀ + A)) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Asymptotics.ofReImT u v))
    (hcleanAxis : ∀ (s : ℝ) (hs : 0 < s),
      s ∈ Set.Ici (1 : ℝ) \ Set.Ioo (t₀ - A) (t₀ + A) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs)) :
    MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => layerTruncCont ℓ d t₀ A ξ r τ)
      (Metric.ball (Work.Asymptotics.onePlusI t₀ ht₀) ε) := by
  classical
  -- the detour is holomorphic
  have hdet := Work.Asymptotics.detourLeftC_mdifferentiableOn_MR ℓ d hd
    (r := r) (c := t₀) ht₀ hA hξ (by linarith) hε hedge
  -- the residue correction is entire
  have hres : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => Work.Asymptotics.resCorr r τ) := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine (by fun_prop : DifferentiableOn ℂ (fun z : ℂ =>
      Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2 * (z - 1))) {z : ℂ | 0 < z.im}).congr ?_
    intro z hz
    show Work.Asymptotics.resCorr r (UpperHalfPlane.ofComplex z)
        = Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2 * (z - 1))
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    rfl
  -- ### the retained piece `∫_E (Kaxis - Aexp)·g`
  have hpiece : ∀ x ∈ Metric.ball (Work.Asymptotics.onePlusI t₀ ht₀) ε,
      MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => layerTruncPiece ℓ d t₀ A r τ) x := by
    intro x hx
    have hxdist : dist x (Work.Asymptotics.onePlusI t₀ ht₀) < ε := by
      simpa [Metric.mem_ball] using hx
    set ρ : ℝ := (ε - dist x (Work.Asymptotics.onePlusI t₀ ht₀)) / 2 with hρdef
    have hρpos : 0 < ρ := by rw [hρdef]; linarith
    have hρlt : dist x (Work.Asymptotics.onePlusI t₀ ht₀) + ρ < ε := by rw [hρdef]; linarith
    set E : Set ℝ := Set.Ici (1 : ℝ) \ Set.Ioo (t₀ - A) (t₀ + A) with hEdef
    have hEmeas : MeasurableSet E := measurableSet_Ici.diff measurableSet_Ioo
    have hEsub : E ⊆ Set.Ioi (0 : ℝ) :=
      fun y hy => Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one (Set.mem_Ici.mp hy.1))
    have hE1 : E ⊆ Set.Ici (1 : ℝ) := fun y hy => hy.1
    -- cleanliness on `E` for the whole closed ball
    have hcleanE : ∀ (t : ℝ) (ht : 0 < t), t ∈ E → ∀ τ : UpperHalfPlane, dist τ x ≤ ρ →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
      intro t ht htE τ hτ
      refine hcleanAxis t ht htE τ ?_
      calc dist τ (Work.Asymptotics.onePlusI t₀ ht₀)
          ≤ dist τ x + dist x (Work.Asymptotics.onePlusI t₀ ht₀) := dist_triangle _ _ _
        _ ≤ ρ + dist x (Work.Asymptotics.onePlusI t₀ ht₀) := by linarith
        _ < ε := by linarith
    have hball : dist x x ≤ ρ := by simpa using hρpos.le
    -- the uniform cusp-expansion bound on the closed ball
    obtain ⟨Cd, Md, T₀, hCdpos, hMdnn, hT₀nn, hdb⟩ :=
      TruncCuspDominator ℓ d hd (K := Metric.closedBall x ρ) (isCompact_closedBall x ρ)
        (t₀ := t₀) (A := A)
        (fun τ hτ s hs hsE => hcleanE s hs hsE τ (Metric.mem_closedBall.mp hτ))
    -- the integrable dominator
    set Dfun : ℝ → ℝ := fun t => Cd * Real.exp (Real.pi * T₀)
      * ((1 + t) ^ Md * Real.exp (-(Real.pi * (1 + r ^ 2) * t))) with hDfundef
    have hDint : IntegrableOn Dfun (Set.Ici (1 : ℝ)) := by
      have ha : (0 : ℝ) < Real.pi * (1 + r ^ 2) := by positivity
      have h := TailIntegrable hMdnn ha
      have h2 : IntegrableOn (fun t : ℝ =>
          (1 + t) ^ Md * Real.exp (-(Real.pi * (1 + r ^ 2) * t))) (Set.Ici (1 : ℝ)) := h
      exact h2.const_mul (Cd * Real.exp (Real.pi * T₀))
    set bound : ℝ → ℝ := E.indicator Dfun with hbounddef
    have hbc : IntegrableOn bound (Set.Ioi (0 : ℝ)) := by
      show Integrable (E.indicator Dfun) (volume.restrict (Set.Ioi (0 : ℝ)))
      rw [integrable_indicator_iff hEmeas]
      show Integrable Dfun ((volume.restrict (Set.Ioi (0 : ℝ))).restrict E)
      rw [Measure.restrict_restrict_of_subset hEsub]
      exact hDint.mono_set hE1
    -- the neighbourhood `U ⊆ ℂ` of `x`: the image of the closed ball of radius `ρ`
    set U : Set ℂ := (UpperHalfPlane.coe : UpperHalfPlane → ℂ) '' (Metric.ball x ρ) with hUdef
    have hUopen : IsOpen U :=
      UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ Metric.isOpen_ball
    have hxU : (x : ℂ) ∈ U := ⟨x, Metric.mem_ball_self hρpos, rfl⟩
    have hUim : ∀ z ∈ U, 0 < z.im := by
      rintro z ⟨w, _, rfl⟩
      exact w.im_pos
    have hUb : ∀ z ∈ U, ∃ w : UpperHalfPlane, dist w x ≤ ρ ∧ (w : ℂ) = z := by
      rintro z ⟨w, hw, rfl⟩
      exact ⟨w, le_of_lt (Metric.mem_ball.mp hw), rfl⟩
    set F : ℂ → ℝ → ℂ := fun z t => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d)
      (UpperHalfPlane.ofComplex z) t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d)
          (UpperHalfPlane.ofComplex z) t)
      * Work.Asymptotics.gaussWeight r t with hFdef
    -- the domination
    have hbb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ∀ z ∈ U, ‖Set.indicator E (fun t' => F z t') t‖ ≤ bound t := by
      filter_upwards with t
      intro z hz
      by_cases htE : t ∈ E
      · have ht1 : (1 : ℝ) ≤ t := Set.mem_Ici.mp htE.1
        obtain ⟨w, hwρ, hwz⟩ := hUb z hz
        have hzw : (⟨z, hUim z hz⟩ : UpperHalfPlane) = w := UpperHalfPlane.ext hwz.symm
        have hdist : dist (⟨z, hUim z hz⟩ : UpperHalfPlane) x ≤ ρ := by rw [hzw]; exact hwρ
        have hdb' := hdb ⟨z, hUim z hz⟩ t (Metric.mem_closedBall.mpr hdist) htE
        have hcoe : UpperHalfPlane.ofComplex z = (⟨z, hUim z hz⟩ : UpperHalfPlane) := by
          apply UpperHalfPlane.ext
          rw [UpperHalfPlane.ofComplex_apply_of_im_pos (hUim z hz)]
        have hnormg : ‖Work.Asymptotics.gaussWeight r t‖
            = Real.exp (-(Real.pi * r ^ 2 * t)) := norm_gaussWeight r t
        have hexp : Real.exp (-(Real.pi * (t - T₀))) * Real.exp (-(Real.pi * r ^ 2 * t))
            = Real.exp (Real.pi * T₀) * Real.exp (-(Real.pi * (1 + r ^ 2) * t)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [Set.indicator_apply, if_pos htE, hbounddef, Set.indicator_apply, if_pos htE, hDfundef]
        simp only [hFdef, hcoe]
        calc ‖(Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (⟨z, hUim z hz⟩ : UpperHalfPlane) t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) (⟨z, hUim z hz⟩ : UpperHalfPlane) t)
              * Work.Asymptotics.gaussWeight r t‖
            = ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (⟨z, hUim z hz⟩ : UpperHalfPlane) t
                - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) (⟨z, hUim z hz⟩ : UpperHalfPlane) t‖
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
    -- holomorphy in `z` of the (indicator) integrand, for every `t`
    have hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ∀ z ∈ U, DifferentiableAt ℂ (fun z' => Set.indicator E (fun t' => F z' t') t) z := by
      filter_upwards with t
      intro z hz
      have hzim : 0 < z.im := hUim z hz
      have heq : (fun z' : ℂ => Set.indicator E (fun t' => F z' t') t)
          = fun z' : ℂ => if t ∈ E then F z' t else 0 := by
        funext z'
        simp only [Set.indicator_apply]
      rw [heq]
      by_cases htE : t ∈ E
      · simp only [if_pos htE]
        have ht1 : (1 : ℝ) ≤ t := Set.mem_Ici.mp htE.1
        have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
        obtain ⟨w, hwρ, hwz⟩ := hUb z hz
        have hJ : Work.Kernels.jInvariantFun (⟨z, hzim⟩ : UpperHalfPlane)
            ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht0) := by
          have hdist : dist (⟨z, hzim⟩ : UpperHalfPlane) x ≤ ρ := by
            have hzw : (⟨z, hzim⟩ : UpperHalfPlane) = w := UpperHalfPlane.ext hwz.symm
            rw [hzw]; exact hwρ
          exact hcleanE t ht0 htE ⟨z, hzim⟩ hdist
        have heq2 : (fun z' : ℂ => F z' t)
            = fun z' : ℂ => (Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex z')
                (Work.Kernels.imagAxis t ht0)
                - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d)
                  (UpperHalfPlane.ofComplex z') t)
              * Work.Asymptotics.gaussWeight r t := by
          funext z'
          simp only [hFdef, Work.Kernels.Kaxis, dif_pos ht0]
        rw [heq2]
        exact ((Work.Asymptotics.differentiableAt_Kfun_tau (ℓ := ℓ) (d := d) hd
          (τ := (⟨z, hzim⟩ : UpperHalfPlane)) (z := Work.Kernels.imagAxis t ht0) hJ).sub
          (differentiableAt_Aexp_ofComplex ℓ d hd t (⟨z, hzim⟩ : UpperHalfPlane))).mul_const _
      · simp only [if_neg htE]
        exact differentiableAt_const _
    -- measurability
    have hmeas : ∀ z ∈ U, AEStronglyMeasurable
        (fun t : ℝ => Set.indicator E (fun t' => F z t') t)
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      intro z hz
      have hFmeas : Measurable (fun t : ℝ => F z t) := by
        have h1 : Measurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d)
            (UpperHalfPlane.ofComplex z) t) :=
          Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd (UpperHalfPlane.ofComplex z)
        have h2 : Measurable (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d)
            (UpperHalfPlane.ofComplex z) t) :=
          (continuous_Aexp_snd ℓ d hd (UpperHalfPlane.ofComplex z)).measurable
        have h3 : Measurable (fun t : ℝ => Work.Asymptotics.gaussWeight r t) := by
          unfold Work.Asymptotics.gaussWeight; fun_prop
        exact ((h1.sub h2).mul h3)
      have h4 : Measurable (E.indicator (fun t : ℝ => F z t)) := hFmeas.indicator hEmeas
      simpa only using h4.aestronglyMeasurable
    -- the parametric-integral engine
    have hdiffOn : DifferentiableOn ℂ
        (fun z : ℂ => ∫ t in Set.Ioi (0 : ℝ), Set.indicator E (fun t' => F z t') t) U :=
      Work.Asymptotics.differentiableOn_integral_Ioi hUopen bound hbc hbb hdiff hmeas
        (fun z hz => Work.Asymptotics.aeStronglyMeasurable_deriv_of_differentiableOn
          hUopen hmeas hdiff z hz)
    -- identify the integral of the indicator with `layerTruncPiece`
    refine MDifferentiableAt.mdifferentiableWithinAt ?_
    rw [UpperHalfPlane.mdifferentiableAt_iff]
    refine (hdiffOn.differentiableAt (hUopen.mem_nhds hxU)).congr_of_eventuallyEq ?_
    filter_upwards [hUopen.mem_nhds hxU] with z hz
    simp only [Function.comp_apply]
    rw [layerTruncPiece_eq_indicatorIoi ℓ d t₀ A r z]
  -- ### the `Aexp` detour term `∫_I Aexp·g`
  have hAterm : ∀ x ∈ Metric.ball (Work.Asymptotics.onePlusI t₀ ht₀) ε,
      MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => ∫ t in Set.Ioo (t₀ - A) (t₀ + A),
            Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
              * Work.Asymptotics.gaussWeight r t) x := by
    intro x hx
    have hxdist : dist x (Work.Asymptotics.onePlusI t₀ ht₀) < ε := by
      simpa [Metric.mem_ball] using hx
    set ρ : ℝ := (ε - dist x (Work.Asymptotics.onePlusI t₀ ht₀)) / 2 with hρdef
    have hρpos : 0 < ρ := by rw [hρdef]; linarith
    have hρlt : dist x (Work.Asymptotics.onePlusI t₀ ht₀) + ρ < ε := by rw [hρdef]; linarith
    set I : Set ℝ := Set.Ioo (t₀ - A) (t₀ + A) with hIdef
    have hImeas : MeasurableSet I := measurableSet_Ioo
    have hIsub : I ⊆ Set.Ioi (0 : ℝ) :=
      fun y hy => Set.mem_Ioi.mpr (lt_trans (by linarith) (Set.mem_Ioo.mp hy).1)
    have hIfin : volume I ≠ ⊤ := by
      have h : volume I ≤ volume (Set.Icc (t₀ - A) (t₀ + A)) :=
        measure_mono Set.Ioo_subset_Icc_self
      rw [Real.volume_Icc] at h
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
    -- a uniform bound for the integrand on `I × closedBall`
    obtain ⟨Cae, hCaenn, haeb⟩ := Aexp_compact_bound ℓ d hd
      (K := Metric.closedBall x ρ) (isCompact_closedBall x ρ) (T := max (t₀ + A) (t₀ - A))
    have hDnn : (0 : ℝ) ≤ Cae := hCaenn
    set bound2 : ℝ → ℝ := I.indicator (fun _ => Cae) with hbound2def
    have hbc2 : IntegrableOn bound2 (Set.Ioi (0 : ℝ)) := by
      show Integrable (I.indicator (fun _ => Cae)) (volume.restrict (Set.Ioi (0 : ℝ)))
      rw [integrable_indicator_iff hImeas]
      show Integrable (fun _ : ℝ => Cae) ((volume.restrict (Set.Ioi (0 : ℝ))).restrict I)
      rw [Measure.restrict_restrict_of_subset hIsub]
      exact MeasureTheory.integrableOn_const hIfin (by simp)
    set U : Set ℂ := (UpperHalfPlane.coe : UpperHalfPlane → ℂ) '' (Metric.ball x ρ) with hUdef
    have hUopen : IsOpen U :=
      UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ Metric.isOpen_ball
    have hxU : (x : ℂ) ∈ U := ⟨x, Metric.mem_ball_self hρpos, rfl⟩
    have hUim : ∀ z ∈ U, 0 < z.im := by
      rintro z ⟨w, _, rfl⟩
      exact w.im_pos
    have hUb : ∀ z ∈ U, ∃ w : UpperHalfPlane, dist w x ≤ ρ ∧ (w : ℂ) = z := by
      rintro z ⟨w, hw, rfl⟩
      exact ⟨w, le_of_lt (Metric.mem_ball.mp hw), rfl⟩
    set F2 : ℂ → ℝ → ℂ := fun z t => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d)
      (UpperHalfPlane.ofComplex z) t * Work.Asymptotics.gaussWeight r t with hF2def
    have hbb2 : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ∀ z ∈ U, ‖Set.indicator I (fun t' => F2 z t') t‖ ≤ bound2 t := by
      filter_upwards with t
      intro z hz
      by_cases htI : t ∈ I
      · have ht0 : 0 < t := lt_trans (by linarith) (Set.mem_Ioo.mp htI).1
        obtain ⟨w, hwρ, hwz⟩ := hUb z hz
        have hcoe : UpperHalfPlane.ofComplex z = w := by
          apply UpperHalfPlane.ext
          rw [UpperHalfPlane.ofComplex_apply_of_im_pos (hUim z hz), UpperHalfPlane.coe_mk, hwz]
        have htT : |t| ≤ max (t₀ + A) (t₀ - A) := by
          rw [abs_of_pos ht0]
          exact le_trans (le_of_lt (Set.mem_Ioo.mp htI).2) (le_max_left _ _)
        have haeb' := haeb w (Metric.mem_closedBall.mpr hwρ) t htT
        have hng : ‖Work.Asymptotics.gaussWeight r t‖ ≤ 1 := by
          rw [norm_gaussWeight, Real.exp_le_one_iff]
          have hprod : (0 : ℝ) ≤ Real.pi * r ^ 2 * t :=
            mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg r)) ht0.le
          linarith
        rw [Set.indicator_apply, if_pos htI, hbound2def, Set.indicator_apply, if_pos htI]
        simp only [hF2def, hcoe]
        calc ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t
              * Work.Asymptotics.gaussWeight r t‖
            = ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t‖
              * ‖Work.Asymptotics.gaussWeight r t‖ := norm_mul _ _
          _ ≤ Cae * 1 := mul_le_mul haeb' hng (norm_nonneg _) hDnn
          _ = Cae := mul_one _
      · rw [Set.indicator_apply, if_neg htI, norm_zero, hbound2def, Set.indicator_apply, if_neg htI]
    have hdiff2 : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ∀ z ∈ U, DifferentiableAt ℂ (fun z' => Set.indicator I (fun t' => F2 z' t') t) z := by
      filter_upwards with t
      intro z hz
      have hzim : 0 < z.im := hUim z hz
      have heq : (fun z' : ℂ => Set.indicator I (fun t' => F2 z' t') t)
          = fun z' : ℂ => if t ∈ I then F2 z' t else 0 := by
        funext z'
        simp only [Set.indicator_apply]
      rw [heq]
      by_cases htI : t ∈ I
      · simp only [if_pos htI]
        exact (differentiableAt_Aexp_ofComplex ℓ d hd t (⟨z, hzim⟩ : UpperHalfPlane)).mul_const _
      · simp only [if_neg htI]
        exact differentiableAt_const _
    have hmeas2 : ∀ z ∈ U, AEStronglyMeasurable
        (fun t : ℝ => Set.indicator I (fun t' => F2 z t') t)
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      intro z hz
      have hFmeas : Measurable (fun t : ℝ => F2 z t) := by
        have h2 : Measurable (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d)
            (UpperHalfPlane.ofComplex z) t) :=
          (continuous_Aexp_snd ℓ d hd (UpperHalfPlane.ofComplex z)).measurable
        have h3 : Measurable (fun t : ℝ => Work.Asymptotics.gaussWeight r t) := by
          unfold Work.Asymptotics.gaussWeight; fun_prop
        exact h2.mul h3
      have h4 : Measurable (I.indicator (fun t : ℝ => F2 z t)) := hFmeas.indicator hImeas
      simpa only using h4.aestronglyMeasurable
    have hdiffOn : DifferentiableOn ℂ
        (fun z : ℂ => ∫ t in Set.Ioi (0 : ℝ), Set.indicator I (fun t' => F2 z t') t) U :=
      Work.Asymptotics.differentiableOn_integral_Ioi hUopen bound2 hbc2 hbb2 hdiff2 hmeas2
        (fun z hz => Work.Asymptotics.aeStronglyMeasurable_deriv_of_differentiableOn
          hUopen hmeas2 hdiff2 z hz)
    refine MDifferentiableAt.mdifferentiableWithinAt ?_
    rw [UpperHalfPlane.mdifferentiableAt_iff]
    refine (hdiffOn.differentiableAt (hUopen.mem_nhds hxU)).congr_of_eventuallyEq ?_
    filter_upwards [hUopen.mem_nhds hxU] with z hz
    simp only [Function.comp_apply]
    rw [AexpInterval_eq_indicatorIoi ℓ d hhi r z]
  -- ### assembly
  intro x hx
  simp only [layerTruncCont]
  exact (((((hpiece x hx).add
    (hdet.mdifferentiableAt (Metric.isOpen_ball.mem_nhds hx))).sub
    (hAterm x hx)).const_smul (Work.Asymptotics.sinSqC r)).add
    ((hres x).const_smul (Work.Asymptotics.sinSqC r))).mdifferentiableWithinAt

end Work.LayerCont
