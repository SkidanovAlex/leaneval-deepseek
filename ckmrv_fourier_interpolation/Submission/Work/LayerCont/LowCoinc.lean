import Mathlib
import Submission.Work.LayerCont.Defs
import Submission.Work.LayerCont.KaxisLowBound
import Submission.Work.LayerCont.TruncHolomorphy
import Submission.Work.Asymptotics.detourLeftC_mdifferentiableOn_MR
import Submission.Work.Asymptotics.detourLeftC_eq_interval_of_clean
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

/-- **The low piece of the contour with the removable `S`-branch coincidence removed.**

In the *trunc* case (`t₀ > 1`) the moving pole `τ - 1` of `K(τ,·)` meets the truncated range
`[1,∞)`, but the low range `(0,1]` then contains the height `t₀⁻¹ = 1/τ.im` at which the
*removable* `S`-branch coincidence `j τ = j (i t)` sits: for fixed `t` the map `τ ↦ Kaxis τ t`
has a pole there, so the integrand is not holomorphic in `τ` on a set of `t` of positive measure.
This is `layerLow` with the interval `I₂ = (t₀⁻¹-A₂, t₀⁻¹+A₂)` removed and replaced by the
*residue-free* left detour `Work.Asymptotics.detourLeftC ℓ d r t₀⁻¹ A₂ ξ₂ τ` (no `resCorr`: the
coincidence is removable, `φ(TS) = 0`). -/
def layerLowCoinc (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (t₀ A₂ ξ₂ r : ℝ)
    (τ : UpperHalfPlane) : ℂ :=
  Work.Asymptotics.sinSqC r *
    ((∫ t in (Set.Ioc (0 : ℝ) 1) \ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂),
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t)
      + Work.Asymptotics.detourLeftC ℓ d r t₀⁻¹ A₂ ξ₂ τ)

/-- The indicator form of the retained integral of `layerLowCoinc`. -/
lemma layerLowCoinc_piece_eq_indicatorIoi (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (t₀ A₂ ξ₂ r : ℝ) (z : ℂ) :
    (∫ t in (Set.Ioc (0 : ℝ) 1) \ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂),
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (UpperHalfPlane.ofComplex z) t
          * Work.Asymptotics.gaussWeight r t)
      = ∫ t in Set.Ioi (0 : ℝ),
          ((Set.Ioc (0 : ℝ) 1) \ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)).indicator
            (fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (UpperHalfPlane.ofComplex z) t
              * Work.Asymptotics.gaussWeight r t) t := by
  have hEmeas : MeasurableSet ((Set.Ioc (0 : ℝ) 1) \ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)) :=
    measurableSet_Ioc.diff measurableSet_Ioo
  have hEsub : ((Set.Ioc (0 : ℝ) 1) \ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)) ⊆ Set.Ioi (0 : ℝ) :=
    fun x hx => Set.mem_Ioi.mpr hx.1.1
  rw [integral_indicator hEmeas, Measure.restrict_restrict_of_subset hEsub]

/-- **Holomorphy of the coincidence-removed low piece.** -/
theorem mdifferentiableOn_layerLowCoinc (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {t₀ A₂ ξ₂ ε r : ℝ} (ht₀ : 0 < t₀) (hA₂ : 0 < A₂) (hξ₂ : 0 < ξ₂)
    (hε : 0 < ε) (hA₂inv : A₂ < t₀⁻¹) (hI₂low : t₀⁻¹ + A₂ < 1)
    (hedge : ∀ (u v : ℝ), 0 < v →
      ((-ξ₂ < u ∧ u < 0 ∧ (v = t₀⁻¹ - A₂ ∨ v = t₀⁻¹ + A₂))
        ∨ (u = -ξ₂ ∧ t₀⁻¹ - A₂ < v ∧ v < t₀⁻¹ + A₂)) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Asymptotics.ofReImT u v))
    (hcleanAxis : ∀ (s : ℝ) (hs : 0 < s),
      s ∈ (Set.Ioc (0 : ℝ) 1) \ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs)) :
    MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => layerLowCoinc ℓ d t₀ A₂ ξ₂ r τ)
      (Metric.ball (Work.Asymptotics.onePlusI t₀ ht₀) ε) := by
  classical
  have hdet := Work.Asymptotics.detourLeftC_mdifferentiableOn_MR ℓ d hd
    (r := r) (c := t₀⁻¹) ht₀ hA₂ hξ₂ (by linarith) hε hedge
  have hpiece : ∀ x ∈ Metric.ball (Work.Asymptotics.onePlusI t₀ ht₀) ε,
      MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => ∫ t in (Set.Ioc (0 : ℝ) 1)
            \ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂),
            Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
              * Work.Asymptotics.gaussWeight r t) x := by
    intro x hx
    have hxdist : dist x (Work.Asymptotics.onePlusI t₀ ht₀) < ε := by
      simpa [Metric.mem_ball] using hx
    set ρ : ℝ := (ε - dist x (Work.Asymptotics.onePlusI t₀ ht₀)) / 2 with hρdef
    have hρpos : 0 < ρ := by rw [hρdef]; linarith
    have hρlt : dist x (Work.Asymptotics.onePlusI t₀ ht₀) + ρ < ε := by rw [hρdef]; linarith
    set E : Set ℝ := (Set.Ioc (0 : ℝ) 1) \ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂) with hEdef
    have hEmeas : MeasurableSet E := measurableSet_Ioc.diff measurableSet_Ioo
    have hEsub : E ⊆ Set.Ioi (0 : ℝ) := fun y hy => Set.mem_Ioi.mpr hy.1.1
    have hE1 : E ⊆ Set.Ioc (0 : ℝ) 1 := fun y hy => hy.1
    -- cleanliness on `E` for the whole closed ball
    have hcleanE : ∀ (t : ℝ) (ht : 0 < t), t ∈ E → ∀ τ : UpperHalfPlane, dist τ x ≤ ρ →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
      intro t ht htE τ hτ
      refine hcleanAxis t ht htE τ ?_
      calc dist τ (Work.Asymptotics.onePlusI t₀ ht₀)
          ≤ dist τ x + dist x (Work.Asymptotics.onePlusI t₀ ht₀) := dist_triangle _ _ _
        _ ≤ ρ + dist x (Work.Asymptotics.onePlusI t₀ ht₀) := by linarith
        _ < ε := by linarith
    -- the uniform bound on the retained interval
    obtain ⟨C, hCnn, hCb⟩ := KaxisBoundedLowBall ℓ d hd x ρ t₀ A₂ hA₂ hA₂inv hI₂low
      (fun w hw t ht htE => hcleanE t ht htE w (Metric.mem_closedBall.mp hw))
    -- the Gaussian factor is at most `1` on `t ≥ 0`
    have hgauss : ∀ v : ℝ, 0 ≤ v → ‖Work.Asymptotics.gaussWeight r v‖ ≤ 1 := by
      intro v hv
      rw [norm_gaussWeight, Real.exp_le_one_iff]
      have : 0 ≤ Real.pi * r ^ 2 * v := by positivity
      linarith
    set bound : ℝ → ℝ := E.indicator (fun _ => C) with hbounddef
    have hEfin : volume E ≠ ⊤ := by
      have h : volume E ≤ volume (Set.Ioc (0 : ℝ) 1) := measure_mono Set.sdiff_subset
      rw [Real.volume_Ioc] at h
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
    have hbc : IntegrableOn bound (Set.Ioi (0 : ℝ)) := by
      show Integrable (E.indicator (fun _ => C)) (volume.restrict (Set.Ioi (0 : ℝ)))
      rw [integrable_indicator_iff hEmeas]
      show Integrable (fun _ : ℝ => C) ((volume.restrict (Set.Ioi (0 : ℝ))).restrict E)
      rw [Measure.restrict_restrict_of_subset hEsub]
      exact MeasureTheory.integrableOn_const hEfin (by simp)
    -- the neighbourhood `U ⊆ ℂ` of `x`
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
    set F : ℂ → ℝ → ℂ := fun z t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d)
      (UpperHalfPlane.ofComplex z) t * Work.Asymptotics.gaussWeight r t with hFdef
    -- the domination
    have hbb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ∀ z ∈ U, ‖Set.indicator E (fun t' => F z t') t‖ ≤ bound t := by
      filter_upwards with t
      intro z hz
      by_cases htE : t ∈ E
      · have ht1 : (0 : ℝ) < t := htE.1.1
        obtain ⟨w, hwρ, hwz⟩ := hUb z hz
        have hcoe : UpperHalfPlane.ofComplex z = w := by
          apply UpperHalfPlane.ext
          rw [UpperHalfPlane.ofComplex_apply_of_im_pos (hUim z hz), UpperHalfPlane.coe_mk, hwz]
        have hKb := hCb w (Metric.mem_closedBall.mpr hwρ) t htE
        rw [Set.indicator_apply, if_pos htE, hbounddef, Set.indicator_apply, if_pos htE]
        simp only [hFdef, hcoe]
        rw [norm_mul]
        calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
              * ‖Work.Asymptotics.gaussWeight r t‖
            ≤ C * 1 := mul_le_mul hKb (hgauss t ht1.le) (norm_nonneg _) hCnn
          _ = C := mul_one _
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
        have ht0 : 0 < t := htE.1.1
        obtain ⟨w, hwρ, hwz⟩ := hUb z hz
        have hJ : Work.Kernels.jInvariantFun (⟨z, hzim⟩ : UpperHalfPlane)
            ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht0) := by
          have hdist : dist (⟨z, hzim⟩ : UpperHalfPlane) x ≤ ρ := by
            have hzw : (⟨z, hzim⟩ : UpperHalfPlane) = w := UpperHalfPlane.ext hwz.symm
            rw [hzw]; exact hwρ
          exact hcleanE t ht0 htE ⟨z, hzim⟩ hdist
        have heq2 : (fun z' : ℂ => F z' t)
            = fun z' : ℂ => Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex z')
                (Work.Kernels.imagAxis t ht0) * Work.Asymptotics.gaussWeight r t := by
          funext z'
          simp only [hFdef, Work.Kernels.Kaxis, dif_pos ht0]
        rw [heq2]
        exact (Work.Asymptotics.differentiableAt_Kfun_tau (ℓ := ℓ) (d := d) hd
          (τ := (⟨z, hzim⟩ : UpperHalfPlane)) (z := Work.Kernels.imagAxis t ht0) hJ).mul_const _
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
        have h2 : Measurable (fun t : ℝ => Work.Asymptotics.gaussWeight r t) := by
          unfold Work.Asymptotics.gaussWeight; fun_prop
        exact h1.mul h2
      have h4 : Measurable (E.indicator (fun t : ℝ => F z t)) := hFmeas.indicator hEmeas
      simpa only using h4.aestronglyMeasurable
    -- the parametric-integral engine
    have hdiffOn : DifferentiableOn ℂ
        (fun z : ℂ => ∫ t in Set.Ioi (0 : ℝ), Set.indicator E (fun t' => F z t') t) U :=
      Work.Asymptotics.differentiableOn_integral_Ioi hUopen bound hbc hbb hdiff hmeas
        (fun z hz => Work.Asymptotics.aeStronglyMeasurable_deriv_of_differentiableOn
          hUopen hmeas hdiff z hz)
    -- identify with the retained integral of `layerLowCoinc`
    refine MDifferentiableAt.mdifferentiableWithinAt ?_
    rw [UpperHalfPlane.mdifferentiableAt_iff]
    refine (hdiffOn.differentiableAt (hUopen.mem_nhds hxU)).congr_of_eventuallyEq ?_
    filter_upwards [hUopen.mem_nhds hxU] with z hz
    simp only [Function.comp_apply, hFdef]
    exact layerLowCoinc_piece_eq_indicatorIoi ℓ d t₀ A₂ ξ₂ r z
  -- assembly
  intro x hx
  simp only [layerLowCoinc]
  exact (((hpiece x hx).add
    (hdet.mdifferentiableAt (Metric.isOpen_ball.mem_nhds hx))).const_smul
    (Work.Asymptotics.sinSqC r)).mdifferentiableWithinAt

/-- The Gaussian factor is at most `1` on the non-negative half-line. -/
lemma norm_gaussWeight_le_one (r t : ℝ) (ht : 0 ≤ t) :
    ‖Work.Asymptotics.gaussWeight r t‖ ≤ 1 := by
  rw [norm_gaussWeight, Real.exp_le_one_iff]
  have h : 0 ≤ Real.pi * r ^ 2 * t := by positivity
  linarith

/-- **The coincidence-removed low piece agrees with the paper's low layer on `{Re τ < 1}`.**

The interval `I₂ = (t₀⁻¹-A₂, t₀⁻¹+A₂)` is removed from the low range `(0,1]` and replaced by the
*residue-free* left detour at height `t₀⁻¹`
(`Work.Asymptotics.detourLeftC_eq_interval_of_clean` + `edgeV_zero_eq`), so the two Lebesgue
integrals coincide.  The integrability on the two pieces is boundedness (from
`Work.LayerCont.KaxisBoundedLowBall` on the retained piece, and from the local bound
`GapBoundKaxisLow` on the compact coincidence interval) plus measurability, and needs the
cleanliness `hcleanIoc` of the *whole* low range — which for `τ.re < 1` is automatic from the web
classification of `Work.LayerCont.ECS.exists_contour_left_data` (see `Submission/ROADMAP.md`). -/
theorem layerLowCoinc_eq_layerLow (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {t₀ A₂ ξ₂ ε r : ℝ} (ht₀ : 0 < t₀) (hA₂ : 0 < A₂) (hξ₂ : 0 < ξ₂)
    (hε : 0 < ε) (hA₂inv : A₂ < t₀⁻¹) (hI₂low : t₀⁻¹ + A₂ < 1)
    (hcl : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect t₀⁻¹ A₂ ξ₂ z → z ≠ γ • τ)
    (hcleanIoc : ∀ (τ : UpperHalfPlane), dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε →
      τ.re < 1 → ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) 1 →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∀ (τ : UpperHalfPlane), dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
      layerLowCoinc ℓ d t₀ A₂ ξ₂ r τ = Work.Asymptotics.layerLow ℓ d τ r := by
  intro τ hτ hτre
  set I₂ : Set ℝ := Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂) with hI₂def
  set E : Set ℝ := (Set.Ioc (0 : ℝ) 1) \ I₂ with hEdef
  set f : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
    * Work.Asymptotics.gaussWeight r t with hfdef
  have hI₂sub : I₂ ⊆ Set.Ioc (0 : ℝ) 1 := fun x hx =>
    ⟨by linarith [hx.1, hA₂inv], by linarith [hx.2, hI₂low]⟩
  have hEmeas : MeasurableSet E := by rw [hEdef]; exact measurableSet_Ioc.diff measurableSet_Ioo
  have hI₂meas : MeasurableSet I₂ := by rw [hI₂def]; exact measurableSet_Ioo
  have hfm : Measurable f := by
    rw [hfdef]
    exact (Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).mul
      (by unfold Work.Asymptotics.gaussWeight; fun_prop)
  -- ### the detour identity (residue-free)
  have hdet : Work.Asymptotics.detourLeftC ℓ d r t₀⁻¹ A₂ ξ₂ τ = ∫ v in I₂, f v := by
    rw [Work.Asymptotics.detourLeftC_eq_interval_of_clean ℓ d (r := r) (c := t₀⁻¹) (A := A₂)
      (ξ := ξ₂) (t₀ := t₀) ht₀ hε hA₂ hξ₂ (by linarith) hcl τ hτ hτre]
    refine MeasureTheory.setIntegral_congr_fun hI₂meas (fun v hv => ?_)
    have hvpos : 0 < v := by linarith [hv.1, hA₂inv]
    rw [hfdef]
    exact edgeV_zero_eq ℓ d r τ hvpos
  -- ### bounds on the two pieces
  obtain ⟨C₁, hC₁nn, hC₁b⟩ := KaxisBoundedLowBall ℓ d hd τ 0 t₀ A₂ hA₂ hA₂inv hI₂low
    (fun w hw t ht htE => by
      have hw' : w = τ := by simpa using hw
      rw [hw']
      exact hcleanIoc τ hτ hτre t ht htE.1)
  obtain ⟨C₂, hC₂nn, hC₂b⟩ := GapBoundKaxisLow ℓ d hd (K := {τ}) isCompact_singleton
    (δ := (t₀⁻¹ - A₂) / 2) (T := t₀⁻¹ + A₂) (by linarith)
    (fun w hw t ht htI => by
      have hw' : w = τ := by simpa using hw
      rw [hw']
      exact hcleanIoc τ hτ hτre t ht ⟨by linarith [htI.1, hA₂inv], by linarith [htI.2, hI₂low]⟩)
  have hbE : ∀ t ∈ E, ‖f t‖ ≤ max C₁ 0 := by
    intro t ht
    have ht0 : 0 ≤ t := (ht.1.1).le
    rw [hfdef, norm_mul]
    exact le_trans (mul_le_mul (hC₁b τ (Metric.mem_closedBall.mpr (by simp)) t ht)
      (norm_gaussWeight_le_one r t ht0) (norm_nonneg _) hC₁nn) (by rw [mul_one]; exact le_max_left _ _)
  have hb2 : ∀ t ∈ I₂, ‖f t‖ ≤ max C₂ 0 := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt (lt_trans (by linarith [ht.1, hA₂inv]) ht.1)
    rw [hfdef, norm_mul]
    have hδ : (t₀⁻¹ - A₂) / 2 ≤ t := by linarith [ht.1, hA₂inv]
    exact le_trans (mul_le_mul (hC₂b τ t (Set.mem_singleton τ) ⟨hδ, ht.2.le⟩)
      (norm_gaussWeight_le_one r t ht0) (norm_nonneg _) hC₂nn)
      (by rw [mul_one]; exact le_max_left _ _)
  -- ### integrability of the two pieces
  have hI₂fin : volume I₂ ≠ ⊤ := by
    have h : volume I₂ ≤ volume (Set.Icc (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)) :=
      measure_mono Set.Ioo_subset_Icc_self
    rw [Real.volume_Icc] at h
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hEfin : volume E ≠ ⊤ := by
    have h : volume E ≤ volume (Set.Ioc (0 : ℝ) 1) := measure_mono Set.sdiff_subset
    rw [Real.volume_Ioc] at h
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hIntE : IntegrableOn f E := by
    haveI : IsFiniteMeasure (volume.restrict E) :=
      ⟨by rw [Measure.restrict_apply_univ]
          exact lt_of_le_of_ne le_top hEfin⟩
    refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => max C₁ 0)
      (MeasureTheory.integrable_const _) hfm.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hEmeas] with t ht
    exact hbE t ht
  have hInt2 : IntegrableOn f I₂ := by
    haveI : IsFiniteMeasure (volume.restrict I₂) :=
      ⟨by rw [Measure.restrict_apply_univ]
          exact lt_of_le_of_ne le_top hI₂fin⟩
    refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => max C₂ 0)
      (MeasureTheory.integrable_const _) hfm.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hI₂meas] with t ht
    exact hb2 t ht
  -- ### the split of the low range
  have hunion : (Set.Ioc (0 : ℝ) 1 \ I₂) ∪ I₂ = Set.Ioc (0 : ℝ) 1 := by
    rw [Set.diff_union_self]
    exact Set.union_eq_left.mpr hI₂sub
  have hsplit : (∫ t in Set.Ioc (0 : ℝ) 1, f t ∂volume)
      = (∫ t in (Set.Ioc (0 : ℝ) 1) \ I₂, f t ∂volume)
        + (∫ t in I₂, f t ∂volume) := by
    have h := MeasureTheory.setIntegral_union (s := Set.Ioc (0 : ℝ) 1 \ I₂) (t := I₂)
      Set.disjoint_sdiff_left hI₂meas hIntE hInt2
    rw [hunion] at h
    exact h
  -- ### `layerLow` as a set integral
  have hll : Work.Asymptotics.layerLow ℓ d τ r
      = Work.Asymptotics.sinSqC r * ∫ t in Set.Ioc (0 : ℝ) 1, f t := by
    rw [Work.Asymptotics.layerLow, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    congr 1
  rw [layerLowCoinc, hll, hdet, hsplit]

end Work.LayerCont
