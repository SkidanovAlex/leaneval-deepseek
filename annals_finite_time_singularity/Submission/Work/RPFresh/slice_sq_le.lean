/-
Copyright: work module for the Elgindi finite-time singularity project.

# The elementary slice bound for the angular weight `σ = sin(2θ)^{-η}`

If `g` is of class `C¹` on `(0,π/2)`, tends to `0` at `0⁺`, and
`∫_0^{π/2} σ (g')² < ∞` where `σ θ = sin(2θ)^{-η}` (`η = 99/100`), then

`g θ ^ 2 ≤ (∫_0^{π/2} σ (g')²) · 2^η θ^{1+η} / (1+η)`  for all `θ ∈ (0,π/2)`.

## Mathematics

* Fundamental theorem of calculus: `g θ = ∫_0^θ g'`, the singularity of `σ` at `0`
  being harmless because `∫_0^θ σ (g')² < ∞` forces `g' ∈ L¹(0,θ)` (this is
  `Work.RPFresh.deriv_integrableOn`, proved from the weighted square bound and the
  elementary inequality `√(AB) ≤ (A+B)/2`).
* Cauchy–Schwarz (`Work.RPFresh.integral_mul_sq_le_sq_mul_sq`) applied to the pair
  `(σ^{1/2} g', σ^{-1/2})` gives
  `(∫_0^θ g')² ≤ (∫_0^θ σ (g')²) · (∫_0^θ sin(2t)^η dt)`.
* `sin(2t) ≤ 2t` on `[0,π/2]` and `η > 0` give the pointwise bound
  `sin(2t)^η ≤ (2t)^η`, so the second factor is at most
  `∫_0^θ (2t)^η dt = 2^η θ^{1+η}/(1+η)` (`Work.RPFresh.integral_sin_two_rpow_le`).
* Finally `∫_0^θ σ (g')² ≤ ∫_0^{π/2} σ (g')²`, the integrand being nonnegative.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.RPFresh.Defs
import Submission.Work.RPFresh.deriv_integrableOn
import Submission.Work.RPFresh.integral_sin_two_rpow_le
import Submission.Work.RPFresh.integral_mul_sq_le_sq_mul_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.RPFresh

open MeasureTheory Set intervalIntegral Filter
open scoped Real Topology

set_option autoImplicit false

/-- **The core of the elementary slice bound.**  Under the hypotheses of
`slice_sq_le` one has, for every `θ ∈ (0,π/2)`,
`g θ ^ 2 ≤ (∫_0^θ σ (g')²) · (∫_0^θ sin(2t)^η dt)`. -/
theorem slice_sq_le_core (g : ℝ → ℝ) (hg : ContDiffOn ℝ 1 g (Set.Ioo 0 (Real.pi/2)))
    (hg0 : Filter.Tendsto g (𝓝[>] (0:ℝ)) (𝓝 0))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.RPFresh.sg θ * (deriv g θ)^2) (Set.Ioo 0 (Real.pi/2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    (g θ)^2 ≤ (∫ t in (0:ℝ)..θ, Work.FTS.EllipticEst.RPFresh.sg t * (deriv g t)^2)
      * (∫ t in (0:ℝ)..θ, (Real.sin (2*t))^(Work.Spaces.eta)) := by
  set A : ℝ → ℝ := fun t => Work.FTS.EllipticEst.RPFresh.sg t * (deriv g t)^2 with hA
  set B : ℝ → ℝ := fun t => (Real.sin (2*t))^(Work.Spaces.eta) with hB
  have hsin_nonneg : ∀ t ∈ Set.Ioc (0:ℝ) θ, 0 ≤ Real.sin (2*t) := by
    intro t ht
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1])
      (by linarith [lt_of_le_of_lt ht.2 hθ.2, Real.pi_pos])
  have hAnneg : ∀ t ∈ Set.Ioc (0:ℝ) θ, 0 ≤ A t := by
    intro t ht
    exact mul_nonneg (Real.rpow_nonneg (hsin_nonneg t ht) _) (sq_nonneg _)
  have hBnneg : ∀ t ∈ Set.Ioc (0:ℝ) θ, 0 ≤ B t := by
    intro t ht
    exact Real.rpow_nonneg (hsin_nonneg t ht) _
  -- ### Fundamental theorem of calculus: `∫_0^θ g' = g θ`
  have hderiv_int : IntegrableOn (deriv g) (Set.Ioo (0:ℝ) θ) :=
    deriv_integrableOn g hg hint hθ
  have hII : IntervalIntegrable (deriv g) volume (0:ℝ) θ := by
    rw [intervalIntegrable_iff, uIoc_of_le hθ.1.le]
    exact hderiv_int.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm
  have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) θ, HasDerivAt g (deriv g x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0:ℝ) (Real.pi/2) := ⟨hx.1, lt_trans hx.2 hθ.2⟩
    exact ((hg.differentiableOn (by norm_num)).differentiableAt
      (Ioo_mem_nhds hx'.1 hx'.2)).hasDerivAt
  have hcontθ : Tendsto g (𝓝[<] θ) (𝓝 (g θ)) :=
    ((hg.continuousOn.continuousAt (Ioo_mem_nhds hθ.1 hθ.2)).tendsto).mono_left
      nhdsWithin_le_nhds
  have hftc : ∫ t in (0:ℝ)..θ, deriv g t = g θ := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hθ.1 hderiv hII hg0 hcontθ
    simpa using h
  -- ### `|g θ| ≤ ∫ |g'|` and the pointwise identity `|g'| = √A √B` on `Ioc 0 θ`
  have habs : |g θ| ≤ ∫ t in (0:ℝ)..θ, |deriv g t| := by
    rw [← hftc]
    exact intervalIntegral.abs_integral_le_integral_abs hθ.1.le
  have hident : ∀ t ∈ Set.Ioc (0:ℝ) θ, |deriv g t| = Real.sqrt (A t) * Real.sqrt (B t) := by
    intro t ht
    have ht2 : t < Real.pi/2 := lt_of_le_of_lt ht.2 hθ.2
    have hs : 0 < Real.sin (2*t) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht2, Real.pi_pos])
    have hkey : Work.FTS.EllipticEst.RPFresh.sg t * (Real.sin (2*t))^(Work.Spaces.eta) = 1 := by
      rw [Work.FTS.EllipticEst.RPFresh.sg_def, ← Real.rpow_add hs]
      simp
    have hAB : A t * B t = (deriv g t)^2 := by
      simp only [hA, hB]
      rw [show Work.FTS.EllipticEst.RPFresh.sg t * (deriv g t)^2
            * (Real.sin (2*t))^(Work.Spaces.eta)
          = (deriv g t)^2 * (Work.FTS.EllipticEst.RPFresh.sg t
            * (Real.sin (2*t))^(Work.Spaces.eta)) by ring,
        hkey, mul_one]
    rw [show |deriv g t| = Real.sqrt ((deriv g t)^2) from
          (Real.sqrt_sq_eq_abs (deriv g t)).symm,
      ← hAB, Real.sqrt_mul (hAnneg t ht)]
  have hstep : |g θ| ≤ ∫ t in Set.Ioc (0:ℝ) θ, Real.sqrt (A t) * Real.sqrt (B t) := by
    calc |g θ| ≤ ∫ t in (0:ℝ)..θ, |deriv g t| := habs
      _ = ∫ t in Set.Ioc (0:ℝ) θ, |deriv g t| := intervalIntegral.integral_of_le hθ.1.le
      _ = ∫ t in Set.Ioc (0:ℝ) θ, Real.sqrt (A t) * Real.sqrt (B t) :=
            setIntegral_congr_fun measurableSet_Ioc hident
  -- ### integrability and measurability of the two factors
  have hAint_Ioo : IntegrableOn A (Set.Ioo (0:ℝ) θ) :=
    hint.mono_set (fun t ht => ⟨ht.1, lt_trans ht.2 hθ.2⟩)
  have hAint_Ioc : IntegrableOn A (Set.Ioc (0:ℝ) θ) :=
    hAint_Ioo.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm
  have hA_sq : IntegrableOn (fun t => (Real.sqrt (A t))^2) (Set.Ioc (0:ℝ) θ) :=
    hAint_Ioc.congr_fun_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (Real.sq_sqrt (hAnneg t ht)).symm)
  have hA_aesm : AEStronglyMeasurable (fun t => Real.sqrt (A t))
      (volume.restrict (Set.Ioc (0:ℝ) θ)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hAint_Ioc.aestronglyMeasurable
  have hBcont : ContinuousOn (fun t : ℝ => (Real.sin (2*t))^(Work.Spaces.eta))
      (Set.uIcc (0:ℝ) θ) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun x _ => Or.inr Work.Spaces.eta_pos.le)
  have hB_II : IntervalIntegrable (fun t : ℝ => (Real.sin (2*t))^(Work.Spaces.eta))
      volume (0:ℝ) θ := hBcont.intervalIntegrable
  have hBint_Ioc : IntegrableOn B (Set.Ioc (0:ℝ) θ) := by
    rw [intervalIntegrable_iff, uIoc_of_le hθ.1.le] at hB_II
    exact hB_II
  have hB_sq : IntegrableOn (fun t => (Real.sqrt (B t))^2) (Set.Ioc (0:ℝ) θ) :=
    hBint_Ioc.congr_fun_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (Real.sq_sqrt (hBnneg t ht)).symm)
  have hB_aesm : AEStronglyMeasurable (fun t => Real.sqrt (B t))
      (volume.restrict (Set.Ioc (0:ℝ) θ)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hBint_Ioc.aestronglyMeasurable
  -- ### Cauchy–Schwarz
  have hCS := integral_mul_sq_le_sq_mul_sq (volume.restrict (Set.Ioc (0:ℝ) θ))
    (f := fun t => Real.sqrt (A t)) (h := fun t => Real.sqrt (B t))
    hA_aesm hB_aesm hA_sq hB_sq
  have hAeq : ∫ t in Set.Ioc (0:ℝ) θ, (Real.sqrt (A t))^2 = ∫ t in Set.Ioc (0:ℝ) θ, A t :=
    setIntegral_congr_fun measurableSet_Ioc (fun t ht => Real.sq_sqrt (hAnneg t ht))
  have hBeq : ∫ t in Set.Ioc (0:ℝ) θ, (Real.sqrt (B t))^2 = ∫ t in Set.Ioc (0:ℝ) θ, B t :=
    setIntegral_congr_fun measurableSet_Ioc (fun t ht => Real.sq_sqrt (hBnneg t ht))
  have hCS' : (∫ t in Set.Ioc (0:ℝ) θ, Real.sqrt (A t) * Real.sqrt (B t))^2
      ≤ (∫ t in Set.Ioc (0:ℝ) θ, A t) * (∫ t in Set.Ioc (0:ℝ) θ, B t) := by
    rw [hAeq, hBeq] at hCS
    exact hCS
  -- ### assembly
  have hsq : (g θ)^2 ≤ (∫ t in Set.Ioc (0:ℝ) θ, Real.sqrt (A t) * Real.sqrt (B t))^2 := by
    rw [← sq_abs (g θ)]
    exact pow_le_pow_left₀ (abs_nonneg (g θ)) hstep 2
  have hfin : (g θ)^2 ≤ (∫ t in Set.Ioc (0:ℝ) θ, A t) * (∫ t in Set.Ioc (0:ℝ) θ, B t) :=
    hsq.trans hCS'
  have hconvA : ∫ t in Set.Ioc (0:ℝ) θ, A t = ∫ t in (0:ℝ)..θ, A t :=
    (intervalIntegral.integral_of_le hθ.1.le).symm
  have hconvB : ∫ t in Set.Ioc (0:ℝ) θ, B t = ∫ t in (0:ℝ)..θ, B t :=
    (intervalIntegral.integral_of_le hθ.1.le).symm
  rw [hconvA, hconvB] at hfin
  exact hfin

theorem slice_sq_le (g : ℝ → ℝ) (hg : ContDiffOn ℝ 1 g (Set.Ioo 0 (Real.pi/2)))
    (hg0 : Filter.Tendsto g (𝓝[>] (0:ℝ)) (𝓝 0))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.RPFresh.sg θ * (deriv g θ)^2) (Set.Ioo 0 (Real.pi/2))) :
    ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), (g θ)^2 ≤
      (∫ t in (0:ℝ)..(Real.pi/2), Work.FTS.EllipticEst.RPFresh.sg t * (deriv g t)^2)
        * (2^Work.Spaces.eta * θ^(1 + Work.Spaces.eta) / (1 + Work.Spaces.eta)) := by
  intro θ hθ
  have hcore := slice_sq_le_core g hg hg0 hint hθ
  -- monotonicity of the weighted energy in the slice
  have hIIfull : IntervalIntegrable
      (fun t => Work.FTS.EllipticEst.RPFresh.sg t * (deriv g t)^2) volume
      (0:ℝ) (Real.pi/2) := by
    rw [intervalIntegrable_iff, uIoc_of_le (le_of_lt (by positivity : (0:ℝ) < Real.pi/2))]
    exact hint.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm
  have hmono : (∫ t in (0:ℝ)..θ, Work.FTS.EllipticEst.RPFresh.sg t * (deriv g t)^2)
      ≤ (∫ t in (0:ℝ)..(Real.pi/2), Work.FTS.EllipticEst.RPFresh.sg t * (deriv g t)^2) := by
    refine integral_mono_interval
      (f := fun t => Work.FTS.EllipticEst.RPFresh.sg t * (deriv g t)^2)
      (c := (0:ℝ)) (a := (0:ℝ)) (b := θ) (d := Real.pi/2) (μ := volume)
      le_rfl hθ.1.le hθ.2.le ?_ hIIfull
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1])
      (by linarith [ht.2, Real.pi_pos])) _) (sq_nonneg _)
  -- the elementary bound on the weight `σ^{-1} = sin(2t)^η`
  have hbnd := integral_sin_two_rpow_le (θ := θ) hθ
  have hAnnB : 0 ≤ ∫ t in (0:ℝ)..θ, (Real.sin (2*t))^(Work.Spaces.eta) := by
    rw [intervalIntegral.integral_of_le hθ.1.le]
    exact setIntegral_nonneg measurableSet_Ioc (fun t ht =>
      Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1])
        (by linarith [lt_of_le_of_lt ht.2 hθ.2, Real.pi_pos])) _)
  have hAnnA : 0 ≤ ∫ t in (0:ℝ)..(Real.pi/2),
      Work.FTS.EllipticEst.RPFresh.sg t * (deriv g t)^2 := by
    rw [intervalIntegral.integral_of_le (le_of_lt (by positivity : (0:ℝ) < Real.pi/2))]
    exact setIntegral_nonneg measurableSet_Ioc (fun t ht =>
      mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1])
        (by linarith [ht.2, Real.pi_pos])) _) (sq_nonneg _))
  exact hcore.trans (mul_le_mul hmono hbnd hAnnB hAnnA)

end Work.RPFresh
