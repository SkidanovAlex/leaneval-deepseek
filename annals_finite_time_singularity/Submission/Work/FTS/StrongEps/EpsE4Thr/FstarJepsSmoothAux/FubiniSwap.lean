import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.measurable_indicator_of_continuousOn
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.exists_bound_integral_Jker_slice
import Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.Jeps_eq_iterated

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Fubini swap for `Fstar (Jeps ρ ε W)`

`J_ε W` is, in the log coordinates, the convolution of `W` with the rescaled kernel `Jker ρ ε`,
which is supported in the closed ball of radius `ε`.  Hence the angular moment
`F_*(z) = ∫_{Iθ} (J_ε W)(z,θ) sin θ cos²θ dθ` is the triple integral

  `∫_{θ} ∫_{p₂} ∫_{p₁} sinCos2 θ · Jker ρ ε (p₁,p₂) · W (z e^{-p₁}) (thShift θ p₂)`

over `θ ∈ Iθ = [0,π/2]`, `|p₂| ≤ ε`, `p₁ ∈ ℝ`, and Fubini's theorem reorders it to

  `∫_{(θ,p₂)} sinCos2 θ · ∫_{p₁} Jker ρ ε (p₁,p₂) · W (z e^{-p₁}) (thShift θ p₂)`,

which is exactly the right hand side of `FubiniSwap` (a `p₁`-convolution at each log-angle).

The exchange is legitimate because the whole integrand is dominated by
`B · sinCos2 θ · G (thShift θ p₂)`, where `B` bounds the `p₁`-slices of the kernel
(`exists_bound_integral_Jker_slice`) and `sinCos2 θ · G (thShift θ p₂)` is integrable on
`Iθ × [-ε,ε]` by hypothesis (`hint`); the measurable structure is supplied by
`measurable_indicator_of_continuousOn` (the profile `W` is only assumed smooth on the *open*
quadrant, so it is extended by `0` off it).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

/-! ### small local helpers -/

/-- `sin θ cos²θ ≥ 0` on `(0, π/2)`. -/
theorem sinCos2_nonneg_local {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg hsin0 (sq_nonneg _)

/-- The rescaled kernel is nonnegative. -/
theorem Jker_nonneg_local {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ) (ε : ℝ)
    (p : ℝ × ℝ) : 0 ≤ Work.FTS.StrongEps.Jker ρ ε p := by
  simp only [Work.FTS.StrongEps.Jker]
  exact mul_nonneg (sq_nonneg _) (hρ.nonneg _)

/-- Every `q`-slice of the kernel is integrable: it is continuous with compact support. -/
theorem integrable_Jker_slice {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) (q : ℝ) :
    MeasureTheory.Integrable (fun p₁ : ℝ => Work.FTS.StrongEps.Jker ρ ε (p₁, q)) := by
  have hcont : Continuous fun p₁ : ℝ => Work.FTS.StrongEps.Jker ρ ε (p₁, q) :=
    (Work.FTS.StrongEps.Jker_continuous hρ ε).comp (by fun_prop)
  have hcs : HasCompactSupport fun p₁ : ℝ => Work.FTS.StrongEps.Jker ρ ε (p₁, q) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) ε) ?_
    intro p₁ hp₁
    have hmem : ((p₁, q) : ℝ × ℝ) ∈ Metric.closedBall 0 ε := by
      by_contra hc
      exact hp₁ (Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε hc)
    have h' : max |p₁| |q| ≤ ε := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using hmem
    have h1 : |p₁| ≤ ε := le_trans (le_max_left _ _) h'
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using h1
  exact hcont.integrable_of_hasCompactSupport hcs

/-! ### the swap -/

theorem FubiniSwap {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {W : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen W)
    {G : ℝ → ℝ} {a b : ℝ}
    (hdom : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |W z θ| ≤ G θ)
    (hint : MeasureTheory.Integrable (fun x : ℝ × ℝ => Work.Elliptic.sinCos2 x.1 * G (Work.FTS.StrongEps.thShift x.1 x.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod (MeasureTheory.volume.restrict (Set.Icc (-ε) ε))))
    (s : ℝ) (hs : ∀ p₁ : ℝ, p₁ ∈ Set.Icc (-ε) ε → Real.exp (s - p₁) ∈ Set.Icc a b) :
    Work.Elliptic.Fstar (Work.FTS.StrongEps.Jeps ρ ε W) (Real.exp s)
      = ∫ x : ℝ × ℝ, Work.Elliptic.sinCos2 x.1 *
          (∫ p₁ : ℝ, Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) * W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2))
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod (MeasureTheory.volume.restrict (Set.Icc (-ε) ε))) := by
  classical
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict Work.Spaces.Iθ with hμ
  set ν : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (-ε) ε) with hν
  set Fun : ℝ × ℝ → ℝ := fun x => Work.Elliptic.sinCos2 x.1 *
      (∫ p₁ : ℝ, Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) * W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2)) with hFun
  -- a.e. `θ ∈ (0, π/2)`
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [MeasureTheory.ae_restrict_iff (p := fun θ => θ ∈ Set.Ioo 0 (Real.pi / 2)) measurableSet_Ioo]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2)] with θ hθ hmem
    exact hθ.mpr hmem
  -- integrability of the integrand over the product measure
  have hInt : MeasureTheory.Integrable Fun (μ.prod ν) := by
    have hGnn : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ G θ := by
      intro θ hθ
      have hmem : (-ε) ∈ Set.Icc (-ε) ε := ⟨le_rfl, by linarith⟩
      have hz : Real.exp (s - (-ε)) ∈ Set.Icc a b := hs (-ε) hmem
      exact le_trans (abs_nonneg _) (hdom _ hz θ hθ)
    obtain ⟨B, hB0, hB⟩ := exists_bound_integral_Jker_slice hρ hε
    have hae1 : ∀ᵐ x ∂(μ.prod ν), x.1 ∈ Set.Ioo 0 (Real.pi / 2) := by
      refine (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
        (s := {x : ℝ × ℝ | x.1 ∈ Set.Ioo 0 (Real.pi / 2)}) ?_).mpr ?_
      · exact measurableSet_Ioo.preimage measurable_fst
      · exact haeθ.mono (fun θ hθ => Filter.Eventually.of_forall (fun _ => hθ))
    have hae2 : ∀ᵐ x ∂(μ.prod ν), x.2 ∈ Set.Icc (-ε) ε := by
      refine (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
        (s := {x : ℝ × ℝ | x.2 ∈ Set.Icc (-ε) ε}) ?_).mpr ?_
      · exact measurableSet_Icc.preimage measurable_snd
      · exact Filter.Eventually.of_forall (fun _ => MeasureTheory.ae_restrict_mem measurableSet_Icc)
    have hae : ∀ᵐ x ∂(μ.prod ν), x.1 ∈ Set.Ioo 0 (Real.pi / 2) ∧ x.2 ∈ Set.Icc (-ε) ε :=
      hae1.and hae2
    have hIntB : MeasureTheory.Integrable
        (fun x : ℝ × ℝ => B * (Work.Elliptic.sinCos2 x.1 * G (Work.FTS.StrongEps.thShift x.1 x.2)))
        (μ.prod ν) := hint.const_mul B
    refine hIntB.mono' ?_ ?_
    · -- a.e. strong measurability: extend `W` by `0` off the open quadrant
      set Wm : ℝ × ℝ → ℝ := Set.indicator Work.FTS.EllipticEst.Q0 (fun p : ℝ × ℝ => W p.1 p.2) with hWm
      have hWm_meas : Measurable Wm := by
        rw [hWm]
        exact measurable_indicator_of_continuousOn Work.FTS.EllipticEst.isOpen_Q0 hsm.continuousOn
      have htan : Measurable Real.tan := by
        rw [show Real.tan = fun x => Real.sin x / Real.cos x from funext Real.tan_eq_sin_div_cos]
        exact Real.measurable_sin.div Real.measurable_cos
      have hth : Measurable fun y : (ℝ × ℝ) × ℝ => Work.FTS.StrongEps.thShift y.1.1 y.1.2 := by
        simp only [Work.FTS.StrongEps.thShift]
        exact Real.measurable_arctan.comp
          ((htan.comp (measurable_fst.comp measurable_fst)).mul
            (Real.measurable_exp.comp (measurable_neg.comp (measurable_snd.comp measurable_fst))))
      have hkmeas : Measurable (Function.uncurry (fun (x : ℝ × ℝ) (p₁ : ℝ) =>
          Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) * Wm (Real.exp (s - p₁), Work.FTS.StrongEps.thShift x.1 x.2))) := by
        have h1 : Measurable fun y : (ℝ × ℝ) × ℝ => Work.FTS.StrongEps.Jker ρ ε (y.2, y.1.2) :=
          (Work.FTS.StrongEps.Jker_continuous hρ ε).measurable.comp
            (Measurable.prodMk measurable_snd (measurable_snd.comp measurable_fst))
        have h2 : Measurable fun y : (ℝ × ℝ) × ℝ =>
            Wm (Real.exp (s - y.2), Work.FTS.StrongEps.thShift y.1.1 y.1.2) :=
          hWm_meas.comp (Measurable.prodMk (Real.measurable_exp.comp (measurable_const.sub measurable_snd)) hth)
        exact h1.mul h2
      have hint_meas : MeasureTheory.StronglyMeasurable (fun x : ℝ × ℝ => ∫ p₁ : ℝ,
          Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) * Wm (Real.exp (s - p₁), Work.FTS.StrongEps.thShift x.1 x.2)) :=
        MeasureTheory.StronglyMeasurable.integral_prod_right
          (f := fun (x : ℝ × ℝ) (p₁ : ℝ) => Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) *
            Wm (Real.exp (s - p₁), Work.FTS.StrongEps.thShift x.1 x.2))
          hkmeas.stronglyMeasurable
      have hsin : MeasureTheory.StronglyMeasurable (fun x : ℝ × ℝ => Work.Elliptic.sinCos2 x.1) := by
        apply Continuous.stronglyMeasurable
        simp only [Work.Elliptic.sinCos2]
        fun_prop
      refine ((hsin.mul hint_meas).aestronglyMeasurable).congr ?_
      filter_upwards [hae1] with x hx1
      simp only [hFun, Pi.mul_apply]
      congr 1
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p₁ => ?_)
      rw [hWm]
      simp only [Set.indicator_of_mem (show (Real.exp (s - p₁), Work.FTS.StrongEps.thShift x.1 x.2)
        ∈ Work.FTS.EllipticEst.Q0 from ⟨Real.exp_pos _, Work.FTS.StrongEps.thShift_mem hx1⟩)]
    · -- the a.e. domination by the integrable envelope
      filter_upwards [hae] with x hx
      obtain ⟨hx1, hx2⟩ := hx
      have hJnn : ∀ p₁ : ℝ, 0 ≤ Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) :=
        fun p₁ => Jker_nonneg_local hρ ε _
      have hbnd : ∀ p₁ : ℝ, Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) *
            |W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2)|
          ≤ Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) * G (Work.FTS.StrongEps.thShift x.1 x.2) := by
        intro p₁
        by_cases hp : p₁ ∈ Set.Icc (-ε) ε
        · exact mul_le_mul_of_nonneg_left
            (hdom _ (hs p₁ hp) _ (Work.FTS.StrongEps.thShift_mem hx1)) (hJnn p₁)
        · -- off `[-ε,ε]` the kernel vanishes (`x.2 ∈ [-ε,ε]`)
          have hz : Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) = 0 := by
            refine Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε ?_
            intro hmem
            have h' : max |p₁| |x.2| ≤ ε := by
              simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using hmem
            exact hp (abs_le.mp (le_trans (le_max_left _ _) h'))
          rw [hz, zero_mul, zero_mul]
      have hslice_int : MeasureTheory.Integrable (fun p₁ : ℝ =>
          Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) * G (Work.FTS.StrongEps.thShift x.1 x.2)) :=
        (integrable_Jker_slice hρ hε x.2).mul_const _
      calc ‖Fun x‖
          = Work.Elliptic.sinCos2 x.1 * ‖∫ p₁ : ℝ, Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) *
              W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2)‖ := by
              rw [hFun]
              simp only [Real.norm_eq_abs, abs_mul]
              rw [abs_of_nonneg (sinCos2_nonneg_local hx1)]
        _ ≤ Work.Elliptic.sinCos2 x.1 * ∫ p₁ : ℝ, ‖Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) *
              W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2)‖ :=
              mul_le_mul_of_nonneg_left (MeasureTheory.norm_integral_le_integral_norm _)
                (sinCos2_nonneg_local hx1)
        _ = Work.Elliptic.sinCos2 x.1 * ∫ p₁ : ℝ, Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) *
              |W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2)| := by
              congr 1
              refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p₁ => ?_)
              simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hJnn p₁)]
        _ ≤ Work.Elliptic.sinCos2 x.1 * ∫ p₁ : ℝ, Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) *
              G (Work.FTS.StrongEps.thShift x.1 x.2) := by
              refine mul_le_mul_of_nonneg_left ?_ (sinCos2_nonneg_local hx1)
              refine MeasureTheory.integral_mono_of_nonneg
                (Filter.Eventually.of_forall fun p₁ => mul_nonneg (hJnn p₁) (abs_nonneg _))
                hslice_int (Filter.Eventually.of_forall hbnd)
        _ = Work.Elliptic.sinCos2 x.1 * ((∫ p₁ : ℝ, Work.FTS.StrongEps.Jker ρ ε (p₁, x.2)) *
              G (Work.FTS.StrongEps.thShift x.1 x.2)) := by
              rw [MeasureTheory.integral_mul_const]
        _ ≤ Work.Elliptic.sinCos2 x.1 * (B * G (Work.FTS.StrongEps.thShift x.1 x.2)) := by
              refine mul_le_mul_of_nonneg_left ?_ (sinCos2_nonneg_local hx1)
              exact mul_le_mul_of_nonneg_right (hB x.2) (hGnn _ (Work.FTS.StrongEps.thShift_mem hx1))
        _ = B * (Work.Elliptic.sinCos2 x.1 * G (Work.FTS.StrongEps.thShift x.1 x.2)) := by ring
  -- the right hand side is the iterated integral
  have hR : (∫ x : ℝ × ℝ, Fun x ∂(μ.prod ν)) = ∫ θ : ℝ, ∫ q : ℝ, Fun (θ, q) ∂ν ∂μ :=
    MeasureTheory.integral_prod Fun hInt
  -- the left hand side is the same iterated integral (slicewise Fubini at fixed `θ`)
  have hL : Work.Elliptic.Fstar (Work.FTS.StrongEps.Jeps ρ ε W) (Real.exp s)
      = ∫ θ : ℝ, ∫ q : ℝ, Fun (θ, q) ∂ν ∂μ := by
    have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        Work.FTS.StrongEps.Jeps ρ ε W (Real.exp s) θ * Work.Elliptic.sinCos2 θ
          = ∫ q in Set.Icc (-ε) ε, Fun (θ, q) := by
      intro θ hθ
      rw [Jeps_eq_iterated hρ hε hsm hθ]
      simp only [hFun]
      rw [MeasureTheory.integral_const_mul]
      ring
    have h1 : Work.Elliptic.Fstar (Work.FTS.StrongEps.Jeps ρ ε W) (Real.exp s)
        = ∫ θ in Work.Spaces.Iθ, ∫ q in Set.Icc (-ε) ε, Fun (θ, q) := by
      rw [Work.Elliptic.Fstar]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [haeθ] with θ hθ
      exact hpt θ hθ
    rw [h1]
  change Work.Elliptic.Fstar (Work.FTS.StrongEps.Jeps ρ ε W) (Real.exp s) = ∫ x : ℝ × ℝ, Fun x ∂(μ.prod ν)
  rw [hL]
  exact hR.symm

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
