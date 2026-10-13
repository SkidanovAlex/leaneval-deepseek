import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.Coercivity.contDiffOn_infty_integral_Itheta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptQSmooth

/-- The set integral over `Iθ = [0,π/2]` is the interval integral over `0..π/2`. -/
private theorem setIntegral_Iθ_eq_intervalIntegral (g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]

/-- **Differentiation of the mode coefficient in `z`.**  For a source `F` smooth on all of
`ℝ²`, the `m`-th angular mode coefficient `cmode m F z` (an integral over `Iθ = [0,π/2]` of
the slice `F z ·` against the mode `e_m` and the weight `cos θ`, divided by a constant) is
differentiable in `z`, with derivative the `m`-th mode coefficient of the partial derivative
`∂_z F`: differentiation under the integral sign. -/
theorem cmode_hasDerivAt_pz {F : ℝ → ℝ → ℝ}
    (hF : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry F)) (m : ℕ) (z : ℝ) :
    HasDerivAt (fun z' => Work.FTS.PhiStar.Series.cmode m F z')
      (Work.FTS.PhiStar.Series.cmode m (Work.Spaces.pz F) z) z := by
  -- smoothness of `F` as a function of two variables
  have hFdiff : Differentiable ℝ (Function.uncurry F) := (hF 1).differentiable (by norm_num)
  have hFcont : Continuous (fun p : ℝ × ℝ => F p.1 p.2) := (hF 0).continuous
  -- joint continuity of the partial derivative `∂_z F`
  have hpz_cont : Continuous (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2) := by
    have hfderiv_cont : Continuous (fderiv ℝ (Function.uncurry F)) :=
      (hF 1).continuous_fderiv (by norm_num)
    refine (hfderiv_cont.clm_apply
      (continuous_const : Continuous fun _ : ℝ × ℝ => ((1 : ℝ), (0 : ℝ)))).congr fun p => ?_
    exact (Work.Spaces.pz_eq_fderiv (hFdiff.differentiableAt)).symm
  -- continuity of the angular mode `e_m`
  have he_cont : Continuous fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
    show Continuous (fun θ : ℝ =>
      Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ))
    exact Real.continuous_cos.mul
      ((Work.FTS.PhiStar.Gegenbauer.continuous_gC (2 * m + 1)).comp Real.continuous_sin)
  -- joint continuity of the two integrands on `Set.univ ×ˢ Iθ`
  have hg : ContinuousOn
      (Function.uncurry fun s θ => F s θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      (Set.univ ×ˢ Work.Spaces.Iθ) := by
    have h : Continuous (fun p : ℝ × ℝ =>
        F p.1 p.2 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2 * Real.cos p.2) :=
      (hFcont.mul (he_cont.comp continuous_snd)).mul
        (Real.continuous_cos.comp continuous_snd)
    exact h.continuousOn
  have hgz : ContinuousOn
      (Function.uncurry fun s θ =>
        Work.Spaces.pz F s θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      (Set.univ ×ˢ Work.Spaces.Iθ) := by
    have h : Continuous (fun p : ℝ × ℝ =>
        Work.Spaces.pz F p.1 p.2 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2 * Real.cos p.2) :=
      (hpz_cont.mul (he_cont.comp continuous_snd)).mul
        (Real.continuous_cos.comp continuous_snd)
    exact h.continuousOn
  -- the pointwise derivative of the integrand is the integrand of the claimed derivative
  have hdiff : ∀ θ ∈ Work.Spaces.Iθ, ∀ s ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun s => F s θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
        (Work.Spaces.pz F s θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) s := by
    intro θ _ s _
    have hslice : DifferentiableAt ℝ (fun s' => F s' θ) s :=
      Work.Spaces.differentiableAt_curry_left (hFdiff.differentiableAt)
    have h1 : HasDerivAt (fun s' => F s' θ) (Work.Spaces.pz F s θ) s := hslice.hasDerivAt
    exact (h1.mul_const (Work.FTS.PhiStar.Gegenbauer.eFam m θ)).mul_const (Real.cos θ)
  -- differentiation under the integral sign over `Iθ`
  have hmain := Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt (V := Set.univ)
    isOpen_univ (Set.mem_univ z) hg hgz hdiff
  -- rewrite the integrals over `Iθ` as interval integrals over `0..π/2`
  have hmain' : HasDerivAt
      (fun s => ∫ θ in (0 : ℝ)..(Real.pi / 2),
        F s θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Work.Spaces.pz F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) z := by
    rw [show (fun s => ∫ θ in (0 : ℝ)..(Real.pi / 2),
          F s θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
        = (fun s => ∫ θ in Work.Spaces.Iθ,
          F s θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) from
      funext fun s => (setIntegral_Iθ_eq_intervalIntegral _).symm]
    exact hmain.congr_deriv (setIntegral_Iθ_eq_intervalIntegral _)
  -- divide by the (constant) normalising factor
  have hfin := hmain'.div_const
    (∫ θ in (0 : ℝ)..(Real.pi / 2), Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
  simpa [Work.FTS.PhiStar.Series.cmode] using hfin

end Work.FTS.PhiStar.Honesty.CptQSmooth
