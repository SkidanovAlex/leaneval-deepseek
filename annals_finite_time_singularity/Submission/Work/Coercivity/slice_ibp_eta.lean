import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.slice_ibp
import Submission.Work.Coercivity.sliceEtaAux
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Auxiliary integrability lemmas for the `η`-weighted angular integration by parts -/

/-- `sin(2θ)^{-η}` is integrable on `Iθ`, since `-1 < -η ≤ 0`. -/
theorem integrableOn_sin_two_eta_neg :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      Work.Spaces.Iθ := by
  have h1 : (-1 : ℝ) < -Work.Spaces.eta := by
    have := Work.Spaces.eta_lt_one
    linarith
  have h2 : -Work.Spaces.eta ≤ 0 := by
    have := Work.Spaces.eta_pos
    linarith
  exact (Work.Spaces.sin_two_rpow (-Work.Spaces.eta) h1 h2).1

/-- The right-hand integrand `cos(2θ)·g²·sin(2θ)^{-η}` of `slice_ibp_eta` is integrable on
`Iθ`: on the compact interval the slice `θ ↦ g z θ` is bounded, and `sin(2θ)^{-η}` is
integrable there. -/
theorem integrableOn_cos_sin_eta_mul_sq (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => Real.cos (2 * θ) * (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      Work.Spaces.Iθ := by
  have hw := integrableOn_sin_two_eta_neg
  have hcont : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ) * (g z θ) ^ 2) Work.Spaces.Iθ :=
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).mul
      ((slice_continuousOn g hg hz).pow 2)
  have h := hw.mul_continuousOn hcont isCompact_Icc
  exact h.congr_fun (fun θ _ => by ring) measurableSet_Icc

/-- The left-hand integrand `D_θg·g·sin(2θ)^{-η} = sin(2θ)^{1-η}·∂_θg·g` of `slice_ibp_eta`
is integrable on `Iθ`: the factor `sin(2θ)` in `D_θ` cancels the singularity of the weight,
and the two slices are continuous, hence bounded, on the compact interval. -/
theorem integrableOn_dth_mul_g_eta (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.Dth g z θ * g z θ * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      Work.Spaces.Iθ := by
  have hw := integrableOn_sin_two_eta_neg
  have hcont : ContinuousOn (fun θ => Work.Spaces.Dth g z θ * g z θ) Work.Spaces.Iθ := by
    show ContinuousOn (fun θ => (Real.sin (2 * θ) * Work.Spaces.pth g z θ) * g z θ)
      Work.Spaces.Iθ
    exact (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).mul
      (slice_pth_continuousOn g hg hz)).mul (slice_continuousOn g hg hz)
  have h := hw.mul_continuousOn hcont isCompact_Icc
  exact h.congr_fun (fun θ _ => by ring) measurableSet_Icc

/-- The derivative of the boundary term `ψ(θ) = sin(2θ)^{1-η}g(z,θ)²`.  This is
`Work.Coercivity.slice_psi_hasDerivAt` with `γ - 1 = η - 1`, i.e. with `α = 10(η-1)`
(note that no positivity of `α` is required there); the derivative is `etaPsi'`. -/
theorem etaPsi_hasDerivAt (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) {z : ℝ} (hz : 0 < z)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' => etaPsi g z θ') (etaPsi' g z θ) θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have h := slice_psi_hasDerivAt (10 * (Work.Spaces.eta - 1)) g hg z θ hz hθ hsin
  have hgam : Work.Spaces.gam (10 * (Work.Spaces.eta - 1)) = Work.Spaces.eta := by
    simp only [Work.Spaces.gam, Work.Spaces.eta]
    norm_num
  have hgam1 : Work.Spaces.gam (10 * (Work.Spaces.eta - 1)) - 1 = Work.Spaces.eta - 1 := by
    rw [hgam]
  have hexp : -(Work.Spaces.gam (10 * (Work.Spaces.eta - 1)) - 1) = 1 - Work.Spaces.eta := by
    rw [hgam1]; ring
  have hexp2 : -(Work.Spaces.gam (10 * (Work.Spaces.eta - 1))) = -Work.Spaces.eta := by rw [hgam]
  convert h using 1
  · ext θ'
    simp only [etaPsi]
    rw [hexp]
  · simp only [etaPsi', etaPsiG, etaPsiH]
    rw [hexp2, hgam1]
    ring

/-! ## The `η`-weighted angular integration by parts -/

theorem slice_ibp_eta (g : ℝ → ℝ → ℝ) (hg : Spaces.SmoothNbhd g) {z : ℝ} (hz : 0 < z) :
    ∫ θ in Spaces.Iθ, Spaces.Dth g z θ * g z θ * (Real.sin (2 * θ)) ^ (-Spaces.eta)
      = (Spaces.eta - 1) * ∫ θ in Spaces.Iθ,
          Real.cos (2 * θ) * (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  have hG : MeasureTheory.IntegrableOn (etaPsiG g z) Work.Spaces.Iθ :=
    integrableOn_dth_mul_g_eta g hg hz
  have hH : MeasureTheory.IntegrableOn (etaPsiH g z) Work.Spaces.Iθ :=
    integrableOn_cos_sin_eta_mul_sq g hg hz
  have hcont : ContinuousOn (fun θ => etaPsi g z θ) (Set.Icc 0 (π / 2)) :=
    etaPsi_continuousOn g hg hz
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (π / 2),
      HasDerivAt (fun θ => etaPsi g z θ) (etaPsi' g z x) x :=
    fun x hx => etaPsi_hasDerivAt g hg hz hx
  have hintG : IntervalIntegrable (etaPsiG g z) volume (0 : ℝ) (π / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi).mpr (hG.mono_set Set.Ioc_subset_Icc_self)
  have hintH : IntervalIntegrable (etaPsiH g z) volume (0 : ℝ) (π / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi).mpr (hH.mono_set Set.Ioc_subset_Icc_self)
  have hint : IntervalIntegrable (etaPsi' g z) volume (0 : ℝ) (π / 2) := by
    have h2 : IntervalIntegrable
        (fun x => 2 * etaPsiG g z x - 2 * (Work.Spaces.eta - 1) * etaPsiH g z x)
        volume (0 : ℝ) (π / 2) :=
      (hintG.const_mul 2).sub (hintH.const_mul (2 * (Work.Spaces.eta - 1)))
    show IntervalIntegrable (fun x => etaPsi' g z x) volume (0 : ℝ) (π / 2)
    simpa only [etaPsi'] using h2
  have hFTC : ∫ x in (0 : ℝ)..(π / 2), etaPsi' g z x = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := (0 : ℝ)) (b := π / 2)
      hpi hcont hderiv hint
    simpa [(etaPsi_zero g z).1, (etaPsi_zero g z).2] using h
  have hconv : ∀ f : ℝ → ℝ, ∫ θ in Work.Spaces.Iθ, f θ = ∫ θ in (0 : ℝ)..(π / 2), f θ := by
    intro f
    rw [show Work.Spaces.Iθ = Set.Icc 0 (π / 2) from rfl,
        MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi]
  have hset : ∫ x in Work.Spaces.Iθ, etaPsi' g z x = 0 := by
    rw [hconv]
    exact hFTC
  simp only [etaPsi'] at hset
  rw [MeasureTheory.integral_sub (hG.const_mul 2) (hH.const_mul (2 * (Work.Spaces.eta - 1))),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hset
  have h2 : 2 * (∫ θ in Work.Spaces.Iθ, etaPsiG g z θ)
      = 2 * ((Work.Spaces.eta - 1) * ∫ θ in Work.Spaces.Iθ, etaPsiH g z θ) := by
    linarith
  exact mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num) h2

end Work.Coercivity
