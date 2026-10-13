/-
# The angular integration by parts `∫_θ C0h·∂_θf = -∫_θ C0g·f` in the open-quadrant class

The identity `C₀ f = -∫_z∫_θ C0g(θ) f(z,θ)/(z(1+z))` underlying the `C₀`-coercivity estimate
needs the angular integration by parts

  `∫_{Iθ} C0h(θ) ∂_θ f(z,θ) dθ = -∫_{Iθ} C0g(θ) f(z,θ) dθ      (z > 0)`

where `C0h = 3 K sin(2θ)` (the angular factor of the density of `L₁₂(Transport f)`) and
`C0g = C0h'`.  The boundary terms `C0h·f` at `θ = 0, π/2` vanish because `C0h` does there.

For the *open-quadrant* class `SmoothOpen` the slice `θ ↦ f z θ` is only known to be
differentiable on the open interval `(0,π/2)`, so the closed-interval IBP
`Work.Coercivity.C0thetaIBP` is not applicable; instead one uses the open-interval FTC together
with the endpoint *limits* of `f`, which are supplied by `BdryTraces` (the slot `a = b = 0`:
`sin(2θ)^{1-γ} f(z,θ)² → 0`).  This is the open-class analogue of
`Work.FTS.CoercivityFix.Coer1T.C0thetaIBP_Q`, whose proof is adapted verbatim.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.CoercivityFix.Coer1T.slotDz_LGammaT
import Submission.Work.FTS.StrongEps.EpsE4Thr.slice_ibp_gen_O

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.OClass.C0EfAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **`f` vanishes at the two angular endpoints**, for every `z > 0`, as a consequence of
`BdryTraces` (the `a + b = 0` slot: `sin(2θ)^{1-γ} f(z,θ)² → 0`).  The open-class analogue of
`Work.FTS.CoercivityFix.Coer1T.tendsto_slice_zero_bdry`, stated at level `0`, which is exactly
the slot supplied by `RegQo α 2 f`. -/
theorem tendsto_slice_zero_bdry_O (α : ℝ) (hα : 0 < α) {f : Fn}
    (hbd : Work.FTS.Nonlin.BdryTraces α 0 f) {s : ℝ} (hs : 0 < s) :
    Filter.Tendsto (fun θ => f s θ) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      Filter.Tendsto (fun θ => f s θ) (𝓝[<] (π / 2)) (𝓝 0) := by
  have hbd' := (hbd 0 0 (le_refl 0)).2 s hs
  have hpi2 : (0 : ℝ) < π / 2 := by positivity
  constructor
  · -- `θ → 0⁺`
    have hsq : Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * f s θ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := hbd'.1
    have hg : Filter.Tendsto (fun θ =>
        Real.sqrt (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * f s θ ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hcomp : Filter.Tendsto (fun θ =>
          Real.sqrt (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * f s θ ^ 2))
          (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
        (Real.continuous_sqrt.tendsto 0).comp hsq
      rw [Real.sqrt_zero] at hcomp
      exact hcomp
    have hle : ∀ᶠ θ in 𝓝[>] (0 : ℝ), |f s θ|
        ≤ Real.sqrt (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * f s θ ^ 2) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hpi2)]
        with θ hθ hθ2
      have hθ' : (0 : ℝ) < θ := hθ
      have hθ2' : θ < π / 2 := hθ2
      have hsin0 : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hgam : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; positivity
      have h1 : (1 : ℝ) ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hsin0 hsin1
          (show (1 : ℝ) - Work.Spaces.gam α ≤ (0 : ℝ) by
            rw [Work.Spaces.gam]; linarith)
        rw [Real.rpow_zero] at h
        exact h
      rw [Real.le_sqrt (abs_nonneg _) (by positivity)]
      rw [sq_abs]
      nlinarith [sq_nonneg (f s θ)]
    have hzero : Filter.Tendsto (fun θ => |f s θ|) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      squeeze_zero' (Filter.Eventually.of_forall (fun θ => abs_nonneg _)) hle hg
    exact (tendsto_zero_iff_abs_tendsto_zero (fun θ => f s θ)).mpr hzero
  · -- `θ → (π/2)⁻`
    have hsq : Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * f s θ ^ 2) (𝓝[<] (π / 2)) (𝓝 0) := hbd'.2
    have hg : Filter.Tendsto (fun θ =>
        Real.sqrt (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * f s θ ^ 2))
        (𝓝[<] (π / 2)) (𝓝 0) := by
      have hcomp : Filter.Tendsto (fun θ =>
          Real.sqrt (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * f s θ ^ 2))
          (𝓝[<] (π / 2)) (𝓝 (Real.sqrt 0)) :=
        (Real.continuous_sqrt.tendsto 0).comp hsq
      rw [Real.sqrt_zero] at hcomp
      exact hcomp
    have hle : ∀ᶠ θ in 𝓝[<] (π / 2), |f s θ|
        ≤ Real.sqrt (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * f s θ ^ 2) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hpi2)]
        with θ hθ2 hθ
      have hθ' : (0 : ℝ) < θ := hθ
      have hθ2' : θ < π / 2 := hθ2
      have hsin0 : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hgam : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; positivity
      have h1 : (1 : ℝ) ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hsin0 hsin1
          (show (1 : ℝ) - Work.Spaces.gam α ≤ (0 : ℝ) by
            rw [Work.Spaces.gam]; linarith)
        rw [Real.rpow_zero] at h
        exact h
      rw [Real.le_sqrt (abs_nonneg _) (by positivity)]
      rw [sq_abs]
      nlinarith [sq_nonneg (f s θ)]
    have hzero : Filter.Tendsto (fun θ => |f s θ|) (𝓝[<] (π / 2)) (𝓝 0) :=
      squeeze_zero' (Filter.Eventually.of_forall (fun θ => abs_nonneg _)) hle hg
    exact (tendsto_zero_iff_abs_tendsto_zero (fun θ => f s θ)).mpr hzero

/-- **The angular integration by parts in the open-quadrant class**:
`∫_{Iθ} C0h(θ) ∂_θ f(z,θ) dθ = -∫_{Iθ} C0g(θ) f(z,θ) dθ` for `z > 0`, where `C0h = 3K sin(2θ)`
is the angular factor of the density of `L₁₂(Transport f)` and `C0g = C0h'`.  The boundary
terms `C0h(0) = C0h(π/2) = 0` vanish, and the two endpoint limits of `C0h·f` are `0` by
`BdryTraces`.  This is `Work.FTS.CoercivityFix.Coer1T.C0thetaIBP_Q` with `SmoothOpen` in place
of `SmoothQuad` (the proof uses only *interior* differentiability of the slice plus the
endpoint limits). -/
theorem C0thetaIBP_O (α : ℝ) (hα : 0 < α) {f : Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hbd : Work.FTS.Nonlin.BdryTraces α 0 f) {s : ℝ} (hs : 0 < s)
    (hfI : MeasureTheory.IntegrableOn (fun θ => f s θ) Work.Spaces.Iθ)
    (hDI : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.Dth f s θ) Work.Spaces.Iθ) :
    ∫ θ in Work.Spaces.Iθ, Work.Coercivity.C0h θ * Work.Spaces.pth f s θ
      = -∫ θ in Work.Spaces.Iθ, Work.Coercivity.C0g θ * f s θ := by
  have hpi2 : (0 : ℝ) ≤ π / 2 := by positivity
  have hpi2pos : (0 : ℝ) < π / 2 := by positivity
  -- the endpoint limits of `f`
  obtain ⟨hf0, hf2⟩ := tendsto_slice_zero_bdry_O α hα hbd hs
  -- the primitive and its derivative on the open interval
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      HasDerivAt (fun θ' => Work.Coercivity.C0h θ' * f s θ')
        (Work.Coercivity.C0g θ * f s θ
          + Work.Coercivity.C0h θ * Work.Spaces.pth f s θ) θ := by
    intro θ hθ
    have h1 : HasDerivAt (fun θ' => f s θ') (Work.Spaces.pth f s θ) θ :=
      (differentiableAt_slice_theta_O hso hs hθ).hasDerivAt
    exact (Work.Coercivity.C0h_hasDerivAt θ).mul h1
  -- integrability of the two summands of the derivative
  have hC0h_cont : Continuous Work.Coercivity.C0h := by
    unfold Work.Coercivity.C0h Work.Spaces.K
    fun_prop
  have hC0g_cont : Continuous Work.Coercivity.C0g := by
    unfold Work.Coercivity.C0g
    fun_prop
  have hK_cont : Continuous (fun θ : ℝ => 3 * Work.Spaces.K θ) := by
    unfold Work.Spaces.K
    fun_prop
  have hI1 : MeasureTheory.IntegrableOn (fun θ => Work.Coercivity.C0g θ * f s θ)
      Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.continuousOn_mul hC0g_cont.continuousOn hfI isCompact_Icc
  have hI2 : MeasureTheory.IntegrableOn (fun θ => Work.Coercivity.C0h θ * Work.Spaces.pth f s θ)
      Work.Spaces.Iθ := by
    refine (MeasureTheory.IntegrableOn.continuousOn_mul hK_cont.continuousOn hDI
      isCompact_Icc).congr_fun ?_ measurableSet_Icc
    intro θ _
    simp only [Work.Coercivity.C0h, Work.Spaces.Dth, Work.Spaces.K]
    ring
  have hderiv_int : IntervalIntegrable (fun θ => Work.Coercivity.C0g θ * f s θ
      + Work.Coercivity.C0h θ * Work.Spaces.pth f s θ) MeasureTheory.volume 0 (π / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi2).mpr
      ((hI1.mono_set Set.Ioc_subset_Icc_self).add (hI2.mono_set Set.Ioc_subset_Icc_self))
  -- the limits of the primitive
  have hlim0 : Filter.Tendsto (fun θ => Work.Coercivity.C0h θ * f s θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Filter.Tendsto Work.Coercivity.C0h (𝓝[>] (0 : ℝ)) (𝓝 (Work.Coercivity.C0h 0)) :=
      hC0h_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    rw [Work.Coercivity.C0h_zero.1] at h1
    simpa using h1.mul hf0
  have hlim2 : Filter.Tendsto (fun θ => Work.Coercivity.C0h θ * f s θ) (𝓝[<] (π / 2)) (𝓝 0) := by
    have h1 : Filter.Tendsto Work.Coercivity.C0h (𝓝[<] (π / 2))
        (𝓝 (Work.Coercivity.C0h (π / 2))) :=
      hC0h_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    rw [Work.Coercivity.C0h_zero.2] at h1
    simpa using h1.mul hf2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := 0) (b := π / 2)
    hpi2pos hderiv hderiv_int hlim0 hlim2
  -- split and convert to set integrals over `Iθ`
  have hsplit : (∫ y in (0 : ℝ)..(π / 2), (Work.Coercivity.C0g y * f s y
        + Work.Coercivity.C0h y * Work.Spaces.pth f s y))
      = (∫ y in (0 : ℝ)..(π / 2), Work.Coercivity.C0g y * f s y)
        + (∫ y in (0 : ℝ)..(π / 2), Work.Coercivity.C0h y * Work.Spaces.pth f s y) :=
    intervalIntegral.integral_add
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpi2).mpr
        (hI1.mono_set Set.Ioc_subset_Icc_self))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpi2).mpr
        (hI2.mono_set Set.Ioc_subset_Icc_self))
  have hzero : (∫ y in (0 : ℝ)..(π / 2), Work.Coercivity.C0g y * f s y)
      + (∫ y in (0 : ℝ)..(π / 2), Work.Coercivity.C0h y * Work.Spaces.pth f s y) = 0 := by
    rw [← hsplit]
    simpa using hFTC
  have hg_eq : (∫ y in Work.Spaces.Iθ, Work.Coercivity.C0g y * f s y)
      = ∫ y in (0 : ℝ)..(π / 2), Work.Coercivity.C0g y * f s y := by
    rw [Work.Spaces.Iθ]
    exact ((intervalIntegral.integral_of_le hpi2).trans
      (MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume)))).symm
  have hh_eq : (∫ y in Work.Spaces.Iθ, Work.Coercivity.C0h y * Work.Spaces.pth f s y)
      = ∫ y in (0 : ℝ)..(π / 2), Work.Coercivity.C0h y * Work.Spaces.pth f s y := by
    rw [Work.Spaces.Iθ]
    exact ((intervalIntegral.integral_of_le hpi2).trans
      (MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume)))).symm
  rw [hg_eq, hh_eq]
  linarith [hzero]

end Work.FTS.StrongEps.EpsE4Thr.OClass.C0EfAux
