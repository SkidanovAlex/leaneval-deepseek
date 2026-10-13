import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.ang_integrals

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.P9

set_option autoImplicit false

/-! ## Vocabulary for the constrained slice Poincaré inequality (`slicePoincare9_fts`)

The target is: for `f : ℝ → ℝ` of class `C²` on `[0,π/2]` with `f 0 = f (π/2) = 0` and
`∫_{Iθ} f θ · sinθcos²θ dθ = 0`, one has `9 ∫_{Iθ} f² ≤ ∫_{Iθ} (f')²`.

The route is the projection of `f` on the kernel direction `s2 θ = sin 2θ` of `-∂_θθ`:
`coeffA f = (4/π) ∫_{Iθ} f · s2` is the first sine coefficient (so that
`∫_{Iθ} f · s2 = (π/4) coeffA f`), and `residG f = f - coeffA f · s2` is the residual, which is
orthogonal to `s2`.  The constraint `∫_{Iθ} f · sinθcos²θ = 0` then bounds the coefficient by the
residual, and the gap-Wirtinger inequality `16 ∫ g² ≤ ∫ (g')²` on the orthogonal complement
closes.

Two technical points are solved once and for all here.

* The global `deriv F` of a function that is only `C²` *on the closed interval* is not
  continuous on `[0,π/2]` (its values at `0` and `π/2` depend on the values of `f` outside the
  interval), so `∫_{Iθ} (deriv F)²` is not obviously honest and the product rule for `deriv` is
  not available at the endpoints.  We therefore work with `w F = derivWithin F [0,π/2]`, which
  *is* continuous on the compact `[0,π/2]` as soon as `F` is `C²` there, and which agrees with
  `deriv F` almost everywhere on `Iθ` (`w_ae_eq_deriv` — true for every `F`).
* The elementary angular integrals (`∫ s2² = π/4`, `∫ sin²θcos⁴θ = π/32`,
  `∫ sinθcos²θ · s2 = 4/15`, `∫ (deriv s2)² = π`) are extracted from
  `Work.FTS.EllipticEst.ang_integrals`. -/

/-- `sin 2θ`, the first Dirichlet mode on `[0,π/2]` and the kernel direction of the `α = 0`
angular operator `L₀ = -∂_θθ + ∂_θ(tan θ ·) - 6` on `[0,π/2]`. -/
def s2 (θ : ℝ) : ℝ := Real.sin (2 * θ)

/-- The derivative of `F` *within* the closed interval `[0,π/2]`. -/
def w (F : ℝ → ℝ) : ℝ → ℝ := derivWithin F (Set.Icc 0 (π / 2))

/-- The first sine coefficient of `f`, `coeffA f = (4/π) ∫_{Iθ} f θ sin 2θ dθ`, normalised so
that `∫_{Iθ} f · sin2θ = (π/4) · coeffA f`. -/
def coeffA (f : ℝ → ℝ) : ℝ := (4 / π) * ∫ θ in Work.Spaces.Iθ, f θ * s2 θ

/-- The residual `residG f = f - coeffA f · sin 2θ`, orthogonal to `sin 2θ` in `L²(Iθ)`. -/
def residG (f : ℝ → ℝ) : ℝ → ℝ := fun θ => f θ - coeffA f * s2 θ

/-! ## Elementary facts about integrals over `Iθ` -/

/-- `∫_{Iθ}` is the interval integral over `0..π/2`. -/
theorem Iθ_eq_interval (G : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, G θ) = ∫ θ in (0 : ℝ)..(π / 2), G θ := by
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2)]

/-- `volume.real Iθ = π/2`. -/
theorem real_volume_Iθ : (volume.real Work.Spaces.Iθ) = π / 2 := by
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl, MeasureTheory.Measure.real,
    Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]

/-- The interval `(0,π/2)` and `Iθ` carry the same restricted measure. -/
theorem restrict_Ioo_eq_restrict_Iθ :
    volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Work.Spaces.Iθ :=
  Measure.restrict_congr_set (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)

/-- Rewriting an integral over `Iθ` under a pointwise equality. -/
theorem setIntegral_Iθ_congr {f g : ℝ → ℝ} (h : ∀ θ ∈ Work.Spaces.Iθ, f θ = g θ) :
    (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in Work.Spaces.Iθ, g θ :=
  setIntegral_congr_fun measurableSet_Icc h

/-- A function continuous on the compact `Iθ` is integrable there. -/
theorem integrableOn_Iθ_of_continuousOn {g : ℝ → ℝ} (hg : ContinuousOn g Work.Spaces.Iθ) :
    IntegrableOn g Work.Spaces.Iθ :=
  hg.integrableOn_compact isCompact_Icc

/-- A globally continuous function is integrable on `Iθ`. -/
theorem integrableOn_Iθ_of_continuous {g : ℝ → ℝ} (hg : Continuous g) :
    IntegrableOn g Work.Spaces.Iθ :=
  integrableOn_Iθ_of_continuousOn hg.continuousOn

/-! ## Continuity and differentiability of the elementary functions -/

theorem continuous_s2 : Continuous s2 := by unfold s2; fun_prop

theorem differentiableAt_s2 (θ : ℝ) : DifferentiableAt ℝ s2 θ := by unfold s2; fun_prop

theorem contDiff_s2 : ContDiff ℝ 2 s2 := by unfold s2; fun_prop

theorem continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2; fun_prop

theorem abs_sinCos2_le_one (θ : ℝ) : |Work.Elliptic.sinCos2 θ| ≤ 1 := by
  have h2 : (Real.cos θ) ^ 2 ≤ 1 := by
    nlinarith [Real.abs_cos_le_one θ, abs_nonneg (Real.cos θ), sq_abs (Real.cos θ)]
  have h1 : |Real.sin θ * Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (Real.cos θ))]
    nlinarith [Real.abs_sin_le_one θ, abs_nonneg (Real.sin θ)]
  simpa [Work.Elliptic.sinCos2] using h1

/-! ## The elementary angular integrals -/

/-- `∫_{Iθ} sin²2θ = π/4`. -/
theorem integral_s2_sq : (∫ θ in Work.Spaces.Iθ, (s2 θ) ^ 2) = π / 4 := by
  simpa [s2] using Work.FTS.EllipticEst.ang_integrals.1

/-- `∫_{Iθ} sin²θcos⁴θ = π/32`. -/
theorem integral_sinCos2_sq :
    (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.sinCos2 θ) ^ 2) = π / 32 :=
  Work.FTS.EllipticEst.ang_integrals.2.1

/-- `∫_{Iθ} sinθcos²θ · sin2θ = 4/15`. -/
theorem integral_sinCos2_mul_s2 :
    (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * s2 θ) = 4 / 15 := by
  simpa [s2] using Work.FTS.EllipticEst.ang_integrals.2.2.1

/-- `deriv (sin 2θ) = 2 cos 2θ`. -/
theorem deriv_s2 : deriv s2 = fun θ : ℝ => 2 * Real.cos (2 * θ) := by
  funext θ
  have h1 : HasDerivAt (fun θ : ℝ => (2 : ℝ) * θ) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  rw [show s2 = fun θ : ℝ => Real.sin (2 * θ) from rfl, h2.deriv]
  ring

/-- `∫_{Iθ} (deriv sin2θ)² = ∫_{Iθ} 4cos²2θ = π`. -/
theorem integral_deriv_s2_sq : (∫ θ in Work.Spaces.Iθ, (deriv s2 θ) ^ 2) = π := by
  have hpt : ∀ θ : ℝ, (deriv s2 θ) ^ 2 = 4 - 4 * (s2 θ) ^ 2 := by
    intro θ
    rw [funext_iff.mp deriv_s2 θ]
    simp only [s2]
    nlinarith [Real.sin_sq_add_cos_sq (2 * θ)]
  have hsplit : (∫ θ in Work.Spaces.Iθ, ((4 : ℝ) - 4 * (s2 θ) ^ 2))
      = (∫ θ in Work.Spaces.Iθ, (4 : ℝ)) - ∫ θ in Work.Spaces.Iθ, 4 * (s2 θ) ^ 2 :=
    MeasureTheory.integral_sub (f := fun _ : ℝ => (4 : ℝ))
      (g := fun θ : ℝ => 4 * (s2 θ) ^ 2)
      (integrableOn_Iθ_of_continuous continuous_const)
      (integrableOn_Iθ_of_continuous (continuous_const.mul (continuous_s2.pow 2)))
  calc (∫ θ in Work.Spaces.Iθ, (deriv s2 θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, ((4 : ℝ) - 4 * (s2 θ) ^ 2) :=
        setIntegral_Iθ_congr (fun θ _ => hpt θ)
    _ = (∫ θ in Work.Spaces.Iθ, (4 : ℝ)) - ∫ θ in Work.Spaces.Iθ, 4 * (s2 θ) ^ 2 := hsplit
    _ = 4 * (π / 2) - 4 * (π / 4) := by
        rw [MeasureTheory.setIntegral_const, real_volume_Iθ,
          MeasureTheory.integral_const_mul, integral_s2_sq]
        simp only [smul_eq_mul]
        ring
    _ = π := by ring

/-! ## The derivative `w` within the closed interval -/

/-- For every `F`, the derivative within `[0,π/2]` agrees with the global derivative almost
everywhere on `Iθ` (they can differ only at the two endpoints). -/
theorem w_ae_eq_deriv (F : ℝ → ℝ) :
    w F =ᵐ[volume.restrict Work.Spaces.Iθ] deriv F := by
  rw [← restrict_Ioo_eq_restrict_Iθ]
  refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  exact derivWithin_of_mem_nhds
    (Icc_mem_nhds (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))

/-- `w F` is continuous on `[0,π/2]` when `F` is `C²` there. -/
theorem continuousOn_w {F : ℝ → ℝ} (hF : ContDiffOn ℝ 2 F (Set.Icc 0 (π / 2))) :
    ContinuousOn (w F) (Set.Icc 0 (π / 2)) :=
  hF.continuousOn_derivWithin (uniqueDiffOn_Icc (by positivity)) (by norm_num)

theorem integrableOn_w_sq {F : ℝ → ℝ} (hF : ContDiffOn ℝ 2 F (Set.Icc 0 (π / 2))) :
    IntegrableOn (fun θ : ℝ => (w F θ) ^ 2) Work.Spaces.Iθ :=
  integrableOn_Iθ_of_continuousOn ((continuousOn_w hF).pow 2)

theorem integrableOn_w_mul {F G : ℝ → ℝ} (hF : ContDiffOn ℝ 2 F (Set.Icc 0 (π / 2)))
    (hG : ContDiffOn ℝ 2 G (Set.Icc 0 (π / 2))) :
    IntegrableOn (fun θ : ℝ => w F θ * w G θ) Work.Spaces.Iθ :=
  integrableOn_Iθ_of_continuousOn ((continuousOn_w hF).mul (continuousOn_w hG))

/-- `∫ (w F)² = ∫ (deriv F)²`: the two integrands agree a.e. on `Iθ`. -/
theorem integral_w_sq_eq_integral_deriv_sq (F : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, (w F θ) ^ 2) = ∫ θ in Work.Spaces.Iθ, (deriv F θ) ^ 2 := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [w_ae_eq_deriv F] with θ hθ
  rw [hθ]

/-- `∫ (w F · w G) = ∫ (deriv F · deriv G)`: the two integrands agree a.e. on `Iθ`. -/
theorem integral_w_mul_eq (F G : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, w F θ * w G θ)
      = ∫ θ in Work.Spaces.Iθ, deriv F θ * deriv G θ := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [w_ae_eq_deriv F, w_ae_eq_deriv G] with θ h1 h2
  rw [h1, h2]

/-- The derivative within `[0,π/2]` of `F - c · sin 2θ`. -/
theorem w_sub_const_mul {F : ℝ → ℝ} (hF : ContDiffOn ℝ 2 F (Set.Icc 0 (π / 2))) (c : ℝ) :
    ∀ θ ∈ Set.Icc 0 (π / 2),
      w (fun θ' : ℝ => F θ' - c * s2 θ') θ = w F θ - c * w s2 θ := by
  intro θ hθ
  have hdF : DifferentiableWithinAt ℝ F (Set.Icc 0 (π / 2)) θ :=
    (hF.differentiableOn (by norm_num)) θ hθ
  have hds2 : DifferentiableWithinAt ℝ s2 (Set.Icc 0 (π / 2)) θ :=
    (differentiableAt_s2 θ).differentiableWithinAt
  have hdG : DifferentiableWithinAt ℝ (fun θ' : ℝ => c * s2 θ') (Set.Icc 0 (π / 2)) θ :=
    hds2.const_mul c
  have hfun : (fun θ' : ℝ => F θ' - c * s2 θ') = F - (fun θ' : ℝ => c * s2 θ') := by
    funext θ'; simp
  simp only [w, hfun]
  rw [derivWithin_sub hdF hdG, derivWithin_const_mul c hds2]

end Work.FTS.EllipticEst.P9
