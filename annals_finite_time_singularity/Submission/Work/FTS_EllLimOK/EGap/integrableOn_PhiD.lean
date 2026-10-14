import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.Cyl.fderiv_rho_theta_eZ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The axial derivative of `x ↦ F(ρ(x), θ(x))`: the `e₃` direction

For a two-variable function `F` and a point `x` off the symmetry axis (`0 < radial x`),

`fderiv ℝ (fun y ↦ F (rho y) (theta y)) x eZ
   = sin θ · ∂_ρ F(ρ,θ) + (cos θ / ρ) · ∂_θ F(ρ,θ)`,

with `(ρ, θ) = (rho x, theta x)`.  Geometrically: along the vertical line `x + t e₃` the point
`(rho, theta)` moves as `(ρ(x₃), θ(x₃))` with `∂_{x₃}ρ = x₃/ρ = sin θ` and
`∂_{x₃}θ = radial/ρ² = cos θ/ρ`, and `e₃` is the coordinate direction `∂_{x₃}`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix
open Work.Cyl

namespace Work.Cyl

/-! ## The dictionary between `(rho, theta)` on `ℝ³` and `(rhoP, thetaP)` on the half plane

`rho y = rhoP (radial y) (axial y)` and `theta y = thetaP (radial y) (axial y)`, so on the
vertical line through `x` we have `rho (x + t e₃) = rhoP (radial x) (axial x + t)` and likewise
for `theta`. -/

private lemma rho_eq_rhoP (y : R3) : rho y = rhoP (radial y) (axial y) := by
  rw [rho, rhoP, radial_sq]

private lemma theta_eq_thetaP (y : R3) : theta y = thetaP (radial y) (axial y) := rfl

/-! ## The axial chain rule along a vertical line in the `(r, x₃)` half plane -/

private lemma deriv_rhoP_thetaP_shift (F : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
    (hF : DiffAt2 F (rhoP r z) (thetaP r z)) :
    deriv (fun t : ℝ => F (rhoP r (z + t)) (thetaP r (z + t))) 0 =
      Real.sin (thetaP r z) * pdR F (rhoP r z) (thetaP r z)
        + Real.cos (thetaP r z) / rhoP r z * pdZ F (rhoP r z) (thetaP r z) := by
  rw [deriv_comp_const_add (fun u : ℝ => F (rhoP r u) (thetaP r u)) z 0, add_zero]
  rw [show deriv (fun u : ℝ => F (rhoP r u) (thetaP r u)) z
      = pdZ (fun r' z' => F (rhoP r' z') (thetaP r' z')) r z from rfl]
  exact pdZ_comp_polar_rho F r z hr hF

theorem fderiv_rho_theta_eZ (F : ℝ → ℝ → ℝ) (x : Work.Cyl.R3)
    (hF : Work.Cyl.DiffAt2 F (Work.Cyl.rho x) (Work.Cyl.theta x)) (hr : 0 < Work.Cyl.radial x) :
    fderiv ℝ (fun y : Work.Cyl.R3 => F (Work.Cyl.rho y) (Work.Cyl.theta y)) x Work.Cyl.eZ =
      Real.sin (Work.Cyl.theta x) * Work.Cyl.pdR F (Work.Cyl.rho x) (Work.Cyl.theta x)
        + Real.cos (Work.Cyl.theta x) / Work.Cyl.rho x *
          Work.Cyl.pdZ F (Work.Cyl.rho x) (Work.Cyl.theta x) := by
  have hrho : rho x = rhoP (radial x) (axial x) := rho_eq_rhoP x
  have htheta : theta x = thetaP (radial x) (axial x) := theta_eq_thetaP x
  have hF' : DiffAt2 F (rhoP (radial x) (axial x)) (thetaP (radial x) (axial x)) := by
    rw [← hrho, ← htheta]; exact hF
  rw [fderiv_apply_eq_deriv_line _ _ _ (differentiableAt_rho_theta_comp F x hF hr)]
  have hfun : (fun t : ℝ => F (rho (x + t • eZ)) (theta (x + t • eZ))) =
      fun t : ℝ =>
        F (rhoP (radial x) (axial x + t)) (thetaP (radial x) (axial x + t)) := by
    funext t
    rw [rho_eq_rhoP (x + t • eZ), theta_eq_thetaP (x + t • eZ), radial_add_smul_eZ,
      axial_add_smul_eZ]
  rw [hfun, deriv_rhoP_thetaP_shift F (radial x) (axial x) hr hF']
  rw [← hrho, ← htheta]

end Work.Cyl
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LevelOneAsm.eigE_span_orthogonal_eq_bot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.LevelOneAsm

local notation "Iθ" => Work.Spaces.Iθ



end Work.FTS.EllipticEst.LevelOneAsm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.zHardyDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## The auxiliary functions -/

/-- The function `a(z) = (z-3)/(2(1+z))` of the completion of squares. -/
def zA (z : ℝ) : ℝ := (z - 3) / (2 * (1 + z))

/-- The derivative of the radial weight `w(z) = (1+z)²/z²`. -/
def zDw (z : ℝ) : ℝ := 2 * (1 + z) / z ^ 2 - 2 * (1 + z) ^ 2 / z ^ 3

/-- The derivative of `zA`. -/
def zDA (z : ℝ) : ℝ := 2 / (1 + z) ^ 2



/-! ## The derivatives of `zA` and of the weight `w` -/

theorem hasDerivAt_zA {z : ℝ} (hz : 0 < z) : HasDerivAt zA (zDA z) z := by
  have hid : HasDerivAt (fun y : ℝ => y) (1 : ℝ) z := hasDerivAt_id z
  have hnum : HasDerivAt (fun y : ℝ => y - 3) 1 z := hid.sub_const 3
  have hden : HasDerivAt (fun y : ℝ => 2 * (1 + y)) 2 z := by
    have h := (hid.const_add (1 : ℝ)).const_mul (2 : ℝ)
    exact h.congr_deriv (by ring)
  have h := hnum.div hden (by positivity)
  change HasDerivAt (fun y : ℝ => (y - 3) / (2 * (1 + y))) (zDA z) z
  refine h.congr_deriv ?_
  rw [zDA]
  have h2 : (1 : ℝ) + z ≠ 0 := by linarith
  field_simp
  try ring

theorem hasDerivAt_w {z : ℝ} (hz : 0 < z) : HasDerivAt Work.Spaces.w (zDw z) z := by
  have hid : HasDerivAt (fun y : ℝ => y) (1 : ℝ) z := hasDerivAt_id z
  have hnum : HasDerivAt (fun y : ℝ => (1 + y) ^ 2) (2 * (1 + z)) z := by
    have h := (hid.const_add (1 : ℝ)).pow 2
    exact h.congr_deriv (by ring)
  have hden : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by
    have h := hid.pow 2
    exact h.congr_deriv (by ring)
  have h := hnum.div hden (by positivity)
  change HasDerivAt (fun y : ℝ => (1 + y) ^ 2 / y ^ 2) (zDw z) z
  refine h.congr_deriv ?_
  rw [zDw]
  have h2 : z ≠ 0 := ne_of_gt hz
  field_simp
  try ring

/-! ## The algebraic identity of the completion of squares -/


/-! ## The pointwise inequality -/



end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.EGap.integrableOn_PhiD =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the angular `L²`-mass of the difference of two profiles

`PhiD Ψ Ψ' z = ∫_θ (Ψ z θ - Ψ' z θ)² dθ` is the angular `L²`-mass of the difference of
two profiles.  Under `HkMem α 0` for both `Ψ` and `Ψ'` (i.e. the single weighted slice
integral `z ↦ ∫_θ g(z,θ)² w(z)² sin(2θ)^{-η}` is integrable in `z` on `[0,∞)`), the
angular mass `PhiD Ψ Ψ'` is integrable on `(0,∞)` and, with the extra radial weight
`z^{-4}` — which is exactly the weight needed to make the weighted elliptic energy finite
near `z = 0` — it is integrable on `(0,1)`:

`Φ(z) ≤ 2 (∫_θ HkIntegrand α 0 Ψ z θ + ∫_θ HkIntegrand α 0 Ψ' z θ)`

for `z > 0`, because the weight `w(z)/sin(2θ)^{η/2}` occurring in the `H⁰`-integrand is
`≥ 1` in the interior of the quadrant, so that

`(Ψ - Ψ')² ≤ 2 (Ψ² + Ψ'²) ≤ 2 (HkIntegrand α 0 Ψ + HkIntegrand α 0 Ψ') / w(z)²`,

and `1/w(z)² = z⁴/(1+z)⁴ ≤ z⁴` (which is `z^{-4} ≤ w(z)²`).  The a.e.-measurability
hypothesis on the uncurried difference is what makes the sliced integral `Φ` measurable.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.EGap

set_option autoImplicit false

/-! ## Elementary estimates -/

/-- For `0 < u ≤ 1` and `W ≠ 0`, the square `a²` is dominated by `(a·(W/u))²/W²`: the
factor `(W/u)²` is at least `W²`. -/
private lemma sq_le_sq_mul_div_sq {a u W : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (hW : W ≠ 0) :
    a ^ 2 ≤ (a * (W / u)) ^ 2 / W ^ 2 := by
  have hkey : (a * (W / u)) ^ 2 / W ^ 2 = a ^ 2 / u ^ 2 := by
    rw [mul_pow, div_pow]; field_simp
  rw [hkey]
  have hu2 : 0 < u ^ 2 := pow_pos hu0 2
  have h1 : (1 : ℝ) ≤ 1 / u ^ 2 := (one_le_div hu2).mpr (by nlinarith)
  calc a ^ 2 = a ^ 2 * 1 := by ring
    _ ≤ a ^ 2 * (1 / u ^ 2) := mul_le_mul_of_nonneg_left h1 (sq_nonneg a)
    _ = a ^ 2 / u ^ 2 := by ring

/-- At level `0` the `H⁰`-integrand collapses to a single square. -/
private lemma HkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand, Work.Spaces.DzIter]

/-- The radial weight is at least `1` on the open half-line: `w(z) = ((1+z)/z)² ≥ 1`. -/
private lemma one_le_w (z : ℝ) (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  have h : Work.Spaces.w z = ((1 + z) / z) ^ 2 := by
    rw [Work.Spaces.w, div_pow]
  rw [h]
  have h1 : 1 ≤ (1 + z) / z := by
    rw [le_div_iff₀ hz]
    linarith
  exact one_le_pow₀ h1

/-- **Pointwise bound in the interior of the quadrant**: the square of the difference of two
profiles is dominated by the sum of their `H⁰`-integrands, divided by `w(z)²`. -/
private lemma diff_sq_le_HkIntegrand {α : ℝ} {Ψ Ψ' : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (Work.FTS_EllLimOK.diff Ψ Ψ' z θ) ^ 2
      ≤ 2 * (Work.Spaces.HkIntegrand α 0 Ψ z θ + Work.Spaces.HkIntegrand α 0 Ψ' z θ)
          / (Work.Spaces.w z) ^ 2 := by
  have hs0 : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hu0 : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hs0 _
  have hu1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs0) hs1 (by norm_num [Work.Spaces.eta])
  have hw1 : 1 ≤ Work.Spaces.w z := one_le_w z hz
  have hw : Work.Spaces.w z ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hw1)
  have hsq := sq_le_sq_mul_div_sq (a := Work.FTS_EllLimOK.diff Ψ Ψ' z θ) hu0 hu1 hw
  have h2 : (Work.FTS_EllLimOK.diff Ψ Ψ' z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = ((Ψ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
          - (Ψ' z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) ^ 2 := by
    rw [Work.FTS_EllLimOK.diff_apply]; ring
  have h3 : ((Ψ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
          - (Ψ' z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) ^ 2
      ≤ 2 * (Ψ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        + 2 * (Ψ' z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    nlinarith [sq_nonneg (Ψ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
        + Ψ' z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]
  have h4 : (2 * (Ψ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        + 2 * (Ψ' z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        / (Work.Spaces.w z) ^ 2
      = 2 * (Work.Spaces.HkIntegrand α 0 Ψ z θ + Work.Spaces.HkIntegrand α 0 Ψ' z θ)
          / (Work.Spaces.w z) ^ 2 := by
    simp only [HkIntegrand_zero_eq]; ring
  calc (Work.FTS_EllLimOK.diff Ψ Ψ' z θ) ^ 2
      ≤ (Work.FTS_EllLimOK.diff Ψ Ψ' z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          / (Work.Spaces.w z) ^ 2 := hsq
    _ = ((Ψ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
          - (Ψ' z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) ^ 2
          / (Work.Spaces.w z) ^ 2 := by rw [h2]
    _ ≤ (2 * (Ψ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        + 2 * (Ψ' z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          / (Work.Spaces.w z) ^ 2 := div_le_div_of_nonneg_right h3 (sq_nonneg _)
    _ = 2 * (Work.Spaces.HkIntegrand α 0 Ψ z θ + Work.Spaces.HkIntegrand α 0 Ψ' z θ)
          / (Work.Spaces.w z) ^ 2 := h4

/-! ## The slicewise bound -/

/-- The angular mass of the difference of two `H⁰`-profiles is dominated by the (weighted)
`H⁰`-slice masses of the two profiles, divided by `w(z)²`. -/
private lemma PhiD_le_div {α : ℝ} {Ψ Ψ' : ℝ → ℝ → ℝ}
    (hHkΨ : Work.Spaces.HkMem α 0 Ψ) (hHkΨ' : Work.Spaces.HkMem α 0 Ψ')
    {z : ℝ} (hz : 0 < z) :
    Work.FTS_EllLimOK.PhiD Ψ Ψ' z
      ≤ 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ' z θ))
          / (Work.Spaces.w z) ^ 2 := by
  have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hz)
  have hslΨ : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 Ψ z θ)
      Work.Spaces.Iθ := hHkΨ.1 z hzIz
  have hslΨ' : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 Ψ' z θ)
      Work.Spaces.Iθ := hHkΨ'.1 z hzIz
  have hdiv : MeasureTheory.IntegrableOn (fun θ => 2 * (Work.Spaces.HkIntegrand α 0 Ψ z θ
      + Work.Spaces.HkIntegrand α 0 Ψ' z θ) / (Work.Spaces.w z) ^ 2) Work.Spaces.Iθ :=
    ((hslΨ.add hslΨ').const_mul 2).div_const _
  -- the pointwise bound holds a.e. on `Iθ`: only the two endpoints are excluded
  have hone : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
    have heq : MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))
        = MeasureTheory.volume.restrict Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]; exact MeasureTheory.restrict_Ioo_eq_restrict_Icc
    rw [← heq]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hθ)
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.FTS_EllLimOK.diff Ψ Ψ' z θ) ^ 2
        ≤ 2 * (Work.Spaces.HkIntegrand α 0 Ψ z θ
            + Work.Spaces.HkIntegrand α 0 Ψ' z θ) / (Work.Spaces.w z) ^ 2 := by
    filter_upwards [hone] with θ hθ
    exact diff_sq_le_HkIntegrand hz hθ.1 hθ.2
  have hmain : Work.FTS_EllLimOK.PhiD Ψ Ψ' z
      ≤ ∫ θ in Work.Spaces.Iθ, 2 * (Work.Spaces.HkIntegrand α 0 Ψ z θ
          + Work.Spaces.HkIntegrand α 0 Ψ' z θ) / (Work.Spaces.w z) ^ 2 :=
    MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) hdiv hae
  have hRHS : ∫ θ in Work.Spaces.Iθ, 2 * (Work.Spaces.HkIntegrand α 0 Ψ z θ
        + Work.Spaces.HkIntegrand α 0 Ψ' z θ) / (Work.Spaces.w z) ^ 2
      = 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ' z θ))
          / (Work.Spaces.w z) ^ 2 := by
    rw [MeasureTheory.integral_div, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add hslΨ hslΨ']
  rw [hRHS] at hmain
  exact hmain

/-- The same bound with the divisor `w(z)² ≥ 1` removed. -/
private lemma PhiD_le {α : ℝ} {Ψ Ψ' : ℝ → ℝ → ℝ}
    (hHkΨ : Work.Spaces.HkMem α 0 Ψ) (hHkΨ' : Work.Spaces.HkMem α 0 Ψ')
    {z : ℝ} (hz : 0 < z) :
    Work.FTS_EllLimOK.PhiD Ψ Ψ' z
      ≤ 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ' z θ)) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hG0 : 0 ≤ 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ)
      + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ' z θ)) := by
    have h1 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ :=
      MeasureTheory.setIntegral_nonneg hIθ (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 Ψ z θ)
    have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ' z θ :=
      MeasureTheory.setIntegral_nonneg hIθ (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 Ψ' z θ)
    linarith
  exact le_trans (PhiD_le_div hHkΨ hHkΨ' hz)
    (div_le_self hG0 (one_le_pow₀ (one_le_w z hz)))

/-! ## The theorem -/

theorem integrableOn_PhiD {α : ℝ} {Ψ Ψ' : ℝ → ℝ → ℝ}
    (hHkΨ : Work.Spaces.HkMem α 0 Ψ) (hHkΨ' : Work.Spaces.HkMem α 0 Ψ')
    (hae : AEMeasurable (Function.uncurry (Work.FTS_EllLimOK.diff Ψ Ψ'))
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    MeasureTheory.IntegrableOn (Work.FTS_EllLimOK.PhiD Ψ Ψ') (Set.Ioi 0) ∧
      MeasureTheory.IntegrableOn (fun z => Work.FTS_EllLimOK.PhiD Ψ Ψ' z * z ^ (-4 : ℝ))
        (Set.Ioo (0 : ℝ) 1) := by
  -- the dominating function: twice the sum of the two `H⁰`-slice masses
  have hGΨ : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ) (Set.Ioi 0) :=
    hHkΨ.2.mono_set (fun z hz => Set.mem_Ici.mpr (le_of_lt hz))
  have hGΨ' : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ' z θ) (Set.Ioi 0) :=
    hHkΨ'.2.mono_set (fun z hz => Set.mem_Ici.mpr (le_of_lt hz))
  have hG : MeasureTheory.IntegrableOn
      (fun z => 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ' z θ))) (Set.Ioi 0) :=
    (hGΨ.add hGΨ').const_mul 2
  -- the angular mass is the sliced integral of an a.e. measurable function
  have hmeas : AEStronglyMeasurable (fun z => Work.FTS_EllLimOK.PhiD Ψ Ψ' z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    have h2 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => (Work.FTS_EllLimOK.diff Ψ Ψ' p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      simpa only [Function.uncurry] using (hae.pow_const 2).aestronglyMeasurable
    simpa only [Work.FTS_EllLimOK.PhiD_apply] using h2.integral_prod_right'
  constructor
  · -- integrability of the angular mass on `(0,∞)`
    refine hG.mono' hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    rw [Real.norm_of_nonneg (Work.FTS_EllLimOK.PhiD_nonneg Ψ Ψ' z)]
    exact PhiD_le hHkΨ hHkΨ' hz
  · -- the weighted integrability on `(0,1)`
    have hzpow_le : ∀ z ∈ Set.Ioo (0 : ℝ) 1, z ^ (-4 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by
      intro z hz
      have hz0 : 0 < z := hz.1
      have hzpow_eq : z ^ (-4 : ℝ) = (z ^ 4)⁻¹ := by
        rw [show (-4 : ℝ) = -(4 : ℝ) by norm_num, Real.rpow_neg (le_of_lt hz0)]
        simp
      have hw2_eq : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 * (z ^ 4)⁻¹ := by
        rw [Work.Spaces.w, div_pow, ← pow_mul, ← pow_mul, div_eq_mul_inv]
      have h1 : (1 : ℝ) ≤ (1 + z) ^ 4 := one_le_pow₀ (by linarith)
      have h2 : 0 < (z ^ 4)⁻¹ := inv_pos.mpr (pow_pos hz0 4)
      rw [hzpow_eq, hw2_eq]
      calc (z ^ 4)⁻¹ = 1 * (z ^ 4)⁻¹ := (one_mul _).symm
        _ ≤ (1 + z) ^ 4 * (z ^ 4)⁻¹ := mul_le_mul_of_nonneg_right h1 (le_of_lt h2)
    have hPhi : AEMeasurable (fun z => Work.FTS_EllLimOK.PhiD Ψ Ψ' z)
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
      have h := (hmeas.restrict : AEStronglyMeasurable
        (fun z => Work.FTS_EllLimOK.PhiD Ψ Ψ' z)
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).restrict (Set.Ioo (0 : ℝ) 1)))
      rw [MeasureTheory.Measure.restrict_restrict measurableSet_Ioo,
        Set.inter_eq_left.mpr Set.Ioo_subset_Ioi_self] at h
      exact h.aemeasurable
    have hpow : AEMeasurable (fun z : ℝ => z ^ (-4 : ℝ))
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
      have hbase : AEMeasurable (fun z : ℝ => (z ^ 4)⁻¹)
          (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
        ((measurable_id.pow_const 4).inv).aemeasurable
      refine hbase.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
      rw [show (-4 : ℝ) = -(4 : ℝ) by norm_num, Real.rpow_neg (le_of_lt hz.1)]
      simp
    have hmeas2 : AEStronglyMeasurable
        (fun z => Work.FTS_EllLimOK.PhiD Ψ Ψ' z * z ^ (-4 : ℝ))
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
      (hPhi.mul hpow).aestronglyMeasurable
    have hG2 : MeasureTheory.IntegrableOn
        (fun z => 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ' z θ)))
        (Set.Ioo (0 : ℝ) 1) :=
      hG.mono_set Set.Ioo_subset_Ioi_self
    refine hG2.mono' hmeas2 ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
    have hz0 : 0 < z := hz.1
    have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
    have hG0 : 0 ≤ 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ' z θ)) := by
      have h1 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ :=
        MeasureTheory.setIntegral_nonneg hIθ (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 Ψ z θ)
      have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ' z θ :=
        MeasureTheory.setIntegral_nonneg hIθ (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 Ψ' z θ)
      linarith
    have hzpow_nonneg : 0 ≤ z ^ (-4 : ℝ) := Real.rpow_nonneg (le_of_lt hz0) _
    have hw2pos : 0 < (Work.Spaces.w z) ^ 2 :=
      pow_pos (lt_of_lt_of_le zero_lt_one (one_le_w z hz0)) 2
    have hratio : z ^ (-4 : ℝ) / (Work.Spaces.w z) ^ 2 ≤ 1 := by
      rw [div_le_iff₀ hw2pos]
      simpa using hzpow_le z hz
    rw [Real.norm_of_nonneg (mul_nonneg (Work.FTS_EllLimOK.PhiD_nonneg Ψ Ψ' z) hzpow_nonneg)]
    calc Work.FTS_EllLimOK.PhiD Ψ Ψ' z * z ^ (-4 : ℝ)
        ≤ (2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ' z θ))
            / (Work.Spaces.w z) ^ 2) * z ^ (-4 : ℝ) :=
          mul_le_mul_of_nonneg_right (PhiD_le_div hHkΨ hHkΨ' hz0) hzpow_nonneg
      _ = 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ' z θ))
            * (z ^ (-4 : ℝ) / (Work.Spaces.w z) ^ 2) := by ring
      _ ≤ 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ' z θ)) * 1 :=
          mul_le_mul_of_nonneg_left hratio hG0
      _ = 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ' z θ)) := by ring

end Work.FTS_EllLimOK.EGap
end
end
