/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weighted `L²`-bound for the angular moment `Qang g i`

The angular moment `Qang g i z = ∫_θ Ktheta θ · D_z^i g (z,θ) dθ` of `ℋ⁴`-data satisfies

  `∫_z (Qang g i z)² w(z)² dz ≤ (∫_θ Ktheta θ²) · |g|²_{ℋ⁴}`   for `i ≤ 4`,

and the integrand is honestly integrable on `Iz = [0,∞)`.

This is the estimate behind the field `N4Norm.fkH` (row 20 of the §8 table, the radial
angular moment `FK g = Qang g 0`): the constant is *lossless* in `α` — it is exactly the
Cauchy–Schwarz constant in `θ`, with the second factor absorbed by a single pure `D_z`-slot
of the `ℋ⁴`-integrand.

Route.

* For `z > 0`, Cauchy–Schwarz in `θ` (`Work.FTS.H2.Qang_sq_leQ`) gives
  `(Qang g i z)² ≤ (∫_θ Ktheta²) · (∫_θ (D_z^i g)²)`.
* On the open angular interval the pure `D_z`-slot of the `ℋ⁴`-integrand dominates the
  weighted square of the iterate, `(D_z^i g z θ)² w(z)² ≤ HkIntegrand α 4 g z θ`
  (`Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq`, whose proof uses `w ≥ 1` and
  `sin(2θ)^{-η} ≥ 1`); the two angular endpoints are null, so this holds a.e. in `θ` on
  `Iθ` and integrating gives `(∫_θ (D_z^i g)²) · w² ≤ ∫_θ HkIntegrand α 4 g z θ`.
* Both steps are pointwise for `z > 0`; the remaining `z = 0` is null in `Iz`.  The
  domination of the left-hand side by `(∫_θ Ktheta²) · ∫_θ HkIntegrand α 4 g z θ` then
  gives the integrability (the right-hand side is integrable by `HkMem`) and the integral
  inequality, `HkSq α 4 g` being the `z`-integral of `∫_θ HkIntegrand α 4 g z θ`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.Nonlinear.Interface
import Submission.Work.FTS.H2.Qang_sq_leQ
import Submission.Work.FTS.H2.QangAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.N4Fields

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The `z = 0`-slice of `Iz = [0,∞)` is null, so every almost-everywhere statement on
`Iz` may be proved on the open half-line. -/
private theorem Iz_ae_eq_Ioi : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
  (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm

/-- The two angular endpoints of `Iθ = [0,π/2]` are null. -/
private theorem Iθ_ae_eq_Ioo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm

/-- **The pure `D_z`-slot domination with the full weight.**  For `z > 0` and
`0 < θ < π/2`, the square of the weighted iterate is dominated by the `ℋ⁴`-integrand:

  `(D_z^i g z θ)² w(z)² ≤ HkIntegrand α 4 g z θ`   (`i ≤ 4`).

This is `Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq` (which gives
`(D_z^i g)² ≤ HkIntegrand/w²`) multiplied by `w² > 0`. -/
private theorem DzIter_sq_w_sq_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) {i : ℕ} (hi : i ≤ 4)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have h1 := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α 4 g i hi hz hθ
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (Work.Spaces.w z))
  rwa [div_mul_cancel₀ _
    (pow_ne_zero 2 (ne_of_gt (Work.FTS.H2.w_pos hz)))] at h2

/-- The radial weight `w` squared is continuous on `(0,∞)`. -/
private theorem continuousOn_w_sq :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => (((1 + z) ^ 2 / z ^ 2) ^ 2) := by
    funext z; rw [Work.Spaces.w]
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2

theorem Qang_sq_w_sq_integral {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    {i : ℕ} (hi : i ≤ 4) :
    MeasureTheory.IntegrableOn (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 4 g := by
  -- the pointwise (in `z > 0`) bound
  have hpt : ∀ z : ℝ, 0 < z →
      (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
    intro z hz
    -- Cauchy–Schwarz in `θ`
    have hCS := Work.FTS.H2.Qang_sq_leQ α g hsm hmem i hi hz
    -- the `θ`-slice domination, with the weight `w z` on the left
    have hslice : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
          * (Work.Spaces.w z) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
      have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
        rw [MeasureTheory.Measure.restrict_congr_set Iθ_ae_eq_Ioo]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => DzIter_sq_w_sq_le_HkIntegrand α g hi hz hθ)
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (hmem.1 z (le_of_lt hz)) hae
      simpa only [MeasureTheory.integral_mul_const] using hmono
    calc (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2))
            * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hCS (sq_nonneg _)
      _ = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
                * (Work.Spaces.w z) ^ 2) := by ring
      _ ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) :=
          mul_le_mul_of_nonneg_left hslice
            (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
  -- the bound holds almost everywhere on `Iz`
  have hle : (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)) := by
    rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hpt
  -- a.e. strong measurability of the left-hand side
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hQ : AEStronglyMeasurable (fun z => Work.Elliptic.Qang g i z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have h := (Work.Spaces.aesm_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter i g p.1 p.2)
        (Work.FTS.H2.continuousOn_Ktheta_DzIter hsm i)).integral_prod_right'
      simpa only [Work.Elliptic.Qang] using h
    have hw : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi]
      exact continuousOn_w_sq.aestronglyMeasurable measurableSet_Ioi
    exact (hQ.pow 2).mul hw
  -- the dominating function is integrable
  have hdom : MeasureTheory.Integrable
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hmem.2.const_mul _
  refine ⟨?_, ?_⟩
  · refine MeasureTheory.Integrable.mono' hdom haesm ?_
    filter_upwards [hle] with z hz
    rwa [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  · have hmono := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      hdom hle
    rw [MeasureTheory.integral_const_mul] at hmono
    exact hmono.trans (le_of_eq rfl)

end Work.FTS.Nonlinear.N4Fields
