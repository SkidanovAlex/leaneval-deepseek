import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open MeasureTheory Set Filter
open scoped Real Topology

/-! ## Interval integrability of `s^{(5-α)/α}·F_*(g)(s)` for an open-quadrant smooth source

The singular radial piece
`Ḡ(α,g)(z) = -(3/(4α)) z^{-5/α} ∫_0^z s^{(5-α)/α} F_*(g)(s) ds` of §'The singular term' is only
a genuine integral if `s ↦ s^{(5-α)/α}·F_*(g)(s)` is interval integrable on `[0,z]`.  This is
proved here for every `α > 0` and every datum `g` which is `C^∞` on the open quadrant
`(0,∞)×(0,π/2)` (`SmoothOpen`, i.e. no boundary regularity at `θ = 0, π/2` is required) and
lies honestly in the weighted space `ℋ⁴` (`HkMem α 4`).

The mathematics, for `z > 0`:

* **Continuity of the moment.**  `F_*(g) = PsiInt g 0` is continuous on `(0,∞)` by
  `Work.FTS.EllipticEst.PsiInt_continuousOn` (the moment tower plus the Cauchy–Schwarz
  majorant `A_1 ∈ L¹`).  Hence so is `s ↦ s^{(5-α)/α}·F_*(g)(s)` on `(0,∞)`.
* **The `L¹` bound.**  `Work.FTS.EllipticEst.GbarSin.Fstar_div_le_majorant` at `j = 0` gives,
  for `s > 0`,
  `|F_*(g)(s)|/s ≤ ((π/2)·∫_θ HkIntegrand α 4 g s θ + 1)/2`,
  and multiplying by `s > 0` bounds `|F_*(g)(s)|` itself.
* **The radial exponent.**  Multiplying by `s^c`, `c = (5-α)/α`, and using
  `s^c·s = s^{c+1}` together with `c + 1 = 5/α > 0`, we get on `(0,z]`
  `‖s^c·F_*(g)(s)‖ ≤ z^{c+1}·((π/2)·G(s) + 1)/2`, where
  `G(s) = ∫_θ HkIntegrand α 4 g s θ` is integrable on `(0,z]` by `HkMem` (`z ∈ Iz`): the
  majorant is an integrable function of `s` on the *finite* interval `(0,z]`. -/
theorem intervalIntegrable_rpow_Fstar_open (α : ℝ) (hα : 0 < α) (g : ℝ → ℝ → ℝ)
    (hso : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    {z : ℝ} (hz : 0 < z) :
    IntervalIntegrable (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar g s)
      MeasureTheory.volume 0 z := by
  set c : ℝ := (5 - α) / α with hc
  have hcp1 : c + 1 = 5 / α := by
    rw [hc]; field_simp; ring
  have hc1 : 0 < c + 1 := by rw [hcp1]; exact div_pos (by norm_num) hα
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le]
  -- (1) the angular moment is continuous on `(0,∞)`
  have hcont : ContinuousOn (fun s : ℝ => Work.Elliptic.Fstar g s) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.PsiInt_continuousOn α 4 g hso hmem 0 (by norm_num)
  -- (2) a.e. strong measurability of the integrand on `(0,z]`
  have haesm : AEStronglyMeasurable (fun s : ℝ => s ^ c * Work.Elliptic.Fstar g s)
      (volume.restrict (Set.Ioc 0 z)) := by
    have hrpow : ContinuousOn (fun s : ℝ => s ^ c) (Set.Ioi 0) :=
      continuousOn_id.rpow_const (fun s hs => Or.inl (ne_of_gt hs))
    exact ((hrpow.mul hcont).mono (fun s hs => hs.1)).aestronglyMeasurable measurableSet_Ioc
  -- (3) the angular slice `G(s) = ∫_θ HkIntegrand α 4 g s θ` is integrable on `(0,z]`
  have hGint : IntegrableOn
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
      (Set.Ioc 0 z) :=
    hmem.2.mono_set (fun s hs => by rw [Work.Spaces.Iz]; exact le_of_lt hs.1)
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 z) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hdom : Integrable (fun s : ℝ => z ^ (c + 1) *
      (((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) + 1) / 2))
      (volume.restrict (Set.Ioc 0 z)) :=
    ((hGint.const_mul (Real.pi / 2)).add hone).div_const 2 |>.const_mul (z ^ (c + 1))
  -- (4) the pointwise domination
  have hpt : ∀ s ∈ Set.Ioc 0 z, ‖s ^ c * Work.Elliptic.Fstar g s‖
      ≤ z ^ (c + 1) * (((Real.pi / 2)
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) + 1) / 2) := by
    intro s hs
    have hs0 : 0 < s := hs.1
    have hsz : s ≤ z := hs.2
    have hGnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ :=
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g s θ
    have hpiG : 0 ≤ (Real.pi / 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) :=
      mul_nonneg (by positivity) hGnn
    have hX0 : 0 ≤ ((Real.pi / 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) + 1) / 2 := by
      linarith
    -- Cauchy–Schwarz for the angular moment, in `L¹` form
    have hdiv := Work.FTS.EllipticEst.GbarSin.Fstar_div_le_majorant α 4 g hso hmem 0
      (by norm_num) hs0
    have hdiv' : |Work.Elliptic.Fstar g s| / s ≤ ((Real.pi / 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) + 1) / 2 := by
      simpa only [Work.Spaces.DzIter_zero] using hdiv
    have hAbs : |Work.Elliptic.Fstar g s| ≤ s * (((Real.pi / 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) + 1) / 2) := by
      have h := (div_le_iff₀ hs0).mp hdiv'
      simpa only [mul_comm] using h
    have hstep1 : s ^ c * |Work.Elliptic.Fstar g s| ≤ s ^ c * (s * (((Real.pi / 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) + 1) / 2)) :=
      mul_le_mul_of_nonneg_left hAbs (Real.rpow_nonneg hs0.le c)
    have hstep2 : s ^ c * (s * (((Real.pi / 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) + 1) / 2))
        = s ^ (c + 1) * (((Real.pi / 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) + 1) / 2) := by
      have hsc : s ^ (c + 1) = s ^ c * s := by
        rw [Real.rpow_add hs0 c 1, Real.rpow_one]
      rw [hsc, mul_assoc]
    have hstep3 : s ^ (c + 1) * (((Real.pi / 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) + 1) / 2)
        ≤ z ^ (c + 1) * (((Real.pi / 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) + 1) / 2) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hs0.le hsz hc1.le) hX0
    have hnorm : ‖s ^ c * Work.Elliptic.Fstar g s‖
        = s ^ c * |Work.Elliptic.Fstar g s| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le c)]
    rw [hnorm]
    exact le_trans hstep1 (le_trans (le_of_eq hstep2) hstep3)
  exact Integrable.mono' hdom haesm (ae_restrict_of_forall_mem measurableSet_Ioc hpt)

end Work.FTS.ClassC
