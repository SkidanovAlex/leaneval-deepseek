import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Honesty.DiffGreen.cmode_sub
import Submission.Work.FTS.PhiStar.Honesty.DiffGreen.radGreen_sub
import Submission.Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries
import Submission.Work.FTS.PhiStar.Honesty.psiSeries_tendsto_of_HkSq
import Submission.Work.FTS.PhiStar.Honesty.continuousOn_cmode_of_hkMem_one
import Submission.Work.FTS.PhiStar.Honesty.cmode_modeEnergy_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

set_option autoImplicit false

namespace Work.FTS.PhiStar.RouteB

/-! ## Locality and additivity of the mode coefficients

The mode coefficient `cmode m F z` is the `e_m`-coefficient of the slice `F z ·` in the weight
`cos θ dθ`, hence is *linear* in the source (this is `DiffGreen.cmode_sub`), and the radial
Green function `radGreen` only sees its source on the open half-line `(0,∞)` (its two defining
integrals range over `(0,z)` and `(z,∞)`).  Composing the two gives the additivity of `acoeff`. -/

/-- `radGreen` only sees the values of its source on the open half-line `(0,∞)`: for `z > 0`
both integrals range over positive arguments only. -/
private lemma radGreen_congr_Ioi {α : ℝ} (m : ℕ) {f g : ℝ → ℝ}
    (h : ∀ t : ℝ, 0 < t → f t = g t) {z : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.Radial.radGreen α m f z
      = Work.FTS.PhiStar.Radial.radGreen α m g z := by
  have h1 : (∫ t in (0 : ℝ)..z, f t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      = (∫ t in (0 : ℝ)..z, g t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) := by
    rw [intervalIntegral.integral_of_le hz.le, intervalIntegral.integral_of_le hz.le]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t ht => by rw [h t ht.1])
  have h2 : (∫ t in Set.Ioi z, f t * t ^ (-(2 * (m : ℝ) / α) - 1))
      = (∫ t in Set.Ioi z, g t * t ^ (-(2 * (m : ℝ) / α) - 1)) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => by rw [h t (lt_trans hz ht)])
  simp only [Work.FTS.PhiStar.Radial.radGreen, h1, h2]

/-- **The mode-`m` radial coefficient is additive in the source** (at `z > 0`): both the mode
coefficient `cmode m · z` (linearity of the slice integral, `DiffGreen.cmode_sub`) and the
radial Green operator (locality on `z > 0`) are additive, and the `L²`-integrability of the two
sources is exactly what `cmode_sq_integrable` provides. -/
private lemma acoeff_sub {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {X Y : ℝ → ℝ → ℝ} (hX : Work.FTS.EllipticEst.SmoothOpen X)
    (hY : Work.FTS.EllipticEst.SmoothOpen Y)
    (hXm : Work.Spaces.HkMem α 0 X) (hYm : Work.Spaces.HkMem α 0 Y)
    (m : ℕ) {z : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.Series.acoeff α m (fun z θ => X z θ - Y z θ) z
      = Work.FTS.PhiStar.Series.acoeff α m X z
        - Work.FTS.PhiStar.Series.acoeff α m Y z := by
  have hsl := Work.FTS.PhiStar.Honesty.DiffGreen.radGreen_sub (α := α) hα hα4 m
    (Work.EllipticEst.ModalSolution.aesm_cmode hY m)
    (Work.EllipticEst.ModalSolution.aesm_cmode hX m)
    (Work.FTS.PhiStar.Honesty.cmode_sq_integrable hY hYm m)
    (Work.FTS.PhiStar.Honesty.cmode_sq_integrable hX hXm m) hz
  have hcg := radGreen_congr_Ioi (α := α) m
    (f := fun t => Work.FTS.PhiStar.Series.cmode m (fun z θ => X z θ - Y z θ) t)
    (g := fun t => Work.FTS.PhiStar.Series.cmode m X t
      - Work.FTS.PhiStar.Series.cmode m Y t)
    (fun t ht => Work.FTS.PhiStar.Honesty.DiffGreen.cmode_sub hX hY hXm hYm m ht) hz
  simp only [Work.FTS.PhiStar.Series.acoeff]
  rw [hcg]
  exact hsl

/-! ## The truncations are additive in the source -/

private lemma psiTrunc_sub_eq {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {X Y : ℝ → ℝ → ℝ} (hX : Work.FTS.EllipticEst.SmoothOpen X)
    (hY : Work.FTS.EllipticEst.SmoothOpen Y)
    (hXm : Work.Spaces.HkMem α 0 X) (hYm : Work.Spaces.HkMem α 0 Y)
    (N : ℕ) {z : ℝ} (hz : 0 < z) (θ : ℝ) :
    Work.FTS.PhiStar.Series.psiTrunc α X N z θ
        - Work.FTS.PhiStar.Series.psiTrunc α Y N z θ
      = Work.FTS.PhiStar.Series.psiTrunc α (fun z θ => X z θ - Y z θ) N z θ := by
  simp only [Work.FTS.PhiStar.Series.psiTrunc]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun m _ => by
    rw [acoeff_sub hα hα4 hX hY hXm hYm m hz]
    ring)

/-- `psiSeries` is additive in the source on the open quadrant: `psiSeries α X - psiSeries α Y = psiSeries α (X - Y)`.
Suggested route (avoids any `Summable` bookkeeping): the truncations satisfy
`psiTrunc α X N z θ - psiTrunc α Y N z θ = psiTrunc α (X - Y) N z θ` for every `N`, because
`acoeff α m (X - Y) z = acoeff α m X z - acoeff α m Y z` (from `cmode_sub` + `radGreen_sub`);
each of the three truncation families converges (`psiTrunc_tendsto_psiSeries`) and the limit of a
difference is the difference of the limits, so `tendsto_nhds_unique` closes it. -/
theorem psiSeries_sub_eqOn {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {X Y : ℝ → ℝ → ℝ}
    (hXsm : Work.FTS.EllipticEst.SmoothOpen X) (hYsm : Work.FTS.EllipticEst.SmoothOpen Y)
    (hXm0 : Work.Spaces.HkMem α 0 X) (hYm0 : Work.Spaces.HkMem α 0 Y)
    (hXm1 : Work.Spaces.HkMem α 1 X) (hYm1 : Work.Spaces.HkMem α 1 Y)
    (hXor : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar X z = 0)
    (hYor : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar Y z = 0)
    (hXL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => X p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0)
    (hYL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Y p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0)
    (hZsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => X z θ - Y z θ))
    (hZor : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (fun z θ => X z θ - Y z θ) z = 0)
    (hZL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (X p.1 p.2 - Y p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Work.FTS.PhiStar.Series.psiSeries α X z θ - Work.FTS.PhiStar.Series.psiSeries α Y z θ
        = Work.FTS.PhiStar.Series.psiSeries α (fun z θ => X z θ - Y z θ) z θ := by
  intro z hz θ hθ0 hθ2
  have hα1 : α ≤ 1 := by linarith
  have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ2⟩
  -- the three truncation families converge to their series
  have hXlim := Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries (α := α) hα hα1
    hXor hXsm hXL2 hz hθI
  have hYlim := Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries (α := α) hα hα1
    hYor hYsm hYL2 hz hθI
  have hZlim := Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries (α := α) hα hα1
    hZor hZsm hZL2 hz hθI
  -- the difference of the first two is again a convergent family, with the limit `· - ·`
  have hsub := hXlim.sub hYlim
  -- and it is *pointwise equal* to the third family
  have hfun : (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α X N z θ
        - Work.FTS.PhiStar.Series.psiTrunc α Y N z θ)
      = fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α (fun z θ => X z θ - Y z θ) N z θ :=
    funext fun N => psiTrunc_sub_eq hα hα4 hXsm hYsm hXm0 hYm0 N hz θ
  rw [hfun] at hsub
  exact tendsto_nhds_unique hsub hZlim

end Work.FTS.PhiStar.RouteB
