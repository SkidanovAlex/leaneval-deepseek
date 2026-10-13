import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.ProductTools
import Submission.Work.Spaces.cs_integral
import Submission.Work.Elliptic.Fstar_sq_le
import Submission.Work.Elliptic.L12_eq_radial
import Submission.Work.FTS.EllipticEst.harOp_aux
import Submission.Work.FTS.EllipticEst.L12_tendsto_atTop_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Gsing α F z → 0` as `z → ∞`

`Work.Elliptic.Gsing α F = Gstar α F + Gbar α F` is the singular part of Elgindi's §'The
singular term'.  Both summands are integrals of the angular moment `F_*`, and we show each of
them tends to `0` at `+∞` from `Work.Spaces.L2Mem F` alone (that is, `∫_0^∞ ∫_θ F(z,θ)² < ∞`).

The reduction is through the pointwise majorant of `F_*` supplied by Cauchy–Schwarz:

  `|F_*(s)| ≤ gsingMaj F s := √(π/2 · ∫_θ F(s,θ)² dθ)`,   `∫_0^∞ (gsingMaj F s)² < ∞`.

* `Gstar α F = -(1/(4α)) L₁₂(F)` and `L₁₂(F)(z) = 3 ∫_z^∞ F_*(s)/s ds`
  (`Work.Elliptic.L12_eq_radial`), a tail of an `L¹` function:
  `L12_tendsto_atTop_zero`.
* `Gbar α F z = -(3/(4α)) z^{-5/α} ∫_0^z s^{5/α-1} F_*(s) ds`, the weighted Hardy transform,
  which vanishes at `+∞` by `harOp_tendsto_zero`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The angular slice of `F` and the pointwise majorant of `F_*` -/

/-- The angular `L²` density `∫_θ F(s,θ)² dθ` of `F`. -/
def gsingSlice (F : ℝ → ℝ → ℝ) (s : ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, (F s θ) ^ 2

/-- The Cauchy–Schwarz majorant `√(π/2 · ∫_θ F(s,θ)²)` of `|F_*(F)(s)|`. -/
def gsingMaj (F : ℝ → ℝ → ℝ) (s : ℝ) : ℝ := Real.sqrt (Real.pi / 2 * gsingSlice F s)

lemma gsingSlice_nonneg (F : ℝ → ℝ → ℝ) (s : ℝ) : 0 ≤ gsingSlice F s :=
  integral_nonneg fun _ => sq_nonneg _

lemma gsingMaj_nonneg (F : ℝ → ℝ → ℝ) (s : ℝ) : 0 ≤ gsingMaj F s :=
  Real.sqrt_nonneg _

/-- `gsingMaj F` is the square root of the `L¹` function `(π/2) · gsingSlice F`. -/
lemma gsingMaj_sq (F : ℝ → ℝ → ℝ) (s : ℝ) :
    (gsingMaj F s) ^ 2 = Real.pi / 2 * gsingSlice F s := by
  rw [gsingMaj, Real.sq_sqrt (mul_nonneg (by positivity) (gsingSlice_nonneg F s))]

/-- Cauchy–Schwarz for the angular moment (`Work.Elliptic.Fstar_sq_le`): `|F_*|` is dominated by
`gsingMaj`. -/
lemma abs_Fstar_le_gsingMaj (F : ℝ → ℝ → ℝ) (hL2 : Work.Spaces.L2Mem F) {s : ℝ} (hs : 0 < s) :
    |Work.Elliptic.Fstar F s| ≤ gsingMaj F s := by
  have h : (Work.Elliptic.Fstar F s) ^ 2
      ≤ Real.pi / 2 * gsingSlice F s := by
    simpa [gsingSlice] using Work.Elliptic.Fstar_sq_le F s (hL2.1 s (le_of_lt hs))
  calc |Work.Elliptic.Fstar F s| = Real.sqrt ((Work.Elliptic.Fstar F s) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (Real.pi / 2 * gsingSlice F s) := Real.sqrt_le_sqrt h
    _ = gsingMaj F s := rfl

/-- The angular slice of an `L2Mem` function is integrable on `(0,∞)`. -/
lemma integrableOn_gsingSlice (F : ℝ → ℝ → ℝ) (hL2 : Work.Spaces.L2Mem F) :
    IntegrableOn (gsingSlice F) (Set.Ioi 0) := by
  have h2 : IntegrableOn (gsingSlice F) (Set.Ici (0 : ℝ)) := hL2.2
  exact MeasureTheory.IntegrableOn.mono_set h2 Set.Ioi_subset_Ici_self

/-- `M²` is integrable for `M = gsingMaj F`. -/
lemma integrableOn_gsingMaj_sq (F : ℝ → ℝ → ℝ) (hL2 : Work.Spaces.L2Mem F) :
    IntegrableOn (fun s => (gsingMaj F s) ^ 2) (Set.Ioi 0) := by
  have h := (integrableOn_gsingSlice F hL2).const_mul (Real.pi / 2)
  refine MeasureTheory.IntegrableOn.congr_fun h (fun s _ => ?_) measurableSet_Ioi
  exact (gsingMaj_sq F s).symm

/-- `gsingMaj F` is a.e. measurable. -/
lemma aemeasurable_gsingMaj (F : ℝ → ℝ → ℝ) (hL2 : Work.Spaces.L2Mem F) :
    AEMeasurable (gsingMaj F) (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have h1 : AEMeasurable (fun s => Real.pi / 2 * gsingSlice F s)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    ((integrableOn_gsingSlice F hL2).aestronglyMeasurable.const_mul
      (Real.pi / 2)).aemeasurable
  exact (Real.continuous_sqrt.comp_aestronglyMeasurable h1.aestronglyMeasurable).aemeasurable

/-! ## The Hardy form of `Gbar` -/

/-- `Gbar α F z = -(3/(4α)) · z^{-5/α} ∫_0^z s^{5/α-1} F_*(s) ds`, i.e. `Gbar α F` is
`-(3/(4α))` times the weighted Hardy transform of the angular moment. -/
lemma Gbar_eq_harOp_form (α : ℝ) (hα : α ≠ 0) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Gbar α F z = -(3 / (4 * α)) * (z ^ (-(5 / α))
      * ∫ s in (0 : ℝ)..z, s ^ (5 / α - 1) * Work.Elliptic.Fstar F s) := by
  have hint : ∫ s in (0 : ℝ)..z, s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s
      = ∫ s in (0 : ℝ)..z, s ^ (5 / α - 1) * Work.Elliptic.Fstar F s :=
    intervalIntegral.integral_congr (fun s _ => by rw [div_sub_one hα])
  rw [Work.Elliptic.Gbar, hint]
  ring

/-! ## The target -/

theorem Gsing_tendsto_atTop_zero (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hL2 : Work.Spaces.L2Mem F) :
    Filter.Tendsto (fun z : ℝ => Work.Elliptic.Gsing α F z) Filter.atTop (nhds (0 : ℝ)) := by
  have hαne : α ≠ 0 := hα.ne'
  have hGstar : Filter.Tendsto (fun z : ℝ => Work.Elliptic.Gstar α F z) Filter.atTop
      (nhds (0 : ℝ)) := by
    have h := L12_tendsto_atTop_zero F hL2
    have hfun : (fun z : ℝ => Work.Elliptic.Gstar α F z)
        = fun z : ℝ => -(1 / (4 * α)) * Work.Elliptic.L12 F z := funext fun z => rfl
    rw [hfun]
    simpa using h.const_mul (-(1 / (4 * α)))
  have hGbar : Filter.Tendsto (fun z : ℝ => Work.Elliptic.Gbar α F z) Filter.atTop
      (nhds (0 : ℝ)) := by
    have h := GsingAux.harOp_tendsto_zero (5 / α) (by positivity) (Work.Elliptic.Fstar F)
      (gsingMaj F)
      (gsingMaj_nonneg F) (integrableOn_gsingMaj_sq F hL2) (aemeasurable_gsingMaj F hL2)
      (fun s hs => abs_Fstar_le_gsingMaj F hL2 hs)
    have hfun : (fun z : ℝ => Work.Elliptic.Gbar α F z) = fun z : ℝ => -(3 / (4 * α))
        * (z ^ (-(5 / α))
          * ∫ s in (0 : ℝ)..z, s ^ (5 / α - 1) * Work.Elliptic.Fstar F s) :=
      funext fun z => Gbar_eq_harOp_form α hαne F z
    rw [hfun]
    simpa using h.const_mul (-(3 / (4 * α)))
  have hsum : Filter.Tendsto
      (fun z : ℝ => Work.Elliptic.Gstar α F z + Work.Elliptic.Gbar α F z)
      Filter.atTop (nhds (0 + 0)) := hGstar.add hGbar
  simpa [Work.Elliptic.Gsing] using hsum

end Work.FTS.EllipticEst
