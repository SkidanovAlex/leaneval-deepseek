import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.ClassCHon.Zpz.RgIbl.intervalIntegrable_mul_deriv_rpow
import Submission.Work.FTS.ClassCHon.Zpz.RgIbl.intervalIntegrable_rpow_mul_contOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Zpz

open MeasureTheory Set Filter

/-- The real-power identity `(t * d t) * t ^ (q - 1) = d t * t ^ q` for `t > 0`. -/
private lemma rgMulRpowSubOne (d : ℝ → ℝ) {q t : ℝ} (ht : 0 < t) :
    (t * d t) * t ^ (q - 1) = d t * t ^ q := by
  have h1 : t ^ q = t ^ ((1 : ℝ) + (q - 1)) := by congr 1; ring
  rw [h1, Real.rpow_add ht, Real.rpow_one]
  ring

/-- `t ↦ c t * t ^ q` has derivative `deriv c t * t ^ q + q * (c t * t ^ (q - 1))` at `t > 0`. -/
private lemma rgHasDerivAt_mul_rpow {q : ℝ} {c : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hcd : HasDerivAt c (deriv c t) t) :
    HasDerivAt (fun s : ℝ => c s * s ^ q)
      (deriv c t * t ^ q + q * (c t * t ^ (q - 1))) t := by
  have hp : HasDerivAt (fun s : ℝ => s ^ q) (q * t ^ (q - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))
  refine (hcd.mul hp).congr_deriv ?_
  ring

/-- **Integration by parts at the lower end, in `rgA`-form** (intended namespace
`Work.FTS.ClassCHon.Zpz`, module `Submission.Work.FTS.ClassCHon.Zpz.radGreen_ibp_lower`).

With `q = rgQ α m = (2*m+5)/α > 0`, `rgA α m c z = ∫ t in (0)..z, c t * t ^ (q - 1)`, and `hlim`
the (requested separately) statement that `t ↦ c t * t ^ q → 0` at `0⁺`: the `t`-weighted source
`t ↦ t * deriv c t` satisfies
`rgA α m (fun t => t * deriv c t) z = c z * z ^ q - q * rgA α m c z` for every `z > 0`.

This is the integration by parts
`∫ x in (0)..z, deriv c x * x ^ q = c z * z ^ q - q * ∫ x in (0)..z, c x * x ^ (q - 1)`
(whose boundary term at `0⁺` vanishes by `hlim`), transported to `rgA` through the a.e. identity
`(t * deriv c t) * t ^ (q - 1) = deriv c t * t ^ q` on `t > 0`, via
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto` applied to `F t = c t * t ^ q` with
`a = 0`, `b = z`, `fa = 0`, `fb = F z`.
Local integrability of `deriv c` (needed for the `IntervalIntegrable` hypothesis of that result on
`(0,z)`) follows from `hd0` on `(0,1)` (`|deriv c t| ≤ z0 ^ (-q) * |t * deriv c t * t ^ (q - 1)|`
for `t ≥ z0 > 0`) and from `hdinf` on `(1,z)` (`|deriv c t| ≤ z ^ p * |t * deriv c t * t ^ (-p-1)|`).
Note `hdinf` is genuinely needed (the interval of integration reaches past `1` when `z > 1`). -/
theorem radGreen_ibp_lower {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hcd : ∀ t : ℝ, 0 < t → HasDerivAt c (deriv c t) t)
    (hlim : Filter.Tendsto (fun t => c t * t ^ (Work.FTS.EllExist.rgQ α m))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (h0 : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)) (Set.Ioo 0 1))
    (hd0 : MeasureTheory.IntegrableOn
      (fun t => t * deriv c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)) (Set.Ioo 0 1))
    (hdinf : MeasureTheory.IntegrableOn
      (fun t => t * deriv c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)) (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z →
      Work.FTS.EllExist.rgA α m (fun t => t * deriv c t) z
        = c z * z ^ (Work.FTS.EllExist.rgQ α m)
          - Work.FTS.EllExist.rgQ α m * Work.FTS.EllExist.rgA α m c z := by
  intro z hz
  have hqpos : 0 < Work.FTS.EllExist.rgQ α m := Work.FTS.EllExist.rgQ_pos hα m
  have hpnn : 0 ≤ Work.FTS.EllExist.rgP α m := Work.FTS.EllExist.rgP_nonneg hα m
  -- `c` is continuous on `(0,∞)` because it is differentiable there
  have hcont : ContinuousOn c (Ioi 0) :=
    fun t ht => (hcd t ht).continuousAt.continuousWithinAt
  -- local integrability of the two summands of the derivative of `t ↦ c t * t ^ q`
  have hA : IntervalIntegrable
      (fun t : ℝ => t * deriv c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)) volume 0 z :=
    RgIbl.intervalIntegrable_mul_deriv_rpow hqpos hpnn hd0 hdinf hz
  have hB : IntervalIntegrable
      (fun t : ℝ => c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)) volume 0 z :=
    RgIbl.intervalIntegrable_rpow_mul_contOn hcont h0 hz
  have hG : IntervalIntegrable
      (fun t : ℝ => t * deriv c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)
        + Work.FTS.EllExist.rgQ α m * (c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)))
      volume 0 z :=
    hA.add (hB.const_mul (Work.FTS.EllExist.rgQ α m))
  -- the derivative of `F t = c t * t ^ q`, in the `rgA`-compatible form
  have hder : ∀ t ∈ Ioo (0 : ℝ) z,
      HasDerivAt (fun s : ℝ => c s * s ^ (Work.FTS.EllExist.rgQ α m))
        (t * deriv c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)
          + Work.FTS.EllExist.rgQ α m * (c t * t ^ (Work.FTS.EllExist.rgQ α m - 1))) t := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have h := rgHasDerivAt_mul_rpow (q := Work.FTS.EllExist.rgQ α m) ht0 (hcd t ht0)
    refine h.congr_deriv ?_
    rw [rgMulRpowSubOne (deriv c) ht0]
  have hFz : Tendsto (fun s : ℝ => c s * s ^ (Work.FTS.EllExist.rgQ α m))
      (nhdsWithin z (Iio z)) (nhds (c z * z ^ (Work.FTS.EllExist.rgQ α m))) :=
    ((rgHasDerivAt_mul_rpow (q := Work.FTS.EllExist.rgQ α m) hz (hcd z hz)).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  -- the fundamental theorem of calculus on `(0, z)`, with the boundary term at `0` killed by `hlim`
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hz hder hG hlim hFz
  have hsplit : ∫ t in (0 : ℝ)..z, (t * deriv c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)
        + Work.FTS.EllExist.rgQ α m * (c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)))
      = (∫ t in (0 : ℝ)..z, t * deriv c t * t ^ (Work.FTS.EllExist.rgQ α m - 1))
        + Work.FTS.EllExist.rgQ α m
          * (∫ t in (0 : ℝ)..z, c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)) := by
    rw [intervalIntegral.integral_add hA (hB.const_mul _), intervalIntegral.integral_const_mul]
  rw [hsplit] at hFTC
  have hFTC' : (∫ t in (0 : ℝ)..z, t * deriv c t * t ^ (Work.FTS.EllExist.rgQ α m - 1))
        + Work.FTS.EllExist.rgQ α m
          * (∫ t in (0 : ℝ)..z, c t * t ^ (Work.FTS.EllExist.rgQ α m - 1))
      = c z * z ^ (Work.FTS.EllExist.rgQ α m) := by
    simpa using hFTC
  simp only [Work.FTS.EllExist.rgA, Work.FTS.EllExist.rgF1]
  linarith [hFTC']

end Work.FTS.ClassCHon.Zpz
