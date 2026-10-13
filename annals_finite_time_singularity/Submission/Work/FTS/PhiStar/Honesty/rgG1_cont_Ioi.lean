/-
# `Work.FTS.PhiStar.Honesty.rgG1_cont_Ioi`

**Continuity of the decaying radial Green branch.**  With `q = rgQ α m = (2m+5)/α ≥ 28` and

  `rgG1 α m c z = z^{-q} · rgA α m c z`,   `rgA α m c z = ∫ t in 0..z, c t · t^{q-1}`,

the function `z ↦ rgG1 α m c z` is continuous on `(0, ∞)` under the *weak* honesty hypotheses
`AEMeasurable c`, `(c t)²/t⁴ ∈ L¹(0,1)`, `(c t)² ∈ L¹(1,∞)`.

Why this is not the false sibling `radGreen_mul_deriv_atTop_zero`: `hnear`/`hfar` constrain `c`
only through `c²`, so they say nothing about the *a.e. strong measurability* of the forward
integrand `rgF1 α m c = c t · t^{q-1}` — with a non-measurable sign the Bochner-integral convention
(`integral_undef`) would make the primitive jump.  The hypothesis `AEMeasurable c` rules exactly
this out (`AEMeasurable.aestronglyMeasurable`), and then `rgF1` is dominated by the AM–GM majorant
`(c t)²/2 + 1/2` on `(0,1]` (`t^{q-1} ≤ 1` and `t⁴ ≤ 1` there) and by `z^{q-1}·((c t)²/2 + 1/2)` on
`(1,z]`, both integrable thanks to `hnear`/`hfar`.

The proof is the assembly of two ingredients:

* `Work.FTS.PhiStar.Honesty.rgF1_integrableOn_Ioc` (delegated, proved in this workspace): the
  forward integrand is integrable on `(0,X]` for every `X > 0`;
* `Work.FTS.EllipticEst.Cert.GbarSin.continuousOn_primitive_Ioi` (already in this workspace):
  a function interval-integrable on `[0,z]` for every `z > 0` has a primitive continuous on
  `(0,∞)`.

Multiplying the continuous primitive `rgA` by the continuous prefactor `z ↦ z^{-q}` gives `rgG1`.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Honesty.rgHonest_aemeas
import Submission.Work.FTS.PhiStar.Honesty.rgF1_integrableOn_Ioc
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.continuousOn_primitive_Ioi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.FTS.PhiStar.Honesty

theorem rgG1_cont_Ioi {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ContinuousOn (fun z : ℝ => Work.FTS.EllExist.rgG1 α m c z) (Set.Ioi 0) := by
  -- the forward integrand is interval integrable on every `[0,z]`, `z > 0`
  have hF1 := rgF1_integrableOn_Ioc (α := α) (m := m) (c := c) hα hα4 hm hc hnear hfar
  have hII : ∀ z : ℝ, 0 < z →
      IntervalIntegrable (Work.FTS.EllExist.rgF1 α m c) volume (0 : ℝ) z :=
    fun z hz => (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).mpr (hF1 z hz)
  -- hence the primitive `rgA z = ∫ t in 0..z, rgF1 α m c t` is continuous on `(0,∞)`
  have hA : ContinuousOn (fun z : ℝ => Work.FTS.EllExist.rgA α m c z) (Set.Ioi 0) := by
    simpa only [Work.FTS.EllExist.rgA] using
      Work.FTS.EllipticEst.Cert.GbarSin.continuousOn_primitive_Ioi hII
  -- and the prefactor `z ↦ z^{-q}` is continuous there
  have hr : ContinuousOn (fun z : ℝ => z ^ (-(Work.FTS.EllExist.rgQ α m))) (Set.Ioi 0) :=
    continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt hz))
  exact hr.mul hA

end Work.FTS.PhiStar.Honesty
