import Mathlib
import Submission.Work.Sweep.Defs
import Submission.Work.Sweep.AeTransverseSphere.ae_transverse_sphere

/-!
# Almost every concentric sphere meets the curve in finitely many points

Fix a smooth knot `K` and a centre `x ∈ ℝ³`.  For almost every radius `r` the
curve meets the sphere of centre `x` and radius `r` in finitely many parameters.

## Strategy

Write `g t = dist (K.curve t) x` for the distance from the centre to the curve.
For almost every `r` the sphere is *transverse* to the curve
(`Work.Sweep.AeTransverseSphere.ae_transverse_sphere`), i.e.

`∀ t, g t = r → t ∈ [0, 2π] → deriv g t ≠ 0`.

The set `L = sphereParamSet K x r` is closed (preimage of `{r}` under the
continuous `g`, intersected with the closed interval `[0, 2π]`) and contained in
the compact interval `[0, 2π]`.  At each of its points `t`, the derivative of `g`
is non-zero, so `g` is differentiable there with a non-zero derivative; the
slope of `g` at `t` is therefore non-zero on a punctured neighbourhood of `t`,
which means that `g y ≠ g t = r` for all `y ≠ t` close enough to `t`.  Hence each
point of `L` is isolated in `L`.

A compact set all of whose points are isolated is finite: if `L` were infinite,
by compactness it would have an accumulation point `t ∈ L`
(`Set.Infinite.exists_accPt_of_subset_isCompact`), contradicting the isolation
just established.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal Topology

namespace Work.Sweep.AeFiniteSphere

/-- If the curve is transverse to the sphere of centre `x` and radius `r`, then
it meets that sphere in finitely many parameters. -/
theorem finite_sphereParamSet_of_isTransverseSphere
    (K : LeanEval.KnotTheory.PardonDistortion.Knot)
    (x : LeanEval.KnotTheory.PardonDistortion.R3) (r : ℝ)
    (h : Work.Sweep.IsTransverseSphere K x r) :
    (Work.Sweep.sphereParamSet K x r).Finite := by
  classical
  -- the distance from the centre, as a function of the curve parameter
  set g : ℝ → ℝ := fun t => dist (K.curve t) x with hg
  have hgc : Continuous g := by
    rw [hg]
    exact K.smooth.continuous.dist continuous_const
  -- `sphereParamSet` is the level set of `g` at `r`, cut out by `[0, 2π]`
  have hclosed : IsClosed (Work.Sweep.sphereParamSet K x r) := by
    have heq : Work.Sweep.sphereParamSet K x r
        = {t : ℝ | g t = r} ∩ Set.Icc (0 : ℝ) (2 * Real.pi) := by
      ext t
      simp only [Work.Sweep.sphereParamSet, Set.mem_inter_iff, Set.mem_preimage,
        Metric.mem_sphere, Set.mem_Icc, Set.mem_ofPred_eq, hg]
    rw [heq]
    exact (isClosed_eq hgc continuous_const).inter isClosed_Icc
  by_contra hfin
  have hinf : (Work.Sweep.sphereParamSet K x r).Infinite := hfin
  -- an infinite subset of the compact interval has an accumulation point
  obtain ⟨tstar, _htstar_Icc, hacc⟩ :=
    hinf.exists_accPt_of_subset_isCompact isCompact_Icc
      (Set.inter_subset_right :
        Work.Sweep.sphereParamSet K x r ⊆ Set.Icc (0 : ℝ) (2 * Real.pi))
  -- the accumulation point lies in the (closed) level set
  have htstar_mem : tstar ∈ Work.Sweep.sphereParamSet K x r := by
    have h1 : tstar ∈ closure (Work.Sweep.sphereParamSet K x r) :=
      hacc.clusterPt.mem_closure
    rwa [hclosed.closure_eq] at h1
  have hgt : g tstar = r := by
    have hmem : K.curve tstar ∈ Metric.sphere x r := htstar_mem.1
    rw [hg]
    exact Metric.mem_sphere.mp hmem
  -- transversality: the distance has non-zero derivative there
  have hderiv : deriv g tstar ≠ 0 := by
    simpa [hg] using h tstar htstar_mem
  have hd : DifferentiableAt ℝ g tstar := differentiableAt_of_deriv_ne_zero hderiv
  have hHas : HasDerivAt g (deriv g tstar) tstar := hasDerivAt_deriv_iff.mpr hd
  -- the slope is non-zero near `tstar`, so `g y ≠ g tstar` for `y ≠ tstar` nearby
  have hslope : ∀ᶠ y in 𝓝[≠] tstar, slope g tstar y ≠ 0 :=
    hHas.tendsto_slope.eventually
      ((isOpen_compl_singleton (x := (0 : ℝ))).mem_nhds (by simpa using hderiv))
  have hne : ∀ᶠ y in 𝓝 tstar, y ≠ tstar → g y ≠ g tstar := by
    rw [eventually_nhdsWithin_iff] at hslope
    filter_upwards [hslope] with y hy hyne
    intro hgy
    exact (hy (by simpa using hyne)) (by simp [slope_def_field, hgy])
  -- a neighbourhood of `tstar` meets `L` only in `tstar`, contradicting `hacc`
  obtain ⟨y, hy, hyne⟩ :=
    accPt_iff_nhds.mp hacc {y : ℝ | y ≠ tstar → g y ≠ g tstar} hne
  have h1 : g y ≠ g tstar := hy.1 hyne
  have h2 : g y = r := by
    have hmem : K.curve y ∈ Metric.sphere x r := hy.2.1
    rw [hg]
    exact Metric.mem_sphere.mp hmem
  exact h1 (h2.trans hgt.symm)

/-- For almost every radius `r`, the knot meets the sphere of centre `x` and
radius `r` in finitely many points. -/
theorem ae_finite_sphereParamSet (K : LeanEval.KnotTheory.PardonDistortion.Knot)
    (x : LeanEval.KnotTheory.PardonDistortion.R3) :
    ∀ᵐ r ∂MeasureTheory.volume, (Work.Sweep.sphereParamSet K x r).Finite := by
  filter_upwards [Work.Sweep.AeTransverseSphere.ae_transverse_sphere K x] with r hr
  exact finite_sphereParamSet_of_isTransverseSphere K x r hr

end Work.Sweep.AeFiniteSphere
