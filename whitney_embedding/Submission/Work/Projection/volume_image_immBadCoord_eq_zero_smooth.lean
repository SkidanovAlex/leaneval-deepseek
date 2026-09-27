import Mathlib
import Submission.Work.Projection.TransverseDefs
import Submission.Work.Projection.volume_image_immBadCoord_eq_zero
import Submission.Work.Projection.dimH_badImmCharts

set_option linter.style.haveILetI false

namespace Work.Projection

open scoped Manifold ContDiff
open Topology MeasureTheory

set_option maxHeartbeats 2000000 in
/-- `Work.Projection.immBadCoord e p` (the image under `pairEquiv n` of the immersion-bad directions
of the chart at `p`, with the *smooth* (`C^∞`) manifold structure, i.e. the order
`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`) has measure zero.  This is identical to
`Work.Projection.volume_image_immBadCoord_eq_zero` in
`Submission.Work.Projection.volume_image_immBadCoord_eq_zero` except that the hypothesis is
smoothness rather than analyticity.  Concretely, the image is that of the map
`(y, w) ↦ pairEquiv n (extract ((D y) w))` on the domain where the last coordinate of `(D y) w` is
non-zero, where `D y = fderiv ℝ (chartRep e p) y`; that map is invariant under scaling `w`, so its
derivative always has the non-zero kernel vector `(0, w)` and hence vanishing determinant, which is
what the equal-dimension case of Sard
(`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`) needs.  The measure is the
Lebesgue (= product Haar) measure on `EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)`. -/
theorem volume_image_immBadCoord_eq_zero_smooth {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e)
    (p : M) :
    MeasureTheory.volume (immBadCoord e p) = 0 := by
  -- `vol : ℝ^{2n} × ℝ^{2n}` is the product of two Haar measures, hence a Haar measure.
  haveI : Measure.IsAddHaarMeasure (volume : Measure
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) :=
    Measure.prod.instIsAddHaarMeasure volume volume
  -- the image under `pairEquiv n` of the parametrisation is `immBadCoord e p`.
  have himg : (fun x => (pairEquiv n).toContinuousLinearEquiv
        (immParam (n:=n) (k:=2*n) e p x)) '' (immDom (n:=n) (k:=2*n) e p) =
      immBadCoord e p := by
    rw [immBadCoord]
    exact Set.image_comp _ _ _
  -- differentiability of the parametrisation on its domain.
  have hdiff : ∀ x ∈ (immDom (n:=n) (k:=2*n) e p),
      HasFDerivWithinAt (fun x => (pairEquiv n).toContinuousLinearEquiv
          (immParam (n:=n) (k:=2*n) e p x))
        (((pairEquiv n).toContinuousLinearEquiv).toContinuousLinearMap.comp
          (fderiv ℝ (immParam (n:=n) (k:=2*n) e p) x))
        (immDom (n:=n) (k:=2*n) e p) x := by
    intro x hx
    obtain ⟨y, w⟩ := x
    have hd : DifferentiableAt ℝ (immParam (n:=n) (k:=2*n) e p) (y,w) :=
      ((contDiffOn_immParam (n:=n) (k:=2*n) e he p).contDiffAt
        ((isOpen_immDom (n:=n) (k:=2*n) e he p).mem_nhds hx)).differentiableAt (by norm_num)
    have hh := (ContinuousLinearEquiv.hasFDerivAt (pairEquiv n).toContinuousLinearEquiv
      (x := immParam (n:=n) (k:=2*n) e p (y,w))).comp (y,w) hd.hasFDerivAt
    exact hh.hasFDerivWithinAt
  -- the derivative is singular everywhere on the domain.
  have hsing : ∀ x ∈ (immDom (n:=n) (k:=2*n) e p),
      (((pairEquiv n).toContinuousLinearEquiv).toContinuousLinearMap.comp
        (fderiv ℝ (immParam (n:=n) (k:=2*n) e p) x)).det = 0 := by
    intro x hx
    obtain ⟨y, w⟩ := x
    have hker : (((pairEquiv n).toContinuousLinearEquiv).toContinuousLinearMap.comp
        (fderiv ℝ (immParam (n:=n) (k:=2*n) e p) (y,w)))
        ((0 : EuclideanSpace ℝ (Fin n)), w) = 0 := by
      simp only [ContinuousLinearMap.comp_apply]
      rw [fderiv_immParam_apply_snd_eq_zero e he p hx]
      simp
    -- the kernel vector `(0, w)` is non-zero, as `w = 0` is excluded by the domain condition.
    have hw : w ≠ 0 := by
      intro hw0
      refine hx.2 ?_
      rw [hw0]
      simp
    have hne : ((0 : EuclideanSpace ℝ (Fin n)), w) ≠ 0 := by
      intro h
      exact hw (by simpa using congrArg Prod.snd h)
    have hker_ne : LinearMap.ker ((((pairEquiv n).toContinuousLinearEquiv).toContinuousLinearMap.comp
        (fderiv ℝ (immParam (n:=n) (k:=2*n) e p) (y,w))).toLinearMap) ≠ ⊥ := by
      intro hbot
      have hmem : ((0 : EuclideanSpace ℝ (Fin n)), w) ∈
          LinearMap.ker ((((pairEquiv n).toContinuousLinearEquiv).toContinuousLinearMap.comp
            (fderiv ℝ (immParam (n:=n) (k:=2*n) e p) (y,w))).toLinearMap) :=
        LinearMap.mem_ker.mpr hker
      rw [hbot] at hmem
      simp only [Submodule.mem_bot] at hmem
      exact hne hmem
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot).mpr hker_ne
  have hmain := addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume)
    (s := immDom (n:=n) (k:=2*n) e p)
    (f := fun x => (pairEquiv n).toContinuousLinearEquiv
      (immParam (n:=n) (k:=2*n) e p x))
    (f' := fun x => ((pairEquiv n).toContinuousLinearEquiv).toContinuousLinearMap.comp
      (fderiv ℝ (immParam (n:=n) (k:=2*n) e p) x))
    hdiff hsing
  rw [himg] at hmain
  exact hmain

end Work.Projection
