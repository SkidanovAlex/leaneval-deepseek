import Mathlib
import Submission.Work.Projection.TransverseDefs

set_option linter.style.haveILetI false

namespace Work.Projection

open scoped Manifold ContDiff
open Topology MeasureTheory

/-- **The chartwise immersion-bad parametrisation has a singular derivative.**  At every point
`(y, w)` of its domain the derivative of `immParam f p` kills the (non-zero) tangent vector
`(0, w)`: indeed `immParam f p (y, t • w) = immParam f p (y, w)` for `t ≠ 0`, because
`extract` is invariant under scaling. -/
lemma fderiv_immParam_apply_snd_eq_zero {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (2*n+1)))
    (hf : ContMDiff (𝓡 n) (𝓡 (2*n+1)) ∞ f) (p : M)
    {y w : EuclideanSpace ℝ (Fin n)} (hyw : (y,w) ∈ immDom (n:=n) (k:=2*n) f p) :
    (fderiv ℝ (immParam (n:=n) (k:=2*n) f p) (y,w)) (0, w) = 0 := by
  have hopen := isOpen_immDom (n:=n) (k:=2*n) f hf p
  have hCD := contDiffOn_immParam (n:=n) (k:=2*n) f hf p
  have hdiff : DifferentiableAt ℝ (immParam (n:=n) (k:=2*n) f p) (y,w) :=
    (hCD.contDiffAt (hopen.mem_nhds hyw)).differentiableAt (by norm_num)
  have hAt : HasFDerivAt (immParam (n:=n) (k:=2*n) f p)
      (fderiv ℝ (immParam (n:=n) (k:=2*n) f p) (y,w)) (y,w) := hdiff.hasFDerivAt
  -- the curve `t ↦ (y, t • w)`, whose tangent at `1` is `(0, w)`.
  have hc : HasDerivAt (fun t : ℝ => (y, t • w)) ((0 : EuclideanSpace ℝ (Fin n)), w) 1 := by
    have h2 : HasDerivAt (fun t : ℝ => t • w) w 1 := by
      simpa using (hasDerivAt_id (1:ℝ)).smul_const w
    have h1 : HasDerivAt (fun _ : ℝ => y) (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      hasDerivAt_const 1 y
    simpa using h1.prodMk h2
  have hcomp : HasDerivAt (fun t : ℝ => immParam (n:=n) (k:=2*n) f p (y, t • w))
      ((fderiv ℝ (immParam (n:=n) (k:=2*n) f p) (y,w))
        ((0 : EuclideanSpace ℝ (Fin n)), w)) 1 :=
    hAt.comp_hasDerivAt_of_eq (x := (1:ℝ)) hc (by simp)
  -- ...but the composition is constant near `1`.
  have hev : (fun t : ℝ => immParam (n:=n) (k:=2*n) f p (y, t • w)) =ᶠ[𝓝 (1:ℝ)]
      (fun _ => immParam (n:=n) (k:=2*n) f p (y,w)) := by
    filter_upwards [eventually_ne_nhds (show (1:ℝ) ≠ 0 by norm_num)] with t ht
    show extract ((fderiv ℝ (chartRep (n:=n) (k:=2*n) f p) y) (t • w)) =
      extract ((fderiv ℝ (chartRep (n:=n) (k:=2*n) f p) y) w)
    rw [ContinuousLinearMap.map_smul, extract_smul t ht]
  have h0 : HasDerivAt (fun _ : ℝ => immParam (n:=n) (k:=2*n) f p (y,w))
      ((fderiv ℝ (immParam (n:=n) (k:=2*n) f p) (y,w))
        ((0 : EuclideanSpace ℝ (Fin n)), w)) 1 :=
    (hev.hasDerivAt_iff).mp hcomp
  exact ((hasDerivAt_const (1:ℝ) (immParam (n:=n) (k:=2*n) f p (y,w))).unique h0).symm

/-- `Work.Projection.immBadCoord e p` (defined in `Submission.Work.Projection.TransverseDefs` as
the image under `pairEquiv n` of the immersion-bad directions of the chart at `p`) has measure
zero.  Concretely, that image is the image of the map `(y, w) ↦ pairEquiv n (extract ((D y) w))` on
the domain where the last coordinate of `(D y) w` is non-zero, where `D y = fderiv ℝ (chartRep e p) y`.
The point is that this map is invariant under scaling `w`, so its derivative always has the non-zero
kernel vector `(0, w)` and hence vanishing determinant; the equal-dimension case of Sard
(`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`) then gives the conclusion.  The
measure is the Lebesgue (= product Haar) measure on
`EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)`. -/
theorem volume_image_immBadCoord_eq_zero {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ⊤ M]
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1)))) ⊤ e) (p : M) :
    MeasureTheory.volume (immBadCoord e p) = 0 := by
  haveI : IsManifold (𝓡 n) ∞ M := IsManifold.of_le (m := ∞) (n := ⊤) le_top
  have he' : ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ e := he.of_le le_top
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
  have hmain := addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume)
    (s := immDom (n:=n) (k:=2*n) e p)
    (f := fun x => (pairEquiv n).toContinuousLinearEquiv
      (immParam (n:=n) (k:=2*n) e p x))
    (f' := fun x => ((pairEquiv n).toContinuousLinearEquiv).toContinuousLinearMap.comp
      (fderiv ℝ (immParam (n:=n) (k:=2*n) e p) x))
    ?_ ?_
  · rw [himg] at hmain
    exact hmain
  · -- differentiability of the parametrisation on its domain.
    intro x hx
    obtain ⟨y, w⟩ := x
    have hdiff : DifferentiableAt ℝ (immParam (n:=n) (k:=2*n) e p) (y,w) :=
      ((contDiffOn_immParam (n:=n) (k:=2*n) e he' p).contDiffAt
        ((isOpen_immDom (n:=n) (k:=2*n) e he' p).mem_nhds hx)).differentiableAt (by norm_num)
    have hh := (ContinuousLinearEquiv.hasFDerivAt (pairEquiv n).toContinuousLinearEquiv
      (x := immParam (n:=n) (k:=2*n) e p (y,w))).comp (y,w) hdiff.hasFDerivAt
    exact hh.hasFDerivWithinAt
  · -- the derivative is singular everywhere on the domain.
    intro x hx
    obtain ⟨y, w⟩ := x
    have hker : (((pairEquiv n).toContinuousLinearEquiv).toContinuousLinearMap.comp
        (fderiv ℝ (immParam (n:=n) (k:=2*n) e p) (y,w)))
        ((0 : EuclideanSpace ℝ (Fin n)), w) = 0 := by
      simp only [ContinuousLinearMap.comp_apply]
      rw [fderiv_immParam_apply_snd_eq_zero e he' p hx]
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
    change LinearMap.det ((((pairEquiv n).toContinuousLinearEquiv).toContinuousLinearMap.comp
      (fderiv ℝ (immParam (n:=n) (k:=2*n) e p) (y,w))).toLinearMap) = 0
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot).mpr hker_ne

end Work.Projection
