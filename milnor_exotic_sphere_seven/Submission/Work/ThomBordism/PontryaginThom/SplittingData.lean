import Submission.Work.ThomBordism.PontryaginThom.TangentCompat
import Submission.Work.ThomBordism.PontryaginThom.FrameCoordsCont
import Submission.Work.ThomBordism.PontryaginThom.exists_normalData_of_immersion
import Submission.Work.ThomBordism.PontryaginThom.Splitting

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The splitting `TV ⊕ ν ≅ ε^{8+k}` of the normal bundle of an immersion

`Splitting.lean` proves `nonempty_bundleIso_splitting`: the complement data `D` of a family of
projections with a common kernel, together with the frames `A i x` of the plane in the charts and
their coordinate extraction `Ainv i x`, produce the splitting of the trivial bundle
`TV ⊕ ν ≅ ε^{8+k}`.  This file supplies its hypotheses for the **concrete** data of an immersion
`f : V → ℝ^{8+k}`:

* `Zt` is the tangent bundle `tangentBundle (𝓡 8) V.pt` (indexed by the atlas of `V`);
* `D = coverData f hf hinj` is the complement data of `exists_normalData_of_immersion.lean`
  (indexed by the finite cover `CoverIdx V k`), whose projection and insertion are
  `coverP`/`coverI`;
* `A i x = frame f i x` is the frame of `im (d f_x)` in the chart `i`, and
  `Ainv i x = frameCoords (frame f i x)` extracts its coordinates.

The hypotheses are then:

* `ker_eq_range` — the kernel of `coverP` is the plane of the frame: `ker_coverP` and the
  chart-independence of the plane `range_coeffMap_frame_agree`;
* `Ainv_left` — `frameCoords_coeffMap`;
* `Ainv_proj` — `coeffMap_frameCoords` (the left side is `orthProj`) against the identity
  `orthInj (complInj (planeProj u)) = orthInj u` (`orthInj_planeProj_complInj`), with the
  chart-independence of `orthProj` (`orthProj_eq_of_range_coeffMap`);
* `Pi_agree` — the same identity for two chart indices: the insertion is the *orthogonal* one, hence
  chart-independent on the plane;
* `A_compat`/`Ainv_compat` — the chain rule (`TangentCompat.lean`).

The output is `nonempty_bundleIso_coverData`: the complement bundle `coverData.toRealBundle` is a
complement of the tangent bundle, i.e. it is the normal bundle of the immersion.
-/

open scoped Manifold ContDiff Topology

namespace Work.ThomBordism.PontryaginThom

open Work.ThomBordism.Grassmann Work.TangentClasses Work.Thom

noncomputable section

variable {V : Man8} {k : ℕ}

/-- The insertion of the complement data, on its base set, is the orthogonal insertion followed by
the coordinate insertion — definitionally, once the `if` of `coverI` is reduced. -/
theorem coverI_of_det (f : V.pt → Euc (8 + k)) (i : CoverIdx V k) (x : V.pt)
    (h : coverDet f i x ≠ 0) :
    coverI f i x = (LinearMap.toContinuousLinearMap (orthInj (coverFrame f i x))).comp
      (LinearMap.toContinuousLinearMap (complInj i.2)) := by
  rw [coverI, dif_pos h]

/-- The projection of the complement data, on its base set, is `planeProj` of the frame. -/
theorem coverP_of_det (f : V.pt → Euc (8 + k)) (i : CoverIdx V k) (x : V.pt)
    (h : coverDet f i x ≠ 0) :
    coverP f i x
      = LinearMap.toContinuousLinearMap (planeProj (coverFrame f i x) i.2 h) := by
  rw [coverP, dif_pos h]

/-- The insertion of the complement data, evaluated on the projection of a vector, is the orthogonal
insertion of the vector: the difference lies in the plane, which the orthogonal insertion kills
(`orthInj_planeProj_complInj`). -/
theorem coverI_coverP_apply (f : V.pt → Euc (8 + k))
    (hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f)
    (hinj : ∀ x : V.pt, Function.Injective (mfderiv (𝓡 8) (𝓡 (8 + k)) f x))
    (i : CoverIdx V k) (x : V.pt) (hx : x ∈ coverBaseSet f i) (u : Fin (8 + k) → ℝ) :
    coverI f i x (coverP f i x u) = orthInj (coverFrame f i x) u := by
  have h : coverDet f i x ≠ 0 := hx.2
  rw [coverI_of_det f i x h, coverP_of_det f i x h]
  exact orthInj_planeProj_complInj (coverFrame f i x)
    (frame_linearIndependent f hf hinj (coverChart i) hx.1) i.2 h u

/-! ## The splitting -/

/-- **The normal bundle of an immersion is a complement of the tangent bundle**:
`TV ⊕ ν ≅ ε^{8+k}` for `ν = (coverData f hf hinj).toRealBundle`, the complement bundle of the image
of the derivative. -/
theorem nonempty_bundleIso_coverData (f : V.pt → Euc (8 + k))
    (hf : ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 f)
    (hinj : ∀ x : V.pt, Function.Injective (mfderiv (𝓡 8) (𝓡 (8 + k)) f x)) :
    Nonempty (BundleIso
      ((tangentBundle (𝓡 8) V.pt).sum (coverData f hf hinj).toRealBundle)
      (RealBundle.trivial V.pt (Euc (8 + k)) Unit)) := by
  classical
  have hLI : ∀ (i : atlas (Euc 8) V.pt) (x : V.pt), x ∈ i.1.source →
      LinearIndependent ℝ (frame f i x) := fun i x hx => frame_linearIndependent f hf hinj i hx
  refine nonempty_bundleIso_splitting (tangentBundle (𝓡 8) V.pt) (coverData f hf hinj)
    (fun i x => frame f i x)
    (fun i x => LinearMap.toContinuousLinearMap (frameCoords (frame f i x)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- continuity of the frame
    intro i
    exact continuousOn_frame f hf i
  · -- continuity of the coordinates: delegated lemma
    intro i
    exact continuousOn_frameCoordsCLM (fun x => frame f i x) (i.1.source)
      (continuousOn_frame f hf i) (fun x hx => hLI i x hx)
  · -- the kernel of the projection is the plane of the frame
    intro j i x hj hi
    rw [show (coverData f hf hinj).P j x = coverP f j x from rfl, ker_coverP f j x hj]
    exact range_coeffMap_frame_agree f hf (coverChart j) i hj.1 hi
  · -- the coordinates are a left inverse of the frame
    intro i x _ v
    show frameCoords (frame f i x) (coeffMap (frame f i x) v) = v
    exact frameCoords_coeffMap (frame f i x) (hLI i x (by assumption)) v
  · -- the two maps are inverse on the fibre
    intro i j x hi hj u
    rw [show (coverData f hf hinj).I j x = coverI f j x from rfl,
      show (coverData f hf hinj).P j x = coverP f j x from rfl]
    change coeffMap (frame f i x) (frameCoords (frame f i x) u)
      = u - coverI f j x (coverP f j x u)
    rw [show coeffMap (frame f i x) (frameCoords (frame f i x) u) = orthProj (frame f i x) u from
      coeffMap_frameCoords (frame f i x) (hLI i x hi) u]
    rw [show coverI f j x (coverP f j x u) = orthInj (coverFrame f j x) u from
      coverI_coverP_apply f hf hinj j x hj u]
    rw [orthInj, LinearMap.sub_apply, LinearMap.id_apply, sub_sub_cancel]
    exact congrArg (fun L => L u)
      (orthProj_eq_of_range_coeffMap (frame f i x) (frame f (coverChart j) x) (hLI i x hi)
        (hLI (coverChart j) x hj.1) (range_coeffMap_frame_agree f hf i (coverChart j) hi hj.1))
  · -- the insertion of the complement is chart-independent
    intro i j x hi hj u
    rw [show (coverData f hf hinj).I i x = coverI f i x from rfl,
      show (coverData f hf hinj).P i x = coverP f i x from rfl,
      show (coverData f hf hinj).I j x = coverI f j x from rfl,
      show (coverData f hf hinj).P j x = coverP f j x from rfl,
      show coverI f i x (coverP f i x u) = orthInj (coverFrame f i x) u from
        coverI_coverP_apply f hf hinj i x hi u,
      show coverI f j x (coverP f j x u) = orthInj (coverFrame f j x) u from
        coverI_coverP_apply f hf hinj j x hj u]
    rw [show orthInj (coverFrame f i x) = orthInj (coverFrame f j x) from by
      rw [orthInj, orthInj, orthProj_eq_of_range_coeffMap (frame f (coverChart i) x)
        (frame f (coverChart j) x) (hLI (coverChart i) x hi.1) (hLI (coverChart j) x hj.1)
        (range_coeffMap_frame_agree f hf (coverChart i) (coverChart j) hi.1 hj.1)]]
  · -- the frame is compatible with the transition function of the tangent bundle
    intro i x hx v
    exact frame_A_compat f hf i hx v
  · -- the coordinates are compatible with the transition function of the tangent bundle
    intro i x hx u
    exact frame_Ainv_compat f hf hinj i hx u

end

end Work.ThomBordism.PontryaginThom
