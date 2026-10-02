import Mathlib
import Submission.Work.ThomBordism.modelLevelBoundary
import Submission.Work.ThomBordism.modelPush
import Submission.Work.ThomBordism.Transversality.Preimage.BoundaryCoord
import Submission.Work.PTGeometric.LevelModel
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.CoreClass
import Submission.Work.Cohomology.HomologyPairSequence

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the model level set as a manifold with boundary, and the boundary sign of the model

`Submission/Work/ThomBordism/NOTE_SESSION29.md` §2–§4.  The last input of the last mile is the
*linear model* statement that the boundary orientation induced on the boundary of the model level set
by the coorientation of the linear splitting is `c` times the boundary generator, with a **universal**
`c = ±1` (only uniformity is used: `w ↦ -w` absorbs the value).  Before that statement can even be
written, `↥(ModelLevelSet v)` must carry a manifold-with-boundary structure whose boundary is
`modelBdry s` — that is this file's content.

* `modelHomeo` — the global homeomorphism `↥(ModelLevelSet v) ≃ₜ EuclideanHalfSpace (m+1)`,
  `x ↦ (s.Φ.symm x.1).1`;
* `modelChartedSpace`, `modelIsManifold` — the induced (singleton-chart) structure;
* `modelBdry_eq_boundary` — its boundary is `modelBdry s`.

Everything here is *linear*: the model level set is the image of `EuclideanHalfSpace (m+1) × {0}`
under the linear isomorphism `s.Φ`, so all of it is a computation with `s.half`, `s.fst`,
`s.Φ.symm_apply_apply` and `ModelSplit`'s coordinate lemmas.

**Lean notes (traps paid for).**  (a) The charted-space and manifold structures *depend on the
splitting `s`* and `s` is not inferable from the type `↥(ModelLevelSet v)`, so they cannot be global
instances: they are `def`/`theorem`s to be brought into scope with `letI := modelChartedSpace s`.
(b) A `letI … := …;` inside **parentheses in a statement** does not parse here; the statements below
therefore use `@`-applications with the instance given explicitly (they are *defeq* to the
`letI`-spelling used in the proofs, so consumers can either `letI` or use these forms).
(c) `EuclideanHalfSpace n` does **not** coerce to `EuclideanSpace ℝ (Fin n)` in an argument position
(the coercion is `@[implicit_reducible]`): write `u.1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Work.PTGeometric
open scoped Manifold ContDiff Topology

namespace Work.ThomBordism

noncomputable section

variable {m k : ℕ} [NeZero (m + 1 + k)] {v : Euc (m + 1 + k) →L[ℝ] Euc k}

/-- **The model level set is the half-space**: the global homeomorphism
`x ↦ (Φ.symm x.1).1` with inverse `u ↦ Φ (u, 0)`. -/
def modelHomeo (s : ModelSplit (a := m + 1) (k := k) v) :
    ↥(ModelLevelSet (a := m + 1) (k := k) v) ≃ₜ EuclideanHalfSpace (m + 1) where
  toFun x := ⟨(s.Φ.symm x.1).1, (s.half (s.Φ.symm x.1)).mp (by
    rw [s.Φ.apply_symm_apply]
    exact x.2.1)⟩
  invFun u := ⟨s.Φ (u.1, 0), (s.half (u.1, 0)).mpr u.2, by
    show v (s.Φ (u.1, (0 : Euc k))) = 0
    rw [s.fst (u.1, 0)]⟩
  left_inv x := by
    refine Subtype.ext ?_
    show s.Φ ((s.Φ.symm x.1).1, (0 : Euc k)) = x.1
    conv_rhs => rw [← s.Φ.apply_symm_apply x.1]
    congr 1
    exact Prod.ext rfl (modelSplit_symm_snd_eq_zero (k := k) s x).symm
  right_inv u := by
    refine Subtype.ext ?_
    show (s.Φ.symm (s.Φ (u.1, (0 : Euc k)))).1 = u.1
    rw [s.Φ.symm_apply_apply]
  continuous_toFun :=
    Continuous.subtype_mk
      (continuous_fst.comp (s.Φ.symm.continuous.comp continuous_subtype_val)) _
  continuous_invFun :=
    Continuous.subtype_mk
      (s.Φ.continuous.comp (continuous_subtype_val.prodMk continuous_const)) _

@[simp] theorem modelHomeo_apply (s : ModelSplit (a := m + 1) (k := k) v)
    (x : ↥(ModelLevelSet (a := m + 1) (k := k) v)) :
    (modelHomeo (k := k) s x).1 = (s.Φ.symm x.1).1 := rfl

/-- The singleton-chart structure on the model level set, modelled on the half-space. -/
def modelChartedSpace (s : ModelSplit (a := m + 1) (k := k) v) :
    ChartedSpace (EuclideanHalfSpace (m + 1))
      ↥(ModelLevelSet (a := m + 1) (k := k) v) :=
  (modelHomeo (k := k) s).toOpenPartialHomeomorph.singletonChartedSpace
    (Homeomorph.toOpenPartialHomeomorph_source _)

/-- The model level set, with the structure above, has the chart-transition groupoid. -/
theorem modelHasGroupoid (s : ModelSplit (a := m + 1) (k := k) v) :
    @HasGroupoid (EuclideanHalfSpace (m + 1)) _
      ↥(ModelLevelSet (a := m + 1) (k := k) v) _
      (modelChartedSpace (k := k) s)
      (contDiffGroupoid ∞ (modelWithCornersEuclideanHalfSpace (m + 1))) := by
  letI := modelChartedSpace (k := k) s
  exact (modelHomeo (k := k) s).toOpenPartialHomeomorph.singleton_hasGroupoid
    (Homeomorph.toOpenPartialHomeomorph_source _)
    (contDiffGroupoid ∞ (modelWithCornersEuclideanHalfSpace (m + 1)))

/-- The model level set, with the structure above, is a `C^∞` manifold with boundary. -/
theorem modelIsManifold (s : ModelSplit (a := m + 1) (k := k) v) :
    @IsManifold ℝ _ (Euc (m + 1)) _ _ (EuclideanHalfSpace (m + 1)) _
      (modelWithCornersEuclideanHalfSpace (m + 1)) ∞
      ↥(ModelLevelSet (a := m + 1) (k := k) v) _ (modelChartedSpace (k := k) s) := by
  letI := modelChartedSpace (k := k) s
  haveI := modelHasGroupoid (k := k) s
  exact IsManifold.mk' (modelWithCornersEuclideanHalfSpace (m + 1)) ∞
    ↥(ModelLevelSet (a := m + 1) (k := k) v)

/-- **The boundary of the model level set is `modelBdry`**: the `0`-th coordinate of the splitting
vanishes exactly on the hyperplane `x 0 = 0`. -/
theorem modelBdry_eq_boundary (s : ModelSplit (a := m + 1) (k := k) v) :
    @ModelWithCorners.boundary ℝ _ (Euc (m + 1)) _ _ (EuclideanHalfSpace (m + 1)) _
      (modelWithCornersEuclideanHalfSpace (m + 1))
      ↥(ModelLevelSet (a := m + 1) (k := k) v) _
      (modelChartedSpace (k := k) s)
      = modelBdry (k := k) s := by
  letI := modelChartedSpace (k := k) s
  haveI : IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) ∞
      ↥(ModelLevelSet (a := m + 1) (k := k) v) := modelIsManifold (k := k) s
  ext x
  rw [mem_modelBdry_iff]
  have he : chartAt (EuclideanHalfSpace (m + 1)) x
      ∈ IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace (m + 1)) ∞
          ↥(ModelLevelSet (a := m + 1) (k := k) v) :=
    IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ (chartAt (EuclideanHalfSpace (m + 1)) x).source := mem_chart_source _ x
  rw [Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
      (m := m + 1) he hx,
    OpenPartialHomeomorph.extend_coe, Function.comp_apply,
    OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq,
    modelWithCornersEuclideanHalfSpace_apply]
  show ((s.Φ.symm x.1).1) 0 = 0 ↔ (x.1 : Euc (m + 1 + k)) 0 = 0
  rw [← modelSplit_coord_zero_iff (s := s) (s.Φ.symm x.1), s.Φ.apply_symm_apply]

end

end Work.ThomBordism
