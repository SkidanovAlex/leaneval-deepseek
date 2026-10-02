import Mathlib
import Submission.Work.ThomBordism.Transversality.Pullback
import Submission.Work.ThomBordism.Transversality.Sard.Strat
import Submission.Work.Surgery.BoundaryInstances
import Submission.Work.ThomBordism.Transversality.Preimage.BoundaryCoord
import Submission.Work.ThomBordism.Transversality.Preimage.LinearAlg

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Setup for the transverse preimage

This file fixes the notation of the construction of the manifold structure on the transverse
preimage `F ⁻¹' X.core` of a smooth map `F : M → X.E` transverse to the core of a `CoreTarget`
`X : CoreTarget (9 + k) k`, with boundary transversality `hbnd`.  The hypotheses are bundled in the
structure `CoreSetup`.

Given such a setup, we choose once and for all, for every point `w` of the preimage, the submersion
normal form of `Φ ∘ F` at `w` (an open partial homeomorphism `domChartAt w` of `M` in the maximal
atlas and a linear equivalence `equivAt w` whose first component is the projection).  The level set
is then, in these coordinates, the affine subspace `{(equivAt w z).1 = c}`.
-/

open scoped Manifold Topology ContDiff
open Function Set Manifold
open ModelWithCorners

namespace Work.ThomBordism.Transversality.Preimage

noncomputable section

/-- **The data of the transverse-preimage construction**: a compact `T2` smooth manifold `M` with
boundary, a `CoreTarget X` of the same dimension `9 + k`, a smooth map `F : M → X.E` transverse to
the core of `X`, whose restriction to the boundary is a submersion along the zero set. -/
structure CoreSetup (k : ℕ) where
  /-- the target -/
  X : CoreTarget ((8 + k) + 1) k
  /-- the source -/
  M : Type
  [topologicalSpace : TopologicalSpace M]
  [chartedSpace : ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
  [isManifold : IsManifold (𝓡∂ ((8 + k) + 1)) smoothHeight M]
  [compactSpace : CompactSpace M]
  [t2Space : T2Space M]
  /-- the map -/
  F : M → X.E
  /-- smoothness of the map -/
  contMDiff : ContMDiff (𝓡∂ ((8 + k) + 1))
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin ((8 + k) + 1)))) smoothHeight F
  /-- transversality to the core -/
  isTransverse : IsTransverse X (𝓡∂ ((8 + k) + 1)) F
  /-- boundary transversality: the restriction of `Φ ∘ F` to `∂M` is a submersion along its
  zero set -/
  bndSubmersion : ∀ (x : M) (hx : x ∈ (𝓡∂ ((8 + k) + 1)).boundary M), X.Φ (F x) = 0 →
    IsSubmersionAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (8 + k)))) (𝓡 k) smoothHeight
      (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary M) => X.Φ (F (y : M))) ⟨x, hx⟩

attribute [instance] CoreSetup.topologicalSpace CoreSetup.chartedSpace CoreSetup.isManifold
  CoreSetup.compactSpace CoreSetup.t2Space

namespace CoreSetup

variable {k : ℕ} (S : CoreSetup k)

/-- The smooth map whose zero set is the transverse preimage of the core. -/
abbrev coreMap (x : S.M) : EuclideanSpace ℝ (Fin k) := S.X.Φ (S.F x)

/-- **The transverse preimage of the core**, as a subtype of `M`. -/
abbrev Pre : Type _ := ↥(S.F ⁻¹' S.X.core)

theorem zero_mem_coreMap (w : S.Pre) : S.coreMap w.1 = 0 := by
  exact w.2

theorem contMDiff_coreMap : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓡 k) smoothHeight S.coreMap :=
  S.X.contMDiff_Φ.comp S.contMDiff

theorem isSubmersionAt_coreMap (w : S.Pre) :
    IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓡 k) smoothHeight S.coreMap w.1 :=
  S.isTransverse w.1 trivial (S.zero_mem_coreMap w)

/-- The chosen complement of the model space in the normal form of `Φ ∘ F` at `w`. -/
noncomputable abbrev complType (w : S.Pre) : Type :=
  Classical.choose (S.isSubmersionAt_coreMap w)

noncomputable instance (w : S.Pre) : NormedAddCommGroup (S.complType w) :=
  Classical.choose (Classical.choose_spec (S.isSubmersionAt_coreMap w))

noncomputable instance (w : S.Pre) : NormedSpace ℝ (S.complType w) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (S.isSubmersionAt_coreMap w)))

/-- The submersion normal form of `Φ ∘ F` at `w`. -/
noncomputable abbrev normForm (w : S.Pre) :
    IsSubmersionAtOfComplement (S.complType w) (𝓡∂ ((8 + k) + 1)) (𝓡 k) smoothHeight
      S.coreMap w.1 :=
  Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (S.isSubmersionAt_coreMap w)))

/-- The domain chart of the normal form. -/
noncomputable abbrev domChartAt (w : S.Pre) :
    OpenPartialHomeomorph S.M (EuclideanHalfSpace ((8 + k) + 1)) :=
  (S.normForm w).domChart

/-- The codomain chart of the normal form. -/
noncomputable abbrev codChartAt (w : S.Pre) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k)) :=
  (S.normForm w).codChart

/-- The linear equivalence of the normal form. -/
noncomputable abbrev equivAt (w : S.Pre) :
    EuclideanSpace ℝ (Fin ((8 + k) + 1)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin k) × S.complType w) :=
  (S.normForm w).equiv

theorem mem_domChartAt_source (w : S.Pre) : w.1 ∈ (S.domChartAt w).source :=
  (S.normForm w).mem_domChart_source

theorem domChartAt_mem_maximalAtlas (w : S.Pre) :
    S.domChartAt w ∈ IsManifold.maximalAtlas (𝓡∂ ((8 + k) + 1)) smoothHeight S.M :=
  (S.normForm w).domChart_mem_maximalAtlas

theorem codChartAt_mem_maximalAtlas (w : S.Pre) :
    S.codChartAt w ∈ IsManifold.maximalAtlas (𝓡 k) smoothHeight
      (EuclideanSpace ℝ (Fin k)) :=
  (S.normForm w).codChart_mem_maximalAtlas

theorem domChartAt_source_subset (w : S.Pre) :
    (S.domChartAt w).source ⊆ S.coreMap ⁻¹' (S.codChartAt w).source :=
  (S.normForm w).source_subset_preimage_source

/-- **The normal form, read on the source**: on the source of the domain chart, the composite
`Φ ∘ F` is read by the first component of the linear equivalence. -/
theorem codChartAt_coreMap (w : S.Pre) {y : S.M} (hy : y ∈ (S.domChartAt w).source) :
    S.codChartAt w (S.coreMap y)
      = (S.equivAt w ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) y)).1 := by
  have hz : (S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) y
      ∈ ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1))).target :=
    PartialEquiv.map_source _ (by simpa using hy)
  have h := (S.normForm w).writtenInCharts hz
  have hinv : ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1))).symm
      ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) y) = y :=
    PartialEquiv.left_inv _
      (by simpa [OpenPartialHomeomorph.extend_source] using hy)
  rw [Function.comp_apply, Function.comp_apply, hinv] at h
  have h2 : (S.codChartAt w).extend (𝓡 k) (S.coreMap y) = S.codChartAt w (S.coreMap y) := by
    rw [OpenPartialHomeomorph.extend_coe]; rfl
  rw [h2] at h
  exact h

/-- **The level set in the normal-form coordinates.**  For `y` in the source of the domain chart
lying in the preimage of the core, the first component of the normal-form coordinates is the same
as at `w`: the preimage is the affine subspace `{z | (A z).1 = (A z₀).1}`. -/
theorem equivAt_fst_eq_of_mem_core (w : S.Pre) {y : S.M} (hy : y ∈ (S.domChartAt w).source)
    (hyW : y ∈ (S.F ⁻¹' S.X.core)) :
    (S.equivAt w ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) y)).1
      = (S.equivAt w ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) w.1)).1 := by
  rw [← codChartAt_coreMap S w hy, ← codChartAt_coreMap S w (mem_domChartAt_source S w)]
  have h1 : S.coreMap y = 0 := by simpa [coreMap, CoreTarget.mem_core] using hyW
  have h2 : S.coreMap w.1 = 0 := S.zero_mem_coreMap w
  rw [h1, h2]

end CoreSetup

end

end Work.ThomBordism.Transversality.Preimage
