import Submission.Work.PTGeometric.LocalLevel
import Submission.Work.ThomBordism.Transversality.Preimage.Setup
import Submission.Work.ThomBordism.Transversality.Preimage.KeyLemma

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The setup for the local level-set preimage theorem

This is the local analogue of `Work.ThomBordism.Transversality.Preimage.CoreSetup`: instead of a
single global defining function `Φ ∘ F` we have, at every point `w` of the closed subset `W`, a
*local* defining function `g w` which is a submersion at `w` and whose zero set on `U w` is exactly
`W`.

Everything downstream (`Lvl.KeyLemma`, `Lvl.Chart`, …) is the corresponding copy of the global
development with `coreMap` replaced by the point-dependent `localMap w`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter
open ModelWithCorners

namespace Work.PTGeometric

noncomputable section

namespace Lvl

/-- **The data of the local level-set construction**: a compact `T2` smooth manifold `M` with
boundary of dimension `(8 + k) + 1`, a closed subset `W`, and local level-set data for `W`. -/
structure Setup (k : ℕ) where
  /-- the source manifold -/
  M : Type
  [topologicalSpace : TopologicalSpace M]
  [chartedSpace : ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
  [isManifold : IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M]
  /-- the subset -/
  W : Set M
  [compactSpace : CompactSpace M]
  [t2Space : T2Space M]
  /-- the subset is closed (so that it is compact) -/
  isClosed_W : IsClosed W
  /-- the local level-set data -/
  data : LocalLevelData k M W

attribute [instance] Setup.topologicalSpace Setup.chartedSpace Setup.isManifold
  Setup.compactSpace Setup.t2Space

namespace Setup

variable {k : ℕ} (S : Setup k)

/-- The subset `W`, as a type. -/
abbrev Pre : Type _ := ↥S.W

/-- The local defining function at the point `w`. -/
abbrev localMap (w : S.Pre) : S.M → EuclideanSpace ℝ (Fin k) := S.data.g w

theorem localMap_self (w : S.Pre) : S.localMap w w.1 = 0 :=
  (S.data.zero_iff w w.1 (S.data.mem_U w)).mpr w.2

theorem contMDiff_localMap (w : S.Pre) :
    ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞ (S.localMap w) :=
  S.data.contMDiff_g w

theorem isSubmersionAt_localMap (w : S.Pre) :
    IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞ (S.localMap w) w.1 :=
  S.data.isSubmersion_g w

/-- **Witnesses for `w` lying in `W`.**  Since `w ∈ U w` and the zero set of `g w` on `U w` is
`W`, the local defining function vanishes at `w`. -/
theorem localMap_eq_zero_iff (w : S.Pre) {y : S.M} (hy : y ∈ S.data.U w) :
    S.localMap w y = 0 ↔ y ∈ S.W :=
  S.data.zero_iff w y hy

/-- The chosen complement of the model space in the normal form of `g w` at `w`. -/
noncomputable abbrev complType (w : S.Pre) : Type :=
  Classical.choose (S.isSubmersionAt_localMap w)

noncomputable instance (w : S.Pre) : NormedAddCommGroup (S.complType w) :=
  Classical.choose (Classical.choose_spec (S.isSubmersionAt_localMap w))

noncomputable instance (w : S.Pre) : NormedSpace ℝ (S.complType w) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (S.isSubmersionAt_localMap w)))

/-- The submersion normal form of `g w` at `w`. -/
noncomputable abbrev normForm (w : S.Pre) :
    IsSubmersionAtOfComplement (S.complType w) (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞
      (S.localMap w) w.1 :=
  Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (S.isSubmersionAt_localMap w)))

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
    S.domChartAt w ∈ IsManifold.maximalAtlas (𝓡∂ ((8 + k) + 1)) ∞ S.M :=
  (S.normForm w).domChart_mem_maximalAtlas

theorem codChartAt_mem_maximalAtlas (w : S.Pre) :
    S.codChartAt w ∈ IsManifold.maximalAtlas (𝓡 k) ∞
      (EuclideanSpace ℝ (Fin k)) :=
  (S.normForm w).codChart_mem_maximalAtlas

theorem domChartAt_source_subset (w : S.Pre) :
    (S.domChartAt w).source ⊆ S.localMap w ⁻¹' (S.codChartAt w).source :=
  (S.normForm w).source_subset_preimage_source

/-- **The normal form, read on the source**: on the source of the domain chart, the composite
`g w` is read by the first component of the linear equivalence. -/
theorem codChartAt_localMap (w : S.Pre) {y : S.M} (hy : y ∈ (S.domChartAt w).source) :
    S.codChartAt w (S.localMap w y)
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
  have h2 : (S.codChartAt w).extend (𝓡 k) (S.localMap w y) = S.codChartAt w (S.localMap w y) := by
    rw [OpenPartialHomeomorph.extend_coe]; rfl
  rw [h2] at h
  exact h

/-- **The level set in the normal-form coordinates.**  For `y ∈ U w` in the source of the domain
chart lying in `W`, the first component of the normal-form coordinates is the same as at `w`: the
level set is the affine subspace `{z | (A z).1 = (A z₀).1}`. -/
theorem equivAt_fst_eq_of_mem_core (w : S.Pre) {y : S.M} (hy : y ∈ (S.domChartAt w).source)
    (hyU : y ∈ S.data.U w) (hyW : y ∈ S.W) :
    (S.equivAt w ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) y)).1
      = (S.equivAt w ((S.domChartAt w).extend (𝓡∂ ((8 + k) + 1)) w.1)).1 := by
  rw [← codChartAt_localMap S w hy, ← codChartAt_localMap S w (mem_domChartAt_source S w)]
  have h1 : S.localMap w y = 0 := (S.localMap_eq_zero_iff w hyU).mpr hyW
  have h2 : S.localMap w w.1 = 0 := S.localMap_self w
  rw [h1, h2]

end Setup

end Lvl

end

end Work.PTGeometric
