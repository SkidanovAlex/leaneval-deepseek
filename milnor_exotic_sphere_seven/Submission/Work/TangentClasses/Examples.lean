import Mathlib
import Submission.Work.TangentClasses.Tangent
import Submission.Work.Milnor.CappedManifold
import Submission.Work.Milnor.MkCharted

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

/-!
# The tangent bundle of the manifolds of this workspace

`Submission/Work/TangentClasses/Tangent.lean` defines the tangent bundle `tangentBundle I M` of a
smooth manifold as gluing data (transition functions = Jacobians of the chart transitions, i.e.
Mathlib's `tangentBundleCore`).  This module records that the construction applies to every manifold
of this workspace, with its rank:

* `Submission.Milnor.Mk k` — Milnor's `M_k`, in the explicit `ℝ⁷` charting of
  `Submission/Work/Milnor/MkCharted.lean` (`tangentMkR7`, rank `7`) and in the product charting
  (`tangentMk`, rank `7`);
* `Submission.Milnor.Vk k` — the disc bundle of `ξ`, the total space of the rank-`4` bundle over
  `S⁴` (`tangentVk`, rank `8`, model `MSpace8 = ℝ⁴ × ℍ`);
* `Work.Milnor.cappedSpace D` — the closed `8`-manifold `X = D(ξ) ∪_F D⁸`, in the `ℝ⁸` charting of
  `Submission/Work/Milnor/CappedManifold.lean` (`tangentCappedR8`, rank `8`) and in the `MSpace8`
  charting used for the cohomology computations (`tangentCapped`, rank `8`);
* the spheres `Sph3 = S³` and `Sph8 = S⁷` (Mathlib's `Metric.sphere`);
* products `M × N`.

All of these are *instances of the same general construction*, and each carries the Mathlib bundle
API (`VectorBundle ℝ E (TangentBundle I M)`, trivialisations, `ContMDiffVectorBundle`), so a caller
can state identifications such as "the tangent bundle of the disc bundle splits as
`π^*(TS⁴ ⊕ ξ)`" in the language of `Submission/Work/TangentClasses/Bundle.lean`.

The normed structure on the product model `ModelProd E E'` (which Mathlib provides only
topologically, cf. `ModelProd`) is registered in
`Submission/Work/TangentClasses/Tangent.lean`, since the tangent bundle of a product-charted
manifold needs its model space to be a normed space.
-/

namespace Work.TangentClasses

open Bundle
open scoped Manifold ContDiff
open RealBundle

noncomputable section

/-! ## Milnor's `M_k` -/

/-- The model of the product charting of `Mk k`. -/
abbrev MkModel : Type := ModelProd (EuclideanSpace ℝ (Fin 4)) (EuclideanSpace ℝ (Fin 3))

section MkProduct

variable (k : ℤ)

/-- **The tangent bundle of Milnor's `M_k`**, in the product charting. -/
abbrev tangentMk : RealBundle (Submission.Milnor.Mk k) MkModel
    (atlas MkModel (Submission.Milnor.Mk k)) :=
  tangentBundle ((𝓡 4).prod (𝓡 3)) (Submission.Milnor.Mk k)

/-- `T M_k` has rank `7`. -/
theorem tangentMk_rank : (tangentMk k).rank = 7 := by
  rw [rank]
  change Module.finrank ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)) = 7
  rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]

end MkProduct

section MkR7

attribute [local instance] Work.Milnor.mkChartedSpace Work.Milnor.mk_isManifold

variable (k : ℤ)

/-- **The tangent bundle of `M_k`** in the explicit `ℝ⁷` charting of
`Submission/Work/Milnor/MkCharted.lean`. -/
noncomputable def tangentMkR7 : RealBundle (Submission.Milnor.Mk k)
    (EuclideanSpace ℝ (Fin 7)) (atlas (EuclideanSpace ℝ (Fin 7)) (Submission.Milnor.Mk k)) :=
  tangentBundle (𝓡 7) (Submission.Milnor.Mk k)

/-- `T M_k` has rank `7`, in the `ℝ⁷` charting. -/
theorem tangentMkR7_rank : (tangentMkR7 k).rank = 7 := by
  rw [rank, finrank_euclideanSpace_fin]

end MkR7

/-! ## The disc bundle `Vk k` -/

section Vk

variable (k : ℤ)

/-- **The tangent bundle of the disc bundle `D(ξ) = Vk k`** of Milnor's bundle. -/
abbrev tangentVk : RealBundle (Submission.Milnor.Vk k) Submission.Milnor.MSpace8
    (atlas Submission.Milnor.MSpace8 (Submission.Milnor.Vk k)) :=
  tangentBundle 𝓘(ℝ, Submission.Milnor.MSpace8) (Submission.Milnor.Vk k)

/-- `T D(ξ)` has rank `8`: the disc bundle is an `8`-manifold. -/
theorem tangentVk_rank : (tangentVk k).rank = 8 := by
  rw [rank, Module.finrank_prod, finrank_euclideanSpace_fin, Quaternion.finrank_eq_four]

end Vk

/-! ## The capped manifold `X = D(ξ) ∪_F D⁸` -/

section Capped

variable (D : Work.Milnor.CapData)

/-- **The tangent bundle of the closed `8`-manifold `X = D(ξ) ∪_F D⁸`**, in the `MSpace8`
charting used for the cohomology computations. -/
abbrev tangentCapped : RealBundle (Work.Milnor.cappedSpace D) Submission.Milnor.MSpace8
    (atlas Submission.Milnor.MSpace8 (Work.Milnor.cappedSpace D)) :=
  tangentBundle 𝓘(ℝ, Submission.Milnor.MSpace8) (Work.Milnor.cappedSpace D)

/-- `T X` has rank `8`. -/
theorem tangentCapped_rank : (tangentCapped D).rank = 8 := by
  rw [rank, Module.finrank_prod, finrank_euclideanSpace_fin, Quaternion.finrank_eq_four]

end Capped

section CappedR8

attribute [local instance] Work.Milnor.cappedChartedSpace Work.Milnor.capped_isManifold

variable (D : Work.Milnor.CapData)

/-- **The tangent bundle of `X`** in the `ℝ⁸` charting of
`Submission/Work/Milnor/CappedManifold.lean`. -/
noncomputable def tangentCappedR8 :
    RealBundle (Work.Milnor.cappedSpace D) (EuclideanSpace ℝ (Fin 8))
      (atlas (EuclideanSpace ℝ (Fin 8)) (Work.Milnor.cappedSpace D)) :=
  tangentBundle (𝓡 8) (Work.Milnor.cappedSpace D)

/-- `T X` has rank `8`, in the `ℝ⁸` charting. -/
theorem tangentCappedR8_rank : (tangentCappedR8 D).rank = 8 := by
  rw [rank, finrank_euclideanSpace_fin]

end CappedR8

/-! ## Spheres -/

section Sphere

variable (n : ℕ)

/-- **The tangent bundle of the sphere `S^n ⊆ ℝ^{n+1}`** (Mathlib's `Metric.sphere`), in the
standard charting by `ℝ^n`. -/
abbrev tangentSphere :
    RealBundle (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
      (EuclideanSpace ℝ (Fin n)) (atlas (EuclideanSpace ℝ (Fin n))
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :=
  tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- `T S^n` has rank `n`. -/
theorem tangentSphere_rank : (tangentSphere n).rank = n := by
  rw [rank, finrank_euclideanSpace_fin]

end Sphere

/-- The tangent bundle of `S³` (the fibre of Milnor's bundles), in the charting by `ℝ³`. -/
abbrev tangentSph3 : RealBundle (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (EuclideanSpace ℝ (Fin 3))
    (atlas (EuclideanSpace ℝ (Fin 3)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) :=
  tangentSphere 3

/-- The tangent bundle of `S⁷` (the boundary sphere of the capping disc), in the charting by `ℝ⁷`. -/
abbrev tangentSph8 : RealBundle (Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1)
    (EuclideanSpace ℝ (Fin 7))
    (atlas (EuclideanSpace ℝ (Fin 7)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1)) :=
  tangentSphere 7

/-! ## Products -/

section Prod

variable {E H E' H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']

/-- **The tangent bundle of a product**, as gluing data over the product model.  (The Jacobian
computation identifying it with `TM ⊕ TN` is
`Submission/Work/TangentClasses/ProdCoord.lean`.) -/
abbrev tangentProd (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (N : Type*) [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N] :
    RealBundle (M × N) (ModelProd E E') (atlas (ModelProd H H') (M × N)) :=
  tangentBundle (I.prod I') (M × N)

/-- The rank of the tangent bundle of a product is the sum of the ranks. -/
theorem tangentProd_rank [Module.Finite ℝ E] [Module.Finite ℝ E']
    (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (N : Type*) [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N] :
    (tangentProd I I' M N).rank = Module.finrank ℝ E + Module.finrank ℝ E' := by
  rw [rank]
  change Module.finrank ℝ (E × E') = Module.finrank ℝ E + Module.finrank ℝ E'
  rw [Module.finrank_prod]

end Prod

/-! ## The model space (the chart; the open disc) -/

section Model

variable (n : ℕ)

/-- **The tangent bundle of the model space `ℝ^n`** — the chart of every manifold of this
workspace, diffeomorphic to the open disc `D^n` (so this is "the tangent bundle of a disc").  All
of its transition functions are the identity: `tangentModel_coordChange`. -/
abbrev tangentModel : RealBundle (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))
    (atlas (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))) :=
  tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))

/-- `T ℝ^n` has rank `n`. -/
theorem tangentModel_rank : (tangentModel n).rank = n := by
  rw [rank, finrank_euclideanSpace_fin]

/-- The tangent bundle of the model space is trivial: all transition functions are the identity. -/
theorem tangentModel_coordChange (x x' z : EuclideanSpace ℝ (Fin n)) :
    (tangentModel n).coordChange (achart (EuclideanSpace ℝ (Fin n)) x)
      (achart (EuclideanSpace ℝ (Fin n)) x') z = 1 :=
  tangentBundle_model_coordChange x x' z

end Model

end

end Work.TangentClasses
