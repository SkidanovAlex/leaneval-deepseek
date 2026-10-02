import Mathlib
import Submission.Work.Milnor.exists_capData_compact
import Submission.Work.Milnor.compactSpace_cappedSpace
import Submission.Work.Milnor.t2space_cappedSpace
import Submission.Work.Cohomology.cohomology_capped_compact
import Submission.Work.Milnor.homology_capped_compact
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.localCohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The closed `8`-manifold `X = D(ξ) ∪_F D⁸`

This file collects the construction of the *closed* `8`-manifold obtained by gluing the disc bundle
`ξ = Vk (-2)` to a disc along a diffeomorphism `F : Mk (-2) ≃ S⁷` of their common boundary
(`Submission/NOTES.md`, §9.3 and §9.8).  It is the manifold to which Hirzebruch's signature
theorem in dimension `8` is applied in the proof that `Mk (-2)` is an exotic `7`-sphere.

Given a capping diffeomorphism `F`, the *capping datum* is chosen once and for all by
`cappedDatum F hF`; its glued space is the closed manifold `X`.  The results collected here are

* `cappedDatum_spec` — the datum is a compact capping for (a choice of) `F` itself;
* `compactSpace_cappedSpace_datum`, `t2space_cappedSpace_datum`,
  `pathConnectedSpace_cappedSpace_datum` — `X` is a compact, Hausdorff, path connected space;
* `isManifold_cappedSpace_datum` — `X` is a smooth `8`-manifold (over the model
  `MSpace8 = ℝ⁴ × ℍ`, which is linearly isometric to `ℝ⁸`);
* `cohomology_cappedSpace_datum` — `H^n(X; ℤ) ≅ ℤ` for `n = 0, 4, 8` and `0` otherwise;
* `homology_capped_datum` — `H_n(X; ℤ) ≅ ℤ` for `n = 0, 4, 8` and `0` otherwise;
* `cappedChartedSpace`, `capped_isManifold` — the re-charting of `X` over `ℝ⁸`;
* `capped_localHomology`, `capped_localCohomology` — `H_8(X,X∖x) ≅ ℤ ≅ H^8(X,X∖x)`;
* `homeo_cappedSpace_mk` — the boundary sphere bundle `Mk (-2)` includes in `X` with
  `F` as the restriction to the glued collar.

The construction is the *inverting* one of `Submission/Work/Milnor/CapCompact.lean`: the collar
`{1/2 < ν} ⊆ Vk (-2)` is glued to the punctured space `ℝ⁸ ∖ {0}` by
`p ↦ (ν p - 1/2)⁻¹ • F(ψ p)`, so that the far end `ν → ∞` of the collar closes up at the origin of
`ℝ⁸` and the glued space is compact.  The corresponding statements for the *non-compact* gluing
of `Submission/Work/Milnor/exists_capData.lean` are `Work.Milnor.cohomology_capped` and
`Work.Milnor.exists_capData`.
-/

namespace Work.Milnor

open scoped Manifold ContDiff Topology
open Submission.Milnor TopologicalSpace

noncomputable section

/-- A chosen capping diffeomorphism of `Mk (-2)` with `S⁷`, from the predicate
`IsCappingDiffeo F`. -/
noncomputable def cappingDiffeo (F : Submission.Milnor.Mk (-2) → Sph8)
    (hF : IsCappingDiffeo F) : Diffeomorph mE4E3 mE7 (Submission.Milnor.Mk (-2)) Sph8 smLevel :=
  Classical.choose hF

theorem cappingDiffeo_apply (F : Submission.Milnor.Mk (-2) → Sph8) (hF : IsCappingDiffeo F) :
    ∀ q : Submission.Milnor.Mk (-2), cappingDiffeo F hF q = F q :=
  fun q => congrFun (Classical.choose_spec hF) q

instance nonempty_Vk (k : ℤ) : Nonempty (Vk k) :=
  ⟨mkToVkFun k (Classical.arbitrary (Mk k))⟩

/-- The glued space of a capping datum is charted on the common model `MSpace8 = ℝ⁴ × ℍ` (the
generic instance `Submission.Glue.Data.instChartedSpace` does not fire by type class search,
because the datum occurs in the goal only through `Data.Glued`). -/
instance instChartedSpace_cappedSpace (D : CapData) : ChartedSpace MSpace8 (cappedSpace D) :=
  Submission.Glue.Data.instChartedSpace D

/-- The glued space of a capping datum is a smooth manifold over `MSpace8`. -/
instance instIsManifold_cappedSpace (D : CapData) : IsManifold 𝓘(ℝ, MSpace8) ∞ (cappedSpace D) :=
  Work.Glue.glued_isManifold D

/-- **The capping datum**: the gluing data whose glued space is the closed `8`-manifold
`X = D(ξ) ∪_F D⁸`. -/
noncomputable def cappedDatum (F : Submission.Milnor.Mk (-2) → Sph8)
    (hF : IsCappingDiffeo F) : CapData :=
  (exists_capData_compact (cappingDiffeo F hF)).choose

theorem cappedDatum_spec (F : Submission.Milnor.Mk (-2) → Sph8) (hF : IsCappingDiffeo F) :
    IsCompactCapping (cappingDiffeo F hF) (cappedDatum F hF) :=
  (exists_capData_compact (cappingDiffeo F hF)).choose_spec

theorem cappedDatum_U (F : Submission.Milnor.Mk (-2) → Sph8) (hF : IsCappingDiffeo F) :
    (cappedDatum F hF).U = collar (-2) :=
  (cappedDatum_spec F hF).1

theorem cappedDatum_V (F : Submission.Milnor.Mk (-2) → Sph8) (hF : IsCappingDiffeo F) :
    (cappedDatum F hF).V = capPunct :=
  (cappedDatum_spec F hF).2.1

/-- **The closed `8`-manifold `X = D(ξ) ∪_F D⁸`.** -/
abbrev capped (F : Submission.Milnor.Mk (-2) → Sph8) (hF : IsCappingDiffeo F) : Type _ :=
  cappedSpace (cappedDatum F hF)

theorem isCompact_capped (F : Submission.Milnor.Mk (-2) → Sph8) (hF : IsCappingDiffeo F) :
    CompactSpace (capped F hF) :=
  compactSpace_cappedSpace (cappingDiffeo F hF) (cappedDatum F hF) (cappedDatum_spec F hF)

theorem isT2_capped (F : Submission.Milnor.Mk (-2) → Sph8) (hF : IsCappingDiffeo F) :
    T2Space (capped F hF) :=
  t2space_cappedSpace (cappingDiffeo F hF) (cappedDatum F hF) (cappedDatum_spec F hF)

theorem isPathConnected_capped (F : Submission.Milnor.Mk (-2) → Sph8) (hF : IsCappingDiffeo F) :
    PathConnectedSpace (capped F hF) :=
  capped_pathConnected (cappedDatum F hF) (cappedDatum_U F hF)

/-- `X = D(ξ) ∪_F D⁸` is a smooth `8`-manifold modelled on `MSpace8 = ℝ⁴ × ℍ`. -/
theorem isManifold_capped (F : Submission.Milnor.Mk (-2) → Sph8) (hF : IsCappingDiffeo F) :
    IsManifold 𝓘(ℝ, MSpace8) ∞ (capped F hF) :=
  instIsManifold_cappedSpace (cappedDatum F hF)

/-- The cohomology of `X = D(ξ) ∪_F D⁸`: `ℤ` in degrees `0`, `4`, `8` and zero otherwise. -/
theorem cohomology_capped_datum (F : Submission.Milnor.Mk (-2) → Sph8) (hF : IsCappingDiffeo F) :
    ∀ n : ℕ, Nonempty (Work.Cohomology.singularCohomology ℤ n (TopCat.of (capped F hF)) ≅
      ModuleCat.of ℤ (Fin ((if n = 0 then 1 else 0) + (if n = 4 then 1 else 0) +
        (if n = 8 then 1 else 0)) → ℤ)) := fun n =>
  Work.Cohomology.cohomology_capped_compact (cappedDatum F hF) (cappedDatum_U F hF) n

/-- The homology of `X = D(ξ) ∪_F D⁸`: `ℤ` in degrees `0`, `4`, `8` and zero otherwise. -/
theorem homology_capped_datum (F : Submission.Milnor.Mk (-2) → Sph8) (hF : IsCappingDiffeo F) :
    ∀ n : ℕ, Nonempty
      ((Work.Cohomology.singularChains ℤ (TopCat.of (capped F hF))).homology n ≅
        ModuleCat.of ℤ (Fin ((if n = 0 then 1 else 0) + (if n = 4 then 1 else 0) +
          (if n = 8 then 1 else 0)) → ℤ)) := fun n =>
  Work.Milnor.homology_capped_compact (cappedDatum F hF) (cappedDatum_U F hF) n

/-- The glued collar of the compact capping is the image of the sphere bundle, and the capping
diffeomorphism `F` is the map on directions. -/
theorem capped_direction (F : Submission.Milnor.Mk (-2) → Sph8) (hF : IsCappingDiffeo F)
    (q : Submission.Milnor.Mk (-2)) :
    ((cappedDatum F hF).φ (mkToVkFun (-2) q) : EuclideanSpace ℝ (Fin 8)) =
      (2 : ℝ) • (F q : EuclideanSpace ℝ (Fin 8)) := by
  have hmem : mkToVkFun (-2) q ∈ (cappedDatum F hF).U := by
    rw [cappedDatum_U F hF]
    exact mem_collar.mpr (one_lt_fibreNorm_mkToVkFun (-2) q)
  have hφ := (cappedDatum_spec F hF).2.2 ⟨mkToVkFun (-2) q, hmem⟩
  rw [hφ, capFunK_mkToVkFun,
    congrArg (fun z : Sph8 => (z : EuclideanSpace ℝ (Fin 8))) (cappingDiffeo_apply F hF q)]

/-! ## The closed manifold re-charted over `ℝ⁸`

Many results of the (co)homology chapter (local homology, the cohomology of spheres, degree theory)
are stated for manifolds charted on `EuclideanSpace ℝ (Fin n)`.  Here the `MSpace8`-charted
structure of the glued space is pushed forward along the linear isometry
`vkModelIso : MSpace8 ≃ ℝ⁸`, exactly as `Submission/Work/Milnor/MkCharted.lean` does for `Mk k`.
-/

/-- The charted space structure on `cappedSpace D` modelled on `ℝ⁸`: the atlas of the gluing,
pushed forward along `vkModelIso`. -/
@[instance_reducible] noncomputable def cappedChartedSpace (D : CapData) :
    ChartedSpace (EuclideanSpace ℝ (Fin 8)) (cappedSpace D) :=
  Work.Morse.pushChartedSpace (Work.Morse.modelHomeo 𝓘(ℝ, MSpace8) vkModelIso)

section Pushed

variable (D : CapData)
attribute [local instance] cappedChartedSpace

/-- `X`, with the pushed-forward atlas onto `ℝ⁸`, is a smooth `8`-manifold. -/
theorem capped_isManifold : IsManifold (𝓡 8) ∞ (cappedSpace D) :=
  Work.Morse.push_isManifold (M := cappedSpace D) (I := 𝓘(ℝ, MSpace8)) vkModelIso

attribute [local instance] capped_isManifold

/-- Smoothness of a real function on `X` is the same in the two charted structures. -/
theorem capped_contMDiff_iff {f : cappedSpace D → ℝ} :
    ContMDiff (𝓡 8) 𝓘(ℝ, ℝ) ∞ f ↔ ContMDiff 𝓘(ℝ, MSpace8) 𝓘(ℝ, ℝ) ∞ f :=
  Work.Morse.contMDiff_push (M := cappedSpace D) (I := 𝓘(ℝ, MSpace8))
    (E' := EuclideanSpace ℝ (Fin 8)) vkModelIso f

/-- The manifold derivative of a real function on `X` in the `ℝ⁸` structure, in terms of the
derivative in the `MSpace8` structure. -/
theorem capped_mfderiv (f : cappedSpace D → ℝ) (x : cappedSpace D) :
    mfderiv (𝓡 8) 𝓘(ℝ, ℝ) f x
      = (mfderiv 𝓘(ℝ, MSpace8) 𝓘(ℝ, ℝ) f x).comp
          (vkModelIso.symm : EuclideanSpace ℝ (Fin 8) →L[ℝ] MSpace8) :=
  Work.Morse.mfderiv_push (M := cappedSpace D) (I := 𝓘(ℝ, MSpace8))
    (E' := EuclideanSpace ℝ (Fin 8)) vkModelIso f x

end Pushed

/-! ## Local (co)homology of `X`

At every point `x` of the closed `8`-manifold `X` the local homology `H_8(X, X ∖ {x})` and the
local cohomology `H^8(X, X ∖ {x})` are `ℤ`: this is the input for the orientation/fundamental
class chapter (see `Submission/NOTES.md` §10.6). -/

/-- The local homology of `X` at any point is `ℤ`. -/
theorem capped_localHomology (D : CapData) (x : cappedSpace D) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 8)) (cappedSpace D) := cappedChartedSpace D
    Nonempty (((Work.Cohomology.relChains (TopCat.of (cappedSpace D)) {y | y ≠ x}).homology 8) ≅
      ModuleCat.of ℤ ℤ) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 8)) (cappedSpace D) := cappedChartedSpace D
  exact Work.Cohomology.localHomology 8 (by norm_num) (cappedSpace D) x

/-- The local cohomology of `X` at any point is `ℤ`. -/
theorem capped_localCohomology (D : CapData) (x : cappedSpace D) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 8)) (cappedSpace D) := cappedChartedSpace D
    Nonempty (((Work.Cohomology.relComplex ℤ (TopCat.of (cappedSpace D)) {y | y ≠ x}).homology 8) ≅
      ModuleCat.of ℤ ℤ) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 8)) (cappedSpace D) := cappedChartedSpace D
  exact Work.Cohomology.localCohomology 8 (by norm_num) (cappedSpace D) x

end

end Work.Milnor
