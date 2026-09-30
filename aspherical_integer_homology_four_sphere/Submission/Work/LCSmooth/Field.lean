/-
# Area `LCSmooth`: the curvature field and the assembly of `Work.Final.FinalInputs`

With the smoothness of the Levi-Civita connection available as an *instance*
(`Submission/Work/LCSmooth/Mhat.lean`), two of the remaining steps of the final assembly of the
challenge theorem become pure plumbing that this file performs once and for all:

* the **curvature field** of `Work.Final.FinalInputs`,
  `∀ K > 0, Submission.RauchK.CurvLe (mhatCov) K`, is produced from the chart-model datum of the
  atlas of `M̂` by `Work.Final.curvLe_of_models` (the curvature bridge of the areas `Space`,
  `Curvature`, `LeviCivita` and `Final`), whose instance argument — the smoothness of `mhatCov` —
  is exactly what this area supplies.  The alternative route through the *pointwise* form
  `sec ≤ 0` is `Work.LCSmooth.curvLe_of_secNonpos_mhat`
  (`Work.CartanHadamard.curvLe_all`, whose instance argument is again this area's);

* the curvature datum itself is reduced to a *sign*: `Work.LCSmooth.hmodels_of_model_secNonpos`
  turns `∀ G ∈ rt.models.models, ∀ x, SecNonposAt G ((extChartAt I4 x) x)` — a sign on the models of
  the atlas, at the points where they are used, which is what the delivered model computations
  `Work.Curvature.secNonposAt_uhs/warped/flat` provide — into the datum `hmodels`, and
  `Work.LCSmooth.hmodels_of_field_secNonpos` does the same for the per-model-field form
  (`rt.models.models = Set.range rt.models.field`, `Work.LCSmooth.models_eq_range_field`);

* the **full `FinalInputs`** is assembled from the still-owed data
  (`Work.LCSmooth.finalInputsOfCurvLe`, `…OfModels`, `…OfSecNonpos`, `…OfModelsAndMV`,
  `…OfCurvLeAndMV`, `…OfModelSecNonpos`), and composed with the delivered chain
  `Work.Final.aspherical_integer_homology_four_sphere` to give the challenge statement
  (`Work.LCSmooth.aspherical_integer_homology_four_sphere_of_data` and its variants).

Nothing in this file is a hypothesis *about* `LCSmooth`: after `import Submission.Work.LCSmooth.All`
the only remaining inputs of the challenge theorem are the two data items owned by other areas —
the sign of the chart models of the atlas `M̂` (`Work.Curvature.secNonposAt_uhs/warped/flat` for
the three documented metrics, which is the "model curvature" datum of `NOTES_FINAL.md` §5) and the
three homology identifications `eM`, `eN`, `hsq` (the fields `L` and `hX` are constructed here, in
`Submission/Work/LCSmooth/MhatMV.lean`).
-/
import Submission.Work.LCSmooth.Mhat
import Submission.Work.LCSmooth.MhatMV

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false
set_option maxHeartbeats 400000

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open CategoryTheory
open LeanEval.Topology

namespace Work.LCSmooth

noncomputable section

section Curvature

variable [rt : Work.Space.RTData]

/-- **The curvature field of `FinalInputs`, from the chart-model datum.**  `hmodels` is the datum
produced by the provider of `Work.Space.RTData` (see `NOTES_FINAL.md` §5): for every point of `M̂`
a chart model of the atlas which agrees with the chart metric near the chart image of the point
and has non-positive sectional curvature there.  The conclusion is the field `curvLe` of
`Work.Final.FinalInputs`.

The instance argument of `Work.Final.curvLe_of_models` (the smoothness of `mhatCov`) is supplied
here by `Work.LCSmooth.instContMDiffCovariantDerivativeMhatCov`. -/
theorem curvLe_of_models_mhat
    (hmodels : ∀ x : rt.Mhat, ∃ G ∈ rt.models.models,
      Work.Curvature.SecNonposAt G ((extChartAt Work.Space.I4 x) x) ∧
      Filter.Eventually (fun q => ∀ a b : Work.Space.E4,
          Submission.ChartConnection.chartGram (I := Work.Space.I4) x
            ((extChartAt Work.Space.I4 x).symm q) a b = G q a b)
        (nhds ((extChartAt Work.Space.I4 x) x))) :
    ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe (Work.Final.mhatCov (rt := rt)) K :=
  Work.Final.curvLe_of_models (rt := rt) hmodels

/-- **The curvature field of `FinalInputs`, from the pointwise `sec ≤ 0` form.**  This is the
fallback route of `Work.Final.FinalInputs.ofSecNonpos`: the pointwise non-positivity of the
sectional-curvature numerator, turned into the parametric bound `∀ K > 0, CurvLe (mhatCov) K` by
`Work.CartanHadamard.curvLe_all` — whose instance argument, the smoothness of `mhatCov`, is again
supplied by this area. -/
theorem curvLe_of_secNonpos_mhat
    (hsec : ∀ x : rt.Mhat, ∀ u v : TangentSpace Work.Space.I4 x,
      ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
        inner ℝ (Submission.CurvatureVec.curvVec (Work.Final.mhatCov (rt := rt)) x u v v) u ≤ 0) :
    ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe (Work.Final.mhatCov (rt := rt)) K :=
  Work.CartanHadamard.curvLe_all (cov := Work.Final.mhatCov (rt := rt)) hsec

/-- The model set of the atlas of `M̂` is the range of its model field
(`Work.Space.ModelAtlas.models`), by definition. -/
theorem models_eq_range_field [rt : Work.Space.RTData] :
    rt.models.models = Set.range rt.models.field := rfl

/-- **The chart-model curvature datum from a curvature sign at the points where the models are
used.**

The hypothesis of `Work.LCSmooth.curvLe_of_models_mhat` (and of `Work.Final.curvLe_of_models`) is a
per-point existential: at every `x : M̂` some model of the atlas agrees with the chart metric near
the chart image of `x` and is non-positively curved *there*.  The agreement clause is
`Work.Space.RTData.chartGram_is_model`, which is delivered by the area `Space` and needs no
hypothesis at all; what a provider of `Work.Space.RTData` has to supply is only the *sign*.

This lemma isolates exactly that: it suffices to know the sign of each model of the atlas **at the
chart images of the points where that chart is used**,

    ∀ G ∈ rt.models.models, ∀ x : rt.Mhat, Work.Curvature.SecNonposAt G ((extChartAt I4 x) x).

This is the form in which the model computations of `Work.Curvature` are available: for the
upper-half-space model `Work.Curvature.secNonposAt_uhs` needs `0 < q 3`, i.e. it is a statement
about the points of the upper half space — which is precisely where the chart images of an
upper-half-space chart lie — while for the flat and warped models
(`Work.Curvature.secNonposAt_flat`, `secNonposAt_warped`) the sign holds at every point.  Compare
`Work.LCSmooth.hmodels_of_atlas_secNonpos` for the (strictly stronger) global form. -/
theorem hmodels_of_model_secNonpos [rt : Work.Space.RTData]
    (h : ∀ G ∈ rt.models.models, ∀ x : rt.Mhat,
      Work.Curvature.SecNonposAt G ((extChartAt Work.Space.I4 x) x)) :
    ∀ x : rt.Mhat, ∃ G ∈ rt.models.models,
      Work.Curvature.SecNonposAt G ((extChartAt Work.Space.I4 x) x) ∧
      Filter.Eventually (fun q => ∀ a b : Work.Space.E4,
          Submission.ChartConnection.chartGram (I := Work.Space.I4) x
            ((extChartAt Work.Space.I4 x).symm q) a b = G q a b)
        (nhds ((extChartAt Work.Space.I4 x) x)) := by
  intro x
  obtain ⟨G, hG, hev⟩ := Work.Space.RTData.chartGram_is_model (D := rt) x
  exact ⟨G, hG, h G hG x, hev⟩

/-- **The chart-model curvature datum from a per-model-field sign** — the form closest to what a
provider of `Work.Space.RTData` proves: since `rt.models.models = Set.range rt.models.field`
(`Work.LCSmooth.models_eq_range_field`), the sign on the field, at the chart images of the points
where the charts are used,

    ∀ i : Fin rt.models.n, ∀ x : rt.Mhat, SecNonposAt (rt.models.field i) ((extChartAt I4 x) x),

gives the datum.  (For the three documented models this is a `fin_cases` check against
`Work.Curvature.secNonposAt_uhs/warped/flat`.) -/
theorem hmodels_of_field_secNonpos [rt : Work.Space.RTData]
    (h : ∀ i : Fin rt.models.n, ∀ x : rt.Mhat,
      Work.Curvature.SecNonposAt (rt.models.field i) ((extChartAt Work.Space.I4 x) x)) :
    ∀ x : rt.Mhat, ∃ G ∈ rt.models.models,
      Work.Curvature.SecNonposAt G ((extChartAt Work.Space.I4 x) x) ∧
      Filter.Eventually (fun q => ∀ a b : Work.Space.E4,
          Submission.ChartConnection.chartGram (I := Work.Space.I4) x
            ((extChartAt Work.Space.I4 x).symm q) a b = G q a b)
        (nhds ((extChartAt Work.Space.I4 x) x)) :=
  hmodels_of_model_secNonpos (fun G hG => by
    obtain ⟨i, rfl⟩ := hG
    exact h i)

/-- **The chart-model curvature datum from a *global* sign on the models.**  This is a genuine
strengthening of `Work.LCSmooth.hmodels_of_model_secNonpos`: the sign is required at *every* point
of the model space rather than at the chart images.  It is available for the flat and warped
models at every point, and for the upper-half-space model only on `0 < q 3`
(`Work.Curvature.secNonposAt_uhs`), so a provider should use the pointwise form above. -/
theorem hmodels_of_atlas_secNonpos [rt : Work.Space.RTData]
    (h : ∀ G ∈ rt.models.models, ∀ q : Work.Space.E4, Work.Curvature.SecNonposAt G q) :
    ∀ x : rt.Mhat, ∃ G ∈ rt.models.models,
      Work.Curvature.SecNonposAt G ((extChartAt Work.Space.I4 x) x) ∧
      Filter.Eventually (fun q => ∀ a b : Work.Space.E4,
          Submission.ChartConnection.chartGram (I := Work.Space.I4) x
            ((extChartAt Work.Space.I4 x).symm q) a b = G q a b)
        (nhds ((extChartAt Work.Space.I4 x) x)) :=
  hmodels_of_model_secNonpos fun G hG x => h G hG _

/-- **The curvature field of `FinalInputs`, from a sign on each model of the atlas** (see
`Work.LCSmooth.hmodels_of_model_secNonpos`).  The conclusion is the field `curvLe` of
`Work.Final.FinalInputs`. -/
theorem curvLe_of_model_secNonpos [rt : Work.Space.RTData]
    (h : ∀ G ∈ rt.models.models, ∀ x : rt.Mhat,
      Work.Curvature.SecNonposAt G ((extChartAt Work.Space.I4 x) x)) :
    ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe (Work.Final.mhatCov (rt := rt)) K :=
  curvLe_of_models_mhat (hmodels_of_model_secNonpos h)

end Curvature

section Assembly

variable [rt : Work.Space.RTData]

/-- **`Work.Final.FinalInputs` assembled from the remaining data, with `cov_smooth` supplied by
this area.**

The six arguments are exactly the data still owed by the areas `Curvature` (through
`curvLe`, e.g. from the chart-model datum via `Work.LCSmooth.curvLe_of_models_mhat`) and
`DeltaHomology`/`Certificates` (`L`, `eM`, `eN`, `hsq`, `hX`); the fields `rt` and `cov_smooth`
are filled here (`cov_smooth` by `Work.LCSmooth.cov_smooth`), and the field `L` and `hX` may also
be taken from the *constructed* `Work.Final.FinalInputs.mhatLES` / `mhatLES_hX`. -/
noncomputable def finalInputsOfCurvLe
    (curvLe : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe (Work.Final.mhatCov (rt := rt)) K)
    (L : Work.HomologyMV.MVLES)
    (eM : ∀ k : ℤ, Work.HomologyMV.ModelM k ≅ L.H (k, 0))
    (eN : ∀ k : ℤ, Work.HomologyMV.ModelN k ≅ L.H (k, 1))
    (hsq : ∀ k : ℤ, (eM k).hom ≫ L.d (k, 0) = Work.HomologyMV.wConcrete k ≫ (eN k).hom)
    (hX : ∀ k : ℕ, L.H ((k : ℤ), 2) ≅
      LeanEval.Topology.intHomology k (TopCat.of rt.Mhat)) :
    Work.Final.FinalInputs where
  rt := rt
  cov_smooth := Work.LCSmooth.cov_smooth
  curvLe := curvLe
  L := L
  eM := eM
  eN := eN
  hsq := hsq
  hX := hX

/-- **`Work.Final.FinalInputs` assembled from the chart-model curvature datum** and the homology
data: `curvLe` is `Work.LCSmooth.curvLe_of_models_mhat hmodels` and `cov_smooth` is this area's
theorem. -/
noncomputable def finalInputsOfModels
    (hmodels : ∀ x : rt.Mhat, ∃ G ∈ rt.models.models,
      Work.Curvature.SecNonposAt G ((extChartAt Work.Space.I4 x) x) ∧
      Filter.Eventually (fun q => ∀ a b : Work.Space.E4,
          Submission.ChartConnection.chartGram (I := Work.Space.I4) x
            ((extChartAt Work.Space.I4 x).symm q) a b = G q a b)
        (nhds ((extChartAt Work.Space.I4 x) x)))
    (L : Work.HomologyMV.MVLES)
    (eM : ∀ k : ℤ, Work.HomologyMV.ModelM k ≅ L.H (k, 0))
    (eN : ∀ k : ℤ, Work.HomologyMV.ModelN k ≅ L.H (k, 1))
    (hsq : ∀ k : ℤ, (eM k).hom ≫ L.d (k, 0) = Work.HomologyMV.wConcrete k ≫ (eN k).hom)
    (hX : ∀ k : ℕ, L.H ((k : ℤ), 2) ≅
      LeanEval.Topology.intHomology k (TopCat.of rt.Mhat)) :
    Work.Final.FinalInputs :=
  finalInputsOfCurvLe (curvLe := curvLe_of_models_mhat hmodels) L eM eN hsq hX

/-- **`Work.Final.FinalInputs` assembled from the pointwise `sec ≤ 0` datum** and the homology
data (the `Work.Final.FinalInputs.ofSecNonpos` route). -/
noncomputable def finalInputsOfSecNonpos
    (hsec : ∀ x : rt.Mhat, ∀ u v : TangentSpace Work.Space.I4 x,
      ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
        inner ℝ (Submission.CurvatureVec.curvVec (Work.Final.mhatCov (rt := rt)) x u v v) u ≤ 0)
    (L : Work.HomologyMV.MVLES)
    (eM : ∀ k : ℤ, Work.HomologyMV.ModelM k ≅ L.H (k, 0))
    (eN : ∀ k : ℤ, Work.HomologyMV.ModelN k ≅ L.H (k, 1))
    (hsq : ∀ k : ℤ, (eM k).hom ≫ L.d (k, 0) = Work.HomologyMV.wConcrete k ≫ (eN k).hom)
    (hX : ∀ k : ℕ, L.H ((k : ℤ), 2) ≅
      LeanEval.Topology.intHomology k (TopCat.of rt.Mhat)) :
    Work.Final.FinalInputs :=
  finalInputsOfCurvLe (curvLe := curvLe_of_secNonpos_mhat hsec) L eM eN hsq hX

/-- **`Work.Final.FinalInputs` assembled with `L` and `hX` filled in by the constructed
Mayer–Vietoris sequence of `M̂`** (`Work.LCSmooth.mhatLES`, `Work.LCSmooth.mhatLES_hX`), and
`cov_smooth` by this area's theorem.

After this, the only inputs of `Work.Final.FinalInputs` that remain are the curvature datum
`hmodels` (owner: the `Work.Space.RTData` provider, see `NOTES_FINAL.md` §5) and the three
homology identifications `eM`, `eN`, `hsq` (owners: DELTAHOMOLOGY + CERTIFICATES). -/
noncomputable def finalInputsOfModelsAndMV
    (hmodels : ∀ x : rt.Mhat, ∃ G ∈ rt.models.models,
      Work.Curvature.SecNonposAt G ((extChartAt Work.Space.I4 x) x) ∧
      Filter.Eventually (fun q => ∀ a b : Work.Space.E4,
          Submission.ChartConnection.chartGram (I := Work.Space.I4) x
            ((extChartAt Work.Space.I4 x).symm q) a b = G q a b)
        (nhds ((extChartAt Work.Space.I4 x) x)))
    (eM : ∀ k : ℤ, Work.HomologyMV.ModelM k ≅ (mhatLES (rt := rt)).H (k, 0))
    (eN : ∀ k : ℤ, Work.HomologyMV.ModelN k ≅ (mhatLES (rt := rt)).H (k, 1))
    (hsq : ∀ k : ℤ, (eM k).hom ≫ (mhatLES (rt := rt)).d (k, 0)
      = Work.HomologyMV.wConcrete k ≫ (eN k).hom) :
    Work.Final.FinalInputs :=
  finalInputsOfModels hmodels (mhatLES (rt := rt)) eM eN hsq (mhatLES_hX (rt := rt))

/-- The same, with the curvature input given as a parametric bound `curvLe` rather than as the
chart-model datum. -/
noncomputable def finalInputsOfCurvLeAndMV
    (curvLe : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe (Work.Final.mhatCov (rt := rt)) K)
    (eM : ∀ k : ℤ, Work.HomologyMV.ModelM k ≅ (mhatLES (rt := rt)).H (k, 0))
    (eN : ∀ k : ℤ, Work.HomologyMV.ModelN k ≅ (mhatLES (rt := rt)).H (k, 1))
    (hsq : ∀ k : ℤ, (eM k).hom ≫ (mhatLES (rt := rt)).d (k, 0)
      = Work.HomologyMV.wConcrete k ≫ (eN k).hom) :
    Work.Final.FinalInputs :=
  finalInputsOfCurvLe curvLe (mhatLES (rt := rt)) eM eN hsq (mhatLES_hX (rt := rt))

/-- **`Work.Final.FinalInputs` assembled from a sign on each model of the atlas and the homology
identifications** — the strongest form of the assembler: the fields `rt`, `cov_smooth`, `L` and
`hX` are all produced here, and the curvature input is the sign of the models at the chart images
(see `Work.LCSmooth.hmodels_of_model_secNonpos`). -/
noncomputable def finalInputsOfModelSecNonpos
    (h : ∀ G ∈ rt.models.models, ∀ x : rt.Mhat,
      Work.Curvature.SecNonposAt G ((extChartAt Work.Space.I4 x) x))
    (eM : ∀ k : ℤ, Work.HomologyMV.ModelM k ≅ (mhatLES (rt := rt)).H (k, 0))
    (eN : ∀ k : ℤ, Work.HomologyMV.ModelN k ≅ (mhatLES (rt := rt)).H (k, 1))
    (hsq : ∀ k : ℤ, (eM k).hom ≫ (mhatLES (rt := rt)).d (k, 0)
      = Work.HomologyMV.wConcrete k ≫ (eN k).hom) :
    Work.Final.FinalInputs :=
  finalInputsOfModelsAndMV (hmodels_of_model_secNonpos h) eM eN hsq

end Assembly

section Main

variable [rt : Work.Space.RTData]

/-- **The challenge theorem, from the chart-model curvature datum and the homology data.**

This is `Work.Final.aspherical_integer_homology_four_sphere` fed with the `FinalInputs` assembled
by this area: it exhibits a closed aspherical integer homology 4-sphere, and the *only* inputs are
`hmodels` (the chart models of the atlas of `M̂` and their non-positive curvature — see
`NOTES_FINAL.md` §5) and the Mayer–Vietoris data `L`, `eM`, `eN`, `hsq`, `hX`.

Nothing about the smoothness of the Levi-Civita connection appears among the hypotheses: it is the
instance of `Submission/Work/LCSmooth/Mhat.lean`. -/
theorem aspherical_integer_homology_four_sphere_of_data
    (hmodels : ∀ x : rt.Mhat, ∃ G ∈ rt.models.models,
      Work.Curvature.SecNonposAt G ((extChartAt Work.Space.I4 x) x) ∧
      Filter.Eventually (fun q => ∀ a b : Work.Space.E4,
          Submission.ChartConnection.chartGram (I := Work.Space.I4) x
            ((extChartAt Work.Space.I4 x).symm q) a b = G q a b)
        (nhds ((extChartAt Work.Space.I4 x) x)))
    (L : Work.HomologyMV.MVLES)
    (eM : ∀ k : ℤ, Work.HomologyMV.ModelM k ≅ L.H (k, 0))
    (eN : ∀ k : ℤ, Work.HomologyMV.ModelN k ≅ L.H (k, 1))
    (hsq : ∀ k : ℤ, (eM k).hom ≫ L.d (k, 0) = Work.HomologyMV.wConcrete k ≫ (eN k).hom)
    (hX : ∀ k : ℕ, L.H ((k : ℤ), 2) ≅
      LeanEval.Topology.intHomology k (TopCat.of rt.Mhat)) :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  Work.Final.aspherical_integer_homology_four_sphere
    (D := finalInputsOfModels hmodels L eM eN hsq hX)

/-- The same, with the connection's smoothness made explicit as a hypothesis that this area's
instance discharges: this is the statement a caller gets if they prefer to see the input.

`Work.LCSmooth.aspherical_integer_homology_four_sphere_of_data` is this theorem with the
hypothesis instantiated by `inferInstance`. -/
theorem aspherical_integer_homology_four_sphere_of_inputs
    [hsm : CovariantDerivative.ContMDiffCovariantDerivative
      (Work.Final.mhatCov (rt := rt)) Work.Final.smoothGrade]
    (curvLe : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe (Work.Final.mhatCov (rt := rt)) K)
    (L : Work.HomologyMV.MVLES)
    (eM : ∀ k : ℤ, Work.HomologyMV.ModelM k ≅ L.H (k, 0))
    (eN : ∀ k : ℤ, Work.HomologyMV.ModelN k ≅ L.H (k, 1))
    (hsq : ∀ k : ℤ, (eM k).hom ≫ L.d (k, 0) = Work.HomologyMV.wConcrete k ≫ (eN k).hom)
    (hX : ∀ k : ℕ, L.H ((k : ℤ), 2) ≅
      LeanEval.Topology.intHomology k (TopCat.of rt.Mhat)) :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  Work.Final.aspherical_integer_homology_four_sphere
    (D := finalInputsOfCurvLe curvLe L eM eN hsq hX)

/-- **The challenge theorem, from the curvature datum and the three homology identifications.**

This is the strongest form this area can offer: with `import Submission.Work.LCSmooth.All`, the
smoothness of the connection (`cov_smooth`) is an instance, and the Mayer–Vietoris sequence `L`
together with the identification `hX` of its `(k,2)`-slot are constructed
(`Work.LCSmooth.mhatLES`, `Work.LCSmooth.mhatLES_hX`).  What is left is exactly

* `hmodels` — the chart models of the atlas of `M̂` and their non-positive curvature
  (`NOTES_FINAL.md` §5; owner: the `Work.Space.RTData` provider), and
* `eM`, `eN`, `hsq` — the identifications of `H_*(A ∩ B)`, `H_*(A) ⊞ H_*(B)` with the free models
  and the commuting square with the concrete Mayer–Vietoris matrix (`NOTES_FINAL.md` §2; owners:
  DELTAHOMOLOGY + CERTIFICATES). -/
theorem aspherical_integer_homology_four_sphere_of_homology_data [rt : Work.Space.RTData]
    (hmodels : ∀ x : rt.Mhat, ∃ G ∈ rt.models.models,
      Work.Curvature.SecNonposAt G ((extChartAt Work.Space.I4 x) x) ∧
      Filter.Eventually (fun q => ∀ a b : Work.Space.E4,
          Submission.ChartConnection.chartGram (I := Work.Space.I4) x
            ((extChartAt Work.Space.I4 x).symm q) a b = G q a b)
        (nhds ((extChartAt Work.Space.I4 x) x)))
    (eM : ∀ k : ℤ, Work.HomologyMV.ModelM k ≅ (mhatLES (rt := rt)).H (k, 0))
    (eN : ∀ k : ℤ, Work.HomologyMV.ModelN k ≅ (mhatLES (rt := rt)).H (k, 1))
    (hsq : ∀ k : ℤ, (eM k).hom ≫ (mhatLES (rt := rt)).d (k, 0)
      = Work.HomologyMV.wConcrete k ≫ (eN k).hom) :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  Work.Final.aspherical_integer_homology_four_sphere
    (D := finalInputsOfModelsAndMV hmodels eM eN hsq)

/-- **The challenge theorem, from a sign on each model of the atlas and the homology
identifications.**  This is the sharpest form the area offers: the chart-model curvature datum is
reduced to the statement that every model of the finite atlas (equivalently, by
`Work.LCSmooth.models_eq_range_field`, every `rt.models.field i`) has non-positive sectional
curvature at the chart images of the points where the chart is used — the hypothesis a provider of
`Work.Space.RTData` discharges by checking the three documented metrics
(`Work.Curvature.secNonposAt_uhs/warped/flat`); `L` and `hX` are constructed, and the smoothness
of the connection is the instance of this area. -/
theorem aspherical_integer_homology_four_sphere_of_model_secNonpos
    (h : ∀ G ∈ rt.models.models, ∀ x : rt.Mhat,
      Work.Curvature.SecNonposAt G ((extChartAt Work.Space.I4 x) x))
    (eM : ∀ k : ℤ, Work.HomologyMV.ModelM k ≅ (mhatLES (rt := rt)).H (k, 0))
    (eN : ∀ k : ℤ, Work.HomologyMV.ModelN k ≅ (mhatLES (rt := rt)).H (k, 1))
    (hsq : ∀ k : ℤ, (eM k).hom ≫ (mhatLES (rt := rt)).d (k, 0)
      = Work.HomologyMV.wConcrete k ≫ (eN k).hom) :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  Work.Final.aspherical_integer_homology_four_sphere
    (D := finalInputsOfModelSecNonpos h eM eN hsq)

end Main

end

end Work.LCSmooth
