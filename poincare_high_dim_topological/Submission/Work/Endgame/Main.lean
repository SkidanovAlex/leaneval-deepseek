import Mathlib
import Submission.Work.Endgame.Basic
import Submission.Work.Endgame.Defs
import Submission.Work.Endgame.complInftyHomeomorph_apply
import Submission.Work.Endgame.exists_compl_homeomorph_euclideanSpace_of_homeomorph_sphere
import Submission.Work.Endgame.isOpenEmbedding_complSingleton
import Submission.Work.Endgame.nonempty_compl_homeomorph_euclideanSpace
import Submission.Work.Endgame.nonempty_compl_pole_homeomorph_euclideanSpace
import Submission.Work.Endgame.nonempty_homeomorph_compl_singleton
import Submission.Work.Endgame.nonempty_homeomorph_onePoint_iff
import Submission.Work.Endgame.nonempty_homeomorph_onePoint_of_compl_homeomorph
import Submission.Work.Endgame.nonempty_homeomorph_sphere_iff_exists_compl_homeomorph
import Submission.Work.Endgame.nonempty_homeomorph_sphere_of_ball_homeomorph
import Submission.Work.Endgame.nonempty_homeomorph_sphere_of_compl_homeomorph
import Submission.Work.Endgame.nonempty_homeomorph_sphere_of_compl_homeomorph_finrank
import Submission.Work.Endgame.nonempty_homeomorph_sphere_of_homeomorph_compl
import Submission.Work.Endgame.nonempty_homeomorph_sphere_of_homeomorph_onePoint
import Submission.Work.Endgame.nonempty_homeomorph_sphere_of_nonempty_compl_homeomorph
import Submission.Work.Endgame.nonempty_homeomorph_sphere_of_sdiff_homeomorph
import Submission.Work.Endgame.onePointComplHomeomorph_apply_coe
import Submission.Work.Endgame.onePointComplHomeomorph_apply_infty
import Submission.Work.Endgame.onePointComplHomeomorph_symm_apply_self

/-!
# `Work.Endgame`: the endgame of the high-dimensional Poincaré conjecture

**Chapter summary.** If `M` is a compact Hausdorff space and the complement of a point `p : M`
is homeomorphic to `ℝⁿ`, then `M` is homeomorphic to the unit sphere `𝕊ⁿ ⊂ ℝⁿ⁺¹`.  In the
notation of the challenge statement `Challenge.lean` this is

```
M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
```

where `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`.

**Proof route** (the one-point compactification):

1. `Work.Endgame.onePointComplHomeomorph p : OnePoint ({p}ᶜ : Set M) ≃ₜ M` — a compact
   Hausdorff space is the one-point compactification of the complement of any of its points.
   This is the universal property of `OnePoint`, `OnePoint.equivOfIsEmbeddingOfRangeEq`,
   applied to the open embedding `({p}ᶜ : Set M) ↪ M`.
2. `Homeomorph.onePointCongr` — the one-point compactification is functorial, so a
   homeomorphism `({p}ᶜ : Set M) ≃ₜ ℝⁿ` induces `OnePoint ({p}ᶜ) ≃ₜ OnePoint ℝⁿ`.
3. `Work.Endgame.onePointEuclideanHomeomorphSphere n : OnePoint (EuclideanSpace ℝ (Fin n)) ≃ₜ 𝕊ⁿ`
   — the one-point compactification of `ℝⁿ` is `𝕊ⁿ` (stereographic projection, Mathlib's
   `onePointEquivSphereOfFinrankEq`).

**Main entry points** (all in `Work.Endgame`):

* `homeomorphSphereOfComplHomeomorph p h : M ≃ₜ 𝕊ⁿ` (`Endgame/Basic.lean`), the actual
  homeomorphism; and the general model-space version
  `homeomorphSphereOfComplHomeomorphOfFinrank p hV h : M ≃ₜ 𝕊ⁿ` taking `h : ({p}ᶜ) ≃ₜ V`
  for an `n`-dimensional normed real space `V`.
* `nonempty_homeomorph_sphere_of_compl_homeomorph p h : Nonempty (M ≃ₜ 𝕊ⁿ)` — the
  `Nonempty` form, which is the shape of the challenge's conclusion.  The variants
  `nonempty_homeomorph_sphere_of_nonempty_compl_homeomorph` (hypothesis wrapped in
  `Nonempty`), `nonempty_homeomorph_sphere_of_homeomorph_compl` (homeomorphism in the other
  direction), `nonempty_homeomorph_sphere_of_sdiff_homeomorph` (complement written
  `Set.univ \ {p}`), `nonempty_homeomorph_sphere_of_ball_homeomorph` (punctured set
  homeomorphic to an open unit ball) and `nonempty_homeomorph_sphere_of_compl_homeomorph_finrank`
  (arbitrary `n`-dimensional normed `V` in place of `ℝⁿ`) are interchangeable presentations
  of the same hypothesis.
* `homeomorphOnePointOfComplHomeomorph p h : M ≃ₜ OnePoint ℝⁿ` and
  `nonempty_homeomorph_onePoint_iff : Nonempty (M ≃ₜ OnePoint ℝⁿ) ↔ ∃ p, Nonempty (({p}ᶜ) ≃ₜ ℝⁿ)`
  — the intermediate reformulation: `M` is the one-point compactification of `ℝⁿ`.
* `endgameOfCharted` below — the same conclusion in the exact hypotheses of the challenge
  statement (with `[ChartedSpace (EuclideanSpace ℝ (Fin n)) M]`).

**Converse / coherence.**

* `nonempty_homeomorph_sphere_iff_exists_compl_homeomorph` — the chapter's top line: for compact
  Hausdorff `M`, `Nonempty (M ≃ₜ 𝕊ⁿ) ↔ ∃ p : M, Nonempty (({p}ᶜ : Set M) ≃ₜ ℝⁿ)`.
* `exists_compl_homeomorph_euclideanSpace_of_homeomorph_sphere` — if `M ≃ₜ 𝕊ⁿ` then *some* point
  of `M` has `ℝⁿ` as its complement.
* `nonempty_compl_homeomorph_euclideanSpace` — `𝕊ⁿ` punctured at *any* point is `ℝⁿ`
  (stereographic projection); `nonempty_compl_pole_homeomorph_euclideanSpace` is the same for
  the pole of `onePointEuclideanHomeomorphSphere`.

**API lemmas.**

* `onePointComplHomeomorph_apply_infty`, `onePointComplHomeomorph_apply_coe`,
  `onePointComplHomeomorph_symm_apply_self` — the values of `onePointComplHomeomorph`;
* `complInftyHomeomorph : ({∞}ᶜ : Set (OnePoint X)) ≃ₜ X` and its `apply` lemma;
* `homeomorphComplSingleton e p : ({p}ᶜ : Set X) ≃ₜ ({e p}ᶜ : Set Y)` and
  `nonempty_homeomorph_compl_singleton` — restriction of a homeomorphism to punctured sets;
* `isOpenEmbedding_complSingleton` — `({p}ᶜ : Set M) ↪ M` is an open embedding for `T1` `M`.

Nothing in this chapter is specific to dimension `≥ 5` or to manifolds: compactness of `M`
and the puncture homeomorphism are the only inputs.
-/

open Metric (sphere)
open Set Filter Topology
open scoped OnePoint

namespace Work.Endgame

/-- **Endgame, in the hypotheses of the challenge statement.** If `M` is a compact Hausdorff
`n`-manifold (here only `[ChartedSpace (EuclideanSpace ℝ (Fin n)) M]` is retained, since the
endgame does not use the manifold structure) and the complement of `p : M` is homeomorphic to
`ℝⁿ`, then `M` is homeomorphic to the unit sphere `𝕊ⁿ ⊂ ℝⁿ⁺¹`. -/
theorem endgameOfCharted {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (p : M)
    (h : ({p}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin n)) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  ⟨homeomorphSphereOfComplHomeomorph p h⟩

/-- **Endgame, in the hypotheses of the challenge statement, with compactness as an explicit
hypothesis.** This is the form to use when compactness of `M` has been established as a term
`hc : CompactSpace M` (for instance from `M ≃ₕ 𝕊ⁿ`) rather than registered as an instance:
`endgameOfChartedCompact hc p h`. -/
theorem endgameOfChartedCompact {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (hc : CompactSpace M) (p : M)
    (h : ({p}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin n)) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  haveI := hc
  ⟨homeomorphSphereOfComplHomeomorph p h⟩

/-- The general main theorem with compactness as an explicit hypothesis, for callers that do not
have the `CompactSpace M` instance registered. -/
theorem nonemptyHomeomorphSphereOfComplHomeomorphCompact {n : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] (hc : CompactSpace M) (p : M)
    (h : ({p}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin n)) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  haveI := hc
  ⟨homeomorphSphereOfComplHomeomorph p h⟩

end Work.Endgame
