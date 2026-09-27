import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Drive.Rays.hairpinOfRayTube
import Submission.Work.Drive.Rays.rayHeightTransverse
import Submission.Work.Drive.Rays.rayCollarOfData

/-!
# A proper embedded line in an open set from a proper embedded ray

The endgame of the "line input" of the non-compact case of Whitney's strong embedding theorem: a
proper embedded ray inside an open set `W` is thickened to a one-sided smooth tube along the ray
(`Work.Drive.Rays.rayHeightTransverse` gives the transverse pair `(P, g)` along the ray,
`Work.Drive.Rays.rayCollarOfData` -- built from the one-sided local slabs
`Work.Drive.Rays.rayLocalSlabs` -- glues them into the tube), and the explicit model hairpin
`Work.Drive.Rays.hairpinOfRayTube` is pasted into that tube.
-/

namespace Work.Drive.Rays

open scoped Manifold ContDiff
open Work.Noncompact.CompressionTube

open scoped Manifold ContDiff in
open Work.Noncompact.CompressionTube in
/-- **The hairpin: a proper embedded line inside `W` from a proper embedded ray inside `W`.**  Given
a `C^∞`, injective, immersive ray `r : ℝ → M` which is proper on `[0,∞)` and whose values on
`[0,∞)` lie in the open set `W`, there is a smooth, injective, proper, immersed line
`γ : ℝ → M` through `r 0` (at time `1`) with `Set.range γ ⊆ W`.

This is the endgame of the "line input" of the compression of the domain in the non-compact case of
Whitney's strong embedding theorem, independent of how the ray `r` was produced; it is one half of
the route "ray + hairpin" for `Work.Drive.line_of_escaping_path`
(`Submission/Work/Drive/line_of_escaping_path.lean`), the other half being the ray construction
`Work.Drive.ray_of_escaping_path` (`Submission/Work/Drive/ray_of_escaping_path.lean`).

Suggested routes.

1. *A thickening of the ray composed with the model hairpin.*  Since `r ↾ [0,∞)` is injective and
   proper into a `T2` manifold, its image is a closed embedded half-line contained in the open set
   `W`, so a neighbourhood of that image inside `W` exists (it may have to be thin near `∂W`).
   The two-sided collar of a *line* is proved
   (`Work.Noncompact.CompressionTube.exists_collar_twosided`, whose `[ConnectedSpace M]` hypothesis
   is unused, so it can be applied in the connected component of `r 0`), and
   `Submission/Work/Noncompact/CompressionTube/halfTube/` (`boxTube`, `collar`,
   `collarInChartCanonical`, `collarEstimate`, `collarTwist`) contains the local model machinery for
   the one-sided case; `Work.Noncompact.CompressionTube.exists_shrunk_tube` /
   `exists_tube_in_open` shrink a tube into a prescribed open set.  Inside the (half-)tube the curve
   `s ↦ (δ · s/√(1+s²) · e₁, |s|)` is a proper embedded smooth immersion of `ℝ` through the core
   point of parameter `0`, and the curve `s ↦ (δ · s/√(1+s²) · e₁, 1 + s²)` passes through the core
   point of parameter `1`; composing with the thickening and shifting the parameter gives `γ` with
   `γ 1 = r 0`.

2. *A second ray glued to the first.*  Apply a ray construction a second time inside
   `W ∖ r '' Set.Ici ε` (open and preconnected by
   `Work.Noncompact.ProperLine.ray_sdiff_nonseparation`, proved) with the *opposite* germ at `r 0`,
   and glue the two rays with the proved
   `Work.Noncompact.CompressionTube.line_of_two_oneSided_rays` (or the `_drive` copy
   `Work.Drive.Rays.line_of_two_germed_oneSided_rays_drive` in
   `Submission/Work/Drive/Rays/lineOfTwoRays_drive.lean`; both take the two rays and give the line).

Both routes are legitimate; do not coordinate with anyone, just finish one of them. -/
theorem lineOfProperRay {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {W : Set M} (hW : IsOpen W) {r : ℝ → M}
    (hrsm : ContMDiffOn MCreal (MC n) smoothOrder r (Set.Ici (0:ℝ)))
    (hrinj : Set.InjOn r (Set.Ici (0:ℝ)))
    (hrp : IsProperMap (fun t : Set.Ici (0:ℝ) => r t))
    (hrimm : ∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv MCreal (MC n) r t))
    (hrW : ∀ t : ℝ, 0 ≤ t → r t ∈ W) :
    ∃ γ : ℝ → M, γ 1 = r 0 ∧ ContMDiff MCreal (MC n) smoothOrder γ ∧
      Function.Injective γ ∧ IsProperMap γ ∧
      (∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) γ t)) ∧ Set.range γ ⊆ W := by
  obtain ⟨g, P, hg, hP, hgc, hPc, htr⟩ :=
    rayHeightTransverse (n := n) hn hW hrsm hrinj hrp hrimm hrW
  obtain ⟨Ψ, hΨsm, hΨ0, hΨinj, hΨimm, hΨW, hΨesc⟩ :=
    rayCollarOfData (n := n) hn hW hrsm hrinj hrp hrimm hrW hg hP hgc hPc htr
  obtain ⟨γ, hγ1, hγsm, hγinj, hγprop, hγimm, hγW⟩ :=
    hairpinOfRayTube (n := n) hn hΨsm hΨ0 hΨinj hΨimm hΨW hΨesc
  exact ⟨γ, by rw [hγ1, ← hΨ0], hγsm, hγinj, hγprop, hγimm, hγW⟩
end Work.Drive.Rays
