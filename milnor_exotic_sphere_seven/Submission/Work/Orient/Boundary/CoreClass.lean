import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.HalfCover
import Submission.Work.Orient.Boundary.HalfCoverGlue

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The class of an orientation over a compact core

The **orientation-theoretic half** of the existence of the relative fundamental class: from an
orientation family `γ` on a compact `C^1` manifold with boundary `W`, and for *any* compact set
`C` of the interior, one gets a class `u ∈ H_{n+1}(W, W∖C)` whose localisation at every point of `C`
is the generator `γ x`.

The proof is the half-space analogue of the existence proof of `Submission/Work/Orient/Closed.lean`:

* `Work.Orient.Boundary.HalfCover` covers `C` by finitely many coordinate half-balls centred at
  points of `C` and **disjoint from `∂W`**;
* the coherence clause of `IsHalfOrientationFamily` (which is imposed precisely over pieces disjoint
  from `∂W`) supplies a class over each piece with the required localisations;
* the classes agree at every point of the pairwise intersections (both restrict to `γ x`, the point
  being interior), and `Work.Orient.Boundary.HalfCoverGlue` glues them;
* restricting from the union of the pieces to `C` gives `u`.

What remains for `Work.Orient.RelativeFundamentalClassExists` is then purely geometric: transporting
`u` from `H_{n+1}(W, W∖C)` to `H_{n+1}(W, ∂W)` when `C` is a *core* (`W∖C` retracts onto `∂W` — the
collar theorem of `Submission/Work/Surgery/`), together with the boundary formula
`Work.Orient.BoundaryOrientationConvention`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold
open Work.ThomBordism
open Work.Orient.Port

namespace Work.Orient.Boundary

noncomputable section

/-- **The orientation-theoretic part of item 2**: an orientation family on a compact `C^1`
manifold with boundary yields a class over every compact subset of the interior whose
localisations are the generators `γ x`. -/
theorem exists_coreClass (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    {C : Set W} (hC : IsCompact C)
    (hCint : ∀ x ∈ C, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (γ : ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
      Work.Orient.LocH W (n + 1) x)
    (hγ : Work.Orient.IsHalfOrientationFamily n W γ) :
    ∃ u : RelH W (n + 1) C,
      ∀ (x : W) (hx : x ∈ C),
        resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx) u = γ x (hCint x hx) := by
  classical
  have hbclosed : IsClosed ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :=
    ModelWithCorners.isClosed_boundary (I := modelWithCornersEuclideanHalfSpace (n + 1))
      (M := W) (n := 1) (by norm_num)
  have hdisj : Disjoint C ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :=
    Set.disjoint_left.mpr (fun x hx1 hx2 => hCint x hx1 hx2)
  obtain ⟨m, z, r, hr, hgood, hzC, hcov, hdisjt⟩ :=
    HalfCover n W hC hdisj hbclosed
  let K : Fin m → Set W := fun i => Work.Orient.halfBallPiece (n + 1) W (z i) (r i)
  have hK : ∀ i, Work.Orient.IsCoordHalfBall (n + 1) W (K i) :=
    fun i => ⟨z i, r i, hr i, hgood i, rfl⟩
  have hint : ∀ (i : Fin m) (x : W), x ∈ K i →
      x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W := by
    intro i x hx hxb
    exact Set.disjoint_left.mp hdisjt hxb (Set.mem_iUnion.mpr ⟨i, hx⟩)
  have hζ_exists : ∀ i, ∃ a : RelH W (n + 1) (K i), ∀ (x : W)
      (hx : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (hxK : x ∈ K i),
      resRelH W (n + 1) (Set.singleton_subset_iff.mpr hxK) a = γ x hx :=
    fun i => hγ.2 (K i) (hK i) (fun x hx => hint i x hx)
  choose hζ hζspec using hζ_exists
  have hglue : ∀ (i j : Fin m) (x : W) (hx : x ∈ K i ∩ K j),
      resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx.1) (hζ i)
        = resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx.2) (hζ j) := by
    intro i j x hx
    rw [hζspec i x (hint i x hx.1) hx.1, hζspec j x (hint j x hx.2) hx.2]
  obtain ⟨γ₀, hγ₀⟩ := HalfCoverGlue n W K hK hint hζ hglue
  refine ⟨resRelH W (n + 1) hcov γ₀, ?_⟩
  intro x hx
  have h1 : resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx) (resRelH W (n + 1) hcov γ₀)
      = resRelH W (n + 1) (Set.singleton_subset_iff.mpr (hcov hx)) γ₀ := by
    rw [show resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx) (resRelH W (n + 1) hcov γ₀)
          = ((resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx)).comp
              (resRelH W (n + 1) hcov)) γ₀ from rfl]
    rw [RelHmap_comp' W (n + 1) (Set.singleton_subset_iff.mpr hx) hcov
      (Set.singleton_subset_iff.mpr (hcov hx))]
  rw [h1]
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcov hx)
  have h2 : resRelH W (n + 1) (Set.singleton_subset_iff.mpr (hcov hx)) γ₀
      = resRelH W (n + 1) (Set.singleton_subset_iff.mpr hxi) (hζ i) := by
    rw [← hγ₀ i, ← LinearMap.comp_apply,
      ← RelHmap_point_fac W (n + 1) (Set.subset_iUnion K i) hxi]
  rw [h2, hζspec i x (hint i x hxi) hxi]

end

end Work.Orient.Boundary
