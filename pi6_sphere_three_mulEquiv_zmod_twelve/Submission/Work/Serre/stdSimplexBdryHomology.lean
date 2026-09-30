import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.RatHurewicz.Bridge.Defs
import Submission.Work.Serre.E0SimplexDefs
import Submission.Work.Serre.simplexBdry_eq_iUnion_coface
import Submission.Work.Serre.simplexBdryGeometry
import Submission.Work.Serre.cornerSimplex_interior
import Submission.Work.Cohomology.relChainsHomeomorphCompat
import Submission.Work.Cohomology.diskPairHomologyTop
import Submission.Work.Cohomology.diskPairHomologyZero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option synthInstance.maxHeartbeats 400000

/-!
# The relative homology of the standard simplex pair `(Δⁿ, ∂Δⁿ)`

The standard `(m+1)`-simplex `Δ^{m+1} = stdSimplex ℝ (Fin (m+2))` with its simplicial boundary
`∂Δ^{m+1} = ⋃ i : Fin (m+2), Set.range (Work.RatHurewicz.Bridge.coface m i)` is a model of the
pair `(D^{m+1}, S^m)`.  Consequently

`H_k(Δ^{m+1}, ∂Δ^{m+1}; ℤ) = ℤ` for `k = m+1` and `0` otherwise.

This is the "local disc-pair" computation feeding the E3(a) step of the Serre computation
(`Submission/Work/Serre/E3A_PLAN.md` §6, piece (iv)).

## The route

Rather than recomputing the pair homology from the long exact sequence of the pair (which requires
a separate analysis in degrees `0` and `1`), we use the fact that the *pair* `(Δⁿ, ∂Δⁿ)` is
homeomorphic to the *pair* `(Dⁿ, Sⁿ⁻¹)`, whose relative homology has already been computed
(`Work.Cohomology.diskPairHomologyTop`, `Work.Cohomology.diskPairHomologyZero`, including their
`n = 1` cases).

* `stdSimplexPairHomeo` constructs the pair homeomorphism in two steps: the affine projection
  `Work.Serre.simplexProj` carries `Δⁿ` onto the corner body `cornerSimplex n` and the boundary
  `∂Δⁿ` onto its frontier (`Work.Serre.proj_mem_frontier_iff`), and Mathlib's gauge rescaling
  (`exists_homeomorph_image_interior_closure_frontier_eq_unitBall`) carries the corner body onto the
  unit ball with its frontier going to the unit sphere.
* `Work.Cohomology.relChainsHomeomorphCompat` transports relative homology along a homeomorphism
  of pairs.
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

set_option linter.style.haveILetI false

noncomputable section

/-- **The pair `(Δⁿ, ∂Δⁿ)` is homeomorphic to the pair `(Dⁿ, Sⁿ⁻¹)`.**

There is a homeomorphism `e : ↥(stdSimplex ℝ (Fin (n+1))) ≃ₜ ↥(Metric.closedBall 0 1)` of the
standard `n`-simplex onto the closed unit ball of `ℝⁿ` which carries the simplicial boundary
`Work.Serre.simplexBdry n` exactly onto the unit sphere. -/
theorem stdSimplexPairHomeo (n : ℕ) :
    ∃ e : ↥(stdSimplex ℝ (Fin (n + 1))) ≃ₜ
        ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1),
      ∀ z, z ∈ simplexBdry n ↔
        ((e z : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :
          EuclideanSpace ℝ (Fin n)) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  haveI : CompactSpace ↥(stdSimplex ℝ (Fin (n + 1))) :=
    isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ (Fin (n + 1)))
  obtain ⟨h, -, hcl, hfr⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (cornerSimplex_convex n) (interior_cornerSimplex_nonempty n (cornerSimplex_interior n))
    (cornerSimplex_isBounded n)
  rw [(cornerSimplex_isClosed n).closure_eq] at hcl
  -- `hcl : h '' cornerSimplex n = closedBall 0 1`, `hfr : h '' frontier (cornerSimplex n) = sphere 0 1`
  let F : ↥(stdSimplex ℝ (Fin (n + 1))) →
      ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    fun z => ⟨h (simplexProj n z.1),
      by rw [← hcl]; exact ⟨simplexProj n z.1, simplexProj_mem_cornerSimplex n z.2, rfl⟩⟩
  have hFcont : Continuous F :=
    Continuous.subtype_mk
      (h.continuous.comp ((continuous_simplexProj n).comp continuous_subtype_val)) _
  have hFinj : Function.Injective F := by
    intro z z' hzz
    refine simplexProj_injective n (h.injective ?_)
    exact congrArg Subtype.val hzz
  have hmem_ball : ∀ x : EuclideanSpace ℝ (Fin n),
      x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ↔ x ∈ h '' cornerSimplex n := by
    intro x
    rw [hcl]
  have hmem_sphere : ∀ x : EuclideanSpace ℝ (Fin n),
      h x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↔ x ∈ frontier (cornerSimplex n) := by
    intro x
    rw [← hfr]
    exact ⟨fun ⟨w, hw, hwx⟩ => by rw [h.injective hwx] at hw; exact hw,
      fun hx => ⟨x, hx, rfl⟩⟩
  have hFsurj : Function.Surjective F := by
    intro y
    obtain ⟨c, hc, hcy⟩ := (hmem_ball y.1).mp y.2
    refine ⟨⟨simplexLift n c, simplexLift_mem_stdSimplex n hc.1 hc.2⟩, ?_⟩
    apply Subtype.ext
    show h (simplexProj n (simplexLift n c)) = y.1
    rw [simplexProj_lift]
    exact hcy
  refine ⟨Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective F ⟨hFinj, hFsurj⟩) hFcont, ?_⟩
  intro z
  have hFe : (Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofBijective F ⟨hFinj, hFsurj⟩) hFcont) z = F z := rfl
  have hFe' : ((F z : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :
      EuclideanSpace ℝ (Fin n)) = h (simplexProj n z.1) := rfl
  rw [hFe, hFe']
  exact (proj_mem_frontier_iff n (cornerSimplex_interior n) z).symm.trans
    (hmem_sphere (simplexProj n z.1)).symm

/-- **The relative homology of the pair `(Δ^{m+1}, ∂Δ^{m+1})` is that of the pair
`(D^{m+1}, S^m)`.** -/
theorem relChains_stdSimplexBdry_iso (m k : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of ↥(stdSimplex ℝ (Fin (m + 2))))
        (⋃ i : Fin (m + 2), Set.range (Work.RatHurewicz.Bridge.coface m i))).homology k) ≅
      ((Work.Cohomology.relChains (Work.Cohomology.diskUnit (m + 1))
        (Work.Cohomology.sphereInUnit (m + 1))).homology k)) := by
  have hA := Work.Serre.simplexBdry_eq_iUnion_coface m
  obtain ⟨e, he⟩ := stdSimplexPairHomeo (m + 1)
  have he' : ∀ z : ↥(stdSimplex ℝ (Fin (m + 2))),
      z ∈ (⋃ i : Fin (m + 2), Set.range (Work.RatHurewicz.Bridge.coface m i)) ↔
        (e z : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)) ∈
          Work.Cohomology.sphereInUnit (m + 1) := by
    intro z
    rw [← hA]
    exact he z
  exact Work.Cohomology.relChainsHomeomorphCompat ↥(stdSimplex ℝ (Fin (m + 2)))
    ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (⋃ i : Fin (m + 2), Set.range (Work.RatHurewicz.Bridge.coface m i))
    (Work.Cohomology.sphereInUnit (m + 1)) e he' k

theorem stdSimplexBdryHomology (m : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of ↥(stdSimplex ℝ (Fin (m + 2))))
        (⋃ i : Fin (m + 2), Set.range (Work.RatHurewicz.Bridge.coface m i))).homology (m + 1))
        ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ k : ℕ, k ≠ m + 1 →
        CategoryTheory.Limits.IsZero (((Work.Cohomology.relChains
          (TopCat.of ↥(stdSimplex ℝ (Fin (m + 2))))
          (⋃ i : Fin (m + 2), Set.range (Work.RatHurewicz.Bridge.coface m i))).homology k))) := by
  constructor
  · obtain ⟨iso⟩ := relChains_stdSimplexBdry_iso m (m + 1)
    exact ⟨iso ≪≫ (Work.Cohomology.diskPairHomologyTop (m + 1) (by omega)).some⟩
  · intro k hk
    obtain ⟨iso⟩ := relChains_stdSimplexBdry_iso m k
    exact IsZero.of_iso (Work.Cohomology.diskPairHomologyZero (m + 1) k (by omega) (by omega)) iso

end

end Work.Serre
