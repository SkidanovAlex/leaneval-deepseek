import Mathlib
import Submission.Work.HomologyExtra.SimplexDisk

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HomologyExtra

/-- **The corner model of the `n`-simplex is the `n`-disc, with boundary the sphere.**

Any compact convex body with nonempty interior in a real normed space is homeomorphic to the
closed unit ball, in a way which carries the interior to the open ball, the closure to the closed
ball and the frontier to the sphere (`exists_homeomorph_image_interior_closure_frontier_eq_unitBall`,
Mathlib's Minkowski-functional construction).  Taking the ambient homeomorphism `h` and restricting
it to the closed body `cornerSimplex n` (which is closed by hypothesis, so that `h` maps it onto
`closedBall 0 1`) yields the required homeomorphism of pairs `(cornerSimplex n, frontier) ≃ (Dⁿ, Sⁿ⁻¹)`.

The hypotheses on `cornerSimplex n` (convexity, closedness, nonempty interior, boundedness) are
exactly those needed for that Mathlib lemma, so this statement is a direct consequence of it and
holds for every `n` for which the hypotheses are satisfied. -/
theorem exists_cornerDiskHomeo (n : ℕ) (hc : Convex ℝ (Work.HomologyExtra.cornerSimplex n))
    (hcl : IsClosed (Work.HomologyExtra.cornerSimplex n))
    (hne : (interior (Work.HomologyExtra.cornerSimplex n)).Nonempty)
    (hb : Bornology.IsBounded (Work.HomologyExtra.cornerSimplex n)) :
    ∃ e : ↥(Work.HomologyExtra.cornerSimplex n) ≃ₜ
        ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1),
      ∀ y : ↥(Work.HomologyExtra.cornerSimplex n),
        (y : EuclideanSpace ℝ (Fin n)) ∈ frontier (Work.HomologyExtra.cornerSimplex n) ↔
          ((e y : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :
            EuclideanSpace ℝ (Fin n)) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  obtain ⟨h, _h_int, h_clo, h_fr⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hne hb
  -- `cornerSimplex n` is closed, hence the ambient homeomorphism `h` maps it onto the closed ball.
  have hs : cornerSimplex n = h ⁻¹' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [← h_clo, hcl.closure_eq, h.preimage_image]
  refine ⟨Homeomorph.sets h hs, ?_⟩
  intro y
  -- The restricted homeomorphism acts as `h` on the underlying points.
  have hcoe : ((Homeomorph.sets h hs y : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :
      EuclideanSpace ℝ (Fin n)) = h (y : EuclideanSpace ℝ (Fin n)) := by
    rw [Homeomorph.sets, Homeomorph.subtype_apply_coe]
  -- `h` carries the frontier onto the sphere, and is injective.
  rw [hcoe, ← h_fr, Set.mem_image]
  constructor
  · rintro hz; exact ⟨y, hz, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    rwa [h.injective hzy] at hz

end Work.HomologyExtra
