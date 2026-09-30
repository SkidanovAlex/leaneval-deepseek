import Mathlib
import Submission.Work.HomologyExtra.SimplexClass
import Submission.Work.HomologyExtra.GeneratorReduction
import Submission.Work.HomologyExtra.simplexNorthCap_contractible
import Submission.Work.HomologyExtra.SimplexDisk
import Submission.Work.HomologyExtra.cornerSimplex_facts
import Submission.Work.HomologyExtra.exists_cornerDiskHomeo
import Submission.Work.HomologyExtra.isIso_relHomologyMap_pairHomOfHomeomorph

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The relative homology of the standard simplex pair `(Δⁿ, ∂Δⁿ)`

The relative homology `H_k(Δⁿ, ∂Δⁿ; ℤ)` is `ℤ` in degree `n` and `0` otherwise (`n ≥ 1`).

The computation is reduced to the already-known disc pair `(Dⁿ, Sⁿ⁻¹)`
(`Work.Homology.relHomology_disc_sphere`) by an explicit homeomorphism of pairs
`(Δⁿ, ∂Δⁿ) ≅ (Dⁿ, Sⁿ⁻¹)`: the standard simplex is homeomorphic to the **corner**
`{y ∈ ℝⁿ | y ≥ 0, ∑ yᵢ ≤ 1}` (`Work.HomologyExtra.simplexCornerHomeo`, which turns the boundary
`∂Δⁿ` into the topological boundary of the corner), and any compact convex body with nonempty
interior is homeomorphic to the closed unit ball mapping its boundary to the sphere (Minkowski
functional, `Work.HomologyExtra.exists_cornerDiskHomeo`).
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.HomologyExtra

noncomputable section

/-- **The boundary of the standard simplex is the boundary of the corner**: the vanishing
barycentric coordinates of a point of `Δⁿ` correspond exactly to the points of the topological
boundary of `cornerSimplex n`. -/
theorem mem_simplexBoundary_iff_frontier (n : ℕ)
    (hfr : ∀ y : EuclideanSpace ℝ (Fin n), y ∈ frontier (cornerSimplex n) ↔
      y ∈ cornerSimplex n ∧ (∑ i, y i = 1 ∨ ∃ i, y i = 0))
    (w : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    w ∈ simplexBoundary n ↔ cornerOfSimplex n w ∈ frontier (cornerSimplex n) := by
  have hsum : ∑ i : Fin n, w.weights (Fin.castSucc i) = 1 - w.weights (Fin.last n) := by
    have h := Fin.sum_univ_castSucc (fun j : Fin (n + 1) => w.weights j)
    have ht : ∑ j : Fin (n + 1), w.weights j = 1 := w.total_of_fintype
    linarith
  rw [hfr]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨cornerOfSimplex_mem n w, ?_⟩
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · right
      exact ⟨i, by rw [cornerOfSimplex_apply, hj]⟩
    · left
      simp only [cornerOfSimplex_apply]
      rw [hsum, hj, sub_zero]
  · rintro ⟨-, h | ⟨i, hi⟩⟩
    · refine ⟨Fin.last n, ?_⟩
      have h' : ∑ i : Fin n, w.weights (Fin.castSucc i) = 1 := by
        simpa only [cornerOfSimplex_apply] using h
      linarith
    · exact ⟨Fin.castSucc i, by simpa only [cornerOfSimplex_apply] using hi⟩

/-- **The relative homology of the standard simplex pair**: `H_k(Δⁿ, ∂Δⁿ; ℤ) ≅ ℤ` for `k = n` and
`0` otherwise (`n ≥ 1`).

Route: `(Δⁿ, ∂Δⁿ) ≅ (Dⁿ, Sⁿ⁻¹)` as pairs of spaces, and relative homology is invariant under
homeomorphisms of pairs, so the claim follows from the disc pair computation
`Work.Homology.relHomology_disc_sphere`. -/
theorem relHomology_simplexPair (n k : ℕ) (hn : 1 ≤ n) :
    Nonempty (Work.Homology.relHomology Work.Homology.ZMod k (Work.HomologyExtra.simplex n)
        (Work.HomologyExtra.simplexBoundary n) ≅
      (if k = n then Work.Homology.ZMod else ModuleCat.of ℤ PUnit)) := by
  obtain ⟨hc, hcl, hb, hint, hfr⟩ := cornerSimplex_facts n hn
  have hne : (interior (cornerSimplex n)).Nonempty := by
    refine ⟨WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ) / (n + 1)), ?_⟩
    rw [hint]
    constructor
    · intro i; positivity
    · have hsum : ∑ _i : Fin n, (1 : ℝ) / ((n : ℝ) + 1) = (n : ℝ) / ((n : ℝ) + 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]
      rw [hsum]
      exact (div_lt_one (by positivity)).mpr (by linarith)
  obtain ⟨e₃, he₃⟩ := exists_cornerDiskHomeo n hc hcl hne hb
  let e : Work.HomologyExtra.simplex n ≃ₜ Work.Cohomology.diskUnit n :=
    (simplexCornerHomeo n).trans e₃
  have hAB : ∀ x : Work.HomologyExtra.simplex n,
      x ∈ Work.HomologyExtra.simplexBoundary n ↔ e x ∈ Work.Cohomology.sphereInUnit n := by
    intro x
    change x ∈ Work.HomologyExtra.simplexBoundary n ↔
      ((e x : Work.Cohomology.diskUnit n) : EuclideanSpace ℝ (Fin n)) ∈
        Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
    rw [mem_simplexBoundary_iff_frontier n hfr x]
    have h2 : e x = e₃ (simplexCornerHomeo n x) := rfl
    rw [h2, ← he₃ (simplexCornerHomeo n x)]
    exact Iff.rfl
  let Φ := pairHomOfHomeomorph e hAB
  haveI : CategoryTheory.IsIso (Work.Homology.relHomologyMap Work.Homology.ZMod k Φ) :=
    isIso_relHomologyMap_pairHomOfHomeomorph e hAB k
  exact ⟨CategoryTheory.asIso (Work.Homology.relHomologyMap Work.Homology.ZMod k Φ) ≪≫
    (Work.Homology.relHomology_disc_sphere n k hn).some⟩

end

end Work.HomologyExtra
