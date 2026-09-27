import Mathlib
import Submission.Work.Cohomology.Mesh
import Submission.Work.Cohomology.sdLC_isBaryNested
import Submission.Work.Cohomology.diam_affComp_le
import Submission.Work.Cohomology.support_pushLC

/-!
# The mesh of the iterated barycentric subdivision

The affine chain `sdIterLC n N` (`Submission/Work/Cohomology/Mesh.lean`) is the `N`-fold barycentric
subdivision of the identity simplex of `Δⁿ`.  Its simplices have diameter at most
`(n/(n+1))^N` — in particular the mesh tends to `0`, which is what makes a sufficiently high
iterate of the subdivision operator land in the small chains of any open cover.

The proof is the induction one expects: `sdLC k`'s simplices are nested barycentres
(`sdLC_isBaryNested`), pushing a family of points forward along such a family contracts the
diameter by the factor `k/(k+1)` (`diam_affComp_le`), and `sdIterLC n (N+1)` pushes `sdLC n`
forward along the simplices of `sdIterLC n N` (`support_pushLC`).
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- The mesh of the identity simplex of `Δⁿ` is at most `1` (the `sup` metric on the standard
simplex has diameter `1`). -/
theorem meshVF_idVert (n : ℕ) : meshVF (idVert n) ≤ 1 := by
  rw [meshVF]
  refine Metric.diam_le_of_forall_dist_le (by norm_num) ?_
  rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
  change dist (idVert n i : Fin (n + 1) → ℝ) (idVert n j) ≤ 1
  simp only [idVert, stdSimplex.vertex_coe]
  by_cases hij : i = j
  · subst hij; simp
  · rw [dist_single_single i j 1 1 hij]
    simp [Real.dist_eq]

/-- **The mesh of the `N`-fold subdivided identity simplex.** -/
theorem mesh_sdIterLC (n N : ℕ) (v : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1)))
    (hv : v ∈ (sdIterLC n N).support) :
    meshVF v ≤ ((n : ℝ) / (n + 1)) ^ N := by
  induction N generalizing v with
  | zero =>
    rw [sdIterLC] at hv
    rw [Finsupp.mem_support_single] at hv
    obtain ⟨hveq, -⟩ := hv
    rw [hveq]
    simpa using meshVF_idVert n
  | succ N ih =>
    rw [sdIterLC] at hv
    obtain ⟨w, hw, u, hu, rfl⟩ := support_pushLC n n (sdIterLC n N) (sdLC n) v hv
    have hu' : IsBaryNested u := sdLC_isBaryNested n u hu
    calc meshVF (affComp w u) ≤ ((n : ℝ) / (n + 1)) * meshVF w := diam_affComp_le n w u hu'
      _ ≤ ((n : ℝ) / (n + 1)) * ((n : ℝ) / (n + 1)) ^ N :=
          mul_le_mul_of_nonneg_left (ih w hw) (by positivity)
      _ = ((n : ℝ) / (n + 1)) ^ (N + 1) := by rw [pow_succ, mul_comm]

end

end Work.Cohomology
