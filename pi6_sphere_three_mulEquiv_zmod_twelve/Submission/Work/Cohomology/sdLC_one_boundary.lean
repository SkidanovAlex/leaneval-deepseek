import Mathlib
import Submission.Work.Cohomology.Subdivision
import Submission.Work.Cohomology.boundaryLC_coneLC

/-!
# The boundary of `sdLC 1`

The base case (`n = 0`) of `Work.Cohomology.sdLC_boundary`: the boundary of the barycentric
subdivision of the identity `1`-simplex of `Δ¹` is the image of `sdLC 0` under the alternating sum
of the two vertex embeddings `Δ⁰ ↪ Δ¹`.

The general cone formula `boundaryLC_coneLC` covers the cone of a chain of degree `≥ 1`; the cone of
a `0`-chain `c` has the extra term `-(∑ coefficient) • (cone point)`, which vanishes here because
`c = [v₁] - [v₀]` has coefficient sum `0`.  This is the content of the computation below.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Cohomology

noncomputable section

/-- The `0`-th face of the cone over the `0`-simplex `v` forgets the cone point (the base case of
the cone formula, not covered by `faceVF_zero_cons`). -/
lemma faceVF_zero_coneVF_fin1 {N : ℕ} (b : stdSimplex ℝ (Fin (N + 1)))
    (v : Fin 1 → stdSimplex ℝ (Fin (N + 1))) :
    faceVF (N := N) (0 : Fin 2) (coneVF b v) = v := by
  funext j
  fin_cases j
  simp [faceVF, coneVF]

/-- The `1`-st face of the cone over the `0`-simplex `v` is constant equal to the cone point. -/
lemma faceVF_one_coneVF_fin1 {N : ℕ} (b : stdSimplex ℝ (Fin (N + 1)))
    (v : Fin 1 → stdSimplex ℝ (Fin (N + 1))) :
    faceVF (N := N) (1 : Fin 2) (coneVF b v) = fun _ : Fin 1 => b := by
  funext j
  fin_cases j
  simp [faceVF, coneVF]

/-- The `k = 0` case of the cone formula on a generator: the boundary of the cone over a
`0`-simplex is the simplex itself minus the cone point. -/
lemma boundaryLC_coneLC_single_zero (N : ℕ) (b : stdSimplex ℝ (Fin (N + 1)))
    (v : Fin 1 → stdSimplex ℝ (Fin (N + 1))) (a : ℤ) :
    boundaryLC N 0 (coneLC N 0 b (Finsupp.single v a)) =
      Finsupp.single v a - Finsupp.single (fun _ : Fin 1 => b) a := by
  rw [coneLC_single, boundaryLC_single, Fin.sum_univ_two]
  rw [faceVF_zero_coneVF_fin1, faceVF_one_coneVF_fin1, sub_eq_add_neg]
  simp

theorem sdLC_one_boundary :
    boundaryLC 1 0 (sdLC 1) =
      ∑ i : Fin 2, ((-1 : ℤ) ^ (i : ℕ)) • embedLC 0 0 i (sdLC 0) := by
  set w1 : Fin 1 → stdSimplex ℝ (Fin 2) := fun _ => stdSimplex.vertex (1 : Fin 2) with hw1
  set w0 : Fin 1 → stdSimplex ℝ (Fin 2) := fun _ => stdSimplex.vertex (0 : Fin 2) with hw0
  have h0 : (embedLC 0 0 (0 : Fin 2)) (sdLC 0) =
      Finsupp.single (fun _ : Fin 1 => stdSimplex.vertex (1 : Fin 2)) 1 := by
    rw [show sdLC 0 = Finsupp.single (idVert 0) 1 from rfl]
    simp only [embedLC, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, idVert,
      stdSimplex.map_vertex]
    congr 1
    funext j
    fin_cases j
    rfl
  have h1 : (embedLC 0 0 (1 : Fin 2)) (sdLC 0) =
      Finsupp.single (fun _ : Fin 1 => stdSimplex.vertex (0 : Fin 2)) 1 := by
    rw [show sdLC 0 = Finsupp.single (idVert 0) 1 from rfl]
    simp only [embedLC, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, idVert,
      stdSimplex.map_vertex]
    congr 1
    funext j
    fin_cases j
    rfl
  have hR : (∑ i : Fin 2, ((-1 : ℤ) ^ (i : ℕ)) • embedLC 0 0 i (sdLC 0)) =
      Finsupp.single w1 1 - Finsupp.single w0 1 := by
    rw [Fin.sum_univ_two, h0, h1, ← hw1, ← hw0]
    simp [sub_eq_add_neg]
  have hL : boundaryLC 1 0 (sdLC 1) = Finsupp.single w1 1 - Finsupp.single w0 1 := by
    have hsd : sdLC 1 =
        coneLC 1 0 (bary (idVert 1)) (Finsupp.single w1 1 - Finsupp.single w0 1) := by
      rw [show sdLC 1 = coneLC 1 0 (bary (idVert 1))
          (∑ i : Fin 2, ((-1 : ℤ) ^ (i : ℕ)) • embedLC 0 0 i (sdLC 0)) from rfl, hR]
    rw [hsd, map_sub, map_sub]
    rw [boundaryLC_coneLC_single_zero 1 (bary (idVert 1)) w1 1,
        boundaryLC_coneLC_single_zero 1 (bary (idVert 1)) w0 1]
    abel
  rw [hL, hR]

end

end Work.Cohomology
