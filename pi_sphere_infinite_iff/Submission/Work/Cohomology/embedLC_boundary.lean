import Mathlib
import Submission.Work.Cohomology.Subdivision

/-!
# `embedLC` commutes with the affine boundary `boundaryLC`

The face embeddings `embedLC N k i : LinChain N k → LinChain (N+1) k` (post-composition of every
vertex with the `i`-th face map `Δ^N → Δ^{N+1}`) commute with the affine boundary operator
`boundaryLC`, in the sense that

`∂ (embedLC_i c) = embedLC_i (∂ c)`.

This is the chain-map property used to identify the subdivided boundary of `Δ^{N+1}` with the
subdivision of the boundary of `Δ^{N+1}` (see `sdLC` in `Submission/Work/Cohomology/Subdivision.lean`).

Both sides are `ℤ`-linear in `c`, so it suffices to check the identity on a generator
`Finsupp.single v a`, where it is immediate from the alternating-sum expansion of the boundary
together with the pointwise (in fact definitional) commutation of the face map `faceVF` with the
reindexing `fun v j => stdSimplex.map (Fin.succAbove i) (v j)`.

## Main results

* `embedLC_map_single` — `embedLC` on a generator;
* `boundaryLC_map_single` — `boundaryLC` on a generator;
* `embedLC_boundary_single` — the identity on a generator;
* `embedLC_boundary` — the identity on all affine chains.
-/

set_option backward.isDefEq.respectTransparency false

namespace Work.Cohomology

noncomputable section

/-- The face embedding `embedLC` on a generator of the affine chains. -/
lemma embedLC_map_single (N k : ℕ) (i : Fin (N + 2))
    (v : Fin (k + 1) → stdSimplex ℝ (Fin (N + 1))) (a : ℤ) :
    embedLC N k i (Finsupp.single v a) =
      Finsupp.single (fun j => stdSimplex.map (Fin.succAbove i) (v j)) a := by
  simp [embedLC, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- The boundary `boundaryLC` on a generator of the affine chains. -/
lemma boundaryLC_map_single (N j : ℕ)
    (v : Fin (j + 2) → stdSimplex ℝ (Fin (N + 1))) (a : ℤ) :
    boundaryLC N j (Finsupp.single v a) =
      ∑ i : Fin (j + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (faceVF (N := N) i v) a := by
  simp only [boundaryLC, LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

/-- **The face reindexing `faceVF` commutes with the `i`-th face embedding.**  Both operations
just relabel and post-compose vertices, so the two composites are definitionally equal. -/
lemma faceVF_embed_comm (N k : ℕ) (i : Fin (N + 2)) (j : Fin (k + 2))
    (v : Fin (k + 2) → stdSimplex ℝ (Fin (N + 1))) :
    faceVF (N := N + 1) j (fun l => stdSimplex.map (Fin.succAbove i) (v l)) =
      fun l => stdSimplex.map (Fin.succAbove i) (faceVF (N := N) j v l) := rfl

/-- The face embedding commutes with the boundary on a generator of the affine chains. -/
lemma embedLC_boundary_single (N k : ℕ) (i : Fin (N + 2))
    (v : Fin (k + 2) → stdSimplex ℝ (Fin (N + 1))) (a : ℤ) :
    boundaryLC (N + 1) k (embedLC N (k + 1) i (Finsupp.single v a)) =
      embedLC N k i (boundaryLC N k (Finsupp.single v a)) := by
  rw [embedLC_map_single,
    boundaryLC_map_single (N := N + 1) (j := k)
      (v := fun l => stdSimplex.map (Fin.succAbove i) (v l)) a,
    boundaryLC_map_single (N := N) (j := k) (v := v) a,
    map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, embedLC_map_single, faceVF_embed_comm]

/-- **The face embedding `embedLC` is a chain map with respect to the affine boundary.** -/
theorem embedLC_boundary (N k : ℕ) (i : Fin (N + 2)) (c : LinChain N (k + 1)) :
    boundaryLC (N + 1) k (embedLC N (k + 1) i c) =
      embedLC N k i (boundaryLC N k c) := by
  refine Finsupp.induction c ?h0 ?hstep
  · simp
  · intro a b f ha hb hf
    simp only [map_add]
    rw [embedLC_boundary_single, hf]

end

end Work.Cohomology
