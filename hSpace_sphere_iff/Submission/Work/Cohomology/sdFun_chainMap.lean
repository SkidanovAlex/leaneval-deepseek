/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The barycentric subdivision is a chain map

The subdivision operator `sdFun X n` on the singular chains of a topological space `X` satisfies
`∂ ∘ sd = sd ∘ ∂`, i.e. it is a chain map of the singular chain complex.

This is the chain-level input of the small-simplex (Mayer–Vietoris) argument for singular
cohomology: the subdivision of a chain reduces its diameter, so it is chain homotopic to the
identity through a chain homotopy built from the prism `tFun` (`tFun_homotopy`).

The proof reduces, by linearity of both sides in the chain `c`, to the case of a single simplex
`c = single τ r`.  There the two sides are computed from

* `sbdry_single` (the boundary of a simplex as the alternating sum of its faces),
* `sdFun_single` (the subdivision of a simplex, pushed forward along the simplex),
* `pushChain_sbdry` (pushforward along a continuous map is a chain map), and
* the universal chain-map identity `sbdry_sdUniv` together with `homOfSimplex_delta`,
  which identifies the `i`-th face of the continuous map of `τ` with the composite of the face
  inclusion and the map of `τ`.
-/
import Mathlib
import Submission.Work.Cohomology.SubdivisionSpace

namespace Work.Cohomology

theorem sdFun_chainMap (X : TopCat.{0}) (n : ℕ)
    (c : Submission.Cohomology.SChain (TopCat.toSSet.obj X) ℚ (n+1)) :
    Submission.Cohomology.sdFun X n
        (Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ n c)
      = Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ n
          (Submission.Cohomology.sdFun X (n+1) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single τ r =>
      rw [Submission.Cohomology.sbdry_single, map_sum]
      simp only [Submission.Cohomology.sdFun_single]
      rw [map_smul, ← Submission.Cohomology.pushChain_sbdry,
        Submission.Cohomology.sbdry_sdUniv, map_sum]
      simp only [map_smul, ← Submission.Cohomology.pushChain_comp,
        ← Submission.Cohomology.homOfSimplex_delta]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [smul_smul]
      congr 1
      rw [zsmul_eq_mul]
      push_cast
      ring

end Work.Cohomology
