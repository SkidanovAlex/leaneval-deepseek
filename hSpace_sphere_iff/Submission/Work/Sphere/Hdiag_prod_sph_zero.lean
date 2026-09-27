/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: hSpace_sphere_iff team

# `H^{p+1}(S^p × S^p) = 0` for `p ≥ 2`

This is the "diagonal" case of the computation of the rational cohomology of a product of
spheres, i.e. the base case `baseE` of `Work.Sphere.prod_sph_main_of_bases`.

The proof is a Mayer–Vietoris computation.  Write `p = n + 1` with `n ≥ 1` and let `z` be the
point `(e, e)` of `X = S^{n+1} × S^{n+1}` (`e` the pole).  Cover `X` by the two open sets

* `U = X \ {z}`  (the punctured product), and
* `V = capMinus n × capMinus n`  (an open square of caps around `z`).

The pieces are acyclic in degree `n + 2` and their intersection `U ∩ V = V \ {z}` vanishes in
degree `n + 1`:

* `H^{n+2}(U) = 0` — the punctured product is homotopy equivalent to the wedge
  `S^{n+1} ∨ S^{n+1}` (`Work.Sphere.Hdiag_punctProd`);
* `H^{n+2}(V) = 0` — `V` is a product of two contractible caps;
* `H^{n+1}(U ∩ V) = 0` — the punctured cap square is homotopy equivalent to `S^{2n+1}`
  (`Work.Sphere.Hdiag_punctCapSq`).

The two-piece cover criterion `Work.Sphere.mv_small_subsingleton` (Mayer–Vietoris together with
the small-simplex theorem) then gives the vanishing of `H^{n+2}(X) = H^{p+1}(S^p × S^p)`.
-/
import Mathlib
import Submission.Work.Sphere.ProdSetup
import Submission.Work.Sphere.ProdRec
import Submission.Work.Sphere.Values
import Submission.Work.Sphere.HdiagBase
import Submission.Work.Sphere.Hdiag_punctProd
import Submission.Work.Sphere.Hdiag_punctCapSq
import Submission.Work.Cohomology.H_subsingleton_of_contractible

open CategoryTheory Simplicial Opposite
open Submission.Cohomology Submission.Sphere

namespace Work.Sphere

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- The pole of `S^{n+1}` lies in the negative cap `capMinus n`. -/
lemma polePt_mem_capMinus (n : ℕ) : polePt (n+1) ∈ capMinus n := by
  rw [Submission.Sphere.capMinus]
  exact pole_ne_neg_pole (n+1)

theorem Hdiag_prod_sph_zero (p : ℕ) (hp : 2 ≤ p) :
    Subsingleton (Submission.Cohomology.H
      (TopCat.toSSet.obj (Work.Sphere.TopProd (Submission.Sphere.Sph p) (Submission.Sphere.Sph p))) ℚ (p+1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  -- the two open sets of the cover
  set U : Set (TopProd (Sph (n+1)) (Sph (n+1))) :=
    {q | q ≠ (polePt (n+1), polePt (n+1))} with hUdef
  set V : Set (TopProd (Sph (n+1)) (Sph (n+1))) :=
    {q | q.1 ∈ capMinus n ∧ q.2 ∈ capMinus n} with hVdef
  have hUopen : IsOpen U := by
    rw [hUdef]
    exact isClosed_singleton.isOpen_compl
  have hVopen : IsOpen V := by
    rw [hVdef]
    exact ((isOpen_capMinus n).preimage continuous_fst).inter
      ((isOpen_capMinus n).preimage continuous_snd)
  have hcov : ∀ q : ↥(TopProd (Sph (n+1)) (Sph (n+1))), q ∈ U ∨ q ∈ V := by
    intro q
    by_cases h : q = (polePt (n+1), polePt (n+1))
    · right
      rw [hVdef, h]
      exact ⟨polePt_mem_capMinus n, polePt_mem_capMinus n⟩
    · left
      rw [hUdef]
      exact h
  -- `U` is the punctured product, acyclic in degree `n + 2`
  have hA : Subsingleton (Submission.Cohomology.H
      (singIn (TopProd (Sph (n+1)) (Sph (n+1))) U) ℚ (n+1+1)) :=
    Submission.Sphere.subsingleton_singIn (Hdiag_punctProd n hn)
  -- `V` is a product of contractible caps, acyclic in degree `n + 2`
  have hB : Subsingleton (Submission.Cohomology.H
      (singIn (TopProd (Sph (n+1)) (Sph (n+1))) V) ℚ (n+1+1)) := by
    refine Submission.Sphere.subsingleton_singIn (W := V) ?_
    have hVeq : V = capMinus n ×ˢ capMinus n := by rw [hVdef]; rfl
    rw [hVeq]
    have : ContractibleSpace ↥(capMinus n) := capMinus_contractible n
    have h1 : Subsingleton (Submission.Cohomology.H
        (TopCat.toSSet.obj (TopCat.of (↥(capMinus n) × ↥(capMinus n)))) ℚ (n+1+1)) :=
      Work.Cohomology.H_subsingleton_of_contractible
        (TopCat.of (↥(capMinus n) × ↥(capMinus n))) inferInstance ℚ (by omega)
    have h2 : Subsingleton (Submission.Cohomology.H
        (TopCat.toSSet.obj (TopCat.of ↥(capMinus n ×ˢ capMinus n))) ℚ (n+1+1)) :=
      subsingleton_of_linearEquiv
        (Classical.choice (H_iso_of_homeo
          (Homeomorph.Set.prod (capMinus n) (capMinus n)) (n+1+1))) h1
    exact h2
  -- `U ∩ V` is the punctured cap square, vanishing in degree `n + 1`
  have hC : Subsingleton (Submission.Cohomology.H
      (singIn (TopProd (Sph (n+1)) (Sph (n+1))) (U ∩ V)) ℚ (n+1)) :=
    Submission.Sphere.subsingleton_singIn (Hdiag_punctCapSq n hn)
  exact mv_small_subsingleton U V hUopen hVopen hcov (n+1) hA hB hC

end

end Work.Sphere
