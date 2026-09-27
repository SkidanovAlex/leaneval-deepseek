/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: hSpace_sphere_iff team

# Mayer–Vietoris criteria for the vanishing of `H^{k+1}`

Two general consequences of the Mayer–Vietoris machinery of `Submission/Work/Cohomology/`:

* `mv_subsingleton_succ`: if `A, B ⊆ S` cover `S`, are acyclic in degree `k+1`, and their
  intersection vanishes in degree `k`, then `H^{k+1}(S)` vanishes.
* `mv_small_subsingleton`: the same for an open cover `X = W₁ ∪ W₂` of a topological space,
  using the small-simplex theorem to replace `Sing X` by the subcomplex
  `singIn X W₁ ⊔ singIn X W₂`.

Also the space `punctCapSq n` occurring in the diagonal computation: a square of open caps of
`S^{n+1} × S^{n+1}` with one point removed.
-/
import Mathlib
import Submission.Work.Sphere.ProdSetup
import Submission.Work.Sphere.Basic
import Submission.Work.Cohomology.singIn_iso
import Submission.Work.Cohomology.small_simplex_injective
import Submission.Work.Cohomology.small_simplex_surjective
import Submission.Work.Cohomology.mvConnecting_surjective

open CategoryTheory Simplicial Opposite
open Submission.Cohomology

namespace Work.Sphere

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- Mayer–Vietoris: if the two pieces are acyclic in degree `k+1` and their intersection
vanishes in degree `k`, then `H^{k+1}` of the total space vanishes. -/
theorem mv_subsingleton_succ {S : SSet.{0}} (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (k : ℕ)
    (hA : Subsingleton (H A ℚ (k+1))) (hB : Subsingleton (H B ℚ (k+1)))
    (hAB' : Subsingleton (H (A ⊓ B : S.Subcomplex) ℚ k)) :
    Subsingleton (H S ℚ (k+1)) :=
  (Work.Cohomology.mvConnecting_surjective S A B hAB k hA hB).subsingleton

/-- **The two-piece cover criterion.**  If `X = W₁ ∪ W₂` is an open cover whose pieces are acyclic
in degree `k+1` and whose intersection vanishes in degree `k`, then `H^{k+1}(X) = 0`. -/
theorem mv_small_subsingleton {X : TopCat.{0}} (W₁ W₂ : Set X) (h₁ : IsOpen W₁) (h₂ : IsOpen W₂)
    (hcov : ∀ x : ↥X, x ∈ W₁ ∨ x ∈ W₂) (k : ℕ)
    (hA : Subsingleton (H (singIn X W₁) ℚ (k+1)))
    (hB : Subsingleton (H (singIn X W₂) ℚ (k+1)))
    (hC : Subsingleton (H (singIn X (W₁ ∩ W₂)) ℚ k)) :
    Subsingleton (H (TopCat.toSSet.obj X) ℚ (k+1)) := by
  have hsmall : Subsingleton (H (singIn X W₁ ⊔ singIn X W₂ : (TopCat.toSSet.obj X).Subcomplex)
      ℚ (k+1)) := by
    refine mv_subsingleton_succ
      ((singIn X W₁).preimage (singIn X W₁ ⊔ singIn X W₂).ι)
      ((singIn X W₂).preimage (singIn X W₁ ⊔ singIn X W₂).ι) ?_ k ?_ ?_ ?_
    · rw [← SSet.Subcomplex.preimage_max, SSet.Subcomplex.preimage_ι]
    · exact subsingleton_of_linearEquiv (Classical.choice (Submission.Sphere.H_iso_of_iso
        (Submission.Sphere.preimageIso _ (singIn X W₁) le_sup_left) (k+1))) hA
    · exact subsingleton_of_linearEquiv (Classical.choice (Submission.Sphere.H_iso_of_iso
        (Submission.Sphere.preimageIso _ (singIn X W₂) le_sup_right) (k+1))) hB
    · rw [← SSet.Subcomplex.preimage_min, ← singIn_inter]
      exact subsingleton_of_linearEquiv (Classical.choice (Submission.Sphere.H_iso_of_iso
        (Submission.Sphere.preimageIso _
          (singIn X (W₁ ∩ W₂))
          (le_trans (singIn_mono Set.inter_subset_left) le_sup_left)) k)) hC
  have hinj := Work.Cohomology.small_simplex_injective X W₁ W₂ h₁ h₂ hcov (k+1)
  exact ⟨fun x y => hinj (Subsingleton.elim _ _)⟩

/-- The open square of caps `capMinus n × capMinus n` inside `S^{n+1} × S^{n+1}`, with the point
`(polePt, polePt)` removed. -/
abbrev punctCapSq (n : ℕ) : TopCat.{0} :=
  TopCat.of {q : ↥(Submission.Sphere.Sph (n+1)) × ↥(Submission.Sphere.Sph (n+1)) //
    q ≠ (Submission.Sphere.polePt (n+1), Submission.Sphere.polePt (n+1)) ∧
      q.1 ∈ Submission.Sphere.capMinus n ∧ q.2 ∈ Submission.Sphere.capMinus n}

end

end Work.Sphere
