/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# `H^{n+2}` of the punctured product `S^{n+1} × S^{n+1} \ {(e,e)}` vanishes

The space `P = (S^{n+1} × S^{n+1}) \ {(e,e)}` (with `e` the pole) is covered by the two open sets

* `W₁ = {q | q.1 ∈ capPlus n}`  (first coordinate different from the pole),
* `W₂ = {q | q.2 ∈ capPlus n}`  (second coordinate different from the pole),

whose *union is all of `P`*: the only point of the product that belongs to neither is `(e,e)`, and
that point has been removed.  Its Mayer–Vietoris sequence therefore computes `H^{n+2}(P)`:

* `W₁ ≅ capPlus n × S^{n+1} ≃ S^{n+1}` and `W₂ ≅ S^{n+1} × capPlus n ≃ S^{n+1}` are homotopy
  equivalent to `S^{n+1}` (the cap is contractible), so `H^{n+2}` of either piece vanishes;
* `W₁ ∩ W₂ ≅ capPlus n × capPlus n` is contractible, so `H^{n+1}` of the intersection vanishes.

The two-piece cover criterion `mv_small_subsingleton` (Mayer–Vietoris + the small-simplex theorem)
then gives `H^{n+2}(P) = 0`.

The homeomorphisms with the products of caps are the three `≃ₜ`'s below; everything else is the
Mayer–Vietoris machine of `Submission/Work/Cohomology` and the cohomology of the spheres
(`Work.Sphere.sphere_subsingleton`).
-/
import Mathlib
import Submission.Work.Sphere.HdiagBase
import Submission.Work.Sphere.ProdRec
import Submission.Work.Sphere.Values

namespace Work.Sphere

open CategoryTheory Simplicial Opposite
open Submission.Cohomology

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-- The product `S^{n+1} × S^{n+1}` with the point `(e,e)` removed. -/
abbrev punctProd (n : ℕ) : TopCat.{0} :=
  TopCat.of {q : ↥(Submission.Sphere.Sph (n+1)) × ↥(Submission.Sphere.Sph (n+1)) //
    q ≠ (Submission.Sphere.polePt (n+1), Submission.Sphere.polePt (n+1))}

/-- The piece of the cover of the punctured product on which the first coordinate lies in the
positive cap. -/
abbrev punctW1 (n : ℕ) : Set ↥(punctProd n) :=
  {q | q.1.1 ∈ Submission.Sphere.capPlus n}

/-- The piece of the cover of the punctured product on which the second coordinate lies in the
positive cap. -/
abbrev punctW2 (n : ℕ) : Set ↥(punctProd n) :=
  {q | q.1.2 ∈ Submission.Sphere.capPlus n}

/-- Membership in the positive cap, in terms of the pole. -/
lemma mem_capPlus_iff (n : ℕ) (x : ↥(Submission.Sphere.Sph (n+1))) :
    x ∈ Submission.Sphere.capPlus n ↔ x ≠ Submission.Sphere.polePt (n+1) := by
  rw [Submission.Sphere.capPlus_eq n, Set.mem_ofPred_eq]

/-- `W₁` is the product of the cap with the sphere. -/
def punctW1Homeo (n : ℕ) :
    ↥(punctW1 n) ≃ₜ ↥(Submission.Sphere.capPlus n) × ↥(Submission.Sphere.Sph (n+1)) where
  toFun q := (⟨q.1.1.1, q.2⟩, q.1.1.2)
  invFun p := ⟨⟨(p.1.1, p.2), fun h =>
    (mem_capPlus_iff n p.1.1).mp p.1.2 (congrArg Prod.fst h)⟩, p.1.2⟩
  left_inv q := by ext <;> rfl
  right_inv p := by ext <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- `W₂` is the product of the sphere with the cap. -/
def punctW2Homeo (n : ℕ) :
    ↥(punctW2 n) ≃ₜ ↥(Submission.Sphere.Sph (n+1)) × ↥(Submission.Sphere.capPlus n) where
  toFun q := (q.1.1.1, ⟨q.1.1.2, q.2⟩)
  invFun p := ⟨⟨(p.1, p.2.1), fun h =>
    (mem_capPlus_iff n p.2.1).mp p.2.2 (congrArg Prod.snd h)⟩, p.2.2⟩
  left_inv q := by ext <;> rfl
  right_inv p := by ext <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The intersection of the two pieces is the square of the cap. -/
def punctW12Homeo (n : ℕ) :
    ↥(punctW1 n ∩ punctW2 n) ≃ₜ ↥(Submission.Sphere.capPlus n) ×
      ↥(Submission.Sphere.capPlus n) where
  toFun q := (⟨q.1.1.1, q.2.1⟩, ⟨q.1.1.2, q.2.2⟩)
  invFun p := ⟨⟨(p.1.1, p.2.1), fun h =>
    (mem_capPlus_iff n p.1.1).mp p.1.2 (congrArg Prod.fst h)⟩, ⟨p.1.2, p.2.2⟩⟩
  left_inv q := by ext <;> rfl
  right_inv p := by ext <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The two pieces are open. -/
theorem isOpen_punctW1 (n : ℕ) : IsOpen (punctW1 n) :=
  (Submission.Sphere.isOpen_capPlus n).preimage (by fun_prop)

/-- The two pieces are open. -/
theorem isOpen_punctW2 (n : ℕ) : IsOpen (punctW2 n) :=
  (Submission.Sphere.isOpen_capPlus n).preimage (by fun_prop)

/-- The two pieces cover the punctured product: the only point of the product lying in neither is
the removed point `(e,e)`. -/
theorem punctW1_union_punctW2 (n : ℕ) :
    ∀ x : ↥(punctProd n), x ∈ punctW1 n ∨ x ∈ punctW2 n := by
  intro x
  by_cases h : x.1.1 ∈ Submission.Sphere.capPlus n
  · exact Or.inl h
  · refine Or.inr ?_
    have hx1 : x.1.1 = Submission.Sphere.polePt (n+1) := by
      by_contra hne
      exact h ((mem_capPlus_iff n x.1.1).mpr hne)
    have hx2 : x.1.2 ≠ Submission.Sphere.polePt (n+1) :=
      fun h2 => x.2 (Prod.ext hx1 h2)
    change x.1.2 ∈ Submission.Sphere.capPlus n
    exact (mem_capPlus_iff n x.1.2).mpr hx2

/-- `H^{n+2}` of the first piece vanishes: it is (homotopy equivalent to) `S^{n+1}`. -/
theorem subsingleton_H_punctW1 (n : ℕ) :
    Subsingleton (H (singIn (punctProd n) (punctW1 n)) ℚ (n+1+1)) := by
  refine Submission.Sphere.subsingleton_singIn (X := punctProd n) (W := punctW1 n)
    (m := n+1+1) ?_
  obtain ⟨e1⟩ := H_iso_of_homeo (A := TopCat.of ↥(punctW1 n))
    (B := TopCat.of (↥(Submission.Sphere.capPlus n) × ↥(Submission.Sphere.Sph (n+1))))
    (punctW1Homeo n) (n+1+1)
  obtain ⟨e2⟩ := H_iso_capPlus_prod n (n+1) (n+1+1)
  exact subsingleton_of_linearEquiv (e1.trans e2)
    (sphere_subsingleton (n+1) (n+1+1) (by omega) (by omega))

/-- `H^{n+2}` of the second piece vanishes: it is (homotopy equivalent to) `S^{n+1}`. -/
theorem subsingleton_H_punctW2 (n : ℕ) :
    Subsingleton (H (singIn (punctProd n) (punctW2 n)) ℚ (n+1+1)) := by
  refine Submission.Sphere.subsingleton_singIn (X := punctProd n) (W := punctW2 n)
    (m := n+1+1) ?_
  obtain ⟨e1⟩ := H_iso_of_homeo (A := TopCat.of ↥(punctW2 n))
    (B := TopCat.of (↥(Submission.Sphere.Sph (n+1)) × ↥(Submission.Sphere.capPlus n)))
    (punctW2Homeo n) (n+1+1)
  obtain ⟨e2⟩ := H_iso_of_homeo
    (A := TopCat.of (↥(Submission.Sphere.Sph (n+1)) × ↥(Submission.Sphere.capPlus n)))
    (B := TopCat.of (↥(Submission.Sphere.capPlus n) × ↥(Submission.Sphere.Sph (n+1))))
    (swapHomeo (TopCat.of (Submission.Sphere.capPlus n)) (Submission.Sphere.Sph (n+1))).symm
    (n+1+1)
  obtain ⟨e3⟩ := H_iso_capPlus_prod n (n+1) (n+1+1)
  exact subsingleton_of_linearEquiv (e1.trans (e2.trans e3))
    (sphere_subsingleton (n+1) (n+1+1) (by omega) (by omega))

/-- `H^{n+1}` of the intersection vanishes: it is a product of two contractible caps. -/
theorem subsingleton_H_punctW1_inter_punctW2 (n : ℕ) :
    Subsingleton (H (singIn (punctProd n) (punctW1 n ∩ punctW2 n)) ℚ (n+1)) := by
  refine Submission.Sphere.subsingleton_singIn (X := punctProd n) (W := punctW1 n ∩ punctW2 n)
    (m := n+1) ?_
  haveI : ContractibleSpace ↥(Submission.Sphere.capPlus n) := capPlus_contractible n
  obtain ⟨e1⟩ := H_iso_of_homeo (A := TopCat.of ↥(punctW1 n ∩ punctW2 n))
    (B := TopCat.of (↥(Submission.Sphere.capPlus n) × ↥(Submission.Sphere.capPlus n)))
    (punctW12Homeo n) (n+1)
  exact subsingleton_of_linearEquiv e1
    (Work.Cohomology.H_subsingleton_of_contractible
      (TopCat.of (↥(Submission.Sphere.capPlus n) × ↥(Submission.Sphere.capPlus n)))
      inferInstance ℚ (by omega))

/-- **`H^{n+2}` of the punctured product `S^{n+1} × S^{n+1} \ {(e,e)}` vanishes.** -/
theorem Hdiag_punctProd (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton (Submission.Cohomology.H
      (TopCat.toSSet.obj (TopCat.of
        {q : ↥(Submission.Sphere.Sph (n+1)) × ↥(Submission.Sphere.Sph (n+1)) //
          q ≠ (Submission.Sphere.polePt (n+1), Submission.Sphere.polePt (n+1))})) ℚ (n+1+1)) := by
  have hmain : Subsingleton (H (TopCat.toSSet.obj (punctProd n)) ℚ (n+1+1)) :=
    mv_small_subsingleton (X := punctProd n) (punctW1 n) (punctW2 n) (isOpen_punctW1 n)
      (isOpen_punctW2 n) (punctW1_union_punctW2 n) (n+1)
      (subsingleton_H_punctW1 n) (subsingleton_H_punctW2 n)
      (subsingleton_H_punctW1_inter_punctW2 n)
  exact hmain

end

end Work.Sphere
