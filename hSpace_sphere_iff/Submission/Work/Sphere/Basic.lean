/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: hSpace_sphere_iff team

# The spheres `Sⁿ` and the two-cap cover of `S^{n+1}`

The sphere `Sⁿ` is `Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1`, i.e. the unit sphere of
`ℝ^{n+1}`.  For the computation of the cohomology of spheres we use the cover of `S^{n+1}` by the
two open caps obtained by deleting the pole `e = (0,…,0,1)` and its antipode `-e`.  Both caps are
contractible, and their intersection is the doubly punctured sphere, which is homotopy equivalent
to `Sⁿ`.

The definitions of the caps and their elementary topological properties are collected here; the
substantial geometric input (contractibility of a punctured sphere, and the homotopy equivalence
of the doubly punctured sphere with `Sⁿ`) is proved elsewhere.
-/
import Mathlib
import Submission.Work.Cohomology.Cohomology
import Submission.Work.Cohomology.H_subsingleton_of_contractible

open CategoryTheory

namespace Submission.Sphere

/-- The sphere `Sⁿ` of radius `1` in `ℝ^{n+1}`, as a topological space. -/
abbrev Sph (n : ℕ) : TopCat.{0} :=
  TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)

/-- The "north pole" `e = (0,…,0,1)` of `Sⁿ`, the last standard basis vector. -/
noncomputable def pole (n : ℕ) : EuclideanSpace ℝ (Fin (n+1)) := EuclideanSpace.single (Fin.last n) 1

@[simp] lemma norm_pole (n : ℕ) : ‖pole n‖ = 1 := by
  rw [pole, PiLp.norm_single, norm_one]

lemma pole_mem_sphere (n : ℕ) : pole n ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_pole]

lemma neg_pole_mem_sphere (n : ℕ) :
    -pole n ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_neg, norm_pole]

lemma pole_ne_neg_pole (n : ℕ) : pole n ≠ -pole n := by
  intro h
  have h1 : dist (pole n) (-pole n) = 0 := by rw [← h, dist_self]
  rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ (pole n), norm_smul, norm_pole,
    mul_one] at h1
  norm_num at h1

/-- The pole of `Sⁿ`, as a point of the sphere. -/
noncomputable def polePt (n : ℕ) : Sph n := ⟨pole n, pole_mem_sphere n⟩

/-- The antipode of the pole of `Sⁿ`, as a point of the sphere. -/
noncomputable def negPolePt (n : ℕ) : Sph n := ⟨-pole n, neg_pole_mem_sphere n⟩

lemma polePt_ne_negPolePt (n : ℕ) : polePt n ≠ negPolePt n := fun h =>
  pole_ne_neg_pole n (Subtype.ext_iff.mp h)

/-- The open cap of `S^{n+1}` obtained by deleting the pole: the "northern" open hemisphere. -/
def capPlus (n : ℕ) : Set (Sph (n+1)) :=
  {x | (x : EuclideanSpace ℝ (Fin (n+2))) ≠ pole (n+1)}

/-- The open cap of `S^{n+1}` obtained by deleting the antipode of the pole. -/
def capMinus (n : ℕ) : Set (Sph (n+1)) :=
  {x | (x : EuclideanSpace ℝ (Fin (n+2))) ≠ -pole (n+1)}

/-- The sphere `S^{n+1}` with the two poles deleted. -/
def doublePunctured (n : ℕ) : Set (Sph (n+1)) :=
  {x | (x : EuclideanSpace ℝ (Fin (n+2))) ≠ pole (n+1) ∧
    (x : EuclideanSpace ℝ (Fin (n+2))) ≠ -pole (n+1)}

lemma isOpen_capPlus (n : ℕ) : IsOpen (capPlus n) := by
  have h : capPlus n = Subtype.val ⁻¹' ({(pole (n+1))}ᶜ : Set (EuclideanSpace ℝ (Fin (n+2)))) :=
    rfl
  rw [h]
  exact isClosed_singleton.isOpen_compl.preimage continuous_subtype_val

lemma isOpen_capMinus (n : ℕ) : IsOpen (capMinus n) := by
  have h : capMinus n =
      Subtype.val ⁻¹' ({(-pole (n+1))}ᶜ : Set (EuclideanSpace ℝ (Fin (n+2)))) := rfl
  rw [h]
  exact isClosed_singleton.isOpen_compl.preimage continuous_subtype_val

lemma capPlus_union_capMinus (n : ℕ) : capPlus n ∪ capMinus n = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases h : (x : EuclideanSpace ℝ (Fin (n+2))) = pole (n+1)
  · refine Or.inr ?_
    rw [capMinus, Set.mem_ofPred_eq]
    rintro hc
    exact pole_ne_neg_pole (n+1) (h.symm.trans hc)
  · exact Or.inl h

lemma capPlus_inter_capMinus (n : ℕ) : capPlus n ∩ capMinus n = doublePunctured n := rfl

end Submission.Sphere
