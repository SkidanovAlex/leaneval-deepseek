/-
Copyright (c) 2026 The contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Coordinates of `K[G]` over the group algebra of a finite-index subgroup

Let `H ≤ G` be a subgroup of finite index and let `K` be a semiring.  Then `K[G]` is a free
left module over `K[H]`, with basis a transversal of the right cosets of `H`.  This file sets
up the vocabulary for that statement:

* `cosetRep H q` for `q : G ⧸ H` is the representative of the *right* coset of `H`
  corresponding to the left coset `q` (the inverse of the canonical representative of `q`,
  so that `cosetRep H q = (Quotient.out q)⁻¹`);
* `coord H K q x` is the component of `x : K[G]` supported on the right coset
  `H · cosetRep H q`, transported to `K[H]` via `h ↦ h · cosetRep H q`.

The two structure statements that the main proof needs are the existence of `a` with
`∑ q, subgroupAlgMap H K (a q) * single (cosetRep H q) 1 = x` and the uniqueness
`coord H K q (∑ q, subgroupAlgMap H K (a q) * single (cosetRep H q) 1) = a q`.
-/
import Mathlib
import Submission.Work.ORReductions.Basic
import Submission.Work.ORReductions.SubgroupAlg

set_option autoImplicit false

namespace Work.ORReductions.Coherent

open MonoidAlgebra

variable {G : Type*} [Group G] {K : Type*}

/-- The representative of the right coset `H · cosetRep H q` of `H` in `G` attached to the
left coset `q ∈ G ⧸ H`; it is the inverse of the canonical representative of `q`. -/
noncomputable def cosetRep (H : Subgroup G) (q : G ⧸ H) : G := (Quotient.out q)⁻¹

/-- Every `g : G` lies in the right coset `H · cosetRep H q` for a suitable left coset `q`. -/
lemma cosetRep_spec (H : Subgroup G) (g : G) : ∃ q : G ⧸ H, g * (cosetRep H q)⁻¹ ∈ H := by
  refine ⟨Quotient.mk (QuotientGroup.leftRel H) g⁻¹, ?_⟩
  have h := Quotient.mk_out (s := QuotientGroup.leftRel H) g⁻¹
  rw [QuotientGroup.leftRel_apply] at h
  have h' : (g * Quotient.out (Quotient.mk (QuotientGroup.leftRel H) g⁻¹))⁻¹ ∈ H := by
    simpa only [mul_inv_rev] using h
  simpa [cosetRep, inv_inv] using H.inv_mem h'

/-- The right cosets `H · cosetRep H q` are pairwise distinct. -/
lemma cosetRep_eq_of_mul_inv_mem (H : Subgroup G) {q q' : G ⧸ H}
    (h : cosetRep H q * (cosetRep H q')⁻¹ ∈ H) : q = q' := by
  have h' : (QuotientGroup.leftRel H) (Quotient.out q) (Quotient.out q') := by
    rw [QuotientGroup.leftRel_apply]
    simpa [cosetRep] using h
  rw [← Quotient.out_eq q, ← Quotient.out_eq q']
  exact Quotient.sound h'

/-- The `K[H]`-component of `x : K[G]` supported on the right coset `H · cosetRep H q`,
transported to `K[H]` via `h ↦ h · cosetRep H q`. -/
noncomputable def coord (H : Subgroup G) (K : Type*) [Semiring K] (q : G ⧸ H)
    (x : MonoidAlgebra K G) : MonoidAlgebra K H :=
  MonoidAlgebra.ofCoeff <|
    Finsupp.comapDomain (fun h : H => (h : G) * cosetRep H q) x.coeff
      (fun _ _ _ _ hab => Subtype.ext (mul_right_cancel hab))

@[simp]
lemma coord_zero (H : Subgroup G) (K : Type*) [Semiring K] (q : G ⧸ H) :
    coord H K q 0 = 0 := by
  ext h
  rfl

lemma coord_add (H : Subgroup G) (K : Type*) [Semiring K] (q : G ⧸ H)
    (x y : MonoidAlgebra K G) : coord H K q (x + y) = coord H K q x + coord H K q y := by
  ext h
  rfl

lemma coord_neg (H : Subgroup G) (K : Type*) [Ring K] (q : G ⧸ H)
    (x : MonoidAlgebra K G) : coord H K q (-x) = -coord H K q x := by
  ext h
  rfl

lemma coord_sub (H : Subgroup G) (K : Type*) [Ring K] (q : G ⧸ H)
    (x y : MonoidAlgebra K G) : coord H K q (x - y) = coord H K q x - coord H K q y := by
  ext h
  rfl

lemma coord_smul (H : Subgroup G) (K : Type*) [CommSemiring K] (q : G ⧸ H) (c : K)
    (x : MonoidAlgebra K G) : coord H K q (c • x) = c • coord H K q x := by
  ext h
  rfl

/-- `coord H K q` as a `K`-linear map. -/
noncomputable def coordLM (H : Subgroup G) (K : Type*) [CommSemiring K] (q : G ⧸ H) :
    MonoidAlgebra K G →ₗ[K] MonoidAlgebra K H where
  toFun := coord H K q
  map_add' := coord_add H K q
  map_smul' := coord_smul H K q

@[simp] lemma coordLM_apply (H : Subgroup G) (K : Type*) [CommSemiring K] (q : G ⧸ H)
    (x : MonoidAlgebra K G) : coordLM H K q x = coord H K q x := rfl

/-- The coefficient of `coord H K q x` at `h` is the coefficient of `x` at
`h · cosetRep H q`. -/
lemma coeff_coord (H : Subgroup G) (K : Type*) [Semiring K] (q : G ⧸ H)
    (x : MonoidAlgebra K G) (h : H) :
    (coord H K q x).coeff h = x.coeff ((h : G) * cosetRep H q) := rfl

/-- `coord H K q` applied to a single, when `g` lies in the coset `H · cosetRep H q`. -/
lemma coord_single_of_mem (H : Subgroup G) (K : Type*) [Semiring K] (q : G ⧸ H) {g : G}
    (hg : g * (cosetRep H q)⁻¹ ∈ H) (c : K) :
    coord H K q (MonoidAlgebra.single g c) =
      MonoidAlgebra.single ⟨g * (cosetRep H q)⁻¹, hg⟩ c := by
  classical
  ext h
  rw [coeff_coord, MonoidAlgebra.coeff_single_apply, MonoidAlgebra.coeff_single_apply]
  by_cases hh : (⟨g * (cosetRep H q)⁻¹, hg⟩ : H) = h
  · have h2 : g = (h : G) * cosetRep H q := by
      have h3 : g * (cosetRep H q)⁻¹ = (h : G) := congrArg Subtype.val hh
      calc g = g * (cosetRep H q)⁻¹ * cosetRep H q := by group
        _ = (h : G) * cosetRep H q := by rw [h3]
    simp [hh, h2]
  · have h2 : ¬ (g = (h : G) * cosetRep H q) := by
      intro hc
      refine hh (Subtype.ext ?_)
      calc g * (cosetRep H q)⁻¹
          = (h : G) * cosetRep H q * (cosetRep H q)⁻¹ := by rw [hc]
        _ = (h : G) := by group
    simp [hh, h2]

/-- `coord H K q` applied to a single, when `g` does not lie in the coset `H · cosetRep H q`. -/
lemma coord_single_of_notMem (H : Subgroup G) (K : Type*) [Semiring K] (q : G ⧸ H) {g : G}
    (hg : g * (cosetRep H q)⁻¹ ∉ H) (c : K) :
    coord H K q (MonoidAlgebra.single g c) = 0 := by
  classical
  ext h
  rw [coeff_coord, MonoidAlgebra.coeff_single_apply]
  have h1 : ¬ (g = (h : G) * cosetRep H q) := by
    intro hc
    refine hg ?_
    rw [hc]
    simpa using h.2
  simp [h1]

/-- The component of `single ((h : G) * cosetRep H q) c` on the coset `H · cosetRep H q`. -/
lemma coord_single_mul_repr (H : Subgroup G) (K : Type*) [Semiring K] (q : G ⧸ H) (h : H)
    (c : K) :
    coord H K q (MonoidAlgebra.single ((h : G) * cosetRep H q) c) =
      MonoidAlgebra.single h c := by
  rw [coord_single_of_mem H K q (show ((h : G) * cosetRep H q) * (cosetRep H q)⁻¹ ∈ H by
    simpa [mul_assoc] using h.2)]
  congr 1
  exact Subtype.ext (by simp)

/-- The component of `single ((h : G) * cosetRep H q') c` on the coset `H · cosetRep H q`
vanishes when `q ≠ q'`. -/
lemma coord_single_mul_repr_eq_zero (H : Subgroup G) (K : Type*) [Semiring K] {q q' : G ⧸ H}
    (hq : q ≠ q') (h : H) (c : K) :
    coord H K q (MonoidAlgebra.single ((h : G) * cosetRep H q') c) = 0 := by
  refine coord_single_of_notMem H K q ?_ c
  intro hcon
  refine hq ?_
  have h2 : cosetRep H q' * (cosetRep H q)⁻¹ ∈ H := by
    have h3 : (h : G)⁻¹ * ((h : G) * cosetRep H q' * (cosetRep H q)⁻¹) ∈ H :=
      H.mul_mem (H.inv_mem h.2) hcon
    have h4 : (h : G)⁻¹ * ((h : G) * cosetRep H q' * (cosetRep H q)⁻¹)
        = cosetRep H q' * (cosetRep H q)⁻¹ := by group
    rwa [h4] at h3
  have h5 : cosetRep H q * (cosetRep H q')⁻¹ ∈ H := by
    simpa using H.inv_mem h2
  exact cosetRep_eq_of_mul_inv_mem H h5

end Work.ORReductions.Coherent
