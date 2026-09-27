/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# Simplicial cohomology

For a simplicial set `S` and a commutative ring `R` we have the cochain complex
(`Submission.Cohomology.coboundary`).  This file defines its cohomology groups

`H^n(S; R) = (cocycles of degree n) / (coboundaries of degree n)`

as an explicit quotient of `R`-submodules of `Cochain S R n`, together with contravariant
functoriality.  The quotient formulation (rather than Mathlib's `HomologicalComplex.homology`)
is used because the graded ring structure of cohomology is convenient to state in this form.
-/
import Mathlib
import Submission.Work.Cohomology.Basic
import Submission.Work.Cohomology.Cup
import Submission.Work.Cohomology.coboundary_comp
import Submission.Work.Cohomology.cupOf_coboundary

open CategoryTheory Simplicial Opposite

namespace Submission.Cohomology

noncomputable section

/-- The `R`-submodule of `n`-cocycles of a simplicial set: cochains `u` with `δu = 0`. -/
def cycles (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ) : Submodule R (Cochain S R n) :=
  LinearMap.ker (coboundary S R n)

/-- The `R`-submodule of `n`-coboundaries: cochains of the form `δu`.  In degree `0` this is
zero. -/
def boundaries (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ) : Submodule R (Cochain S R n) :=
  match n with
  | 0 => ⊥
  | m + 1 => LinearMap.range (coboundary S R m)

/-- The coboundaries, viewed as a submodule of the cocycles. -/
def boundariesInCycles (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ) :
    Submodule R (cycles S R n) :=
  (boundaries S R n).comap (cycles S R n).subtype

/-- The `n`-th cohomology group of a simplicial set with coefficients in `R`. -/
abbrev H (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ) : Type _ :=
  (cycles S R n) ⧸ boundariesInCycles S R n

/-- The cohomology class of a cocycle. -/
def H.mk {S : SSet.{0}} {R : Type} [CommRing R] {n : ℕ} (u : Cochain S R n)
    (hu : u ∈ cycles S R n) : H S R n :=
  Submodule.Quotient.mk ⟨u, hu⟩

lemma H.mk_eq_mk_iff {S : SSet.{0}} {R : Type} [CommRing R] {n : ℕ} (u u' : Cochain S R n)
    (hu : u ∈ cycles S R n) (hu' : u' ∈ cycles S R n) :
    H.mk u hu = H.mk u' hu' ↔ u - u' ∈ boundaries S R n := by
  rw [H.mk, H.mk, Submodule.Quotient.eq]
  exact Iff.rfl

@[simp] lemma mem_cycles_iff {S : SSet.{0}} {R : Type} [CommRing R] {n : ℕ}
    (u : Cochain S R n) : u ∈ cycles S R n ↔ coboundary S R n u = 0 := Iff.rfl

lemma mem_boundaries_succ {S : SSet.{0}} {R : Type} [CommRing R] {n : ℕ}
    (u : Cochain S R (n + 1)) :
    u ∈ boundaries S R (n + 1) ↔ ∃ v : Cochain S R n, coboundary S R n v = u := Iff.rfl

/-- The pointwise form of `δ² = 0`. -/
lemma coboundary_coboundary {S : SSet.{0}} {R : Type} [CommRing R] {n : ℕ}
    (v : Cochain S R n) : coboundary S R (n + 1) (coboundary S R n v) = 0 := by
  have h := congrArg (fun (f : Cochain S R n →ₗ[R] Cochain S R (n + 2)) => f v)
    (Work.Cohomology.coboundary_comp S R n)
  simpa [LinearMap.comp_apply] using h

/-- A coboundary is a cocycle. -/
lemma boundaries_le_cycles (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ) :
    boundaries S R n ≤ cycles S R n := by
  match n with
  | 0 => exact bot_le
  | m + 1 =>
      rintro u ⟨v, rfl⟩
      exact coboundary_coboundary v

section Functoriality

variable {S T : SSet.{0}} {R : Type} [CommRing R]

/-- Pullback of cochains preserves cocycles. -/
lemma pullbackCo_mem_cycles (f : S ⟶ T) {n : ℕ} {u : Cochain T R n} (hu : u ∈ cycles T R n) :
    pullbackCo R f u ∈ cycles S R n := by
  rw [mem_cycles_iff] at hu ⊢
  rw [← pullbackCo_coboundary R f n u, hu]
  ext σ; rfl

/-- Pullback of cochains preserves coboundaries. -/
lemma pullbackCo_mem_boundaries (f : S ⟶ T) {n : ℕ} {u : Cochain T R n}
    (hu : u ∈ boundaries T R n) : pullbackCo R f u ∈ boundaries S R n := by
  match n with
  | 0 =>
      rw [boundaries] at hu ⊢
      rw [Submodule.mem_bot] at hu ⊢
      rw [hu]
      ext σ; rfl
  | m + 1 =>
      rw [boundaries, LinearMap.mem_range] at hu ⊢
      obtain ⟨v, rfl⟩ := hu
      exact ⟨pullbackCo R f v, by rw [← pullbackCo_coboundary R f m v]⟩

/-- Pullback of cocycles along a map of simplicial sets. -/
def cyclesMap (f : S ⟶ T) (n : ℕ) : cycles T R n →ₗ[R] cycles S R n where
  toFun u := ⟨pullbackCo R f u.1, pullbackCo_mem_cycles f u.2⟩
  map_add' u v := by ext σ; rfl
  map_smul' r u := by ext σ; rfl

/-- The contravariant map induced by a morphism of simplicial sets on cohomology. -/
def H.map (R : Type) [CommRing R] {S T : SSet.{0}} (f : S ⟶ T) (n : ℕ) :
    H T R n →ₗ[R] H S R n :=
  (boundariesInCycles T R n).mapQ (boundariesInCycles S R n) (cyclesMap (R := R) f n)
    (by
      intro u hu
      show (cyclesMap (R := R) f n u : Cochain S R n) ∈ boundaries S R n
      exact pullbackCo_mem_boundaries f (show u.1 ∈ boundaries T R n from hu))

@[simp] lemma H.map_mk (R : Type) [CommRing R] {S T : SSet.{0}} (f : S ⟶ T) {n : ℕ}
    (u : Cochain T R n) (hu : u ∈ cycles T R n) :
    H.map R f n (H.mk u hu) = H.mk (pullbackCo R f u) (pullbackCo_mem_cycles f hu) := by
  rw [H.map, H.mk, Submodule.mapQ_apply]
  rfl

/-- Pullback along the identity is the identity on cohomology. -/
lemma H.map_id (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ) :
    H.map R (CategoryTheory.CategoryStruct.id S) n = 1 := by
  apply LinearMap.ext
  intro x
  induction x using Quot.inductionOn with
  | h u =>
    change H.map R (CategoryTheory.CategoryStruct.id S) n (H.mk u.1 u.2) = H.mk u.1 u.2
    rw [H.map_mk]
    rfl

end Functoriality

section CupCocycles

variable {S : SSet.{0}} {R : Type} [CommRing R]

/-- The cup product of two cocycles is a cocycle. -/
lemma cupOf_mem_cycles {n p q : ℕ} (h : p + q = n) {u : Cochain S R p} {v : Cochain S R q}
    (hu : u ∈ cycles S R p) (hv : v ∈ cycles S R q) : cupOf S R h u v ∈ cycles S R n := by
  rw [mem_cycles_iff] at hu hv ⊢
  rw [Work.Cohomology.cupOf_coboundary S R h]
  rw [hu, hv]
  simp

/-- `(δa) ⌣ v` is a coboundary when `v` is a cocycle. -/
lemma cupOf_coboundary_left_mem_boundaries {n p q : ℕ} (h : p + q = n) (a : Cochain S R p)
    {v : Cochain S R q} (hv : v ∈ cycles S R q) :
    cupOf S R (by omega : (p + 1) + q = n + 1) (coboundary S R p a) v
      ∈ boundaries S R (n + 1) := by
  rw [mem_cycles_iff] at hv
  rw [mem_boundaries_succ]
  refine ⟨cupOf S R h a v, ?_⟩
  rw [Work.Cohomology.cupOf_coboundary S R h, hv]
  simp

/-- `u ⌣ (δb)` is a coboundary when `u` is a cocycle. -/
lemma cupOf_coboundary_right_mem_boundaries {m p q : ℕ} (h : p + (q + 1) = m) {u : Cochain S R p}
    (hu : u ∈ cycles S R p) (b : Cochain S R q) :
    cupOf S R h u (coboundary S R q b) ∈ boundaries S R m := by
  obtain rfl : m = p + q + 1 := by omega
  rw [mem_cycles_iff] at hu
  rw [mem_boundaries_succ]
  refine ⟨(-1 : ℤ) ^ p • cupOf S R rfl u b, ?_⟩
  rw [map_zsmul, Work.Cohomology.cupOf_coboundary S R (rfl : p + q = p + q), hu,
    cupOf_zero_left, zero_add]
  rw [negOnePow_smul_smul]

end CupCocycles

section CupH

variable {S : SSet.{0}} {R : Type} [CommRing R]

/-- The cup product on cohomology, with the ambient degree `n` and the splitting `h : p + q = n`
explicit.  It is defined by choosing representatives (using `Quot.out`); the computation rule on
classes is `H.cupOf_mk`. -/
noncomputable def H.cupOf {n p q : ℕ} (h : p + q = n) (x : H S R p) (y : H S R q) :
    H S R n :=
  H.mk (Submission.Cohomology.cupOf S R h (Quot.out x).1 (Quot.out y).1)
    (cupOf_mem_cycles (R := R) h (Quot.out x).2 (Quot.out y).2)

/-- The cup product of cohomology classes in degrees `p` and `q`. -/
noncomputable def H.cup (p q : ℕ) (x : H S R p) (y : H S R q) : H S R (p + q) :=
  H.cupOf rfl x y

/-- The unit class in degree `0`. -/
noncomputable def H.one : H S R 0 :=
  H.mk (oneCochain S R) (by
    rw [mem_cycles_iff]
    ext σ
    rw [coboundary_apply]
    simp [Fin.sum_univ_two, oneCochain])

end CupH

end

end Submission.Cohomology
