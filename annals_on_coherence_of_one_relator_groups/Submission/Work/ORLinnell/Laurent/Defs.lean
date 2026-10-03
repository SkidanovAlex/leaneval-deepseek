/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.ORLinnell
-/
import Mathlib
import Submission.Work.ORLinnell.Linnell

/-!
# The Laurent decomposition attached to `N ◁ H` with `H/N` cyclic

Let `N ≤ H ≤ G`, `N` normal in `H`, and let `s : H` be an element whose powers form a set of
coset representatives (up to `N`) of `H/N`, i.e. satisfy

`∀ h : H, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf H`.

For a Linnell datum `L : LinnellDatum K G U` we write `laurentBasis L s j = (s ^ j : U)` for the
image of `s ^ j` in `U`, and `laurentSum L s c` for a formal sum `Σ_j d_j * s ^ j`, `d_j ∈ D N`,
with `c : ℤ →₀ ↥(L.D N)`.

This file collects the elementary algebra of these objects.  The two substantive facts are that
`laurentSum` is multiplicative and that it is injective on coefficients (Linnell independence);
they are proved in the sibling files `laurent_mul` and `laurent_unique` and assembled in
`existsUnique_laurent_rep`.
-/

namespace Work.ORLinnell.Laurent

open Work.ORLinnell

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Nontrivial U]
  [Algebra K U]

/-- The image in `U` of the group element `s ^ j` of `H`, where `s : H`. -/
noncomputable def laurentBasis (L : LinnellDatum K G U) {H : Subgroup G} (s : H) (j : ℤ) : U :=
  (L.gen ((s ^ j : H) : G) : U)

/-- The formal Laurent sum `Σ_j d_j s ^ j`, for `c : ℤ →₀ ↥(D N)` the finitely supported family
of coefficients `d_j`. -/
noncomputable def laurentSum (L : LinnellDatum K G U) {N H : Subgroup G} (s : H)
    (c : ℤ →₀ ↥(L.D N)) : U :=
  c.sum (fun j d => (d : U) * laurentBasis L s j)

variable {L : LinnellDatum K G U} {H : Subgroup G} {s : H}

@[simp] theorem laurentBasis_zero : laurentBasis L s (0 : ℤ) = 1 := by
  simp [laurentBasis]

@[simp] theorem laurentBasis_one : laurentBasis L s (1 : ℤ) = (L.gen (s : G) : U) := by
  simp [laurentBasis]

theorem laurentBasis_add (i j : ℤ) :
    laurentBasis L s (i + j) = laurentBasis L s i * laurentBasis L s j := by
  simp only [laurentBasis]
  rw [show ((s ^ (i + j) : H) : G) = ((s ^ i : H) : G) * ((s ^ j : H) : G) from by
    rw [zpow_add]; rfl]
  simp

theorem laurentBasis_mul_neg (j : ℤ) : laurentBasis L s j * laurentBasis L s (-j) = 1 := by
  rw [← laurentBasis_add]; simp

theorem laurentBasis_neg_mul (j : ℤ) : laurentBasis L s (-j) * laurentBasis L s j = 1 := by
  rw [← laurentBasis_add]; simp

/-- Conjugation by `s ^ j` preserves `D N` (normality of `N` in `H`). -/
theorem laurentBasis_conj_mem {N : Subgroup G} (hH : N ≤ H) (hN : (N.subgroupOf H).Normal)
    (j : ℤ) (d : ↥(L.D N)) :
    laurentBasis L s j * (d : U) * laurentBasis L s (-j) ∈ L.D N := by
  have key : ((s ^ (-j) : H) : G) = ((s ^ j : H) : G)⁻¹ := by rw [zpow_neg]; rfl
  have h := L.conj_mem hH hN (s ^ j) (d : U) d.2
  simpa only [laurentBasis, key, map_inv, Units.val_inv_eq_inv_val] using h

/-- The conjugation of a coefficient, as an element of `D N`. -/
theorem exists_conj_mem {N : Subgroup G} (hH : N ≤ H) (hN : (N.subgroupOf H).Normal)
    (j : ℤ) (d : ↥(L.D N)) :
    ∃ e : ↥(L.D N), (e : U) = laurentBasis L s j * (d : U) * laurentBasis L s (-j) :=
  ⟨⟨_, laurentBasis_conj_mem hH hN j d⟩, rfl⟩

/-- `laurentSum` is definitionally the finsupp sum appearing in the statements. -/
theorem laurentSum_eq {N : Subgroup G} (c : ℤ →₀ ↥(L.D N)) :
    laurentSum L s c =
      c.sum (fun j d => (d : U) * (L.gen ((s ^ j : H) : G) : U)) :=
  rfl

theorem laurentSum_single {N : Subgroup G} (j : ℤ) (d : ↥(L.D N)) :
    laurentSum L s (Finsupp.single j d) = (d : U) * laurentBasis L s j := by
  rw [laurentSum, Finsupp.sum_single_index (by simp)]

theorem laurentSum_zero {N : Subgroup G} : laurentSum L s (0 : ℤ →₀ ↥(L.D N)) = 0 := by
  rw [laurentSum, Finsupp.sum_zero_index]

theorem laurentSum_add {N : Subgroup G} (c c' : ℤ →₀ ↥(L.D N)) :
    laurentSum L s (c + c') = laurentSum L s c + laurentSum L s c' := by
  rw [laurentSum, Finsupp.sum_add_index (by simp) (by intro a _ b₁ b₂; simp [add_mul])]
  simp [laurentSum]

theorem laurentSum_neg {N : Subgroup G} (c : ℤ →₀ ↥(L.D N)) :
    laurentSum L s (-c) = -(laurentSum L s c) := by
  have h : (-c : ℤ →₀ ↥(L.D N)) = 0 - c := by rw [zero_sub]
  rw [h, laurentSum, laurentSum, Finsupp.sum_sub_index (by intro a b₁ b₂; simp [sub_mul])]
  rw [Finsupp.sum_zero_index, zero_sub]

theorem laurentSum_sub {N : Subgroup G} (c c' : ℤ →₀ ↥(L.D N)) :
    laurentSum L s (c - c') = laurentSum L s c - laurentSum L s c' := by
  rw [sub_eq_add_neg, laurentSum_add, laurentSum_neg, sub_eq_add_neg]

/-- The single term `d * s ^ 0` for `d ∈ D N`. -/
theorem laurentSum_of_mem {N : Subgroup G} {x : U} (hx : x ∈ L.D N) :
    ∃ c : ℤ →₀ ↥(L.D N), laurentSum L s c = x :=
  ⟨Finsupp.single 0 ⟨x, hx⟩, by rw [laurentSum_single, laurentBasis_zero, mul_one]⟩

/-- Every element of `H` is a single `D N`-multiple of a power of `s`. -/
theorem laurentSum_gen {N : Subgroup G} (hs : ∀ h : H, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf H)
    (h : H) : ∃ c : ℤ →₀ ↥(L.D N), laurentSum L s c = (L.gen (h : G) : U) := by
  obtain ⟨j, hj⟩ := hs h
  set n : H := h * s ^ (-j) with hn
  have hj' : (n : G) ∈ N := by
    rw [hn]; exact Subgroup.mem_subgroupOf.mp hj
  have hns : n * s ^ j = h := by
    rw [hn, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  refine ⟨Finsupp.single j ⟨(L.gen (n : G) : U), ?_⟩, ?_⟩
  · simpa using L.gen_mem N ⟨n, hj'⟩
  · rw [laurentSum_single]
    simp only [laurentBasis]
    have hprod : (n : G) * ((s ^ j : H) : G) = (h : G) := by
      rw [← Subgroup.coe_mul]; exact congrArg (fun x : H => (x : G)) hns
    have hgen : L.gen (n : G) * L.gen ((s ^ j : H) : G) = L.gen (h : G) := by
      rw [← map_mul, hprod]
    rw [← Units.val_mul, hgen]

end Work.ORLinnell.Laurent
