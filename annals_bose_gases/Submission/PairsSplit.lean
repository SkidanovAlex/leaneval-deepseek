import Mathlib.Algebra.BigOperators.Fin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Layer 2 helper (SubaddVol): splitting a sum over unordered pairs `{i<j}` in
`Fin (N1+N2)` into pairs inside the first block (`Fin N1`, embedded by
`Fin.castAdd N2`), pairs inside the second block (`Fin N2`, embedded by
`Fin.natAdd N1`), and cross pairs `(castAdd i, natAdd j)`.

This module is self-contained (pure Finset combinatorics over `Fin`).
-/

set_option autoImplicit false

namespace Submission.BoseGases

/-- Elements of the first block are smaller than elements of the second block. -/
lemma castAdd_lt_natAdd {N1 N2 : ℕ} (i : Fin N1) (j : Fin N2) :
    Fin.castAdd N2 i < Fin.natAdd N1 j := by
  change (Fin.castAdd N2 i).1 < (Fin.natAdd N1 j).1
  simp
  omega

/-- No element of the second block is smaller than an element of the first block. -/
lemma not_natAdd_lt_castAdd {N1 N2 : ℕ} (j : Fin N2) (i : Fin N1) :
    ¬ Fin.natAdd N1 j < Fin.castAdd N2 i := by
  change ¬ (Fin.natAdd N1 j).1 < (Fin.castAdd N2 i).1
  simp
  omega

/-- `Fin.castAdd` preserves the strict order. -/
lemma castAdd_lt_castAdd_iff {N1 N2 : ℕ} (i j : Fin N1) :
    (Fin.castAdd N2 i < Fin.castAdd N2 j) ↔ i < j := by
  constructor
  · intro h
    have hval : (i : ℕ) < (j : ℕ) := by
      change (Fin.castAdd N2 i).1 < (Fin.castAdd N2 j).1 at h
      simp at h
      exact h
    exact hval
  · intro h
    change (i : ℕ) < (j : ℕ) at h
    change (Fin.castAdd N2 i).1 < (Fin.castAdd N2 j).1
    simp
    exact h

/-- A sum over pairs `p.1 < p.2` equals the nested sum over the two indices with
the `if`-guard `i < j`. -/
lemma pair_sum_as_double {N : ℕ} {M : Type*} [AddCommMonoid M] (h : Fin N → Fin N → M) :
    (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)), h p.1 p.2)
    = (∑ i : Fin N, ∑ j : Fin N, if i < j then h i j else 0) := by
  rw [Finset.sum_filter]
  change (∑ p : Fin N × Fin N, if p.1 < p.2 then h p.1 p.2 else 0)
      = (∑ i : Fin N, ∑ j : Fin N, if i < j then h i j else 0)
  rw [Fintype.sum_prod_type]

/-- A double sum over `Fin (N1+N2) × Fin (N1+N2)` splits into the four blocks
(first, first), (first, second), (second, first) and (second, second). -/
lemma double_sum_split {N1 N2 : ℕ} {M : Type*} [AddCommMonoid M]
    (F : Fin (N1+N2) → Fin (N1+N2) → M) :
    (∑ a : Fin (N1+N2), ∑ b : Fin (N1+N2), F a b)
    = (∑ i₁ : Fin N1, ∑ i₂ : Fin N1, F (Fin.castAdd N2 i₁) (Fin.castAdd N2 i₂))
    + (∑ i₁ : Fin N1, ∑ j₂ : Fin N2, F (Fin.castAdd N2 i₁) (Fin.natAdd N1 j₂))
    + (∑ j₁ : Fin N2, ∑ i₂ : Fin N1, F (Fin.natAdd N1 j₁) (Fin.castAdd N2 i₂))
    + (∑ j₁ : Fin N2, ∑ j₂ : Fin N2, F (Fin.natAdd N1 j₁) (Fin.natAdd N1 j₂)) := by
  simp_rw [Fin.sum_univ_add, Finset.sum_add_distrib]
  ac_rfl

/-- Sums over pairs `{i<j}` in `Fin (N1+N2)` split into block 1, block 2 and cross pairs. -/
lemma sum_pairs_block_split {N1 N2 : ℕ} {M : Type*} [AddCommMonoid M]
    (g : Fin (N1+N2) → Fin (N1+N2) → M) :
    (∑ p ∈ (Finset.univ.filter (fun p : Fin (N1+N2) × Fin (N1+N2) => p.1 < p.2)), g p.1 p.2)
  = (∑ p ∈ (Finset.univ.filter (fun p : Fin N1 × Fin N1 => p.1 < p.2)),
        g (Fin.castAdd N2 p.1) (Fin.castAdd N2 p.2))
  + (∑ p ∈ (Finset.univ.filter (fun p : Fin N2 × Fin N2 => p.1 < p.2)),
        g (Fin.natAdd N1 p.1) (Fin.natAdd N1 p.2))
  + (∑ i : Fin N1, ∑ j : Fin N2, g (Fin.castAdd N2 i) (Fin.natAdd N1 j)) := by
  calc
    (∑ p ∈ (Finset.univ.filter (fun p : Fin (N1+N2) × Fin (N1+N2) => p.1 < p.2)), g p.1 p.2)
      = (∑ a : Fin (N1+N2), ∑ b : Fin (N1+N2), if a < b then g a b else 0) := by
        exact pair_sum_as_double g
    _ = (∑ i₁ : Fin N1, ∑ i₂ : Fin N1,
            if Fin.castAdd N2 i₁ < Fin.castAdd N2 i₂ then g (Fin.castAdd N2 i₁) (Fin.castAdd N2 i₂) else 0)
        + (∑ i₁ : Fin N1, ∑ j₂ : Fin N2,
            if Fin.castAdd N2 i₁ < Fin.natAdd N1 j₂ then g (Fin.castAdd N2 i₁) (Fin.natAdd N1 j₂) else 0)
        + (∑ j₁ : Fin N2, ∑ i₂ : Fin N1,
            if Fin.natAdd N1 j₁ < Fin.castAdd N2 i₂ then g (Fin.natAdd N1 j₁) (Fin.castAdd N2 i₂) else 0)
        + (∑ j₁ : Fin N2, ∑ j₂ : Fin N2,
            if Fin.natAdd N1 j₁ < Fin.natAdd N1 j₂ then g (Fin.natAdd N1 j₁) (Fin.natAdd N1 j₂) else 0) := by
        rw [double_sum_split (F := fun a b => if a < b then g a b else 0)]
    _ = (∑ i₁ : Fin N1, ∑ i₂ : Fin N1,
            if i₁ < i₂ then g (Fin.castAdd N2 i₁) (Fin.castAdd N2 i₂) else 0)
        + (∑ i₁ : Fin N1, ∑ j₂ : Fin N2, g (Fin.castAdd N2 i₁) (Fin.natAdd N1 j₂))
        + 0
        + (∑ j₁ : Fin N2, ∑ j₂ : Fin N2,
            if j₁ < j₂ then g (Fin.natAdd N1 j₁) (Fin.natAdd N1 j₂) else 0) := by
        simp [castAdd_lt_natAdd, not_natAdd_lt_castAdd, castAdd_lt_castAdd_iff]
    _ = (∑ p ∈ (Finset.univ.filter (fun p : Fin N1 × Fin N1 => p.1 < p.2)),
            g (Fin.castAdd N2 p.1) (Fin.castAdd N2 p.2))
        + (∑ p ∈ (Finset.univ.filter (fun p : Fin N2 × Fin N2 => p.1 < p.2)),
            g (Fin.natAdd N1 p.1) (Fin.natAdd N1 p.2))
        + (∑ i : Fin N1, ∑ j : Fin N2, g (Fin.castAdd N2 i) (Fin.natAdd N1 j)) := by
        rw [← pair_sum_as_double (fun i j => g (Fin.castAdd N2 i) (Fin.castAdd N2 j))]
        rw [← pair_sum_as_double (fun i j => g (Fin.natAdd N1 i) (Fin.natAdd N1 j))]
        simp
        ac_rfl

end Submission.BoseGases
