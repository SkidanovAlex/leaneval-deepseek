import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Pure finite-index combinatorics for the block split `Fin (a+b) ≃ Fin a ⊕ Fin b`.

The sum over ordered pairs `(p.1, p.2)` with `p.1 < p.2` in `Fin (a + b)` splits into:
pairs both in the first block `Fin a` (embedded by `Fin.castAdd b`), pairs both in the
second block `Fin b` (embedded by `Fin.natAdd a`), and cross pairs (first block, second
block).  This is the pair-sum bookkeeping behind the superadditivity of the box energy.
-/

namespace Submission.BoseGases

set_option autoImplicit false

open scoped BigOperators

/-! ## Helper facts used by the block split -/

/-- Elements of the first block are smaller than elements of the second block. -/
private lemma ps_castAdd_lt_natAdd {a b : ℕ} (i : Fin a) (j : Fin b) :
    Fin.castAdd b i < Fin.natAdd a j := by
  change (Fin.castAdd b i).1 < (Fin.natAdd a j).1
  simp
  omega

/-- No element of the second block is smaller than an element of the first block. -/
private lemma ps_not_natAdd_lt_castAdd {a b : ℕ} (j : Fin b) (i : Fin a) :
    ¬ Fin.natAdd a j < Fin.castAdd b i := by
  change ¬ (Fin.natAdd a j).1 < (Fin.castAdd b i).1
  simp
  omega

/-- `Fin.castAdd` preserves the strict order. -/
private lemma ps_castAdd_lt_castAdd_iff {a b : ℕ} (i j : Fin a) :
    (Fin.castAdd b i < Fin.castAdd b j) ↔ i < j := by
  constructor
  · intro h
    have hval : (i : ℕ) < (j : ℕ) := by
      change (Fin.castAdd b i).1 < (Fin.castAdd b j).1 at h
      simp at h
      exact h
    exact hval
  · intro h
    change (i : ℕ) < (j : ℕ) at h
    change (Fin.castAdd b i).1 < (Fin.castAdd b j).1
    simp
    exact h

/-- A sum over ordered pairs `p.1 < p.2` equals the nested sum over the two indices with
the `if`-guard `i < j`. -/
private lemma ps_pair_sum_as_double {N : ℕ} {M : Type*} [AddCommMonoid M]
    (h : Fin N → Fin N → M) :
    (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)), h p.1 p.2)
    = (∑ i : Fin N, ∑ j : Fin N, if i < j then h i j else 0) := by
  rw [Finset.sum_filter]
  change (∑ p : Fin N × Fin N, if p.1 < p.2 then h p.1 p.2 else 0)
      = (∑ i : Fin N, ∑ j : Fin N, if i < j then h i j else 0)
  rw [Fintype.sum_prod_type]

/-- A double sum over `Fin (a+b) × Fin (a+b)` splits into the four blocks
(first, first), (first, second), (second, first) and (second, second). -/
private lemma ps_double_sum_split {a b : ℕ} {M : Type*} [AddCommMonoid M]
    (F : Fin (a+b) → Fin (a+b) → M) :
    (∑ x : Fin (a+b), ∑ y : Fin (a+b), F x y)
    = (∑ i₁ : Fin a, ∑ i₂ : Fin a, F (Fin.castAdd b i₁) (Fin.castAdd b i₂))
    + (∑ i₁ : Fin a, ∑ j₂ : Fin b, F (Fin.castAdd b i₁) (Fin.natAdd a j₂))
    + (∑ j₁ : Fin b, ∑ i₂ : Fin a, F (Fin.natAdd a j₁) (Fin.castAdd b i₂))
    + (∑ j₁ : Fin b, ∑ j₂ : Fin b, F (Fin.natAdd a j₁) (Fin.natAdd a j₂)) := by
  simp_rw [Fin.sum_univ_add, Finset.sum_add_distrib]
  ac_rfl

/-- The block split, for a general additive target. -/
private lemma ps_pairSum_general {a b : ℕ} {α : Type*} [AddCommMonoid α]
    (f : Fin (a + b) → Fin (a + b) → α) :
    (∑ p ∈ (Finset.univ.filter (fun p : Fin (a+b) × Fin (a+b) => p.1 < p.2)), f p.1 p.2)
  = (∑ p ∈ (Finset.univ.filter (fun p : Fin a × Fin a => p.1 < p.2)),
        f (Fin.castAdd b p.1) (Fin.castAdd b p.2))
    + (∑ p ∈ (Finset.univ.filter (fun p : Fin b × Fin b => p.1 < p.2)),
        f (Fin.natAdd a p.1) (Fin.natAdd a p.2))
    + ∑ i : Fin a, ∑ j : Fin b, f (Fin.castAdd b i) (Fin.natAdd a j) := by
  calc
    (∑ p ∈ (Finset.univ.filter (fun p : Fin (a+b) × Fin (a+b) => p.1 < p.2)), f p.1 p.2)
      = (∑ x : Fin (a+b), ∑ y : Fin (a+b), if x < y then f x y else 0) := by
        exact ps_pair_sum_as_double (N := a + b) f
    _ = (∑ i₁ : Fin a, ∑ i₂ : Fin a,
            if Fin.castAdd b i₁ < Fin.castAdd b i₂ then f (Fin.castAdd b i₁) (Fin.castAdd b i₂) else 0)
        + (∑ i₁ : Fin a, ∑ j₂ : Fin b,
            if Fin.castAdd b i₁ < Fin.natAdd a j₂ then f (Fin.castAdd b i₁) (Fin.natAdd a j₂) else 0)
        + (∑ j₁ : Fin b, ∑ i₂ : Fin a,
            if Fin.natAdd a j₁ < Fin.castAdd b i₂ then f (Fin.natAdd a j₁) (Fin.castAdd b i₂) else 0)
        + (∑ j₁ : Fin b, ∑ j₂ : Fin b,
            if Fin.natAdd a j₁ < Fin.natAdd a j₂ then f (Fin.natAdd a j₁) (Fin.natAdd a j₂) else 0) := by
        exact ps_double_sum_split (a := a) (b := b)
          (F := fun x y : Fin (a + b) => if x < y then f x y else 0)
    _ = ((∑ i₁ : Fin a, ∑ i₂ : Fin a,
            if i₁ < i₂ then f (Fin.castAdd b i₁) (Fin.castAdd b i₂) else 0)
        + (∑ i₁ : Fin a, ∑ j₂ : Fin b, f (Fin.castAdd b i₁) (Fin.natAdd a j₂)))
        + (∑ j₁ : Fin b, ∑ j₂ : Fin b,
            if j₁ < j₂ then f (Fin.natAdd a j₁) (Fin.natAdd a j₂) else 0) := by
        simp [ps_castAdd_lt_natAdd, ps_not_natAdd_lt_castAdd, ps_castAdd_lt_castAdd_iff]
    _ = ((∑ p ∈ (Finset.univ.filter (fun p : Fin a × Fin a => p.1 < p.2)),
            f (Fin.castAdd b p.1) (Fin.castAdd b p.2))
        + (∑ i₁ : Fin a, ∑ j₂ : Fin b, f (Fin.castAdd b i₁) (Fin.natAdd a j₂)))
        + (∑ p ∈ (Finset.univ.filter (fun p : Fin b × Fin b => p.1 < p.2)),
            f (Fin.natAdd a p.1) (Fin.natAdd a p.2)) := by
        rw [← ps_pair_sum_as_double (N := a) (h := fun i j => f (Fin.castAdd b i) (Fin.castAdd b j))]
        rw [← ps_pair_sum_as_double (N := b) (h := fun i j => f (Fin.natAdd a i) (Fin.natAdd a j))]
    _ = (∑ p ∈ (Finset.univ.filter (fun p : Fin a × Fin a => p.1 < p.2)),
            f (Fin.castAdd b p.1) (Fin.castAdd b p.2))
        + (∑ p ∈ (Finset.univ.filter (fun p : Fin b × Fin b => p.1 < p.2)),
            f (Fin.natAdd a p.1) (Fin.natAdd a p.2))
        + ∑ i : Fin a, ∑ j : Fin b, f (Fin.castAdd b i) (Fin.natAdd a j) := by
        ac_rfl

/-- The sum over ordered pairs `i < j` of `Fin (a+b)` splits into the two blocks and the
cross pairs. -/
lemma pairSum_eq_blocks {a b : ℕ} (f : Fin (a + b) → Fin (a + b) → ℝ) :
    (∑ p ∈ (Finset.univ.filter (fun p : Fin (a+b) × Fin (a+b) => p.1 < p.2)), f p.1 p.2)
  = (∑ p ∈ (Finset.univ.filter (fun p : Fin a × Fin a => p.1 < p.2)),
        f (Fin.castAdd b p.1) (Fin.castAdd b p.2))
    + (∑ p ∈ (Finset.univ.filter (fun p : Fin b × Fin b => p.1 < p.2)),
        f (Fin.natAdd a p.1) (Fin.natAdd a p.2))
    + ∑ i : Fin a, ∑ j : Fin b, f (Fin.castAdd b i) (Fin.natAdd a j) := by
  exact ps_pairSum_general f

/-- Variant with a general additive target. -/
lemma pairSum_eq_blocks' {a b : ℕ} {α : Type*} [AddCommMonoid α]
    (f : Fin (a + b) → Fin (a + b) → α) :
    (∑ p ∈ (Finset.univ.filter (fun p : Fin (a+b) × Fin (a+b) => p.1 < p.2)), f p.1 p.2)
  = (∑ p ∈ (Finset.univ.filter (fun p : Fin a × Fin a => p.1 < p.2)),
        f (Fin.castAdd b p.1) (Fin.castAdd b p.2))
    + (∑ p ∈ (Finset.univ.filter (fun p : Fin b × Fin b => p.1 < p.2)),
        f (Fin.natAdd a p.1) (Fin.natAdd a p.2))
    + ∑ i : Fin a, ∑ j : Fin b, f (Fin.castAdd b i) (Fin.natAdd a j) := by
  exact ps_pairSum_general f

end Submission.BoseGases
