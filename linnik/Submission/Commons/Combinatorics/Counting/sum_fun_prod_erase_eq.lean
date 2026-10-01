import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

namespace Commons.Combinatorics.Counting

open Finset
open scoped BigOperators

/-- The complement of the point `i` inside `ι`, as a subtype of `ι`; this is the index type of the
"free" coordinates of a function `ι → α` once the value at `i` has been fixed. -/
abbrev EraseFiber {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) : Type _ :=
  {j : ι // j ∈ (Finset.univ.erase i : Finset ι)}

/-- A function `ι → α` is determined by its value at `i` together with its restriction to the
remaining coordinates, giving the equivalence `(ι → α) ≃ α × (EraseFiber i → α)`. -/
noncomputable def eraseEquiv (ι α : Type*) [Fintype ι] [DecidableEq ι] (i : ι) :
    (ι → α) ≃ α × (EraseFiber i → α) where
  toFun w := (w i, fun j => w j.1)
  invFun p := fun j => if h : j = i then p.1 else p.2 ⟨j, by simp [Finset.mem_erase, h]⟩
  left_inv w := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  right_inv p := by
    obtain ⟨u, g⟩ := p
    refine Prod.ext ?_ ?_
    · simp
    · funext j
      have hj : (j : ι) ≠ i := (Finset.mem_erase.mp j.2).1
      simp only [hj, dif_neg, not_false_iff]

/-- Sum over functions of a product over all but one coordinate factors as a power of the
single-variable sum: `∑_{w : ι → α} ∏_{j ≠ i} h (w i) (w j) = ∑_{u : α} (∑_{v : α} h u v)^(|ι|-1)`. -/
theorem sum_fun_prod_erase_eq {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (i : ι) (h : α → α → ℝ) :
    (∑ w : ι → α, ∏ j ∈ (Finset.univ.erase i), h (w i) (w j))
      = ∑ u : α, (∑ v : α, h u v) ^ (Fintype.card ι - 1) := by
  classical
  have hcard : Fintype.card (EraseFiber i) = Fintype.card ι - 1 := by
    have h1 : Fintype.card (EraseFiber i) = (Finset.univ.erase i).card := by
      rw [← Finset.card_univ, Finset.univ_eq_attach, Finset.card_attach]
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  calc
    (∑ w : ι → α, ∏ j ∈ (Finset.univ.erase i), h (w i) (w j))
        = ∑ p : α × (EraseFiber i → α),
            ∏ j : EraseFiber i, h p.1 (p.2 j) := by
          rw [Fintype.sum_equiv (eraseEquiv ι α i)
                (fun w : ι → α => ∏ j ∈ (Finset.univ.erase i), h (w i) (w j))
                (fun p : α × (EraseFiber i → α) => ∏ j : EraseFiber i, h p.1 (p.2 j))]
          intro w
          change (∏ j ∈ Finset.univ.erase i, h (w i) (w j))
              = ∏ j : EraseFiber i, h (w i) (w j.1)
          rw [Finset.prod_subtype (Finset.univ.erase i) (fun x => Iff.rfl)]
    _ = ∑ u : α, ∑ g : EraseFiber i → α, ∏ j : EraseFiber i, h u (g j) :=
          Fintype.sum_prod_type _
    _ = ∑ u : α, (∑ v : α, h u v) ^ (Fintype.card ι - 1) := by
          apply Finset.sum_congr rfl
          intro u _
          have hpu : (∑ g : EraseFiber i → α, ∏ j : EraseFiber i, h u (g j))
              = (∑ v : α, h u v) ^ Fintype.card (EraseFiber i) := by
            rw [← Fintype.prod_sum (f := fun (_ : EraseFiber i) (v : α) => h u v)]
            rw [Finset.prod_const, Finset.card_univ]
          rw [hpu, hcard]

end Commons.Combinatorics.Counting