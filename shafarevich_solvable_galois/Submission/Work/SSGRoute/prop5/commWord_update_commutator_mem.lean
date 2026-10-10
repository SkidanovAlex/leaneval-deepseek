import Mathlib.GroupTheory.Nilpotent
import Submission.Work.SSGRoute.prop5.Basic
import Submission.Work.SSGRoute.prop5.commutator_lowerCentralSeries_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.prop5

open scoped commutatorElement

/-- A single commutator of arbitrary elements lies in `γ₁`. -/
lemma commutator_mem_lowerCentralSeries_one {P : Type*} [Group P] (a b : P) :
    ⁅a, b⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries 1 := by
  rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)

/-- **Weighted lower-central-series membership of the commutator word.**
If the `i`-th letter `y i` lies in `γ_{w i}`, then the `j`-fold commutator word lies in
`γ_{j + ∑ i, w i - 1}`. -/
theorem commWord_mem_lowerCentralSeries_weighted {P : Type*} [Group P] (j : ℕ)
    (y : Fin j → P) (w : Fin j → ℕ)
    (h : ∀ i, y i ∈ (⊤ : Subgroup P).lowerCentralSeries (w i)) :
    commWord j y ∈ (⊤ : Subgroup P).lowerCentralSeries ((∑ i, w i) + j - 1) := by
  match j, y, w with
  | 0, y, w => simp
  | 1, y, w =>
      rw [commWord_one]
      have hidx : (∑ i : Fin 1, w i) + 1 - 1 = w 0 := by
        rw [Fin.sum_univ_one]
        omega
      rw [hidx]
      exact h 0
  | (k + 2), y, w =>
      rw [commWord_succ_succ]
      have ih := commWord_mem_lowerCentralSeries_weighted (k + 1) (fun t => y t.succ)
        (fun t => w t.succ) (fun i => h i.succ)
      have hmem := commutator_lowerCentralSeries_le P (w 0)
        ((∑ t : Fin (k + 1), w t.succ) + (k + 1) - 1)
        (Subgroup.commutator_mem_commutator (h 0) ih)
      have hidx : w 0 + ((∑ t : Fin (k + 1), w t.succ) + (k + 1) - 1) + 1
          = (∑ i : Fin (k + 2), w i) + (k + 2) - 1 := by
        rw [Fin.sum_univ_succ (fun i : Fin (k + 2) => w i)]
        omega
      rw [hidx] at hmem
      exact hmem

open scoped commutatorElement in
theorem commWord_update_commutator_mem {P : Type*} [Group P] (j : ℕ) (hj : 1 ≤ j)
    (x : Fin j → P) (k : Fin j) (a b : P) :
    commWord j (Function.update x k ⁅a, b⁆) ∈ (⊤ : Subgroup P).lowerCentralSeries j := by
  have hw : ∀ i, (Function.update x k ⁅a, b⁆) i ∈
      (⊤ : Subgroup P).lowerCentralSeries (if i = k then 1 else 0) := by
    intro i
    by_cases hik : i = k
    · rw [hik]
      have : ⁅a, b⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries (1 : ℕ) :=
        commutator_mem_lowerCentralSeries_one a b
      simpa [Function.update_self] using this
    · rw [Function.update_of_ne hik]
      simp only [if_neg hik]
      exact Subgroup.mem_top _
  have hmem := commWord_mem_lowerCentralSeries_weighted j (Function.update x k ⁅a, b⁆)
    (fun i => if i = k then 1 else 0) hw
  have hsum : (∑ i : Fin j, (if i = k then 1 else 0 : ℕ)) = 1 :=
    Fintype.sum_ite_eq' k (fun _ => 1)
  have hidx : (∑ i : Fin j, (if i = k then 1 else 0 : ℕ)) + j - 1 = j := by
    rw [hsum]; omega
  rwa [hidx] at hmem

end Work.SSGRoute.prop5
