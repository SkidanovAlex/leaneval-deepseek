import Mathlib
import Submission.Work.Cohomology.cup1Aux

/-!
# The shuffle identities for the cup-1 product

For an `(n+m)`-simplex `σ` and `0 ≤ s < m` the `s`-th summand of the cup-1 product pairs the
`n`-face `[s,s+n]` with the `m`-face `[0,s] ∪ [s+n, n+m-1]` (after deleting a vertex `k`).
The six identities here say what happens for the three regimes `k ≤ s`, `s < k ≤ s+n`,
`s+n < k`; they are the combinatorial heart of `δ(α ∪₁ β) = α ⌣ β - (-1)^{nm} β ⌣ α`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- The value of `p.succAbove i` in `ℕ`-terms. -/
lemma succAbove_val_if' {N : ℕ} (p : Fin (N+1)) (i : Fin N) :
    (p.succAbove i).val = if i.val < p.val then i.val else i.val + 1 := by
  rw [succAbove_val_if]
  by_cases h : i.val < p.val
  · rw [if_pos h, if_pos (by simp only [Fin.val_castSucc, Fin.lt_def]; omega)]
  · rw [if_neg h, if_neg (by simp only [Fin.val_castSucc, Fin.lt_def]; omega)]

/-- Regime `k ≤ s`: the front `n`-face becomes the `(s+1)`-st `n`-face. -/
lemma Fface_Del_le (n m k s : ℕ) (hk : k ≤ s) (hs : s + 1 ≤ m) :
    Fface n m s (by omega) ≫ Delmap n m k (by omega) = Amap n m (s+1) (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, Fface_val, Delmap_val_if, Amap_val]
  split_ifs <;> omega

/-- Regime `s+n < k`: the front `n`-face becomes the `s`-th `n`-face. -/
lemma Fface_Del_gt (n m k s : ℕ) (hk : s + n + 1 ≤ k) (hs : s + 1 ≤ m) :
    Fface n m s (by omega) ≫ Delmap n m k (by omega) = Amap n m s (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, Fface_val, Delmap_val_if, Amap_val]
  split_ifs <;> omega

/-- Regime `s < k ≤ s+n`: the front `n`-face becomes a face of the `(n+1)`-face `[s,s+n+1]`. -/
lemma Fface_Del_mid (n m k s : ℕ) (hk1 : s + 1 ≤ k) (hk2 : k ≤ s + n) (hs : s + 1 ≤ m) :
    Fface n m s (by omega) ≫ Delmap n m k (by omega)
      = SimplexCategory.δ (⟨k - s, by omega⟩ : Fin (n+2)) ≫ Wmap n m s (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, CategoryTheory.comp_apply, SimplexCategory.coe_δ,
    Fface_val, Delmap_val_if, Wmap_val, succAbove_val_if']
  split_ifs <;> omega

/-- Regime `k ≤ s`: the back `m`-face becomes a face of the `(m+1)`-face `[0,s+1] ∪ [s+n+1,n+m]`. -/
lemma Gface_Del_le (n m k s : ℕ) (hk : k ≤ s) (hs : s + 1 ≤ m) :
    Gface n m s (by omega) ≫ Delmap n m k (by omega)
      = SimplexCategory.δ (⟨k, by omega⟩ : Fin (m+2)) ≫ Qmap n m (s+1) (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, CategoryTheory.comp_apply, SimplexCategory.coe_δ,
    Gface_apply, Gfun_val_if, Delmap_val_if, Qmap_val_if, succAbove_val_if']
  split_ifs <;> omega

/-- Regime `s+n < k`: the back `m`-face becomes a face of the `(m+1)`-face `[0,s] ∪ [s+n,n+m]`. -/
lemma Gface_Del_gt (n m k s : ℕ) (hk1 : s + n + 1 ≤ k) (hk2 : k ≤ n + m) (hs : s + 1 ≤ m) :
    Gface n m s (by omega) ≫ Delmap n m k (by omega)
      = SimplexCategory.δ (⟨k - n + 1, by omega⟩ : Fin (m+2)) ≫ Qmap n m s (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, CategoryTheory.comp_apply, SimplexCategory.coe_δ,
    Gface_apply, Gfun_val_if, Delmap_val_if, Qmap_val_if, succAbove_val_if']
  split_ifs <;> omega

/-- Regime `s < k ≤ s+n`: the back `m`-face becomes the `m`-face `[0,s] ∪ [s+n+1,n+m]`. -/
lemma Gface_Del_mid (n m k s : ℕ) (hk1 : s + 1 ≤ k) (hk2 : k ≤ s + n) (hs : s + 1 ≤ m) :
    Gface n m s (by omega) ≫ Delmap n m k (by omega) = Ymap n m s (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, Gface_apply, Gfun_val_if, Delmap_val_if, Ymap_val_if]
  split_ifs <;> omega

end

end Work.Cohomology
