import Mathlib
import Submission.Work.RatHurewicz.FillFamilyDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Face commutation lemmas for the cubical `K`-operator

The consistency of the prescribed boundary data of the filling `K (ℓ+1) p` on the codimension two
skeleton needs the fact that "inserting the frozen values at two coordinates" does not depend on
the order of insertion, and likewise for the corresponding deletion maps.  This file proves these
identities.

* `val_succAbove`, `val_castPred`, `val_predAbove` — the numerical values of `Fin.succAbove`,
  `Fin.castPred` and `Fin.predAbove`;
* `succAbove_comp_eq` — the two composites of `succAbove`s describing a codimension two face agree
  (a pure computation in `Fin`);
* `delCM_comp_eq` — the same for the deletion maps `delCM`;
* `faceCM_comp_eq` — the dual statement for the face inclusions `faceCM`, obtained from the
  deletion statement by the fact that each composite is inverse to the corresponding double
  deletion on the codimension two face.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

theorem val_succAbove {n : ℕ} (p : Fin (n+1)) (i : Fin n) :
    ((p.succAbove i : Fin (n+1)) : ℕ) = if (i : ℕ) < (p : ℕ) then (i : ℕ) else (i : ℕ) + 1 := by
  rw [Fin.succAbove]
  by_cases h : (i : ℕ) < (p : ℕ)
  · rw [if_pos (show i.castSucc < p by rw [Fin.lt_def, Fin.val_castSucc]; exact h), if_pos h,
      Fin.val_castSucc]
  · rw [if_neg (show ¬ (i.castSucc < p) by rw [Fin.lt_def, Fin.val_castSucc]; exact h), if_neg h,
      Fin.val_succ]

theorem val_castPred {n : ℕ} (i : Fin (n+1)) (h : i ≠ Fin.last n) :
    ((i.castPred h : Fin n) : ℕ) = (i : ℕ) := by
  have h2 := Fin.val_castSucc (i.castPred h)
  rw [Fin.castSucc_castPred i h] at h2
  exact h2.symm

theorem val_predAbove {n : ℕ} (p : Fin n) (i : Fin (n+1)) :
    ((p.predAbove i : Fin n) : ℕ) = if (p : ℕ) < (i : ℕ) then (i : ℕ) - 1 else (i : ℕ) := by
  rw [Fin.predAbove]
  by_cases h : (p : ℕ) < (i : ℕ)
  · rw [dif_pos (show p.castSucc < i by rw [Fin.lt_def, Fin.val_castSucc]; exact h), if_pos h]
    exact Fin.val_pred i (by rintro rfl; simp at h)
  · rw [dif_neg (show ¬ (p.castSucc < i) by rw [Fin.lt_def, Fin.val_castSucc]; exact h),
      if_neg h, val_castPred]

theorem succAbove_comp_eq {n : ℕ} (j j' : Fin (n+1)) (hjj : j ≠ j') :
    (Fin.castSucc j).succAbove ∘ (j.predAbove (Fin.castSucc j')).succAbove
      = (Fin.castSucc j').succAbove ∘ (j'.predAbove (Fin.castSucc j)).succAbove := by
  funext x
  apply Fin.ext
  simp only [Function.comp_apply, val_succAbove, val_predAbove, Fin.val_castSucc]
  split_ifs <;> omega

theorem delCM_comp_eq {n : ℕ} (j j' : Fin (n+1)) (hjj : j ≠ j')
    {κ κ₂ : Fin (n+1)} (hκ : (Fin.castSucc j).succAbove κ = Fin.castSucc j')
    (hκ₂ : (Fin.castSucc j').succAbove κ₂ = Fin.castSucc j)
    {κ'' κ₂'' : Fin n} (hκ'' : (κ''.castSucc : Fin (n+1)) = κ)
    (hκ₂'' : (κ₂''.castSucc : Fin (n+1)) = κ₂) :
    (delCM n κ'').comp (delCM (n+1) j) = (delCM n κ₂'').comp (delCM (n+1) j') := by
  have hκ' : κ = j.predAbove (Fin.castSucc j') := by
    rw [← hκ]; exact (Fin.predAbove_succAbove j κ).symm
  have hκ₂' : κ₂ = j'.predAbove (Fin.castSucc j) := by
    rw [← hκ₂]; exact (Fin.predAbove_succAbove j' κ₂).symm
  have h := succAbove_comp_eq j j' hjj
  apply ContinuousMap.ext
  intro z
  funext x
  simp only [ContinuousMap.comp_apply, delCM_apply]
  rw [hκ'', hκ', hκ₂'', hκ₂']
  exact congrArg z (congrFun h x)

theorem faceCM_comp_eq {n : ℕ} (j j' : Fin (n+1)) (hjj : j ≠ j')
    {κ κ₂ : Fin (n+1)} (hκ : (Fin.castSucc j).succAbove κ = Fin.castSucc j')
    (hκ₂ : (Fin.castSucc j').succAbove κ₂ = Fin.castSucc j)
    {κ'' κ₂'' : Fin n} (hκ'' : (κ''.castSucc : Fin (n+1)) = κ)
    (hκ₂'' : (κ₂''.castSucc : Fin (n+1)) = κ₂)
    (b b' : unitInterval) :
    (faceCM (Fin.castSucc j) b).comp (faceCM (Fin.castSucc κ'') b')
      = (faceCM (Fin.castSucc j') b').comp (faceCM (Fin.castSucc κ₂'') b) := by
  have hD : (delCM n κ'').comp (delCM (n+1) j)
      = (delCM n κ₂'').comp (delCM (n+1) j') :=
    delCM_comp_eq j j' hjj hκ hκ₂ hκ'' hκ₂''
  have hround : ∀ w : IC n,
      ((delCM n κ'').comp (delCM (n+1) j))
        (((faceCM (Fin.castSucc j) b).comp (faceCM (Fin.castSucc κ'') b')) w) = w := by
    intro w
    simp only [ContinuousMap.comp_apply]
    rw [delCM_faceCM_castSucc (n+1) j b (faceCM (Fin.castSucc κ'') b' w),
      delCM_faceCM_castSucc n κ'' b' w]
  have hround₂ : ∀ w : IC n,
      ((delCM n κ₂'').comp (delCM (n+1) j'))
        (((faceCM (Fin.castSucc j') b').comp (faceCM (Fin.castSucc κ₂'') b)) w) = w := by
    intro w
    simp only [ContinuousMap.comp_apply]
    rw [delCM_faceCM_castSucc (n+1) j' b' (faceCM (Fin.castSucc κ₂'') b w),
      delCM_faceCM_castSucc n κ₂'' b w]
  have heta : ∀ z : IC (n+2), z (Fin.castSucc j) = b → z (Fin.castSucc j') = b' →
      ((faceCM (Fin.castSucc j) b).comp (faceCM (Fin.castSucc κ'') b'))
        (((delCM n κ'').comp (delCM (n+1) j)) z) = z := by
    intro z hz hz'
    have hX : (delCM (n+1) j z) (Fin.castSucc κ'') = b' := by
      rw [delCM_apply, hκ'', hκ, hz']
    simp only [ContinuousMap.comp_apply]
    rw [faceCM_delCM_of_apply n κ'' (delCM (n+1) j z) hX,
      faceCM_delCM_of_apply (n+1) j z hz]
  have hface : ∀ w : IC n,
      (((faceCM (Fin.castSucc j') b').comp (faceCM (Fin.castSucc κ₂'') b)) w)
        (Fin.castSucc j) = b := by
    intro w
    simp only [ContinuousMap.comp_apply]
    rw [faceCM_eq_insertNth, ← hκ₂, Fin.insertNth_apply_succAbove, faceCM_eq_insertNth,
      ← hκ₂'', Fin.insertNth_apply_same]
  have hface' : ∀ w : IC n,
      (((faceCM (Fin.castSucc j') b').comp (faceCM (Fin.castSucc κ₂'') b)) w)
        (Fin.castSucc j') = b' := by
    intro w
    simp only [ContinuousMap.comp_apply]
    rw [faceCM_eq_insertNth, Fin.insertNth_apply_same]
  apply ContinuousMap.ext
  intro w
  simp only [ContinuousMap.comp_apply]
  calc (faceCM (Fin.castSucc j) b) (faceCM (Fin.castSucc κ'') b' w)
      = (faceCM (Fin.castSucc j) b) (faceCM (Fin.castSucc κ'') b'
          (((delCM n κ'').comp (delCM (n+1) j))
            ((faceCM (Fin.castSucc j') b') (faceCM (Fin.castSucc κ₂'') b w)))) := by
        rw [show ((delCM n κ'').comp (delCM (n+1) j))
            ((faceCM (Fin.castSucc j') b') (faceCM (Fin.castSucc κ₂'') b w)) = w from by
          rw [hD]; exact hround₂ w]
    _ = (faceCM (Fin.castSucc j') b') (faceCM (Fin.castSucc κ₂'') b w) :=
        heta _ (hface w) (hface' w)


/-! ## The general (uniform) deletion and insertion identities -/

/-- The index of the coordinate `x` in the cube `I^{n+1}` after deleting the coordinate `p`
(so that `p.succAbove (predG p x h) = x`). -/
def predG {n : ℕ} (p : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ p) : Fin n :=
  if hp : (p : ℕ) < (x : ℕ) then
    ⟨(x : ℕ) - 1, by have := x.isLt; omega⟩
  else
    ⟨(x : ℕ), by
      have h1 : (x : ℕ) ≠ (p : ℕ) := fun hh => h (Fin.ext hh)
      have h2 : (x : ℕ) ≤ n := Nat.lt_succ_iff.mp x.isLt
      omega⟩

theorem val_predG {n : ℕ} (p : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ p) :
    (predG p x h : ℕ) = if (p : ℕ) < (x : ℕ) then (x : ℕ) - 1 else (x : ℕ) := by
  rw [predG]; split_ifs <;> rfl

theorem succAbove_predG {n : ℕ} (p : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ p) :
    p.succAbove (predG p x h) = x := by
  apply Fin.ext
  rw [val_succAbove, val_predG]
  have h1 : (x : ℕ) ≠ (p : ℕ) := fun hh => h (Fin.ext hh)
  split_ifs <;> omega

/-- Deleting two coordinates of `I^{n+2}` in the two possible orders gives the same map. -/
theorem delG_comp_eq {n : ℕ} (i i' : Fin (n + 2)) (h : i ≠ i') :
    (delG n (predG i i' h.symm)).comp (delG (n + 1) i)
      = (delG n (predG i' i h)).comp (delG (n + 1) i') := by
  have hh : (i : ℕ) ≠ (i' : ℕ) := fun h' => h (Fin.ext h')
  apply ContinuousMap.ext
  intro z
  funext x
  simp only [ContinuousMap.comp_apply, delG_apply]
  congr 1
  apply Fin.ext
  simp only [val_succAbove, val_predG]
  split_ifs <;> omega

/-- Inserting two frozen values into `I^n`, in the two possible orders, gives the same map. -/
theorem faceCM_comp_eq_gen {n : ℕ} (i i' : Fin (n + 2)) (h : i ≠ i') (b b' : unitInterval) :
    (faceCM i b).comp (faceCM (predG i i' h.symm) b')
      = (faceCM i' b').comp (faceCM (predG i' i h) b) := by
  have hD := delG_comp_eq i i' h
  have hround : ∀ w : IC n,
      ((delG n (predG i i' h.symm)).comp (delG (n + 1) i))
        (((faceCM i b).comp (faceCM (predG i i' h.symm) b')) w) = w := by
    intro w
    simp only [ContinuousMap.comp_apply]
    rw [faceCM_delG (n := n + 1) i b (faceCM (predG i i' h.symm) b' w),
      faceCM_delG (n := n) (predG i i' h.symm) b' w]
  have hround₂ : ∀ w : IC n,
      ((delG n (predG i' i h)).comp (delG (n + 1) i'))
        (((faceCM i' b').comp (faceCM (predG i' i h) b)) w) = w := by
    intro w
    simp only [ContinuousMap.comp_apply]
    rw [faceCM_delG (n := n + 1) i' b' (faceCM (predG i' i h) b w),
      faceCM_delG (n := n) (predG i' i h) b w]
  have heta : ∀ z : IC (n + 2), z i = b → z i' = b' →
      ((faceCM i b).comp (faceCM (predG i i' h.symm) b'))
        (((delG n (predG i i' h.symm)).comp (delG (n + 1) i)) z) = z := by
    intro z hz hz'
    have hX : (delG (n + 1) i z) (predG i i' h.symm) = b' := by
      rw [delG_apply, succAbove_predG, hz']
    simp only [ContinuousMap.comp_apply]
    rw [delG_faceCM (n := n) (predG i i' h.symm) (delG (n + 1) i z) hX,
      delG_faceCM (n := n + 1) i z hz]
  have hface : ∀ w : IC n,
      (((faceCM i' b').comp (faceCM (predG i' i h) b)) w) i = b := by
    intro w
    simp only [ContinuousMap.comp_apply]
    rw [show (faceCM i' b' (faceCM (predG i' i h) b w)) i
        = (faceCM i' b' (faceCM (predG i' i h) b w)) (i'.succAbove (predG i' i h)) from
      congrArg _ (succAbove_predG i' i h).symm]
    rw [faceCM_eq_insertNth, Fin.insertNth_apply_succAbove, faceCM_eq_insertNth,
      Fin.insertNth_apply_same]
  have hface' : ∀ w : IC n,
      (((faceCM i' b').comp (faceCM (predG i' i h) b)) w) i' = b' := by
    intro w
    simp only [ContinuousMap.comp_apply]
    rw [faceCM_eq_insertNth, Fin.insertNth_apply_same]
  apply ContinuousMap.ext
  intro w
  simp only [ContinuousMap.comp_apply]
  calc (faceCM i b) (faceCM (predG i i' h.symm) b' w)
      = (faceCM i b) (faceCM (predG i i' h.symm) b'
          (((delG n (predG i i' h.symm)).comp (delG (n + 1) i))
            ((faceCM i' b') (faceCM (predG i' i h) b w)))) := by
        rw [show ((delG n (predG i i' h.symm)).comp (delG (n + 1) i))
            ((faceCM i' b') (faceCM (predG i' i h) b w)) = w from by
          rw [hD]; exact hround₂ w]
    _ = (faceCM i' b') (faceCM (predG i' i h) b w) :=
        heta _ (hface w) (hface' w)

end

end Work.RatHurewicz
