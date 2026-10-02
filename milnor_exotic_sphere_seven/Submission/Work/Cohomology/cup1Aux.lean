import Mathlib
import Submission.Work.Cohomology.cup1defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary order maps for the cup-1 identity

Combinatorial skeleton for the cochain-level identity `δ(α ∪₁ β) = α ⌣ β - (-1)^{nm} β ⌣ α`
(for cocycles `α`, `β`) of `Submission/Work/Cohomology/cup1defs.lean`.

For an `(n+m)`-simplex `σ` the relevant faces are

* `[t, t+n]`             (`Amap`, an `n`-simplex)     for `0 ≤ t ≤ m`,
* `[0,t] ∪ [t+n, n+m]`   (`Qmap`, an `(m+1)`-simplex) for `0 ≤ t ≤ m`,
* `[s, s+n+1]`           (`Wmap`, an `(n+1)`-simplex) for `0 ≤ s < m`,
* `[0,s] ∪ [s+n+1, n+m]` (`Ymap`, an `m`-simplex)     for `0 ≤ s < m`,
* deletion of the vertex `k` (`Delmap`).

The main content is the composition identities `Fface s ≫ Delmap k` and `Gface s ≫ Delmap k`
in the three regimes `k ≤ s`, `s < k ≤ s+n`, `s+n < k`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## The auxiliary order maps -/

/-- The `n`-face `[t, t+n]` of an `(n+m)`-simplex, as `⦋n⦌ ⟶ ⦋n+m⦌`. -/
def Amap (n m t : ℕ) (h : t ≤ m) : ⦋n⦌ ⟶ ⦋n+m⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun (i : Fin (n+1)) =>
        (⟨t + i.val, by have := i.isLt; have := h; omega⟩ : Fin (n+m+1))
      monotone' := fun _ _ hij => by simp only [Fin.le_def] at hij ⊢; omega }

/-- The `(m+1)`-simplex `[0,t] ∪ [t+n, n+m]` of an `(n+m)`-simplex. -/
def Qmap (n m t : ℕ) (h : t ≤ m) : ⦋m+1⦌ ⟶ ⦋n+m⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun (j : Fin (m+2)) =>
        if hj : j.val ≤ t then (⟨j.val, by have := j.isLt; have := h; omega⟩ : Fin (n+m+1))
        else (⟨j.val + n - 1, by have := j.isLt; have := h; omega⟩ : Fin (n+m+1))
      monotone' := fun _ _ hij => by
        simp only [Fin.le_def] at hij ⊢
        split_ifs with h1 h2 h2 <;> simp only [Fin.le_def] <;> omega }

/-- The `(n+1)`-simplex `[s, s+n+1]` of an `(n+m)`-simplex. -/
def Wmap (n m s : ℕ) (h : s + 1 ≤ m) : ⦋n+1⦌ ⟶ ⦋n+m⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun (i : Fin (n+2)) =>
        (⟨s + i.val, by have := i.isLt; have := h; omega⟩ : Fin (n+m+1))
      monotone' := fun _ _ hij => by simp only [Fin.le_def] at hij ⊢; omega }

/-- The `m`-simplex `[0,s] ∪ [s+n+1, n+m]` of an `(n+m)`-simplex. -/
def Ymap (n m s : ℕ) (h : s + 1 ≤ m) : ⦋m⦌ ⟶ ⦋n+m⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun (j : Fin (m+1)) =>
        if hj : j.val ≤ s then (⟨j.val, by have := j.isLt; have := h; omega⟩ : Fin (n+m+1))
        else (⟨j.val + n, by have := j.isLt; have := h; omega⟩ : Fin (n+m+1))
      monotone' := fun _ _ hij => by
        simp only [Fin.le_def] at hij ⊢
        split_ifs with h1 h2 h2 <;> simp only [Fin.le_def] <;> omega }

/-- The order map `⦋n+m-1⦌ ⟶ ⦋n+m⦌` skipping the vertex `k`. -/
def Delmap (n m k : ℕ) (h : 1 ≤ n + m) : ⦋n+m-1⦌ ⟶ ⦋n+m⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun (j : Fin (n+m-1+1)) =>
        if _hj : j.val < k then (⟨j.val, by have := j.isLt; have := h; omega⟩ : Fin (n+m+1))
        else (⟨j.val + 1, by have := j.isLt; have := h; omega⟩ : Fin (n+m+1))
      monotone' := fun _ _ hij => by
        simp only [Fin.le_def] at hij ⊢
        split_ifs with h1 h2 h2 <;> simp only [Fin.le_def] <;> omega }

/-! ## Value lemmas -/

@[simp] lemma Amap_val (n m t : ℕ) (h : t ≤ m) (i : Fin (n+1)) :
    ((ConcreteCategory.hom (Amap n m t h)) i).val = t + i.val := rfl

@[simp] lemma Qmap_apply (n m t : ℕ) (h : t ≤ m) (j : Fin (m+2)) :
    ((ConcreteCategory.hom (Qmap n m t h)) j) = Gfun n (m+1) t (by omega) j := rfl

lemma Qmap_val_le (n m t : ℕ) (h : t ≤ m) (j : Fin (m+2)) (hj : j.val ≤ t) :
    ((ConcreteCategory.hom (Qmap n m t h)) j).val = j.val := by
  rw [Qmap_apply, Gfun_val_le n (m+1) t (by omega) j hj]

lemma Qmap_val_gt (n m t : ℕ) (h : t ≤ m) (j : Fin (m+2)) (hj : t < j.val) :
    ((ConcreteCategory.hom (Qmap n m t h)) j).val = j.val + n - 1 := by
  rw [Qmap_apply, Gfun_val_gt n (m+1) t (by omega) j hj]

@[simp] lemma Wmap_val (n m s : ℕ) (h : s + 1 ≤ m) (i : Fin (n+2)) :
    ((ConcreteCategory.hom (Wmap n m s h)) i).val = s + i.val := rfl

lemma Ymap_val_le (n m s : ℕ) (h : s + 1 ≤ m) (j : Fin (m+1)) (hj : j.val ≤ s) :
    ((ConcreteCategory.hom (Ymap n m s h)) j).val = j.val := by
  rw [show ((ConcreteCategory.hom (Ymap n m s h)) j)
    = (if _hj : j.val ≤ s then (⟨j.val, by have := j.isLt; have := h; omega⟩ : Fin (n+m+1))
        else (⟨j.val + n, by have := j.isLt; have := h; omega⟩ : Fin (n+m+1))) from rfl]
  rw [dif_pos hj]

lemma Ymap_val_gt (n m s : ℕ) (h : s + 1 ≤ m) (j : Fin (m+1)) (hj : s < j.val) :
    ((ConcreteCategory.hom (Ymap n m s h)) j).val = j.val + n := by
  rw [show ((ConcreteCategory.hom (Ymap n m s h)) j)
    = (if _hj : j.val ≤ s then (⟨j.val, by have := j.isLt; have := h; omega⟩ : Fin (n+m+1))
        else (⟨j.val + n, by have := j.isLt; have := h; omega⟩ : Fin (n+m+1))) from rfl]
  rw [dif_neg (by omega)]

lemma Delmap_val_lt (n m k : ℕ) (h : 1 ≤ n + m) (j : Fin (n+m-1+1)) (hj : j.val < k) :
    ((ConcreteCategory.hom (Delmap n m k h)) j).val = j.val := by
  rw [show ((ConcreteCategory.hom (Delmap n m k h)) j)
    = (if _hj : j.val < k then (⟨j.val, by have := j.isLt; have := h; omega⟩ : Fin (n+m+1))
        else (⟨j.val + 1, by have := j.isLt; have := h; omega⟩ : Fin (n+m+1))) from rfl]
  rw [dif_pos hj]

lemma Delmap_val_ge (n m k : ℕ) (h : 1 ≤ n + m) (j : Fin (n+m-1+1)) (hj : k ≤ j.val) :
    ((ConcreteCategory.hom (Delmap n m k h)) j).val = j.val + 1 := by
  rw [show ((ConcreteCategory.hom (Delmap n m k h)) j)
    = (if _hj : j.val < k then (⟨j.val, by have := j.isLt; have := h; omega⟩ : Fin (n+m+1))
        else (⟨j.val + 1, by have := j.isLt; have := h; omega⟩ : Fin (n+m+1))) from rfl]
  rw [dif_neg (by omega)]



/-- The morphism `⦋p⦌ ⟶ ⦋q⦌` attached to an equality of lengths (identity on labels). -/
def shmap (p q : ℕ) (h : p = q) : ⦋p⦌ ⟶ ⦋q⦌ := eqToHom (congrArg SimplexCategory.mk h)

lemma shmap_val (p q : ℕ) (h : p = q) (i : Fin (p+1)) :
    ((ConcreteCategory.hom (shmap p q h)) i).val = i.val :=
  coe_eqToHom_mk h i

/-! ## Function-form value lemmas -/

lemma Amap_hom (n m t : ℕ) (h : t ≤ m) (i : Fin (n+1)) :
    (ConcreteCategory.hom (Amap n m t h)) i
      = (⟨t + i.val, by have := i.isLt; have := h; omega⟩ : Fin (n+m+1)) := rfl

lemma Wmap_hom (n m s : ℕ) (h : s + 1 ≤ m) (i : Fin (n+2)) :
    (ConcreteCategory.hom (Wmap n m s h)) i
      = (⟨s + i.val, by have := i.isLt; have := h; omega⟩ : Fin (n+m+1)) := rfl

lemma Qmap_hom (n m t : ℕ) (h : t ≤ m) (j : Fin (m+2)) :
    (ConcreteCategory.hom (Qmap n m t h)) j
      = (if hj : j.val ≤ t then (⟨j.val, by have := j.isLt; have := h; omega⟩ : Fin (n+m+1))
          else (⟨j.val + n - 1, by have := j.isLt; have := h; omega⟩ : Fin (n+m+1))) := rfl

lemma Ymap_hom (n m s : ℕ) (h : s + 1 ≤ m) (j : Fin (m+1)) :
    (ConcreteCategory.hom (Ymap n m s h)) j
      = (if hj : j.val ≤ s then (⟨j.val, by have := j.isLt; have := h; omega⟩ : Fin (n+m+1))
          else (⟨j.val + n, by have := j.isLt; have := h; omega⟩ : Fin (n+m+1))) := rfl

lemma Delmap_hom (n m k : ℕ) (h : 1 ≤ n + m) (j : Fin (n+m-1+1)) :
    (ConcreteCategory.hom (Delmap n m k h)) j
      = (if _hj : j.val < k then (⟨j.val, by have := j.isLt; have := h; omega⟩ : Fin (n+m+1))
          else (⟨j.val + 1, by have := j.isLt; have := h; omega⟩ : Fin (n+m+1))) := rfl

lemma Fface_hom (n m s : ℕ) (h : s + n ≤ n + m - 1) (i : Fin (n+1)) :
    (ConcreteCategory.hom (Fface n m s h)) i
      = (⟨s + i.val, by have := i.isLt; omega⟩ : Fin (n+m-1+1)) := rfl

lemma Gfun_eq (n m s : ℕ) (h : s + n ≤ n + m - 1) (j : Fin (m+1)) (hj : j.val ≤ s) :
    Gfun n m s h j = (⟨j.val, by have := j.isLt; omega⟩ : Fin (n+m-1+1)) := by
  apply Fin.ext
  rw [Gfun_val_le n m s h j hj]

lemma Gfun_eq' (n m s : ℕ) (h : s + n ≤ n + m - 1) (j : Fin (m+1)) (hj : s < j.val) :
    Gfun n m s h j = (⟨j.val + n - 1, by have := j.isLt; omega⟩ : Fin (n+m-1+1)) := by
  apply Fin.ext
  rw [Gfun_val_gt n m s h j hj]

/-! ## `ℕ`-valued conditional forms -/

lemma Gfun_val_if (n m s : ℕ) (h : s + n ≤ n + m - 1) (j : Fin (m+1)) :
    (Gfun n m s h j).val = if j.val ≤ s then j.val else j.val + n - 1 := by
  by_cases hj : j.val ≤ s
  · rw [if_pos hj, Gfun_val_le n m s h j hj]
  · rw [if_neg hj, Gfun_val_gt n m s h j (by omega)]

lemma Delmap_val_if (n m k : ℕ) (h : 1 ≤ n+m) (j : Fin (n+m-1+1)) :
    ((ConcreteCategory.hom (Delmap n m k h)) j).val = if j.val < k then j.val else j.val + 1 := by
  by_cases hj : j.val < k
  · rw [if_pos hj, Delmap_val_lt n m k h j hj]
  · rw [if_neg hj, Delmap_val_ge n m k h j (by omega)]

lemma Qmap_val_if (n m t : ℕ) (h : t ≤ m) (j : Fin (m+2)) :
    ((ConcreteCategory.hom (Qmap n m t h)) j).val = if j.val ≤ t then j.val else j.val + n - 1 := by
  by_cases hj : j.val ≤ t
  · rw [if_pos hj, Qmap_val_le n m t h j hj]
  · rw [if_neg hj, Qmap_val_gt n m t h j (by omega)]

lemma Ymap_val_if (n m s : ℕ) (h : s + 1 ≤ m) (j : Fin (m+1)) :
    ((ConcreteCategory.hom (Ymap n m s h)) j).val = if j.val ≤ s then j.val else j.val + n := by
  by_cases hj : j.val ≤ s
  · rw [if_pos hj, Ymap_val_le n m s h j hj]
  · rw [if_neg hj, Ymap_val_gt n m s h j (by omega)]

lemma succAbove_val_if {N : ℕ} (p : Fin (N+1)) (i : Fin N) :
    (p.succAbove i).val = if i.castSucc < p then i.val else i.val + 1 := by
  by_cases h : i.castSucc < p
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt p i h, Fin.val_castSucc]
  · rw [if_neg h, Fin.succAbove_of_le_castSucc p i (by omega), Fin.val_succ]

end

end Work.Cohomology
