import Mathlib

/-!
Auxiliary definitions for `Work.KT.hk_idem_C`.

Given `r ≤ n`, we identify `(Fin r → ℂ) × (Fin (n - r) → ℂ)` with `Fin n → ℂ`
by putting the first block in the coordinates `0, …, r-1` and the second block
in the coordinates `r, …, n-1`.
-/

namespace Work.KT

/-- The function sending a pair of functions to the function on `Fin n` whose
first `r` coordinates are the first component and whose remaining coordinates
are the second component. -/
noncomputable def combineFun (n r : ℕ) (hr : r ≤ n)
    (fg : (Fin r → ℂ) × (Fin (n - r) → ℂ)) : Fin n → ℂ :=
  fun i => if h : (i : ℕ) < r then fg.1 ⟨i, h⟩ else fg.2 ⟨(i : ℕ) - r, by omega⟩

@[simp] theorem combineFun_apply (n r : ℕ) (hr : r ≤ n)
    (fg : (Fin r → ℂ) × (Fin (n - r) → ℂ)) (i : Fin n) :
    combineFun n r hr fg i =
      (if h : (i : ℕ) < r then fg.1 ⟨i, h⟩ else fg.2 ⟨(i : ℕ) - r, by omega⟩) := rfl

/-- The inverse of `combineFun`: reading off the two blocks of a function on `Fin n`. -/
noncomputable def splitFun (n r : ℕ) (hr : r ≤ n) (v : Fin n → ℂ) :
    (Fin r → ℂ) × (Fin (n - r) → ℂ) :=
  (fun j => v ⟨(j : ℕ), by omega⟩, fun j => v ⟨r + (j : ℕ), by omega⟩)

@[simp] theorem splitFun_fst (n r : ℕ) (hr : r ≤ n) (v : Fin n → ℂ) :
    (splitFun n r hr v).1 = (fun j : Fin r => v ⟨(j : ℕ), by omega⟩) := rfl

@[simp] theorem splitFun_snd (n r : ℕ) (hr : r ≤ n) (v : Fin n → ℂ) :
    (splitFun n r hr v).2 = (fun j : Fin (n - r) => v ⟨r + (j : ℕ), by omega⟩) := rfl

/-- The linear equivalence identifying `(Fin r → ℂ) × (Fin (n - r) → ℂ)` with
`Fin n → ℂ` by concatenating the two blocks. -/
noncomputable def combine (n r : ℕ) (hr : r ≤ n) :
    ((Fin r → ℂ) × (Fin (n - r) → ℂ)) ≃ₗ[ℂ] (Fin n → ℂ) where
  toFun := combineFun n r hr
  invFun := splitFun n r hr
  left_inv := by
    intro fg
    obtain ⟨f, g⟩ := fg
    simp only [combineFun_apply, splitFun, Prod.mk.injEq]
    constructor
    · funext j; simp only [dif_pos j.isLt]
    · funext j
      have h : ¬ ((r + (j:ℕ) : ℕ) < r) := by omega
      have h2 : (⟨r + (j:ℕ) - r, by omega⟩ : Fin (n - r)) = j := by
        apply Fin.ext
        rw [Fin.val_mk, Nat.add_sub_cancel_left]
      simp only [dif_neg h, h2]
  right_inv := by
    intro v
    funext i
    simp only [combineFun_apply, splitFun]
    split_ifs with hi
    · exact congrArg v (Fin.ext rfl)
    · refine congrArg v ?_
      apply Fin.ext
      rw [Fin.val_mk]
      exact Nat.add_sub_of_le (not_lt.mp hi)
  map_add' := by
    intro f g
    funext i
    simp only [combineFun_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    split_ifs <;> rfl
  map_smul' := by
    intro c f
    funext i
    simp only [combineFun_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply]
    split_ifs <;> rfl

@[simp] theorem combine_apply (n r : ℕ) (hr : r ≤ n)
    (fg : (Fin r → ℂ) × (Fin (n - r) → ℂ)) :
    combine n r hr fg = combineFun n r hr fg := rfl

end Work.KT
