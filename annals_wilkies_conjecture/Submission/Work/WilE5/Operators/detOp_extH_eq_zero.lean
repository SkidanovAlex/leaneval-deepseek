import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.Wilkies.E.Spec

/-!
# The extended system `(h, x - z)` does not change `detOp` vanishing

For the fibrewise stratification one needs that adjoining the base-coordinate shifts `x_i - z_i`
(with the base directions `x_i` as pivots) to a system `h : Fin j → EAPoly (p+q) r` whose pivots
`ι` all lie in *fibre* directions does not change whether the operator `detOp c · · (yDir p l) f`
vanishes.

The matrix of the extended system has the block form

```
        ι-cols   x-cols   y-col
h-rows [   A         0        u   ]
x-rows [   0         I        0   ]
f-row  [   v         0        t   ]
```

where `A`, `u`, `v`, `t` are the blocks of the matrix of the original system, while the `x`-rows
are the base shifts `x_i - z_i`, whose derivatives are `δ` in the base directions and `0` in the
fibre directions (the latter because the pivots `ι a` are fibre directions by hypothesis `hι`).

Since the row and the column reordering that puts the identity block first is the *same*
permutation of `Fin (j+p+1)`, its sign cancels: the determinant of the block matrix is
`det 1 * det A = det A` (`Matrix.det_fromBlocks_zero₁₂`), and reindexing by an equivalence does not
change the determinant (`Matrix.det_submatrix_equiv_self`).

The formalisation below consists of the index permutation `swapIdx`, the transfer lemmas for the
polynomial rows and the derivative directions, the entrywise block identity, and the determinant
identity for the two operators.
-/

set_option autoImplicit false
noncomputable section
namespace Work.WilE5.Operators
open WilkiesDesign WilkiesDesign.E

variable {p q r j : ℕ}

/-! ## §1. The index permutation -/

/-- Forward map: the `p` base-shift rows/columns first, then the `j` equation rows/columns, then
the final row/column.  (Concretely `i ↦ j + i` for `Fin p`, `a ↦ a` for `Fin j` and `j ↦ j + p`.) -/
def swapFwd (p j : ℕ) : Fin p ⊕ Fin (j + 1) → Fin (j + p + 1) :=
  fun x => match x with
    | Sum.inl i => Fin.castSucc (Fin.natAdd j i)
    | Sum.inr b => Fin.lastCases (Fin.last (j + p)) (fun a : Fin j => Fin.castSucc (Fin.castAdd p a)) b

/-- Inverse of `swapFwd`: a value `< j` is an equation row/column, a value in `[j, j+p)` is a
base-shift row/column, and the last value is the final one. -/
def swapBwd (p j : ℕ) : Fin (j + p + 1) → Fin p ⊕ Fin (j + 1) :=
  fun n => Fin.lastCases (Sum.inr (Fin.last j))
    (fun n' : Fin (j + p) => Fin.addCases (fun a : Fin j => Sum.inr (Fin.castSucc a))
      (fun i : Fin p => Sum.inl i) n') n

@[simp] theorem swapFwd_inl (i : Fin p) :
    swapFwd p j (Sum.inl i) = Fin.castSucc (Fin.natAdd j i) := rfl

@[simp] theorem swapFwd_inr_castSucc (a : Fin j) :
    swapFwd p j (Sum.inr (Fin.castSucc a)) = Fin.castSucc (Fin.castAdd p a) := by
  simp [swapFwd]

@[simp] theorem swapFwd_inr_last :
    swapFwd p j (Sum.inr (Fin.last j)) = Fin.last (j + p) := by
  simp [swapFwd]

@[simp] theorem swapBwd_last :
    swapBwd p j (Fin.last (j + p)) = Sum.inr (Fin.last j) := by
  simp [swapBwd]

@[simp] theorem swapBwd_castSucc (n' : Fin (j + p)) :
    swapBwd p j (Fin.castSucc n') = Fin.addCases (fun a : Fin j => Sum.inr (Fin.castSucc a))
      (fun i : Fin p => Sum.inl i) n' := by
  simp [swapBwd]

theorem swapBwd_swapFwd (x : Fin p ⊕ Fin (j + 1)) : swapBwd p j (swapFwd p j x) = x := by
  rcases x with i | b
  · rw [swapFwd_inl, swapBwd_castSucc, Fin.addCases_right]
  · induction b using Fin.lastCases with
    | last => rw [swapFwd_inr_last, swapBwd_last]
    | cast a => rw [swapFwd_inr_castSucc, swapBwd_castSucc, Fin.addCases_left]

theorem swapFwd_swapBwd (n : Fin (j + p + 1)) : swapFwd p j (swapBwd p j n) = n := by
  induction n using Fin.lastCases with
  | last => rw [swapBwd_last, swapFwd_inr_last]
  | cast n' =>
      rw [swapBwd_castSucc]
      induction n' using Fin.addCases with
      | left a => rw [Fin.addCases_left, swapFwd_inr_castSucc]
      | right i => rw [Fin.addCases_right, swapFwd_inl]

/-- The index permutation used to bring the extended matrix into block form. -/
def swapIdx (p j : ℕ) : (Fin p ⊕ Fin (j + 1)) ≃ Fin (j + p + 1) :=
  Equiv.mk (swapFwd p j) (swapBwd p j) (swapBwd_swapFwd) (swapFwd_swapBwd)

theorem swapIdx_eq_swapFwd :
    (⇑(swapIdx p j) : Fin p ⊕ Fin (j + 1) → Fin (j + p + 1)) = swapFwd p j := by
  funext x
  rfl

/-! ## §2. Derivatives of the base shifts -/

/-- The fibre directions differ from the base directions. -/
theorem fibre_ne_base (i : Fin p) (l : Fin q) :
    (Sum.inl (Fin.castAdd q i) : Fin (p + q) ⊕ Fin r) ≠ Sum.inl (yDir p l) := by
  simp only [Sum.inl.injEq, ne_eq, yDir, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
  omega

/-- Two distinct base directions stay distinct. -/
theorem base_ne_base {i i' : Fin p} (h : i ≠ i') :
    (Sum.inl (Fin.castAdd q i) : Fin (p + q) ⊕ Fin r) ≠ Sum.inl (Fin.castAdd q i') := by
  intro hh
  exact h (Fin.castAdd_inj.mp (Sum.inl.inj hh))

/-- The derivative of the base shift `x i - z i` in a base direction is `δ`. -/
theorem eaD_castAdd_xShift (c : EAChain (p + q) r) (z : Fin (p + q) → ℝ) (i i' : Fin p) :
    eaD c (Fin.castAdd q i') (xShift (q := q) (r := r) z i) = if i = i' then 1 else 0 := by
  simp only [eaD, xShift, map_sub, MvPolynomial.pderiv_C, MvPolynomial.pderiv_X, sub_zero]
  simp only [Pi.single_eq_of_ne
    (by simp : (Sum.inl (Fin.castAdd q i) : Fin (p + q) ⊕ Fin r) ≠ Sum.inr _)]
  simp only [mul_zero, Finset.sum_const_zero, add_zero]
  by_cases h : i = i'
  · subst h; simp [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (base_ne_base h)]
    simp [h]

/-- The derivative of the base shift `x i - z i` in a fibre direction is `0`. -/
theorem eaD_yDir_xShift (c : EAChain (p + q) r) (z : Fin (p + q) → ℝ) (i : Fin p) (l : Fin q) :
    eaD c (yDir p l) (xShift (q := q) (r := r) z i) = 0 := by
  simp only [eaD, xShift, map_sub, MvPolynomial.pderiv_C, MvPolynomial.pderiv_X, sub_zero]
  simp only [Pi.single_eq_of_ne
    (by simp : (Sum.inl (Fin.castAdd q i) : Fin (p + q) ⊕ Fin r) ≠ Sum.inr _)]
  rw [Pi.single_eq_of_ne (fibre_ne_base i l)]
  simp

/-- Same, for an arbitrary fibre direction. -/
theorem eaD_fibre_xShift (c : EAChain (p + q) r) (z : Fin (p + q) → ℝ) (i : Fin p)
    (d : Fin (p + q)) (hd : ∃ l' : Fin q, d = yDir p l') :
    eaD c d (xShift (q := q) (r := r) z i) = 0 := by
  obtain ⟨l', rfl⟩ := hd
  exact eaD_yDir_xShift c z i l'

/-! ## §3. Transfer lemmas along the permutation -/

/-- Row polynomials: the `inr` (equation) part. -/
theorem row_swapIdx (h : Fin j → EAPoly (p + q) r) (z : Fin (p + q) → ℝ)
    (f : EAPoly (p + q) r) (b : Fin (j + 1)) :
    (Fin.lastCases (n := j + p) (motive := fun _ => EAPoly (p + q) r) f (extH h z))
      (swapFwd p j (Sum.inr b)) = Fin.lastCases f h b := by
  induction b using Fin.lastCases with
  | last => rw [swapFwd_inr_last, Fin.lastCases_last, Fin.lastCases_last]
  | cast a =>
      rw [swapFwd_inr_castSucc, Fin.lastCases_castSucc, Fin.lastCases_castSucc]
      simp [extH, Fin.append_left]

/-- Row polynomials: the `inl` (base shift) part. -/
theorem row_swapIdx_inl (h : Fin j → EAPoly (p + q) r) (z : Fin (p + q) → ℝ)
    (f : EAPoly (p + q) r) (i : Fin p) :
    (Fin.lastCases (n := j + p) (motive := fun _ => EAPoly (p + q) r) f (extH h z))
      (swapFwd p j (Sum.inl i)) = xShift (q := q) (r := r) z i := by
  rw [swapFwd_inl, Fin.lastCases_castSucc]
  simp [extH, Fin.append_right]

/-- Derivative directions: the `inr` (equation) part. -/
theorem dir_swapIdx (ι : Fin j → Fin (p + q)) (l : Fin q) (b : Fin (j + 1)) :
    (Fin.lastCases (n := j + p) (motive := fun _ => Fin (p + q)) (yDir p l) (extι ι))
      (swapFwd p j (Sum.inr b)) = Fin.lastCases (yDir p l) ι b := by
  induction b using Fin.lastCases with
  | last => rw [swapFwd_inr_last, Fin.lastCases_last, Fin.lastCases_last]
  | cast a =>
      rw [swapFwd_inr_castSucc, Fin.lastCases_castSucc, Fin.lastCases_castSucc]
      simp [extι, Fin.append_left]

/-- Derivative directions: the `inl` (base) part. -/
theorem dir_swapIdx_inl (ι : Fin j → Fin (p + q)) (l : Fin q) (i : Fin p) :
    (Fin.lastCases (n := j + p) (motive := fun _ => Fin (p + q)) (yDir p l) (extι ι))
      (swapFwd p j (Sum.inl i)) = Fin.castAdd q i := by
  rw [swapFwd_inl, Fin.lastCases_castSucc]
  simp [extι, Fin.append_right]

/-- The direction `Fin.lastCases (yDir p l) ι b` is a fibre direction. -/
theorem fibre_lastCases_dir (ι : Fin j → Fin (p + q)) (l : Fin q)
    (hι : ∀ a, ∃ l' : Fin q, ι a = yDir p l') (b : Fin (j + 1)) :
    ∃ l' : Fin q, Fin.lastCases (yDir p l) ι b = yDir p l' := by
  induction b using Fin.lastCases with
  | last => exact ⟨l, by simp⟩
  | cast a => obtain ⟨l', hl'⟩ := hι a
              exact ⟨l', by simpa using hl'⟩

/-! ## §4. The matrices and the block identity -/

/-- The matrix of the extended system `(h, x - z)` (pivots `(ι, x)`, last column `∂_{y_l}`). -/
def extMat (c : EAChain (p + q) r) (h : Fin j → EAPoly (p + q) r) (ι : Fin j → Fin (p + q))
    (z : Fin (p + q) → ℝ) (f : EAPoly (p + q) r) (l : Fin q) :
    Matrix (Fin (j + p + 1)) (Fin (j + p + 1)) (EAPoly (p + q) r) :=
  Matrix.of fun (a b : Fin (j + p + 1)) =>
    eaD c (Fin.lastCases (yDir p l) (extι ι) b) (Fin.lastCases f (extH h z) a)

/-- The matrix of the original system (pivots `ι`, last column `∂_{y_l}`). -/
def sMat (c : EAChain (p + q) r) (h : Fin j → EAPoly (p + q) r) (ι : Fin j → Fin (p + q))
    (f : EAPoly (p + q) r) (l : Fin q) :
    Matrix (Fin (j + 1)) (Fin (j + 1)) (EAPoly (p + q) r) :=
  Matrix.of fun (a b : Fin (j + 1)) =>
    eaD c (Fin.lastCases (yDir p l) ι b) (Fin.lastCases f h a)

/-- The `(j+1) × p` block of base-direction derivatives of the extended rows. -/
def blkC (c : EAChain (p + q) r) (h : Fin j → EAPoly (p + q) r) (f : EAPoly (p + q) r) :
    Matrix (Fin (j + 1)) (Fin p) (EAPoly (p + q) r) :=
  Matrix.of fun (b : Fin (j + 1)) (i : Fin p) => eaD c (Fin.castAdd q i) (Fin.lastCases f h b)

theorem extMat_eq_detOp (c : EAChain (p + q) r) (h : Fin j → EAPoly (p + q) r)
    (ι : Fin j → Fin (p + q)) (z : Fin (p + q) → ℝ) (f : EAPoly (p + q) r) (l : Fin q) :
    detOp c (extH h z) (extι ι) (yDir p l) f = (extMat c h ι z f l).det := rfl

theorem sMat_eq_detOp (c : EAChain (p + q) r) (h : Fin j → EAPoly (p + q) r)
    (ι : Fin j → Fin (p + q)) (f : EAPoly (p + q) r) (l : Fin q) :
    (sMat c h ι f l).det = detOp c h ι (yDir p l) f := rfl

/-- The `(inl, inl)` block is the identity. -/
theorem extMat_11 (c : EAChain (p + q) r) (h : Fin j → EAPoly (p + q) r)
    (ι : Fin j → Fin (p + q)) (z : Fin (p + q) → ℝ) (f : EAPoly (p + q) r) (l : Fin q)
    (i i' : Fin p) :
    extMat c h ι z f l (swapFwd p j (Sum.inl i)) (swapFwd p j (Sum.inl i'))
      = (1 : Matrix (Fin p) (Fin p) (EAPoly (p + q) r)) i i' := by
  simp only [extMat, Matrix.of_apply, row_swapIdx_inl, dir_swapIdx_inl]
  rw [Matrix.one_apply]
  exact eaD_castAdd_xShift c z i i'

/-- The `(inl, inr)` block vanishes: the base shifts have no fibre derivative. -/
theorem extMat_12 (c : EAChain (p + q) r) (h : Fin j → EAPoly (p + q) r)
    (ι : Fin j → Fin (p + q)) (hι : ∀ a, ∃ l' : Fin q, ι a = yDir p l')
    (z : Fin (p + q) → ℝ) (f : EAPoly (p + q) r) (l : Fin q) (i : Fin p) (b' : Fin (j + 1)) :
    extMat c h ι z f l (swapFwd p j (Sum.inl i)) (swapFwd p j (Sum.inr b')) = 0 := by
  simp only [extMat, Matrix.of_apply, row_swapIdx_inl, dir_swapIdx]
  obtain ⟨l', hl'⟩ := fibre_lastCases_dir ι l hι b'
  rw [hl']
  exact eaD_yDir_xShift c z i l'

/-- The `(inr, inl)` block is `blkC`. -/
theorem extMat_21 (c : EAChain (p + q) r) (h : Fin j → EAPoly (p + q) r)
    (ι : Fin j → Fin (p + q)) (z : Fin (p + q) → ℝ) (f : EAPoly (p + q) r) (l : Fin q)
    (b : Fin (j + 1)) (i' : Fin p) :
    extMat c h ι z f l (swapFwd p j (Sum.inr b)) (swapFwd p j (Sum.inl i'))
      = blkC c h f b i' := by
  simp only [extMat, blkC, Matrix.of_apply, dir_swapIdx_inl, row_swapIdx]

/-- The `(inr, inr)` block is the matrix of the original system. -/
theorem extMat_22 (c : EAChain (p + q) r) (h : Fin j → EAPoly (p + q) r)
    (ι : Fin j → Fin (p + q)) (z : Fin (p + q) → ℝ) (f : EAPoly (p + q) r) (l : Fin q)
    (b b' : Fin (j + 1)) :
    extMat c h ι z f l (swapFwd p j (Sum.inr b)) (swapFwd p j (Sum.inr b'))
      = sMat c h ι f l b b' := by
  simp only [extMat, sMat, Matrix.of_apply, row_swapIdx, dir_swapIdx]

/-- The extended matrix, reindexed by `swapIdx`, is the block matrix `[[1, 0], [blkC, sMat]]`. -/
theorem submatrix_swapIdx_extH (c : EAChain (p + q) r) (h : Fin j → EAPoly (p + q) r)
    (ι : Fin j → Fin (p + q)) (hι : ∀ a, ∃ l' : Fin q, ι a = yDir p l')
    (z : Fin (p + q) → ℝ) (f : EAPoly (p + q) r) (l : Fin q) :
    (extMat c h ι z f l).submatrix (swapIdx p j) (swapIdx p j)
      = Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) (EAPoly (p + q) r)) 0
          (blkC c h f) (sMat c h ι f l) := by
  rw [swapIdx_eq_swapFwd]
  funext x y
  rcases x with i | b <;> rcases y with i' | b'
  · simpa only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁] using extMat_11 c h ι z f l i i'
  · simpa only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      using extMat_12 c h ι hι z f l i b'
  · simpa only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁] using extMat_21 c h ι z f l b i'
  · simpa only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂] using extMat_22 c h ι z f l b b'

/-! ## §5. The determinant identity -/

/-- The determinant of the matrix of the extended system equals the determinant of the matrix of
the original one. -/
theorem det_extH_eq (c : EAChain (p + q) r) (h : Fin j → EAPoly (p + q) r)
    (ι : Fin j → Fin (p + q)) (hι : ∀ a, ∃ l' : Fin q, ι a = yDir p l')
    (z : Fin (p + q) → ℝ) (f : EAPoly (p + q) r) (l : Fin q) :
    detOp c (extH h z) (extι ι) (yDir p l) f = detOp c h ι (yDir p l) f := by
  have hblock := submatrix_swapIdx_extH c h ι hι z f l
  calc detOp c (extH h z) (extι ι) (yDir p l) f
      = (extMat c h ι z f l).det := extMat_eq_detOp c h ι z f l
    _ = ((extMat c h ι z f l).submatrix (swapIdx p j) (swapIdx p j)).det :=
        (Matrix.det_submatrix_equiv_self (swapIdx p j) (extMat c h ι z f l)).symm
    _ = (Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) (EAPoly (p + q) r)) 0
          (blkC c h f) (sMat c h ι f l)).det := by rw [hblock]
    _ = (1 : Matrix (Fin p) (Fin p) (EAPoly (p + q) r)).det * (sMat c h ι f l).det :=
        Matrix.det_fromBlocks_zero₁₂ 1 (blkC c h f) (sMat c h ι f l)
    _ = (sMat c h ι f l).det := by rw [Matrix.det_one, one_mul]
    _ = detOp c h ι (yDir p l) f := sMat_eq_detOp c h ι f l

theorem detOp_extH_eq_zero {p q r j : ℕ} (c : WilkiesDesign.E.EAChain (p + q) r)
    (h : Fin j → WilkiesDesign.E.EAPoly (p + q) r) (ι : Fin j → Fin (p + q))
    (hι : ∀ a, ∃ l : Fin q, ι a = Work.WilE5.yDir p l)
    (z : Fin (p + q) → ℝ) (f : WilkiesDesign.E.EAPoly (p + q) r) (l : Fin q) :
    WilkiesDesign.E.detOp c (Work.WilE5.extH h z) (Work.WilE5.extι ι) (Work.WilE5.yDir p l) f = 0 ↔
      WilkiesDesign.E.detOp c h ι (Work.WilE5.yDir p l) f = 0 := by
  rw [det_extH_eq c h ι hι z f l]

end Work.WilE5.Operators
