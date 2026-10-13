import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.WilE5.Operators.detOp_extH_eq_zero

/-!
# The extended Jacobian stays nondegenerate

Let `c` be an exp-affine chain on `ℝ^{p+q}`, `h : Fin j → EAPoly (p+q) r` a system of `j`
equations whose pivots `ι a` all point in *fibre* directions (`ι a = yDir p l`), and `z` a
point at which the `j × j` Jacobian

`A = (eaEval c (eaD c (ι b) (h a)) z)_{a,b}`

is invertible.  Viewing the extended system `extH h z = (h, x_i - z_i)` with the extended pivots
`extι ι = (ι, x_i)` as a system of `j + p` equations in `j + p` unknowns (the point `z` is a
nondegenerate zero of it, with the base coordinates *pinned* by the shifts `x_i - z_i`), the
extended Jacobian

`M = (eaEval c (eaD c (extι ι b) (extH h z a)) z)_{a,b}`,   `a, b : Fin (j+p)`

is invertible as well.

The reason is that the reindexing `Fin j ⊕ Fin p ≃ Fin (j+p)` in which the equation rows and
`ι`-columns come first, and the base-shift rows and `x`-columns last, exhibits `M` as the block
matrix

```
        ι-cols   x-cols
h-rows [   A        B   ]
x-rows [   0        1   ]
```

where `B` is some block.  Indeed the shift `x_i - z_i` is linear, hence its derivative is the
constant `δ` in the base direction `x_{i'}` and `0` in any fibre direction.  The sign of the
reindexing cancels (`Matrix.det_submatrix_equiv_self`), so
`det M = det A * det 1 = det A ≠ 0` (`Matrix.det_fromBlocks_zero₂₁`).
-/

set_option autoImplicit false

namespace Work.Strat

open WilkiesDesign WilkiesDesign.E

theorem det_extJac_ne_zero {p q r j : ℕ} (c : WilkiesDesign.E.EAChain (p + q) r)
    (h : Fin j → WilkiesDesign.E.EAPoly (p + q) r) (ι : Fin j → Fin (p + q))
    (hι : ∀ a, ∃ l : Fin q, ι a = Work.WilE5.yDir p l) (z : Fin (p + q) → ℝ)
    (hdet : (Matrix.of fun a b => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (ι b) (h a)) z).det ≠ 0) :
    (Matrix.of fun a b =>
      WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Work.WilE5.extι ι b) (Work.WilE5.extH h z a)) z).det ≠ 0 := by
  -- The reindexed matrix is the block matrix `[[A, B], [0, 1]]`.
  have hblock :
      (Matrix.of fun a b =>
        eaEval c (eaD c (Work.WilE5.extι ι b) (Work.WilE5.extH h z a)) z).submatrix
          (finSumFinEquiv (m := j) (n := p)) (finSumFinEquiv (m := j) (n := p))
        = Matrix.fromBlocks
            (Matrix.of fun a b => eaEval c (eaD c (ι b) (h a)) z)
            (Matrix.of fun a i => eaEval c (eaD c (Fin.castAdd q i) (h a)) z) 0 1 := by
    funext x y
    rcases x with a | i <;> rcases y with b | i'
    · -- `(h, ι)` block: the original Jacobian.
      simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left, Matrix.fromBlocks_apply₁₁]
      simp [Work.WilE5.extι, Work.WilE5.extH, Fin.append_left]
    · -- `(h, x)` block.
      simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Matrix.fromBlocks_apply₁₂]
      simp [Work.WilE5.extι, Work.WilE5.extH, Fin.append_left, Fin.append_right]
    · -- `(x, ι)` block: the shifts are constant along the fibre directions `ι b`.
      obtain ⟨l, hl⟩ := hι b
      simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
        Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      simp only [Matrix.of_apply, Work.WilE5.extι, Work.WilE5.extH, Fin.append_left, Fin.append_right]
      rw [hl, Work.WilE5.Operators.eaD_yDir_xShift]
      simp [eaEval]
    · -- `(x, x)` block: the identity.
      simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₂₂]
      simp only [Matrix.of_apply, Work.WilE5.extι, Work.WilE5.extH, Fin.append_right]
      rw [Work.WilE5.Operators.eaD_castAdd_xShift, Matrix.one_apply]
      by_cases hii : i = i'
      · subst hii; simp [eaEval]
      · simp [eaEval, hii]
  -- Reindexing does not change the determinant, and the block matrix is triangular.
  have hdet' : (Matrix.of fun a b =>
        eaEval c (eaD c (Work.WilE5.extι ι b) (Work.WilE5.extH h z a)) z).det
      = (Matrix.of fun a b => eaEval c (eaD c (ι b) (h a)) z).det := by
    rw [← Matrix.det_submatrix_equiv_self (finSumFinEquiv (m := j) (n := p))
        (Matrix.of fun a b => eaEval c (eaD c (Work.WilE5.extι ι b) (Work.WilE5.extH h z a)) z),
      hblock, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  rw [hdet']
  exact hdet

end Work.Strat
