import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.WilE5.Basic

set_option autoImplicit false
noncomputable section

namespace Work.Strat

open WilkiesDesign WilkiesDesign.E

/-!
# Vanishing of `detOpSt` by a row relation

`detOpSt c B l χ` is the determinant `detOp c (hFun B) (pivFun B) (yDir p l) χ`, i.e. the
`(j+1) × (j+1)` determinant (`j = B.length`) whose first `j` rows are the equations of `B`,
differentiated in fibre directions, and whose last row is `χ` differentiated in fibre
directions.

This file proves that such a determinant vanishes as soon as *every* fibre derivative
`eaD c (yDir p d) χ` of the last row is the same linear combination
`∑ a, lam a • eaD c (yDir p d) (hFun B a)` of the corresponding derivatives of the first `j`
rows (the coefficients `lam a` being independent of the direction `d`).  The two ingredients
are purely algebraic:

* `det_eq_zero_of_last_row_combination`: a square matrix whose last row is a fixed linear
  combination of its other rows has determinant `0`;
* `eaEval_detOp_eq_zero_of_row_relation`: `eaEval` commutes with `detOp` (this is
  `Work.WilE5.eaEval_detOp`), so the relation between the derivatives of `χ` and of the `h a`
  at the point `z` becomes a row relation for the evaluated matrix.
-/

/-- A square `(n+1) × (n+1)` matrix whose last row is a fixed linear combination
`∑ a, lam a • (row a)` of its first `n` rows has determinant zero. -/
theorem det_eq_zero_of_last_row_combination {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (lam : Fin n → ℝ)
    (h : ∀ j : Fin (n + 1), M (Fin.last n) j = ∑ a : Fin n, lam a * M (Fin.castSucc a) j) :
    M.det = 0 := by
  -- replace the last row of `M` by the same linear combination: this does not change the matrix,
  -- but `Matrix.det_updateRow_sum` computes its determinant as `c (last n) • M.det`
  set c : Fin (n + 1) → ℝ := Fin.lastCases 0 lam with hc
  have hkey : M.updateRow (Fin.last n) (∑ k, c k • M k) = M := by
    ext i j
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [Matrix.updateRow_ne (Fin.castSucc_ne_last i')]
    · rw [Matrix.updateRow_self]
      have hsum : (∑ k : Fin (n + 1), c k • M k) j
          = ∑ a : Fin n, lam a * M (Fin.castSucc a) j := by
        simp only [Finset.sum_apply, Pi.smul_apply]
        rw [Fin.sum_univ_castSucc]
        simp only [hc, Fin.lastCases_castSucc, Fin.lastCases_last, smul_eq_mul, zero_mul,
          add_zero]
      rw [hsum, h j]
  have hd := Matrix.det_updateRow_sum M (Fin.last n) c
  rw [hkey] at hd
  simp only [hc, Fin.lastCases_last, zero_smul] at hd
  exact hd

/-- `eaEval`-form of the row-combination criterion for `detOp`: if every fibre derivative of `φ`
at `z` is the linear combination `∑ a, lam a • (derivative of `h a`)`, with coefficients `lam a`
independent of the fibre direction, then `detOp c h (yDir p ∘ ι) (yDir p l) φ` evaluates to `0`
at `z`. -/
theorem eaEval_detOp_eq_zero_of_row_relation {p q r j : ℕ} (c : EAChain (p + q) r)
    (h : Fin j → EAPoly (p + q) r) (ι : Fin j → Fin q) (φ : EAPoly (p + q) r)
    (z : Fin (p + q) → ℝ) (l : Fin q) (lam : Fin j → ℝ)
    (hrel : ∀ l' : Fin q, eaEval c (eaD c (Work.WilE5.yDir p l') φ) z =
      ∑ a : Fin j, lam a * eaEval c (eaD c (Work.WilE5.yDir p l') (h a)) z) :
    eaEval c (detOp c h (fun a => Work.WilE5.yDir p (ι a)) (Work.WilE5.yDir p l) φ) z = 0 := by
  rw [Work.WilE5.eaEval_detOp]
  apply det_eq_zero_of_last_row_combination (n := j) (lam := lam)
  intro b
  simp only [Matrix.of_apply]
  rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
  · simpa only [Fin.lastCases_castSucc, Fin.lastCases_last] using hrel (ι b')
  · simpa only [Fin.lastCases_castSucc, Fin.lastCases_last] using hrel l

/-- **The requested lemma.** If, in a fibre direction `d`, every derivative
`eaD c (yDir p d) χ` is the same linear combination (coefficients `lam a`, independent of `d`)
of the derivatives of the equations `hFun B a` of the system `B`, then the determinant
`detOpSt c B l χ` vanishes at `z`. -/
theorem detOpSt_eq_zero_of_row_combination {p q r : ℕ} (c : WilkiesDesign.E.EAChain (p + q) r)
    (B : List (WilkiesDesign.E.EAPoly (p + q) r × Fin q)) (χ : WilkiesDesign.E.EAPoly (p + q) r)
    (l : Fin q) (z : Fin (p + q) → ℝ) (lam : Fin B.length → ℝ)
    (hl : ∀ d : Fin q, WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Work.WilE5.yDir p d) χ) z
      = ∑ a : Fin B.length,
          lam a * WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Work.WilE5.yDir p d) (Work.WilE5.hFun B a)) z) :
    WilkiesDesign.E.eaEval c (Work.WilE5.detOpSt c B l χ) z = 0 := by
  have h := eaEval_detOp_eq_zero_of_row_relation (p := p) (q := q) (r := r) (j := B.length) c
    (Work.WilE5.hFun B) (fun a => (B.get a).2) χ z l lam hl
  exact h

end Work.Strat
