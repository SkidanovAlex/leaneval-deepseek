import Mathlib
import Submission.Work.WilE5.Sys

namespace Work.WilE5.Bounds

open WilkiesDesign WilkiesDesign.E

/-! ## Degree bookkeeping for the iterated fibrewise operator

The three ingredients are

* `det_totalDegree_le_row` — a determinant is bounded in degree by the sum of a *row-wise* bound
  (the transpose of `Work.WilE2.Matrix.det_totalDegree_le`; note the row index is the one that
  indexes the polynomial `f` in `detOp`, so this is the shape needed here);
* `atomDeg_detOp_le` — one `detOp` step raises `atomDeg` by at most `∑ a, atomDeg (h a) + 1`;
* `atomDeg_foldr_le` — a fold of such steps with orders `m l` raises `atomDeg` by at most
  `(∑ l, m l) * C`, uniformly in the number of *distinct* directions (repeats are counted).
-/

/-- The determinant of a matrix over `EAPoly` is bounded in degree by the sum of a row-wise bound
on the entries. -/
private theorem det_totalDegree_le_row {ι : Type*} [Fintype ι] [DecidableEq ι] {k r : ℕ}
    (M : Matrix ι ι (EAPoly k r)) (b : ι → ℕ) (hb : ∀ a c, (M a c).totalDegree ≤ b a) :
    M.det.totalDegree ≤ ∑ a, b a := by
  classical
  rw [Matrix.det_apply']
  refine MvPolynomial.totalDegree_finsetSum_le fun σ _ => ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hsign : (↑↑(Equiv.Perm.sign σ) : EAPoly k r).totalDegree = 0 := by
    have h : (↑↑(Equiv.Perm.sign σ) : EAPoly k r)
        = MvPolynomial.C ((↑↑(Equiv.Perm.sign σ) : ℤ) : ℝ) := rfl
    rw [h, MvPolynomial.totalDegree_C]
  rw [hsign, Nat.zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => hb (σ i) i).trans ?_
  exact le_of_eq (Equiv.sum_comp σ b)

/-- One `detOp` step raises `atomDeg` by at most `∑ a, atomDeg (h a) + 1`. -/
private theorem atomDeg_detOp_le {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (l : Fin k) (f : EAPoly k r) :
    atomDeg (detOp c h ι l f) ≤ atomDeg f + (∑ a, atomDeg (h a)) + 1 := by
  classical
  have hM : (Matrix.of (fun (a b : Fin (j + 1)) =>
      eaD c (Fin.lastCases l ι b) (Fin.lastCases f h a))).det.totalDegree
      ≤ ∑ a : Fin (j + 1), atomDeg (Fin.lastCases f h a) := by
    refine det_totalDegree_le_row _ (fun a => atomDeg (Fin.lastCases f h a)) ?_
    intro a b'
    exact totalDegree_eaD_le c _ _
  have hsum : (∑ a : Fin (j + 1), atomDeg (Fin.lastCases f h a))
      = (∑ a : Fin j, atomDeg (h a)) + atomDeg f := by
    rw [Fin.sum_univ_castSucc]
    simp
  rw [detOp, atomDeg]
  omega

/-- Iterating a single step `m` times raises `atomDeg` by at most `m * C`. -/
private theorem atomDeg_iterate_le {k r : ℕ} (T : EAPoly k r → EAPoly k r) (C : ℕ)
    (hT : ∀ f, atomDeg (T f) ≤ atomDeg f + C) (m : ℕ) (f : EAPoly k r) :
    atomDeg (T^[m] f) ≤ atomDeg f + m * C := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    calc atomDeg (T (T^[m] f)) ≤ atomDeg (T^[m] f) + C := hT _
      _ ≤ (atomDeg f + m * C) + C := by omega
      _ = atomDeg f + (m + 1) * C := by ring

/-- One fibrewise step `detOpSt c B l` raises `atomDeg` by at most
`(∑ a, atomDeg (hFun B a)) + 1`. -/
private theorem atomDeg_detOpSt_le {p q r : ℕ} (c : EAChain (p + q) r)
    (B : List (EAPoly (p + q) r × Fin q)) (l : Fin q) (f : EAPoly (p + q) r) :
    atomDeg (detOpSt c B l f) ≤ atomDeg f + ((∑ a : Fin B.length, atomDeg (hFun B a)) + 1) := by
  have h := atomDeg_detOp_le c (hFun B) (pivFun B) (yDir p l) f
  simpa only [detOpSt, Nat.add_assoc] using h

/-- A right fold of iterated steps, with one order per direction, raises `atomDeg` by at most
`(∑ l, m l) * C`. -/
private theorem atomDeg_foldr_le {q k r : ℕ} (T : Fin q → EAPoly k r → EAPoly k r) (C : ℕ)
    (hT : ∀ l f, atomDeg (T l f) ≤ atomDeg f + C) (m : Fin q → ℕ) (ψ : EAPoly k r) :
    atomDeg ((List.finRange q).foldr (fun l g => (T l)^[m l] g) ψ)
      ≤ atomDeg ψ + (∑ i, m i) * C := by
  have key : ∀ (L : List (Fin q)) (φ : EAPoly k r),
      atomDeg (L.foldr (fun l g => (T l)^[m l] g) φ) ≤ atomDeg φ + (L.map m).sum * C := by
    intro L
    induction L with
    | nil => intro φ; simp
    | cons l L ih =>
      intro φ
      have h := ih φ
      simp only [List.foldr_cons, List.map_cons, List.sum_cons]
      calc atomDeg ((T l)^[m l] (L.foldr (fun l g => (T l)^[m l] g) φ))
          ≤ atomDeg (L.foldr (fun l g => (T l)^[m l] g) φ) + m l * C :=
            atomDeg_iterate_le (T l) C (hT l) (m l) _
        _ ≤ (atomDeg φ + (L.map m).sum * C) + m l * C := by omega
        _ = atomDeg φ + (m l + (L.map m).sum) * C := by ring
  have h := key (List.finRange q) ψ
  rwa [← List.ofFn_eq_map, List.sum_ofFn] at h

/-- Iterating the fibrewise operator raises `atomDeg` at most *linearly* in the order, with the
coefficient given by the sum of the pivot functions' degrees.  This is what keeps the recursion's
degrees polynomial in `X.deg` (iterating the crude bound `totalDegree_detOp_le` would only give an
exponential bound).

Suggested route: first prove the *row-indexed* determinant bound
`(Matrix.det M).totalDegree ≤ ∑ a, (the total degree bound of row a)` for a matrix over `EAPoly`
(via `Matrix.det_apply`, `MvPolynomial.totalDegree_prod_le`/`totalDegree_sum_le` and
`Finset.sum_le_sum`; `Work.WilE9.Deg.det_totalDegree_le_row` is a ready-made variant), then apply it
to the `(j+1) × (j+1)` matrix defining `detOp c (hFun σ.B) (pivFun σ.B) (yDir p l) f` with the row
bounds `atomDeg (hFun σ.B a)` for `a < σ.B.length` and `atomDeg f` for the last row
(`atomDeg_eaD_le`), to get
`atomDeg (detOp c (hFun σ.B) (pivFun σ.B) (yDir p l) f) ≤
atomDeg f + (∑ a, atomDeg (hFun σ.B a)) + 1`.  Then induct on the number of applications: `yOpSt` is a
`List.finRange q`-fold right fold of `(detOpSt c σ.B l)^[m l]`, so the total number of applications
is `mSum m` and each adds at most `(∑ a, atomDeg (hFun σ.B a)) + 1`. -/
theorem atomDeg_yOpSt_le {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (σ : Work.WilE5.St p q X.r)
    (ψ : WilkiesDesign.E.EAPoly (p + q) X.r) (m : Fin q → ℕ) :
    WilkiesDesign.E.atomDeg (Work.WilE5.yOpSt X.c σ.B m ψ) ≤
      WilkiesDesign.E.atomDeg ψ + (Work.WilE5.mSum m) *
        ((∑ a : Fin σ.B.length, WilkiesDesign.E.atomDeg (Work.WilE5.hFun σ.B a)) + 1) := by
  have hfold := atomDeg_foldr_le (T := fun l => detOpSt X.c σ.B l)
    (C := (∑ a : Fin σ.B.length, atomDeg (hFun σ.B a)) + 1)
    (fun l f => atomDeg_detOpSt_le X.c σ.B l f) m ψ
  rw [yOpSt, mSum]
  exact hfold

end Work.WilE5.Bounds
