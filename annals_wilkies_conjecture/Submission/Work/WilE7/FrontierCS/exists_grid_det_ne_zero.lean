/-
  WilE7 / CS-slice, node **N2** (`exists_grid_det_ne_zero`).

  A 0/1 ("grid") slope matrix already makes `P · Λ + Q` invertible, provided some real slope
  does.  The function `Λ ↦ det (P · Λ + Q)` is affine in each matrix entry (`det` is linear in
  each column, and each entry lives in a single column), so by `multiAffine_eq_zero` (N2a) it is
  determined by its values on the `0/1` cube: if it vanished on every `0/1` matrix it would vanish
  identically, contradicting N2b (`exists_real_slope_det_ne_zero`).
-/
import Mathlib
import Submission.Work.WilE7.FrontierCS.Defs
import Submission.Work.WilE7.FrontierCS.multiAffine_eq_zero
import Submission.Work.WilE7.FrontierCS.exists_real_slope_det_ne_zero

set_option autoImplicit false
noncomputable section
open Classical
open Matrix

namespace Work.WilE7.FrontierCS

/-! ### Matrix calculus helpers -/

/-- `mulVec` of a vector updated in one coordinate: the change is a multiple of the
corresponding column. -/
private lemma mulVec_update {j d : ℕ} (P : Matrix (Fin j) (Fin d) ℝ) (v : Fin d → ℝ)
    (k : Fin d) (t : ℝ) :
    P.mulVec (Function.update v k t) = P.mulVec v + (t - v k) • P.col k := by
  have h : Function.update v k t = v + (t - v k) • Pi.single k (1:ℝ) := by
    ext l
    rw [Function.update_apply]
    by_cases hl : l = k
    · subst hl; simp
    · simp [hl]
  rw [h, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one]

/-- The entrywise form of `mulVec_update`. -/
private lemma sum_mul_update {d j : ℕ} (P : Matrix (Fin j) (Fin d) ℝ) (v : Fin d → ℝ)
    (k : Fin d) (t : ℝ) (r : Fin j) :
    (∑ l, P r l * Function.update v k t l) = (∑ l, P r l * v l) + (t - v k) * P r k := by
  have h := congrFun (mulVec_update P v k t) r
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.col_apply] at h
  exact h

/-- Removing one column of a product: `P * (A` with column `c` replaced by `v`) is `P * A` with
column `c` replaced by `P.mulVec v`. -/
private lemma mul_updateCol {d j : ℕ} (P : Matrix (Fin j) (Fin d) ℝ)
    (A : Matrix (Fin d) (Fin j) ℝ) (c : Fin j) (v : Fin d → ℝ) :
    P * A.updateCol c v = (P * A).updateCol c (P.mulVec v) := by
  ext r c'
  by_cases h : c' = c
  · subst h
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · simp [Matrix.mul_apply, updateCol_ne h]

/-- Rewriting `P * B + Q` when one entry of `B` (column `c`, row `k`) is replaced by `t`: this
adds `(t - B k c) • P.col k` to column `c`. -/
private lemma key {d j : ℕ} (P : Matrix (Fin j) (Fin d) ℝ) (Q : Matrix (Fin j) (Fin j) ℝ)
    (A : Matrix (Fin d) (Fin j) ℝ) (k : Fin d) (c : Fin j) (t : ℝ) :
    P * (A.updateCol c (Function.update (fun r => A r c) k t)) + Q
      = (P * A + Q).updateCol c ((P * A + Q).col c + (t - A k c) • P.col k) := by
  ext r c'
  by_cases hc : c' = c
  · rw [hc] at *
    simp only [Matrix.add_apply, Matrix.mul_apply, updateCol_self, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.col_apply]
    rw [sum_mul_update (v := fun r => A r c)]
    ring
  · simp only [Matrix.add_apply, Matrix.mul_apply, updateCol_ne hc]

/-- Replacing a column by itself changes nothing. -/
private lemma updateCol_col {d j : ℕ} (A : Matrix (Fin d) (Fin j) ℝ) (c : Fin j) :
    A.updateCol c (A.col c) = A := by
  ext r c'
  by_cases h : c' = c
  · subst h; simp [Matrix.col_apply]
  · simp [updateCol_ne h]

/-- **Affineness of the determinant in a single entry.**  If the `(k,c)` entry of `A` is `0`, then
`t ↦ det (P * (A` with entry `(k,c)` set to `t`) `+ Q)` is affine. -/
private lemma det_affine {d j : ℕ} (P : Matrix (Fin j) (Fin d) ℝ) (Q : Matrix (Fin j) (Fin j) ℝ)
    (A : Matrix (Fin d) (Fin j) ℝ) (k : Fin d) (c : Fin j) (h0 : A k c = 0) (t : ℝ) :
    (P * (A.updateCol c (Function.update (fun r => A r c) k t)) + Q).det
      = (P * A + Q).det
        + t * ((P * (A.updateCol c (Function.update (fun r => A r c) k 1)) + Q).det
               - (P * A + Q).det) := by
  have hkey := key P Q A k c t
  have hkey1 := key P Q A k c 1
  rw [hkey, hkey1, h0, sub_zero]
  simp only [Matrix.det_updateCol_add, Matrix.det_updateCol_smul, updateCol_col]
  ring

/-- Read a matrix off a vector indexed by `Fin (d*j)`, via the standard reindexing
`Fin d × Fin j ≃ Fin (d*j)`. -/
private def enc {d j : ℕ} (x : Fin (d*j) → ℝ) : Matrix (Fin d) (Fin j) ℝ :=
  Matrix.of (fun k c => x (finProdFinEquiv (k, c)))

/-- Updating the coordinate of `x` labelled by `i` corresponds to updating the `(k,c)` entry of
`enc x`, where `(k,c)` is the pair encoded by `i`; the base matrix is the one whose entry there is
already `0`. -/
private lemma enc_update_zero {d j : ℕ} (x : Fin (d*j) → ℝ) (k : Fin d) (c : Fin j)
    (i : Fin (d*j)) (hi : finProdFinEquiv (k, c) = i) (t : ℝ) :
    enc (Function.update x i t)
      = (enc (Function.update x i 0)).updateCol c
          (Function.update (fun r => (enc (Function.update x i 0)) r c) k t) := by
  ext k' c'
  by_cases hc : c' = c
  · rw [hc]
    simp only [enc, Matrix.of_apply, updateCol_self, Function.update_apply]
    by_cases hk' : k' = k
    · subst hk'
      simp [hi]
    · have hne : ¬ (finProdFinEquiv (k', c) = i) := by
        intro h
        have h2 : (k', c) = (k, c) := finProdFinEquiv.injective (by rw [hi]; exact h)
        exact hk' (by simpa using congrArg Prod.fst h2)
      simp [hk', hne]
  · simp only [enc, Matrix.of_apply, updateCol_ne hc, Function.update_apply]
    have hne : ¬ (finProdFinEquiv (k', c') = i) := by
      intro h
      have h2 : (k', c') = (k, c) := finProdFinEquiv.injective (by rw [hi]; exact h)
      exact hc (by simpa using congrArg Prod.snd h2)
    simp [hne]

/-! ### The grid lemma -/

theorem exists_grid_det_ne_zero {d j : ℕ} (P : Matrix (Fin j) (Fin d) ℝ)
    (Q : Matrix (Fin j) (Fin j) ℝ)
    (hsurj : ∀ y : Fin j → ℝ, ∃ t e, P.mulVec t + Q.mulVec e = y) :
    ∃ b : Fin d → Fin j → Bool, (P * Work.WilE7.FrontierCS.gridMat b + Q).det ≠ 0 := by
  obtain ⟨Λ, hΛ⟩ := exists_real_slope_det_ne_zero P Q hsurj
  by_contra h
  push Not at h
  -- the matrix-entry function whose determinant we study
  let F : (Fin (d*j) → ℝ) → ℝ := fun x => (P * enc x + Q).det
  -- it is affine in every coordinate
  have haff : ∀ (x : Fin (d*j) → ℝ) (i : Fin (d*j)) (t : ℝ),
      F (Function.update x i t)
        = F (Function.update x i 0)
          + t * (F (Function.update x i 1) - F (Function.update x i 0)) := by
    intro x i t
    set k := (finProdFinEquiv.symm i).1 with hk
    set c := (finProdFinEquiv.symm i).2 with hc
    have hki : finProdFinEquiv (k, c) = i := by
      simpa [hk, hc] using Equiv.apply_symm_apply finProdFinEquiv i
    have h0 : (enc (Function.update x i 0)) k c = 0 := by
      rw [enc, Matrix.of_apply, Function.update_apply]
      simp [hki]
    show (P * enc (Function.update x i t) + Q).det
        = (P * enc (Function.update x i 0) + Q).det
          + t * ((P * enc (Function.update x i 1) + Q).det
                 - (P * enc (Function.update x i 0) + Q).det)
    rw [enc_update_zero x k c i hki t, enc_update_zero x k c i hki 1]
    exact det_affine P Q (enc (Function.update x i 0)) k c h0 t
  -- it vanishes on the `0/1` cube exactly when the grid determinants vanish
  have hcube : ∀ b : Fin (d*j) → Bool, F (fun i => if b i then 1 else 0) = 0 := by
    intro b
    have hm : enc (fun i => if b i then 1 else 0)
        = gridMat (fun (k : Fin d) (c : Fin j) => b (finProdFinEquiv (k, c))) := by
      ext k c
      simp only [enc, Matrix.of_apply, gridMat, Matrix.of_apply]
    show (P * enc (fun i => if b i then 1 else 0) + Q).det = 0
    rw [hm]
    exact h _
  have hzero : ∀ x : Fin (d*j) → ℝ, F x = 0 := multiAffine_eq_zero (m := d*j) F haff hcube
  -- but the real slope gives a point where it does not vanish
  have hwit : F (fun i => Λ (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) ≠ 0 := by
    intro hc0
    have h2 : enc (fun i => Λ (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) = Λ := by
      ext k c
      simp only [enc, Matrix.of_apply]
      simp
    have hc0' : (P * enc (fun i => Λ (finProdFinEquiv.symm i).1
        (finProdFinEquiv.symm i).2) + Q).det = 0 := hc0
    rw [h2] at hc0'
    exact hΛ hc0'
  exact hwit (hzero _)

end Work.WilE7.FrontierCS
