import Mathlib
import Submission.Work.WilkiesH.Norm.Defs
import Submission.Work.WilG5.Basic
import Submission.Work.WilG0.API
import Submission.Work.WilkiesH.Omega.omega_poly_le
import Submission.Work.WilkiesH.Omega.omega_poly_lt

/-!
# The normalisation pieces are `Ω`-definable

`normPiece σ = {x : Fin n → ℝ | ∀ i, x i ∈ shapeSet (σ i)}` is the (non-disjoint) cover of
`ℝⁿ` on which every coordinate lies in the region prescribed by `σ`, so it is the
intersection over the coordinates of the one-dimensional region of `σ i` placed on
coordinate `i`.

Each of those coordinate conditions is cut out by at most two *linear* polynomial
inequalities:

* `pos`    : `[0,1]`   = `{0 ≤ x i} ∩ {x i ≤ 1}`,
* `neg`    : `[-1,0]`  = `{-1 ≤ x i} ∩ {x i ≤ 0}`,
* `big`    : `(1,∞)`   = `{1 - x i < 0}`,
* `bigNeg` : `(-∞,-1)` = `{1 + x i < 0}`.

A single linear inequality is `Ω`-definable with format `n + 2` (resp. `n + 3` for the strict
one) and degree `3`, by `Omega.omega_poly_le` (whose auxiliary polynomial raises the degree by
two) resp. `Omega.omega_poly_lt`; intersecting two of them adds one to the format and sums the
degrees, giving format `n + 3` and degree `6` per coordinate.  Intersecting over the `n`
coordinates (the axiom `SOMin.inter`) gives format `n + 4` and degree `6n`, uniformly in `S`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Norm

open WilkiesDesign WilkiesConjecture

/-- A set which is a *non-strict* sublevel set of a linear polynomial lies in `Ω` with format
`n + 2` and degree `3` (`Omega.omega_poly_le` raises the degree by two). -/
private lemma omega_eval_le {n : ℕ} {S : WilkiesDesign.SOMin} {A : Set (Fin n → ℝ)}
    (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ 1) (hA : A = {x | P.eval x ≤ 0}) :
    A ∈ S.Ω (n + 2) 3 n := by
  rw [hA]
  exact Work.WilG0.Omega_mono_FD le_rfl (by omega) (Work.WilkiesH.Omega.omega_poly_le S n P)

/-- A set which is a *strict* sublevel set of a linear polynomial lies in `Ω` with format
`n + 3` and degree `3` (`Omega.omega_poly_lt`). -/
private lemma omega_eval_lt {n : ℕ} {S : WilkiesDesign.SOMin} {A : Set (Fin n → ℝ)}
    (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ 1) (hA : A = {x | P.eval x < 0}) :
    A ∈ S.Ω (n + 3) 3 n := by
  rw [hA]
  exact Work.WilG0.Omega_mono_FD le_rfl (by omega) (Work.WilkiesH.Omega.omega_poly_lt S n P)

/-- Each coordinate condition of a normalisation shape is `Ω`-definable, with format `n + 3`
and degree `6` — bounds depending only on the ambient dimension `n` (and not on `S`). -/
theorem coordShape_mem {n : ℕ} (S : WilkiesDesign.SOMin) (i : Fin n) (s : NormShape) :
    {x : Fin n → ℝ | x i ∈ shapeSet s} ∈ S.Ω (n + 3) 6 n := by
  -- degree bounds for the linear polynomials used below
  have hX : (MvPolynomial.X i : MvPolynomial (Fin n) ℝ).totalDegree ≤ 1 :=
    le_of_eq (MvPolynomial.totalDegree_X i)
  have hC : ∀ a : ℝ, (MvPolynomial.C a : MvPolynomial (Fin n) ℝ).totalDegree ≤ 1 := by
    intro a
    rw [MvPolynomial.totalDegree_C]; omega
  have hsub : ∀ P Q : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ 1 → Q.totalDegree ≤ 1 →
      (P - Q).totalDegree ≤ 1 := by
    intro P Q hP hQ
    exact (MvPolynomial.totalDegree_sub P Q).trans (max_le hP hQ)
  have hadd : ∀ P Q : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ 1 → Q.totalDegree ≤ 1 →
      (P + Q).totalDegree ≤ 1 := by
    intro P Q hP hQ
    exact (MvPolynomial.totalDegree_add P Q).trans (max_le hP hQ)
  cases s with
  | pos =>
    have h1 : {x : Fin n → ℝ | 0 ≤ x i} ∈ S.Ω (n + 2) 3 n := by
      refine omega_eval_le (-MvPolynomial.X i) ?_ ?_
      · rw [MvPolynomial.totalDegree_neg]; exact hX
      · ext x
        simp only [Set.mem_ofPred_eq, MvPolynomial.eval_neg, MvPolynomial.eval_X]
        constructor <;> intro h <;> linarith
    have h2 : {x : Fin n → ℝ | x i ≤ 1} ∈ S.Ω (n + 2) 3 n := by
      refine omega_eval_le (MvPolynomial.X i - MvPolynomial.C (1 : ℝ)) (hsub _ _ hX (hC 1)) ?_
      ext x
      simp only [Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X,
        MvPolynomial.eval_C]
      constructor <;> intro h <;> linarith
    have heq : {x : Fin n → ℝ | x i ∈ shapeSet NormShape.pos} =
        {x : Fin n → ℝ | 0 ≤ x i} ∩ {x : Fin n → ℝ | x i ≤ 1} := by
      ext x
      simp only [shapeSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Icc]
    rw [heq]
    exact Work.WilG0.Omega_mono_FD (by omega) (by omega) (Work.WilG0.Omega_inter2 h1 h2)
  | neg =>
    have h1 : {x : Fin n → ℝ | -1 ≤ x i} ∈ S.Ω (n + 2) 3 n := by
      refine omega_eval_le (MvPolynomial.C (-1 : ℝ) - MvPolynomial.X i)
        (hsub _ _ (hC (-1)) hX) ?_
      ext x
      simp only [Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X,
        MvPolynomial.eval_C]
      constructor <;> intro h <;> linarith
    have h2 : {x : Fin n → ℝ | x i ≤ 0} ∈ S.Ω (n + 2) 3 n := by
      refine omega_eval_le (MvPolynomial.X i) hX ?_
      ext x
      simp only [Set.mem_ofPred_eq, MvPolynomial.eval_X]
    have heq : {x : Fin n → ℝ | x i ∈ shapeSet NormShape.neg} =
        {x : Fin n → ℝ | -1 ≤ x i} ∩ {x : Fin n → ℝ | x i ≤ 0} := by
      ext x
      simp only [shapeSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Icc]
    rw [heq]
    exact Work.WilG0.Omega_mono_FD (by omega) (by omega) (Work.WilG0.Omega_inter2 h1 h2)
  | big =>
    have h1 : {x : Fin n → ℝ | 1 < x i} ∈ S.Ω (n + 3) 3 n := by
      refine omega_eval_lt (MvPolynomial.C (1 : ℝ) - MvPolynomial.X i) (hsub _ _ (hC 1) hX) ?_
      ext x
      simp only [Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X,
        MvPolynomial.eval_C]
      constructor <;> intro h <;> linarith
    have heq : {x : Fin n → ℝ | x i ∈ shapeSet NormShape.big} =
        {x : Fin n → ℝ | 1 < x i} := by
      ext x
      simp only [shapeSet, Set.mem_ofPred_eq, Set.mem_Ioi]
    rw [heq]
    exact Work.WilG0.Omega_mono_FD le_rfl (by omega) h1
  | bigNeg =>
    have h1 : {x : Fin n → ℝ | x i < -1} ∈ S.Ω (n + 3) 3 n := by
      refine omega_eval_lt (MvPolynomial.C (1 : ℝ) + MvPolynomial.X i) (hadd _ _ (hC 1) hX) ?_
      ext x
      simp only [Set.mem_ofPred_eq, MvPolynomial.eval_add, MvPolynomial.eval_X,
        MvPolynomial.eval_C]
      constructor <;> intro h <;> linarith
    have heq : {x : Fin n → ℝ | x i ∈ shapeSet NormShape.bigNeg} =
        {x : Fin n → ℝ | x i < -1} := by
      ext x
      simp only [shapeSet, Set.mem_ofPred_eq, Set.mem_Iio]
    rw [heq]
    exact Work.WilG0.Omega_mono_FD le_rfl (by omega) h1

/-- **The normalisation piece is `Ω`-definable.**  Since `normPiece σ` is the intersection of
the `n` coordinate conditions `x i ∈ shapeSet (σ i)`, which are each `Ω`-definable with format
`n + 3` and degree `6` (`coordShape_mem`), intersecting them costs one more format and sums
the degrees, so `normPiece σ ∈ S.Ω (n + 4) (6n) n`, uniformly in the structure `S`. -/
theorem normPiece_mem {n : ℕ} (σ : Fin n → NormShape) :
    ∃ a b : ℕ, ∀ S : WilkiesDesign.SOMin, normPiece σ ∈ S.Ω a b n := by
  refine ⟨n + 4, 6 * n, fun S => ?_⟩
  have hA : ∀ i : Fin n, {x : Fin n → ℝ | x i ∈ shapeSet (σ i)} ∈ S.Ω (n + 3) 6 n :=
    fun i => coordShape_mem S i (σ i)
  have h := S.inter (fun _ : Fin n => 6)
    (fun i : Fin n => {x : Fin n → ℝ | x i ∈ shapeSet (σ i)}) hA
  have hsum : (∑ _ : Fin n, (6 : ℕ)) = 6 * n := by
    simp [Finset.sum_const, Fintype.card_fin, Nat.mul_comm]
  rw [hsum] at h
  have heq : (⋂ i : Fin n, {x : Fin n → ℝ | x i ∈ shapeSet (σ i)}) = normPiece σ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, normPiece]
  rw [heq] at h
  exact Work.WilG0.Omega_mono_FD (by omega) le_rfl h

end Work.WilkiesH.Norm
