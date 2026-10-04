import Mathlib
import Submission.Work.Diff.Alg.Pinch.RicFormDefs
import Submission.Work.Diff.Alg.Pinch.inPIC2_ric_eq_zero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Positivity of the scalar curvature of a nonzero algebraic curvature tensor in `PIC2`

If `S ≠ 0` is an algebraic curvature tensor in the cone `InPIC2` (`PIC2 ≥ 0`, i.e. `M × ℝ²` has
nonnegative isotropic curvature), then its scalar curvature is strictly positive.

The two ingredients are

* `inPIC2_metric_basic`: `InPIC2 R` implies `scalAlg R ≥ 0` and makes the Ricci tensor
  positive semidefinite;
* `inPIC2_ric_eq_zero`: the `PIC2` cone meets the hyperplane `ric = 0` only at the origin.

Indeed `scalAlg` is the trace of the positive semidefinite Ricci tensor, so `scalAlg S = 0` forces
`ric S = 0`, whence `S = 0` by `inPIC2_ric_eq_zero`.  (The hypothesis `RicPinch p S` with `p < 1`
is therefore not needed: `InPIC2` alone suffices.  In particular the statement covers the pinching
parameter `p = 1 - 4 / ((n : ℝ) - 2 + 8a)` of the Böhm–Wilking cone.)
-/

set_option linter.unusedVariables false

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg Matrix

variable {n : ℕ}

/-- The quadratic form `∑ᵢⱼ Mᵢⱼ vᵢ vⱼ` of a matrix, written as a dot product:
`∑ᵢⱼ Mᵢⱼ vᵢ vⱼ = v ⬝ᵥ (M *ᵥ v)`. -/
private lemma sum2_eq_dotProduct_mulVec (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    (∑ i, ∑ j, M i j * v i * v j) = v ⬝ᵥ (M *ᵥ v) := by
  simp only [dotProduct, mulVec]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  ring

/-- The Ricci tensor of an algebraic curvature tensor is symmetric. -/
private lemma ric_symm' {R : Curv4 n} (hR : IsAlgCurv R) (i j : Fin n) :
    ric R i j = ric R j i := by
  simp only [ric]
  exact Finset.sum_congr rfl (fun k _ => hR.2.1 k j k i)

/-- `scalAlg` is the trace of the Ricci tensor. -/
private lemma sum_ric_diag (R : Curv4 n) : (∑ i, ric R i i) = scalAlg R := by
  simp only [ric, scalAlg]
  rw [Finset.sum_comm]

/-- If `R` lies in the `PIC2` cone and `scalAlg R = 0` then its Ricci tensor vanishes. -/
lemma ric_eq_zero_of_scalAlg_eq_zero {R : Curv4 n} (hR : IsAlgCurv R) (hP : InPIC2 R)
    (hscal : scalAlg R = 0) : ∀ i j, ric R i j = 0 := by
  set M : Matrix (Fin n) (Fin n) ℝ := fun i j => ric R i j with hMdef
  -- `M` is Hermitian and positive semidefinite by `InPIC2`
  have hHerm : M.IsHermitian := by
    refine Matrix.IsHermitian.ext ?_
    intro i j
    rw [hMdef]
    simp only [star_trivial]
    exact ric_symm' hR j i
  have hPSD : M.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm ?_
    intro x
    rw [star_trivial, ← sum2_eq_dotProduct_mulVec]
    simp only [hMdef, ric]
    exact (inPIC2_metric_basic n).2.1 R hP x
  -- its trace is `scalAlg R`, hence vanishes, so all diagonal entries vanish
  have htrace : ∑ i, M i i = 0 := by
    rw [hMdef]
    show (∑ i, ric R i i) = 0
    rw [sum_ric_diag, hscal]
  have hdiag : ∀ i, M i i = 0 := by
    intro i
    have h1 : M i i ≤ ∑ j, M j j :=
      Finset.single_le_sum (f := fun j => M j j) (fun j _ => hPSD.diag_nonneg)
        (Finset.mem_univ i)
    rw [htrace] at h1
    exact le_antisymm h1 hPSD.diag_nonneg
  -- a positive semidefinite matrix with vanishing quadratic form on `eᵢ` kills the column `i`
  intro i j
  have hji : ric R j i = 0 := by
    have hq : (Pi.single i (1 : ℝ) : Fin n → ℝ) ⬝ᵥ
        (M *ᵥ (Pi.single i (1 : ℝ) : Fin n → ℝ)) = 0 := by
      rw [Matrix.mulVec_single_one, single_one_dotProduct]
      exact hdiag i
    have hcol : M *ᵥ (Pi.single i (1 : ℝ) : Fin n → ℝ) = 0 := by
      refine (hPSD.dotProduct_mulVec_zero_iff (x := (Pi.single i (1 : ℝ) : Fin n → ℝ))).mp ?_
      simpa using hq
    have h2 := congrFun hcol j
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at h2
    rw [hMdef] at h2
    simpa using h2
  rw [ric_symm' hR i j]
  exact hji

/-- A nonzero algebraic curvature tensor in the `PIC2` cone has strictly positive scalar curvature.
The Ricci pinching hypothesis is not needed for this statement. -/
theorem scalAlg_pos_of_inPIC2_ricpinch (n : ℕ) (hn2 : 2 ≤ n) {a : ℝ} (ha : 1 / 2 < a)
    {S : Submission.Diff.Alg.Curv4 n} (hS : Submission.Diff.Alg.IsAlgCurv S)
    (hS0 : S ≠ 0) (hP : Submission.Diff.Alg.InPIC2 S)
    (hric : Work.Diff.Alg.Pinch.RicPinch (1 - 4 / ((n : ℝ) - 2 + 8 * a)) S) :
    0 < Submission.Diff.Alg.scalAlg S / (n : ℝ) := by
  have hn : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hnonneg : 0 ≤ scalAlg S := (inPIC2_metric_basic n).2.2 S hP
  rcases eq_or_lt_of_le hnonneg with h0 | hpos
  · exfalso
    exact hS0 (inPIC2_ric_eq_zero n hS hP (ric_eq_zero_of_scalAlg_eq_zero hS hP h0.symm))
  · exact div_pos hpos hn

end Work.Diff.Alg.Pinch
