import Mathlib
import Submission.Work.WilCrux.Clean.LineSliceDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilCrux.Clean

open WilkiesDesign

/-!
## `Work.WilCrux.Clean.sliceLineSet_mem`

The slicing affine set `sliceLineSet n i w₁ ⊆ ℝ^{n+2}` (see `LineSliceDefs`) is the intersection
over `j : Fin n` of the hyperplanes `z (sxIdx n j) = w₁ j + z (sTIdx n) · (if j = i then 1 else 0)`.
Each is the zero set of the *linear* polynomial

`sliceLinePoly n i w₁ j = X (sxIdx n j) - C (w₁ j) - X (sTIdx n) * C (if j = i then 1 else 0)`,

whose coefficients involve `w₁` but whose total degree is `≤ 1` (the `if` is a *constant* of the
polynomial ring, so the product `X * C c` has degree `≤ 1`, not `2`).  Hence `S.hyp` gives each
hyperplane a format `n+2` and degree `≤ 1` — independent of `w₁` — and `SOMin.inter` intersects
the `n` of them, producing format `n+3` and degree `∑ j, (sliceLinePoly n i w₁ j).totalDegree ≤ n`,
which `mem_mono` sends to the required format and degree `(n+3, n)`.
-/

/-- The linear polynomial whose zero set is the `j`-th equation defining the slicing line
`x = w₁ + t · eᵢ` inside `ℝ^{n+2}`. -/
def sliceLinePoly (n : ℕ) (i : Fin n) (w₁ : Fin n → ℝ) (j : Fin n) :
    MvPolynomial (Fin (n + 2)) ℝ :=
  MvPolynomial.X (sxIdx n j) - MvPolynomial.C (w₁ j) -
    MvPolynomial.X (sTIdx n) * MvPolynomial.C (if j = i then (1 : ℝ) else 0)

/-- `sliceLinePoly` has total degree `≤ 1`: it is a difference of a linear form and a constant
times one variable. -/
theorem sliceLinePoly_totalDegree_le (n : ℕ) (i : Fin n) (w₁ : Fin n → ℝ) (j : Fin n) :
    (sliceLinePoly n i w₁ j).totalDegree ≤ 1 := by
  unfold sliceLinePoly
  refine le_trans (Work.WilG5.td_sub_le _ _) (max_le ?_ ?_)
  · refine le_trans (Work.WilG5.td_sub_le _ _) (max_le ?_ ?_)
    · exact Work.WilG5.td_X_le _
    · exact le_trans (Work.WilG5.td_C_le _) (by omega)
  · refine le_trans (Work.WilG5.td_mul_le _ _) ?_
    have h1 : (MvPolynomial.X (sTIdx n) : MvPolynomial (Fin (n + 2)) ℝ).totalDegree ≤ 1 :=
      Work.WilG5.td_X_le _
    have h2 : (MvPolynomial.C (if j = i then (1 : ℝ) else 0) :
        MvPolynomial (Fin (n + 2)) ℝ).totalDegree ≤ 0 :=
      Work.WilG5.td_C_le _
    omega

/-- The individual equation of `sliceLineSet` is the zero set of `sliceLinePoly`. -/
theorem sliceLineSet_eq_iInter (n : ℕ) (i : Fin n) (w₁ : Fin n → ℝ) :
    sliceLineSet n i w₁ = ⋂ j : Fin n,
      {z : Fin (n + 2) → ℝ | MvPolynomial.eval z (sliceLinePoly n i w₁ j) = 0} := by
  ext z
  simp only [sliceLineSet, Set.mem_ofPred_eq, Set.mem_iInter, sliceLinePoly,
    MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
  constructor
  · intro h j
    have hj := h j
    show z (sxIdx n j) - w₁ j - z (sTIdx n) * (if j = i then 1 else 0) = 0
    linarith
  · intro h j
    have hj := h j
    linarith

theorem sliceLineSet_mem (S : WilkiesDesign.SOMin) {n : ℕ} (i : Fin n) (w₁ : Fin n → ℝ) :
    Work.WilCrux.Clean.sliceLineSet n i w₁ ∈ S.Ω (n + 3) n (n + 2) := by
  classical
  have hsingle : ∀ j : Fin n,
      {z : Fin (n + 2) → ℝ | MvPolynomial.eval z (sliceLinePoly n i w₁ j) = 0} ∈
        S.Ω (n + 2) (sliceLinePoly n i w₁ j).totalDegree (n + 2) :=
    fun j => S.hyp (n + 2) (sliceLinePoly n i w₁ j)
  have hmem : (⋂ j : Fin n,
      {z : Fin (n + 2) → ℝ | MvPolynomial.eval z (sliceLinePoly n i w₁ j) = 0}) ∈
      S.Ω ((n + 2) + 1) (∑ j : Fin n, (sliceLinePoly n i w₁ j).totalDegree) (n + 2) :=
    S.inter (fun j : Fin n => (sliceLinePoly n i w₁ j).totalDegree)
      (fun j : Fin n =>
        {z : Fin (n + 2) → ℝ | MvPolynomial.eval z (sliceLinePoly n i w₁ j) = 0}) hsingle
  rw [sliceLineSet_eq_iInter]
  refine Work.WilG5.mem_mono hmem (n + 3) n (by omega) ?_
  have h1 : (∑ j : Fin n, (sliceLinePoly n i w₁ j).totalDegree) ≤ ∑ _ : Fin n, 1 :=
    Finset.sum_le_sum (fun j _ => sliceLinePoly_totalDegree_le n i w₁ j)
  have h2 : (∑ _ : Fin n, 1) = n := by simp
  omega

end Work.WilCrux.Clean
