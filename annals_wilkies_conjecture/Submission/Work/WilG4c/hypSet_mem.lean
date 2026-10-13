/-
  `Work.WilG4c.hypSet_mem`: the domain condition of the `ε`-`δ` formula,

    `hypSet N = {(x,c,ε,δ,y,u,w) | ∑ i, (y_i - x_i)^2 < δ^2}`,

  is an `Ω`-set in the ambient space `ℝ^{bigDim N}`.

  Proof strategy.  `hypSet N` is the positivity set of the polynomial

    `hypPoly N = X_δ^2 - ∑ i, (X_{y_i} - X_{x_i})^2`

  (of total degree at most `2`), and positivity sets of polynomials are `Ω`-sets by
  `Work.WilG1.Calc.pos_mem` — the classical identity `0 < p ↔ ∃ t, t^2 p = 1` writes the
  positivity set as the projection of a hypersurface.  `pos_mem` gives format
  `bigDim N + 2` and degree `(hypPoly N).totalDegree + 2`; the degree is raised to the
  explicit numeral `4` using `(hypPoly N).totalDegree ≤ 2`.
-/
import Mathlib
import Submission.Work.WilG4c.EpsSetDefs

set_option autoImplicit false

noncomputable section

namespace Work.WilG4c

open WilkiesDesign

/-! ## The polynomial whose positivity set is `hypSet N` -/

/-- The polynomial `δ^2 - ∑ i, (y_i - x_i)^2` on the big space. -/
def hypPoly (N : ℕ) : MvPolynomial (Fin (bigDim N)) ℝ :=
  MvPolynomial.X (dIdx N) ^ 2
    - ∑ i : Fin N, (MvPolynomial.X (yIdx N i) - MvPolynomial.X (xIdx N i)) ^ 2

/-- Evaluation of `hypPoly` in coordinates. -/
theorem eval_hypPoly (N : ℕ) (z : Fin (bigDim N) → ℝ) :
    MvPolynomial.eval z (hypPoly N) =
      z (dIdx N) ^ 2 - ∑ i : Fin N, (z (yIdx N i) - z (xIdx N i)) ^ 2 := by
  simp only [hypPoly, MvPolynomial.eval_sub, MvPolynomial.eval_sum, MvPolynomial.eval_pow,
    MvPolynomial.eval_X]

/-- `hypSet N` is the positivity set of `hypPoly N`. -/
theorem hypSet_eq (N : ℕ) :
    hypSet N = {z : Fin (bigDim N) → ℝ | 0 < MvPolynomial.eval z (hypPoly N)} := by
  ext z
  rw [hypSet, Set.mem_ofPred_eq, Set.mem_ofPred_eq, eval_hypPoly]
  constructor <;> intro h <;> linarith

/-! ## Degree bookkeeping -/

/-- Each summand of `hypPoly` has total degree at most `2`. -/
theorem td_sq_sub_le (N : ℕ) (i : Fin N) :
    ((MvPolynomial.X (yIdx N i) - MvPolynomial.X (xIdx N i) :
        MvPolynomial (Fin (bigDim N)) ℝ) ^ 2).totalDegree ≤ 2 := by
  have hpq : (MvPolynomial.X (yIdx N i) - MvPolynomial.X (xIdx N i) :
      MvPolynomial (Fin (bigDim N)) ℝ).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
    simp
  calc ((MvPolynomial.X (yIdx N i) - MvPolynomial.X (xIdx N i) :
        MvPolynomial (Fin (bigDim N)) ℝ) ^ 2).totalDegree
      ≤ 2 * (MvPolynomial.X (yIdx N i) - MvPolynomial.X (xIdx N i) :
          MvPolynomial (Fin (bigDim N)) ℝ).totalDegree := MvPolynomial.totalDegree_pow _ 2
    _ ≤ 2 * 1 := by linarith
    _ = 2 := by norm_num

/-- `hypPoly N` has total degree at most `2`. -/
theorem totalDegree_hypPoly_le (N : ℕ) : (hypPoly N).totalDegree ≤ 2 := by
  have hsq : (MvPolynomial.X (dIdx N) ^ 2 : MvPolynomial (Fin (bigDim N)) ℝ).totalDegree
      ≤ 2 := by
    calc (MvPolynomial.X (dIdx N) ^ 2 : MvPolynomial (Fin (bigDim N)) ℝ).totalDegree
        ≤ 2 * (MvPolynomial.X (dIdx N) : MvPolynomial (Fin (bigDim N)) ℝ).totalDegree :=
          MvPolynomial.totalDegree_pow _ 2
      _ = 2 := by rw [MvPolynomial.totalDegree_X]
  have hsum : (∑ i : Fin N, (MvPolynomial.X (yIdx N i) - MvPolynomial.X (xIdx N i) :
      MvPolynomial (Fin (bigDim N)) ℝ) ^ 2).totalDegree ≤ 2 := by
    exact MvPolynomial.totalDegree_finsetSum_le
      (s := (Finset.univ : Finset (Fin N))) (d := 2)
      (f := fun i : Fin N => ((MvPolynomial.X (yIdx N i) - MvPolynomial.X (xIdx N i) :
        MvPolynomial (Fin (bigDim N)) ℝ) ^ 2))
      (hf := fun i _ => td_sq_sub_le N i)
  rw [hypPoly]
  exact le_trans (MvPolynomial.totalDegree_sub _ _) (max_le hsq hsum)

/-! ## The main lemma -/

theorem hypSet_mem (S : WilkiesDesign.SOMin) (N : ℕ) :
    ∃ A B : ℕ, Work.WilG4c.hypSet N ∈ S.Ω A B (Work.WilG4c.bigDim N) := by
  have hpos : {z : Fin (bigDim N) → ℝ | 0 < MvPolynomial.eval z (hypPoly N)} ∈
      S.Ω (bigDim N + 2) ((Polynomial.C ((hypPoly N).totalDegree + 2)).eval N)
        (bigDim N) :=
    Work.WilG1.Calc.pos_mem (S := S) (m := bigDim N) N (hypPoly N)
  have hmem : hypSet N ∈
      S.Ω (bigDim N + 2) ((Polynomial.C ((hypPoly N).totalDegree + 2)).eval N)
        (bigDim N) := by
    rw [hypSet_eq N]
    exact hpos
  refine ⟨bigDim N + 2, 4, ?_⟩
  refine Work.WilG5.mem_mono hmem (bigDim N + 2) 4 le_rfl ?_
  simp only [Polynomial.eval_C]
  have htd := totalDegree_hypPoly_le N
  omega

end Work.WilG4c
