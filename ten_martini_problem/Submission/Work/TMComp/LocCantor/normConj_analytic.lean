import Mathlib
import Submission.Work.TMComp.LocCantor.Defs

set_option linter.unusedVariables false

/-!
# C17 (`P_LocCantor`) — analyticity and periodicity of the normalised conjugacy

`normConj A σ x = (√|det A(x)|)⁻¹ • (A(x) · diag(1,σ)).adjugate`.  When `A` has analytic
entries, constant nonvanishing determinant `d`, and is `1`-periodic, every entry of
`normConj A σ` is again analytic on all of `ℝ`, and `normConj A σ` is `1`-periodic.

The proof is purely algebraic: the determinant is the constant `d`, so the scalar prefactor
`(√|det A(x)|)⁻¹` is the constant `(√|d|)⁻¹`; the adjugate of a `2 × 2` matrix has entries
that are (up to sign) entries of `A(x) · diag(1,σ)`, hence analytic; and periodicity is
inherited from `hper`.
-/

namespace Work.TMComp.LocCantor

/-- Entrywise analyticity of the adjugate of a `2 × 2` matrix whose entries are analytic. -/
theorem analyticOnNhd_adjugate_fin_two {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hB : ∀ i j, AnalyticOnNhd ℝ (fun x => B x i j) Set.univ) :
    ∀ i j, AnalyticOnNhd ℝ (fun x => (B x).adjugate i j) Set.univ := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    · simp only [Matrix.adjugate_fin_two, Matrix.cons_val_fin_one, Fin.isValue,
        Matrix.of_apply, Matrix.cons_val']
      first
        | exact hB 1 1
        | exact (hB 0 1).neg
        | exact (hB 1 0).neg
        | exact hB 0 0

theorem normConj_analytic {A : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {σ d : ℝ} (hd : d ≠ 0)
    (hA : ∀ i j, AnalyticOnNhd ℝ (fun x => A x i j) Set.univ) (hdet : ∀ x, (A x).det = d)
    (hper : ∀ x, A (x + 1) = A x) :
    (∀ i j, AnalyticOnNhd ℝ (fun x => Work.TMComp.normConj A σ x i j) Set.univ) ∧
      (∀ x, Work.TMComp.normConj A σ (x + 1) = Work.TMComp.normConj A σ x) := by
  -- the scalar prefactor is the constant `(√|d|)⁻¹`
  have heq : ∀ x, Work.TMComp.normConj A σ x
      = (Real.sqrt |d|)⁻¹ • (A x * Work.TMComp.sgnMat σ).adjugate := by
    intro x
    simp only [Work.TMComp.normConj, hdet x]
  -- entries of `A · diag(1,σ)` are analytic
  have hB : ∀ i j, AnalyticOnNhd ℝ (fun x => (A x * Work.TMComp.sgnMat σ) i j) Set.univ := by
    intro i j
    fin_cases j
    · show AnalyticOnNhd ℝ (fun x => (A x * Work.TMComp.sgnMat σ) i (0 : Fin 2)) Set.univ
      have h : (fun x => (A x * Work.TMComp.sgnMat σ) i (0 : Fin 2)) = fun x => A x i 0 := by
        funext x; simp [Matrix.mul_apply, Fin.sum_univ_two, Work.TMComp.sgnMat]
      rw [h]; exact hA i 0
    · show AnalyticOnNhd ℝ (fun x => (A x * Work.TMComp.sgnMat σ) i (1 : Fin 2)) Set.univ
      have h : (fun x => (A x * Work.TMComp.sgnMat σ) i (1 : Fin 2)) = fun x => A x i 1 * σ := by
        funext x; simp [Matrix.mul_apply, Fin.sum_univ_two, Work.TMComp.sgnMat]
      rw [h]; exact (hA i 1).mul analyticOnNhd_const
  have hadj := analyticOnNhd_adjugate_fin_two hB
  constructor
  · intro i j
    have hfun : (fun x => Work.TMComp.normConj A σ x i j)
        = (Real.sqrt |d|)⁻¹ • (fun x => (A x * Work.TMComp.sgnMat σ).adjugate i j) := by
      funext x
      rw [heq x]
      simp [Matrix.smul_apply]
    rw [hfun]
    exact (hadj i j).const_smul
  · intro x
    rw [heq x, heq (x + 1), hper x]

end Work.TMComp.LocCantor
