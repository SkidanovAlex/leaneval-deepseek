import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG0.API

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign

/-- For a polynomial `P` in `n` variables, the auxiliary polynomial
`Q(x,t) = P(x) + t²` in `n+1` variables.  Its zero set is `Ω`-definable by `SOMin.hyp`, and
its projection to the `x`-coordinates is exactly the sublevel set `{x | P x ≤ 0}`. -/
private def auxPoly {n : ℕ} (P : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin (n + 1)) ℝ :=
  MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) P +
    (MvPolynomial.X (Fin.last n)) ^ 2

/-- Evaluation of `auxPoly P` in coordinates. -/
private theorem auxPoly_eval {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (z : Fin (n + 1) → ℝ) :
    MvPolynomial.eval z (auxPoly P) =
      MvPolynomial.eval (Fin.init z) P + (z (Fin.last n)) ^ 2 := by
  have hinit : (z ∘ Fin.castSucc) = Fin.init z := rfl
  simp only [auxPoly, MvPolynomial.eval_add, MvPolynomial.eval_pow, MvPolynomial.eval_X,
    MvPolynomial.eval_rename, hinit]

/-- `auxPoly` preserves the total degree bound `2`. -/
private theorem auxPoly_totalDegree_le {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ 2) : (auxPoly P).totalDegree ≤ 2 := by
  simp only [auxPoly]
  refine (MvPolynomial.totalDegree_add _ _).trans ?_
  rw [max_le_iff]
  constructor
  · exact (MvPolynomial.totalDegree_rename_le _ _).trans hP
  · refine (MvPolynomial.totalDegree_pow _ 2).trans ?_
    rw [MvPolynomial.totalDegree_X]

/-- The projection of the zero set of `auxPoly P` is the sublevel set `{P ≤ 0}`: a point `x`
is the first `n` coordinates of a zero of `P(x) + t²` iff `P x ≤ 0`. -/
private theorem projLast_auxPoly_zero {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    projLast {w : Fin (n + 1) → ℝ | MvPolynomial.eval w (auxPoly P) = 0}
      = {x : Fin n → ℝ | MvPolynomial.eval x P ≤ 0} := by
  ext x
  simp only [projLast, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht⟩
    rw [auxPoly_eval P (Fin.snoc x t), Fin.init_snoc, Fin.snoc_last] at ht
    linarith [sq_nonneg t]
  · intro hx
    refine ⟨Real.sqrt (-(MvPolynomial.eval x P)), ?_⟩
    rw [auxPoly_eval P (Fin.snoc x _), Fin.init_snoc, Fin.snoc_last,
      Real.sq_sqrt (by linarith : (0 : ℝ) ≤ -(MvPolynomial.eval x P))]
    ring

/-- The sublevel set of a polynomial of total degree at most `2` is `Ω`-definable with format
`n + 2` and degree `2`: add the variable `t` and the equation `P(x) + t² = 0`, take the zero
set (`SOMin.hyp`, degree is `(auxPoly P).totalDegree ≤ 2`), and project out `t`
(`SOMin.proj` raises the format by one, giving `n + 2`). -/
theorem omega_poly_le_two (S : WilkiesDesign.SOMin) (n : ℕ) (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ 2) :
    {x : Fin n → ℝ | P.eval x ≤ 0} ∈ S.Ω (n + 2) 2 n := by
  have hQtd : (auxPoly P).totalDegree ≤ 2 := auxPoly_totalDegree_le P hP
  have hhyp : {w : Fin (n + 1) → ℝ | MvPolynomial.eval w (auxPoly P) = 0} ∈
      S.Ω (n + 1) (auxPoly P).totalDegree (n + 1) := S.hyp (n + 1) (auxPoly P)
  have h2 : {w : Fin (n + 1) → ℝ | MvPolynomial.eval w (auxPoly P) = 0} ∈
      S.Ω (n + 1) 2 (n + 1) := Work.WilG0.Omega_mono_D hQtd hhyp
  have hproj : projLast {w : Fin (n + 1) → ℝ | MvPolynomial.eval w (auxPoly P) = 0} ∈
      S.Ω (n + 2) 2 n :=
    Work.WilG0.Omega_mono_F (show n + 1 + 1 ≤ n + 2 by omega) (S.proj h2)
  rwa [projLast_auxPoly_zero] at hproj

end Work.WilCrux
