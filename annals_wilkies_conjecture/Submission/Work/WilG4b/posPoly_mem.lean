import Mathlib
import Submission.Work.WilG5.Basic
import Submission.Work.WilG1.Basic

/-!
  Area G4b: the positive set of a polynomial is an `Ω`-set.

  The frozen `SOMin.Ω` calculus has hypersurfaces (`SOMin.hyp`) as its only algebraic
  primitives, so inequalities have to be manufactured.  The classical trick: for a
  polynomial `P` in `n` variables consider `Q(x,t) = P(x) + t²` in `n+1` variables.  Then

      `projLast {Q = 0} = {x | P(x) ≤ 0}`

  because `P(x) + t² = 0` has a real solution `t` iff `P(x) ≤ 0` (take `t = √(-P(x))`).
  Complementing turns `≤` into `>`.  Counting the format increments: `hyp` gives format
  `n+1`, `proj` gives `n+2`, `compl` gives `n+3`, and we are allowed `n+4`; the degree
  picks up at most `2` from the square, and we are allowed `P.totalDegree + 3`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.WilG4b

open WilkiesDesign WilkiesConjecture

/-- `P(x) + t²`, where `t` is the last of the `n+1` variables. -/
def posPolyAux {n : ℕ} (P : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin (n + 1)) ℝ :=
  MvPolynomial.rename Fin.castSucc P +
    MvPolynomial.X (Fin.last n) * MvPolynomial.X (Fin.last n)

/-- Evaluation of `posPolyAux` at a point whose last coordinate is `t`. -/
theorem eval_posPolyAux {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (t : ℝ) :
    MvPolynomial.eval (Fin.snoc x t : Fin (n + 1) → ℝ) (posPolyAux P)
      = MvPolynomial.eval x P + t * t := by
  have h1 : MvPolynomial.eval (Fin.snoc x t : Fin (n + 1) → ℝ)
      (MvPolynomial.rename Fin.castSucc P) = MvPolynomial.eval x P := by
    rw [MvPolynomial.eval_rename]
    have hcomp : (Fin.snoc x t : Fin (n + 1) → ℝ) ∘ Fin.castSucc = x := by
      funext i
      exact @Fin.snoc_castSucc n (fun _ => ℝ) t x i
    rw [hcomp]
  simp only [posPolyAux]
  rw [MvPolynomial.eval_add, h1, MvPolynomial.eval_mul, MvPolynomial.eval_X,
    @Fin.snoc_last n (fun _ => ℝ) t x]

/-- The total degree of `posPolyAux P` is at most `P.totalDegree + 3`. -/
theorem td_posPolyAux {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    (posPolyAux P).totalDegree ≤ P.totalDegree + 3 := by
  simp only [posPolyAux]
  refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
  refine max_le ?_ ?_
  · exact le_trans (MvPolynomial.totalDegree_rename_le _ _) (by omega)
  · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.totalDegree_X]
    omega

/-- The projection of the hypersurface `{Q = 0}` is the sublevel set `{P ≤ 0}`. -/
theorem projLast_posPolyAux {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    projLast {z : Fin (n + 1) → ℝ | MvPolynomial.eval z (posPolyAux P) = 0}
      = {x : Fin n → ℝ | MvPolynomial.eval x P ≤ 0} := by
  ext x
  simp only [projLast, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht⟩
    rw [eval_posPolyAux] at ht
    nlinarith [sq_nonneg t]
  · intro hx
    refine ⟨Real.sqrt (-MvPolynomial.eval x P), ?_⟩
    rw [eval_posPolyAux]
    have hsq : Real.sqrt (-MvPolynomial.eval x P) * Real.sqrt (-MvPolynomial.eval x P)
        = -MvPolynomial.eval x P := by
      rw [← sq, Real.sq_sqrt (by linarith)]
    rw [hsq]
    ring

theorem posPoly_mem (S : WilkiesDesign.SOMin) {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    {x : Fin n → ℝ | 0 < MvPolynomial.eval x P} ∈ S.Ω (n + 4) (P.totalDegree + 3) n := by
  have hhyp : {z : Fin (n + 1) → ℝ | MvPolynomial.eval z (posPolyAux P) = 0}
      ∈ S.Ω (n + 1) (posPolyAux P).totalDegree (n + 1) := S.hyp (n + 1) (posPolyAux P)
  have hproj : projLast {z : Fin (n + 1) → ℝ | MvPolynomial.eval z (posPolyAux P) = 0}
      ∈ S.Ω (n + 2) (posPolyAux P).totalDegree n := S.proj hhyp
  rw [projLast_posPolyAux] at hproj
  have hcompl : ({x : Fin n → ℝ | MvPolynomial.eval x P ≤ 0})ᶜ
      ∈ S.Ω (n + 3) (posPolyAux P).totalDegree n := S.compl hproj
  have hset2 : ({x : Fin n → ℝ | MvPolynomial.eval x P ≤ 0})ᶜ
      = {x : Fin n → ℝ | 0 < MvPolynomial.eval x P} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  rw [hset2] at hcompl
  exact Work.WilG5.mem_mono hcompl (n + 4) (P.totalDegree + 3) (by omega) (td_posPolyAux P)

end Work.WilG4b
