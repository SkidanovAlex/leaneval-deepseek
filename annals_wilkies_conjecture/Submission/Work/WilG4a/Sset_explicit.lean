import Mathlib
import Submission.Work.WilG1.Plumb.SsetMem

set_option linter.unusedSimpArgs false

namespace Work.WilG4a

open WilkiesDesign
open Work.WilG1.Plumb

/-- Explicit `Ω`-bounds for the derivative set `Sset N i f`: whenever `graphOf f` lies in
`S.Ω F D (N+1)`, the set of pairs `(x,c)` for which `c` is the `i`-th partial derivative of `f`
at `x` lies in `S.Ω (AFR N F + 1) ((2 X + (2 KK N + 4 N + 80)).eval D) (N+1)`.

This is the explicit-constant strengthening of `Work.WilG1.Plumb.Sset_omega_aux`, which only
asserts the existence of *some* numeral format and *some* polynomial degree bound. -/
theorem Sset_explicit {S : WilkiesDesign.SOMin} {N F D : ℕ} {f : (Fin N → ℝ) → ℝ} (i : Fin N)
    (hf : WilkiesDesign.graphOf f ∈ S.Ω F D (N + 1)) :
    Work.WilG1.Plumb.Sset N i f ∈
      S.Ω (Work.WilG1.Plumb.AFR N F + 1)
        ((Polynomial.C 2 * Polynomial.X + Polynomial.C (2 * Work.WilG1.Plumb.KK N + N * 4 + 80)).eval D)
        (N + 1) := by
  -- `innerSet` is an Ω-set, at format `AA N F + 1` and degree `DEG0 N D`.
  have hin : innerSet N i f ∈ S.Ω (AA N F + 1) (DEG0 N D) (bigDim N) :=
    innerSet_mem (S := S) i hf
  -- Complement it.
  have hinc : (innerSet N i f)ᶜ ∈ S.Ω (AA N F + 1 + 1) (DEG0 N D) (bigDim N) := S.compl hin
  -- Project the last `N + 2` coordinates out, then complement: this is `∀ y u w`.
  have hpj : projYSet N i f ∈ S.Ω (A0 N F) (DEG0 N D) (aDim N) := by
    have h := Work.WilG5.projN_mem (S := S) (n := aDim N) (N + 2) (AA N F + 1 + 1)
      (DEG0 N D) hinc
    have h' := S.compl h
    simpa [projYSet, A0] using h'
  -- `δ > 0` is the positivity set of the hyperplane `δ = 0`.
  have hposd : posDSet N ∈ S.Ω (A0 N F) 3 (aDim N) := by
    have h := Work.WilG1.Calc.pos_mem (S := S) (m := aDim N) 0
      (MvPolynomial.X (dIdxA N) : MvPolynomial (Fin (aDim N)) ℝ)
    exact Work.WilG1.Omega.mono (by simpa [posDSet] using h) (le_A0_posD N F)
      (by simp [MvPolynomial.totalDegree_X])
  have hI1 : posDSet N ∩ projYSet N i f ∈ S.Ω (A1 N F) (DEG1 N D) (aDim N) := by
    have h := inter_same hposd hpj
    simpa [A1, DEG1] using h
  -- Project the last coordinate `δ`: this is `∃ δ > 0`.
  have hpd : projDSet N i f ∈ S.Ω (A1 N F + 1) (DEG1 N D) (bDim N) := by
    have h := Work.WilG5.projN_mem (S := S) (n := bDim N) 1 (A1 N F) (DEG1 N D) hI1
    simpa [projDSet] using h
  have hpdc : (projDSet N i f)ᶜ ∈ S.Ω (A1 N F + 1 + 1) (DEG1 N D) (bDim N) := S.compl hpd
  -- `ε > 0`.
  have hpse : posESet N ∈ S.Ω (A2 N F) 3 (bDim N) := by
    have h := Work.WilG1.Calc.pos_mem (S := S) (m := bDim N) 0
      (MvPolynomial.X (eIdxB N) : MvPolynomial (Fin (bDim N)) ℝ)
    exact Work.WilG1.Omega.mono (by simpa [posESet] using h) (le_A2_posE N F)
      (by simp [MvPolynomial.totalDegree_X])
  have hpdc' : (projDSet N i f)ᶜ ∈ S.Ω (A2 N F) (DEG1 N D) (bDim N) := by
    simpa [A2] using hpdc
  have hI2 : posESet N ∩ (projDSet N i f)ᶜ ∈ S.Ω (A3 N F) (DEG2 N D) (bDim N) := by
    have h := inter_same hpse hpdc'
    simpa [A3, DEG2] using h
  -- Project the last coordinate `ε`, then complement: this is `∀ ε > 0`.
  have hSs : Sset N i f ∈ S.Ω (AFR N F + 1) (DEG2 N D) (N + 1) := by
    have h := Work.WilG5.projN_mem (S := S) (n := N + 1) 1 (A3 N F) (DEG2 N D) hI2
    have h' := S.compl h
    simpa [Sset, AFR] using h'
  -- The explicit degree polynomial is exactly `DEG2`.
  have hb : (Polynomial.C 2 * Polynomial.X + Polynomial.C (2 * KK N + N * 4 + 80)).eval D
      = DEG2 N D := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  rw [hb]
  exact hSs

end Work.WilG4a
