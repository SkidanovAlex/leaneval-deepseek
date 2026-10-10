import Mathlib
import Submission.Work.MotK.TGen.ZElim2Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen.ZElim2AuxE

open MvPolynomial

theorem totalDegree_g0p {L : Type*} [Field L] (r : L) (hr : r ≠ 0) :
    (Work.MotK.TGen.g0p r).totalDegree = 5 := by
  have hr7 : r ^ 7 ≠ 0 := pow_ne_zero 7 hr
  -- The top-degree homogeneous part `r⁷X₀⁵ - r²X₁⁵` has total degree exactly `5`.
  have hA : (C (r ^ 7) * (X (0 : Fin 2)) ^ 5 - C (r ^ 2) * (X (1 : Fin 2)) ^ 5 :
      MvPolynomial (Fin 2) L).totalDegree = 5 := by
    have hhom : (C (r ^ 7) * (X (0 : Fin 2)) ^ 5 - C (r ^ 2) * (X (1 : Fin 2)) ^ 5 :
        MvPolynomial (Fin 2) L).IsHomogeneous 5 :=
      (MvPolynomial.isHomogeneous_C_mul_X_pow (r ^ 7) (0 : Fin 2) 5).sub
        (MvPolynomial.isHomogeneous_C_mul_X_pow (r ^ 2) (1 : Fin 2) 5)
    have hne : (C (r ^ 7) * (X (0 : Fin 2)) ^ 5 - C (r ^ 2) * (X (1 : Fin 2)) ^ 5 :
        MvPolynomial (Fin 2) L) ≠ 0 := by
      intro h
      have h1 : r ^ 7 = 0 := by
        have hc := congrArg (MvPolynomial.eval (![1, 0] : Fin 2 → L)) h
        simpa using hc
      exact hr7 h1
    exact hhom.totalDegree hne
  -- The remaining part has total degree at most `4`.
  have hR : (- C (r ^ 3 * (3 + r ^ 5)) * (X (0 : Fin 2)) ^ 2 * (X (1 : Fin 2))
      + C (1 + 2 * r ^ 5) * (X (0 : Fin 2)) * (X (1 : Fin 2)) ^ 3 + C (r ^ 2) :
        MvPolynomial (Fin 2) L).totalDegree ≤ 4 := by
    have h1 : (- C (r ^ 3 * (3 + r ^ 5)) * (X (0 : Fin 2)) ^ 2 * (X (1 : Fin 2)) :
        MvPolynomial (Fin 2) L).IsHomogeneous 3 := by
      have hc : (- C (r ^ 3 * (3 + r ^ 5)) : MvPolynomial (Fin 2) L).IsHomogeneous 0 :=
        (MvPolynomial.isHomogeneous_C (σ := Fin 2) (R := L) (r ^ 3 * (3 + r ^ 5))).neg
      have hx : ((X (0 : Fin 2)) ^ 2 : MvPolynomial (Fin 2) L).IsHomogeneous 2 :=
        MvPolynomial.isHomogeneous_X_pow (σ := Fin 2) (R := L) (0 : Fin 2) 2
      have hy : (X (1 : Fin 2) : MvPolynomial (Fin 2) L).IsHomogeneous 1 :=
        MvPolynomial.isHomogeneous_X (σ := Fin 2) (R := L) (1 : Fin 2)
      exact (hc.mul hx).mul hy
    have h2 : (C (1 + 2 * r ^ 5) * (X (0 : Fin 2)) * (X (1 : Fin 2)) ^ 3 :
        MvPolynomial (Fin 2) L).IsHomogeneous 4 := by
      have hc : (C (1 + 2 * r ^ 5) : MvPolynomial (Fin 2) L).IsHomogeneous 0 :=
        MvPolynomial.isHomogeneous_C (σ := Fin 2) (R := L) (1 + 2 * r ^ 5)
      have hx : (X (0 : Fin 2) : MvPolynomial (Fin 2) L).IsHomogeneous 1 :=
        MvPolynomial.isHomogeneous_X (σ := Fin 2) (R := L) (0 : Fin 2)
      have hy : ((X (1 : Fin 2)) ^ 3 : MvPolynomial (Fin 2) L).IsHomogeneous 3 :=
        MvPolynomial.isHomogeneous_X_pow (σ := Fin 2) (R := L) (1 : Fin 2) 3
      exact (hc.mul hx).mul hy
    have h3 : (C (r ^ 2) : MvPolynomial (Fin 2) L).IsHomogeneous 0 :=
      MvPolynomial.isHomogeneous_C (σ := Fin 2) (R := L) (r ^ 2)
    refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
    · refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
      · exact le_trans h1.totalDegree_le (by norm_num)
      · exact le_trans h2.totalDegree_le (by norm_num)
    · exact le_trans h3.totalDegree_le (by norm_num)
  -- Split off the top-degree part.
  have hg : Work.MotK.TGen.g0p r =
      (C (r ^ 7) * (X (0 : Fin 2)) ^ 5 - C (r ^ 2) * (X (1 : Fin 2)) ^ 5)
      + (- C (r ^ 3 * (3 + r ^ 5)) * (X (0 : Fin 2)) ^ 2 * (X (1 : Fin 2))
         + C (1 + 2 * r ^ 5) * (X (0 : Fin 2)) * (X (1 : Fin 2)) ^ 3 + C (r ^ 2)) := by
    rw [Work.MotK.TGen.g0p]
    first | refl_ring1 | ring
  have hlt : (- C (r ^ 3 * (3 + r ^ 5)) * (X (0 : Fin 2)) ^ 2 * (X (1 : Fin 2))
      + C (1 + 2 * r ^ 5) * (X (0 : Fin 2)) * (X (1 : Fin 2)) ^ 3 + C (r ^ 2) :
        MvPolynomial (Fin 2) L).totalDegree
      < (C (r ^ 7) * (X (0 : Fin 2)) ^ 5 - C (r ^ 2) * (X (1 : Fin 2)) ^ 5 :
        MvPolynomial (Fin 2) L).totalDegree :=
    lt_of_le_of_lt hR (by rw [hA]; norm_num)
  rw [hg]
  exact (MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt hlt).trans hA

end Work.MotK.TGen.ZElim2AuxE
