import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.ZAll

/-- The five-term quintic `C a * X₀⁵ + C b * X₀²X₁ + C c * X₀X₁³ + C d * X₁⁵ + C e` has total
degree `5` as soon as `a ≠ 0` (the `X₀⁵` term; `b, c, d, e` are arbitrary).

Used by `Work.MotK.TGen.ZElim2IrredCharAll` to split the degrees of a factorisation
`g * h = f` of the five-term quintic (`g.totalDegree + h.totalDegree = 5`).

Route: `ZElim2AuxE.totalDegree_g0p`
(`Submission/Work/MotK/TGen/ZElim2AuxE/totalDegree_g0p.lean`) proves the same statement for `g0p`
by splitting off the degree-`5` part `C a * X₀⁵ + C d * X₁⁵` (use
`MvPolynomial.isHomogeneous_C_mul_X_pow`, `.add`, `.totalDegree` with a nonvanishing argument) and
bounding the remainder by `4` (`MvPolynomial.totalDegree_add`, `le_max_left`,
`MvPolynomial.isHomogeneous_*.totalDegree_le`), then applying
`MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt`.  (`Submission/Work/MotK/TGen/
fiveTermTotalDegree.lean` states the `d ≠ 0` variant and is still `sorry`; this copy with `a ≠ 0`
is the useful one.) -/
theorem FiveTermTotalDegree {K : Type} [Field K] (a b c d e : K) (ha : a ≠ 0) :
    (MvPolynomial.C a * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ 5
      + MvPolynomial.C b * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ 2 * MvPolynomial.X 1
      + MvPolynomial.C c * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
          * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ 3
      + MvPolynomial.C d * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ 5
      + MvPolynomial.C e).totalDegree = 5 := by
  -- The degree-`5` homogeneous part `C a * X₀⁵ + C d * X₁⁵`, nonzero because `a ≠ 0`.
  have hA : (MvPolynomial.C a * (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) ^ 5
      + MvPolynomial.C d * (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) ^ 5 :
      MvPolynomial (Fin 2) K).totalDegree = 5 := by
    have hhom : (MvPolynomial.C a * (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) ^ 5
        + MvPolynomial.C d * (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) ^ 5 :
        MvPolynomial (Fin 2) K).IsHomogeneous 5 :=
      (MvPolynomial.isHomogeneous_C_mul_X_pow a (0 : Fin 2) 5).add
        (MvPolynomial.isHomogeneous_C_mul_X_pow d (1 : Fin 2) 5)
    have hne : (MvPolynomial.C a * (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) ^ 5
        + MvPolynomial.C d * (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) ^ 5 :
        MvPolynomial (Fin 2) K) ≠ 0 := by
      intro h
      have h1 := congrArg (MvPolynomial.eval (![1, 0] : Fin 2 → K)) h
      simp at h1
      exact ha h1
    exact hhom.totalDegree hne
  -- The remainder has total degree at most `4`.
  have hR : (MvPolynomial.C b * (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) ^ 2
      * (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K)
      + MvPolynomial.C c * (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K)
        * (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) ^ 3
      + MvPolynomial.C e : MvPolynomial (Fin 2) K).totalDegree ≤ 4 := by
    have h1 : (MvPolynomial.C b * (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) ^ 2
        * (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) :
        MvPolynomial (Fin 2) K).IsHomogeneous 3 :=
      ((MvPolynomial.isHomogeneous_C (σ := Fin 2) (R := K) b).mul
        (MvPolynomial.isHomogeneous_X_pow (σ := Fin 2) (R := K) (0 : Fin 2) 2)).mul
        (MvPolynomial.isHomogeneous_X (σ := Fin 2) (R := K) (1 : Fin 2))
    have h2 : (MvPolynomial.C c * (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K)
        * (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) ^ 3 :
        MvPolynomial (Fin 2) K).IsHomogeneous 4 :=
      ((MvPolynomial.isHomogeneous_C (σ := Fin 2) (R := K) c).mul
        (MvPolynomial.isHomogeneous_X (σ := Fin 2) (R := K) (0 : Fin 2))).mul
        (MvPolynomial.isHomogeneous_X_pow (σ := Fin 2) (R := K) (1 : Fin 2) 3)
    have h3 : (MvPolynomial.C e : MvPolynomial (Fin 2) K).IsHomogeneous 0 :=
      MvPolynomial.isHomogeneous_C (σ := Fin 2) (R := K) e
    refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
    · refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
      · exact le_trans h1.totalDegree_le (by norm_num)
      · exact le_trans h2.totalDegree_le (by norm_num)
    · exact le_trans h3.totalDegree_le (by norm_num)
  -- Split off the top-degree part.
  have hg : (MvPolynomial.C a * (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) ^ 5
      + MvPolynomial.C b * (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) ^ 2
        * (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K)
      + MvPolynomial.C c * (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K)
        * (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) ^ 3
      + MvPolynomial.C d * (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) ^ 5
      + MvPolynomial.C e : MvPolynomial (Fin 2) K) =
      ((MvPolynomial.C a * (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) ^ 5
        + MvPolynomial.C d * (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) ^ 5 :
        MvPolynomial (Fin 2) K)
      + (MvPolynomial.C b * (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) ^ 2
        * (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K)
        + MvPolynomial.C c * (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K)
          * (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) ^ 3
        + MvPolynomial.C e : MvPolynomial (Fin 2) K)) := by ring
  have hlt : (MvPolynomial.C b * (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) ^ 2
        * (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K)
        + MvPolynomial.C c * (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K)
          * (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) ^ 3
        + MvPolynomial.C e : MvPolynomial (Fin 2) K).totalDegree
      < (MvPolynomial.C a * (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) ^ 5
        + MvPolynomial.C d * (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) ^ 5 :
        MvPolynomial (Fin 2) K).totalDegree :=
    lt_of_le_of_lt hR (by rw [hA]; norm_num)
  rw [hg]
  exact (MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt hlt).trans hA

end Work.MotK.ZAll
