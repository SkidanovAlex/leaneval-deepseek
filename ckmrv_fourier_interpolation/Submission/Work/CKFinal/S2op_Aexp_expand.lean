import Mathlib
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Kernels.KernelEquations

namespace Work.CKFinal

/-- `S2op` is additive in the function variable: it is the group-algebra slash by
`S(T-I)²`, and `slash` is additive in the function (`Work.Kernels.slash_add_F`). -/
private lemma S2opAexp_add (k : ℤ) (F G : UpperHalfPlane → ℂ) :
    Work.Asymptotics.S2op k (F + G) = Work.Asymptotics.S2op k F + Work.Asymptotics.S2op k G := by
  simp only [Work.Asymptotics.S2op]
  exact Work.Kernels.slash_add_F k _ F G

/-- `S2op` is `ℂ`-homogeneous in the function variable (`Work.Kernels.slash_smul_F`). -/
private lemma S2opAexp_smul (k : ℤ) (c : ℂ) (F : UpperHalfPlane → ℂ) :
    Work.Asymptotics.S2op k (c • F) = c • Work.Asymptotics.S2op k F := by
  simp only [Work.Asymptotics.S2op]
  exact Work.Kernels.slash_smul_F k _ c F

/-- The `S(T-I)²`-defect operator `Work.Asymptotics.S2op` is `ℂ`-linear in its function
variable, so on the non-decaying part `𝒢(σ,it) = Aexp G σ t` of the CKMRV kernel it acts
coefficientwise: the `t`-dependent factors `1`, `(it)`, `e^{2πt}`, `e^{2πt}(it)` pass straight
through. -/
theorem S2op_Aexp_expand (k : ℤ) (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (t : ℝ) :
    Work.Asymptotics.S2op k (fun σ : UpperHalfPlane => Work.Asymptotics.Aexp G σ t) τ
      = Work.Asymptotics.S2op k (G 0 0) τ + ((t : ℂ) * Complex.I) * Work.Asymptotics.S2op k (G 0 1) τ
        + Complex.exp (2 * Real.pi * t)
          * (Work.Asymptotics.S2op k (G 1 0) τ
            + ((t : ℂ) * Complex.I) * Work.Asymptotics.S2op k (G 1 1) τ) := by
  -- Rewrite `Aexp G · t` as the constant-coefficient `ℂ`-linear combination of the `G i j`.
  have hfe : (fun σ : UpperHalfPlane => Work.Asymptotics.Aexp G σ t)
      = G 0 0 + ((t : ℂ) * Complex.I) • G 0 1
        + Complex.exp (2 * Real.pi * t) • (G 1 0 + ((t : ℂ) * Complex.I) • G 1 1) := by
    ext σ
    simp only [Work.Asymptotics.Aexp, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfe]
  -- Push the operator through the linear combination, coefficientwise.
  simp only [S2opAexp_add, S2opAexp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

end Work.CKFinal
