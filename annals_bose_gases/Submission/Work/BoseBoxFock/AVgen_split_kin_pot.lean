import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.rowSplitDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

set_option maxHeartbeats 800000

/-- **The kinetic/potential isolation of `AVgen`.**  Every summand of `AVgen` carries either
only the kinetic weights (`E.tau`, `E.b`, `E.eT`, `E.d`, `E.ell`) or only the potential weights
(`E.W1`, `E.W1omega`, `E.W1omega0`, `E.hatChi`, `E.hatChiSq`, `E.fL`, `E.mu`); the contact and
chemical rows additionally use `gHat0`.  Zeroing the potential weights and `gHat0`
(`kinOnlyEnv`, `PHs = ∅`, `gHat0 = 0`) therefore leaves exactly the kinetic group, and zeroing
the kinetic weights (`potOnlyEnv`) leaves exactly the potential group; the two groups are
disjoint, so the operator splits as claimed.  Pure case analysis on the twelve summands:
unfold, kill the vanishing coefficients, `ring`. -/
theorem AVgen_split_kin_pot {m : ℕ} [NeZero m] {n : ℕ}
    (B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) →
      ((Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ) → ((Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ))
    (idop : ((Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ) → ((Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ))
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (T_NH : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    Work.BoseBoxFock.AVgen B idop f g T_NH PHs E gHat0
      = Work.BoseBoxFock.AVgen B idop f g T_NH ∅ (Work.BoseBoxFock.kinOnlyEnv E) 0
        + Work.BoseBoxFock.AVgen B idop f g T_NH PHs (Work.BoseBoxFock.potOnlyEnv E) gHat0 := by
  funext x
  simp only [Work.BoseBoxFock.AVgen, Work.BoseBoxFock.kinOnlyEnv, Work.BoseBoxFock.potOnlyEnv,
    Pi.add_apply]
  simp
  ring

end Work.BoseBoxFock
