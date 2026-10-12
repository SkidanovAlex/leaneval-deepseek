import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Bridge

/-- The symmetrisation average of a function bounded by `C` is bounded by `C`:
`symAvgF N f x = (N!)⁻¹ ∑_σ f (σ · x)` is a convex combination (`1/N! ≥ 0` and the
`N!` numerators sum to `N!`) of values of `f`, so the triangle inequality gives
`|symAvgF N f x| ≤ (N!)⁻¹ ∑_σ |f (σ · x)| ≤ (N!)⁻¹ · N! · C = C`. -/
theorem abs_symAvgF_le {N : ℕ} {f : Work.BoseSym.Conf N → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ C) (x : Work.BoseSym.Conf N) :
    |Work.BoseSym.symAvgF N f x| ≤ C := by
  simp only [Work.BoseSym.symAvgF, Submission.BoseGases.symAvg]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (Nat.factorial N : ℝ))]
  have hsum : |∑ σ : Equiv.Perm (Fin N), f (Submission.BoseGases.actPerm N σ x)| ≤
      (Nat.factorial N : ℝ) * C := by
    calc |∑ σ : Equiv.Perm (Fin N), f (Submission.BoseGases.actPerm N σ x)|
        ≤ ∑ σ : Equiv.Perm (Fin N), |f (Submission.BoseGases.actPerm N σ x)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin N), C := Finset.sum_le_sum (fun σ _ => hf _)
      _ = (Nat.factorial N : ℝ) * C := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
          simp [nsmul_eq_mul]
  calc 1 / (Nat.factorial N : ℝ) *
        |∑ σ : Equiv.Perm (Fin N), f (Submission.BoseGases.actPerm N σ x)|
      ≤ 1 / (Nat.factorial N : ℝ) * ((Nat.factorial N : ℝ) * C) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = C := by
        have hfac : (Nat.factorial N : ℝ) ≠ 0 := by positivity
        field_simp

end Work.BoseSym.Bridge
