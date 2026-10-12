import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Perm

open Work.BoseSym

/-- The symmetrisation average fixes an element that is already invariant under
every permutation of the particles. -/
theorem symAvgAmb_eq_of_isSym {N : ℕ} {p : Amb N} (hp : IsSym N p) : symAvgAmb N p = p := by
  classical
  have hfix : ∀ σ : Equiv.Perm (Fin N), permAmb N σ p = p := hp
  have hcard : ((Finset.card (Finset.univ : Finset (Equiv.Perm (Fin N)))) : ℝ) =
      (Nat.factorial N : ℝ) := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  unfold symAvgAmb
  rw [Finset.sum_congr rfl (fun σ _ => hfix σ), Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℝ, hcard,
    smul_smul, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero N), one_smul]

end Work.BoseSym.Perm
