import Mathlib
import Submission.Work.KT.PsiC.BFrame

/-!
# `Work.PsiC.invB_gamB_perm`

The position permutation `invB n` (reversal of the three tensor pairs) inverts the six-cycle
`gamB n = (cB n)⁻¹ * sB n` of the frame-B computation, and is itself an involution:

`invB * gamB * invB = gamB⁻¹`,   `invB * invB = 1`.

Both claims are pure permutation computations on the index type
`IB n = (I2 n × I2 n) × I2 n`, `I2 n = Fin n × Fin n`, and are checked pointwise after
evaluating the two generators `cB` and `sB` (`Work.KT.PsiC.cB_apply`, `Work.KT.PsiC.sB_apply`).
-/

namespace Work.PsiC

/-- `invB n` reverses the three pairs of the frame-B index. -/
theorem invB_apply (n : ℕ) (a b c d e f : Fin n) :
    Work.KT.PsiC.invB n (((a, b), (c, d)), (e, f)) = (((e, f), (c, d)), (a, b)) := rfl

/-- `gamB n = (cB n)⁻¹ * sB n` swaps each pair and rotates the pairs forwards. -/
theorem gamB_apply (n : ℕ) (a b c d e f : Fin n) :
    Work.KT.PsiC.gamB n (((a, b), (c, d)), (e, f)) = (((d, c), (f, e)), (b, a)) := by
  show ((Work.KT.PsiC.cB n)⁻¹ * Work.KT.PsiC.sB n) (((a, b), (c, d)), (e, f)) = _
  rw [Equiv.Perm.mul_apply, Work.KT.PsiC.sB_apply]
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
  exact (Work.KT.PsiC.cB_apply n d c f e b a).symm

/-- The inverse of `gamB n` rotates the first entries the other way. -/
theorem gamB_inv_apply (n : ℕ) (a b c d e f : Fin n) :
    (Work.KT.PsiC.gamB n)⁻¹ (((a, b), (c, d)), (e, f)) = (((f, e), (b, a)), (d, c)) := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
  exact (gamB_apply n f e b a d c).symm

/-- `invB n` is an involution. -/
theorem invB_mul_self (n : ℕ) : Work.KT.PsiC.invB n * Work.KT.PsiC.invB n = 1 := by
  apply Equiv.ext
  intro x
  rcases x with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩
  simp [invB_apply]

/-- `invB n` conjugates `gamB n` into its inverse. -/
theorem invB_conj_gamB (n : ℕ) :
    Work.KT.PsiC.invB n * Work.KT.PsiC.gamB n * Work.KT.PsiC.invB n =
      (Work.KT.PsiC.gamB n)⁻¹ := by
  apply Equiv.ext
  intro x
  rcases x with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩
  simp only [Equiv.Perm.mul_apply, invB_apply, gamB_apply, gamB_inv_apply]

theorem invB_gamB_perm (n : ℕ) :
    Work.KT.PsiC.invB n * Work.KT.PsiC.gamB n * Work.KT.PsiC.invB n = (Work.KT.PsiC.gamB n)⁻¹ ∧
      Work.KT.PsiC.invB n * Work.KT.PsiC.invB n = 1 :=
  ⟨invB_conj_gamB n, invB_mul_self n⟩

end Work.PsiC
