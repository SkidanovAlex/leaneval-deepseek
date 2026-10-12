import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Submission.Work.BoseB4.Coherent
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

/-- Condensate creation acts on the coherent-state transform as multiplication by `z̄`:
`Φ(a₀†Ψ)(z) = z̄ · Φ(Ψ)(z)`.  This is FS §8.3's crucial identity
`a₀† ↦ z̄` under the `c`-number substitution, stated as the recursion
`cohWeight (n+1) z * √(n+1) = z̄ * cohWeight n z` level by level. -/
theorem Phi_a0d {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Ψ : Work.BoseB4.FockCore E) (z : ℂ) :
    Work.BoseB4.Phi (Work.BoseB4.a0d Ψ) z = (starRingEnd ℂ z) • Work.BoseB4.Phi Ψ z := by
  induction Ψ using Finsupp.induction_linear with
  | zero => simp [Phi, PhiLin]
  | add f g hf hg =>
    rw [map_add, Phi_add, hf, hg, Phi_add, smul_add]
  | single n v =>
    rw [a0d_single, Phi_single, Phi_single, smul_smul, cohWeight_succ, smul_smul]

end Work.BoseB4
