import Mathlib
import Submission.Work.BoseBoxFock.SymBlocks
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

@[reducible] noncomputable def instSymQ2exCEndACG {m : ℕ} [NeZero m] :
    AddCommGroup (Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m)) :=
  LinearMap.addCommGroup
attribute [local instance] instSymQ2exCEndACG

theorem SymQ2exC_blocks {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    Work.BoseBoxFock.Q2exC f E =
      (E.rho : ℂ) • (Work.BoseBoxFock.BNω f E
        + (((E.W1omega0 : ℝ)) : ℂ) • Work.BoseBoxFock.nPlusChi f
        - ((((E.W1omega 0 + E.W1omega0) : ℝ)) : ℂ) • Work.BoseBoxFock.nmF f 0) := by
  -- `nmF f k` and `nOpC (f k)` are the same operator, so the two sides are sums
  -- of the single mode word `creOfE (f k) ∘ₗ annOfE (f k)` with the weights
  -- `ρ(Ŵ₁ω(k) + Ŵ₁ω(0))` (left) and `ρŴ₁ω(k) + ρŴ₁ω(0)` (right); the left sum
  -- omits `k = 0`, which is exactly the subtracted `k = 0` term on the right.
  simp only [Work.BoseBoxFock.Q2exC, Work.BoseBoxFock.BNω, Work.BoseBoxFock.nPlusChi,
    Work.BoseBoxFock.nmF, Work.BoseBoxFock.nOpC]
  rw [Work.BoseBoxFock.sum_excited_eq_sub]
  rw [smul_sub, smul_add, smul_smul, Finset.smul_sum]
  rw [Finset.smul_sum]
  rw [← Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [smul_smul, ← add_smul]
    congr 1
    push_cast
    ring
  · rw [smul_smul, ← Complex.ofReal_mul]

end Work.BoseBoxFock
