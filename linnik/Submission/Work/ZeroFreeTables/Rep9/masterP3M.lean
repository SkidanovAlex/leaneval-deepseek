import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.P9.prim.masterP3_assembly

namespace Work.ZeroFreeTables.Rep9

theorem masterP3M {a δ c e M : ℝ} (ha : 0 < a) (hδ0 : 0 < δ) (hδ1 : δ < 1) (he : 0 < e) :
    ∃ L₀ : ℝ, ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hprim : χ.IsPrimitive) {L lam₁ : ℝ}, L₀ ≤ L → Real.log (N:ℝ) ≤ L → 0 ≤ lam₁ →
      lam₁ ≤ M → Work.ZeroFreeTables.LogDerivHyp χ δ L c →
      ∀ s : ℂ, s.re = 1 + a/L → |s.im| ≤ 4 →
        Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
          ≤ -Work.ZeroFreeTables.P3NearSumL N L χ s a lam₁ δ + (a + lam₁) * (c + e) :=
  Work.ZeroFreeTables.P9.prim.masterP3 ha hδ0 hδ1 he M

end Work.ZeroFreeTables.Rep9
