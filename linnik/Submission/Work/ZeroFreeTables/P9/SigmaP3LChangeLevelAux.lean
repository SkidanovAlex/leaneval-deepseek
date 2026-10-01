/-
# ZeroFreeTables/P9/SigmaP3LChangeLevelAux

Auxiliary definitions for `SigmaP3L_changeLevel_diff`.

* `sigmaTerm M L χ s a λ₁ n` — the `n`-th summand of `SigmaP3L M L χ s a λ₁`
  (`SigmaP3L_eq_tsum_sigmaTerm` records that `SigmaP3L` is `L⁻¹` times its `tsum`).
* `tailSummand q σ j n` — the summand `1_{¬(n,q)=1} · Λ(n) · n^{-σ} · (log n)^j`
  of the "bad" (non-coprime to the level `q`) part of the von Mangoldt series.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow

open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables.P9

/-- The `n`-th summand of `SigmaP3L M L χ s a λ₁`. -/
def sigmaTerm (M : ℕ) [NeZero M] (L : ℝ) (χ : DirichletCharacter ℂ M) (s : ℂ) (a lam₁ : ℝ)
    (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) * (χ (n : ZMod M) / (n : ℂ) ^ s).re
    * Work.ZeroFreeTables.hbWL L a lam₁ n

/-- `SigmaP3L` is `L⁻¹` times the `tsum` of `sigmaTerm` (definitional). -/
lemma SigmaP3L_eq_tsum_sigmaTerm (M : ℕ) [NeZero M] (L : ℝ) (χ : DirichletCharacter ℂ M)
    (s : ℂ) (a lam₁ : ℝ) :
    Work.ZeroFreeTables.SigmaP3L M L χ s a lam₁
      = L⁻¹ * ∑' n : ℕ, sigmaTerm M L χ s a lam₁ n := rfl

/-- The summand `1_{¬(n,q)=1} · Λ(n) · n^{-σ} · (log n)^j` of the non-coprime tail. -/
def tailSummand (q : ℕ) (σ : ℝ) (j : ℕ) (n : ℕ) : ℝ :=
  (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
    * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j

end Work.ZeroFreeTables.P9
