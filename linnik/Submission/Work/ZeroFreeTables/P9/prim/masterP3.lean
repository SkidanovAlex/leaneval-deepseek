/-
# ZeroFreeTables/P9/prim/masterP3

The single-point `P₃` master bound (HB §9): for a non-principal primitive character,
`1 + a/L`-line and `|Im s| ≤ 4`, the log-derivative quality `LogDerivHyp` bounds the
smoothed von Mangoldt functional by the near-zero sum plus `α(c+e)`.

This file starts the proof with the **explicit-formula application**: the identity
`SigmaP3L_eq_logDeriv_derivs` is combined with `lDiffExplicit_gen` at `k = 1, 2` to replace
`(L'/L)` and its first two iterated derivatives by the zero sums and the trivial
(parity) sums.  The result — `SigmaP3L_eq_explicit_zeros` below — is the shape every
downstream near/far estimate consumes.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P9.lDiffExplicit_gen
import Submission.Work.ZeroFreeTables.P9.prim.SigmaP3L_eq_logDeriv_derivs

open DirichletCharacter Complex
open scoped Classical BigOperators

namespace Work.ZeroFreeTables.P9.prim

open Work.ZeroFreeTables

/-- **Explicit-formula application.**  For a non-principal primitive character `χ` with parity
`par ∈ {0,1}` and `1 < Re s`, the smoothed von Mangoldt functional is

`Σ(s,χ) = -(α/L)(L'/L)(s).re - (α/L)² (Z₂(s) + T₂(s)).re - (2/3)(α/L)³ (Z₃(s) + T₃(s)).re`,

`α = a + λ₁`, where `Z_k(s) = Σ_u zeroMult(χ,u) (s-u)^{-(k+1)}` is the zero sum and
`T_k(s) = Σ_n (s + par + 2n)^{-(k+1)}` is the trivial/parity sum, `k = 1, 2`.  This is the
form in which the §9 zero-free estimate (via the near/far split and `LogDerivHyp`) is applied. -/
theorem SigmaP3L_eq_explicit_zeros {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) (par : ℕ) (hpar0 : χ.Even → par = 0) (hpar1 : χ.Odd → par = 1)
    {s : ℂ} (hs : 1 < s.re) (a lam₁ L : ℝ) :
    SigmaP3L N L χ s a lam₁
      = -((a + lam₁) / L) * (logDeriv (DirichletCharacter.LFunction χ) s).re
        - ((a + lam₁) / L) ^ 2 *
            ((∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2)
              + ∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2).re
        - (2 / 3) * ((a + lam₁) / L) ^ 3 *
            ((∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3)
              + ∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3).re := by
  -- the explicit formula at k = 1 and k = 2
  obtain ⟨_, hform2⟩ :=
    Work.ZeroFreeTables.P9.lDiffExplicit_gen χ hχ hprim 1 (by norm_num) par hpar0 hpar1 hs
  obtain ⟨_, hform3⟩ :=
    Work.ZeroFreeTables.P9.lDiffExplicit_gen χ hχ hprim 2 (by norm_num) par hpar0 hpar1 hs
  -- Z₂ + T₂ = - (L'/L)'   and   Z₃ + T₃ = (1/2) (L'/L)''
  have hsum2 : (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2)
      + ∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2
      = - iteratedDeriv 1 (logDeriv (DirichletCharacter.LFunction χ)) s := by
    simpa using hform2
  have hsum3 : (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3)
      + ∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3
      = (1 / 2 : ℂ) * iteratedDeriv 2 (logDeriv (DirichletCharacter.LFunction χ)) s := by
    simpa using hform3
  have hD1 : iteratedDeriv 1 (logDeriv (DirichletCharacter.LFunction χ)) s
      = - ((∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2)
            + ∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2) := by
    rw [hsum2]; ring
  have hD2 : iteratedDeriv 2 (logDeriv (DirichletCharacter.LFunction χ)) s
      = 2 * ((∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3)
            + ∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3) := by
    rw [hsum3]; ring
  rw [SigmaP3L_eq_logDeriv_derivs χ hs a lam₁ L, hD1, hD2, Complex.neg_re, Complex.mul_re]
  norm_num
  ring

end Work.ZeroFreeTables.P9.prim
