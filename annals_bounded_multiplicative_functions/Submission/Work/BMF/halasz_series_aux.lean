import Mathlib
import Submission.Work.BMF.halasz_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary definitions for `Work.BMF.halasz_series_bound`

The local Euler factor `g_p(s) = Σ_{e≥0} f(p^e) (p^e)^{-s}` of a multiplicative `f`,
the log-derivative `Ψ(s) = Σ_p g_p'(s)/g_p(s)` of the Euler product `G = LSeries f`,
its prime part `Ψ₁(s) = -Σ_p f(p) log p · p^{-s}`, and the remainder `Ψ₂ = Ψ - Ψ₁`.

These are used by `Work.BMF.halasz_series_bound`.
-/

namespace Work.BMF

open Finset Real Complex

/-- The local Euler factor `g_p(s) = Σ_{e ≥ 0} f(p^e) (p^e)^{-s}` of `f` at the prime `p`. -/
noncomputable def gp (f : ℕ → ℂ) (p : ℕ) (s : ℂ) : ℂ :=
  ∑' e : ℕ, LSeries.term f s (p ^ e)

/-- The (formal) log-derivative `Ψ(s) = Σ_p g_p'(s)/g_p(s)` of the Euler product of `f`. -/
noncomputable def Psi (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, deriv (gp f p) s / gp f p s

/-- The prime part `Ψ₁(s) = -Σ_p f(p) (log p) p^{-s}` of `Ψ`. -/
noncomputable def Psi1 (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, -(f p * (Real.log (p : ℕ) : ℂ) * (p : ℂ) ^ (-s))

/-- The remainder `Ψ₂ = Ψ - Ψ₁` (higher prime powers and the `p^{-2σ}` corrections). -/
noncomputable def Psi2 (f : ℕ → ℂ) (s : ℂ) : ℂ := Psi f s - Psi1 f s

end Work.BMF
