import Mathlib
import Submission.Commons.NumberTheory.Zeta.xi_logDeriv_re_lower_general

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `xi_logDeriv_re_lower`: the real part of the log-derivative of the completed zeta is
bounded below on the strip `1 < σ ≤ 2`, `|t| ≥ H`.

Let `xi(s) := (1/2)·s·(s−1)·completedRiemannZeta s` (the Riemann `ξ` function).  The
classical lower bound `Re(ξ′/ξ)(σ+i·t) ≥ −C` for `1 < σ ≤ 2` and large `|t|` is a direct
consequence of the uniform bound on the whole half-plane `Re s > 1` published as
`Commons.NumberTheory.Zeta.xi_logDeriv_re_lower_general` (whose proof runs through the
Hadamard partial fraction of the entire completion `Ξ(s) = 1/2 + (1/2)·s·(s−1)·Λ₀(s)`
over its zeros, all lying in the critical strip: every partial-fraction summand
`Re(1/(s−ρ)) + Re(1/ρ) ≥ 0` contributes nonnegatively on `Re s > 1`).
-/

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- Real part of the logarithmic derivative of the completed zeta function is bounded below on
the strip `1 < σ ≤ 2` away from the real axis: `∃ C > 0, ∃ H ≥ 2`, `∀ |t| ≥ H`, `∀ 1 < σ ≤ 2`,
`-C ≤ Re(ξ′/ξ(σ + i·t))` with `ξ(s) = (1/2)·s·(s−1)·completedRiemannZeta s`. -/
theorem xi_logDeriv_re_lower :
    ∃ C : ℝ, 0 < C ∧ ∃ H : ℝ, (2 : ℝ) ≤ H ∧
      ∀ t : ℝ, H ≤ |t| → ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
        -C ≤ (logDeriv (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s)
            (((σ : ℂ) + (t : ℂ) * Complex.I))).re := by
  rcases xi_logDeriv_re_lower_general with ⟨C, hCpos, hCore⟩
  refine ⟨C, hCpos, (2 : ℝ), by norm_num, ?_⟩
  intro t ht σ hσ1 hσ2
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hs : (1 : ℝ) < s.re := by
    dsimp [s]
    simp [hσ1]
  have hb := hCore s hs
  simpa [s] using hb

end Commons.NumberTheory.Zeta
