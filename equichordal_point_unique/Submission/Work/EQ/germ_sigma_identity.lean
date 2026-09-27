import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.germ_value_defs
import Submission.Work.EQ.germ_poly_identity

/-!
# `germ_sigma_identity`: `σ(u)² · (1 + R(ℓu)²) = 1`, cleared

With `ℓ = eqLam a` and the rational germ `h = N/D` (`D(0) ≠ 0`), the semi-projective
`x`-coordinate is `X(u) = Λ(u)/P2(u)` and `σ(u) = X(ℓu) + X(u) = Ψ(u)/Θ(u)`, where

* `P2(u) = N(ℓu)D(u) - N(u)D(ℓu)`,
* `Λ(u) = (a/2)·P2(u) + a·N(u)·D(ℓu)`,
* `Ψ(u) = Λ(ℓu)P2(u) + Λ(u)P2(ℓu)`, `Θ(u) = P2(u)P2(ℓu)`, `E = N² + D²`.

The statement below is Rychlik's key identity `σ(u)²·(1 + R(ℓu)²) = 1` with the denominators
`Θ(u)²` and `D(ℓu)²` cleared:

```
Ψ(u)² · E(ℓu) = D(ℓu)² · Θ(u)².
```

The proof has two ingredients.

* **A purely algebraic identity.**  Writing `N₀ = N(u)`, `N₁ = N(ℓu)`, `N₂ = N(ℓ²u)` and
  `D₀ = D(u)`, `D₁ = D(ℓu)`, `D₂ = D(ℓ²u)`, `P = N₁D₀ - N₀D₁`, `Q = N₂D₁ - N₁D₂`,
  `Δ = N₂D₀ - N₀D₂`, one computes
  ```
  Ψ = (a/2)(P·Q + Q·P) + a(N₁D₂·P + N₀D₁·Q) = a·N₁·D₁·Δ,
  ```
  all of the `N₀N₁D₁D₂` terms cancelling.  (`hPsi` below.)

* **The germ identity at `ℓu`.**  `germ_poly_identity` evaluated at `ℓu` (where `(ℓu)/ℓ = u`)
  reads `P²Q² = a²N₁²·E(ℓu)·Δ²`, i.e. `Θ(u)² = a²N₁²·E(ℓu)·Δ²`.

Then `Ψ(u)² E(ℓu) = a²N₁²D₁²Δ²E(ℓu) = D₁²Θ(u)²`, which is the claim.
-/

namespace Work.EQ

open Polynomial

theorem germ_sigma_identity {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) {N D : Polynomial ℂ} (hD0 : Polynomial.eval 0 D ≠ 0)
    (hDN : ∀ᶠ u in nhds (0 : ℂ), h u * Polynomial.eval u D = Polynomial.eval u N) (u : ℂ) :
    (Work.EQ.Psip N D (a : ℂ) (Work.EQ.eqLam a : ℂ)).eval u ^ 2 *
        (Work.EQ.Ep N D).eval ((Work.EQ.eqLam a : ℂ) * u)
      = ((D.eval ((Work.EQ.eqLam a : ℂ) * u)) ^ 2) *
        (Work.EQ.ThetaP N D (Work.EQ.eqLam a : ℂ)).eval u ^ 2 := by
  have hℓ0 : (eqLam a : ℂ) ≠ 0 := by
    have h1 : (1 : ℝ) - a ≠ 0 := by linarith
    have h2 : (1 : ℝ) + a ≠ 0 := by linarith
    have h3 : eqLam a ≠ 0 := by
      rw [eqLam]; exact div_ne_zero h1 h2
    exact_mod_cast h3
  -- the germ identity at `ℓu`; here `(ℓu)/ℓ = u`
  have h4 := germ_poly_identity ha0 ha1 hh hD0 hDN ((eqLam a : ℂ) * u)
  rw [mul_div_cancel_left₀ u hℓ0] at h4
  -- the `Ψ`-expansion `Ψ(u) = a·N(ℓu)·D(ℓu)·(N(ℓ²u)D(u) - N(u)D(ℓ²u))`
  have hPsi : (Psip N D (a : ℂ) (eqLam a : ℂ)).eval u
      = (a : ℂ) * (N.eval ((eqLam a : ℂ) * u)) * (D.eval ((eqLam a : ℂ) * u))
        * (N.eval ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) * D.eval u
           - N.eval u * D.eval ((eqLam a : ℂ) * ((eqLam a : ℂ) * u))) := by
    simp only [Psip, Lam, P2p, Np, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_comp]
    ring
  have hTheta : (ThetaP N D (eqLam a : ℂ)).eval u
      = (N.eval ((eqLam a : ℂ) * u) * D.eval u - N.eval u * D.eval ((eqLam a : ℂ) * u))
        * (N.eval ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) * D.eval ((eqLam a : ℂ) * u)
           - N.eval ((eqLam a : ℂ) * u) * D.eval ((eqLam a : ℂ) * ((eqLam a : ℂ) * u))) := by
    simp only [ThetaP, P2p, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_comp]
  have hE : (Ep N D).eval ((eqLam a : ℂ) * u)
      = N.eval ((eqLam a : ℂ) * u) ^ 2 + D.eval ((eqLam a : ℂ) * u) ^ 2 := by
    simp [Ep, Polynomial.eval_add, Polynomial.eval_pow]
  rw [hPsi, hTheta, hE]
  linear_combination (-(D.eval ((eqLam a : ℂ) * u)) ^ 2) * h4

end Work.EQ
