/-
# `Work.FTS.PhiStar.Gegenbauer.Defs` — the explicit angular Dirichlet basis of `Lzero`

`Work.Elliptic.Lzero Ψ = -∂_θθΨ + ∂_θ(tan θ·Ψ) - 6Ψ` is the `α = 0` part of the
self-similar Biot–Savart operator.  Its Dirichlet problem on `(0, π/2)` has *explicit*
spectral data (see `NOTES_bslOp_sol_exists.md` in the parent directory):

* eigenfunctions `e_m(θ) = cos θ · q_m(sin θ)` with `q_m = C_{2m+1}^{(3/2)}` the Gegenbauer
  polynomial of order `3/2` (equivalently `q_m = P'_{2m+2}`, the derivative of the Legendre
  polynomial);
* eigenvalues `λ_m = 2m(2m+5)`, `m = 0,1,2,…`.

`m = 0` gives `e_0 ∝ sin 2θ`, the kernel of `Lzero`; `m = 1` gives
`e_1 = cos θ(sin θ - (7/3) sin³θ)` with `Lzero e_1 = 14 e_1` (the certificate
`Work.FTS.H2.PhiStarE.EigenCertificate`).

The self-adjoint weight is `cos θ dθ`; in the variable `u = sin θ` the eigenproblem is the
classical Gegenbauer problem of order `3/2` with weight `(1-u²)du`, and

  `∫_0^{π/2} e_m e_n cos θ dθ = ∫_0^1 (1-u²) q_m(u) q_n(u) du`.

The engine is the Gegenbauer equation `(1-u²)q'' - 4u q' + n(n+3) q = 0` for `q = C_n^{(3/2)}`
(`n = 2m+1`: `n(n+3) = 4 + 2m(2m+5)`), proved in `Gegenbauer/gC_ode.lean` from the three-term
recurrence below.
-/
import Mathlib.Analysis.Complex.Trigonometric

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.Gegenbauer

set_option autoImplicit false

/-- The Gegenbauer polynomial `C_n^{(3/2)}` of order `3/2`, defined by the classical three-term
recurrence `(n+1)C_{n+1} = 2(n+3/2)x·C_n - (n+2)C_{n-1}`, with `C_0 = 1`, `C_1 = 3x`.

(`C_0 = 1`, `C_1 = 3x`, `C_2 = (15x²-3)/2`, `C_3 = (35x³-15x)/2`, …; in particular
`C_{2m+1}` is an odd polynomial of degree `2m+1`.) -/
def gC : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | 1 => fun x => 3 * x
  | (n + 2) => fun x =>
      (2 * ((n : ℝ) + 5 / 2) * x * gC (n + 1) x - ((n : ℝ) + 3) * gC n x) / ((n : ℝ) + 2)

/-- The `m`-th Dirichlet eigenfunction of `Lzero`: `e_m(θ) = cos θ · gC (2m+1) (sin θ)`. -/
def eFam (m : ℕ) (θ : ℝ) : ℝ := Real.cos θ * gC (2 * m + 1) (Real.sin θ)

/-- The eigenvalue of `eFam m`: `λ_m = 2m(2m+5)`. -/
def lam (m : ℕ) : ℝ := 2 * (m : ℝ) * (2 * (m : ℝ) + 5)

end Work.FTS.PhiStar.Gegenbauer
