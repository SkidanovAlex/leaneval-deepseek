/-
# Vocabulary of the lifting proof of Theorem `bile` at `r = 1` (paper: Proposition `bile-2`)

This module fixes the objects of the lifting argument by which the finite-cyclic arithmetic
bilinear estimate is deduced from the physical minor-arc estimate `ImprovKMT`:

* `bileLift ψ R u` -- the lift `n ↦ R^{-1/2} ψ(n/R) u (n mod Q)` of a function on `ℤ/Qℤ`;
* `bileHalvedAvg P N u v` -- the halved average at scale `N`,
  `z ↦ N⁻¹ ∑_{N/2 < n ≤ N} u(z-n) v(z-P(n))`, i.e. `AhalfR TZ N X P` applied to the lifts;
* `bileLiftSum P ψ R N u v` -- the same sum with the lifted inputs, i.e. the physical average
  `Ã_N(bileLift ψ R u, bileLift ψ R v)`.

Nothing is asserted here; the lemmas about these objects live in the companion modules
(`BileLiftKmtProjZero`, `BileLiftAhalfLimit`, ...).
-/
import Mathlib

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.KMTPlan.A6

noncomputable section

open Polynomial Finset

/-- The lift of a function on `ℤ/Qℤ` by a window `ψ` at scale `R`: `n ↦ R^{-1/2} ψ(n/R) u(n)`. -/
noncomputable def bileLift (ψ : ℝ → ℂ) (R : ℕ) {Q : ℕ} (u : ZMod Q → ℂ) : ℤ → ℂ :=
  fun n => ((Real.sqrt (R : ℝ))⁻¹ : ℂ) * ψ ((n : ℝ) / (R : ℝ)) * u (n : ZMod Q)

/-- The halved average at scale `N` on `ℤ/Qℤ`: `z ↦ N⁻¹ ∑_{N/2 < n ≤ N} u(z-n) v(z-P(n))`.
This is the average computed by `AhalfR TZ N X P` on periodic data. -/
noncomputable def bileHalvedAvg (P : Polynomial ℤ) (N : ℕ) {Q : ℕ}
    (u v : ZMod Q → ℂ) : ZMod Q → ℂ :=
  fun z => (N : ℂ)⁻¹ * ((Finset.Icc (N / 2 + 1) N).sum fun n : ℕ =>
    u (z - (n : ℤ)) * v (z - Polynomial.eval (n : ℤ) P))

/-- The physical halved average of the *lifts*: `x ↦ N⁻¹ ∑_{N/2 < n ≤ N}
`bileLift ψ R u (x-n) · bileLift ψ R v (x-P(n))`.  This is `AhalfR TZ N X P` applied to the two
lifts, written out so that the companion lemmas need no unfolding. -/
noncomputable def bileLiftSum (P : Polynomial ℤ) (ψ : ℝ → ℂ) (R N : ℕ) {Q : ℕ}
    (u v : ZMod Q → ℂ) : ℤ → ℂ :=
  fun x => (N : ℂ)⁻¹ * ((Finset.Icc (N / 2 + 1) N).sum fun n : ℕ =>
    bileLift ψ R u (x - (n : ℤ)) * bileLift ψ R v (x - Polynomial.eval (n : ℤ) P))

end

end Work.KMTPlan.A6
