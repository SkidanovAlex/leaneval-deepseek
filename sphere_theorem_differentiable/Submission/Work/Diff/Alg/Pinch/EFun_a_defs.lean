import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.BQDefs
import Submission.Work.Diff.Alg.q2p_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Parameters and the decomposition data for `EFun_X_strict_at_degenerate_a`

Brendle–Schoen, *Manifolds with 1/4-pinched curvature are space forms*, Proposition 14, and
Böhm–Wilking, *Manifolds with positive curvature operators are space forms*, Lemma 3.5.

The cone `Ĉ(a)`, `a > 1/2`, is `Ĉ(a) = ℓ_{a,1/2}(D(p))` with `p = 1 - 4/(n-2+8a)`; writing
`s = 2a - 1` (so `p = 1 - 4/(n+2+4s)`), the Böhm–Wilking correction term `D_{a,1/2}(S)` has, next
to the (frame dependent) operator eigenvalue decomposition of Böhm–Wilking Corollary 2.3, the
following *frame free* decomposition into Kulkarni–Nomizu products of positive semidefinite
`2`-tensors:

`D_{a,1/2}(S) = ((n+2)/4) • (A ∧ A) + (2 s λ̄) • (B ∧ id) + (1/2) • (Ric₀² ∧ id) + γ • (id ∧ id)`

with `λ̄ = scal(S)/n`, `A = Ric₀(S) + (4λ̄/(n+2)) • id`, `B = Ric₀(S) + (4λ̄/(n+2+4s)) • id`, and

`γ = λ̄² ((n-2)/(n+2) + s(n-6+4s)/(n+2+4s)) - s |Ric₀(S)|² / (4(n + (n-1)s))`.

This is the form of Böhm–Wilking's computation used here: the Ricci pinching hypothesis
`Ric ≥ (p/n) scal` says exactly that `B` is positive semidefinite (`B = Ric - p λ̄ id`), and the
λ̄²/|Ric₀|² part of `γ` is then positive by the estimate
`|Ric₀|² ≤ n(n-1)(1-p)²λ̄²` (Böhm–Wilking, proof of Lemma 3.5).
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- The Böhm–Wilking parameter `s = 2a - 1` of the cone family `Ĉ(a)`, `a > 1/2`. -/
noncomputable def bwS (a : ℝ) : ℝ := 2 * a - 1

/-- The Ricci pinching parameter `p = 1 - 4/(n - 2 + 8a)` of the cone `Ĉ(a)` (Brendle–Schoen
Prop. 14).  Equivalently `p = 1 - 4/(n + 2 + 4s)` with `s = 2a - 1`. -/
noncomputable def bwP (n : ℕ) (a : ℝ) : ℝ := 1 - 4 / ((n : ℝ) - 2 + 8 * a)

/-- The mean curvature `λ̄ = scal(S)/n`. -/
noncomputable def bwLam (n : ℕ) (S : Curv4 n) : ℝ := scalAlg S / (n : ℝ)

/-- The positive semidefinite `2`-tensor `A = Ric₀(S) + (4λ̄/(n+2)) • id` of the decomposition. -/
noncomputable def bwA (n : ℕ) (S : Curv4 n) : Fin n → Fin n → ℝ :=
  fun i j => ric0 S i j + (4 * bwLam n S / ((n : ℝ) + 2)) * id2 n i j

/-- The positive semidefinite `2`-tensor `B = Ric₀(S) + (4λ̄/(n+2+4s)) • id` of the
decomposition; under the hypothesis `RicPinch p S` this is `B = Ric(S) - p λ̄ • id`. -/
noncomputable def bwB (n : ℕ) (a : ℝ) (S : Curv4 n) : Fin n → Fin n → ℝ :=
  fun i j => ric0 S i j + (4 * bwLam n S / ((n : ℝ) + 2 + 4 * bwS a)) * id2 n i j

/-- The coefficient `γ` of the `(id ∧ id)` term in the decomposition of `D_{a,1/2}(S)`. -/
noncomputable def bwGamma (n : ℕ) (a : ℝ) (S : Curv4 n) : ℝ :=
  bwLam n S ^ 2 * (((n : ℝ) - 2) / ((n : ℝ) + 2)
      + bwS a * (((n : ℝ) - 6 + 4 * bwS a) / ((n : ℝ) + 2 + 4 * bwS a)))
    - bwS a * ric0Frob2 S / (4 * ((n : ℝ) + ((n : ℝ) - 1) * bwS a))

end Work.Diff.Alg.Pinch
