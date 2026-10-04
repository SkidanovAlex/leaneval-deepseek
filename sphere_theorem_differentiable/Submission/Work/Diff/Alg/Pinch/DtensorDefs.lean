import Mathlib
import Submission.Work.Diff.Alg.Pinch.Linv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Böhm–Wilking difference tensor `D_{a,b}`

For the target `Work.Diff.Alg.Pinch.EFun_X_strict_at_degenerate` the Böhm–Wilking identity
(`Work.Diff.Alg.Pinch.linv_Q_ell` / Theorem 2 of Böhm–Wilking) writes

`ℓ_{a,b}^{-1}(Q(ℓ_{a,b} S)) = Q S + D_{a,b}(S)`

with

`D_{a,b}(S) = ((n-2)b² - 2(a-b)) · (Ric₀ ∧ Ric₀) + 2a · (Ric ∧ Ric) + 2b² · (Ric₀² ∧ id)
              + [(n b²(1-2b) - 2(a-b)(1-2b+nb²)) / (n(1+2(n-1)a)) · |Ric₀|²] · (id ∧ id)`.

This module only records that tensor (for `a = ccA n b`), so that the *strict positivity* of
its Hermitian form on nondegenerate directions — the Böhm–Wilking eigenvalue computation
(Corollary 2.3 / Lemma 3.4 of Böhm–Wilking, Prop. 13 of Brendle–Schoen) — can be stated and
proved independently of the identity itself.
-/

namespace Work.Diff.Alg.Pinch

open Submission.Diff.Alg

variable {n : ℕ}

/-- The Böhm–Wilking tensor `D_{a,b}(S)` (specialized to `a = ccA n b`), i.e. the difference
`ℓ_{a,b}^{-1}(Q(ℓ_{a,b} S)) - Q S`. -/
noncomputable def Dtensor (n : ℕ) (b : ℝ) (S : Curv4 n) : Curv4 n :=
  (((n : ℝ) - 2) * b ^ 2 - 2 * (ccA n b - b)) • knProd (ric0 S) (ric0 S)
    + (2 * ccA n b) • knProd (ric S) (ric S)
    + (2 * b ^ 2) • knProd (ric0sq S) (id2 n)
    + ((((n : ℝ) * b ^ 2 * (1 - 2 * b) - 2 * (ccA n b - b) * (1 - 2 * b + (n : ℝ) * b ^ 2))
        / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * ccA n b))) * ric0Frob2 S)
      • knProd (id2 n) (id2 n)

end Work.Diff.Alg.Pinch
