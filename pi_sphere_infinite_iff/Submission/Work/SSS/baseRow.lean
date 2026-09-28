import Mathlib
import Submission.Work.SSS.Packet
import Submission.Work.SSS.BaseRowMain
import Submission.Work.SSS.Lem.finite_E2_zero_zero

/-!
# The bottom-row edge statement of the convergence of the spectral sequence

For a saturated filtration `ξ` of a chain complex `C` of `ℤ`-modules (in the sense of
`Work.SSS.Filtration`), the bottom row argument of the spectral sequence shows that the `E²` term
`E²_{n,0}` is finitely generated as soon as `H_n(C)` is and all the `E²` terms `E²_{n-r,r-1}` of
total degree `n-1` are (`2 ≤ r ≤ n`).

The proof uses the chain of submodules `baseZ ξ (n-1) 2 ⊇ … ⊇ baseZ ξ (n-1) (n+1)` of the row
`E¹_{n,0}`; the successive quotients are the strata of the image filtration of `H_{n-1}(F_{n-1})`
(which are subquotients of the `E²` page in total degree `n-1`), while the last term is
`ker (E¹_{n,0} → H_{n-1}(F_{n-1}))`, whose quotient by the boundaries `baseB ξ (n-1)` is
`H_n(C)/Φ_{n-1}`.
-/

set_option autoImplicit false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits

/-- The **bottom-row edge statement** of the convergence of the spectral sequence of a saturated
filtration: `E²_{n,0}` is finitely generated when `H_n(C)` is and all E² terms `E²_{n-r,r-1}`
of total degree `n-1` are (`2 ≤ r ≤ n`). -/
theorem baseRow (C : ChainComplex (ModuleCat ℤ) ℕ) (ξ : Work.SSS.Filtration C) (n : ℕ)
    (hH : Module.Finite ℤ (C.homology n))
    (hE : ∀ r : ℕ, 2 ≤ r → r ≤ n → Module.Finite ℤ (Work.SSS.E2 ξ (n - r) (r - 1))) :
    Module.Finite ℤ (Work.SSS.E2 ξ n 0) := by
  rcases n with _ | m
  · exact Work.SSS.Lem.finite_E2_zero_zero ξ hH
  · refine (finite_E2_succ_iff ξ m).mpr ?_
    rw [ker_d1_eq_baseZ_two ξ m]
    exact fgQuot_baseB_baseZ_two ξ m hH hE

end Work.SSS
