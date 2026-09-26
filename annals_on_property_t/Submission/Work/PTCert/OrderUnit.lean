import Submission.Work.PTCert.Checkers

/-!
# PTCert — the order-unit lemma (residual absorption)

For a product `g` of `n` letters (identity or Nielsen transvections),
`2 - g - g⁻¹ = star (1 - g) * (1 - g) ≤ 2 n² Δ` in the `Σ²` order.  Used to absorb the (exact,
rational, tiny) residual between the numerical certificate and the target into the slack
`(λ - λ') Δ` (Ozawa / Netzer–Thom), so that the SDP solution never has to satisfy the linear
constraints exactly.
-/

open OnPropertyT Submission.FreeGroupAut Submission.RouteB Submission.RouteB.Edge
open scoped BigOperators

set_option autoImplicit false

namespace Submission.PTCert

/-- **(Q4) Order-unit lemma.** -/
def OrderUnitLemma (r : ℕ) : Prop :=
  ∀ ks : List ℕ, (∀ k ∈ ks, k < NB1 r) →
    IsSOS (((2 * ks.length ^ 2 : ℕ) : ℝ) • deltaSub r r
      - ((2 : ℝ) • (1 : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r))))
          - MonoidAlgebra.of ℝ _ (lprod r ks) - MonoidAlgebra.of ℝ _ (lprod r ks)⁻¹))

end Submission.PTCert
