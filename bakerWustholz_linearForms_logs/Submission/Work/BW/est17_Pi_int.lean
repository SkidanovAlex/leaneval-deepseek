import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.auxpolydefs
import Submission.Work.BW.deltaRat_int

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The `Π`-factor `∏_m Δ(γ_{ι m}(λ); t_m)` of the rational factor of the `est17` expansion is an
integer: each factor is `deltaRat (gamInt b k Lm (ι m) (fun i => (lm.2.2 i : ℕ))) (t m) ∈ ℤ` by
`deltaRat_int`, hence so is their product. -/
theorem est17_Pi_int {K : Type*} [Field K] [NumberField K] {n r : ℕ} {v : ℕ}
    {b : Fin n → ℤ} {k : Fin n} {Lm : Fin r → Fin n → ℤ} {σl : Fin r → ℝ}
    {ι : Fin (r - 1) → Fin n} {t : Fin (r - 1) → ℕ}
    (lm : AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl)) :
    ∃ N : ℤ, (∏ m, Polynomial.aeval
        (((∑ i, derVec b k Lm (ι m) i * (lm.2.2 i : ℤ)) : ℤ) : ℚ) (deltaPoly (t m)))
      = (N : ℚ) := by
  -- Each factor is `deltaRat (γ_{ι m}(λ)) (t m)`, an integer by `deltaRat_int`.
  choose N hN using fun m =>
    deltaRat_int (∑ i, derVec b k Lm (ι m) i * (lm.2.2 i : ℤ)) (t m)
  refine ⟨∏ m, N m, ?_⟩
  rw [Int.cast_prod]
  exact Finset.prod_congr rfl fun m _ => hN m

end Work.BW
