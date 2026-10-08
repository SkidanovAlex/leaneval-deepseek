import Mathlib
import Submission.Work.ThmF.ChV12.irreducible_of_orderOf_prime
import Submission.Work.ThmF.ChV12.odd_ppd_normalizes_of_FT

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

-- **(2026-10-07, area owner).**  The Feit–Thompson-free statement of this node is not derivable in
-- this workspace (see the status report in `ChV12/ppdClosureProp_holds.lean`: the FT-free substitute
-- is Hering's classification of transitive linear groups, CFSG-level).  Per the lead's ruling the
-- odd-order theorem may be assumed, so the node now carries `(hFT : FeitThompsonProp)` and is proved
-- from the already-proved `Work.ThmF.ChV12.<twin>`; the FT-free route survives as the
-- `PpdClosureProp`/`TransversalLinearSolvable` definitions.


theorem odd_ppd_normalizes {A : Type} [Group A] [Finite A]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x) {k q : ℕ}
    (hk1 : 1 ≤ k) (hk : Nat.card A = 2 ^ k) (hq : Nat.Prime q)
    (hord : orderOf (2 : ZMod q) = k)
    (G : Subgroup (MulAut A)) (hodd : Odd (Nat.card G))
    (σ : MulAut A) (hσG : σ ∈ G) (hσ : orderOf σ = q) :
    ∀ g ∈ G, ∃ i : ℤ, g * σ * g⁻¹ = σ ^ i := odd_ppd_normalizes_of_FT hFT hA2 hAc hk1 hk hq hord G hodd σ hσG hσ

end Work.ThmF.ChV12
