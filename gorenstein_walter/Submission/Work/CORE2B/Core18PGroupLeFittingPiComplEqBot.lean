import Mathlib
import Submission.Work.CORE2B.Defs
import Submission.Work.CORE2B.C18PGroupLeFittingPiComplEqBot_proved

/-!
# GW design 18, item A′, leaf H4: a `p`-subgroup of `F_{π'}(M)` with `p ∈ π` is trivial

Sketch (0.05–0.15k).  `fittingPiIn πᶜ M = (piCore πᶜ (fitting M)).map _`; every element of
`piCore πᶜ _` has order whose prime factors lie in `πᶜ` (it is a `πᶜ`-group), while a nontrivial
`p`-group has an element of order `p` (Cauchy), `p ∈ π`.  (BMAX/`fittingPiIn_compl_inf_eq_bot`
and CORE2B `L27_*` files use the same `piCore` API.)
-/


namespace Work.GW18

open Subgroup

theorem Core18PGroupLeFittingPiComplEqBot {G : Type} [Group G] [Finite G] (M : Subgroup G)
    (π : Set ℕ) (p : ℕ) [Fact p.Prime] (hpπ : p ∈ π) (K : Subgroup G) (hK : IsPGroup p K)
    (hKle : K ≤ Work.GW2.fittingPiIn πᶜ M) : K = ⊥ := Work.CORE2B.C18PGroupLeFittingPiComplEqBot_proved M π p hpπ K hK hKle

end Work.GW18
