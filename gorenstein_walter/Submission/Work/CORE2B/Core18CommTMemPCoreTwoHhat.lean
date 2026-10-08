import Mathlib
import Submission.Work.CORE2B.HallPerPrime_aux
import Submission.Work.CORE2B.C18CommTMemPCoreTwoHhat_proved

/-!
# GW design 18, item A′, leaf H6: `[y, t] ∈ O₂(Ĥ)` for `y ∈ Ĥ`

Sketch (0.05–0.15k).  Thm 2.6 (`h26`): `S ∩ C_G(U) = O₂(Ĥ)`; `t ∈ S` (`t ∈ S₀ ≤ S`) and `t`
centralizes `U` (`t_commutes_U`), so `t ∈ O₂(Ĥ)`.  `O₂(Ĥ) = pCoreIn 2 Ĥ` is normalized by `Ĥ`
(`le_normalizer_pCoreIn_local`/`le_normalizer_map_subtype_local`), so `y t y⁻¹ ∈ O₂(Ĥ)`, and
`t⁻¹ ∈ O₂(Ĥ)`.
-/


namespace Work.GW18

open Subgroup

theorem Core18CommTMemPCoreTwoHhat (h26 : Work.GW2.Thm26Prop) (G : Type) [Group G] [Finite G]
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (y : G) (hy : y ∈ B.Hhat) :
    y * B.t * y⁻¹ * B.t⁻¹ ∈ Work.GW2.pCoreIn 2 B.Hhat := Work.CORE2B.C18CommTMemPCoreTwoHhat_proved h26 G hFT hCtx B y hy

end Work.GW18
