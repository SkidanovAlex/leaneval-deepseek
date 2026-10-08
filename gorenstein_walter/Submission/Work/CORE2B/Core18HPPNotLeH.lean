import Mathlib
import Submission.Work.CORE2B.HallPerPrime_Xodd
import Submission.Work.CORE2B.C18HPPNotLeH_proved

/-!
# GW design 18, item A′, leaf H1: the `t`-invariant Sylow `P` of `O(C_G(s))` is not in `C_G(t)`

Bender p. 222: "since `t` and `s` are conjugate, `P ⊄ C_G(t)`".

Sketch (0.2–0.35k).  Suppose `P ≤ H = C_G(t)`.  `H = U ⊔ S` (`T.split`), `P` has odd order
(`P ≤ O(C_G(s))`), so `P ≤ U` (`hallXodd_odd_subgroup_le_of_sup` /
`hallXodd_le_of_sup_isPGroup` in `HallPerPrime_Xodd`).  `s = t^g` (`T.fus`, as in the proof of
`HallPerPrime_Xodd`), so `C_G(s) = C_G(t)^{g⁻¹}`, `O(C_G(s)) = U^{g⁻¹}` and
`|O(C_G(s))| = |U|`.  `hPsyl` makes `|P|` the full `p`-part of `|O(C_G(s))| = |U|`, so `P` is a
Sylow `p`-subgroup of `U` (`P ≤ U`, equal `p`-part); the normal `p`-subgroup `O_p(U)` of `U` lies
in every Sylow `p`-subgroup of `U` (`Sylow.le_of_normal` style, via `pCoreIn`), so
`O_p(U) ≤ P ≤ C_G(s)`, contradicting `hXlt`.  (For `p = 2`, `P = 1` and `O_2(U) = 1`
(`pCoreIn_two_eq_bot`), again contradicting `hXlt`.)
-/


namespace Work.GW18

open Subgroup

theorem Core18HPPNotLeH (T : Work.GW2.LocalToolkit) (G : Type) [Group G] [Finite G]
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (s : G)
    (hs : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0) (p : ℕ) (hp : Nat.Prime p) (P : Subgroup G)
    (hPK : P ≤ Work.GW2.oddCoreIn (Subgroup.centralizer ({s} : Set G)))
    (hPp : IsPGroup p P)
    (hPsyl : ¬ p ∣ P.relIndex (Work.GW2.oddCoreIn (Subgroup.centralizer ({s} : Set G))))
    (hXlt : ¬ Work.GW2.pCoreIn p B.U ≤ Subgroup.centralizer ({s} : Set G)) :
    ¬ P ≤ Subgroup.centralizer ({B.t} : Set G) := Work.CORE2B.C18HPPNotLeH_proved T G hCtx B s hs hs0 p hp P hPK hPp hPsyl hXlt

end Work.GW18
