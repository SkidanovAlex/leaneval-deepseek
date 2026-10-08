import Mathlib
import Submission.Work.BG.BInvAux.Basic
import Submission.Work.BG.C_odd_mem_U

namespace Work.BG.BInvAux

open Subgroup in
/-- **An odd-order element of `C_G(S)` lies in `B`.**

`c ∈ C_G(S)` with `orderOf c` odd lies in `U = O(C_G(t))` by `Work.BG.C_odd_mem_U`
(`S ≤ C_G(t) = H = U ⊔ S` with `S` a `2`-group, so an odd-order element of `H` must lie in the
odd factor `U`). Combined with `c ∈ C_G(S)` this is exactly `c ∈ B = U ⊓ C_G(S)`
(`mem_B_iff`). -/
theorem odd_order_mem_B {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) (hn : D.n = 2)
    {c : G} (hc : c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G))
    (hodd : Odd (orderOf c)) :
    c ∈ D.B :=
  (mem_B_iff D).mpr ⟨Work.BG.C_odd_mem_U D hn hc hodd, hc⟩

end Work.BG.BInvAux
