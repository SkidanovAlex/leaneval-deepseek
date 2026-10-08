import Mathlib
import Submission.Work.BG.BInvAux.Basic

namespace Work.BG.BInvAux

open scoped Pointwise

set_option linter.style.haveILetI false

open Subgroup in
/-- **`C_G(S) = B · S`** for `n = 2`: every element of `C_G(S)` factors as `u * s` with
`u ∈ B = U ⊓ C_G(S)` and `s ∈ S`.

Indeed `C_G(S) ≤ C_G(t) = H = U ⊔ S` (`centralizer_S_le_H`, `H_eq_U_sup_S`), and since
`S ≤ N_G(U)` the join `U ⊔ S` is the set product `U * S` (`Work.BG.coe_U_sup_S`).  Writing
`c = u * s`, both `c` and `s` centralise `S` (for `s` because `S` is abelian when `n = 2`,
`S_commutative`), hence so does `u = c * s⁻¹`, and `u ∈ U` by construction, so
`u ∈ U ⊓ C_G(S) = B`. -/
theorem decomp_centralizer {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) (hn : D.n = 2)
    {c : G} (hc : c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G)) :
    ∃ u ∈ D.B, ∃ s ∈ (D.S : Subgroup G), c = u * s := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  -- `c ∈ C_G(t) = H` and `H = U ⊔ S`
  have hcH : c ∈ D.H := centralizer_S_le_H D hc
  have hmem : c ∈ D.U ⊔ (D.S : Subgroup G) := by
    rw [H_eq_U_sup_S D]; exact hcH
  -- `U ⊔ S = U · S` because `S ≤ N_G(U)`
  have hprod : c ∈ (↑D.U : Set G) * (↑(D.S : Subgroup G) : Set G) := by
    rw [← Work.BG.coe_U_sup_S D]; exact hmem
  obtain ⟨u, hu, s, hs, hus⟩ := Set.mem_mul.mp hprod
  -- `s ∈ S` centralises `S`: `S` is abelian for `n = 2`
  have hsC : s ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact S_commutative D hn x hx s hs
  -- hence `u = c * s⁻¹` centralises `S` as well, and `u ∈ U`, so `u ∈ B`
  have huC : u ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G) := by
    have h : u = c * s⁻¹ := by rw [← hus]; group
    rw [h]
    exact Subgroup.mul_mem _ hc (Subgroup.inv_mem _ hsC)
  refine ⟨u, ?_, s, hs, hus.symm⟩
  refine ⟨⟨hu, ?_⟩, ⟨hu, ?_⟩⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp huC D.t1 D.t1_mem).symm
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp huC D.t2 D.t2_mem).symm

end Work.BG.BInvAux
