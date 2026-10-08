import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.conj_mem_iff_mem_of_orderTwo
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.mem_map_conj_iff
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.orderOf_conj
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.map_conj_eq_of_mem

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

theorem eq_of_mem_map_conj_of_orderTwo {G : Type*} [Group G] (M : Subgroup G)
    (hOdd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    {t x y : G} (ht : orderOf t = 2)
    (hx : t ∈ M.map (MulAut.conj x).toMonoidHom)
    (hy : t ∈ M.map (MulAut.conj y).toMonoidHom) :
    M.map (MulAut.conj x).toMonoidHom = M.map (MulAut.conj y).toMonoidHom := by
  set N : Subgroup G := M.map (MulAut.conj x).toMonoidHom with hN
  -- Transfer the odd-intersection hypothesis to the conjugate `N = Mᵡ`.
  have hOddN : ∀ g : G, g ∉ N →
      Odd (Nat.card ((N ⊓ N.map (MulAut.conj g).toMonoidHom : Subgroup G))) := by
    intro g hgN
    have hcon : x⁻¹ * g * x ∉ M := by
      intro hh
      apply hgN
      rw [hN, mem_map_conj_iff]
      exact hh
    have hodd := hOdd (x⁻¹ * g * x) hcon
    have hsub : (M ⊓ M.map (MulAut.conj (x⁻¹ * g * x)).toMonoidHom : Subgroup G).map (MulAut.conj x).toMonoidHom
        = N ⊓ N.map (MulAut.conj g).toMonoidHom := by
      rw [hN]
      rw [Subgroup.map_inf M (M.map (MulAut.conj (x⁻¹ * g * x)).toMonoidHom)
            (MulAut.conj x).toMonoidHom (MulEquiv.injective _)]
      congr 1
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext m
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hcard : Nat.card (N ⊓ N.map (MulAut.conj g).toMonoidHom : Subgroup G)
        = Nat.card (M ⊓ M.map (MulAut.conj (x⁻¹ * g * x)).toMonoidHom : Subgroup G) := by
      rw [← hsub, Subgroup.card_map_of_injective (MulEquiv.injective _)]
    rw [hcard]; exact hodd
  -- `Mᵞ` is the conjugate of `N = Mᵡ` by `y * x⁻¹`.
  have hNy : N.map (MulAut.conj (y * x⁻¹)).toMonoidHom = M.map (MulAut.conj y).toMonoidHom := by
    rw [hN, Subgroup.map_map]
    congr 1
    ext m
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have htNy : t ∈ N.map (MulAut.conj (y * x⁻¹)).toMonoidHom := by rw [hNy]; exact hy
  have hmem : y * x⁻¹ ∈ N :=
    (conj_mem_iff_mem_of_orderTwo N hOddN hx ht (g := y * x⁻¹)).1 htNy
  have hNg : N.map (MulAut.conj (y * x⁻¹)).toMonoidHom = N := map_conj_eq_of_mem N hmem
  exact hNg.symm.trans hNy

end Commons.GroupTheory.StronglyEmbedded
