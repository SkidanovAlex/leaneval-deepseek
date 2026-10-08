import Mathlib.GroupTheory.OrderOfElement

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

theorem centralizer_le {G : Type*} [Group G] (M : Subgroup G)
    (hOdd : ∀ g : G, g ∉ M → Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    {t : G} (htM : t ∈ M) (ht : orderOf t = 2) :
    Subgroup.centralizer ({t} : Set G) ≤ M := by
  intro c hc
  by_contra hcM
  have hodd : Odd (Nat.card ((M ⊓ M.map (MulAut.conj c).toMonoidHom : Subgroup G))) := hOdd c hcM
  have hcomm : c * t = t * c := (Subgroup.mem_centralizer_singleton_iff.mp hc)
  have htmap : t ∈ M.map (MulAut.conj c).toMonoidHom := by
    refine ⟨t, htM, ?_⟩
    change c * t * c⁻¹ = t
    calc
      c * t * c⁻¹ = t * c * c⁻¹ := by rw [hcomm]
      _ = t := by simp
  have htK : t ∈ (M ⊓ M.map (MulAut.conj c).toMonoidHom : Subgroup G) := ⟨htM, htmap⟩
  have hdvd : 2 ∣ Nat.card ((M ⊓ M.map (MulAut.conj c).toMonoidHom : Subgroup G)) := by
    simpa [ht] using (Subgroup.orderOf_dvd_natCard (M ⊓ M.map (MulAut.conj c).toMonoidHom : Subgroup G) htK)
  exact (Nat.not_even_iff_odd.mpr hodd) ((even_iff_two_dvd).mpr hdvd)

end Commons.GroupTheory.StronglyEmbedded