import Mathlib.GroupTheory.OrderOfElement
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.map_conj_eq_of_mem

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

/-- For an involution `t ∈ M`, membership of `t` in the conjugate `Mᵍ := gMg⁻¹`
is equivalent to `g ∈ M`.

The forward direction: if `g ∉ M` but `t ∈ Mᵍ`, then `t` lies in the
intersection `M ⊓ Mᵍ`, whose order is odd by hypothesis; but `t` has order 2,
forcing `2 ∣ |M ⊓ Mᵍ|`, a contradiction.  The backward direction: if `g ∈ M`
then conjugation by `g` fixes `M`, so `Mᵍ = M ∋ t`. -/
theorem conj_mem_iff_mem_of_orderTwo {G : Type*} [Group G] (M : Subgroup G)
    (hOdd : ∀ g : G, g ∉ M → Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    {t : G} (htM : t ∈ M) (ht : orderOf t = 2) {g : G} :
    t ∈ M.map (MulAut.conj g).toMonoidHom ↔ g ∈ M := by
  constructor
  · intro htg
    by_contra hg
    have htK : t ∈ (M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G) := ⟨htM, htg⟩
    have hdvd : 2 ∣ Nat.card (M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
      simpa [ht] using
        (Subgroup.orderOf_dvd_natCard (M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G) htK)
    exact (Nat.not_even_iff_odd.mpr (hOdd g hg)) (even_iff_two_dvd.mpr hdvd)
  · intro hg
    rw [map_conj_eq_of_mem M hg]
    exact htM

end Commons.GroupTheory.StronglyEmbedded
