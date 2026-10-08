import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.sylow2_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

open scoped Pointwise

/-- In a finite group `G`, let `M` be a subgroup of even order whose intersection with
each of its conjugates `Mᵍ` (`g ∉ M`) has odd order (a "strongly embedded" `M`, possibly
the whole group).  Then every Sylow 2-subgroup of `G` is conjugate into `M`.

If `M = G` this is trivial.  Otherwise `sylow2_le` supplies a Sylow 2-subgroup
`P₀ ≤ M` of `G`; by Sylow's second theorem `P₀` and the given `P` are conjugate,
say `P = x • P₀`, and then `P = x P₀ x⁻¹ ≤ x M x⁻¹ = M.map (conj x)`. -/
theorem sylow2_mem_conj {G : Type*} [Group G] [Finite G] (M : Subgroup G)
    (hEven : Even (Nat.card M))
    (hOdd : ∀ g : G, g ∉ M → Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    (P : Sylow 2 G) : ∃ x : G, (P : Subgroup G) ≤ M.map (MulAut.conj x).toMonoidHom := by
  classical
  by_cases hMtop : M = ⊤
  · -- M = G: take x = 1
    refine ⟨1, ?_⟩
    intro p hp
    rw [hMtop]
    exact Subgroup.mem_map.mpr ⟨p, by simp, by simp⟩
  · -- M ≠ ⊤: some Sylow 2-subgroup P₀ of G lies inside M
    obtain ⟨P₀, hP₀⟩ := sylow2_le M hMtop hEven hOdd
    -- P₀ and P are conjugate (Sylow's second theorem); write P = x • P₀
    obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G P₀ P
    refine ⟨x, ?_⟩
    rw [← hx]
    change (MulAut.conj x • (P₀ : Subgroup G)) ≤ M.map (MulAut.conj x).toMonoidHom
    rw [show MulAut.conj x • (P₀ : Subgroup G) = (P₀ : Subgroup G).map (MulAut.conj x).toMonoidHom by rfl]
    exact Subgroup.map_mono hP₀

end Commons.GroupTheory.StronglyEmbedded
