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
the whole group).  Then every involution `t` of `G` is conjugate into `M`: some conjugate
of `t` lies in `M`, i.e. `t` belongs to a conjugate `Mˣ` of `M`. -/
theorem involution_mem_conj {G : Type*} [Group G] [Finite G] (M : Subgroup G)
    (hEven : Even (Nat.card M))
    (hOdd : ∀ g : G, g ∉ M → Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    {t : G} (ht : orderOf t = 2) : ∃ x : G, t ∈ M.map (MulAut.conj x).toMonoidHom := by
  classical
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  by_cases hMtop : M = ⊤
  · -- M = G: take x = 1
    refine ⟨1, ?_⟩
    rw [hMtop]
    refine (Subgroup.mem_map).mpr ⟨t, trivial, ?_⟩
    simp
  · -- M ≠ ⊤: some Sylow 2-subgroup P of G lies inside M
    obtain ⟨P, hPleM⟩ := sylow2_le M hMtop hEven hOdd
    -- ⟨t⟩ is a 2-subgroup of G, hence lies in some Sylow 2-subgroup R of G
    let Q : Subgroup G := Subgroup.zpowers t
    have hQpg : IsPGroup 2 Q := by
      refine IsPGroup.of_card (p := 2) (n := 1) ?_
      dsimp [Q]
      rw [Nat.card_zpowers, ht]
    obtain ⟨R, hQR⟩ := IsPGroup.exists_le_sylow (P := Q) hQpg
    have htR : t ∈ (R : Subgroup G) := hQR (Subgroup.mem_zpowers t)
    -- R is conjugate to P (Sylow's theorem); write R = g • P
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P R
    have hRleM : (R : Subgroup G) ≤ M.map (MulAut.conj g).toMonoidHom := by
      rw [← hg]
      change (MulAut.conj g • (P : Subgroup G)) ≤ M.map (MulAut.conj g).toMonoidHom
      rw [show MulAut.conj g • (P : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom by rfl]
      exact Subgroup.map_mono hPleM
    refine ⟨g, hRleM htR⟩

end Commons.GroupTheory.StronglyEmbedded
