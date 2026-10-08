import Mathlib
import Submission.Work.Hall.SchurZassenhaus.hall_schurZassenhaus_conj
import Submission.Work.Coprime.schurZassenhaus_conj_of_solvable_quotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.Coprime

/-- Conjugacy form of Schur--Zassenhaus needed for the coprime action development: if `G` is a
normal Hall subgroup of the finite group `X` (`|G|` coprime to `[X : G]`), `A` is a complement of
`G`, and `K` is any subgroup with `G ⊔ K = ⊤`, then some conjugate of `K` contains `A`.

The complement `B ≤ K` of `G` is obtained by applying Schur--Zassenhaus existence to the normal
Hall subgroup `G ∩ K` of `K`; then `A` and `B` are two complements of the normal Hall subgroup `G`
of `X`, so Schur--Zassenhaus conjugacy (in whichever of the two forms the solvability hypothesis
provides) makes them conjugate. -/
theorem exists_conj_le_of_isComplement {X : Type*} [Group X] [Finite X]
    {G A K : Subgroup X} [G.Normal]
    (hc : (Nat.card G).Coprime G.index) (hGA : G.IsComplement' A)
    (hsup : G ⊔ K = ⊤)
    (hsol : Group.IsSolvable G ∨ Group.IsSolvable (X ⧸ G)) :
    ∃ x : X, A ≤ K.map (MulAut.conj x).toMonoidHom := by
  classical
  -- The normal Hall subgroup `G ∩ K` of `K`.
  haveI hN'norm : (G.subgroupOf K).Normal := Subgroup.Normal.subgroupOf inferInstance K
  have hcop : (Nat.card (G.subgroupOf K)).Coprime (G.subgroupOf K).index :=
    coprime_card_subgroupOf_index' (N := G) (Y := K) hc
  -- Schur--Zassenhaus existence: `K` has a complement `B'` of `G ∩ K`.
  obtain ⟨B', hB'⟩ := Subgroup.exists_right_complement'_of_coprime (N := G.subgroupOf K) hcop
  let B : Subgroup X := B'.map K.subtype
  have hBK : B ≤ K := by
    rintro y ⟨z, _hz, rfl⟩
    exact z.2
  have hcardB' : Nat.card B' = (G.subgroupOf K).index := Subgroup.IsComplement.card_right hB'
  have hrelidx : (G.subgroupOf K).index = G.index := by
    change G.relIndex K = G.index
    rw [← Subgroup.relIndex_sup_left (H := K) (K := G), hsup, Subgroup.relIndex_top_right]
  have hcardA : Nat.card A = G.index := Subgroup.IsComplement.card_right hGA
  have hcardB : Nat.card B = Nat.card A := by
    have h1 : Nat.card B = Nat.card B' :=
      Subgroup.card_map_of_injective (f := K.subtype) Subtype.coe_injective
    rw [h1, hcardB', hrelidx, ← hcardA]
  -- `B` is disjoint from `G`.
  have hBG : B ⊓ G = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro y hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyB, hyG⟩ := hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hyB
    have hzN : z ∈ G.subgroupOf K := by rw [Subgroup.mem_subgroupOf]; exact hyG
    have hzbot : z ∈ (⊥ : Subgroup ↥K) := disjoint_iff_inf_le.mp hB'.disjoint ⟨hzN, hz⟩
    have hz1 : z = 1 := Subgroup.mem_bot.mp hzbot
    rw [hz1]; rfl
  -- Hence `B` is a complement of `G` in `X`.
  have hGB : G.IsComplement' B := by
    rw [Subgroup.isComplement'_iff_card_mul_and_disjoint]
    refine ⟨?_, disjoint_iff.mpr (by rw [inf_comm]; exact hBG)⟩
    rw [hcardB]
    exact (Subgroup.isComplement'_iff_card_mul_and_disjoint.mp hGA).1
  -- Schur--Zassenhaus conjugacy: `A` and `B` are conjugate.
  obtain ⟨g, hg⟩ : ∃ g : X, B = A.map (MulAut.conj g).toMonoidHom := by
    rcases hsol with hG | hQ
    · exact Work.Hall.SchurZassenhaus.hall_schurZassenhaus_conj hG hc hGA hGB
    · exact schurZassenhaus_conj_of_solvable_quotient hc hQ hGA hGB
  refine ⟨g⁻¹, ?_⟩
  intro a ha
  refine Subgroup.mem_map.mpr ⟨MulAut.conj g a, ?_, ?_⟩
  · have hmem : MulAut.conj g a ∈ B := by
      rw [hg]
      exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    exact hBK hmem
  · show (MulAut.conj g⁻¹) (MulAut.conj g a) = a
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group

end Work.Coprime
