import Mathlib
import Submission.Work.ZassenhausSuzuki.SzAuto.conj_of_complements

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.SzAuto

set_option linter.style.haveILetI false

open scoped Pointwise IsMulCommutative

/-- Conjugation by `k : E` commutes with the embedding of `E` into `G`: pushing a conjugate of a
subgroup of `E` into `G` is the same as conjugating the image in `G` by the image of `k`. -/
lemma map_subtype_map_conj {G : Type*} [Group G] {E : Subgroup G} (B : Subgroup E) (k : E) :
    Subgroup.map E.subtype (B.map (MulAut.conj k).toMonoidHom)
      = (Subgroup.map E.subtype B).map (MulAut.conj (E.subtype k)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

/-- Zassenhaus/Schur–Zassenhaus conjugacy, relative to a subgroup `E` of `G`: if `K` is an abelian
subgroup of `E` that is normal in `E`, and `A`, `B` are two complements of `K` in `E` with
`|K|` coprime to `|A|`, then `A` is the conjugate of `B` by an element of `K`. -/
theorem conj_of_complements_in {G : Type*} [Group G] [Finite G]
    (K A B E : Subgroup G) (hKE : K ≤ E) (hAE : A ≤ E) (hBE : B ≤ E)
    (hKab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hKnorm : ∀ g ∈ E, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hcop : Nat.Coprime (Nat.card K) (Nat.card A))
    (hA : A ⊔ K = E) (hA' : A ⊓ K = ⊥)
    (hB : B ⊔ K = E) (hB' : B ⊓ K = ⊥) :
    ∃ k ∈ K, A = B.map (MulAut.conj k).toMonoidHom := by
  -- Transfer everything to the group `E` itself.
  let Ke : Subgroup ↥E := K.subgroupOf E
  let Ae : Subgroup ↥E := A.subgroupOf E
  let Be : Subgroup ↥E := B.subgroupOf E
  have hmapK : Subgroup.map E.subtype Ke = K := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKE]
  have hmapA : Subgroup.map E.subtype Ae = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAE]
  have hmapB : Subgroup.map E.subtype Be = B := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBE]
  have hcardK : Nat.card Ke = Nat.card K := by
    have h := Subgroup.card_map_of_injective (f := E.subtype) (K := Ke) Subtype.coe_injective
    rw [hmapK] at h; exact h.symm
  have hcardA : Nat.card Ae = Nat.card A := by
    have h := Subgroup.card_map_of_injective (f := E.subtype) (K := Ae) Subtype.coe_injective
    rw [hmapA] at h; exact h.symm
  have hmapTop : Subgroup.map E.subtype (⊤ : Subgroup ↥E) = E := by
    refine le_antisymm (Subgroup.map_subtype_le ⊤) ?_
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  -- `K` (as a subgroup of `E`) is normal in `E`.
  have hKnormal : Ke.Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hKnorm (g : G) g.2 (n : G) hn
  letI : Ke.Normal := hKnormal
  -- The complement decompositions transfer to `E`.
  have hsupA : Ae ⊔ Ke = ⊤ := by
    apply Subgroup.map_injective (f := E.subtype) Subtype.coe_injective
    rw [Subgroup.map_sup, hmapA, hmapK, hA, hmapTop]
  have hsupB : Be ⊔ Ke = ⊤ := by
    apply Subgroup.map_injective (f := E.subtype) Subtype.coe_injective
    rw [Subgroup.map_sup, hmapB, hmapK, hB, hmapTop]
  have hinfA : Ae ⊓ Ke = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxA, hxK⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_subgroupOf] at hxA hxK
    rw [Subgroup.mem_bot]
    have : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hA']; exact Subgroup.mem_inf.mpr ⟨hxA, hxK⟩
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hinfB : Be ⊓ Ke = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxB, hxK⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_subgroupOf] at hxB hxK
    rw [Subgroup.mem_bot]
    have : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hB']; exact Subgroup.mem_inf.mpr ⟨hxB, hxK⟩
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hcompA : Ke.IsComplement' Ae := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff_inf_le, inf_comm, hinfA]
    · rw [Set.eq_univ_iff_forall]
      intro x
      have hx : x ∈ Ke ⊔ Ae := by rw [sup_comm, hsupA]; exact Subgroup.mem_top x
      obtain ⟨k, hk, a, ha, hka⟩ :=
        (Subgroup.mem_sup_of_normal_left (s := Ke) (t := Ae)).mp hx
      exact Set.mem_mul.mpr ⟨k, hk, a, ha, hka⟩
  have hcompB : Ke.IsComplement' Be := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff_inf_le, inf_comm, hinfB]
    · rw [Set.eq_univ_iff_forall]
      intro x
      have hx : x ∈ Ke ⊔ Be := by rw [sup_comm, hsupB]; exact Subgroup.mem_top x
      obtain ⟨k, hk, b, hb, hkb⟩ :=
        (Subgroup.mem_sup_of_normal_left (s := Ke) (t := Be)).mp hx
      exact Set.mem_mul.mpr ⟨k, hk, b, hb, hkb⟩
  have hcopE : Nat.Coprime (Nat.card Ke) Ke.index := by
    rw [hcompA.symm.index_eq_card, hcardA, hcardK]
    exact hcop
  have hKabE : ∀ a ∈ Ke, ∀ b ∈ Ke, a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    have h1 := hKab (a : G) (Subgroup.mem_subgroupOf.mp ha) (b : G) (Subgroup.mem_subgroupOf.mp hb)
    simpa using h1
  haveI : IsMulCommutative Ke :=
    IsMulCommutative.of_comm (fun a b : Ke => Subtype.ext (hKabE a a.2 b b.2))
  -- Apply Schur–Zassenhaus conjugacy inside `E`.
  obtain ⟨g, hg⟩ :=
    Work.Hall.SchurZassenhaus.hall_sz_conj_abelian (N := Ke) (H := Be) (K := Ae) hcopE hcompB hcompA
  obtain ⟨k, hk, hkconj⟩ :=
    Work.ZassenhausSuzuki.SzAuto.exists_mem_conj_of_map_conj_eq (B := Be) (K := Ke) hsupB hg
  -- Push the conjugacy back down to `G`.
  refine ⟨(k : G), ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mp hk
  · rw [← hmapA, hkconj, map_subtype_map_conj, hmapB]
    rfl

end Work.ZassenhausSuzuki.SzAuto
