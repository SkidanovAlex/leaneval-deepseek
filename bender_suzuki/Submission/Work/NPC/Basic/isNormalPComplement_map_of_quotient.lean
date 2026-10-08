import Mathlib
import Submission.Work.NPC.Defs
import Submission.Work.NPC.Basic.isNormalPComplement_unique

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.NPC.Basic

/-- If `A ⊴ G` has `p`-group quotient, and `N ⊴ A` is a normal `p`-complement of `A`, then the
image of `N` in `G` is a normal `p`-complement of `G`.

* Normality of `N.map A.subtype` in `G`: conjugation by `g : G` restricts to an automorphism of
  `A` (via `MulAut.conjNormal`), which carries the normal `p`-complement `N` of `A` to another
  one; by uniqueness of normal `p`-complements (`isNormalPComplement_unique`) it must fix `N`.
* `|N.map A.subtype| = |N|` is coprime to `p`.
* `G ⧸ N.map A.subtype` is a `p`-group: by `Subgroup.index_map_subtype` its index is
  `[G : A] * [A : N]`, a product of two `p`-powers. -/
theorem isNormalPComplement_map_of_quotient {G : Type*} [Group G] [Finite G] {p : ℕ}
    {A : Subgroup G} [A.Normal] {N : Subgroup ↥A} (hN : Work.NPC.IsNormalPComplement p N)
    (hA : IsPGroup p (G ⧸ A)) :
    Work.NPC.IsNormalPComplement p (N.map A.subtype) := by
  haveI hNn : N.Normal := hN.normal
  have hnorm : (N.map A.subtype).Normal := by
    -- Conjugation by any `g : G` fixes `N` inside `A`.
    have key : ∀ g : G, N.map ((MulAut.conjNormal (H := A) g : ↥A →* ↥A)) = N := by
      intro g
      have hM : Work.NPC.IsNormalPComplement p
          (N.map ((MulAut.conjNormal (H := A) g : ↥A →* ↥A))) := by
        haveI hnorm' : (N.map ((MulAut.conjNormal (H := A) g : ↥A →* ↥A))).Normal :=
          hNn.map _ (MulAut.conjNormal (H := A) g).surjective
        refine ⟨inferInstance, ?_, ?_⟩
        · rw [Subgroup.card_map_of_injective (f := (MulAut.conjNormal (H := A) g : ↥A →* ↥A))
              (MulAut.conjNormal (H := A) g).injective]
          exact hN.coprime_card
        · exact IsPGroup.of_equiv hN.isPGroup_quotient
            (QuotientGroup.congr N (N.map ((MulAut.conjNormal (H := A) g : ↥A →* ↥A)))
              (MulAut.conjNormal (H := A) g) rfl)
      exact Work.NPC.Basic.isNormalPComplement_unique
        (N := N.map ((MulAut.conjNormal (H := A) g : ↥A →* ↥A))) (M := N) hM hN
    refine Subgroup.Normal.mk (fun n hn g => ?_)
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hn
    refine Subgroup.mem_map.mpr ⟨MulAut.conjNormal (H := A) g a, ?_, ?_⟩
    · rw [← key g]
      exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    · exact MulAut.conjNormal_apply g a
  haveI := hnorm
  refine ⟨hnorm, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (f := A.subtype) A.subtype_injective]
    exact hN.coprime_card
  · -- `[G : N.map A.subtype] = [A : N] * [G : A]` is a product of `p`-powers.
    obtain ⟨a, ha⟩ := isPGroup_iff_card_dvd_pow.mp hN.isPGroup_quotient
    obtain ⟨b, hb⟩ := isPGroup_iff_card_dvd_pow.mp hA
    refine IsPGroup.of_card_dvd_pow (n := a + b) ?_
    rw [← Subgroup.index_eq_card (H := N.map A.subtype), Subgroup.index_map_subtype, Nat.pow_add,
      Subgroup.index_eq_card (H := N), Subgroup.index_eq_card (H := A)]
    exact Nat.mul_dvd_mul ha hb

end Work.NPC.Basic
