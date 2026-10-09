import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.SIdeles
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT

/-- **Second isomorphism theorem, one-sided form.**  If `A ⊔ B = ⊤` for subgroups `A`, `B` of an
abelian group `G`, then `B ⧸ (B ⊓ A) ≃* G ⧸ A`: the composite `B ↪ G ↠ G ⧸ A` is surjective
because every element of `G` is a product `a * b` with `a ∈ A`, `b ∈ B`, and its kernel is
`B ⊓ A`. -/
private lemma nonempty_quot_inf_mulEquiv_quot {G : Type*} [CommGroup G]
    (A B : Subgroup G) (h : (⊤ : Subgroup G) = A ⊔ B) :
    Nonempty (B ⧸ (B ⊓ A).subgroupOf B ≃* G ⧸ A) := by
  let φ : B →* G ⧸ A := (QuotientGroup.mk' A).comp B.subtype
  have hker : φ.ker = (B ⊓ A).subgroupOf B := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change ((x : G) : G ⧸ A) = 1 ↔ (x : G) ∈ B ⊓ A
    rw [QuotientGroup.eq_one_iff]
    exact ⟨fun hh => ⟨x.2, hh⟩, fun hh => hh.2⟩
  have hsurj : Function.Surjective φ := by
    rintro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective A y
    have hx : x ∈ A ⊔ B := by
      have hx' : x ∈ (⊤ : Subgroup G) := trivial
      rwa [h] at hx'
    rw [Subgroup.mem_sup] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    refine ⟨⟨b, hb⟩, ?_⟩
    show ((b : G) : G ⧸ A) = ((x : G) : G ⧸ A)
    rw [← hab, QuotientGroup.mk_mul]
    have h1 : ((a : G) : G ⧸ A) = 1 := (QuotientGroup.eq_one_iff a).mpr ha
    rw [h1, one_mul]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)⟩

theorem quot_TIdeles_mulEquiv_ideleClassGroup {L : Type} [Field L] [NumberField L]
    (T : Set (NK.GlobalCFT.Place L))
    (h : (⊤ : Subgroup (NK.GlobalCFT.Idele L)) =
      NK.GlobalCFT.Idele.principalSubgroup L ⊔ TIdeles T) :
    Nonempty (TIdeles T ⧸
      (TIdeles T ⊓ NK.GlobalCFT.Idele.principalSubgroup L).subgroupOf (TIdeles T)
      ≃* NK.GlobalCFT.IdeleClassGroup L) :=
  nonempty_quot_inf_mulEquiv_quot (Idele.principalSubgroup L) (TIdeles T) h

end NK.GlobalCFTdeep.Herbrand
