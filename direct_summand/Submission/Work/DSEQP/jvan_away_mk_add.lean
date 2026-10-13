import Mathlib

namespace Work.DSEQP

lemma jvan_away_mk_add {S : Type*} [CommRing S] {σ : Type*} [SetLike σ S] [AddSubgroupClass σ S]
    {𝒜 : ℕ → σ} [GradedRing 𝒜] {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) (k : ℕ) (s t : S)
    (hs : s ∈ 𝒜 (k • d)) (ht : t ∈ 𝒜 (k • d)) :
    HomogeneousLocalization.Away.mk 𝒜 hf k s hs + HomogeneousLocalization.Away.mk 𝒜 hf k t ht =
      HomogeneousLocalization.Away.mk 𝒜 hf k (s + t) (add_mem hs ht) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_add, HomogeneousLocalization.Away.val_mk]
  rw [Localization.add_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

end Work.DSEQP
